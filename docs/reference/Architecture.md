# Architecture

som-knowledge-machine is a Clojure port of KM, The Knowledge Machine, inference engine 2.5.45. The specification is the Lisp source in `src/knowledge-machine/km-2-5-45-packaged.lisp`. This document is the map of the port. The history of each finished step is in `docs/migration/`.

## Shape

The engine is a library. Two adapters sit on it. Each adapter holds the knowledge base and the query for its own caller and passes them into `evaluate`.

```
line of text        som.km.repl     som.km.engine/evaluate     printed answer
HTTP request        som.km.server   som.km.engine/evaluate     JSON answer
                                        som.km.interpreter
                                   som.km.slotvals  som.km.frame  som.km.stack
                                        som.km.read    som.km.print
                                              som.km.term
```

| Namespace | Role |
| --- | --- |
| `som.km.engine` | Reads one expression and evaluates it. `reset` rebuilds the built-in vocabulary in a knowledge base the caller passes in. |
| `som.km.interpreter` | The one dispatcher. The handler table is the Lisp alist, in its original order. `:value` is the answer list. |
| `som.km.slotvals` | Local slot values, and the six sources a slot value can come from. Only the local store contributes. |
| `som.km.read` | Turns text into a term. Case is preserved. |
| `som.km.print` | Turns a term into the text `km-format` would write. |
| `som.km.term` | Cons cells, symbols, and list shape. The empty list is nil. |
| `som.km.strings` | `explode`, `concat-list`, and `substitute-string`, used by the printer. |
| `som.km.explain` | Recognizes and removes comment tags and source markers. The interpreter strips them before dispatch. |
| `som.km.utils` | List, set, and binding helpers. A proper list is walked strictly. |
| `som.km.kbutils` | Shape tests and `km-equal`. It does not ask whether a name is a class or a slot. |
| `som.km.frame` | The frame store. A knowledge base is a value the caller passes back in. |
| `som.km.stack` | The goal stack and the loop check. Both stacks live on the query. The interpreter pushes goals. |
| `som.km.minimatch` | `minimatch` returns captured pieces. `full-match` returns a binding list. The handler table uses it. |
| `som.km.repl` | The `KM>` prompt. It holds one session. `q` leaves when the line reads as that symbol. |
| `som.km.server` | The HTTP service. It holds one session. The handler turns a request into a map and writes the response. |

A cons cell is a record, so it answers `map?`. Code that accepts a map tests for a cons cell first. The frame store does this where it accepts a map. `som.km.engine/reset` calls `som.km.frame/reset`. A direct `reset` keeps the inference counters and the list of instances being unified. A top-level `evaluate` clears those before the expression runs.

`som.km.server/handler` is an ordinary function from a request map to a response map. The JDK HTTP server (`com.sun.net.httpserver.HttpServer`) is the socket in front of that function. The service listens on `127.0.0.1`, port `8080` unless `PORT` is set.

| Method and path | Behavior |
| --- | --- |
| `GET /` | Names the other routes. |
| `GET /status` | Returns the build description from `som.km.engine/status`. |
| `POST /query` | Submits the body as Knowledge Machine text. The body is `text/plain`, or it has no content type. |

HTTP status comes from the result: `200` when `:ok` is true, `400` for `empty` and for `read`, `501` for `not-ported`, `415` for a body that is not plain text, `404` for an unknown route.

## Result map

`som.km.engine/evaluate` takes the text and an optional map `{:bindings ... :kb ... :query ...}`. The bindings map is how `#t` finds a name. The prompt and the service pass an empty bindings map and their own knowledge base and query. A call that omits `:kb` starts from the built-in vocabulary and does not see an earlier call.

| Key | Meaning |
| --- | --- |
| `:ok` | True when the text was read and the form is one this step runs, including a syntax error. False for `empty`, `read`, and `not-ported`. |
| `:error` | `empty` when there is nothing to read, `read` when the text is not a term, `not-ported` when the form is in the table and is not run yet. Absent when the expression ran. |
| `:message` | The sentence for an empty line, a read failure, or a form that is not ported yet. |
| `:input` | The trimmed text, when the caller sent some. A blank string has no `:input`. |
| `:value` | The answer list. Nil is an empty answer. Absent on a read error. |
| `:errors` | The error sentences recorded while reasoning, in order. |
| `:error-structures` | The expression recorded with each error. |
| `:warnings` | The warning sentences, in order. |
| `:text` | Text a command would have printed. Present for the stack inspectors. |
| `:kb` | The knowledge base to pass on the next call. Absent on a read error. |
| `:query` | The query to pass on the next call. The fail mode and the object stack live here. |
| `:incomplete` | On a read error, true when the text is only a prefix of a term. |

The prompt prints `:text`, when it is present, and then `km-format` of `:value`. Nil prints as `nil`. When `:errors` is not empty, the same line ends with `   ; (WARNING: Errors occurred during reasoning)`. A refusal prints `:message`. A line that reads as the symbol `q` ends the prompt and prints nothing. Evaluating `q` answers the list `(q)`, so the leave test uses the term that was read.

The service returns the same map as JSON, without `:kb` or `:query`. A proper list is an array. A symbol, a keyword, a dotted cons, and a ratio are objects. An integer that fits in a long is a number. A larger integer is decimal text. `q` is an expression and does not stop the service.

`status` reports `:evaluator "interpreter"`. A refusal named `not-ported` maps to HTTP 501. A syntax error stays HTTP 200.

## State

The knowledge base is a value. `som.km.frame/knowledge-base` builds an empty one. The caller passes it into the store functions and uses the value they return. It holds the frames, the order they were first stored, the bindings, the gensym counter, the current situation, the situation and theory names, the situation-facet cache, the deleted names, and the runtime flags. A frame has four facets. A facet holds an ordered list of `(slot (value ...))`. In `*Global` the facet name is the facet. In another situation the name is the facet name joined to the situation name.

`reset` clears the frames and rebuilds the built-in vocabulary in the returned value. The classes, the slots, and the instances `t`, `f`, the fluent statuses, and `*Global` are frames. The default fluent status is `*Fluent`. The optimization flags start clear. A non-fluent slot is stored in `*Global` when the caller leaves the situation out. A prototype is not redirected yet. A theory is not recognized yet.

The query holds the object stack and the goal stack. A goal is the canonical expression, the situation, the expression that was pushed, the inference number, and the target. A unification is recorded under `|all situations|`. `looping-on?` compares the canonical form after bindings are followed. `&+!` stays distinct from `&`. An `or` between a goal and its repeat is still a loop. `reset` clears both stacks. It keeps the list of instances being unified, the inference counters, and the caller's unstackable-instance list. That list starts as `(t)`.

`evaluate` takes the knowledge base and the query, pushes a goal for an expression that reaches the handler table, and returns the answer list. The prompt holds one session for the person at the keyboard. The running service holds one session and locks it, so one request uses that value at a time. Two posts on that service see each other's assertions. The prompt and the service do not see each other. `(reset-kb)` rebuilds the vocabulary and answers `(t)`. `(show-goal-stack)` at the top level shows an empty stack, because the top-level clear runs first. `(show-obj-stack)` shows the frames touched on that query.

A top-level call clears the goal stack, the instances being unified, both inference counters, the depth, and the looping flag. It leaves the object stack, the fail mode, and a caller's depth limit. It does not turn inverse installation back on. The depth limit starts unset. A query deeper than 400 stops the way a set limit would.

Unification in Knowledge Machine rewrites frames. Those operators are recognized and refused. The knowledge base value is still where that state will live. One caller uses a given value at a time. Dereferencing follows bindings unless the caller turns it off. Ununification stays off. Constraints are stored and answer nil. They are not enforced yet.

## Dependencies

`deps.edn` declares Clojure and `org.clojure/data.json` from Maven Central. Tests use the Cognitect test runner. This build resolves Maven through a Nexus mirror of Maven Central. The mirror does not serve Clojars, so Ring is not on the classpath. Replacing the JDK server is a later decision, recorded here when it happens.

## What the Lisp modules become

The concatenated Lisp file is marked with `;;; FILE:` headers. `src/knowledge-machine/disassemble` is the Perl unpacker taken from that file. Running it writes one source file per header into `src/knowledge-machine/packages/`. Each of those files, except `README.txt`, begins with the `km` package forms the script inserts. How those files fit together is recorded in `src/knowledge-machine/packages/Architecture.md`. The runtime flags, frame layout, and reader macros are recorded in `src/knowledge-machine/packages/Conventions.md`. The port follows those modules in the order listed in `docs/migration/README.md`. Why that order differs from the Lisp load order, and where Clojure will not produce the same result, is recorded in `docs/migration/plan.md`. `compiled-handlers.lisp` stays unported. It is a generated flattening of the same interpreter. `htextify.lisp` is a stub.
