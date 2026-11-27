# Architecture

som-knowledge-machine is a Clojure port of KM, The Knowledge Machine, inference engine 2.5.45. The specification is the Lisp source in `src/knowledge-machine/km-2-5-45-packaged.lisp`. This document is the map of the port. The history of each finished step is in `docs/migration/`.

## Shape

The engine is a library. Two adapters sit on it. Each adapter holds the knowledge base and the query for its own caller and passes them into `evaluate`.

```
line of text        som.km.repl     som.km.engine/evaluate     printed answer
HTTP request        som.km.server   som.km.engine/evaluate     JSON answer
(load-lib)          som.kb/load-lib som.km.loadkb/load-file    loaded names
                                        som.km.interpreter
                          som.km.display
                          som.km.trace    som.km.stats    som.km.sadl    som.km.license
                          som.km.loadkb     som.km.writer     som.km.anglify
                          som.km.situations
                          som.km.slotvals   som.km.unify   som.km.subsumes   som.km.stack
                          som.km.prototypes som.km.taxonomy    som.km.frame
                                        som.km.read    som.km.print
                                        som.km.errors  som.km.term
```

| Namespace | Role |
| --- | --- |
| `som.km.engine` | Reads one expression and evaluates it. `reset` rebuilds the built-in vocabulary in a knowledge base the caller passes in. |
| `som.km.interpreter` | The one dispatcher. The handler table is the Lisp alist, in its original order. `:value` is the answer list. `(a Class)` creates an anonymous instance. In prototype mode that instance is a participant. `(a-prototoype Class)` is the empty prototype. `load-kb`, `(load-lib)`, `save-kb`, checkpoint, and undo run. `(load-lib)` loads the component library into the knowledge base passed to `evaluate`. A load resets the inference engine once at the start, and a form that is not ported yet follows `:on-error`. `(trace)`, `(untrace)`, spy, profile, `(do-plan)`, `(license)`, `(evaluate)`, and `(comments)` run. `do-script`, `is-true`, `all-true`, `some-true`, `in-every-situation`, `showme`, `showme-all`, `evaluate-all`, `thelast`, `exists`, `has-value`, `print`, and `format` run. `(anonymous-instancep ...)` stays refused. `(version)` prints the Knowledge Machine banner and answers `(t)`. A trace line is recorded on `:text`. The interactive menu is not read. |
| `som.km.display` | `showme`, `showme-all`, and `evaluate-all`. `showme-all` sorts slot names with `string<` on the symbol name. The interpreter is passed in as `km-int`. This namespace does not require the interpreter. |
| `som.km.trace` | Records one call, exit, fail, or comment line on `:text`, and appends it to the named file when trace-to-file is on. The interactive menu is not read. This namespace does not require the interpreter. |
| `som.km.stats` | The short statistics line, the long report, the spot line, and the profile table. A positive interval keeps the extra closing parenthesis from the Lisp format. The frame store, unification, and prototypes update their own counters. This namespace does not require them or the interpreter. |
| `som.km.sadl` | `(do-plan)` reads `first-subevent`, runs `(do-and-next)`, and follows `next-event`. The interpreter is passed in as `km-int`. This namespace does not require the interpreter. |
| `som.km.license` | The text `(license)` prints. It is the repository `LICENSE` file, captured when the namespace loads. |
| `som.km.loadkb` | Loads and saves a knowledge base, and undoes a logged change. The caller passes the value in. A load resets the inference engine once at the start. A form that is not ported yet follows `:on-error`. This namespace does not require the interpreter. The interpreter is passed in as `km-int`. `fastsave` stays refused. |
| `som.km.writer` | Prints a frame, or a whole knowledge base, as KM text. Each save group and the comments section are sorted with `string-lessp`. A subclass of `Situation` writes its assertions as `(in-every-situation ...)`, with `TheSituation` and `Self` restored. `htextify` returns nothing. This namespace does not require the interpreter or the loader. |
| `som.km.anglify` | Turns a Knowledge Machine expression into one English string. `make-phrase` and `make-sentence` flatten a value, or a `:set` or `:seq` of values. A number below 1 uses scientific form with the Lisp exponent width, so `0.0001` is `1.000e-4`. A name lookup runs with tracing off and restores the flag. The interpreter is passed in as `km-int`. This namespace does not require the interpreter. |
| `som.km.situations` | Enters a situation or a theory, runs an action, and collects own facts from supersituations and visible theories. The slot reader and the interpreter are passed in. This namespace does not require either of them. |
| `som.km.slotvals` | Local slot values, and the six sources a slot value can come from. A suitable prototype is cloned before the local store, the class rules, and the subslot values. An inertial fluent in a local situation is projected from the previous situation. Own facts from supersituations and visible theories are merged. The parent situation's value is not re-read. Local and inherited constraints are enforced on the values just read. `(the most-specific of ...)` and `(the most-general of ...)` keep those classes. |
| `som.km.prototypes` | Builds a prototype and clones its participant graph onto an instance. The interpreter and the slot reader are passed in. This namespace does not require either of them. |
| `som.km.unify` | Lazy unification and the constraint check. The interpreter is passed in, so the two can call each other. |
| `som.km.subsumes` | Whether an existing instance matches a description. The store and unification call it through hooks, so this namespace does not require the interpreter. |
| `som.km.taxonomy` | Subclass links stored on the knowledge base, the class test unification uses, and the `(taxonomy)` listing. A class with nothing stored and no built-in link has Thing as its superclass. A built-in superclass slot stays empty until something stores it. The printed tree sorts each level with `string<` on the symbol name. Descending subclasses checks partitions and does not store an unplaced class under Thing. The interpreter is passed in as `km-int`. This namespace does not require the interpreter or the writer. |
| `som.km.errors` | Sentences recorded while reasoning. `:on-error` of abort throws with the knowledge base at the error. |
| `som.km.read` | Turns text into a term. Case is preserved. |
| `som.km.print` | Turns a term into the text `km-format` would write. `format` and `km-format` print `~a`, `~s`, `~%`, `~&`, `~~`, `~d`, and `~nT`. |
| `som.km.term` | Cons cells, symbols, and list shape. The empty list is nil. |
| `som.km.strings` | `explode`, `concat-list`, and `substitute-string`, used by the printer and by English text. |
| `som.km.explain` | Recognizes and removes comment tags and source markers, collapses a `:set` explanation, and builds the KM form a stored explanation prints as. The frame store keeps the records newest first, and it keeps `(comment ...)` text. `(why)` prints the entry and exit lines and that form. `(justify)` omits the subgoal line unless developer mode is on. With `justify-leaves` on, a leaf is one English sentence and can name the class the triple came from. `(get-justification)` returns those lines. `(explain-all)` and `(clear-explanations)` run. |
| `som.km.utils` | List, set, and binding helpers. A proper list is walked strictly. |
| `som.km.kbutils` | Shape tests and `km-equal`. It does not ask whether a name is a class or a slot. |
| `som.km.frame` | The frame store. A knowledge base is a value the caller passes back in. |
| `som.km.stack` | The goal stack and the loop check. Both stacks live on the query. The interpreter pushes goals. |
| `som.km.minimatch` | `minimatch` returns captured pieces. `full-match` returns a binding list. The handler table uses it. |
| `som.km.repl` | The `KM>` prompt. A local situation is shown in brackets and a theory in braces. It holds one session. `q` leaves when the line reads as that symbol. A load that is not silent writes each file's line as that file is read. |
| `som.km.startup` | Starts that prompt after loading the shipped component library and the Springs of MUD library. `startup.sh` and `startup.cmd` run it with `-J-Xmx4g`. |
| `som.km.configured` | Starts that prompt from `src/resources/config.edn`. `clojure -M:configured` reads that file. The `:component-libraries` section is the component-library build `all` from `tools/builds.lisp`, in that build's order, then `som-component-library`. Each directory is loaded through the same `(load-lib)` as the prompt. |
| `som.km.server` | The HTTP service. It holds one session. The handler turns a request into a map and writes the response. |
| `som.kb` | Loads the component library from the Readme under `src/resources/km-component-library`. `load-lib` takes the caller's knowledge base and query. Each `.km` file is one `load-kb`. `:value` is the list of pathname-names. A `.lisp` file is listed on `:lisp` and left unevaluated. Children of one directory are sorted with `string<`. A library caller passes the knowledge base in. `(load-lib)` at the prompt and over HTTP calls the same function through `evaluate`, and the session keeps the returned knowledge base. |

`som.kb/components-path` is the shipped `components` directory. `som.kb/som-components-path` is `src/resources/som-component-library`. `load-lib` walks a directory the way the Readme's `traverse-directory` does: a subdirectory's files are placed in front of the entries already collected, a file is placed in front, and an empty directory is visited as a file. A file named `Thing.km` is probed as the directory `Thing/`. The returned names are consed, so they come back in the reverse of that visit order. The type test is case-sensitive. A missing directory records `No such directory %s!`.

A command name matches its upper-case spelling and its lower-case spelling. A mixed-case name is a different symbol. `(version)` and `(VERSION)` print the banner. `(Version has ...)` is a frame assertion.

The supported component profile is build `all`: `core`, `specs`, `science/shared`, `science/biology`, `science/physics`, `science/chemistry`, and `bsp`, then the Springs of MUD library. `tools/builds.lisp` is the source of that list, and `km-filepath` uses build `all` when no build is named. `chem-halo`, `bio-halo`, `phys-halo`, and the `SME-*` directories belong to other builds. Build `exhaustive` and a walk of the components root load `science/chemistry` together with `science/chem-halo`. Those two directories declare different superclasses for the same electrolyte classes, and together they close the Ionic-Compound-Substance cycle. `load-clib-build` also walks `tools/` and `databases/` for Lisp tooling. This port leaves `.lisp` files unread, and those two directories are not part of build `all`.

`(load-lib)` is evaluated by `som.km.engine/evaluate`, so the prompt, the startup command, the configured startup, and the HTTP service share it. No directory argument loads `components-path`. That walk follows the component Readme and includes every variant under `components`. It is a separate load from build `all`. A string argument is that directory, and a quoted string is unwrapped. `:silent t` and `:silentp t` skip the per-file loading lines. `:silent f`, and a call with no silent flag, record those lines. The prompt writes each one as the file is read. The answer is the list of pathname-names. `evaluate` returns the loaded `:kb` and `:query`, and each front keeps them for the next call. HTTP keeps the lines on `:text` and writes them with the response.

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
| `:text` | Text a command would have printed. Present for the stack inspectors, a trace, a comment, and `(license)`. |
| `:statistics` | The one-line statistics sentence, including its closing newline. Present on a top-level form that ran. Absent on `not-ported`, `empty`, and `read`. |
| `:kb` | The knowledge base to pass on the next call. Absent on a read error. |
| `:query` | The query to pass on the next call. The fail mode, `:on-error`, and the object stack live here. |
| `:incomplete` | On a read error, true when the text is only a prefix of a term. |

The prompt prints `:text`, when it is present, and then `km-format` of `:value`. Nil prints as `nil`. When `:errors` is not empty, the same line ends with `   ; (WARNING: Errors occurred during reasoning)`. When `:statistics` is present, it follows on the next line. A refusal prints `:message`. A line that reads as the symbol `q` ends the prompt and prints nothing. Evaluating `q` answers the list `(q)`, so the leave test uses the term that was read.

The service returns the same map as JSON, without `:kb` or `:query`. A proper list is an array. A symbol, a keyword, a dotted cons, and a ratio are objects. An integer that fits in a long is a number. A larger integer is decimal text. `q` is an expression and does not stop the service.

`status` reports `:evaluator "interpreter"`. A refusal named `not-ported` maps to HTTP 501. A syntax error stays HTTP 200.

## State

The knowledge base is a value. `som.km.frame/knowledge-base` builds an empty one. The caller passes it into the store functions and uses the value they return. It holds the frames, the order they were first stored, the bindings, the gensym counter, the current situation, the situation and theory names, the situation-facet cache, the deleted names, and the runtime flags. A frame has four facets. A facet holds an ordered list of `(slot (value ...))`. In `*Global` the facet name is the facet. In another situation the name is the facet name joined to the situation name.

`reset` clears the frames and rebuilds the built-in vocabulary in the returned value. The classes, the slots, and the instances `t`, `f`, the fluent statuses, and `*Global` are frames. The default fluent status is `*Fluent`. The optimization flags start clear. A non-fluent slot is stored in `*Global` when the caller leaves the situation out. A fact about a prototype participant is stored in `*Global`. The warning the Lisp records for that redirect is not recorded. A theory is recognized when its name is on `:theories`, or when its `instance-of` in `*Global` includes Theory. Visible theories are newest first. Entering a non-global situation that is not a theory turns situations mode on. `reset` rebuilds the runtime, so that mode, the visible theories, and the current situation return to their starting values.

Logging and creation logging start off. Slot checking starts off, and that flag is stored only. While logging is on, each top-level command except `showme`, `undo`, and `why` stores a snapshot on the value before the command runs. `undo` returns to that snapshot, including the done flags. The creation log records new frames. `undo-creations` deletes the anonymous ones and puts the gensym counter back. `store-kb` keeps another snapshot on the same value. `with-morphism` keeps a renaming alist on the value until a later load replaces it. `save-kb` writes UTF-8. A file whose bytes are not UTF-8 is read as ISO-8859-1. Frames are written in groups. Each group, and the comments section, is sorted with `string-lessp`. `(show-comment ...)` stays in stored order. `fastsave-kb` stays refused.

`*verbose-number-to-text*` starts false and `*output-precision*` starts at 3. `*default-km-behavior-for-expand-text*` starts true. `*justify-leaves*` and `*developer-mode*` start false. Tracing, interactive tracing, and the five finer trace switches start off. Comment display starts on. Reset statistics starts enabled. The inference-report frequency starts unset. The trace file starts as `%trace.km`. A `SETQ` of one of these is accepted only inside `load-kb`. `save-kb` does not write them. `reset` restores the defaults. `(trace)` turns tracing and interactive tracing on, clears the five finer switches, and answers `(t)`. It does not read a menu. `(taxonomy)` descending `subclasses` removes a redundant superclass or subclass link, checks partitions, and then prints the tree in `string<` order. The check records a warning and leaves an unplaced class without a stored superclass. A cycle in the class or slot hierarchy is recorded on `:errors` and the walk continues, so `(taxonomy)` still answers `(t)`. An `inherit-with-overrides` climb records the same cycle and stops that branch. A walk called outside an evaluation still throws. A listing on another relation, such as `subslots`, does not clean. The step 14 flags are unchanged.

The query holds the object stack and the goal stack. A goal is the canonical expression, the situation, the expression that was pushed, the inference number, and the target. A unification is recorded under `|all situations|`. `looping-on?` compares the canonical form after bindings are followed. `&+!` stays distinct from `&`. An `or` between a goal and its repeat is still a loop. `reset` clears both stacks. It keeps the list of instances being unified, the inference counters, and the caller's unstackable-instance list. That list starts as `(t)`.

`evaluate` takes the knowledge base and the query, pushes a goal for an expression that reaches the handler table, and returns the answer list. The prompt holds one session for the person at the keyboard. The running service holds one session and locks it, so one request uses that value at a time. Two posts on that service see each other's assertions. The prompt and the service do not see each other. `(reset-kb)` rebuilds the vocabulary and answers `(t)`. `(show-goal-stack)` at the top level shows an empty stack, because the top-level clear runs first. `(show-obj-stack)` shows the frames touched on that query.

A top-level call clears the goal stack, the instances being unified, the depth, the trace depth, and the looping flag, and it resets tracing. It zeroes both inference counters, the Skolem count, the unification count, the classification counts, the maximum trace depth, and the knowledge-base access count, unless reset statistics is disabled. That flag starts true. While it is false, the stacks and the trace depth are still cleared and the counters are kept. It leaves the object stack, the fail mode, and a caller's depth limit. It turns inverse installation on with those counters. While reset statistics is disabled, the caller's inverse flag stays. `load-kb` resets the inference engine after that clear. The counters are zeroed again only when reset statistics is enabled, and inverses are turned on even when the flag is off. A file that writes `(disable-installing-inverses)` after the enable line still reloads with the flag off. A form inside the file that is not ported yet follows `:on-error`. Continue keeps the later forms and answers `(t)`. Abort stops, answers nil, and records the aborted sentence. Either way the load itself ran. `reset` and a direct store leave that flag as it stands. The depth limit starts unset and still uses the depth counter. A query deeper than 400 stops the way a set limit would. The trace indent uses the separate trace depth.

Unification rewrites the caller's knowledge base. `&` and `&!` combine two values and keep the result. `&&` and `&+` merge a pair when the classes stored so far pass the subsumption test. A failed `&&` pair stays in the result. `&?` and `&+?` only test, and the trial is discarded. A lazy result may leave `(_A & _B)` on a slot. The next read of that slot finishes it. A constraint stored with a value is checked on that read. A constraint form by itself still answers nil. `(the Class with ...)` searches instances already stored and records an error when the answer is not one instance. `(the+ Class with ...)` searches and then creates an instance on a miss. An existential that covers a value already on the slot is not stored again. A leftover `(a Class)` in `&&` is created. `(a Class)` creates an anonymous instance and puts it on the object stack. `(every Class has-definition ...)` and `(instance has-definition ...)` store a definition. A slot read, a `has`, a new instance, a written `&`, and a load with `:eval-instances` classify the frame and count the attempt. A prototype applies through that description test. Rule bodies run: `(if ...)` chooses a branch, `allof`, `oneof`, and `forall` walk a collection, `called` keeps tagged values, and `(the Class slot of frame)` keeps values of that class. An instance `also-has` appends values, `also-hasnt` deletes them, and `now-has` replaces them. `(the1 ...)`, `(the2 ...)`, `(the3 ...)`, `(theN ...)`, and `(theNth ...)` read by position. `append` and `reverse` build a sequence. A stored `(no-inheritance)` skips inheritance and subslots, `set-filter` filters, `(sometimes ...)` evaluates its body, a default is applied once, and a deletion writes the inverse of `<>`. A slot read then clones a suitable prototype, then uses the local store, rules inherited from classes, and values on subslots. A clone records `(cloned-from ...)`. `(why)` prints the KM form of that record. `(new-situation)` enters a local situation. `(in-situation ...)` and `(in-theory ...)` run a body and restore the previous situation when the body returns. An abort leaves the temporary situation in force. An inertial fluent projects from the previous situation. Own facts climb supersituations and visible theories. When several sources contribute, the earlier duplicate survives that climb, a looping residue that is not the current goal is evaluated and written back, a second prototype pass joins appending values that share a cloned-from source, pieces of an `&` expression are linked in the situation that was current, and a class with nothing stored has Thing as its superclass while the built-in superclass slots stay empty until stored. Explanation records are stored newest first. A vanished triple on a built-in remove-subsumers or remove-subsumees slot is dropped when two frames are bound, and the bound-away frame stays. `(comment ...)` stores its text, a save writes those user comments in `string-lessp` order, `(why)` prints the entry and exit lines and the rule, and `(justify)` with both flags off omits the subgoal line. With `justify-leaves` on, the English sentence can name the class the triple came from. A situation-local explanation is written back into that situation. A fluent read in `*Global` after situations mode is on records an error. Universal slots, including `instance-of`, stay in `*Global`. One caller uses a given value at a time. Dereferencing follows bindings unless the caller turns it off. Ununification stays off. `:on-error` defaults to continue. Abort returns nil and keeps the knowledge base at the error.

## Test organization

Tests have three classpath roots under `test/`: `component-libraries`,
`inference-engine`, and `agent-goals`. The test alias includes all three;
the Cognitect runner discovers them recursively under `test`. Existing test
namespaces are preserved. [The test index](../../test/README.md) documents
group commands and placement. Component-library tests cover loading, packaging,
configuration, and startup. Engine tests include support functions and the
prompt/HTTP translations. Agent tests cover level goals, area preferences,
command selection, routes, and player-context isolation. Their
[guide](../../test/agent-goals/README.md) follows the conclusion contracts in
[Conclusion Driven Development](ConclusionDrivenDevelopment.md), distinguishes
licensed attempts from observed execution, and identifies coverage gaps.

## Dependencies

`deps.edn` declares Clojure and `org.clojure/data.json` from Maven Central. Tests use the Cognitect test runner. This build resolves Maven through a Nexus mirror of Maven Central. The mirror does not serve Clojars, so Ring is not on the classpath. Replacing the JDK server is a later decision, recorded here when it happens.

## JVM library

The JAR build writes a directory index at
`META-INF/som-knowledge-machine/resources.edn`. `som.km.resource-library`
uses this index to list packaged component directories. `som.kb` preserves the
filesystem walk's order over those entries and passes classloader resource URLs
to `som.km.loadkb/load-file`. The loader retains UTF-8 decoding with the existing
ISO-8859-1 fallback. Resource streams are closed after reading. This works with
Spring Boot's context classloader and nested JAR URLs.

Filesystem directories take precedence. When a directory under `src/resources/`
is absent, `load-lib` resolves it from the resource index. Explicit
`classpath:resources/...` paths select packaged libraries. The default paths
select classpath libraries when the source tree is absent. Configuration entries
and caller-owned session state pass through the same engine entry point.

The Maven artifact `org.springy.som:som-knowledge-machine:0.1.0-SNAPSHOT`
contains the `som.km` Clojure namespaces, the `som.kb` component loader, and the repository license. The JVM
consumer loads `som.km.engine` through Clojure `require`. Its entry points are
`status`, `session`, and `evaluate`. The caller owns each session and carries
the returned `:kb` and `:query` into its next call. `som.kb/load-lib` loads
the component library into that same session. The generated POM declares
the runtime dependencies. The tools.build dependency is scoped to the build alias.

The full notice ships at `META-INF/som-knowledge-machine/LICENSE`. The current
`som.km.license` namespace reads the filesystem at load time. See the
[packaging note](../migration/21-maven-library.md) for the classpath lookup follow-up.

## What the Lisp modules become

The concatenated Lisp file is marked with `;;; FILE:` headers. `src/knowledge-machine/disassemble` is the Perl unpacker taken from that file. Running it writes one source file per header into `src/knowledge-machine/packages/`. Each of those files, except `README.txt`, begins with the `km` package forms the script inserts. How those files fit together is recorded in `src/knowledge-machine/packages/Architecture.md`. The runtime flags, frame layout, and reader macros are recorded in `src/knowledge-machine/packages/Conventions.md`. The port follows those modules in the order listed in `docs/migration/README.md`. Why that order differs from the Lisp load order, and where Clojure will not produce the same result, is recorded in `docs/migration/plan.md`. `compiled-handlers.lisp` stays unported. It is a generated flattening of the same interpreter. `htextify.lisp` is a stub.
