# Architecture

som-knowledge-machine is a Clojure port of KM, The Knowledge Machine, inference engine 2.5.45. The specification is the Lisp source in `src/knowledge-machine/km-2-5-45-packaged.lisp`. This document is the map of the port. The history of each finished step is in `docs/migration/`.

## Shape

The engine is a library. Two adapters sit on it. Neither adapter stores a knowledge base of its own.

```
line of text        som.km.repl     som.km.engine/evaluate     printed text
HTTP request        som.km.server   som.km.engine/evaluate     JSON response
```

| Namespace | Role |
| --- | --- |
| `som.km.engine` | Answers a question. Returns a result map. |
| `som.km.repl` | The `KM>` prompt. `q` leaves the prompt and is not sent to the engine. |
| `som.km.server` | The HTTP service. Turns a request into a map, calls the handler, and writes the response. |

`som.km.server/handler` is an ordinary function from a request map to a response map. The JDK HTTP server (`com.sun.net.httpserver.HttpServer`) is the socket in front of that function. The service listens on `127.0.0.1`, port `8080` unless `PORT` is set.

| Method and path | Behavior |
| --- | --- |
| `GET /` | Names the other routes. |
| `GET /status` | Returns the build description from `som.km.engine/status`. |
| `POST /query` | Submits the body as Knowledge Machine text. The body is `text/plain`, or it has no content type. |

HTTP status comes from the result: `200` when `:ok` is true, `400` for `empty`, `501` for `not-ported`, `415` for a body that is not plain text, `404` for an unknown route.

## Result map

`som.km.engine/evaluate` takes one string and returns a map.

| Key | Meaning |
| --- | --- |
| `:ok` | True only when the engine produced an answer. |
| `:error` | A short name for the refusal, present when `:ok` is false. |
| `:message` | The sentence a person should read. |
| `:input` | The trimmed text, when the caller sent some. |
| `:value` | The answer, present when `:ok` is true. |

The prompt prints `:value` when there is an answer, and `:message` otherwise. The service returns the whole map as JSON.

Evaluation is not ported yet. A blank string returns `:error "empty"`. Any other string returns `:error "not-ported"`.

## State

There is no knowledge base yet. When it arrives, it will be a value the caller holds and passes into the engine. The prompt session holds one value. The service process holds one value. They see each other's assertions only when a step runs them on the same value on purpose.

Unification in Knowledge Machine rewrites frames. That state stays inside the knowledge base value. One caller uses a given value at a time.

## Dependencies

`deps.edn` declares Clojure and `org.clojure/data.json` from Maven Central. Tests use the Cognitect test runner. This build resolves Maven through a Nexus mirror of Maven Central. The mirror does not serve Clojars, so Ring is not on the classpath. Replacing the JDK server is a later decision, recorded here when it happens.

## What the Lisp modules become

The concatenated Lisp file is marked with `;;; FILE:` headers. `src/knowledge-machine/disassemble` is the Perl unpacker taken from that file. Running it writes one source file per header into `src/knowledge-machine/packages/`. Each of those files, except `README.txt`, begins with the `km` package forms the script inserts. How those files fit together is recorded in `src/knowledge-machine/packages/Architecture.md`. The runtime flags, frame layout, and reader macros are recorded in `src/knowledge-machine/packages/Conventions.md`. The port follows those modules in the order listed in `docs/migration/README.md`. Why that order differs from the Lisp load order, and where Clojure will not produce the same result, is recorded in `docs/migration/plan.md`. `compiled-handlers.lisp` stays unported. It is a generated flattening of the same interpreter. `htextify.lisp` is a stub.
