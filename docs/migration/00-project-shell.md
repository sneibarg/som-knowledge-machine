# Step 0: Project shell

The repository is now a Clojure project. It can start a `KM>` prompt, and it can start an HTTP service. Both of them call the same function. That function does not evaluate a Knowledge Machine expression yet.

## What you can do now

Run the tests:

```
clojure -M:test
```

Start the prompt:

```
clojure -M:repl
```

The session opens with the Knowledge Machine version, 2.5.45, and the original copyright. The prompt is `KM>`. Type a line and the program answers, in English, that it accepted the text and did not evaluate it. `q` ends the session. That is the same leave command as the Lisp read-eval-print loop in `interpreter.lisp`. A capital `Q` is not the leave command, because Knowledge Machine keeps case.

Start the service:

```
clojure -M:server
```

It listens on `http://127.0.0.1:8080`. `PORT` chooses another port. Three routes answer:

- `GET /` names the other two routes.
- `GET /status` returns the build: the name, the Knowledge Machine version, the license, and the two interfaces, `repl` and `http`.
- `POST /query` takes the expression as plain text (`Content-Type: text/plain`, or no content type). A blank body returns status 400. Any other text returns status 501 and the same refusal the prompt prints. A JSON body returns status 415, because the expression is text, not a JSON object. An unknown path returns status 404.

`q` sent to `POST /query` does not stop the service. Leaving is a prompt command. The service has no session to leave.

## How the two fronts share one engine

`som.km.engine` is the library. `som.km.repl` and `som.km.server` are adapters.

`evaluate` takes one string and returns a map:

- `:ok` is true only when there is an answer. It is never true in this step.
- `:error` names the refusal: `empty` or `not-ported`.
- `:message` is the sentence a person should read.
- `:input` is the text after trimming, when the caller sent some.
- `:value` will hold the answer once evaluation exists. It is absent for now.

The prompt prints `:message`, or `:value` when an answer exists. The service returns the whole map as JSON and chooses the HTTP status from `:error`: 400 for `empty`, 501 for `not-ported`, 415 for a body that is not plain text, 200 for an answer.

There is no knowledge base in this step, so there is nothing for the two fronts to share or to keep apart. When the knowledge base arrives, it will be a value the caller holds. A prompt session will hold one. The service process will hold one. They will see each other's assertions only if a later step runs them on the same value on purpose.

## Where the HTTP server comes from

The service uses the HTTP server in the JDK (`com.sun.net.httpserver.HttpServer`). The request is turned into a Clojure map, `som.km.server/handler` returns a response map, and the server writes that response.

Ring would be the usual Clojure HTTP stack. Ring is published on Clojars. This machine resolves Maven artifacts through a Nexus mirror of Maven Central, and that mirror does not serve Clojars, so a Ring dependency does not resolve here. The handler stays a plain function. A later step can place Ring, or another server, in front of that function without changing the routes or the engine.

The service binds to `127.0.0.1` only.

## Lisp files this step used

No Knowledge Machine behavior was ported. The leave command `q` is taken from `km-read-eval-print` in `interpreter.lisp`. The version string `2.5.45` and the copyright years are taken from `header.lisp` and the license text at the top of the concatenated source. The license is copied into `LICENSE`.

## What is still absent

Reading a Knowledge Machine expression. Frames, slots, and situations. Loading a knowledge base. Inheritance, unification, constraints, prototypes, and explanations. Trace output, statistics, and the English writer. The `(license)` command. A real answer from either front.
