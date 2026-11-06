# som-knowledge-machine

A Clojure port of KM, the Knowledge Machine inference engine, version 2.5.45.

The original Lisp source is `src/knowledge-machine/km-2-5-45-packaged.lisp`. The port proceeds one piece at a time. Each finished piece is described in [docs/migration](docs/migration/README.md).

The prompt and the HTTP service are two fronts on one engine, `som.km.engine`. Neither front stores a knowledge base of its own.

## Tests

```
clojure -M:test
```

## Prompt

```
clojure -M:repl
```

The prompt is `KM>`. A line is accepted and is not evaluated yet. `q` leaves the prompt.

## HTTP service

```
clojure -M:server
```

The service listens on `http://127.0.0.1:8080`. Set `PORT` to choose another port.

- `GET /status` returns the build description as JSON.
- `POST /query` takes one Knowledge Machine expression as a `text/plain` body. Evaluation is not ported yet, so a non-empty expression returns status 501 and a JSON explanation.
- `GET /` names those two routes.

## License

Simplified BSD Licence. See [LICENSE](LICENSE). Copyright (c) 1994-2015 Peter Clark and Bruce Porter.
