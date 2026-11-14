# som-knowledge-machine

A Clojure port of KM, the Knowledge Machine inference engine, version 2.5.45.

The original Lisp source is `src/knowledge-machine/km-2-5-45-packaged.lisp`. The port proceeds one piece at a time. Each finished piece is described in [docs/migration](docs/migration/README.md).

The prompt and the HTTP service are two fronts on one engine, `som.km.engine`. Neither front stores a knowledge base of its own.

## Tests

```
clojure -M:test
```

## Maven library

Run these commands from the repository root with the Clojure CLI and the project JDK.

```sh
clojure -T:build jar
clojure -T:build install
```

Set the Maven artifact version in [`VERSION`](VERSION). The build names the JAR
`target/som-knowledge-machine-<version>.jar` and writes the same version into
its POM. The `install` task rebuilds and installs both files under
`org.springy.som:som-knowledge-machine:<version>`. Use the same local Maven
repository in the producer and consumer. If the consumer uses a custom
repository, set the producer's project `:mvn/local-repo` to the same path.

The JAR contains Clojure sources loaded through `require`, and Maven resolves
the runtime dependencies from the POM. See the [packaging note](docs/migration/21-maven-library.md)
for the packaged `(license)` behavior.

### Publish to Nexus

Make the project JDK, Clojure CLI, and Maven available to the Jenkins agent.
Configure a server entry in the agent's `~/.m2/settings.xml` with ID
`nexus-snapshots` and credentials that can deploy to the local Nexus server.
From the checkout root, run this as the Jenkins shell build step:

```sh
sh ./deploy.sh
```

The script reads `VERSION`, builds the JAR, and deploys it with the generated
POM. Versions ending in `-SNAPSHOT` go to
`http://dragon:8089/repository/maven-snapshots/`. A version without that suffix
uses the `nexus-releases` server entry and publishes to
`http://dragon:8089/repository/maven-releases/`. Pass extra Maven options to the
script as needed, for example `sh ./deploy.sh -s /path/to/settings.xml`.

## Prompt

```
clojure -M:repl
```

The prompt is `KM>`. A line is read and printed. It is not evaluated yet. `q` leaves the prompt. An unfinished expression continues on the next line.

## HTTP service

```
clojure -M:server
```

The service listens on `http://127.0.0.1:8080`. Set `PORT` to choose another port.

- `GET /status` returns the build description as JSON.
- `POST /query` takes one Knowledge Machine expression as a `text/plain` body. A term returns status 200 and the printed form. The expression is not evaluated. A blank body or a broken expression returns status 400.
- `GET /` names those two routes.

## License

Simplified BSD Licence. See [LICENSE](LICENSE). Copyright (c) 1994-2015 Peter Clark and Bruce Porter.
