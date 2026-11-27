# som-knowledge-machine

A Clojure port of KM, the Knowledge Machine inference engine, version 2.5.45.

The original Lisp source is `src/knowledge-machine/km-2-5-45-packaged.lisp`. The port proceeds one piece at a time. Each finished piece is described in [docs/migration](docs/migration/README.md).

The prompt and the HTTP service are two fronts on one engine, `som.km.engine`. Neither front stores a knowledge base of its own.

## Tests

```
clojure -M:test
```

See [test/README.md](test/README.md) for component-library, inference-engine,
and agent-goal suites and commands. The [agent guide](test/agent-goals/README.md)
documents conclusion contracts, selection rules, and coverage limits.

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

The prompt is `KM>`. A line is read and evaluated. `q` leaves the prompt. An unfinished expression continues on the next line.

`startup.sh` and `startup.cmd` start that prompt with a 4GB heap and load both component libraries before the first `KM>` line. The shipped library takes several minutes. Some of its files record an error, and the load continues.

```
sh ./startup.sh
```

```
startup.cmd
```

`clojure -M:configured` starts that same prompt from `src/resources/config.edn`. The file is EDN. The `:component-libraries` section is the component-library build `all` from `tools/builds.lisp`, then the Springs of MUD library. Each directory is loaded in the order written, through `(load-lib)`, which walks it recursively. A path in the file is relative to the working directory. A backslash is rewritten to a forward slash. The load does not print a line per file. It prints how many errors that directory recorded, and the prompt keeps the loaded knowledge base. A missing file, or a file that is not this map, stops before the prompt. `(load-lib)` with no directory still walks the whole `components` tree, including the halo and SME variants that build `all` leaves out.

```
clojure -M:configured
```

## HTTP service

```
clojure -M:server
```

The service listens on `http://127.0.0.1:8080`. Set `PORT` to choose another port.

- `GET /status` returns the build description as JSON.
- `POST /query` takes one Knowledge Machine expression as a `text/plain` body. A term returns status 200 and the printed form. The expression is not evaluated. A blank body or a broken expression returns status 400.
- `GET /` names those two routes.

## Component library

The component library shipped with this build is `src/resources/km-component-library/rkf-clib/components`. Load it at the `KM>` prompt. The whole tree takes several minutes and about a gigabyte of heap, so start the prompt with extra memory:

```
clojure -J-Xmx4g -M:repl
```

```
KM> (load-lib :silent t)
```

`(load-lib)` with no directory reads the shipped `components` directory. `:silent t` skips the line for each file. Omit `:silent`, or pass `:silent f`, and the prompt writes a line as each file is read:

```
Loading .../Thing.km...
.../Thing.km loaded!
```

The answer after the load is the list of `.km` names. Some files record an error and the load continues. The prompt then adds `WARNING: Errors occurred during reasoning`. The knowledge base from the files that loaded stays available on the next line.

`(require ...)`, `(def ...)`, and `kb/load-lib` are Clojure. At `KM>` each of those lines is a Knowledge Machine expression and answers nil.

To load one directory, pass its path with forward slashes. A backslash in a Knowledge Machine string is an escape.

```
KM> (load-lib "src/resources/km-component-library/rkf-clib/components/science/physics" :silent t)
```

`:silentp t` is the same flag. A quoted path works: `(load-lib '"src/resources/km-component-library/rkf-clib/components/science/physics" :silent t)`.

A program that calls the loader from Clojure starts with `clojure` and passes the knowledge base in:

```clojure
(require '[som.kb :as kb]
         '[som.km.engine :as engine])

(def session (engine/session))
(def loaded (kb/load-lib (:kb session) (:query session) kb/components-path :silent true))
```

Pass the returned `:kb` and `:query` into the next call. The same call loads one part of the library:

```clojure
(kb/load-lib (:kb session)
             (:query session)
             (str kb/components-path "science/physics")
             :silent true)
```

`:value` is the list of `.km` pathname-names, the file name with the directory and the `.km` suffix removed. `:lisp` lists the `.lisp` paths in the tree. Those files are Common Lisp, and this port leaves them unread. The prompt and HTTP answers include `:value` and leave `:lisp` off the printed result. `.kml` files and every other file type are skipped. The type test is case-sensitive.

Each `.km` file is loaded with `load-kb`, which resets the inference engine at the start of that file. A subdirectory's files are placed in front of the entries already collected. Children of one directory are ordered with `string<`, upper case before lower case. The shipped library holds thousands of `.km` files. A form this port refuses follows the query's `:on-error`. The default records the error on `:errors` and continues with the rest of the library. A file the reader cannot finish records `Loading of ... aborted!` and the loader goes on to the next file. A missing directory records `No such directory` and `:value` is nil.

### Loading libraries from an imported JAR

The JAR includes its configuration, component libraries, and a resource index.
`load-lib` reads packaged files through the thread context classloader, including
when the library is inside a Spring Boot executable JAR. An existing filesystem
directory is loaded directly. A missing `src/resources/...` directory is resolved
against the packaged resources, so the shipped `config.edn` works outside the
checkout. Use `classpath:resources/...` to select packaged resources explicitly.

For example, a JVM caller can load the Springs of MUD library into its own session.

```clojure
(require '[som.km.engine :as engine])
(def loaded
  (engine/evaluate
    "(load-lib \"src/resources/som-component-library\" :silent t)"
    (engine/session)))
```

Pass the returned `:kb` and `:query` into subsequent calls to `evaluate`.
The same expression works at `KM>` and through HTTP. With no directory argument,
`load-lib` uses the shipped KM library in either the checkout or the JAR.

## Springs of MUD component library

Goal-oriented play for Springs of MUD lives in `src/resources/som-component-library`. `(load-lib)` with no argument still reads the shipped library above. Load and query instructions are in that directory's [README](src/resources/som-component-library/README.md).

## License

Simplified BSD Licence. See [LICENSE](LICENSE). Copyright (c) 1994-2015 Peter Clark and Bruce Porter.
