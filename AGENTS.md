# AGENTS.md

## Project Direction

Build a faithful, scalable, and maintainable port of KM, The Knowledge Machine, inference engine 2.5.45.

The Lisp source in `src/knowledge-machine/km-2-5-45-packaged.lisp` is the specification. The Clojure program accepts the same knowledge bases and answers the same questions. Preserve the query language, the frame and slot model, inheritance, unification, constraints, prototypes, explanations, and case. Preserve the `KM>` prompt and the `q` leave command. Keep the Simplified BSD Licence and the Clark and Porter copyright with the port.

Scalable means the engine is a library and its state is explicit. The prompt and the HTTP service are adapters. Each holds its own knowledge base value, so more than one session can exist without a process-wide global store. One knowledge base value is used by one caller at a time. Concurrent use of a single knowledge base waits for a step that defines it.

Maintainable means the port follows the Lisp module boundaries, one piece at a time, in clear Clojure. Each finished piece is described in plain English. There is one implementation of each behavior. `compiled-handlers.lisp` is a generated speed flattening of the interpreter. Port the interpreter, and leave that generated file as reference.

## Reference

Lasting information about this system lives in `docs/reference/`. Read [docs/reference/Architecture.md](docs/reference/Architecture.md) before changing structure, public functions, or the boundary between the engine and its adapters. When a change alters that picture, update the document in the same change.

The step-by-step record of the port lives in [docs/migration/README.md](docs/migration/README.md). Read it before starting a step.

The Lisp file is one concatenation. A line `;;; FILE: name.lisp` marks an original module. The license text is in `LICENSE`. The `README` text file has details about how to run KM. The split files are stored in packages.

## Coding Conventions

Build this as a functional Clojure application.

- A function takes its inputs as arguments and returns its result as a value. The usual function is pure: the same arguments produce the same result, and the function leaves the world unchanged.
- Use immutable data. Maps, vectors, and sets are the ordinary collections. Thread values through the call. When data changes, return a new value.
- Name a transformation and compose it with the next one. A long function that mixes reading input, deciding, and writing output gets split along those seams.
- Keep effects at the edges. The prompt and the HTTP service perform I/O. Engine code takes data and returns data.
- The knowledge base is the stateful core, because unification rewrites frames. Hold that state in one value the caller passes in. Update it through functions that take the knowledge base as an argument.
- Keep lazy sequences away from knowledge-base updates. A lazy sequence that changes the store when it is later realized races every other caller. Use `loop`/`recur`, `reduce`, or another strict traversal for work that reads or writes the store.
- Pass context as an argument. A dynamic var is for a value that is truly stack-scoped, such as a tracing flag around one call. Say that at the definition.
- Prefer functions to macros. A macro is warranted when the caller must control whether an argument is evaluated.
- Add a protocol, multimethod, or record when a real variation is in the code. A single implementation stays a function and a map.
- Keep namespaces small and focused under `som.km`. Alias them with a short prefix. Use kebab-case. Predicates end in `?`.
- A public function has a docstring that says, in plain English, what it returns.
- Domain results are maps with keyword keys, as `som.km.engine/evaluate` returns. An empty expression or a refusal is a result map. An exception is for a broken invariant or an unexpected failure. Adapters format the result map. They do not invent a second result shape.
- Test behavior with `clojure.test`. Test the engine directly, and test each adapter's translation to and from the engine. A test that opens a socket starts and stops its own server.
- A comment says why, and only where the code cannot. In particular, comment a behavior preserved from the Lisp that would look accidental in Clojure.
- Dependencies are declared in `deps.edn` and resolve from Maven Central. The build mirror does not serve Clojars. A Clojars library waits until the mirror can resolve it, and that decision is recorded in `docs/reference/Architecture.md`.

## Change Discipline

- Take one migration step at a time. The order is the table in `docs/migration/README.md`.
- Finish the step with a plain-English note in `docs/migration/`. The note says what the piece is, what a person can do now, which Lisp files it comes from, what is still absent, and how to try it. Add the step to the index.
- Update `docs/reference/Architecture.md` when the step changes the structure, the public functions, or the way state is held.
- Keep the observable Lisp behavior. Where the Clojure expression of a function is clearer than the Lisp control flow, keep that behavior and describe the difference in the migration note.
- Cover the new behavior with tests. Run `clojure -M:test` and see it pass before treating the step as done.
- A behavior the engine gains is reachable from the prompt and from HTTP through the same engine function.
- Leave code, docs, and license text outside the step as they are.
- The port remains under the Simplified BSD Licence in `LICENSE`.
