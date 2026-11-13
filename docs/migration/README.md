# Migration

This directory records each finished step of the port from Knowledge Machine 2.5.45 to Clojure. The notes say what the step produced, in plain English.

The original source is one concatenated Lisp file, `src/knowledge-machine/km-2-5-45-packaged.lisp`. It is marked into the modules Knowledge Machine was built from. Later steps follow those modules.

| Step | Note | Result |
| --- | --- | --- |
| 0 | [Project shell](00-project-shell.md) | A Clojure project with a prompt and an HTTP service. Both call one engine. The engine does not evaluate yet. |
| 1 | [Read and print](01-read-and-print.md) | One expression is read and printed. It is not evaluated. Comment and source tags can be recognized and removed. |
| 2 | [Patterns, lists, and equality](02-patterns-lists-and-equality.md) | Patterns match. Lists and sets can be compared. The prompt still only reads and prints. |
| 3 | [The frame store](03-the-frame-store.md) | Frames, slots, situations, and bindings are stored in a value the caller holds. The prompt still only reads and prints. |
| 4 | [Built-in vocabulary and reset](04-built-in-vocabulary-and-reset.md) | `reset` rebuilds the built-in classes, slots, and instances in the caller's knowledge base. The prompt still only reads and prints. |
| 5 | [The goal stack](05-the-goal-stack.md) | A query records goals and notices a repeated goal. The prompt still only reads and prints. |
| 6 | [The interpreter](06-the-interpreter.md) | Literals, arithmetic, tests, local slot values, and constraint forms run. The prompt and the HTTP service both evaluate. |
| 7 | [Unification and constraints](07-unification-and-constraints.md) | `&`, `&&`, and the other equality operators run. A constraint on a stored value is checked when the slot is read. |
| 8 | [Subsumption](08-subsumption.md) | An existing instance can be matched to a description. A value an existing value already covers is not stored again. |
| 9 | [Inheritance and subslots](09-inheritance-and-subslots.md) | A slot read uses the local store, rules inherited from classes, and values on subslots. |
| 10 | [Prototypes](10-prototypes.md) | `(a-prototype Class)` builds a prototype, and a later slot read clones it onto an instance. |
| 11 | [Explanations](11-explanations.md) | `(why)` prints the KM form of a stored explanation. A class rule, a clone, and `(explanation ...)` can supply one. |
| 12 | [Situations, actions, and theories](12-situations.md) | A local situation, a theory, and an action update the knowledge base the caller holds. An inertial fluent projects from the previous situation. |
| 13 | [Load, save, and undo](13-load-save-and-undo.md) | A knowledge base is saved as KM text and loaded back. Undo restores a snapshot of the value the caller holds. `fastsave` stays unported. |
| 14 | [English text and the taxonomy listing](14-english-and-taxonomy.md) | `make-sentence` and `make-phrase` turn an expression into one string. `(taxonomy)` prints the subclass tree in list order. `(pluralize)` records that it is no longer defined. |
| 15 | [Trace, statistics, the event-chain walker, and the licence](15-trace-statistics-sadl-and-license.md) | `(trace)` records a line for each goal. The counters are reset and printed. `(do-plan)` walks a chain of events. `(license)` prints the repository licence. |

## Still ahead

The planned steps are finished. The order came from the call graph in [the migration plan](plan.md). That note also records where Clojure will not produce the same result as the Lisp. `loadme.lisp` is the Lisp load order. It is not this list.

`compiled-handlers.lisp` is a generated flattening of the interpreter. The port keeps one handler implementation. `compiler.lisp` is not ported. `htextify.lisp` is a stub.
