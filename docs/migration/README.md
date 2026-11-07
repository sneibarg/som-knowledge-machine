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

## Still ahead

The order comes from the call graph in [the migration plan](plan.md). That note also records where Clojure will not produce the same result as the Lisp. `loadme.lisp` is the Lisp load order. It is not this list.

7. Unification and constraints, together.
8. Subsumption, and the redundant-value check that uses it.
9. Inheritance and subslots.
10. Prototypes.
11. Explanations.
12. Situations, actions, theories, projection, and supersituations.
13. Load, save, and undo. `fastsave` stays unported.
14. English text and the taxonomy listing.
15. Trace, statistics, the SADL event-chain walker, and the license text.

`compiled-handlers.lisp` is a generated flattening of the interpreter. The port keeps one handler implementation. `compiler.lisp` is not ported. `htextify.lisp` is a stub.
