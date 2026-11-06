# Migration

This directory records each finished step of the port from Knowledge Machine 2.5.45 to Clojure. The notes say what the step produced, in plain English.

The original source is one concatenated Lisp file, `src/knowledge-machine/km-2-5-45-packaged.lisp`. It is marked into the modules Knowledge Machine was built from. Later steps follow those modules.

| Step | Note | Result |
| --- | --- | --- |
| 0 | [Project shell](00-project-shell.md) | A Clojure project with a prompt and an HTTP service. Both call one engine. The engine does not evaluate yet. |

## Still ahead

The order comes from the call graph in [the migration plan](plan.md). That note also records where Clojure will not produce the same result as the Lisp. `loadme.lisp` is the Lisp load order. It is not this list.

1. Read and print Knowledge Machine terms, including comment and source syntax.
2. Patterns, lists, and equality, including `km-equal` and which duplicate survives.
3. The frame store: facets, slot order, situations as names, and bindings. Edges that call the interpreter, subsumption, or the object stack stay stubbed.
4. Built-in vocabulary and `reset-kb`.
5. The goal stack and loop detection.
6. The interpreter, in handler groups: literals and structures, arithmetic, tests, local assert and lookup, then constraint forms recorded as data.
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
