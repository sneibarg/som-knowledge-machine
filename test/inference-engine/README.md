# Inference-engine tests

These tests preserve the behavior of KM 2.5.45 and its Clojure engine boundary.
The specification is `src/knowledge-machine/km-2-5-45-packaged.lisp`;
[Architecture](../../docs/reference/Architecture.md) describes the port and
[migration notes](../../docs/migration/README.md) explain completed pieces.
Engine goal-stack entries and KM actions belong here. Agent intentions and
licensed commands belong in [agent-goals](../agent-goals/README.md).

Every file below is under `som/km/` and has namespace `som.km.<name>-test`.

| File | Behavior under test |
| --- | --- |
| `read_test.clj` | KM terms, reader syntax, case, and malformed input. |
| `strings_test.clj` | String explosion, concatenation, and substitution. |
| `utils_test.clj` | Strict list traversal, sets, and bindings. |
| `kbutils_test.clj` | Term shape, KM equality, descriptions, collections, and reserved words. |
| `minimatch_test.clj` | Pattern matching, captures, bindings, and handler lookup. |
| `frame_test.clj` | Frame facets, slots, inverses, bindings, frame creation/deletion, built-in vocabulary, and reset. |
| `stack_test.clj` | Query goals, canonicalization, repeated goals, and loop detection. |
| `engine_test.clj` | Public result maps, errors/refusals, values, and caller-owned sessions. |
| `interpreter_test.clj` | Literals, arithmetic, predicates, assertions, slot reads, constraints, commands, and evaluation depth. |
| `unify_test.clj` | Unification operators, trial versus retained changes, and constraints. |
| `subsumes_test.clj` | Description matching, existential coverage, and search/create behavior. |
| `inheritance_test.clj` | Class rules, overrides, subslots, constraints, implicit Thing, and taxonomy cycles. |
| `prototype_test.clj` | Prototype construction, participants, cloning, and applicability. |
| `explain_test.clj` | Comment/source markers, stored provenance, why/justify, explanation ordering, and removal. |
| `situation_test.clj` | Situation/theory contexts, fluent projection, action add/delete lists, and restoration. |
| `loadkb_test.clj` | KM file load/save, encoding, checkpoints, undo, runtime flags, morphisms, and explanation round trips. |
| `anglify_test.clj` | English phrases, numeric text, name lookup, taxonomy output, and English justification. |
| `trace_test.clj` | Tracing, spypoints, profiling, statistics, version/license text, and event-chain plans. |
| `creation_test.clj` | Anonymous instances, object-stack names, lazy paths, and parts inferred from a Door component fixture. |
| `classify_test.clj` | Definitions, classification triggers, unification, loading, and prototype description tests. |
| `rulebody_test.clj` | Conditional and collection rule bodies, bindings, tagged values, and class-filtered paths. |
| `edit_test.clj` | Append/replace/delete assertions, classification after edits, positional access, and sequences. |
| `flag_test.clj` | Inheritance flags, filters, defaults, inverse installation, and deletion exclusions. |
| `survivor_test.clj` | Duplicate survival, looping residue, clone cycles, appending prototypes, and situation-correct links. |
| `command_test.clj` | Display/evaluation commands, truth queries, formatting, scripts, and universally asserted situations. |
| `repl_test.clj` | Prompt text, multiline input, q, result formatting, and session translation. |
| `server_test.clj` | HTTP routes, status codes, JSON representation, session retention, and socket integration. |

Run `clojure -M:test -d test/inference-engine`, or one namespace with
`clojure -M:test -n som.km.unify-test`. The HTTP integration tests own their
servers. Load/save and trace tests use temporary files. Component files used as
engine fixtures resolve relative to the repository root.
