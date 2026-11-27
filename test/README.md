# Tests

Run commands from the repository root with the Clojure CLI and the project JDK.
All suites use `clojure.test` and the Cognitect test runner.

| Folder | What belongs here | Run this group |
| --- | --- | --- |
| [component-libraries](component-libraries/README.md) | Library traversal, loading, packaging, configuration, and startup integration. | `clojure -M:test -d test/component-libraries` |
| [inference-engine](inference-engine/README.md) | KM language and inference semantics, engine support functions, and prompt/HTTP translations. | `clojure -M:test -d test/inference-engine` |
| [agent-goals](agent-goals/README.md) | Application intentions, evidence-supported conclusions, and the directives they license. | `clojure -M:test -d test/agent-goals` |

Run everything with `clojure -M:test`. The runner searches `test` recursively;
`deps.edn` puts each group on the test classpath. Namespaces retain their existing
names, so commands such as `clojure -M:test -n som.km.engine-test` still work.
Keep a namespace in only one group. New test paths within a group must match
their namespace, for example `som/km/engine_test.clj` for `som.km.engine-test`.

Classify a test by the behavior it establishes. A KM action or interpreter goal
stack is engine behavior; an agent's desired level and choice of a command are
application behavior. An engine regression may use a component file as a fixture
without becoming a component-library acceptance test.

The component suite loads the shipped library and can take several minutes and
substantial heap. Use `clojure -J-Xmx4g -M:test` if the default heap is insufficient.
The startup and agent suites load `src/resources/som-component-library`.
The agent README records the current conclusion contracts and their limits.
