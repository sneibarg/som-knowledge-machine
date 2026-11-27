# Test organization

This maintenance change groups the existing tests by their purpose. It adds no
KM language feature and does not advance the numbered port steps.

`test/component-libraries` covers library traversal, loading, packaged resources,
configuration, and startup. `test/inference-engine` covers engine semantics,
support functions, and adapters. `test/agent-goals` covers level intentions,
progress conclusions, area preferences, known commands, routes, and the
directives they support. Each folder has a README, with commands in the
[test index](../../test/README.md). All 32 test files retain their contents and
namespaces, including all 388 test definitions. The test alias supplies the
three classpath roots; existing full-suite and namespace commands still work.

The agent guide follows [Conclusion Driven Development](../reference/ConclusionDrivenDevelopment.md).
It identifies intentions, evidence ownership, conclusion consumers, context,
selection policy, absence, validity, and verification examples. It distinguishes
a heuristic area preference from an optimum, an empty path from an absent path,
an eligible command from a successful action, and context isolation from cache
invalidation. Execution feedback and conflicting-evidence contracts remain
coverage gaps; gear, practice, and personality remain skeleton components.

No Lisp module is newly ported. The existing engine tests preserve the packaged
Lisp interpreter and its supporting modules; the component loader tests derive
from the component Readme. Agent knowledge is application-specific. Engine
behavior, state ownership, and license text are unchanged.

Run `clojure -M:test`, or select a group with
`clojure -M:test -d test/agent-goals` (substitute either other group).
Validation results are recorded below.

The agent-only command passes 30 tests with 974 assertions, zero failures, and
zero errors. File hashes confirm all 32 test files are unchanged; every agent
test name is documented, and local documentation links resolve.

The full `clojure -J-Xmx4g -M:test` run completed 388 tests with 3,467
assertions, two failures, and zero errors. Both failures concern unchanged
assertions and unchanged resource paths:

- `som.kb-test/load-lib-loads-the-shipped-component-library` expects silent
  output to contain only aborted-load lines, but the shipped library prints
  taxonomy text. Step 27 already records this failure.
- `som.km.startup-test/som-components-path-points-at-the-library` expects
  `Som-Level-Goal.km` directly at the library root. The current library stores
  it under `level/`. This assertion already refers to the old layout.

These failures were retained rather than changing acceptance expectations as
part of the test organization. Logs are in `target/test-organization/`.
