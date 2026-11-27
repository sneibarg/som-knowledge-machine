# Mobile experience sources

The `mobile` component package records encountered mobs in each agentic
player's situation. A level view can now identify positive current-level
experience evidence, missing observations, reachable sources, and a selected
last-known room and route. Selection ranks observed yield and uses encounter
order for ties. A remembered encounter is not proof of current presence or
safety. Existing fresh-reading hunt rules still govern consider and engage.

This is application knowledge, not another numbered Lisp interpreter port.
It follows the KM user manual's frames, N-to-1 sequences, guarded rules, and
now-has updates, and the situations manual's fluent assertion partitions.
No Lisp module, interpreter code, shipped KM component, or license text changes.

Load the complete Som library, assert encounters and their sequence inside the
player situation, and add `som-mobile-search-from` to a normal level view.
Read `som-mobile-target`, `som-mobile-destination`, and `som-mobile-route` in
that situation. The [package guide](../../src/resources/som-component-library/mobile/README.md)
gives executable query forms, all conclusion contracts, and validity limits.

The caller owns evidence reconciliation and uses new views after updates.
Spawn timing, live command execution, combat outcomes, arbitrary-map route
termination, and general conflicting-evidence handling remain absent.

Run `clojure -M:test -n som.km.mobile-goal-test`,
`clojure -M:test -d test/agent-goals`, and `clojure -J-Xmx4g -M:test`.
The final agent suite passes 43 tests with 1,629 assertions, zero failures, and zero errors. Documentation links, catalog counts, and coverage entries were checked.

Composition exposed an existing route-cache defect: recursive requests were
reused across root searches, retaining paths from an earlier map. The Som route
component now computes a root context (the root frame itself by default) and
passes it to recursive requests through som-route-context-in. Child lookup
includes the derived som-route-context, so it recognizes the root when checking
cycles and does not reuse another search's cached path. Mobile queries create
fresh roots; caching remains within a search. Tests first query a path, change
an exit, and ask from a fresh view with the same endpoints, including an
intermediate-room change. Existing repeated-endpoint requests retain their
listed-exit ordering. No second routing implementation or interpreter change
is introduced.

The full `clojure -J-Xmx4g -M:test` run completed 401 tests and 4,122 assertions,
with two failures and zero errors. These are the same pre-existing failures
recorded in [test organization](test-organization.md):

- `som.kb-test/load-lib-loads-the-shipped-component-library` expects silent
  load text to contain only aborted-load lines; the shipped library also emits
  taxonomy text.
- `som.km.startup-test/som-components-path-points-at-the-library` still checks
  for `Som-Level-Goal.km` at the library root instead of under `level/`.

Both assertions remain unchanged. The new mobile behavior and existing agent
contracts pass together. Validation logs are under `target/test-organization/`.
