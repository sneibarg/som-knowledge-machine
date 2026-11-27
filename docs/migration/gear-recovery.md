# Gear recovery strategies

The existing gear package now records room, shop, corpse, mobile, and player
observations and derives conditional recovery strategies. It reuses the current
gear piece, report, and goal vocabulary; no item package is created. A confirmed
player snapshot and explicit wanted loadout support proposals through purchases,
intermediate-mob prerequisites, travel, loot, and equipping. Cumulative spending,
reserved funds, compatible worn slots, and reusable carried prerequisites are
accounted for in projected states. Player sightings never authorize acquisition;
examined mobile gear additionally needs confirmed yield and a learned combat
prerequisite model before it can support a strategy.

After death, a new confirmed snapshot replaces actual owned/worn gear and coins.
Fresh requests reject superseded snapshots and ignore stale stored goal-met
claims in favor of current equipment. Predictions are distinct frames and never
install themselves as actual possessions, equipment, or money. The first
proposal still needs live validation and observation before reconsideration.

This is application knowledge following the KM manuals' frame, sequence,
conditional-rule, and fluent-situation semantics. No Lisp module is newly ported;
the interpreter, shipped KM component tree, adapters, and license are unchanged.
Enchanting, live commands, earning purchase money, probabilistic combat/loot,
and general conflict reconciliation remain absent. Search is bounded and does
not exhaust combinations of every alternative prerequisite history.

See the [gear guide](../../src/resources/som-component-library/gear/README.md)
for executable examples, all conclusion contracts, and how to assert/revise
sources and snapshots. Run `clojure -M:test -n som.km.gear-recovery-test`,
`clojure -M:test -d test/agent-goals`, and `clojure -J-Xmx4g -M:test`.
Validation results follow.

Projected histories also track defeated encounter identities. A single mob cannot
be used twice, including when a prerequisite fight consumes the parent's holder.
Explicitly evidenced loot bundles can supply several pieces with one defeat;
any named bundle member can serve a goal. Observation-only worn gear does not
establish either the bundle or a repeat spawn opportunity.

The focused gear suite passes 24 tests with 1,496 assertions and no failures or
errors. The executable guide passes all 21 expressions and four documented
answers. Catalog counts, relative links, and coverage entries were verified.
The full-suite result follows.

The final `clojure -J-Xmx4g -M:test` run completed 425 tests with 5,636
assertions, two failures, and zero errors. Both are unchanged pre-existing
failures recorded in [test organization](test-organization.md):

- `som.kb-test/load-lib-loads-the-shipped-component-library` expects silent
  output to contain only aborted-load lines; the library emits taxonomy text.
- `som.km.startup-test/som-components-path-points-at-the-library` still expects
  `Som-Level-Goal.km` at the library root rather than under `level/`.

The new gear tests and the existing agent, mobile, and route tests pass.
Validation logs are under `target/test-organization/`.
