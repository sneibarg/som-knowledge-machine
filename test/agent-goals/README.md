# Agent goals and conclusions

This suite documents level goals, explored areas, learned commands, and routes asserted by
[`som/km/som_agent_goal_test.clj`](som/km/som_agent_goal_test.clj), namespace
`som.km.som-agent-goal-test`. Run it from the repository root:

```sh
clojure -M:test -d test/agent-goals
clojure -M:test -n som.km.som-agent-goal-test
```

The organization follows [Conclusion Driven Development](../../docs/reference/ConclusionDrivenDevelopment.md):
start with the intended outcome and the decision, identify the conclusions it
needs, then test forward from evidence to conclusions and licensed attempts.
The contracts below describe existing assertions, including their limits. They
do not claim complete conformance with the methodology.

## Intention, evidence, and ownership

The intention is to reach a target character level under a risk ceiling and an
optional time budget. `Som-Level-Goal` owns the intention: `som-target-level`,
`som-risk-ceiling`, `som-budget-minutes`, and the score cadence. Kind defaults
to `level`; cadence defaults to 15 and can be overridden.

The caller supplies a `Som-Progress-Projection` for one `score`, `death`, or
`view` event. It owns the observations: level, remaining experience and span,
elapsed minutes, prior notch, cooldown, score/save counters, health, position,
exits, area knowledge, room freshness, and ordered mobile readings. Each
`Som-Mobile-Reading` supplies a name, consider outlook, freshness, and player
flag. The tests assert these observations; they do not collect them from a game.

`Som-Goal-View` connects `*Goal` and `*Clock` through `som-goal` and
`som-progress`. Queries derive progress, pace, risk, due observations, and the
licensed rule/directive. `Som-Level-Directive` supplies the proposed attempts.
The external caller owns command execution and the observations returned after it.

Area, command, and route rules own their separate conclusions. A player's
`Som-Agentic-Player` situation owns fluent evidence, bootstrap status, known
commands, and explored rooms. Two players can reuse the same frame names with
different observations and conclusions. Bootstrap completion is an assertion
from the caller, not a conclusion that the bootstrap commands succeeded.

The tested dependency graph is:

```text
goal + projection identity -> clock validity -> usable conclusions
experience observations -> experience used -> fraction -> levels earned
goal + progress + time -> met / deadline / pace
pace + risk ceiling + prior notch + event + cooldown -> next notch
cadence + counters -> score due / checkpoint due
these conclusions + health + room + ordered mobiles + exits
    -> first licensed rule -> directive -> attempts
external execution -> new observations -> next projection and view
```

The last line describes the caller's responsibility; this suite ends at attempts.
It proves neither command execution nor successful progress after an attempt.

## Conclusion contracts

Each row states the question, supporting evidence, and consumer. All answers
apply to the goal and projection connected to this particular view.

| Conclusion | Question, answer, and consumer | Evidence, selection, and limits |
| --- | --- | --- |
| `som-clock-stale` | Does the stored clock belong to this goal? A stale clock prevents a decision from using it. | Projection target is compared with goal target. A different target gives `(t)` and suppresses pace, notch, met, score due, and rule/directive. The tested mismatch is target 4 against goal 5. |
| `som-exp-used`, `som-estimate-overwritten` | Which experience observation supports progress? Fraction consumes the selected value. | A score-page value of 400 replaces an estimate of 900 and marks overwrite `(t)`. Estimate-only uses 900 without that marker. |
| `som-fraction`, `som-span-reading`, `som-levels-earned` | How much progress does this reading support? Pace consumes progress. | Remaining experience and stored span establish a fraction; 400 remaining of 1000 gives `3/5`, equal to 0.6. The first observed span is retained even when first seen mid-level, marked `first-reading-counted-as-width`. A zero span yields no fraction or span marker. These are observation-relative values, not proof of a full level's original width. |
| `som-met` | Has this goal been met? Rule selection consumes this answer. | Current level reaching target, or stored `som-met-in = t`, supports `(t)`; level 4 against target 5 without the flag has no answer. A stale target suppresses the conclusion. |
| `som-pace`, `som-deadline-missed`, `som-pace-withheld` | Is progress sampling, behind, on, ahead, or open? Risk adjustment and hunt policy consume pace. | Budget, elapsed time, progress, score count, and met state qualify the result. First score samples. Missing or zero budget is open. Tested pace-band boundaries are on. An exhausted unmet budget is behind and marks deadline missed without requiring division by remaining time; a met goal has no pace or missed-deadline marker in that scenario. |
| `som-notch`, `som-notch-moved`, `som-cooldown-next` | What risk setting does this event support? Hunt policy consumes the setting; the caller carries it forward. | Behind raises cautious to steady to bold, bounded by the ceiling. Ahead drops one step. Death resets to cautious and starts cooldown 30, including death while already cautious. Cooldown blocks a tested behind-score raise. An open budget sets the ceiling at the first score and does not automatically restore it after death. A missed deadline can select the ceiling. |
| `som-score-due`, `som-checkpoint-due` | Is a new score or save needed? Directive rules consume these flags. | Cadence 15 is due at 15 steps, not 14; forced score or zero scores also makes score due. A second score with zero steps is not due. Zero saves makes checkpoint due; one save does not. A stale clock suppresses both. |
| `som-explored-area`, `som-fitting-area`, `som-optimal-area` | Which known explored area fits this level? A consumer may use it as an area preference. | Caller-owned explored flags and bounds filter the projection's area sequence. Highest lower bound wins, then lowest upper bound, then caller order. Missing bounds are excluded. Nil means no supported choice among supplied areas. The name "optimal" denotes this heuristic ranking, not a measured optimum in experience or travel time. It does not license a directive or supply a route. |
| `som-command-heading`, `som-command-allowed`, `som-command-for-goal` | Which learned commands serve the asked command goal? Exploration consumes the command catalog. | Bootstrap owns the player's command sequence. Stored category overrides the SUMMARY fallback. Forbidden names are excluded; remaining matches preserve bootstrap order. Known goals with no matches can return an empty `:seq`. Unknown headings give no answer. Category membership establishes catalog eligibility, not success in the game. |
| `som-exploration-attempt` | Which exploration attempts may rules 10 and 12 send? The directive consumes them. | Rule 10 filters untried exits to known allowed movement commands in exit order. Rule 12 uses known recall, then known where; a single available command is one `:args`, neither is an empty `:seq`. No area choice or path is required. |
| `som-route-exits` | Which listed exits connect two explored rooms? A route consumer receives exit objects. | The first path follows listed exit order within the player's explored rooms; a visited-room cycle is skipped. Same origin/destination yields an empty `:seq`; no discovered connection gives nil. Open/unlock requirements remain metadata, so a found path does not establish that it is immediately traversable. A changed map is queried using a new route. |
| `som-licensed-rule` | Which policy rule wins for this evidence? The directive depends on this selection. | First matching rule wins. The table below lists asserted examples. Ordered mobiles retain projection order; the suite does not establish an optimal target search. Rules 1 and 14 can be selected without a directive. |
| `som-licensed-directive`, `som-attempts`, `som-directive-role`, `som-allow-social` | Which attempt, sequence, or hold is licensed? The external executor consumes it. | Attempts use `(:args role category command argument)` or a `:seq`. Every tested non-yield directive forbids social behavior with `no`. An empty `(:seq)` is a valid hold. Nil directive means yield/no licensed directive, and does not establish that no possible action exists. |

Nil results require their slot context: not yet met, no due flag, stale evidence,
an unusable span, and a policy yield are different meanings. The helpers assert
an empty `:errors` collection alongside expected values or nil. A reasoning
error therefore cannot silently pass as an expected absence. An empty attempt
sequence must remain distinct from a missing directive.

## Decisions supported by the conclusions

The examples below are the `testing` cases within
`the-directive-licenses-the-first-matching-rule`. Rule numbers are observable
answers from the component rules, not test execution order.

| Rule | Tested evidence and supported decision | Expected attempts |
| --- | --- | --- |
| 1 | Target met with no gear gate: yield. | No directive. A supplied gear gate lets the tested fresh-mobile case fall through to rule 9. |
| 2 | Score is due. | `(:args survey "information / communication" score "")` |
| 3 | Areas unknown after a score. | Sequence of `areas` and `where` surveys. |
| 4 | Fighting at the tested missed health line: escape. | `(:args escape combat flee "")` |
| 7 | Low health outside combat: rest; healthy but resting: stand. | `(:args recover movement rest "")` or `(:args recover movement stand "")` |
| 8 | A reading lacks consider evidence, including a player before a safe goblin: investigate. | A `consider` survey for the first such reading. This establishes a request for evidence, not that the target is safe to fight. |
| 9 | Fresh safe mobile evidence supports engagement. | `(:args engage combat kill goblin)`; two eligible mobiles choose the first (`alpha`). |
| 10 | Untried north exit with steady risk, or cautious while behind, including exhausted budget. | Sequence containing `(:args travel movement north "")` when north is a learned allowed movement command. |
| 11 | Repop room while on pace: hold; stale room: observe. | Empty `(:seq)` with role `hold`, or `(:args survey objects look "")`. |
| 12 | Cautious and on pace with an untried exit: recall and locate. | Sequence of `(:args travel movement recall "")` and a `where` survey when both commands are known. |
| 13 | Checkpoint due. | `(:args checkpoint other save "")` |
| 14 | Idle view after saving, or fighting without a missed health line and without mobiles. | No directive. Missing maximum health in the tested fighting case also yields. |

Rules 5 and 6 are intentionally absent from the component policy. The table
records tested branches; it does not claim exhaustive coverage of every input.
`expect-attempts` also rejects these words in every checked attempt:
`practice`, `train`, `eat`, `drink`, `follow`, `group`, `kick`, `cast`,
`backstab`, `disarm`, `rescue`, `wimpy`, `quit`, `delete`, `murder`, `steal`,
and `password`. The source-contract test separately checks the directive text.

## Verification examples and validity

| Contract or change | Named tests |
| --- | --- |
| Goal defaults and override | `a-level-goal-defaults-kind-and-cadence` |
| Sampling, exact fractional progress, retained observed span, and zero span | `the-first-score-is-still-sampling`; `a-fraction-of-three-fifths-matches-six-tenths`; `a-mid-level-span-is-not-rewritten`; `a-zero-span-does-not-divide` |
| Goal completion | `met-is-the-target-or-the-stored-flag` |
| Behind/ahead risk changes and boundary selection | `pace-behind-raises-one-step-and-stops-at-the-ceiling`; `pace-boundaries-are-on`; `pace-ahead-drops-one-step` |
| Death feedback and cooldown | `a-death-lands-on-cautious-and-starts-the-cooldown` |
| Open budget and exhausted budget | `an-open-budget-sets-the-ceiling-once`; `omitted-minutes-and-asserted-zero-are-open`; `a-used-up-unmet-budget-is-behind-without-a-quotient` |
| Stronger observation supersedes estimate | `a-score-page-replaces-an-experience-estimate` |
| Changed target invalidates the clock | `a-restored-clock-with-a-different-target-is-stale` |
| Cadence, forced observations, and saves | `score-due-and-checkpoint-due-follow-the-counters` |
| Selection and attempts | `the-directive-licenses-the-first-matching-rule` |
| Library composition, supported forms, and vocabulary isolation | `som-agent-loads-the-component-library`; `the-component-text-does-not-use-refused-forms`; `loading-core-goal-does-not-change-the-som-answer` |
| Player contexts and bootstrap evidence | `one-situation-per-agentic-player-keeps-its-own-answers`; `a-completed-bootstrap-stays-in-that-players-situation` |
| Area ranking, missing bounds, no candidates, and context | `an-explored-area-inside-the-level-range-is-optimal`; `an-explored-area-stays-in-that-players-situation` |
| Command categories, filtering, attempts, and context | `known-commands-serve-the-asked-goal`; `exploration-follows-the-known-commands`; `a-players-commands-stay-in-that-situation` |
| Route order, cycle, empty path, no connection, prerequisites, changed map, and context | `exits-to-a-destination-follow-the-listed-order`; `a-players-rooms-stay-in-that-situation` |
| Independent projection contexts | `a-second-scenario-does-not-see-the-first-clock` |

The fixture loads the library once into an immutable base. `project` starts each
scenario from that base, then strictly reduces assertions through the returned
knowledge base and query. `*Goal`, `*Clock`, and `*View` can be reused without
sharing a previous scenario's facts. `project-from` adds the core Goal library
to test composition without changing the Som answer. Additional tests reuse frame names inside two player situations and verify
independent goals, bootstrap state, areas, commands, and routes. This is context
separation; it does not verify invalidation of cached answers after editing an existing view.

A new goal, target, observation, budget, risk constraint, or rule policy can
require reconsideration of dependent conclusions. Current tests cover a target
mismatch, alternative estimates, death/cooldown, and separate projections. Most
comparisons construct independent scenarios; they do not simulate a live event
loop carrying every output into the next event.

## Required inputs and coverage still absent

The tests load the 44 `.km` files under `src/resources/som-component-library`,
including its nine inference-chain folders, and the shipped core `Goal.km`.
The library composition checks assert the vocabulary, inverses, fluent slots,
and independence from the core Goal/Event model. The gear, practice, and
personality classes are skeletons; declaring them does not establish goal behavior.
See the [component architecture](../../docs/reference/som-component-architecture/README.md)
and its [object catalog](../../docs/reference/som-component-architecture/objects.md)
for the full vocabulary and rule ownership.

The suite does not yet establish conflict outcomes for contradictory facts,
general incomplete-evaluation reporting, complete missing-evidence coverage,
dependency/cache invalidation within one evolving view, provenance linking a
licensed action to all its supporting conclusions, or execution feedback after
command success, refusal, or failure. Route tests exercise a cycle and a changed
map with a new route; they do not prove termination for every recursive input.
The suite does not verify repeated-attempt policy or externally observed
completion. Gear recovery scenarios are documented below. Practice and social goals still have no behavioral scenarios here.

For a new agent goal, state the intention and consumer first, then define each
required conclusion using all eight contract elements in the reference document.
Add supported, absent, uncertain, and conflicting examples; test changed evidence
and constraints; verify selection and observation after execution where execution
is in scope. Record remaining gaps explicitly rather than treating a licensed
attempt as proof of the desired outcome.

## Remembered mobile conclusions

`som/km/mobile_goal_test.clj` (`som.km.mobile-goal-test`) tests the
[mobile conclusion contracts](../../src/resources/som-component-library/mobile/README.md)
from intention through encounter evidence, experience sources, reachable
locations, target selection, and routes. Run
`clojure -M:test -n som.km.mobile-goal-test`.

| Named test | Contract and limit |
| --- | --- |
| `mobile-vocabulary-loads-with-fluent-player-owned-relations` | Loader, fluent declarations, and inverse relations. |
| `positive-experience-requires-an-identified-nonplayer-and-current-level-evidence` | Positive evidence, zero/negative results, players, unknown classification, and mismatched level. |
| `missing-evidence-is-an-investigation-question` | Unmeasured, outdated, unclassified, and unlocated records remain distinct from negative observations. |
| `target-selection-ranks-reachable-yields-and-keeps-encounter-order-on-ties` | Reachability, yield ranking, stable ties, and door prerequisites. |
| `an-empty-route-is-a-supported-arrival-and-not-a-missing-path` | Same-room empty path is a supported result. |
| `a-last-room-outside-the-explored-map-is-not-reachable` | Evidence of gain does not establish a known route. |
| `no-records-and-no-route-context-have-different-results` | Empty evidence set versus missing search context. |
| `inactive-or-incomplete-level-goals-do-not-select-mobiles` | Met, stale, wrong-kind, missing, and incomplete intention/context. |
| `a-new-level-needs-new-experience-evidence` | Level change invalidates past experience evidence for selection. |
| `a-new-view-reconsiders-replaced-evidence-and-a-changed-map` | Reconciliation with now-has and a fresh view, including the same route endpoints. |
| `a-new-view-reconsiders-an-intermediate-route-change` | Cached child routes also reconsider changed exits. |
| `players-keep-their-mobile-evidence-and-conclusions-separate` | Shared frame names with independent player assertions and answers. |
| `prompt-and-http-query-the-same-mobile-conclusion` | Both adapters expose the same inference through evaluate. |

The selected target is a last-known source to investigate, not permission to
attack. Tests do not execute movement/combat or prove a measured future gain.
The caller supplies fresh observations and reconsideration after action.

## Gear recovery strategies

`som/km/gear_recovery_test.clj` (`som.km.gear-recovery-test`) tests the
[gear contracts](../../src/resources/som-component-library/gear/README.md).
Run `clojure -M:test -n som.km.gear-recovery-test`.
The scenarios cover sources, conditional planning, money/equipment transitions,
death, incomplete evidence, bounded refusals, isolation, and both adapters:

- `a-room-piece-produces-a-proposal-without-changing-observed-ownership`.
- `a-purchase-debits-the-projected-purse-only`.
- `a-shop-and-intermediate-mob-chain-enables-stronger-gear`.
- `corpse-loot-is-distinct-from-examined-player-and-mobile-equipment`.
- `prices-and-the-emergency-reserve-bound-purchases`.
- `cumulative-purchases-use-one-purse-and-select-supported-cheaper-options`.
- `shared-intermediate-gear-is-not-purchased-twice-and-conflicting-weapons-are-reequipped`.
- `ancestors-reserve-their-purchase-cost-while-obtaining-prerequisites`.
- `current-gear-and-empty-goals-have-valid-empty-or-equip-only-strategies`.
- `incompatible-final-slots-are-rejected-but-paired-slots-are-distinct`.
- `unusable-or-restricted-gear-does-not-become-a-viable-target`.
- `cycles-and-transition-limits-produce-bounded-refusals`.
- `known-unavailable-or-unpermitted-sources-do-not-authorize-acquisition`.
- `mobile-loot-requires-current-level-models-allowed-risk-and-a-nonplayer`.
- `travel-reuses-the-route-chain-and-updates-only-the-projected-room`.
- `death-discards-lost-equipment-and-replans-through-an-affordable-intermediate`.
- `incomplete-inconsistent-and-unsupported-inputs-have-domain-results`.
- `player-situations-isolate-sources-purses-and-regearing-results`.
- `prompt-and-http-expose-the-same-regearing-conclusion`.
- `contradictory-worn-slots-and-unknown-target-slots-have-distinct-results`.
- `predicted-equipment-is-not-a-confirmed-observation`.
- `one-mob-cannot-be-defeated-twice-but-an-evidenced-loot-bundle-can-supply-two-pieces`.
- `a-prerequisite-fight-cannot-consume-the-mob-needed-by-its-parent`.
- `any-explicitly-evidenced-piece-in-a-loot-bundle-can-serve-the-goal`.

Every engine result is checked for reasoning errors. Strategies and projected
results are checked separately from unchanged observed ownership/purse. The
multi-mob example requires a shop weapon and successive intermediate weapons;
the multi-goal example reuses and re-equips one purchased prerequisite. These
tests do not claim live combat success, global optimality, or exhaustive search
over every prerequisite history.
