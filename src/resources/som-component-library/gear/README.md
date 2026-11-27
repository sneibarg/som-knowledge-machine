# Gear observations and re-gearing

This package records studied gear and its sources, and derives a conditional
strategy for equipping a requested loadout. It extends the existing
`Som-Gear-Piece` and `Som-Gear-Goal` vocabulary. Room pickups, shop purchases,
corpse loot, and gear obtained by defeating intermediate mobs can contribute
to a strategy. Examining gear on another player or mobile establishes an
observation, not ownership or permission to take it.

Load the complete `src/resources/som-component-library` using `(load-lib)`.
The package uses player situations, existing mobile identity/classification,
and the [route chain](../route/README.md). Queries run through the same engine
from the prompt and HTTP. There is no separate item package.

## Evidence and ownership

Assert facts inside the agentic player's `Som-Agentic-Player` situation.
Every package slot is fluent. Two players can use the same frame names while
keeping their observations, purses, and planning results separate.

| Record | Caller-owned evidence |
| --- | --- |
| `Som-Gear-Piece` | Existing description, keyword, worn slot/index, level, comparison, and alignment fields, plus `som-gear-usable`. |
| `Som-Gear-Report` | Existing speaker, raw text, and claims. A report is provenance, not an acquisition opportunity. |
| `Som-Gear-Source` | Source kind, item, room, holder, price, availability, permission, access assessment, and any gear prerequisites. |
| `Som-Gear-State` | A complete observed owned/equipped loadout, purse, room, character level, optional alignment side, and confirmation flag. |
| `Som-Gear-Goal` | Action `regear` or `replace`, wanted loadout, and optional acquisition risk ceiling. Legacy enchant intentions remain stored but are not planned. |

Use stable gear identifiers chosen by the caller. The planner treats each wanted
identifier as one piece to obtain and equip, with any indexed source as a known
way to obtain that piece. It does not infer equivalence from display names.
Use separate identifiers and slot indices for separate pieces needed together,
such as two rings. Quantities, interchangeable-item matching, and automatic
statistic-based gear ranking are not implemented.

`som-gear-usable = t` is an affirmative assessment for this player, not an
inference from seeing another character wear the item. Missing or false
assessments prevent a proposed equip step. Known level refusals, alignment
refusals, object levels above the character's level, and rejected alignments
also block equipping. These checks consume existing gear fields; they do not
invent a combat or item-score formula. The caller maintains assessments when
level, class, skills, alignment, or other relevant conditions change.

## Record sources without inventing ownership

The player holds one ordered `som-known-gear-source` sequence. Each source has
`som-gear-source-item`, `som-gear-source-room`, and existing `som-holder`
identifying the room, seller, corpse, mobile, or player. An optional
`som-gear-source-report` references a `Som-Gear-Report`.

| Source kind | Additional evidence needed to propose acquisition |
| --- | --- |
| `room` | Available, permitted pickup with assessed access. Proposed action is `take`. |
| `shop` | Available, permitted purchase, assessed access, a seller, and a known nonnegative price. Proposed action is `buy`. |
| `corpse` | Available, permitted loot, assessed access, and a corpse holder. Proposed action is `loot`. This can recover the player's own lost gear when the corpse remains accessible. |
| `mobile` | Available and permitted opportunity, assessed access, explicit nonplayer classification on the holder, known item yield, a supported conditional combat model, an explicit gear-prerequisite sequence, matching character level, and allowed risk. Proposed action is `defeat-loot`. |
| `player` | Observation only. It is never an acquisition candidate, even if other flags are set. |

The common flags are `som-gear-source-available`,
`som-gear-source-permitted`, and `som-gear-source-accessible`; all must be `t`.
Access means the caller has assessed the non-equipment access conditions and
the prerequisites of the planned approach. A known path alone does not provide
that assessment. Unknown or false flags do not authorize an attempt.

For mobiles, `som-gear-source-loot-known = t` records evidence that defeating
the holder can yield the piece. Worn or carried gear alone is insufficient.
`som-gear-source-model-known = t` qualifies the stated
`som-gear-source-requires` equipment sequence as an evidence-backed conditional
combat assessment. An explicit `(:seq)` means assessed unarmed prerequisites;
an unset slot means unknown. `som-gear-source-assessed-level` is the character's
level when that model was assessed, not the mob's level.
`som-gear-source-risk` is `cautious`, `steady`, or `bold`; the goal's
`som-gear-risk` bounds it and defaults to cautious when absent.

Mob holders identify concrete encounters, not a reusable mob kind. Projected
`som-gear-defeated` histories prevent defeating the same encounter twice,
including a mob consumed by an earlier prerequisite fight. An observed snapshot
may supply this sequence; absence starts an empty history. A respawn requires
fresh evidence and its own encounter identity, not an assumed repeat opportunity.

An optional `som-gear-source-yields` sequence records an explicitly evidenced
mobile loot bundle. It must include the source's offered piece. Any member can
serve a wanted loadout; one predicted fight adds the declared bundle to owned
gear, without duplicating pieces already owned. Otherwise only the offered piece
is predicted. Examining several worn pieces does not establish a loot bundle.

An acquisition model remains conditional on its stated non-gear assumptions.
It does not guarantee a win or drop. The live consumer still checks current
health, fresh target evidence, policy, and access before acting. Shop prices,
stock, corpses, and mob availability must be maintained from observations.

## Plan a purchase followed by intermediate fights

This minimal example puts all sources in the same explored room. Remote sources
use the known map and add explicit travel steps.

```lisp
(load-lib "src/resources/som-component-library" :silent t)
(*PlayerA has (instance-of (Som-Agentic-Player)))
(in-situation *PlayerA
  (*Courtyard has (instance-of (Som-Explored-Room))))
(in-situation *PlayerA
  (*PlayerA has (som-explored-room ((:seq *Courtyard)))))
(in-situation *PlayerA
  (*Club has (instance-of (Som-Gear-Piece)) (som-short ("club"))
             (som-keyword (club)) (som-worn-slot (wield)) (som-gear-usable (t))))
(in-situation *PlayerA
  (*Spear has (instance-of (Som-Gear-Piece)) (som-short ("spear"))
              (som-keyword (spear)) (som-worn-slot (wield)) (som-gear-usable (t))))
(in-situation *PlayerA
  (*Sword has (instance-of (Som-Gear-Piece)) (som-short ("sword"))
              (som-keyword (sword)) (som-worn-slot (wield)) (som-gear-usable (t))))
(in-situation *PlayerA
  (*Bandit has (instance-of (Som-Mobile)) (som-player (f))))
(in-situation *PlayerA
  (*Guard has (instance-of (Som-Mobile)) (som-player (f))))
(in-situation *PlayerA
  (*Club-offer has (instance-of (Som-Gear-Source))
                   (som-gear-source-kind (shop)) (som-gear-source-item (*Club))
                   (som-holder (*Merchant)) (som-gear-source-room (*Courtyard))
                   (som-gear-source-price (5)) (som-gear-source-available (t))
                   (som-gear-source-permitted (t)) (som-gear-source-accessible (t))))
(in-situation *PlayerA
  (*Spear-loot has (instance-of (Som-Gear-Source))
                   (som-gear-source-kind (mobile)) (som-gear-source-item (*Spear))
                   (som-holder (*Bandit)) (som-gear-source-room (*Courtyard))
                   (som-gear-source-available (t)) (som-gear-source-permitted (t))
                   (som-gear-source-accessible (t)) (som-gear-source-loot-known (t))
                   (som-gear-source-model-known (t)) (som-gear-source-assessed-level (1))
                   (som-gear-source-risk (cautious)) (som-gear-source-requires ((:seq *Club)))))
(in-situation *PlayerA
  (*Sword-loot has (instance-of (Som-Gear-Source))
                   (som-gear-source-kind (mobile)) (som-gear-source-item (*Sword))
                   (som-holder (*Guard)) (som-gear-source-room (*Courtyard))
                   (som-gear-source-available (t)) (som-gear-source-permitted (t))
                   (som-gear-source-accessible (t)) (som-gear-source-loot-known (t))
                   (som-gear-source-model-known (t)) (som-gear-source-assessed-level (1))
                   (som-gear-source-risk (cautious)) (som-gear-source-requires ((:seq *Spear)))))
(in-situation *PlayerA
  (*PlayerA has (som-known-gear-source ((:seq *Sword-loot *Spear-loot *Club-offer)))))
(in-situation *PlayerA
  (*Observed has (instance-of (Som-Gear-State)) (som-gear-confirmed (t))
                 (som-gear-owned ((:seq))) (som-gear-equipped ((:seq)))
                 (som-gear-coins (10)) (som-gear-room (*Courtyard)) (som-level (1))))
(in-situation *PlayerA
  (*PlayerA has (som-gear-state (*Observed))))
(in-situation *PlayerA
  (*Goal has (instance-of (Som-Gear-Goal)) (som-gear-action (regear))
             (som-gear-risk (cautious)) (som-gear-wanted ((:seq *Sword)))))
(in-situation *PlayerA
  (*Recovery has (instance-of (Som-Regear-Request))
                 (som-regear-goal (*Goal)) (som-regear-start (*Observed))))
(in-situation *PlayerA (the som-regear-status of *Recovery))
; => (planned)
(in-situation *PlayerA
  (the som-step-kind of (the som-regear-strategy of *Recovery)))
; => ((:seq buy equip defeat-loot equip defeat-loot equip))
(in-situation *PlayerA (the som-regear-cost of *Recovery))
; => (5)
(in-situation *PlayerA (the som-gear-owned of *Observed))
; => ((:seq))
```

The strategy includes equipping each intermediate weapon before its dependent
fight. Replacing a worn piece retains it in owned inventory. A later fight can
re-equip that intermediate piece and restore the desired final loadout afterward.
Prerequisites and final loadouts must fit together: the same worn slot/index
cannot contain two different pieces. An absent index means zero; explicit
different indices distinguish paired slots.

## Conclusion contracts

The contracts follow [Conclusion Driven Development](../../../../docs/reference/ConclusionDrivenDevelopment.md).
The intention is the goal's explicit wanted loadout. The consumer is an agent
choosing an acquisition/equip proposal. The context is one fresh request, its
confirmed snapshot, and the current player's source observations and map.

| Conclusion | Meaning and dependencies | Selection, absence, and limits |
| --- | --- | --- |
| `som-regear-observations` | The player's indexed source observations, including observation-only gear. | Source order is preserved. An empty sequence means no indexed observations, not that the world has no gear. |
| `som-regear-status` | Whether inputs support a loadout strategy. | `incomplete`, `stale`, `unsupported-goal`, `inconsistent`, `invalid`, `needs-gear-evidence`, `incompatible-goals`, `blocked`, `planned`, or `complete`. Missing state fields, a superseded snapshot, contradictory equipment, and already-equipped goals have different results. |
| `som-regear-strategy` | An ordered sequence of proposed transitions sufficient to equip the wanted pieces if their assumptions and outcomes hold. | Among supported complete options at each task, lower coin cost wins, then fewer transitions, then source order. An empty sequence is a valid completed loadout; nil means no strategy supported by this request. |
| `som-regear-next-step` | The first proposed transition for the consumer to validate now. | Nil for a completed or unsupported strategy. Later steps are conditional and must not be executed blindly. |
| `som-regear-final-state` | Predicted inventory, equipment, purse, and room after a successful strategy. | A `Som-Gear-Projection`, or the unchanged observed state for an empty strategy. It is never installed as the player's real state by planning. |
| `som-regear-cost` | Current purse minus predicted final purse. | Cumulative purchases use one purse. Owned/shared prerequisite pieces are not bought twice. No coins are assumed from future kills, sales, or loot. |
| `som-regear-risk`, `som-regear-reserve`, `som-regear-limit` | The goal's risk ceiling, coins to leave unspent, and transition budget. | Defaults are cautious, zero reserved coins, and 16 transitions. Override reserve/limit with `som-regear-reserve-in` and `som-regear-limit-in`. Negative inputs are invalid. |

`blocked` means this bounded planning policy found no supported strategy under
the supplied models, purse, reserve, map, usability evidence, and limit. It
does not establish global impossibility. The policy selects a preferred
prerequisite strategy before continuing its parent; it does not exhaust every
combination of alternative prerequisite histories. It does not promise a
globally cheapest loadout, shortest journey, or optimal combat strategy.
The active dependency chain rejects circular unowned gear requirements. The
transition budget also bounds re-equipping and acquisition recursion.

Each `Som-Gear-Step` exposes `som-step-kind`, `som-step-item`, `som-step-cost`,
`som-step-before`, `som-step-after`, `som-step-request`, and
`som-step-observation`. Acquisition/travel steps carry `som-step-source`;
travel steps carry `som-step-route`, retaining exit open/unlock requirements.
Source access must already be assessed; the planner does not execute door
commands or establish that a route is currently safe from geometric connectivity.

## Death, observations, and reconsideration

After death, assert a new complete confirmed `Som-Gear-State` containing only
the items still possessed and worn, the remaining coins, room, and current
character level. Explicit empty owned/equipped sequences mean the gear is gone.
Replace the player's `som-gear-state` pointer with `now-has`, then create a new
`Som-Regear-Request` against that snapshot. Old gear records and source memories
can remain knowledge without remaining possessions.

The request rejects an older snapshot as stale. A previously stored
`som-gear-met` flag does not override current equipment observations. If the
player's corpse is still accessible and loot is permitted, index a corpse
source; otherwise available shops and intermediate-mob models can support a
replacement chain. A lost powerful weapon cannot satisfy a prerequisite merely
because the player used to own it.

Treat each confirmed snapshot frame as an immutable observation. Create a new
frame and replace the player's current-state pointer for every planning-relevant
change, including price, access, permission, and combat-model changes even when
the loadout itself is unchanged. Cached old requests are not live checks.

After each movement, purchase, pickup, loot result, fight, or equip attempt,
observe what actually happened and plan again from a new confirmed snapshot
and request. Failed attacks, missing drops, refusals, changed stock, and blocked
paths update evidence before another attempt. Refresh the source assessments
and usability/risk models when their assumptions change. Use `now-has` to
replace changing N-to-1 values and whole sequences.

Planning creates hypothetical `Som-Gear-Projection` and `Som-Gear-Step` frames;
it never asserts live acquisition, spends live coins, or equips the character.
Projections omit the confirmation and character-observation fields required
of a real snapshot. KM does not provide general truth maintenance, so cached
old requests are historical answers rather than live authorizations. The
executor must confirm that a step still refers to the current observed snapshot
and apply existing live safety/command policy. Automatic combat execution,
enchanting, farming purchase money, probabilistic drop models, and reconciliation
of contradictory sources remain outside this package.

## Files and verification

`Som-Gear-Piece.km`, `Som-Gear-Goal.km`, and `Som-Gear-Report.km` retain the
existing vocabulary. `Som-Gear-Source.km`, `som-player-gear-source.km`,
`Som-Gear-State.km`, and `som-player-gear-state.km` define the new evidence.
`Som-Regear-Request.km` exposes conclusions; `Som-Regear-Task.km` and
`Som-Regear-Choice.km` compose bounded plans. `Som-Gear-Projection.km` and
`Som-Gear-Step.km` represent predicted states and proposals. Legacy alignment
and weapon-skill records remain available; their fields can inform caller
assessments, but no weapon-stat ranking is invented here.

Run `clojure -M:test -n som.km.gear-recovery-test` or the complete agent suite
with `clojure -M:test -d test/agent-goals`. The [test guide](../../../../test/agent-goals/README.md)
maps named examples to their contracts. Tests cover all source kinds, staged
shop/mob recovery, cumulative/reserved funds, shared prerequisites, wear slots,
known restrictions, cycles, bounded refusal, routes, death, player isolation,
single-use mob encounters and evidenced multi-piece loot,
prediction versus observation, and both adapters. They verify conclusions and
state separation, not successful live movement, purchase, or combat.
