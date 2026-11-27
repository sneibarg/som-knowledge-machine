# Vocabulary

Twenty-nine classes subclass `Thing`. `Som-Agentic-Player` subclasses `Situation`. Twelve relations are `N-to-1` slots whose inverse is declared beside them. The slots this library declares are `*Fluent`. A conclusion is written in one `(every ... has ...)` so two files do not store two values on the same slot. Nine legacy classes remain declarations without behavior of their own; shared gear and alignment fields can support caller assessments and re-gearing.

This note is the caller-facing list. Every declared frame, including the helper conclusions and every `*-rule` slot, is in [Objects](objects.md).

## Classes

`Som-Agentic-Player` is one agentic player's situation. Assertions and query results for that player stay in it.

| Slot | Who writes it | Meaning |
| --- | --- | --- |
| `som-bootstrap` | Caller | `t` when this player's bootstrap has completed. Empty until then. |

`Som-Level-Goal` is the goal the view is judged against.

| Slot | Who writes it | Meaning |
| --- | --- | --- |
| `som-kind-in` | Caller, optional | Kind as asserted. Empty means `som-kind` is `level`. |
| `som-kind` | Rule | The goal kind. |
| `som-target-level` | Caller | The level asked for. |
| `som-risk-ceiling` | Caller | The highest notch pace may reach: `cautious`, `steady`, or `bold`. |
| `som-budget-minutes` | Caller | The minute budget. `0` means open-ended. Assert an omitted budget as `0`. |
| `som-score-every-in` | Caller, optional | Cadence as asserted. Empty means `som-score-every` is `15`. |
| `som-score-every` | Rule | Steps between scores. |

`Som-Progress-Projection` is the clock and the room, copied in by the caller for this event. Numbers the rules compare are present. A counter that has not started is `0`. These slots may be empty: `som-gear-gate`, `som-max-hit`, `som-hit`, `som-score-page-exp`, `som-exp-estimate`, `som-position`, `som-flee-floor`, and `som-opponent-outlook`.

| Slot | Meaning |
| --- | --- |
| `som-event` | `score`, `death`, or `view`. |
| `som-clock-kind` | Kind stored on the clock. A mismatch with `som-kind` makes the clock stale. |
| `som-clock-target` | Target stored on the clock. A mismatch with `som-target-level` makes the clock stale. |
| `som-start-level` | Level on the first score. |
| `som-start-fraction` | Fraction on the first score. |
| `som-level` | Level on the latest score. |
| `som-exp-to-level` | Experience still to level on the latest score page. |
| `som-exp-span` | Experience span taken from the first score on this level. `0` means the span is unknown. |
| `som-exp-estimate` | Experience to level after a receive line, before the next score. |
| `som-score-page-exp` | Experience to level on a score page. When set, it replaces the estimate. |
| `som-elapsed-minutes` | Minutes since the first score. |
| `som-score-count` | Scores already folded into this projection. |
| `som-first-score` | `t` when this score is the first one on the clock. |
| `som-prior-notch` | Notch stored before this event. |
| `som-cooldown-steps` | Cooldown steps still stored. A death stores `30` on `som-cooldown-next`. |
| `som-saves` | Checkpoints stored on this level. `0` means a checkpoint is due. |
| `som-score-steps` | Steps since the last score. The caller stores `0` after a score is folded in. |
| `som-score-forced` | `t` when the engine marked a score due, as after a fight. |
| `som-met-in` | `t` when met was already stored. |
| `som-deadline-in` | `t` when a missed deadline was already stored. |
| `som-max-hit` | Max hit on the latest score, when that page printed it. |
| `som-hit` | Hit points the engine is using for this step. |
| `som-position` | Position word on the latest score, such as `resting`. |
| `som-areas-known` | Any value means at least one area record is stored. Omit the slot when none are. |
| `som-fighting` | `t` when the engine says the character is fighting. |
| `som-opponent-outlook` | Left empty. No rule reads it. |
| `som-repop-room` | `t` when the engine has seen a kill in this room. |
| `som-room-stale` | `t` when the session room record needs another look. |
| `som-gear-gate` | Gear gate the engine copied, or empty. Rule 1 is the only reader. |
| `som-flee-floor` | `play.flee_hp` as copied by the engine. Empty means the bold health line is not applied. |
| `som-untried-exits` | A `:seq` of direction symbols this process has not taken. `(:seq)` means none. |
| `som-reading` | A `:seq` of `Som-Mobile-Reading` instances, already ordered by the caller. |

`Som-Mobile-Reading` is one mobile on that seq.

| Slot | Meaning |
| --- | --- |
| `som-mobile-name` | Symbol the attempt will name. |
| `som-outlook` | `safe`, `even`, `risky`, `fatal`, `unknown`, or empty. Empty means the consider has not been taken. |
| `som-fresh` | `t` when the consider was taken in this room during this visit. |
| `som-player` | `t` when the engine says this is a player. |

`Som-Goal-View` joins one goal and one projection. Its other slots are conclusions, except `som-command-goal`, which the caller asserts when asking which commands serve a goal. Read the conclusions. Do not assert them.

`Som-Level-Directive` is created only for a real license. Its slots are `som-directive-role`, `som-allow-social`, and `som-attempts`. `som-allow-social` is the symbol `no`.

## Relations

| Forward | Inverse | Gloss |
| --- | --- | --- |
| `som-goal` | `som-goal-of` | is judged against / is the goal of |
| `som-progress` | `som-progress-of` | is drawn from / is the progress of |
| `som-reading` | `som-reading-of` | includes the reading / is a reading on |
| `som-licensed-directive` | `som-licensed-directive-of` | is licensed as / is the directive of |
| `som-area` | `som-area-of` | includes the area / is an area on |
| `som-known-command` | `som-known-command-of` | includes the command learned at bootstrap / is a command known to |
| `som-explored-room` | `som-explored-room-of` | includes the explored room / is a room known to |
| `som-room-exit` | `som-room-exit-of` | includes the exit / is an exit from |

`som-reading` holds one `:seq`. The readings are members of that seq, not several values of the slot. `som-area` holds one `:seq` the same way. The file is `som-known-area.km`. `som-known-command` holds one `:seq` on the player's situation, in bootstrap order. The file is `som-player-command.km`. `som-explored-room` holds one `:seq` on the player's situation, in the order the caller asserted the rooms. The file is `som-player-room.km`. `som-room-exit` holds one `:seq` on the explored room, in the order the room listed them. The file is `som-explored-exit.km`.

## Conclusions worth reading

| Slot | Answer |
| --- | --- |
| `som-fraction` | Fraction through the level, a ratio. Empty when the span is `0`. |
| `som-levels-earned` | Levels earned since the clock started. |
| `som-pace` | `sampling`, `behind`, `on`, `ahead`, or `open`. Empty when the clock is stale, or when the budget is used up and the goal is already met. |
| `som-notch` | `cautious`, `steady`, or `bold` after this event. Empty when the clock is stale. |
| `som-notch-moved` | `raised`, `dropped`, `ceiling`, or `unchanged`. A death reports `dropped`. |
| `som-cooldown-next` | Cooldown to store. A death answers `30`. Any other event answers the cooldown that was asserted. |
| `som-met` | `t` when a score has shown the target level or higher, or when `som-met-in` is `t`. |
| `som-deadline-missed` | `t` when a positive budget has run out and the goal is unmet. |
| `som-score-due` | `t` when a score should be taken. |
| `som-checkpoint-due` | `t` when this level has no checkpoint yet. |
| `som-clock-stale` | `t` when the stored kind or target differs from the goal. |
| `som-licensed-rule` | The first matching hunt rule, `1` through `14`, skipping `5` and `6`. Empty when the clock is stale. |
| `som-licensed-directive` | One `Som-Level-Directive`, or empty for rule `1`, rule `14`, and a stale clock. |
| `som-explored-area` | The `:seq` of areas on the projection whose `som-explored` is `t`, in the caller's order. Empty when none are. |
| `som-fitting-area` | Explored areas whose level range contains `som-level`. Empty when the level is empty or none fit. |
| `som-optimal-area` | The fitting area with the greatest `som-level-low`, then the least `som-level-high`, then the caller's order. Empty when none fit. |
| `som-command-heading` | The stored category, or the SUMMARY heading when the category is blank. |
| `som-command-for-goal` | The allowed known commands whose heading is the category for `som-command-goal`, in bootstrap order. Empty when the goal is empty or unknown. |
| `som-exploration-attempt` | The attempts hunt rule 10 or 12 sends from the known commands. Empty for every other rule. |
| `som-route-exits` | The `:seq` of exits to take from `som-route-from` to `som-route-to`, in the order to take them. `(:seq)` when the two rooms are the same. Empty when no connection is known. |

`som-pace-withheld` is declared and its rule does not fire. A used-up unmet budget is `behind`.

## Som-Area

The caller asserts one area. `som-explored` is `t` when this character has been there. Empty means the area was listed and not explored. `som-level-low` and `som-level-high` are the two ends of a range such as `1-5`.

| Slot | Who writes it | Meaning |
| --- | --- | --- |
| `som-area-name` | Caller | The area name. |
| `som-area-author` | Caller, optional | The author the areas listing printed. |
| `som-level-low` | Caller | The low end of the range. |
| `som-level-high` | Caller | The high end of the range. |
| `som-explored` | Caller | `t` when the character has been in this area. |

## Som-Known-Command

The caller asserts one command inside the player's situation. `som-command-category` and `som-command-help` may be empty. A blank category leaves the heading to the SUMMARY row for that name. `where` and `delete` are the strings `"where"` and `"delete"`.

| Slot | Who writes it | Meaning |
| --- | --- | --- |
| `som-command-name` | Caller | The command name. |
| `som-command-category` | Caller, optional | The category bootstrap stored. Empty uses the SUMMARY heading. |
| `som-command-help` | Caller, optional | The stored help text. |
| `som-command-heading` | Rule | The category this command serves. |
| `som-command-allowed` | Rule | `t` when the catalog may return this command. |

`som-command-goal` on the view is one of `explore`, `recover`, `survey`, `escape`, `engage`, `look`, or `checkpoint`. `explore` and `recover` use `movement`. `survey` uses `"information / communication"`. `escape` and `engage` use `combat`. `look` uses `objects`. `checkpoint` uses `other`.

## Explored rooms

The caller asserts each room the character has been in, and the directions that room allows. `som-explored-room` on the current situation is one `:seq` of those rooms. `som-room-exit` on a room is one `:seq` of its exits, in the order the room listed them.

| Slot | Who writes it | Meaning |
| --- | --- | --- |
| `som-place-name` | Caller | The name of the explored room. |
| `som-exit-direction` | Caller | The direction this exit allows. |
| `som-exit-to` | Caller | The explored room this direction enters. Empty when the far room is unknown. |
| `som-requires-open` | Caller | `t` when the door must be opened. Empty means that step is not required. |
| `som-requires-unlock` | Caller | `t` when the door must be unlocked. Empty means that step is not required. |

A locked door has both flags. A closed door has the open flag.

`som-route-from` and `som-route-to` are the two rooms the caller asks about. `som-route-exits` is the `:seq` of exits to take, in that order. The same room at both ends is `(:seq)`. No known connection leaves the slot empty. An exit that must be opened or unlocked stays in the seq. The conclusion does not add a command for either flag.

## Skeletons

These classes subclass `Thing`. The caller may assert them. No conclusion reads them, and none of them has a rule.

| Class | Slots |
| --- | --- |
| `Som-Social-Connection` | `som-bond-name`, `som-standing`, `som-pending`, `som-pending-text`, `som-last-utterance`, `som-turns`, `som-last-room`, `som-bond-company` |
| `Som-Personality` | `som-personality-name`, `som-bearing`, `som-personality-company`, `som-manner` |
| `Som-Gear-Piece` | `som-short`, `som-keyword`, `som-location`, `som-worn-slot`, `som-slot-index`, `som-holder`, `som-look-result`, `som-description`, `som-comparison`, `som-compared-to`, `som-enchant`, `som-gear-kind`, `som-weapon-type`, `som-wield-band`, `som-object-level`, `som-level-block`, `som-alignment-known`, `som-alignment-block`, `som-rejects` |
| `Som-Gear-Report` | `som-speaker`, `som-report-text`, `som-claim`, `som-reported-type` |
| `Som-Weapon-Skill` | `som-weapon-skill-name`, `som-weapon-percent` |
| `Som-Gear-Goal` | `som-gear-action`, `som-gear-risk`, `som-gear-met`, `som-practices-left`. The slot it replaces is `som-worn-slot`. |
| `Som-Learned-Ability` | `som-ability-name`, `som-ability-percent`, `som-ability-done`, `som-group-only` |
| `Som-Practice-State` | `som-class-name`, `som-trains`, `som-listing-stale`, `som-offers-stale` |
| `Som-Gain-Offer` | `som-offer-name`, `som-offer-kind`, `som-offer-cost` |
| `Som-Practice-Room` | `som-room-name`, `som-practice-mark`, `som-gain-mark` |
| `Som-Alignment` | `som-alignment-word`, `som-alignment-integer`, `som-alignment-side` |

## Remembered mobiles

`Som-Mobile` is one encounter record in the player's situation. Its caller inputs
are `som-mobile-name` (shared with readings), `som-player` (`f` for an identified
nonplayer), `som-mobile-experience`, `som-mobile-experience-level` (character
level), and `som-mobile-last-room`. `som-known-mobile` is one ordered sequence
on the player situation; replace it with `now-has` when the index changes.

The view accepts `som-mobile-search-from`, an explored room. Its public
conclusions are `som-mobile-search-status`, `som-experience-mobile`,
`som-mobile-needs-evidence`, `som-reachable-mobile`, `som-mobile-target`,
`som-mobile-destination`, and `som-mobile-route`. All added slots are fluent.
The [package guide](../../../src/resources/som-component-library/mobile/README.md)
defines their contracts and examples.

## Gear observations and re-gearing

`Som-Gear-Piece` adds `som-gear-usable`; the existing slot/index, level, and
alignment fields constrain proposed equipping. `Som-Gear-Goal` adds
`som-gear-wanted`, a sequence of desired worn pieces, and accepts `regear`
alongside replace and legacy enchant intentions. Its stored met flag remains
caller-owned. `Som-Gear-Source` holds one room, shop, corpse, mobile, or player
sighting; `som-known-gear-source` indexes those observations on the player.
`som-gear-state` selects the player's current confirmed `Som-Gear-State`.

`Som-Regear-Request` accepts `som-regear-goal`, `som-regear-start`, and optional
limit/reserve overrides. It returns status, strategy, next step, projected final
state, cost, and observation context. `Som-Gear-Projection`, `Som-Gear-Step`,
`Som-Regear-Task`, and `Som-Regear-Choice` hold predictions, proposals, and
planning dependencies. All new slots are fluent. The [gear guide](../../../src/resources/som-component-library/gear/README.md)
defines typed inputs, all public conclusion contracts, and execution limits.
