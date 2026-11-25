# Vocabulary

Five classes subclass `Thing`. `Som-Agentic-Player` subclasses `Situation`. Four relations are `N-to-1` slots whose inverse is declared beside them. The slots this library declares are `*Fluent`. A conclusion is written in one `(every ... has ...)` so two files do not store two values on the same slot.

This note is the caller-facing list. Every declared frame, including the helper conclusions and every `*-rule` slot, is in [Objects](objects.md).

## Classes

`Som-Agentic-Player` is one agentic player's situation. Assertions and query results for that player stay in it.

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

`Som-Goal-View` joins one goal and one projection. Its other slots are conclusions. Read them. Do not assert them.

`Som-Level-Directive` is created only for a real license. Its slots are `som-directive-role`, `som-allow-social`, and `som-attempts`. `som-allow-social` is the symbol `no`.

## Relations

| Forward | Inverse | Gloss |
| --- | --- | --- |
| `som-goal` | `som-goal-of` | is judged against / is the goal of |
| `som-progress` | `som-progress-of` | is drawn from / is the progress of |
| `som-reading` | `som-reading-of` | includes the reading / is a reading on |
| `som-licensed-directive` | `som-licensed-directive-of` | is licensed as / is the directive of |

`som-reading` holds one `:seq`. The readings are members of that seq, not several values of the slot.

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

`som-pace-withheld` is declared and its rule does not fire. A used-up unmet budget is `behind`.
