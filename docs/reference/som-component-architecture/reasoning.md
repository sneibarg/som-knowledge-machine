# Reasoning

The view computes fraction and pace, then the notch, then the first hunt rule. Pace does not read the notch. The notch reads pace. The directive reads both. No conclusion reads itself.

A stale clock stops the chain. `som-clock-stale` is `t` when `som-clock-kind` differs from `som-kind` or `som-clock-target` differs from `som-target-level`. Pace, notch, met, deadline, score due, checkpoint due, the licensed rule, and the directive are then empty. Fraction may still be computed. The license does not read it.

## Fraction

Experience used is `som-score-page-exp` when that slot has a value, and `som-exp-estimate` otherwise. With neither, the view uses `som-exp-to-level`. A score page sets `som-estimate-overwritten` to `t`.

When `som-exp-span` is greater than `0`, the fraction is `1` minus experience used divided by the span. A span of `0` leaves the fraction empty and records no error. The span reading is `first-reading-counted-as-width` when the span is a positive first reading on this level. A later span is kept as asserted. The view does not rewrite it.

Levels earned are the current level plus the fraction, minus the start level and the start fraction.

## Pace

The sample is ready when elapsed minutes are at least `2` and the score count is at least `2`.

| Situation | Pace |
| --- | --- |
| Clock is stale | empty |
| Budget is missing or `0` | `open` |
| Remaining minutes are `0` or less, and the goal is unmet | `behind` |
| Remaining minutes are `0` or less, and the goal is met | empty |
| Sample is not ready | `sampling` |
| Actual is below needed times `4/5` | `behind` |
| Actual is above needed times `6/5` | `ahead` |
| Otherwise, once the sample is ready | `on` |

Needed is remaining levels divided by remaining minutes, and only when remaining minutes are greater than `0`. Actual is levels earned divided by elapsed minutes, and only when elapsed minutes are greater than `0`. The band edges use those ratios. A value sitting on `4/5` or on `6/5` is `on`.

The used-up unmet case is decided before any quotient. In this port `(4 / 0)` is `999999` and `(0 / 0)` is `1`, so the rule tests remaining minutes first and does not divide. `som-pace-withheld` stays empty.

When the budget is greater than `0`, assert elapsed minutes. The deadline test compares remaining minutes with `0`, and that comparison records an error when elapsed minutes are empty.

## Notch

The ladder is `cautious`, then `steady`, then `bold`. The ceiling is `som-risk-ceiling`.

A score moves the notch as follows.

| Situation | Notch | `som-notch-moved` |
| --- | --- | --- |
| Deadline missed and the goal is unmet | the ceiling | `ceiling` |
| Budget is `0` and this is the first score | the ceiling | `ceiling` |
| Pace is `behind` and the cooldown is `0` | one step up, stopping at the ceiling | `raised`, or `unchanged` when it was already there |
| Pace is `ahead` | one step down, stopping at `cautious` | `dropped`, or `unchanged` at `cautious` |
| Pace is `on`, `open`, or `sampling` | the prior notch | `unchanged` |

A later open-ended score does not raise the notch again. Only the first score on a zero budget jumps to the ceiling.

A death answers `cautious` from `bold`, from `steady`, and from `cautious`. `bold` to `cautious` is two steps. `som-notch-moved` is `dropped`, and `som-cooldown-next` is `30`. A later score keeps that cooldown until the caller has counted it down. While `som-cooldown-steps` is still `30`, a `behind` pace does not raise the notch.

A view keeps the prior notch. It does not apply the one-step pace move a second time. The one exception is a missed deadline whose prior notch is still below the ceiling: the view jumps to the ceiling and `som-notch-moved` is `ceiling`.

## Health, survey, and engage

`som-health-line` is computed only when both `som-max-hit` and `som-hit` have values. Otherwise it is empty. Empty is not `missed`.

| Notch | Missed when |
| --- | --- |
| `cautious` | hit divided by max hit is at most `1/2` |
| `steady` | hit divided by max hit is at most `1/3` |
| `bold` | `som-flee-floor` has a value and hit is at most that floor |

A bold line with a max hit and an empty floor is `clear`. The division sits in the branch that already knows both numbers.

`som-survey-reading` is the first reading whose outlook has no value. A player is included. The seq order is the caller's order.

`som-engage-reading` is the first reading that is a fight for this notch, whose `som-fresh` is `t`, and whose `som-player` is not `t`.

| Outlook | Fight when the notch is |
| --- | --- |
| `safe` | `cautious`, `steady`, or `bold` |
| `even` | `steady` or `bold` |
| `risky` | `bold` |

`fatal`, `unknown`, a missing outlook, and an empty notch are not fights.

`som-exit-allowed` is `t` for `cautious` when pace is `behind` and `som-repop-room` is not `t`. It is `t` for `steady` and `bold` when there is no engage reading and no survey reading. `sampling`, `on`, `ahead`, and `open` do not open a new exit at `cautious`. A used-up unmet budget is `behind`, so a cautious character may take an untried exit when the room is not a repop room.

## Hunt rules

`som-licensed-rule` is the first match. There is no rule 0, and the rule does not return `5` or `6`. The directive is built for every other number except `1` and `14`.

| Rule | When it matches | Role | Attempts |
| --- | --- | --- | --- |
| 1 | Met, and `som-gear-gate` is empty | | No directive. A set gear gate falls through. |
| 2 | Score is due | `survey` | `(:args survey "information / communication" score "")` |
| 3 | Areas are unknown and the score count is greater than `0` | `survey` | `areas`, then `where`, same category, argument `""` |
| 4 | Fighting, and the health line is `missed` | `escape` | `(:args escape combat flee "")` |
| 7 | Not fighting, and the health line is `missed` | `recover` | `(:args recover movement rest "")` |
| 7 | Not fighting, health line `clear`, position `resting` | `recover` | `(:args recover movement stand "")` |
| 8 | A survey reading exists | `survey` | `consider` that reading's name |
| 9 | An engage reading exists | `engage` | `kill` that reading's name |
| 10 | No survey, no engage, exit allowed, and the exit seq is non-empty | `travel` | one `(:args travel movement <direction> "")` per exit |
| 11 | No survey, no engage, repop room, and pace is `ahead`, `on`, `open`, or `sampling` | `survey` or `hold` | `look` when the room is stale, otherwise `(:seq)` |
| 12 | Checkpoint is not due, exit is not allowed, the exit seq is non-empty, and rules 8 through 11 missed | `travel` | `recall`, then `where` |
| 13 | Checkpoint is due | `checkpoint` | `(:args checkpoint other save "")` |
| 14 | Nothing above | | No directive. |

Score due is `t` when the score count is `0`, when `som-score-forced` is `t`, or when `som-score-steps` has reached `som-score-every`. Checkpoint due is `t` when `som-saves` is `0`. A due score is rule 2 and comes before the checkpoint.

Rule 12's attempts are `(:args travel movement recall "")` and then `(:args survey "information / communication" where "")`. Those two attempts are not added to `save`, and they are not built for the idle view that has no exits. A checkpoint-due view with no earlier hunt is rule 13. The same view after `som-saves` is `1` is rule 14.

Rule 10's argument is `""`. The preference is the direction, so the attempt names `north` once.

Attempts do not use these preferences: `practice`, `train`, `eat`, `drink`, `follow`, `group`, `kick`, `cast`, `backstab`, `disarm`, `rescue`, `wimpy`, `quit`, `delete`, `murder`, `steal`, `password`, or `!`. Engage is `kill` only.

The category that contains a slash is the string `"information / communication"`. An unquoted slash would divide.

## Absent on purpose

Rules 5 and 6 are the opponent branches in the strategy notes. They are not encoded. `som-opponent-outlook` stays empty, and a missing consider is still rule 8, including while fighting. An idle fighting view with a clear or empty health line, no mobiles, and no exits is rule 14.

The header of `Som-Level-Directive.km` names the four engine rules that have already run: danger at `play.flee_hp`, leave a threat the engine did not engage, stand after a position refusal, and an owed reply. A personality yield, a gear strategy, and a catalog pick are absent here.
