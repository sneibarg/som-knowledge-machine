# Objects

Every frame the Springs of MUD component library declares. The directory is `src/resources/som-component-library`. How to load it and how to ask one question are in the [library README](../../../src/resources/som-component-library/README.md). Pace, the notch, and the hunt are also summarized in [Reasoning](reasoning.md). This note names each frame, who writes it, and what a read returns.

The library declares 6 classes and 122 slots.

`Thing`, `Slot`, `N-to-1`, `*Fluent`, `Situation`, and `text-gen` are built in. They are named here only where a class rule stores a value on `text-gen`.

Each slot this library declares is an instance of `Slot`, cardinality `N-to-1`, fluent status `*Fluent`, with one `text-gloss`. A forward relation also has domain `Thing`, a range, an inverse, and `original-slot` `t`. An inverse declares `instance-of`, `fluent-status`, and `text-gloss`. A second `(every Som-Goal-View has ...)` appends slots. `Som-Goal-View.km` writes the fraction, pace, and notch conclusions. `Som-Level-Directive.km` writes the hunt conclusions onto the same class.

A conclusion slot's class value is `(the <slot>-rule of Self)`. The paired `*-rule` slot holds the expression. Reading either slot runs that expression and returns the same answer. The caller asserts neither. The gloss on every `*-rule` slot is `the rule for <slot>`.

One query is one score, one death, or one view. The caller asserts the goal, the projection, and the view's two relations. The next event is a new projection and a new view.

## Classes

`Som-Level-Goal`, `Som-Progress-Projection`, `Som-Mobile-Reading`, `Som-Goal-View`, and `Som-Level-Directive` store `(superclasses (Thing))`. `Som-Agentic-Player` stores `(superclasses (Situation))`.

| Class | File | What it is |
| --- | --- | --- |
| `Som-Agentic-Player` | `Som-Agentic-Player.km` | One agentic player's situation. Fluent values asserted or computed there stay there. |
| `Som-Level-Goal` | `Som-Level-Goal.km` | The level asked for, the risk ceiling, the minute budget, and the score cadence. |
| `Som-Progress-Projection` | `Som-Progress-Projection.km` | The clock and the room, copied in for this event. No rule writes these slots. |
| `Som-Mobile-Reading` | `Som-Mobile-Reading.km` | One mobile on the projection's reading sequence. The sequence stays in caller order. |
| `Som-Goal-View` | `Som-Goal-View.km` | One goal judged against one projection. Its other slots are conclusions. |
| `Som-Level-Directive` | `Som-Level-Directive.km` | One license. The view creates it for a hunt rule that sends attempts. |

## Relations

| Forward | Inverse | Range | Forward gloss | Inverse gloss | Holder |
| --- | --- | --- | --- | --- | --- |
| `som-goal` | `som-goal-of` | `Som-Level-Goal` | is judged against | is the goal of | The view, asserted by the caller. |
| `som-progress` | `som-progress-of` | `Som-Progress-Projection` | is drawn from | is the progress of | The view, asserted by the caller. |
| `som-reading` | `som-reading-of` | `Som-Mobile-Reading` | includes the reading | is a reading on | The projection. One `:seq`, in caller order. |
| `som-licensed-directive` | `som-licensed-directive-of` | `Som-Level-Directive` | is licensed as | is the directive of | The view. The hunt rule writes it. |

`som-reading` is one sequence value. The readings are members of that `:seq`.

`som-licensed-directive` is declared in `som-licensed-directive.km`. The expression that fills it is `som-licensed-directive-rule` in `Som-Level-Directive.km`. A read is one `Som-Level-Directive`, or empty when the clock is stale, when `som-licensed-rule` is empty, or when that rule is `1` or `14`. A created directive has `som-directive-role` from `som-role-for-rule`, `som-allow-social` `no`, and `som-attempts` from `som-attempts-for-rule`.

## Som-Level-Goal

The caller asserts `som-target-level`, `som-risk-ceiling`, and `som-budget-minutes`. Assert a missing budget as `0`.

| Slot | Writer | Gloss | What a read returns |
| --- | --- | --- | --- |
| `som-kind-in` | Caller, optional | the kind as asserted | The kind the caller stored. Empty leaves `som-kind` as `level`. |
| `som-kind` | Class rule | the goal kind | `som-kind-in` when that slot has a value, otherwise `level`. |
| `som-target-level` | Caller | the level asked for | The level the goal asks for. |
| `som-risk-ceiling` | Caller | the highest notch pace may reach | `cautious`, `steady`, or `bold`. |
| `som-budget-minutes` | Caller | the minute budget, or zero when play is open-ended | A positive budget, or `0` for open-ended play. |
| `som-score-every-in` | Caller, optional | the cadence as asserted | The cadence the caller stored. Empty leaves `som-score-every` as `15`. |
| `som-score-every` | Class rule | the steps between scores | `som-score-every-in` when that slot has a value, otherwise `15`. |

The same class rule writes the built-in `text-gen` slot. The sentence is "The level goal is level", the target, "at", and the ceiling. For target `5` and ceiling `bold` the sentence is "The level goal is level 5 at bold."

## Som-Progress-Projection

The caller writes every slot in this table. A counter that has not started is `0`. These slots may be empty: `som-gear-gate`, `som-max-hit`, `som-hit`, `som-score-page-exp`, `som-exp-estimate`, `som-position`, `som-flee-floor`, and `som-opponent-outlook`. `som-reading` is the relation above.

| Slot | Gloss | What the caller stores |
| --- | --- | --- |
| `som-event` | the event this projection answers | `score`, `death`, or `view`. |
| `som-clock-kind` | the kind stored on the clock | Compared with `som-kind`. A difference makes the clock stale. |
| `som-clock-target` | the target stored on the clock | Compared with `som-target-level`. A difference makes the clock stale. |
| `som-start-level` | the level on the first score | Level when the clock started. |
| `som-start-fraction` | the fraction on the first score | Fraction when the clock started. |
| `som-level` | the level on the latest score | Level on the latest score page. |
| `som-exp-to-level` | experience to level on the latest score page | Experience still to level. `som-exp-used` uses it when neither replacement is set. |
| `som-exp-span` | experience span taken from the first score on this level | `0` leaves the fraction empty. A positive span is the width of the level. |
| `som-exp-estimate` | experience to level after a receive line, before the next score | Used when `som-score-page-exp` is empty. |
| `som-score-page-exp` | experience to level on a score page that replaces the estimate | When set, `som-exp-used` prefers it. |
| `som-elapsed-minutes` | minutes since the first score | Assert this when the budget is greater than `0`. An empty value makes the remaining-minutes comparison record an error. |
| `som-score-count` | scores already folded into this projection | `0` makes a score due. |
| `som-first-score` | this score is the first one on the clock | `t` on the first score. With budget `0`, that score sets the notch to the ceiling. |
| `som-prior-notch` | the notch stored before this event | `cautious`, `steady`, or `bold`. |
| `som-cooldown-steps` | cooldown steps still stored | A death answers `30` on `som-cooldown-next`. While this slot is still `30`, a `behind` pace does not raise the notch. |
| `som-saves` | checkpoints stored on this level | `0` makes a checkpoint due. |
| `som-score-steps` | steps since the last score. Python stores 0 after a score is folded in | Reaching `som-score-every` makes a score due. |
| `som-score-forced` | the engine marked a score due, as after a fight | `t` makes a score due. |
| `som-met-in` | met was already stored | `t` makes `som-met` true without another level test. |
| `som-deadline-in` | deadline missed was already stored | `t` makes `som-deadline-missed` true. |
| `som-max-hit` | max hit on the latest score, if that page printed it | With `som-hit`, the health line can be computed. |
| `som-hit` | hit points the engine is using for this step | With `som-max-hit`, the health line can be computed. |
| `som-position` | the position word on the latest score | `resting` is the word rule 7 uses for `stand`. |
| `som-areas-known` | at least one area record is stored | Any value means an area is known. Omit the slot when none are. |
| `som-fighting` | the engine says the character is fighting | `t` while fighting. |
| `som-opponent-outlook` | not projected. Rules 5 and 6 are not licensed until a player proposal names the fight marker | Left empty. No rule reads it. |
| `som-repop-room` | the engine has seen a kill in this room | `t` blocks a cautious exit and can match rule 11. |
| `som-room-stale` | the session room record needs another look | `t` makes rule 11 attempt `look`. |
| `som-gear-gate` | the gear gate the engine copied, or empty | Rule 1 matches only while this slot is empty. A set gate falls through. |
| `som-flee-floor` | play.flee_hp as copied by the engine. Empty means the bold line is not applied | A bold health line is `missed` when hit is at most this floor. |
| `som-untried-exits` | exits this process has not taken | A `:seq` of direction symbols. `(:seq)` means none. |

## Som-Mobile-Reading

| Slot | Writer | Gloss | What a read returns |
| --- | --- | --- | --- |
| `som-mobile-name` | Caller | the mobile name | The symbol an attempt names. |
| `som-outlook` | Caller | the consider outlook | `safe`, `even`, `risky`, `fatal`, `unknown`, or empty. Empty means the consider has not been taken. |
| `som-fresh` | Caller | the consider was taken in this room during this visit | `t` when this visit's consider is still fresh. Engage requires `t`. |
| `som-player` | Caller | the engine says this is a player | `t` when the engine says this is a player. Engage requires this to be other than `t`. A survey reading still includes a player. |

## Som-Level-Directive

The view creates an instance. The caller does not.

| Slot | Gloss | What a read returns |
| --- | --- | --- |
| `som-directive-role` | the role of this license | The role `som-role-for-rule` computed: `survey`, `escape`, `recover`, `engage`, `travel`, `hold`, or `checkpoint`. |
| `som-allow-social` | no blocks a greeting while this directive exists | The symbol `no` on every directive this library creates. |
| `som-attempts` | the attempts this license sends | The value `som-attempts-for-rule` computed. One attempt is `(:args role category preference argument)`. Several attempts are one `:seq`. A hold is `(:seq)`. |

## Conclusions on Som-Goal-View

Declared in `Som-Goal-View.km`. Each row is one conclusion. The paired rule slot is `<slot>-rule`, declared on the next line of that file, gloss `the rule for <slot>`.

A stale clock leaves pace, notch, met, deadline, score due, checkpoint due, the licensed rule, and the directive empty. Fraction can still be computed. The license does not read it.

A `<`, `>`, `<=`, or `>=` against an empty slot records an error. `som-needed`, `som-actual`, `som-sample-ready`, `som-pace-band`, and the deadline test use those comparisons. The caller asserts the numbers those rules read. `som-remaining-minutes` is present when both the budget and the elapsed minutes have values. When the budget is greater than `0`, assert elapsed minutes.

| Slot | Gloss | What a read returns |
| --- | --- | --- |
| `som-clock-stale` | the clock was started for a different kind or target | `t` when `som-clock-kind` differs from `som-kind`, or `som-clock-target` differs from `som-target-level`. A match leaves the slot empty. |
| `som-exp-used` | the experience figure fraction uses | `som-score-page-exp` when set, otherwise `som-exp-estimate` when set, otherwise `som-exp-to-level`. |
| `som-estimate-overwritten` | a score page replaced an experience estimate | `t` when both `som-score-page-exp` and `som-exp-estimate` have values. |
| `som-fraction` | fraction through the level | `1` minus `som-exp-used` divided by `som-exp-span`, when the span is greater than `0`. A span of `0` leaves the slot empty and records no error. |
| `som-span-reading` | the span is a positive first reading on this level | `first-reading-counted-as-width` when `som-exp-span` is greater than `0`. The rule does not test `som-first-score` and does not write `som-exp-span`. |
| `som-levels-earned` | levels earned since the clock started | Current level minus start level, plus the fraction, minus the start fraction. Empty when the fraction is empty. |
| `som-current-level-as-fraction` | level plus fraction | `som-level` plus `som-fraction`. Empty when the fraction is empty. |
| `som-remaining-levels` | target minus the fractional level | `som-target-level` minus `som-current-level-as-fraction`. Empty when that sum is empty. |
| `som-remaining-minutes` | budget minus elapsed minutes | `som-budget-minutes` minus `som-elapsed-minutes`, when both have values. |
| `som-needed` | levels per minute still required | `som-remaining-levels` divided by `som-remaining-minutes`, when remaining minutes are greater than `0`. |
| `som-actual` | levels per minute so far | `som-levels-earned` divided by `som-elapsed-minutes`, when elapsed minutes are greater than `0`. |
| `som-sample-ready` | two minutes and two scores have been seen | `t` when elapsed minutes are at least `2` and the score count is at least `2`. |
| `som-pace-band` | behind, on, or ahead once the sample is ready | `behind` when actual is below needed times `4/5`. `ahead` when actual is above needed times `6/5`. `on` on either edge and between them. Pace reads this only after the sample is ready. |
| `som-pace-withheld` | not set. A used-up unmet budget is behind, not a withheld band | Empty. The rule condition is `(not (t = t))`. |
| `som-pace` | the pace band | See the pace table below. |
| `som-met` | a score has shown the target level or higher | Empty on a stale clock. Otherwise `t` when `som-met-in` is `t`, or when `som-level` is at least `som-target-level`. |
| `som-deadline-missed` | the budget ran out unmet | Empty on a stale clock. Otherwise `t` when `som-deadline-in` is `t`, or when the budget is greater than `0`, remaining minutes are `0` or less, and the goal is unmet. |
| `som-raised-one` | the notch one step up, stopping at the ceiling | The prior notch when it already equals the ceiling. `steady` when the prior notch is `cautious`. `bold` when the prior notch is `steady` and the ceiling is `bold`. Otherwise the prior notch. |
| `som-dropped-one` | the notch one step down, stopping at cautious | `steady` from `bold`. `cautious` from `steady`. `cautious` from any other prior notch. |
| `som-dropped-on-death` | the notch after a death | `cautious` from `bold`. Otherwise `som-dropped-one`, so `steady` and `cautious` also answer `cautious`. |
| `som-cooldown-next` | the cooldown to store after this event | Empty on a stale clock. `30` on a death. Any other event answers `som-cooldown-steps`. |
| `som-notch-on-score` | the notch a score query stores | See the score notch table below. |
| `som-notch-on-view` | the notch a view query stores | The ceiling when the deadline is missed and the prior notch is still below the ceiling. Otherwise the prior notch. |
| `som-notch` | the notch after this event | Empty on a stale clock. A death reads `som-dropped-on-death`. A score reads `som-notch-on-score`. A view, and any other event, reads `som-notch-on-view`. |
| `som-notch-moved` | how the notch moved | Empty on a stale clock. A death answers `dropped`. A score answers `ceiling`, `raised`, `dropped`, or `unchanged` as in the score table. A view answers `ceiling` when it jumped, otherwise `unchanged`. |
| `som-score-due` | a score should be taken | Empty on a stale clock. Otherwise `t` when the score count is `0`, or `som-score-forced` is `t`, or `som-score-steps` has reached `som-score-every`. |
| `som-checkpoint-due` | this level has no checkpoint yet | Empty on a stale clock. Otherwise `t` when `som-saves` is `0`. |

`som-pace` answers in this order. The used-up budget is decided before any quotient. In this port `(4 / 0)` is `999999` and `(0 / 0)` is `1`, so the rule tests remaining minutes first.

| Situation | `som-pace` |
| --- | --- |
| Clock is stale | empty |
| Budget is missing or `0` | `open` |
| Remaining minutes are `0` or less, and the goal is unmet | `behind` |
| Remaining minutes are `0` or less, and the goal is met | empty |
| Sample is not ready | `sampling` |
| Sample is ready | `som-pace-band` |

A score sets `som-notch-on-score` and `som-notch-moved` as follows. The ladder is `cautious`, then `steady`, then `bold`.

| Situation | Notch | `som-notch-moved` |
| --- | --- | --- |
| Deadline missed and the goal is unmet | the ceiling | `ceiling` |
| Budget is `0` and this is the first score | the ceiling | `ceiling` |
| Pace is `behind` and the cooldown is `0` | `som-raised-one` | `raised`, or `unchanged` when the notch stayed |
| Pace is `ahead` | `som-dropped-one` | `dropped`, or `unchanged` at `cautious` |
| Pace is `on`, `open`, or `sampling` | the prior notch | `unchanged` |

A later open-ended score does not raise the notch again. Only the first score on a zero budget jumps to the ceiling. While `som-cooldown-steps` is still `30`, a `behind` pace does not raise the notch.

### Rule slots in Som-Goal-View.km

Each of these is a `Slot`. Its gloss is `the rule for` the paired conclusion. A read returns the same answer as that conclusion.

`som-clock-stale-rule`, `som-exp-used-rule`, `som-estimate-overwritten-rule`, `som-fraction-rule`, `som-levels-earned-rule`, `som-current-level-as-fraction-rule`, `som-remaining-levels-rule`, `som-remaining-minutes-rule`, `som-needed-rule`, `som-actual-rule`, `som-sample-ready-rule`, `som-pace-rule`, `som-pace-band-rule`, `som-pace-withheld-rule`, `som-span-reading-rule`, `som-met-rule`, `som-deadline-missed-rule`, `som-notch-rule`, `som-notch-moved-rule`, `som-cooldown-next-rule`, `som-raised-one-rule`, `som-dropped-one-rule`, `som-dropped-on-death-rule`, `som-notch-on-score-rule`, `som-notch-on-view-rule`, `som-score-due-rule`, `som-checkpoint-due-rule`.

## Hunt slots on Som-Goal-View

Declared in `Som-Level-Directive.km` and stored on `Som-Goal-View` by the second `(every Som-Goal-View has ...)`. The relation `som-licensed-directive` itself is declared in `som-licensed-directive.km`.

| Slot | Gloss | What a read returns |
| --- | --- | --- |
| `som-health-line` | missed, clear, or empty | Empty unless both `som-max-hit` and `som-hit` have values. `cautious` is `missed` at hit/max of `1/2` or less, otherwise `clear`. `steady` is `missed` at `1/3` or less, otherwise `clear`. `bold` is `missed` when `som-flee-floor` has a value and hit is at most that floor, otherwise `clear`. An empty floor on a bold line is `clear`. A notch other than `cautious`, `steady`, or `bold` leaves the line empty. |
| `som-survey-reading` | the first reading with no consider | The first `Som-Mobile-Reading` on `som-reading` whose `som-outlook` is empty. A player is included. The sequence order is the caller's order. |
| `som-engage-reading` | the first reading this notch will fight | The first reading that is fresh, whose `som-player` is other than `t`, and whose outlook is a fight for this notch. `safe` fights at `cautious`, `steady`, and `bold`. `even` fights at `steady` and `bold`. `risky` fights at `bold`. `fatal`, `unknown`, a missing outlook, and an empty notch are not fights. |
| `som-exit-allowed` | the notch may open an untried exit | `t` at `cautious` when pace is `behind` and `som-repop-room` is other than `t`. `t` at `steady` or `bold` when there is no engage reading and no survey reading. `sampling`, `on`, `ahead`, and `open` leave a cautious exit closed. |
| `som-licensed-rule` | the first hunt rule that matches | Empty on a stale clock. Otherwise the first matching number in the hunt table. The numbers are `1` through `14` with no branch that returns `5` or `6`. |
| `som-role-for-rule` | the role for the licensed rule | The role column below. Rules `1` and `14` leave it empty. |
| `som-attempts-for-rule` | the attempts for the licensed rule | The attempts column below. One `(:args ...)` is one attempt. Rule 10 and rule 12 hold a `:seq`. Rule 11's hold is `(:seq)`. |
| `som-licensed-directive-rule` | the rule for som-licensed-directive | The same answer as `som-licensed-directive`: one directive, or empty for a stale clock, an empty rule, rule `1`, and rule `14`. |

`som-health-line-rule`, `som-survey-reading-rule`, `som-engage-reading-rule`, `som-exit-allowed-rule`, `som-licensed-rule-rule`, `som-role-for-rule-rule`, and `som-attempts-for-rule-rule` are the paired rule slots. Each gloss is `the rule for` its conclusion. A read returns the same answer as that conclusion.

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

Rule 12's attempts are `(:args travel movement recall "")` and then `(:args survey "information / communication" where "")`. The category that contains a slash is the string `"information / communication"`. Rule 11's look attempt is `(:args survey objects look "")`. Rule 9's attempt is `(:args engage combat kill <name>)`. Rule 8's attempt is `(:args survey "information / communication" consider <name>)`. Rule 10's argument is `""`. The preference is the direction.

The header of `Som-Level-Directive.km` names four engine rules that have already run: danger at `play.flee_hp`, leave a threat the engine did not engage, stand after a position refusal, and an owed reply. A personality yield, a gear strategy, and a catalog pick have no slot here. `som-gear-gate` is read only by rule 1.

A fighting view that misses rule 4 continues through the later rules. A missing consider is rule 8, including while fighting. An idle fighting view with a clear or empty health line, no mobiles, and no exits is rule 14. `som-opponent-outlook` has no reader.
