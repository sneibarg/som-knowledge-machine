# Springs of MUD component library

This directory is a Knowledge Machine component library for Springs of MUD. It answers one level-goal question: a score, a death, or a view of the current room. It names the explored area that shortens the time to the next level, the learned commands that serve a goal, and the exploration attempts those commands produce. It names the exits to take from one explored room to another. The caller keeps the clock and sends the line.

`(load-lib)` with no directory still reads the shipped library in `src/resources/km-component-library`. Load this directory by path. The slot list, pace bands, notch steps, and hunt rules are in [docs/reference/som-component-architecture](../../../docs/reference/som-component-architecture/README.md). Every class, relation, inverse, conclusion, helper, and rule slot is named in [objects.md](../../../docs/reference/som-component-architecture/objects.md).

## What was added

Forty-four `.km` files, in nine folders. Each folder is one inference chain. The chains are described in the architecture note under Conclusion driven development. Twenty-nine classes subclass `Thing`. `Som-Agentic-Player` subclasses `Situation`, one situation for each agentic player. Twelve relations connect a view to its goal, its progress, its mobile readings, its areas, and the directive it licenses, connect a situation to the commands learned at bootstrap and to the rooms that have been explored, and connect an explored room to the exits it allows, and connect a player to remembered mobiles and a mobile to its last-known room, and a player to gear-source observations and its current confirmed gear state. Nine legacy classes retain declarations without behavior of their own. The gear package now reads the existing piece and goal vocabulary, including shared alignment metadata. The shipped `Goal` class stays an `Event`. These classes do not subclass it, and they do not reuse `has-goal`, `objective`, `agent`, `Action`, or `Planning`.

| File | What it declares |
| --- | --- |
| `situation/Som-Agentic-Player.km` | One agentic player's situation. Assertions and query results for that player stay in it. |
| `level/Som-Level-Goal.km` | The goal. Kind defaults to `level`. The score cadence defaults to `15`. |
| `level/Som-Progress-Projection.km` | Facts the caller copies in for one event: level, experience, minutes, notch, combat, exits. |
| `level/Som-Goal-View.km` | The view that computes fraction, pace, notch, score due, and checkpoint due. |
| `level/Som-Mobile-Reading.km` | One mobile: name, consider outlook, fresh, and whether it is a player. |
| `level/Som-Level-Directive.km` | The first matching hunt rule, and the directive that rule licenses. |
| `level/som-goal.km` | `som-goal` / `som-goal-of`. The view is judged against the goal. |
| `level/som-progress.km` | `som-progress` / `som-progress-of`. The view is drawn from the projection. |
| `level/som-reading.km` | `som-reading` / `som-reading-of`. The projection includes the readings. |
| `level/som-licensed-directive.km` | `som-licensed-directive` / `som-licensed-directive-of`. The view is licensed as the directive. |
| `area/Som-Area.km` | One area: name, author, level range, and whether it has been explored. |
| `area/som-known-area.km` | `som-area` / `som-area-of`. The projection includes the areas. |
| `area/Som-Area-Choice.km` | The explored areas, the ones whose range contains the character's level, and the one optimal area. |
| `command/Som-Known-Command.km` | One command. The heading is the stored category, or the SUMMARY heading when that category is blank. |
| `command/som-player-command.km` | `som-known-command` / `som-known-command-of`. The situation includes the commands learned at bootstrap. |
| `command/Som-Command-Choice.km` | The known commands that serve the asked goal, and the exploration attempts hunt rules 10 and 12 send. |
| `route/Som-Explored-Room.km` | One room the character has been in. |
| `route/Som-Room-Exit.km` | One direction that room allows, and whether it must be opened or unlocked. |
| `route/som-explored-exit.km` | `som-room-exit` / `som-room-exit-of`. The room includes its exits. |
| `route/som-player-room.km` | `som-explored-room` / `som-explored-room-of`. The situation includes the explored rooms. |
| `route/Som-Route.km` | The exits to take from one explored room to another. |
| `mobile/Som-Mobile.km` | A remembered encounter, observed experience at a character level, and last-known room. |
| `mobile/som-player-mobile.km` | The player situation's ordered `som-known-mobile` sequence. |
| `mobile/Som-Mobile-Choice.km` | Experience sources, evidence gaps, reachable sources, target, destination, and route on the goal view. |

The [gear package](gear/README.md) now includes source observations, confirmed snapshots, and conditional re-gearing strategies. Nine legacy classes across gear, practice, and personality retain declarations without behavior of their own.

| File | What it declares |
| --- | --- |
| `personality/Som-Social-Connection.km` | One bond: standing, a pending reply, and company. |
| `personality/Som-Personality.km` | Bearing, company, and manner. |
| `gear/Som-Gear-Piece.km` | One studied piece, its slot, and player-specific usability evidence. |
| `gear/Som-Gear-Report.km` | What one player said about a piece. |
| `gear/Som-Weapon-Skill.km` | One weapon skill and its percent. |
| `gear/Som-Gear-Goal.km` | Replace/regear loadout intentions and legacy enchant/acknowledgment fields. |
| `practice/Som-Learned-Ability.km` | One practiced skill or spell. |
| `practice/Som-Practice-State.km` | Class, trains, and the stale flags. |
| `practice/Som-Gain-Offer.km` | One `gain list` row. |
| `practice/Som-Practice-Room.km` | Whether one room accepted practice or gain. |
| `gear/Som-Alignment.km` | The side read from score. |

Load the library directory. The walk includes each chain folder. The view rules are split across `level/Som-Goal-View.km`, `level/Som-Level-Directive.km`, `area/Som-Area-Choice.km`, and `command/Som-Command-Choice.km`. The route conclusion is in `route/Som-Route.km`. The relations live in their own files. One file on its own does not answer a question.

`som-kind` is `level` unless `som-kind-in` is set. `som-score-every` is `15` unless `som-score-every-in` is set. `(the text-gen of *Goal)` is one sentence, for example "The level goal is level 5 at bold."

## How to load it

At the `KM>` prompt, start from the repository root. A backslash in a Knowledge Machine string is an escape, so use forward slashes.

```
clojure -M:repl
```

```
KM> (load-lib "src/resources/som-component-library" :silent t)
```

`:silentp t` is the same flag. The answer is the list of forty-four pathname-names. `:errors` is empty when the directory loads.

`startup.sh` and `startup.cmd`, from the repository root, start the prompt and load the shipped library and then this directory. The shipped library takes several minutes.

From Clojure, pass the knowledge base in and keep the returned `:kb` and `:query`:

```clojure
(require '[som.kb :as kb]
         '[som.km.engine :as engine])

(def session (engine/session))
(def loaded
  (kb/load-lib (:kb session)
               (:query session)
               "src/resources/som-component-library"
               :silent true))
```

`:value` is the pathname-names. `:lisp` is empty. This directory has no `.lisp` files and no `.kml` files. `README.md` is skipped.

The acceptance tests load this path and leave the shipped tree alone:

```
clojure -M:test -n som.km.som-agent-goal-test
```

## How to ask

One query answers one event. Build three frames on the loaded knowledge base.

1. A `Som-Level-Goal`. Assert `som-target-level`, `som-risk-ceiling`, and `som-budget-minutes`. Use `0` for an open-ended budget. Assert a missing budget as `0` as well. An empty budget slot is treated as open-ended pace, and a later numeric comparison can record an error if some other rule still reads it.
2. A `Som-Progress-Projection`. Assert `som-event` as `score`, `death`, or `view`, and the counters and world facts for this step. `som-opponent-outlook` stays empty. The caller does not copy it from a mobile.
3. A `Som-Goal-View` whose `som-goal` is the goal and whose `som-progress` is the projection. Mobile readings are instances of `Som-Mobile-Reading`, and `som-reading` on the projection is a `:seq` of them in the order the caller already chose.

```
(*Goal has (instance-of (Som-Level-Goal))
           (som-target-level (5))
           (som-risk-ceiling (bold))
           (som-budget-minutes (10)))

(*Clock has (instance-of (Som-Progress-Projection))
            (som-event (view))
            (som-level (1))
            (som-elapsed-minutes (0))
            (som-score-count (1))
            (som-prior-notch (cautious))
            (som-cooldown-steps (0))
            (som-saves (1))
            (som-score-steps (0))
            (som-areas-known (t)))

(*View has (instance-of (Som-Goal-View))
           (som-goal (*Goal))
           (som-progress (*Clock)))
```

Read the answer off `*View`:

```
KM> (the som-pace of *View)
KM> (the som-notch of *View)
KM> (the som-licensed-rule of *View)
KM> (the som-attempts of (the som-licensed-directive of *View))
```

Pace is one of `sampling`, `behind`, `on`, `ahead`, or `open`. The notch is `cautious`, `steady`, or `bold`. A licensed directive has `som-allow-social` `no`, a role, and attempts. Each attempt is `(:args role category preference argument)`. Several attempts are one `:seq`. A hold is `(:seq)`. Rules 1 and 14, and a stale clock, license no directive.

The caller stores whatever the next event must see: the notch, `som-cooldown-next`, the score counters, and the saves. The next event is a new projection and a new view. Start that question from the knowledge base that loaded the library, so one clock is not still present when the next question runs.

## One situation per agentic player

Each agentic player is a `Som-Agentic-Player`. The slots this library declares are `*Fluent`. A value asserted in a player's situation is stored there, and a query run there keeps its answer there. A second player's situation has its own values. The class rules stay in `*Global` and are visible from the player's situation.

```
(*PlayerA has (instance-of (Som-Agentic-Player)))

(in-situation *PlayerA
  (*Goal has (instance-of (Som-Level-Goal))
             (som-target-level (5))
             (som-risk-ceiling (bold))
             (som-budget-minutes (10))))
```

Assert the projection and the view the same way, inside that situation. Read the answer there:

```
(in-situation *PlayerA (the som-pace of *View))
```

When that player's bootstrap has completed, assert it in the same situation:

```
(in-situation *PlayerA
  (*PlayerA has (som-bootstrap (t))))
```

`(the som-bootstrap of *PlayerA)`, read inside `*PlayerA`, answers `(t)`. The slot stays empty until that assertion. A second player is a second `Som-Agentic-Player`. The names `*Goal`, `*Clock`, and `*View` can be used again. Their values, and `som-bootstrap`, stay in the situation where they were asserted.

## Explored areas

`som-areas-known` still means the areas listing has been stored. It does not say the character has been there. Assert each area on the projection, inside the player's situation. `som-explored` is `t` when the caller asserts that this character has been in that area. Leave it empty when the area was only listed.

```
(in-situation *PlayerA
  (*Grove has (instance-of (Som-Area))
              (som-area-name ("Grove"))
              (som-level-low (1))
              (som-level-high (10))
              (som-explored (t))))

(in-situation *PlayerA
  (*Warren has (instance-of (Som-Area))
               (som-area-name ("Warren"))
               (som-level-low (5))
               (som-level-high (8))
               (som-explored (t))))

(in-situation *PlayerA
  (*Clock has (som-area ((:seq *Grove *Warren)))))
```

Read the choice on the view:

```
(in-situation *PlayerA (the som-optimal-area of *View))
```

At level 6 the answer is `(*Warren)`. Both ranges contain 6, and Warren's low end is higher, so its content is closer to the character. The same low end breaks by the lower high end. The same bounds keep the caller's sequence order. An area above or below the character's level is not chosen. A listed area that has not been explored is not chosen. The slot is empty when no explored area contains the level. The choice does not license a directive and does not name a path.

Until a situation is entered, a query in `*Global` reads the values stored there. Once a situation has been entered, read a fluent from inside that situation.

## Learned commands

Bootstrap asserts each learned command inside the player's situation, then one `:seq` on that situation. The file is `som-player-command.km`. On a case-insensitive volume `som-known-command.km` is the class file `Som-Known-Command.km`.

A stored category is the heading. A blank category uses the SUMMARY heading for that name. `consider` is not on that index. Its blank heading is `information / communication`. A stored category wins when it differs from the SUMMARY heading. The names `where` and `delete` are the strings `"where"` and `"delete"`. Those spellings are reserved as symbols. `quit`, `delete`, `murder`, `steal`, `password`, and `!` are not commands the catalog may return.

```
(in-situation *PlayerA
  (*Cmd-north has (instance-of (Som-Known-Command))
               (som-command-name (north))
               (som-command-category (movement))))

(in-situation *PlayerA
  (*Cmd-where has (instance-of (Som-Known-Command))
               (som-command-name ("where"))))

(in-situation *PlayerA
  (*PlayerA has (som-known-command ((:seq *Cmd-north *Cmd-where)))))
```

`som-known-command` is `N-to-1`. A later bootstrap replaces that seq with `now-has`. A second `has` keeps the first seq.

Assert `som-command-goal` on the view when asking which commands serve a goal. The symbols are `explore`, `recover`, `survey`, `escape`, `engage`, `look`, and `checkpoint`. `explore` and `recover` use `movement`. `survey` uses `"information / communication"`. `escape` and `engage` use `combat`. `look` uses `objects`. `checkpoint` uses `other`.

```
(in-situation *PlayerA
  (*View has (som-command-goal (explore))))

(in-situation *PlayerA (the som-command-for-goal of *View))
```

The answer is the allowed known commands whose heading is that category, in the order bootstrap stored them. An unknown goal, or an empty `som-command-goal`, is empty. Another player's situation does not see the seq.

Hunt rules 10 and 12 send `som-exploration-attempt`. Rule 10 is one `(:args travel movement <direction> "")` for each untried exit that is a known allowed movement command, in exit order. When none of the exits are, the attempts are `(:seq)`. Rule 12 is `recall` when that command is known as `movement`, then `where` when that command is known as `"information / communication"`. One of those is a single `:args`. Neither is `(:seq)`. The other hunt attempts still name their verb. The attempts do not read `som-optimal-area` and do not name a path. `som-optimal-area` remains the explored area that contains the level.

Closed words such as `behind`, `on`, `open`, `cautious`, `steady`, and `bold` are ordinary symbols. Comparisons against an empty slot use `=` or `has-value`. A `<` or `>` on an empty slot records an error.

## What the components leave out

The engine has already applied four safety rules before this view is asked: danger at `play.flee_hp`, leave a threat the engine did not engage, stand after a position refusal, and an owed reply. A personality yield is absent. The separate gear query derives re-gearing strategies; the level hunt does not automatically select them. `som-gear-gate` is read only by hunt rule 1. Hunt rules 10 and 12 send `som-exploration-attempt`. The legacy declaration-only classes are not interpreted as new level, area, or command policies. The area choice does not change hunt rule 3.

Rules 5 and 6 wait until a player proposal names the fight marker. `som-opponent-outlook` stays empty, and no rule reads it. A fighting view that misses rule 4 does not hold and does not flee for an opponent. A survey reading is rule 8. An idle fighting view with no mobiles and no exits is rule 14.

## Routes

The [route package guide](route/README.md) documents player-scoped map assertions,
path queries, conclusion contracts, fresh search contexts after map changes,
and verification examples.

## Remembered mobiles

The [mobile package](mobile/README.md) stores encounters in the player's situation
and supports finding previously observed experience sources for an active level
goal. It separates positive current-level experience evidence from unknown or
outdated observations, reuses the explored-room route chain, and selects a
reachable last-known location by observed yield and encounter order. Remembered
mobiles do not replace fresh `som-reading` observations or the hunt policy.
The package guide documents assertions, conclusion contracts, validity, and tests.

## Gear sources and recovery

The [gear guide](gear/README.md) documents room pickups, purchases, corpse loot,
and observations on players and mobiles. A fresh request can derive a bounded
strategy through purchases and intermediate mobs while accounting for equipped
prerequisites and one purse. Planning uses hypothetical states, leaves observed
ownership unchanged, and reconsiders loss after death from a new confirmed
snapshot. Examine-only sightings do not grant acquisition or combat permission.
