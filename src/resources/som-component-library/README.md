# Springs of MUD component library

This directory is a Knowledge Machine component library for Springs of MUD. It answers one level-goal question: a score, a death, or a view of the current room. The caller keeps the clock, sends the line, and picks the catalog command. These components do not.

`(load-lib)` with no directory still reads the shipped library in `src/resources/km-component-library`. Load this directory by path. The slot list, pace bands, notch steps, and hunt rules are in [docs/reference/som-component-architecture](../../../docs/reference/som-component-architecture/README.md). Every class, relation, inverse, conclusion, helper, and rule slot is named in [objects.md](../../../docs/reference/som-component-architecture/objects.md).

## What was added

Nine `.km` files. Five classes subclass `Thing`. Four relations connect a view to its goal, its progress, its mobile readings, and the directive it licenses. The shipped `Goal` class stays an `Event`. These classes do not subclass it, and they do not reuse `has-goal`, `objective`, `agent`, `Action`, or `Planning`.

| File | What it declares |
| --- | --- |
| `Som-Level-Goal.km` | The goal. Kind defaults to `level`. The score cadence defaults to `15`. |
| `Som-Progress-Projection.km` | Facts the caller copies in for one event: level, experience, minutes, notch, combat, exits. |
| `Som-Goal-View.km` | The view that computes fraction, pace, notch, score due, and checkpoint due. |
| `Som-Mobile-Reading.km` | One mobile: name, consider outlook, fresh, and whether it is a player. |
| `Som-Level-Directive.km` | The first matching hunt rule, and the directive that rule licenses. |
| `som-goal.km` | `som-goal` / `som-goal-of`. The view is judged against the goal. |
| `som-progress.km` | `som-progress` / `som-progress-of`. The view is drawn from the projection. |
| `som-reading.km` | `som-reading` / `som-reading-of`. The projection includes the readings. |
| `som-licensed-directive.km` | `som-licensed-directive` / `som-licensed-directive-of`. The view is licensed as the directive. |

Load the directory. The view rules are split across `Som-Goal-View.km` and `Som-Level-Directive.km`, and the relations live in their own files. One file on its own does not answer a question.

`som-kind` is `level` unless `som-kind-in` is set. `som-score-every` is `15` unless `som-score-every-in` is set. `(the text-gen of *Goal)` is one sentence, for example "The level goal is level 5 at bold."

## How to load it

At the `KM>` prompt, start from the repository root. A backslash in a Knowledge Machine string is an escape, so use forward slashes.

```
clojure -M:repl
```

```
KM> (load-lib "src/resources/som-component-library" :silent t)
```

`:silentp t` is the same flag. The answer is the list of nine pathname-names. `:errors` is empty when the directory loads.

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

Closed words such as `behind`, `on`, `open`, `cautious`, `steady`, and `bold` are ordinary symbols. Comparisons against an empty slot use `=` or `has-value`. A `<` or `>` on an empty slot records an error.

## What the components leave out

The engine has already applied four safety rules before this view is asked: danger at `play.flee_hp`, leave a threat the engine did not engage, stand after a position refusal, and an owed reply. A personality yield, a gear strategy, and a catalog pick are absent. `som-gear-gate` is read only by hunt rule 1.

Rules 5 and 6 wait until a player proposal names the fight marker. `som-opponent-outlook` stays empty, and no rule reads it. A fighting view that misses rule 4 does not hold and does not flee for an opponent. A survey reading is rule 8. An idle fighting view with no mobiles and no exits is rule 14.
