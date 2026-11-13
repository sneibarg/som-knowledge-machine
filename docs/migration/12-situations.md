# Step 12: Situations, actions, and theories

A knowledge base can leave `*Global`. The current situation is part of the value the caller holds. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(new-situation)` creates `_Situation1`, enters it, and answers `(_Situation1)`. `(curr-situation)` answers the same name. `(end-situation)` and `(global-situation)` enter `*Global` and answer `(*Global)`.

`(in-situation _Situation1 (the color of Fred))`, issued from `*Global`, reads the slot there and then `(curr-situation)` is `*Global` again. Re-entering the situation that is already current leaves you there. A refusal from the situation expression is returned before situations mode changes. `(in-situation Fred)` records that Fred is not an instance of Situation, answers nil, and still turns situations mode on.

`(a Situation)` and `(a Theory)` create an instance outside prototype mode. `(a Cat)` and `(a Cat with (color (black)))` stay refused, with the same sentences as before. `(a-prototype Cat)` from inside a situation created by `(new-situation)` records `Can't enter prototype mode when in a Situation!`.

A fluent asserted in the local situation is visible there. The same slot read with an explicit `*Global` is empty. After `(new-situation)`, `(the color of Fred)` back in `*Global` records the situations-mode error and answers nil, including when red was stored in `*Global` before the mode was turned on. `instance-of` is universal, so `(the instance-of of X)` in `*Global` still works. `(the supersituations of _Situation1)` is `(*Global)`. Those two computed slots do not pass through the mode check.

`(location has (fluent-status (*Inertial-Fluent)))`, then a local `(Fred has (location (home)))`, then `(next-situation)`, then `(the location of Fred)` answers `(home)`. The frame records `(projected-from _Situation1)`. `(why)` follows that record into the previous situation and answers `(t)`. A ground fact there has no stored explanation, so the text says `(no explanation available)`. A plain fluent `color` does not project. `(age has (fluent-status (*Inertial-Fluent)))` and `(age has (cardinality (N-to-1)))` project `30` the same way. A `color` stored in `*Global` before `(new-situation)` is visible in the child through the supersituation climb.

`(a Theory)`, then `(secret has (fluent-status (*Non-Fluent)))`, then `(in-theory _Theory1 (Fred has (secret (hidden))))` stores `hidden` on that theory. The same slot in `*Global` is empty, and `(curr-situation)` is `*Global` again. `instance-of` and `superclasses` stay in `*Global` even inside a theory. `(see-theory _Theory1)` makes a fluent stored in the theory visible from `*Global`. The read copies that value onto the instance. `(hide-theory _Theory1)` answers `(t)` when nothing remains visible. The copied value stays. A fluent in that theory that was not read is absent after the hide.

`(_Move has (add-list ((:triple Fred color green))))` inside a local situation, then `(do _Move)`, asserts green in the next situation and returns to the old one. The answer is a one-element list of the next situation. `(do-and-next _Move)` stays in that next situation. A `del-list` of `(:triple Fred location home)` on an inertial slot blocks the later projection, so `(the location of Fred)` is nil.

The prompt prints `[_Situation1] KM>` in a local situation and `{_Theory1} KM>` in a theory. `*Global` stays `KM> `.

On the HTTP service, after the prototype fur check, `(new-situation)` is HTTP 200 and the symbol name starts with `_Situation`. `(global-situation)` is HTTP 200 and the value is `[{"symbol": "*Global"}]`. `(a Cat)` on that service stays HTTP 501.

## Where this port differs from the Lisp

The KM 1.4 fluent-status banner is not printed. Trace comments are not printed, including the warning when `prev-situation` has several values and the note that a situation name is bound to a different object. The first value is kept.

A refusal such as `(in-situation (a Cat))` returns before situations mode is turned on. The Lisp would evaluate `(a Cat)`, fail the class check, and still turn the mode on.

The shipped Lisp leaves the supersituation value re-read switched off. This port does the same. Own facts from supersituations and from visible theories are merged. Duplicate values on that climb keep the later copy. The Lisp keeps the earlier copy. Sources and comments on those facts are left in place. A supersituation cycle stops when a situation is seen again.

`*project-cached-values-only*` stays nil, so projection uses `prev-situation` only. Two or more projected values for a single-valued slot write the `ERROR!` sentences on `:text` and keep the first.

`also-has` as a user command stays refused. A deletion stores `(<> value)` through the frame store. The inverse `<>` is not written. A comparison against `(the ?x of ?y)` records that it is not ported yet and the action stops. A ground precondition goes through `(frame is '(a Thing with ...))`, and a description with slots is still refused, so that refusal is returned rather than treated as an unsatisfied precondition. Interactive preconditions stay off. The commented Event check and the second-time check stay inactive, as they do in the Lisp. Any named instance can be an action. `(a Thing)` stays refused.

`(result-of ...)` and `(precondition-for ...)` are stored. `(why)` prints them as `(|<location unknown>| ...)`. `projected-from` is followed and is not itself the printed rule.

An abort during a body leaves the temporary situation in force. Classification is turned off for an action and restored on a normal return and on an abort. `do-script`, `do-plan`, `in-every-situation`, and `is-true`, `all-true`, and `some-true` as user commands stay refused. `clear-situations` stays an embedded-Lisp refusal. `nowexists` is not ported. The step 10 and step 11 gaps stay.

## Lisp files this step used

`frame-io.lisp` supplies the situation transitions, `do-action`, theories, and the supersituation own-fact climb. `interpreter.lisp` supplies the situation, theory, and action handlers, and the prompt. `get-slotvals.lisp` supplies projection and the disabled parent-value switch.

## What is still absent

Loading, saving, and undo. English sentences. Trace and statistics. `do-script`, `do-plan`, and `in-every-situation`. `is-true`, `all-true`, and `some-true` as commands. Interactive preconditions, `nowexists`, and the fluent-status banner. `(a Cat)` outside prototype mode. `also-has` as a user command.

## How to try it

`clojure -M:test` runs the suite, including situations. At the `KM>` prompt, `(new-situation)`, then `(Fred has (color (red)))`, then `(the color of Fred)` answers `(red)`. The prompt shows the situation in brackets. `(global-situation)` returns to `KM> `. `q` leaves. `POST /query` with `(new-situation)` and then `(global-situation)` uses the same service. `(a Cat)` is still refused.
