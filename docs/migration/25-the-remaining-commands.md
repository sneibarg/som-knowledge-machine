# Step 25: The remaining commands

`showme`, `showme-all`, and `evaluate-all` print. `is-true`, `all-true`, and `some-true` test triples. `do-script` runs a script. `in-every-situation` stores an assertion that a new instance runs, and a save writes that command back. `thelast`, `exists`, `has-value`, `print`, and `format` run. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(Fred has (color (red)))` then `(showme Fred)` answers `(Fred)`, and the text contains `(Fred has` and `(color (red))`. `(showme (the color of Sue))` answers nil, and the text says `No frames to show`. `(showme Fred "file.km")` writes the frame, and the text says `(Output sent to file "file.km")`. `(showme-here Fred)` prints the frame in the current situation.

`(Fred has (color (red)) (Age (3)))` then `(showme-all Fred)` prints `Age` before `color`. `(every Cat has (color (black)))` and `(_Cat1 has (instance-of (Cat)) (color (red)))` then `(showme-all _Cat1)` prints the two color rule sets joined by `&&`.

`(color has (instance-of (Slot)))` then `(evaluate-all Fred)` prints `  (color (red))` and answers `(Fred)`.

Two `(a Cat)` forms, then `(thelast Cat)`, answers the newer name.

`(has-value (the color of Fred))` is `(t)` when red is stored, and nil when the slot is empty. `(has-value (1 + 2))` is `(t)`. `(exists (the color of Fred))` records the renamed warning and answers `(t)`.

`(is-true (:triple Fred color red))` is `(t)`. A missing value is nil. `(:triple (1 + 2) > 0)` is `(t)`. A value that is not a triple records the triple sentence and answers nil. `(all-true nil)` is `(t)`. `(some-true nil)` is nil.

`(print (1 + 2))` answers `(3)`, and the text contains `(3)`. `(format nil "~a" (1 + 2))` answers the one-element list of `(3)`. `(format t "~a" 1)` answers `(t)`. `(km-format nil "~a" "hi")` includes the quotes. A flag other than `t`, `nil`, or `NIL` records the second-argument sentence and leaves the arguments unread.

`(new-situation)`, a script whose action adds green, then `(do-script Script)`, leaves Fred's color green.

`(in-every-situation Situation (TheSituation has (color (red))))` then `(a Situation)` stores red on that situation. A save writes `TheSituation`. A fresh `(load-kb ...)` then `(a Situation)` stores red again. `(in-every-situation Cat ...)` records that Cat is not a subclass of Situation.

`(Animal has (superclasses (Thing)))` and `(Cat has (superclasses (Animal)))`, then `(the most-specific of (:set Animal Cat))` is `(Cat)` and `(the most-general of (:set Animal Cat))` is `(Animal)`.

On the HTTP service, `(has-value (1 + 2))` is HTTP 200, the value is the symbol `t`, and the statistics line contains `inferences`.

## Where this port differs from the Lisp

The review names `nowexists` with the commands a transcript calls. The interpreter has no `(nowexists ...)` handler. The only call of that function is commented out. `(nowexists Fred)` is a syntax error. The slot `nowexists` stays the built-in inertial fluent it already was.

`showme` with one argument prints every situation and every theory. `(showme expr file)` prints every situation and the visible theories, and the empty-frames sentence still goes to the answer text. `(showme-here expr)` prints the current situation and the visible theories. `showme-all` sorts slot names with `string<` on the symbol name, so an upper-case name comes before a lower-case name. `(evaluate-all ...)` reads every instance of `Slot`. A user slot is included when that slot is an instance of `Slot`.

`(in-every-situation ...)` stores the assertion on the situation class. `TheSituation` is stored as `#,Self`, and a user's `Self` is stored as `SubSelf`. Reading the assertion binds `Self`, so `#,Self` becomes the new situation and `SubSelf` is put back to `Self` before the assertion runs. The save writes `TheSituation` and `Self` again. The class test is `is-subclass-of`, so `Situation` itself qualifies.

`(the most-specific of ...)` and `(the most-general of ...)` run. They call `remove-subsumers` and `remove-subsumees`. `remove-subsumees` compares each class with the whole list, so a subclass that appears after its superclass is dropped. A custom aggregation function stays refused. `(anonymous-instancep ...)` and `(function ...)` stay refused.

## Lisp files this step used

`stack.lisp` prints `showme`, `showme-all`, and `evaluate-all`. `interpreter.lisp` holds `is-true`, `all-true`, `some-true`, `do-script`, `in-every-situation`, `thelast`, `exists`, `has-value`, `print`, `format`, and `km-format`. `frame-io.lisp` runs the assertions of a new instance and defines `remove-subsumees`. `writer.lisp` writes `(in-every-situation ...)` for a subclass of `Situation` and restores `TheSituation` and `Self`. `nowexists` is defined in `frame-io.lisp` and is not dispatched.

## What is still absent

`(anonymous-instancep ...)` stays refused, and `(function ...)` stays refused. `(sanity-check ...)` answers `(t)` and leaves its body unread. An action precondition that goes through `(a Thing with ...)` still stops the action. `fastsave-kb`, `fastload-kb`, `faslsave-kb`, and `load-newest-kb` stay refused. `(SETQ ...)` at the prompt stays refused. A custom aggregation function stays refused. `(explained-by ...)` stays refused. A cached explanation stays unported. Next is the small texts: the exponent width of a number below 1, the extra statistics parenthesis, and `(version)` when a transcript needs it.

## How to try it

`clojure -M:test` runs the suite, including these commands. At the `KM>` prompt, `(has-value (1 + 2))` answers `(t)`. `(showme Fred)` after `(Fred has (color (red)))` prints the frame. `q` leaves. `POST /query` with `(has-value (1 + 2))` returns HTTP 200 and the symbol `t`.
