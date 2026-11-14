# Step 20: Stored flags

A stored flag changes the next read. `(no-inheritance)` skips inheritance and subslots. `set-filter` filters. `(sometimes ...)` evaluates its body. A default is applied once. A top-level query turns inverse installation back on. A load leaves inverses off when the knowledge base had them off. A deletion writes the inverse of `<>`. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(sometimes (1 + 2))` answers `(3)`. The constraints flag is set.

`(Fred has (color (red (sometimes (a Cat)))))` then `(the color of Fred)` answers `(red _Cat1)`. The next read of that slot answers the same list and creates no further instance.

`(every Cat has (color (black)))` then `(_Cat1 has (instance-of (Cat)) (color ((no-inheritance))))` then `(the color of _Cat1)` answers nil. `(color has (subslots (hue)))` then `(_Cat2 has (hue (red)) (color ((no-inheritance))))` then `(the color of _Cat2)` answers nil. `(_Cat3 has (instance-of (Cat)) (color (red (no-inheritance))))` then `(the color of _Cat3)` answers `(red)`. `(_Cat4 has (instance-of (Cat)))` then `(the color of _Cat4)` answers `(black)`. `(_Cat5 has (instance-of (Cat)) (color ((no-inheritance) (:default white))))` then `(the color of _Cat5)` answers nil.

`(every Measurement has (value ((set-filter pair-filter))))` then an instance whose value is `(:pair 1 *foot)`, `(:pair 2 *foot)`, `(:pair 1 *yard)`, `(:pair 2 *yard)`, and `green` answers `((:pair 1 *foot) (:pair 1 *yard) green)`. `PAIR-FILTER` keeps the first pair of each unit. `(set-filter no-such-filter)` beside `red` and `blue` answers `(red blue)` and records `Unrecognized set-filter`.

`(Fred has (color ((:default (a Color)))))` then `(the color of Fred)` answers one Color instance. The next read answers that same instance and creates none. `(Sue has (color (blue (:default red))))` answers a list that holds blue and red. After `(age has (cardinality (N-to-1)))`, `(Pete has (age (30 (:default 40))))` then `(the age of Pete)` answers `(30)`. `(Ann has (color ((<> red) (:default red))))` then `(the color of Ann)` answers nil. `(Bob has (color ((<> red) (:default blue))))` then `(the color of Bob)` answers `(blue)`. `(every Cat has (color ((:default black))))` then an instance's color is `(black)`.

`(disable-installing-inverses)` answers `(t)` and leaves inverse installation off. The next `(Fred has (loves (Sue)))` turns it on, and `(the loves-of of Sue)` answers `(Fred)`.

In a new situation, `(Fred has (loves (Sue)))` then `(_Move has (del-list ((:triple Fred loves Sue))))` then `(do-and-next _Move)` leaves `(the loves of Fred)` nil, and Sue's `loves-of` holds `(<> Fred)`. `(Fred also-hasnt (loves (Mary)))` leaves Mary's `loves-of` empty. A deletion of `t` leaves `t`'s `loves-of` empty.

A save of a knowledge base whose inverse installation is off contains `(disable-installing-inverses) ; This knowledge base had inverse installation off` after the enable line. `(load-kb ...)` of that file leaves the flag off. A save whose flag is on omits that comment, and the load leaves the flag on.

On the HTTP service, `(sometimes (1 + 2))` is HTTP 200, the value is `[3]`, and the statistics line contains `inferences`. The prompt prints `(3)` and then the statistics line.

## Where this port differs from the Lisp

`(no-inheritance)` changes the slot read. The Lisp also requires `*use-no-inheritance-flag*`, which starts nil and is never set. Subslots, inherited rules, and a default folded into that same list are skipped. A local value stored beside the constraint stays. Constraints are still collected.

`set-filter` applies `pair-filter`. The Lisp applies the named function when `*remove-violating-instances*` is set, and that flag starts nil, so the stock clause returns the original values. The name matches without regard to case. The first pair of each unit is kept, and a value that is not a pair is kept. An unrecognized name records `Unrecognized set-filter` and leaves the values. The read stores the filtered list through the ordinary slot write.

`(sometimes ...)` evaluates its body when the expression is read and when a stored value list is read. While a constraint is being enforced, `sometimes` answers the symbol `t`. `(sanity-check ...)` answers `(t)`. The sanity flag starts unset, and the body stays unread.

A default body runs once, against the intermediate values, and the concrete value is cached. The next read returns that value. A single-valued clash drops the default. A value that fails the constraints is dropped. A multivalued slot keeps a local value and a default that agrees with the constraints.

A top-level query turns inverse installation on when reset statistics is enabled. That flag starts enabled. When it is disabled, the caller's inverse flag stays. The Lisp `reset-inference-engine` enables inverses whenever the top-level keyword asks for a statistics reset, including when the counter-zeroing flag leaves the counters alone. `reset` and a direct store leave the flag as it stands, so a later direct store of Fred loves Sue leaves `loves-of` empty.

`write-kb` writes `(enable-installing-inverses)` before the parameter block. When the knowledge base had inverse installation off, the port writes `(disable-installing-inverses)` on the next line. A load of that file leaves the flag off. The Lisp file ends on the enable line, so a load of a Lisp save ends with inverses on. A top-level `(save-kb ...)` after `(disable-installing-inverses)` turns the flag on before the write, so that file omits the extra line. The load leaves the inference counters as they stand.

A deletion through `del-list` writes `(<> value)` on the slot and `(<> frame)` on the inverse when both are knowledge-base objects, the slot records inverses, and the value is a concept that records inverses. `t` is a built-in instance, so its inverse exclusion is omitted. `delete-val` and `also-hasnt` remove the value and leave the inverse exclusion unwritten.

## Lisp files this step used

`interpreter.lisp` supplies `(sometimes ...)` and `(:default ...)`. `get-slotvals.lisp` supplies the `(no-inheritance)` skip and the default second pass. `constraints.lisp` supplies `set-filter`, `pair-filter`, and the default filter. `frame-io.lisp` supplies the inverse of `<>`. `loadkb.lisp` supplies the enable on a top-level reset and the order of the enable line in a save.

## What is still absent

`(sanity-check ...)` answers `(t)` and leaves its body unread. `(anonymous-instancep ...)`, `(has-value ...)`, and `(function ...)` stay refused. `showme` and `showme-all` stay refused. `do-script` and `in-every-situation` stay refused. One survivor when several sources contribute is the next wrap-up step.

## How to try it

`clojure -M:test` runs the suite, including stored flags. At the `KM>` prompt, `(sometimes (1 + 2))` answers `(3)`. `(every Cat has (color (black)))`, then `(_Cat1 has (instance-of (Cat)) (color ((no-inheritance))))`, then `(the color of _Cat1)` answers nil. `q` leaves. `POST /query` with `(sometimes (1 + 2))` returns HTTP 200 and the value `[3]`.
