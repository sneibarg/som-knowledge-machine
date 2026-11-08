# Step 11: Explanations

`(why)` reads the explanation store. A slot value that came from a class rule, a clone, or an explicit `(explanation ...)` form can say where it came from. The prompt and the HTTP service both call the same engine function. The printer still writes the KM form. English sentences wait for step 14.

## What you can do now

`(why)` on a fresh knowledge base answers nil and prints `There are no answers to explain!`.

`(every Cat has (color (black)))`, then `(_Cat1 has (instance-of (Cat)))`, then `(the color of _Cat1)` answers `(black)`. `(why)` and `(why (:triple _Cat1 color black))` answer `(t)`. The text contains `(:triple _Cat1 color black [in *Global]) because:` and `RULE: (every Cat has (color (black)))`.

`(Fred has (color (red)))` then `(why (:triple Fred color red))` answers `(t)` and the text contains `(no explanation available)`. A value written with no source has nothing to record.

`(Fred has (loves (Sue)))` then `(explanation (:triple Fred loves Sue) ((added-at Person "by hand")))` answers `(t)`. `(why (:triple Sue loves-of Fred))` prints the forward triple `(:triple Fred loves Sue` and `RULE: (added-at Person "by hand")`. The lookup uses the slot and its inverse.

`(a-prototype Cat)`, then that root `has (color (black))`, then `(end-prototype)`, then `(_Cat1 has (instance-of (Cat)))`, then `(the color of _Cat1)`, then `(why (:triple _Cat1 color black))` prints `cloned-from` and the prototype name. The same record stays on the clone that was bound away. `(the cloned-from of _Cat1)` still includes the prototype.

`(why (Fred))` records `Bad argument to (why ...)` and answers nil. `(no-explanations)` answers `(t)` and a later class rule is not recorded. `(explanations)` answers `(t)` and recording is on again. `(explanations color)` records that slot and its inverse.

A fluent `color` explanation written while the current situation is `_Sit1` is stored on `explanation_Sit1`. `(why)` in `_Sit1` prints the rule. `(why)` in `*Global` does not. A non-fluent `instance-of` explanation written in `_Sit1` is stored on the global `explanation` property and is visible from `*Global`. The same record written in both places is kept once. The copy written first survives, and a different global record still follows it.

`(justify (:triple _Cat1 color black))` answers `(t)`. The text contains `subgoal` and the class rule. `(get-justification (:triple _Cat1 color black))` answers a one-element list of that text.

On the HTTP service, `(every Cat has (color (black)))`, then `(_Cat2 has (instance-of (Cat)))`, then `(the color of _Cat2)`, then `(why)` is HTTP 200. The value is `[{"symbol": "t"}]`. The text contains `(every Cat has (color (black)))`. `(a Cat)` stays HTTP 501.

## Where this port differs from the Lisp

Explanations are oldest first. The Lisp keeps the newest first, so the same deduplication keeps the newest record there and the earliest record here.

`remove-clone-cycles` is not run. A binding copies the bound-away frame's records onto the survivor and leaves them on the bound-away frame. The Lisp deletes that frame's structure. The merge does not drop a `remove-subsumers` record whose triple has disappeared.

`(why)` prints the KM rule. Comment text, `ENTRY TEXT`, and `EXIT TEXT` are absent, because comment storage is not ported. `(justify)` prints the developer-mode lines (`subgoal ... Computed from:` and the KM rule, or `(unrecorded!)`). `*developer-mode*` stays nil, and `*justify-leaves*` stays nil. `make-phrase` is step 14. A justification does not walk comment-tag subgoals, so the depth of 20 is not reached by those subgoals.

A cached explanation is not stored. A `:set` explanation is not stored. `modify-set` is not applied. An odd source path prints as `(|<location unknown>| expr)`. The Lisp sentence `Even path length` is not recorded.

`(explanations)` answers `(t)`. The Lisp returns the flag itself. `(explain-all)`, `(clear-explanations)`, `(comment)`, `(show-comment)`, `(show-explanations)`, and `(catch-explanations)` stay refused.

`(projected-from ...)` is followed when a record already contains it. Nothing writes that record until step 12 projects. `(a Cat)` outside prototype mode stays refused. A slot read that was cached before a prototype existed stays empty. The step 10 gaps stay: the stored prototype definition spells `(a-prototype Class)`, classification through subsumption is not called, a second prototype unify is not pushed, the protoinstance redirect to `*Global` records no warning, and `evaluate-paths` skips `<>` and classification.

## Lisp files this step used

`explain.lisp` supplies the explanation property, the two-direction lookup, `(why)`, `(justify)`, `(get-justification)`, and `build-rule`. `interpreter.lisp` supplies the handlers and `process-km1-result`, which records the commented expression when a slot read has a target. `frame-io.lisp` supplies `remove-sources-from-vals` and the merge inside `km-bind`.

## What is still absent

English answers. Situations other than `*Global` as a mode, actions, theories, and writing a projection. Loading and saving. Trace and statistics. Embedded Lisp. `(a Cat)` as a creation form outside prototype mode. Comment storage, `(explain-all)`, and `(clear-explanations)`.

## How to try it

`clojure -M:test` runs the suite, including explanations. At the `KM>` prompt, `(every Cat has (color (black)))`, then `(_Cat1 has (instance-of (Cat)))`, then `(the color of _Cat1)`, then `(why)` prints the class rule. `q` leaves. `POST /query` with `(why)` after the inherited color of `_Cat2` answers `(t)` on the same service. `(a Cat)` is still refused.
