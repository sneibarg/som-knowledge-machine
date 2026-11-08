# Step 7: Unification and constraints

Two values can be unified, and a constraint stored with a slot value is checked when that slot is read. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(_Cat1 & _Cat2)` answers `(_Cat1)` when both are instances of Cat. `_Cat2` then names `_Cat1`. `(*Fred & *Sue)` records an error and leaves both frames as they were. `(1 & 1)` answers `(1)`. `(1 & 2)` records one error, the two numbers are different, and the answer is nil. `(1 &? 1.0)` answers `(t)`. `(1 & 1.0)` answers `(1)`.

`&?` and `&+?` answer `(t)` or nil. The trial is discarded. Evaluating an argument still stores what that argument stores. `&+` of a Cat and a Dog, with no subclass link stored, answers nil and leaves the knowledge base unchanged. `&` of that pair answers the left instance, and its `instance-of` holds both classes. `&+!` of that pair answers nil and leaves the knowledge base unchanged.

`((_C1) && (_A1))` merges the pair when Cat is stored as a subclass of Animal. The answer is `(_C1)`, `_A1` names `_C1`, and `instance-of` keeps Cat. `((_Cat1) && (_Dog1))` keeps both values and records no error. The arguments of `&&` are sets. `(_Cat1 && _Dog1)` records that the arguments should be sets.

A single-valued `age` can hold `((_A & _B))` after a lazy unification. `(the age of _P1)` finishes that residue. `&!` stores the ground value and leaves no residue.

`(_C1 /== _C2)` stores the inequality. A later `&` records that constraint and does not merge the two. `(Pat has (color (red (must-be-a Color))))` then `(the color of Pat)` answers `(red)`, and `red` is an instance of Color. A slot that holds only `(must-be-a Color)` still answers nil, and the constraint remains. `(at-most 1 Cat)` on two Cat instances unifies them. The same constraint on two cats that are `/==` records an error and keeps both. `(at-least 2 Cat)` with one value does not create a filler and does not record an error. `(exactly 1 Cat)` with one value is quiet.

`(a Cat)` is still refused, and HTTP stays 501. `(1 & 1)` on that same service is HTTP 200 and the value is `[1]`. `(1 &? (a Thing))` answers `(t)`. `(1 & (a Coordinate))` answers `(1)`.

Pass `:query {:on-error :abort}` to `evaluate` and `(1 & 2)` answers nil, records the error, and the knowledge base is the one at the error. The default is continue. `:abort-silently` aborts the same way. `:debug` and `:break` continue. Nothing is printed.

## Where this port differs from the Lisp

`&&` skips a pair whose classes do not subsume. The expression keeps both values. It does not answer nil because one pair failed. It does not create an instance for `(a Class)`, and it does not drop a value because an existential covers it. Creation of `(a Cat)` and that covered-value check stay ahead.

Class subsumption uses the links stored so far, plus the built-in links. Thing is not added when a class does not name it. A Cat with no stored path to Thing is not counted by `(at-most 1 Thing)`. `(at-most 1 Cat)` counts a Cat. Constraints inherited from a class are not applied yet. The slot check uses the values in hand and does not read the slot again.

Only `*Global` is merged. Other situations, and copying a situation's contents, wait. Prototypes, explanations, and description subsumption wait. `set-filter` is embedded Lisp and is not applied. `sometimes` is not evaluated as a body. While a constraint is being enforced, `sometimes` answers the symbol `t`, and the slot reader does not treat that symbol as a list of values. `at-least` and `exactly` do not invent fillers. A violated value stays in the list, and the violation is recorded. `*sanity-checks*` stays nil. `(sanity-check ...)` still answers `(t)` and does not run its body.

A failed `&`, `&!`, `==`, `&&`, or `&+` restores the knowledge base from the start of that attempt when the attempt returns. An abort keeps the knowledge base at the error. A specific failure is recorded once. The generic sentence is not added after it. `(1 & 1.0)` answers `(1)` because the expression test uses `km-equal`. The value-level check uses `equal`, so `1` and `1.0` are different numbers when that check is reached. `((Fred == Sue) and (a Cat))` unifies the two sides and does not evaluate the cat. The packaged `and` writes the literal symbol `yy` in that position.

`/==` is its own inverse. The name contains a slash, so the inverse is stored on a symbol with no namespace. There is no separate list of user inequality slots. The fluent-instance shortcut is off. Deferred unification is commented out in the Lisp and is not implemented. Classification after a merge is not run.

`:on-error` stays through a top-level call, the way the fail mode does. There is no command to set it in this step.

## Lisp files this step used

`lazy-unify.lisp` and `constraints.lisp` supply unification and the constraint check. The unification rows in `interpreter.lisp` call them. The local read in `get-slotvals.lisp` enforces constraints after the values are computed. Breaking up `(a Class)` and `(a Class with ...)`, including `called` and `uniquely-called`, is the small part of `subsumes.lisp` that unification calls. `is`, path subsumption, and dropping a covered value stay in the next step.

## What is still absent

`(a Cat)` as a creation form. The general `is` test. Inheritance and subslots. Prototypes. Explanations. Situations other than `*Global`, actions, theories, and projection. Loading and saving. English answers. Trace and statistics. Embedded Lisp.

## How to try it

`clojure -M:test` runs the suite, including unification. At the `KM>` prompt, `(_Cat1 has (instance-of (Cat)))`, then `(_Cat2 has (instance-of (Cat)))`, then `(_Cat1 & _Cat2)` answers `(_Cat1)`. `(1 & 2)` records an error and answers nil. `q` leaves. `POST /query` with `(1 & 1)` answers the same value the prompt would. `(a Cat)` is still refused.
