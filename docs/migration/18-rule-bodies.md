# Step 18: Rule bodies

A class rule can choose a branch, walk a collection, keep a tagged value, and keep the values of one class. The prompt and the HTTP service both call the same engine function. A definition whose body uses `(if ...)` now classifies.

## What you can do now

`(if t then 1 else 2)` answers `(1)`. `(if (not t) then 1 else 2)` answers `(2)`. `(if nil then 1)` answers nil and records no error. `(if t then 1)` is that same form with else nil. `(if f then 1 else 2)` answers `(1)`. The atom `f` evaluates to the list `(f)`, and the false test looks at the whole answer. The else branch runs when that answer is the atom nil, the symbol `f`, or the symbol `F`. A condition this step does not run, such as `(showme 1)`, refuses the query. Neither branch creates an instance.

`(allof (:set 1 2 3) where (It > 1))` answers `(2 3)`. `(oneof (:set 1 2 3) where (It > 1))` answers `(2)`. `(forall (:set 1 2) (It + 1))` answers `(2 3)`. `(allof (:set 1 2) must (It > 0))` answers `(t)`. The same test with `(It > 1)` answers nil. `(allof nil must (showme It))` answers `(t)`, and the test is left unevaluated. `(forall nil (showme It))` answers nil, and the body is left unevaluated. `(allof2 (:set 1 2) where (It2 > 1))` answers `(2)`. The same quantifiers with a trailing `2` substitute `It2`, so a nested walk can still name the outer `It`.

`(allof ?x in (:set 1 2 3) where (?x > 1))` answers `(2 3)`. `(forall ?x in (:set 1 2) (?x + 1))` answers `(2 3)`. `(forall cat in (:set 1) It)` records that the second argument should be a variable. The printed form is the short one, and the sentence says "second argument" even though the variable is written first. `(theoneof (:set 1) where t)` answers `(1)`. `(theoneof (:set 1 2) where t)` answers `(1)` and records that the expression was expected to return a single value.

`(forall-seq (:seq 1 2 3) where (It > 1) (It + 1))` answers `((:seq 3 4))`. A failed constraint is dropped. A nil success stays, so `(forall-seq (:seq 1) where t nil)` answers a sequence whose element is the empty list. A success equal to the symbol `to-remove` is dropped with the failures, so `(forall-seq (:seq 1) where t to-remove)` answers `((:seq))`. `(forall-bag (:bag 1 2 3) where (It > 1) (It + 1))` answers `((:bag 3 4))`. A bag also drops a nil success, so `(forall-bag (:bag 1) where t nil)` answers `((:bag))`. `(forall-seq nil It)` answers nil and records no error. `(forall-seq ?x in nil It)` records that the value should be a single sequence. The printed form includes `where t` and `?x`, because the short form is rewritten before that check. A variable that is not a variable is reported on the short form, before the rewrite.

`((:set _Cat1 _Dog1) called Fred)`, after those frames store the tag, answers `(_Cat1)`. `(_Cat1 uniquely-called Fred)` is the same filter. A miss such as `(_Cat1 called Sue)` answers nil and records no error. `(fail-noisily)`, then the same miss, records the called/uniquely-called sentence. `(a Cat called Fred)` answers `(_Cat1)`, stores `(called (Fred))`, and turns the tags flag on. `(a Cat uniquely-called Fred)` also turns the constraints flag on, and `(the uniquely-called of _Cat1)` answers `(Fred)`. `(a Cat called (a Dog))` records that the tag must be an atom or a constraint, creates nothing, and still turns the tags flag on. The bare form indents that dash by four spaces. The `with` form indents it by three. `(a Cat called Fred with (color red))` records the bad slot structure and creates nothing.

Inside an open prototype, `(a Cat called Fred with (color ((a Color))))` stores a Color instance on `color` before the form returns, and `(the called of ...)` answers `(Fred)`.

`(the Color color of Fred)`, when Fred's color holds `_Red1` and the symbol `red`, answers `(_Red1)`. `(the * color of Fred)` keeps both. `(the Wing (parts *) of Fred)` walks one level of `parts` and keeps the wing. `(the Number number of (:set x y))` answers `(2)`. `(the Cat number of (:set x y))` answers nil and records no error.

`(every Cat has (label ((if (the color of Self) then named else unnamed))))`, then a red cat, makes `(the label of _Cat1)` answer `(named)`. A cat with no color answers `(unnamed)`, and that empty color read records no error.

`(every Colored has-definition (instance-of (Cat)) (color ((if t then red))))`, then a cat whose color is red, makes `(the color of _Cat1)` answer `(red)` and adds Colored.

On the HTTP service, `(if t then 1 else 2)` is HTTP 200, the value is `[1]`, and the statistics line contains `inferences`.

## Where this port differs from the Lisp

The handlers follow `interpreter.lisp`. The condition of `(if ...)` uses the default fail mode. The branches use the caller's fail mode, and the target is left unused. A short quantifier rewrites to its `where` form and runs again. `(?expr uniquely-called ?tag)` rewrites to `called`.

`(the Class slot of frame)` keeps a value when the stored class test succeeds. Thing is not a superclass of a user class that names no superclass, so `(the Thing slot of frame)` drops a value whose only class is that user class. A number stays under Number.

The quiet warning inside a missed `called` is a comment in the Lisp, and it stays unprinted. The top-level fail mode starts as `:fail`. `(fail-noisily)` sets it to `:error`, and the next miss records the sentence.

An action precondition that goes through `(a Thing with ...)` still stops the action.

## Lisp files this step used

`interpreter.lisp` supplies `(if ...)`, `called`, `uniquely-called`, the `allof` / `oneof` / `forall` family, the sequence and bag forms, the `*2` and `?var in` forms, and `(the Class slot of frame)`.

## What is still absent

`(anonymous-instancep ...)` and `(has-value ...)`. `Entity.km` uses both inside rules that also use `(if ...)` and `forall-seq`, so that file still stops. A rule that only needs the forms this step runs now produces the slot value. `Door.km` has neither `has-definition` nor `(if ...)`.

`(function ...)` stays the embedded-Lisp refusal. Instance `also-has`, `also-hasnt`, and `now-has`. `(the1 ...)`, `(the2 ...)`, `(the3 ...)`, and `(theNth ...)`. Sequence `append` and `reverse`. `(no-inheritance)`, `set-filter`, `showme`, `do-script`, `is-true`, `all-true`, `some-true`, and `in-every-situation`. Those are the next wrap-up steps.

## How to try it

`clojure -M:test` runs the suite, including rule bodies. At the `KM>` prompt, `(if t then 1 else 2)` answers `(1)`. `(allof (:set 1 2 3) where (It > 1))` answers `(2 3)`. `(a Cat called Fred)` answers `(_Cat1)`. `q` leaves. `POST /query` with `(if t then 1 else 2)` returns HTTP 200 and the value `[1]`.
