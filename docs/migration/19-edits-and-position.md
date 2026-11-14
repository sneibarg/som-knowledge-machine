# Step 19: Edits and position

An instance can gain, lose, or replace its own slot values. A query can read one place in a list, or build a sequence. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(Fred also-has (color (blue)))`, after Fred's color is red, answers `(Fred)`, and `(the color of Fred)` answers `(red blue)`. `(Fred also-has (color (red)))` again leaves that same list. `(Fred now-has (color (green)))` replaces it, and `(the color of Fred)` answers `(green)`. `(Fred now-has (loves (Mary)))`, after loves held Sue, answers `(Fred)`. `(the loves of Fred)` answers `(Mary)`, `(the loves-of of Sue)` answers nil, and `(the loves-of of Mary)` answers `(Fred)`.

`(Fred also-has (color red))` records the bad structure and leaves green in place. `(1 also-has (color (red)))` records that the expression does not evaluate to a KB object name, answers nil, and creates no instance.

`(Fred also-hasnt (color (red)))`, after the color is `(red blue)`, answers `(Fred)` and leaves blue. `(Fred also-hasnt (color (green)))` records no error and leaves blue. `(Fred also-hasnt (loves (Sue)))` clears loves and loves-of. `(every Cat also-hasnt (color (red)))` answers nil and records that also-hasnt cannot be used with an every expression. The class expression is left unevaluated. `(1 also-hasnt (color (red)))` records the same object-name sentence, and the reprinted form is `(1 also-has (color (red)))`.

`(Fred now-has)`, after classification is turned back on and Fred already owns a house that matches a House-Owner definition, adds House-Owner. `(Sue also-has)` on the same facts adds no class. `(Pete also-has (owns (_House1)))` adds House-Owner.

Inside an open prototype, `(a Cat)` then `also-has` of `(color ((a Color)))` stores a Color instance. `now-has` of `(size ((a Size)))` stores the expression `(a Size)`.

`(the1 color of Fred)`, when the color is `(red blue)`, answers `(red blue)`. `(theNth 1 of (the color of Fred))` answers `(red)`. `(theNth 2 of (the color of Fred))` answers `(blue)`. `(the1 parts of Fred)`, when the parts are `(:pair wing 1)` and `(:pair tail 2)`, answers `(wing tail)`. `(the2 parts of Fred)` answers `(1 2)`. `(theNth 1 of (the parts of Fred))` answers `((:pair wing 1))`. `(the3 of (:pair x y))` answers nil and records no error. `(the2 of red)` answers nil and records no error. `(theN 2 of (:pair x y))` answers `(y)`. `(theNth 5 of (:set x y))` answers nil and records no error.

`(theNth 0 of (a Cat))` answers nil, records that the index should be a non-negative integer, prints `(the 0 of (a Cat))`, and creates one instance. `(theNth nil of 1)` records that the index did not return a value, and records the integer sentence. `(theNth (showme 1) of (a Cat))` refuses the query and creates no instance.

`(1 append 2)` answers `((:seq 1 2))`. `((:bag 1) append (:bag 2))` answers `((:bag 1 2))`. `((:seq 1) append (:bag 2))` answers `((:seq 1 2))` and records that the elements should be both sequences or both bags. `(nil append (:seq 1))` answers `((:seq 1))`. `((:pair x 1) append (:seq y))` answers `((:seq (:pair x 1) y))`. `(reverse (:seq 1 2 3))` answers `((:seq 3 2 1))`. `(reverse nil)` answers nil and records no error. `(reverse (:bag 1))` answers nil and records that the value is not a sequence. The sentence names `(:seq <e1> ... <en>)`.

On the HTTP service, `(theNth 2 of (:set x y))` is HTTP 200, the value is `[{"symbol": "y"}]`, and the statistics line contains `inferences`.

## Where this port differs from the Lisp

The handlers follow `interpreter.lisp`. `(the1 slot of frame)`, `(the2 slot of frame)`, and `(the3 slot of frame)` rewrite to `(the1 of (the slot of frame))` and run again. The general forms are `(theN n of frame)` and `(theNth n of frame)`. The slot shorthand stops at the3.

`(the1 of ...)` keeps a value that is not a structured list, so a plain multi-value slot comes back whole. `(the2 of ...)` and `(the3 of ...)` drop that value. A structured value yields the argument at that place. `(theN ...)` counts the keyword in the length. A place past that length is dropped, and an index of 1 keeps the whole value. An empty `(:seq)`, `(:pair)`, or `(:function)` is rejected or collapses before that length rule can show.

The integer check prints `(the <expr> of <frame>)` for both `(theN ...)` and `(theNth ...)`. The sentence says non-negative. The check accepts an integer of 1 or more, so 0 is rejected. A refused index stops the query before the collection is read. A user-error index still reads the collection, and both sentences are recorded.

`also-has` stores by appending and classifies from the slots it wrote. An empty `also-has` names no slots, so classification stays off. `now-has` stores by overwriting and classifies with every definition eligible, including when the form names no slots. `now-has` leaves a prototype path as written. `also-has` evaluates that path while a prototype is open. `also-hasnt` deletes each named value, leaves a missing value in place, and does not classify. The object-name error reprints `also-has`.

`append` of a sequence and a bag records the mixed-elements sentence and answers a sequence. A pair, a quote, an atom, or a number is one element. `reverse` of nil answers nil. `reverse` of a bag, a pair, or an atom records the non-sequence sentence and answers nil.

## Lisp files this step used

`interpreter.lisp` supplies instance `also-has`, `also-hasnt`, and `now-has`, `(the1 ...)`, `(the2 ...)`, `(the3 ...)`, `(theN ...)`, `(theNth ...)`, `append`, and `reverse`.

## What is still absent

`(anonymous-instancep ...)` and `(has-value ...)`. `Entity.km` still stops on those calls. `(function ...)` stays the embedded-Lisp refusal. `showme` and `showme-all` stay refused.

`(no-inheritance)` is recorded and the read still inherits. `set-filter` is recorded and the filter is not applied. `(sometimes ...)` is not evaluated as a body. A default is included again on the next read. A top-level query does not turn inverse installation back on, and the inverse of `<>` is not written. `do-script` and `in-every-situation` stay refused. Those are the next wrap-up steps.

## How to try it

`clojure -M:test` runs the suite, including edits and position. At the `KM>` prompt, `(Fred also-has (color (blue)))` appends blue. `(theNth 2 of (:set x y))` answers `(y)`. `(1 append 2)` answers `((:seq 1 2))`. `q` leaves. `POST /query` with `(theNth 2 of (:set x y))` returns HTTP 200 and the value `[{"symbol": "y"}]`.
