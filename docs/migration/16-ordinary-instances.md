# Step 16: Ordinary instances

`(a Class)` creates an anonymous instance outside prototype mode. The prompt and the HTTP service both call the same engine function. A class rule whose value is `(a Class)`, a miss from `(the+ ...)`, and a leftover `(a Class)` inside `&&` each return that instance.

## What you can do now

`(a Cat)` answers `(_Cat1)`. `(the instance-of of _Cat1)` answers `(Cat)`. The instance is on the object stack, and the Skolem count moves. A second `(a Cat)` on the same value answers `(_Cat2)`. `(a Cat with (color (black)))` answers `(_Cat1)`, and `(the color of _Cat1)` answers `(black)`.

`(Fred has (color (red)))` and then `(a Cat with (color ((the color of Fred))))` stores the path. `(the color of _Cat1)` evaluates it and answers `(red)`. In prototype mode, `(a Class with ...)` still evaluates paths immediately. `(a-prototype Cat with (color ((a Color))))` does not create the color. After `(end-prototype)` and `(_Cat1 has (instance-of (Cat)))`, `(the color of _Cat1)` creates an instance whose name starts with `_Color`, and its `instance-of` is `(Color)`.

`(the+ Cat with (color (green)))` finds a stored red cat and answers that cat. A miss creates a new cat whose color is green. `(a+ ...)` is the same search. `(every Cat has (friend ((a Cat))))` and then `(_Cat1 has (instance-of (Cat)))` make `(the friend of _Cat1)` create another cat. The second read returns the same cat, and the slot is recorded as done.

`((_Cat1) && ((a Cat)))` still answers `(_Cat1)` and creates nothing. `((_Cat1) && ((a Dog)))` answers `(_Cat1 _Dog1)`, and `_Dog1` is a Dog. `((_Cat1) && ((a Cat with (color (red)))))` still answers `(_Cat1)` and stores red. `(1 & (a Coordinate))` still answers `(1)` and does not create a coordinate.

`('(a Cat with (color (red))) is '(a Animal))` answers nil, and no cat remains. After `(Cat has (superclasses (Animal)))`, the same form answers `(t)`, and no cat remains. `('(a Cat with (color (red))) is '(a Cat with (color (red))))` answers `(t)`. The same form with `blue` answers nil. The temporary instance is removed either way.

`(in-situation (a Cat))` creates the cat, records that it is not a Situation, and turns situations mode on. `(a Situation)` still creates a situation. `(a Cat called Fred)` stays refused. `(every Cat has-definition ...)` stays refused.

`src/resources/km-component-library/rkf-clib/components/core/Door.km` loads. `(a Door)` answers an instance whose name starts with `_Door`. `(the plays of` that instance`)` answers an instance of `Portal-Covering`. `(the is-part-of of` the door`)` answers an instance of `Architectural-Structure`.

On the HTTP service, `(a Cat)` is HTTP 200 and the symbol name starts with `_Cat`. `(if t then 1 else 2)` stays HTTP 501.

## Where this port differs from the Lisp

Classification does not run, so a new instance keeps the classes written on it. The assertions slot is not evaluated. Slots named by `slots-to-opportunistically-evaluate` are not read at creation. `(a Class called ...)` and `(a Class uniquely-called ...)` stay refused.

Outside prototype mode, a path in `(a Class with ...)` is stored and evaluated on the later slot read. The Lisp does the same. The temporary instance used by `('(a ...) is '(a ...))` is removed by restoring the knowledge base and the query. The Lisp undoes a checkpoint. The answer is the same, and nothing created for the test remains.

A class that has not been declared draws no warning. The Lisp warns.

## Lisp files this step used

`interpreter.lisp` supplies `(a Class)` and `(a Class with ...)`. `frame-io.lisp` supplies `create-instance` and the object-stack push inside `add-slotsvals`. `lazy-unify.lisp` evaluates a leftover existential on the second pass of `&&`. `subsumes.lisp` builds the temporary instance for one description subsuming another, then removes it.

## What is still absent

`has-definition`, classification, and the classification counters. `(if ...)`, `allof`, `oneof`, `forall`, `called`, and `uniquely-called`. Instance `also-has`. `(no-inheritance)` and `set-filter` still do not change the read. The explanation order, the file order, and the commands in the later wrap-up steps. The assertions slot and the opportunistic slot list. `Entity.km` in the component library uses `forall` and `(if ...)`, so those rules still do not answer.

## How to try it

`clojure -M:test` runs the suite, including ordinary instances. At the `KM>` prompt, `(a Cat)` answers `(_Cat1)`. `(every Cat has (friend ((a Cat))))`, then `(_Cat1 has (instance-of (Cat)))`, then `(the friend of _Cat1)` answers another cat. `q` leaves. `POST /query` with `(a Cat)` returns HTTP 200 and a symbol whose name starts with `_Cat`. `(if t then 1 else 2)` is still refused.
