# Step 8: Subsumption

An existing instance can be tested against a description. The prompt and the HTTP service both call the same engine function. The test does not create a Skolem, and it does not unify the two sides.

## What you can do now

`(_Cat1 is '(a Cat))` answers `(t)` after `(_Cat1 has (instance-of (Cat)))`. `(_Dog1 is '(a Cat))` answers nil. `(_Cat1 is _Cat1)` answers `(t)`. `(_Cat1 is '(a Cat with (color (red))))` answers `(t)` when the color is red, and nil when it is blue.

A constraint in the description is checked in satisfaction mode. `(_Cat1 is '(a Cat with (color (red (must-be-a Color)))))` answers nil, and records no error, until `(red has (instance-of (Color)))`. It then answers `(t)`. `(must-be-a Thing)` answers `(t)`.

`(the Cat with (color (red)))` answers `(_Cat1)` when that cat is already stored. `(every Cat)` answers every stored cat, newest first. Two red cats make `(the Cat with (color (red)))` record that several values were found, and the answer is nil. `(the Cat with (color (green)))` records that no values were found. No frame is added.

`(the+ Cat with (color (red)))` answers the same stored cat. So does `(a+ Cat with (color (red)))`. A search with no match is refused, and HTTP stays 501. Two matches keep the first, which is the newest, and record that a single value was expected. `(every (airplane parts Wing))` answers `_Wing1` when that wing's `parts-of` is `airplane`.

`(_Pete has (owns (_Cat1)))` and then `(_Pete has (owns ((a Cat))))` leaves the slot as `(_Cat1)` once `_Cat1` is a Cat. The same `(a Cat)` beside an unclassified `_Dog1` stays as `((_Dog1) && ((a Cat)))`.

`((_Cat1) && ((a Cat)))` answers `(_Cat1)`. No new frame is created. `((_Cat1) && ((a Dog)))` keeps `(_Cat1 (a Dog))` and records no error. `((_Cat1) && ((a Cat with (color (red)))))` answers `(_Cat1)` and stores red on `color`.

`(Number subsumes Integer)` answers `(t)`. `(Integer subsumes Number)` answers nil. `(Animal subsumes Cat)` answers `(t)` after `(Cat has (superclasses (Animal)))`. `(Cat subsumes Animal)` answers nil. `(_Cat1 isa Cat)` answers `(t)`. `(_Cat1 isa Dog)` answers nil. `(1 isa Number)` answers `(t)`. `((:set 1 2) includes 2)` answers `(t)`. `((:set 1 2) is-superset-of (:set 2))` answers `(t)`.

`(a Cat)` is still refused, and HTTP stays 501. On that same service, after `_Cat1` is a red Cat, `(the Cat with (color (red)))` is HTTP 200 and the value is `[{"symbol": "_Cat1"}]`. `(every Cat has (color (black)))` is still refused.

## Where this port differs from the Lisp

`(the Class with ...)` searches and records an error when the answer is not one instance. It does not create an instance. `(the+ Class with ...)` searches first. The create that follows a miss is still refused, so the answer is the not-ported refusal. Several matches keep the first and record the unique-value error. Forcing inverses on a newly created instance waits with creation.

The candidate set is the object stack. The inverse read `(the Class invslot of value)` is not ported. That refusal is discarded, and the search continues. A user class does not gain Thing as a superclass. `(every Thing)` then answers `(Cat)`, the class frame, because a frame with no stored `instance-of` is a Thing. It does not answer `_Cat1`.

Two slotless class descriptions compare through the subclass links stored so far. No temporary instance is created. `('(a Cat with (color (red))) is '(a Animal))` is still refused, and that refusal leaves nothing behind. A leftover `(a Class)` after `&&` is not evaluated. Explanations are not recorded, and the subsumption trace is not printed. Situations other than the current one are not searched.

The covered-value check inside `&&` uses `&+`. That can write the instance's slots, as the color example does. A failed `&+` restores the knowledge base from the start of that attempt and records no error.

## Lisp files this step used

`subsumes.lisp` supplies `is0`, the description test, the path rewrite, `remove-subsuming-exprs`, and `valset-subsumes-valset`. The `every`, `the`, `the+`, `a+`, `is`, `isa`, `subsumes`, `includes`, and `is-superset-of` rows in `interpreter.lisp` call them. The store's redundant-value check calls `valset-subsumes-valset`. Lazy unification calls `remove-subsuming-exprs`.

## What is still absent

`(a Cat)` as a creation form. Inheritance and subslots. Prototypes. Explanations. Situations other than the current one, actions, theories, and projection. Loading and saving. English answers. Trace and statistics. Embedded Lisp.

## How to try it

`clojure -M:test` runs the suite, including subsumption. At the `KM>` prompt, `(_Cat1 has (instance-of (Cat)))`, then `(_Cat1 has (color (red)))`, then `(_Cat1 is '(a Cat with (color (red))))` answers `(t)`. `(the Cat with (color (red)))` answers `(_Cat1)`. `q` leaves. `POST /query` with that `the` expression, on a service that has already stored the cat, answers the same value the prompt would. `(a Cat)` is still refused.
