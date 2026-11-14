# Step 17: Definitions and classification

`(every Class has-definition ...)` stores a definition. An instance that matches it gains that class. The prompt and the HTTP service both call the same engine function. A slot read, a `has`, a new instance, a written `&`, and a load asked to evaluate instances each classify. A prototype applies through that test, including when the description names slots. Those attempts are counted.

## What you can do now

`(every House-Owner has-definition (instance-of (Person)) (owns ((a House))))` answers `(House-Owner)`. It does not create a house. The definition is stored on House-Owner's member-definition facet, and House-Owner is indexed on Person. Both classification counters stay at 0.

`(Fred has (instance-of (Person)) (owns (_House1)))`, after `_House1` is a House, makes Fred a House-Owner. `(every House-Owner has (title (owner)))` and then `(the title of Fred)` answers `(owner)`. `(Sue has (instance-of (Person)))` leaves Sue a Person. The attempted count moves for both. The succeeded count moves for Fred.

A definition without `instance-of` records the sentence "You must specify an `instance-of' slot value" and stores nothing. `(every House-Owner has-definition (instance-of ((a Person))))` records that the filler must be an atomic class name and creates no person. `(every 1 has-definition ...)` records that 1 is not a class name. `(1 has-definition ...)` records that 1 is not a knowledge-base object name, and that sentence still begins `(every 1 has-definition ...)`.

`(every House-Owner now-has-definition (instance-of (Person)) (color (red)))` replaces the definition. `(every House-Owner now-has-definition)` removes it. The definitions flag stays on.

`(Fred has-definition (instance-of (Person)) (owns (_House1)))` stores Fred's own definition. A later `(a Person with (owns (_House1)))` unifies with Fred.

`(_Person1 & _Person2)`, when `_Person1` is a Person and `_Person2` owns the house, answers `(_Person1)` and makes that survivor a House-Owner. `(_Person1 &? _Person2)` does not classify and does not add the class. `(a Cat)` and `(1 & 1)` leave both classification counters at 0. `(1 & 1)` also leaves the unification count at 0.

`(load-kb "path")` of a file that only stores the definition answers `(t)`. `(disable-classification)`, then a matching `has`, then `(enable-classification)`, then a load of the bare name `Fred`, leaves Fred's classes unchanged. The same load with `:eval-instances t` adds House-Owner.

A prototype whose scope is `(the-class Cell with (has-part ((a Nucleus))))`, and whose own slots include `(wall (rigid))`, gives `wall` to a Cell that has a Nucleus and adds Euk-cell. A Cell with no Nucleus stays a Cell and has no wall. An instance that is already an Euk-cell still receives `wall`. `(a Nucleus)` inside that description does not create another Nucleus.

`(the-class Cat)` answers `((the-class Cat))`. `(the-class Cat with (color (black)))` answers that description. Neither creates a cat.

`(every Colored has-definition (instance-of (Cat)) (color ((if t then red))))` stores the definition. `(the color of _Cat1)` on a red cat is refused, because `(if ...)` is not ported yet. The color stays stored.

On the HTTP service, `(every House-Owner has-definition (instance-of (Person)))` is HTTP 200 and the value is the symbol House-Owner.

## Where this port differs from the Lisp

The description is tested as `(a Class with ...)`, where Class is the instance's current class and the slot pairs are the definition's slots. The Lisp head is Thing, because every class sits under Thing. A user class is not stored under Thing here, so that head would fail before the slots were read. The definition's own `instance-of` stays in the slot pairs. `(Thing subsumes Cat)` is still nil.

A slot read classifies a knowledge-base object before the local value is read. The calls in `get-slotvals.lisp` are comments, and they would classify only when an instance is created and when `has` runs. The same frame is not classified again while that test reads one of its slots. A query with no definition and no slotted prototype still leaves both counters at 0, and that check does not read a slot.

`(a Cat)` names only `instance-of`. After `/==` is removed that list is empty, so creation does not classify. A `has` that names another slot does.

The new class is recorded with the definition as its explanation. Older `instance-of` explanations are left as they were. `make-assertions` is not run. Slots named by `slots-to-opportunistically-evaluate` are not read. A class that has not been declared draws no warning.

Installing an inverse does not classify the other frame. `(evaluate-paths)` does not classify the clones it builds. In prototype mode, a load asked to evaluate instances does not run the constraint pass. A number in that batch is skipped. The Lisp records that a number is not a knowledge-base object.

A prototype test that hits a form this step does not run is treated as unsatisfied, so the slot read continues. A member definition that hits `(if ...)` refuses the query. The checks that only skip a hopeless class are not used, so a definition is tested once the outer gate has passed.

`*RECURSIVE-CLASSIFICATION*`, `*INDIRECT-CLASSIFICATION*`, and `*CLASSIFY-SLOTLESS-INSTANCES*` stay at their defaults, which are all true. This step does not accept a `SETQ` of those names. `(disable-classification)` and `(enable-classification)` run. A `SETQ` of `*CLASSIFICATION-ENABLED*` or `*PROTOTYPE-CLASSIFICATION-ENABLED*` inside `load-kb` was already accepted.

An action precondition that goes through `(a Thing with ...)` still stops the action instead of counting as an unsatisfied precondition.

Finer classify trace comments are not printed.

## Lisp files this step used

`interpreter.lisp` supplies `has-definition`, `now-has-definition`, and `(the-class ...)`. `frame-io.lisp` supplies the parent index, `classify`, and the three ways a definition can apply: as a member, as another instance, and as a prototype scope. `prototypes.lisp` supplies the membership short-circuit. `get-slotvals.lisp` is where a slot read would have classified; those calls are comments.

## What is still absent

`(if ...)`, `allof`, `oneof`, `forall` and their `?var in` forms, `called`, `uniquely-called`, and `(the Class slot of frame)`. A component-library definition whose body uses one of those still refuses the query that evaluates it. `Entity.km` uses `forall` and `(if ...)`. Many class rules stored beside a definition do the same. `Door.km` itself still loads as an ordinary instance file. Those rule bodies are the next step.

Instance `also-has`. `(no-inheritance)` and `set-filter` still do not change the read. The explanation order, the file order, and the commands in the later wrap-up steps. The assertions slot and the opportunistic slot list.

## How to try it

`clojure -M:test` runs the suite, including definitions and classification. At the `KM>` prompt, `(every House-Owner has-definition (instance-of (Person)) (owns ((a House))))` answers `(House-Owner)`. `(_House1 has (instance-of (House)))`, then `(Fred has (instance-of (Person)) (owns (_House1)))`, makes `(the instance-of of Fred)` include House-Owner. `q` leaves. `POST /query` with `(every House-Owner has-definition (instance-of (Person)))` returns HTTP 200 and the symbol House-Owner. `(if t then 1 else 2)` is still refused.
