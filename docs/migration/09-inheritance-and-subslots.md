# Step 9: Inheritance and subslots

A slot read uses the local store, the rules on the instance's classes, and the values on the slot's subslots. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(every Cat has (color (black)))` answers `(Cat)`. `(_Cat1 has (instance-of (Cat)))` then `(the color of _Cat1)` answers `(black)`. `(the color of Cat)` answers nil. The rule is stored for members of Cat. Cat's own class is Thing, and Thing has no color rule.

`(every Animal has (color (black)))`, `(Cat has (superclasses (Animal)))`, and `(every Cat has (color (brown)))` give `_Cat1` both colors. A second `(every Cat has (color (black)))` on a class that already says black leaves one black. `(every Cat also-has (color (tan)))` adds tan. `(every Cat now-has (color (white)))` leaves white for an instance that has not been read yet. `Black` stays `Black`. `(every Cat has (owner (Self)))` answers `(_Cat1)` for that instance.

A read that finds nothing is remembered. `(every Cat has (color (black)))` after that empty read is still visible on the next `(the color of _Cat1)`, because asserting the rule clears the cache on Cat's instances. `(color has (subslots (hue)))` and `(_Cat1 has (hue (red)))` make `(the color of _Cat1)` include red. A local blue is kept beside it. `(hue has (subslots (shade)))` makes `(the all-subslots of color)` include hue and shade. `(the subslots of color)` stays the stored list `(hue)`.

`(the all-superclasses of Integer)` answers `(Thing Number)`. `(the all-superclasses of Cat)` answers `(Thing)` when Cat names no superclass. `(the all-classes of _Cat1)` answers `(Thing Cat)`. `(the all-classes of 1)` answers `(Thing Integer Number)`. `(the instance-of of 1)` and `(the classes of 1)` answer `(Integer)`. `(the all-superclasses of 1)` records that 1 is not a knowledge-base object. `(the subclasses of Sequence)` stays `(Triple Pair)`. `(the subclasses of Cat)` stays the stored children. `(the all-subclasses of Cat)` also includes the classes under those children. `(the instances of Cat)` stays the stored inverse. `(the all-instances of Cat)` includes a Tabby as well. `(the all-instances of Boolean)` answers `(t f)`.

`(every Cat has (color ((must-be-a Color))))` and a local `ink` make `ink` a Color. `(every Cat has (color ((mustnt-be-a Dog))))` with a Dog stored in the slot records a constraint violation and keeps the Dog. The stored member value still carries its `(@ Self Cat color)` source. The printed answer does not.

`(a Cat)`, `(every Cat has-definition ...)`, and `(why)` stay refused. A member rule whose value is `(a Cat)` stays refused, and that refusal is not remembered as a finished read. On the HTTP service, after `(every Cat has (color (black)))` and `(_Cat2 has (instance-of (Cat)))`, `(the color of _Cat2)` is HTTP 200 and the value is `[{"symbol": "black"}]`.

## Where this port differs from the Lisp

`superclasses`, `subclasses`, `instances`, `subslots`, and `superslots` are ordinary lookups. `(the subclasses of Sequence)` stays the stored `(Triple Pair)`. The `all-*` slots walk. `all-superclasses` adds Thing and leaves the class out. `immediate-superclasses` still does not invent Thing, so `(Thing subsumes Cat)` stays nil for a Cat that names no superclass. `(the all-subclasses of Thing)` includes that Cat anyway, because an unplaced class is listed under Thing for this walk. `(every Thing)` still answers `(Cat)`, the class frame.

`instances` and `all-instances` read the global store. Projection is not applied. Boolean and Fluent-Status use their built-in instances. A prototype participant is left out. There are none yet.

A `has-definition` is still refused, so classification does not reassign an instance's class. The classification flags stay on for the step that stores definitions. `(no-inheritance)` does not suppress inheritance or subslots. The flag that would turn that check on is unset.

The source wrapped around a class value covers an atom and a list. It does not split `&` or `&&`, walk an embedded `(a ...)`, or build a dotted source. A default expression is included again on the read. The extra default filter is not ported. Prototypes, projection, and supersituations contribute nothing.

An inherited `(a Cat)` stays refused. The refusal is not recorded as done. Existentials are not reified, because the current situation is `*Global`. The assertions-slot bookkeeping is omitted. `most-specific` and `most-general` stay refused. `check-slot` stays off.

A finished read writes the values on the instance and remembers the slot. `has` and `(every Class has ...)` clear that memory. A direct store does not. A frame that is not an instance of the class keeps a remembered empty answer. An instance that already stored black keeps black when the class rule is replaced with white, and the next read combines the stored values with the new rule.

A class that lists itself as a subclass makes `(the all-subclasses of Cat)` throw. `(the subclasses of Cat)` stays the stored list. A subslot cycle throws the same way. Situations other than `*Global` are not read.

## Lisp files this step used

`frame-io.lisp` supplies the class and subslot walks: `immediate-classes`, `all-superclasses`, `all-subclasses`, `all-classes`, `all-instances`, and `all-subslots`. `get-slotvals.lisp` supplies the local store, the subslot values, and the rules inherited from classes. The `every` `has`, `also-has`, and `now-has` rows in `interpreter.lisp` store those rules on the member facet and clear the cache. `explain.lisp` supplies the `(@ Self class slot)` wrapper.

## What is still absent

`(a Cat)` as a creation form. Prototypes. Explanations, including `(why)`. Situations other than `*Global`, actions, theories, and projection. Loading and saving. English answers. Trace and statistics. Embedded Lisp. A definition that reclassifies an instance.

## How to try it

`clojure -M:test` runs the suite, including inheritance. At the `KM>` prompt, `(every Cat has (color (black)))`, then `(_Cat1 has (instance-of (Cat)))`, then `(the color of _Cat1)` answers `(black)`. `(color has (subslots (hue)))` and `(_Cat1 has (hue (red)))` make the next color read include red. `q` leaves. `POST /query` with `(the color of _Cat2)`, on a service that has already stored the rule and the instance, answers the same value the prompt would. `(a Cat)` is still refused.
