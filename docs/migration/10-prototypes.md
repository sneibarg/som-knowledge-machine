# Step 10: Prototypes

`(a-prototype Class)` builds a prototype. A later slot read clones that prototype onto an ordinary instance. The prompt and the HTTP service both call the same engine function. `(a Cat)` at the top level stays refused.

## What you can do now

`(a-prototype Cat)` answers `(_ProtoCat1)`. `(_ProtoCat1 has (color (black)))` then `(end-prototype)` leaves prototype mode and answers `(t)`. `(_Cat1 has (instance-of (Cat)))` then `(the color of _Cat1)` answers `(black)`. `(the cloned-from of _Cat1)` includes the prototype, and `(the clone-built-from of _Cat1)` does too. The explanation on the clone is `(instance color black (cloned-from prototype clone participant))`. `instance-of` is copied and has no `cloned-from` explanation. The expressions recorded on the prototype are `((a-prototype Cat) (_ProtoCat1 has (color (black))) (end-prototype))`.

While the prototype is open, `(_ProtoCat1 has (color ((a Color))))` creates another participant. The later color read clones that participant as an ordinary instance whose name starts with `_`. The `instance-of` of that color answers `(Color)`. `(a-prototype Cat with (color ((a Color))))` stores the expression and does not create the color. The later color read stays refused, and the message names `(a Color)`.

A second prototype of Cat that only has `size` supplies `small` on a size read. The first prototype still supplies `black` on a color read. `(a-prototype Wine with (color (red)))` supplies red to a Cat whose superclasses include Wine. `(every Cat has (color (black)))` still supplies black beside a prototype that only has size.

`(the instances of Cat)` includes the prototype root. `(the all-instances of Cat)` leaves that root out and keeps `_Cat1`. `(the color of _ProtoCat1)` after `(end-prototype)` answers `(black)` and records that a protoinstance was queried outside prototype mode. `(the instance-of of _ProtoCat1)` answers `(Cat)` and does not record that sentence. A color read that found nothing before any prototype existed stays empty after the prototype is built.

`(a-prototype Cat)` while a prototype is already open records the nested-mode error and answers nil. The same form in a local situation, or in a theory, records the situation or theory error. `(a-prototype (1 + 2))` records that the class is not a symbol or a class description. `(clone Cat)` records that Cat is not a prototype. `(end-prototype)` when no prototype is open still answers `(t)`.

`(a Cat)`, `(a Cat with (color (black)))`, and `(a Cat called Fred)` stay refused. On the HTTP service, `(a-prototype Dog)`, then that root `has (fur (brown))`, then `(end-prototype)`, then `(_Dog1 has (instance-of (Dog)))`, then `(the fur of _Dog1)` is HTTP 200 and the value is `[{"symbol": "brown"}]`. `(end-prototype)` is `[{"symbol": "t"}]`. `(a Cat)` stays HTTP 501.

## Where this port differs from the Lisp

The stored definition says `(a-prototype Cat)`. The Lisp writes the misspelled head `a-prototoype` when the form has no slot pairs.

A prototype applies when the instance is already one of the prototype's `instance-of` classes. The classification test that would call subsumption is not run, so a description with slots does not bring a prototype in, and a failed classification does not fail the query. Several prototypes of one class are tried in the order they were stored.

The `unify-with-clone-of` goal is not pushed. A prototype already reached through `clone-built-from` is not unified again. The Lisp binds `partially-included-prototype` for that second pass, and an appending slot then merges with `&&`. That binding is not stored. `remove-clone-cycles` is not run.

A fact about a prototype participant is stored in `*Global` when the current situation is somewhere else. The Lisp warning for that redirect is not recorded. `prototype-scope` is registered on a class frame that already exists. Writing the scope does not create the class. The Lisp keeps `defined-prototypes` as a symbol property, so the class need not be a known frame. On `(a-prototype ...)`, `instance-of` and `prototype-of` are written first, and their inverses create the class before the scope is registered.

`(evaluate-paths)` outside prototype mode can still clone. It does not expand `<>` and it does not reclassify the clones. `also-has` stays refused, so it does not evaluate paths. `(a Class with ...)` stored as a slot value can evaluate its paths before that slot is written back. The graph above uses `(a Class)` inside `has`.

Explanations are oldest first. The Lisp keeps the newest first. Step 11 reads the four-element record. `(why)` stays refused. A slot read that was cached before the prototype existed is left as it is. Situations other than `*Global`, theories as a mode, projection, and supersituations are still later.

## Lisp files this step used

`prototypes.lisp` supplies `(a-prototype ...)`, `(end-prototype)`, `(clone ...)`, and the participant copy. Source 1 of `get-slotvals.lisp` runs that clone before the instance's own values and the class rules are collected. `frame-io.lisp` supplies `evaluate-paths` and the `defined-prototypes` registration on `prototype-scope`.

## What is still absent

`(a Cat)` as a creation form outside prototype mode. `(why)` and the rest of the explanation store. Situations other than `*Global`, actions, theories, and projection. Loading and saving. English answers. Trace and statistics. Embedded Lisp. A definition that reclassifies an instance. Prototype classification through subsumption.

## How to try it

`clojure -M:test` runs the suite, including prototypes. At the `KM>` prompt, `(a-prototype Cat)`, then `(_ProtoCat1 has (color (black)))`, then `(end-prototype)`, then `(_Cat1 has (instance-of (Cat)))`, then `(the color of _Cat1)` answers `(black)`. `q` leaves. `POST /query` with the Dog example above answers brown on the same service. `(a Cat)` is still refused.
