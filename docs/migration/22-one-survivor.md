# Step 22: One survivor

When several sources contribute, one survivor remains. A situation climb keeps the earlier duplicate. A looping residue that is not itself the current goal is evaluated and written back. A prototype already included through `cloned-from` is unified again, and a user appending slot can then join values that share a cloned source. A cyclic clone explanation is dropped. Pieces of an `&` expression are linked in the situation that was current. A class with nothing stored has Thing as its superclass, and the built-in superclass slots stay empty until something stores them. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(Fred has (color (red)))`, then `(new-situation)`, then `(Fred has (color (blue)))`, then `(a Situation with (supersituations (_Situation1)))`, then a theory that stores Fred's color as red and is made visible, then `(in-situation _Situation2 (the color of Fred))` answers `(red blue)`. The local color of Fred in `_Situation2` is empty before that read. `color` is multivalued and fluent.

`(Sue has (age (30)))`, then `(Fred has (age ((the age of Sue))))`, then a read of `(the age of Fred)` whose depth limit is already past, answers `(30)` and stores `(30)` on Fred. `(Fred has (age ((the age of Fred))))` then `(the age of Fred)` still answers nil and leaves `age` empty, because that residue is the goal already under way. `(1 + 2 + 3)` under a depth limit of 0 still answers nil.

`(parts has (combine-values-by-appending (t)))`, then `(a-prototype Cell)` whose root has a Wall with origin `proto`, then a separate Wall whose `cloned-from` is that prototype wall and whose code is `mine`, then `_Cell1` with `instance-of` Cell, `cloned-from` the root, and that wall as a part. `(the parts of _Cell1)` answers one part. That part's origin is `proto` and its code is `mine`. `(_Cell1 &! _Cell2)` with two ordinary walls, and no partial prototype in force, keeps both walls.

A `cloned-from` explanation whose second element is the clone itself is dropped when the clone is built. A `cloned-from` explanation whose second element is still a prototype remains. Records stay oldest first.

`(a Situation)` leaves the current situation `*Global` and turns inverse installation on. Storing `(Sue & _X)` on Fred's `loves` in that new situation leaves Sue's `loves-of` in `*Global`. The outer value stays in the situation that was named.

`(_Cat1 has (instance-of (Cat)))` then `(_Cat1 isa Thing)` answers `(t)`. `(every Thing)` includes `_Cat1`. `(the all-subclasses of Thing)` includes `Cat`. `(Thing subsumes Cat)` answers `(t)`. `(the superclasses of Integer)` answers `(Number)`, and a direct read of the stored slot is empty. `(the subclasses of Sequence)` answers `(Pair Triple)`. `(the all-superclasses of Integer)` answers `(Thing Number)`. A stored superclass list still wins. `(Cat has (subclasses (Tabby)))` then `(the subclasses of Cat)` answers `(Tabby)`.

On the HTTP service, `(Thing subsumes Cat)` is HTTP 200, the value is `[{"symbol": "t"}]`, and the statistics line contains `inferences`.

## Where this port differs from the Lisp

The climb keeps the earlier copy of a duplicate value list. A later copy is dropped. The sources of those lists stay. The following combine of a local list with that climb uses the ordinary duplicate rule and keeps the later copy, which is what `get-slotvals` does.

A stored residue that still needs evaluation, and is not itself the current goal, is evaluated with fail mode fail. The answer is written back, including a nil answer, unless the slot has `dont-cache-values`. A refusal is returned as it is and is not stored. A residue that is itself the current goal returns nil with no message, and the slot reader can cache that nil. A fully evaluated stored list is returned as it stands. Nothing is printed. The Lisp evaluates that same residue. The self-goal specimen still removes the slot.

A prototype already reached through `clone-built-from` is not unified again. A prototype reached through `cloned-from` is unified again. For that pass the query records `partially-included-prototype`, and the previous value is restored afterwards, including when an abort is thrown. The binding is not stored on the knowledge base. While that binding is set, an eager unify of two knowledge-base objects on a user appending slot joins values that share a cloned source with `&!`. The gate looks at the direct `cloned-from` values and then `prototype-participant-of`. The pairing uses the transitive `cloned-from` closure, the shared prototype roots, and classes that subsume either way. Equal values and a pair already pending equality are left unjoined. One evaluation combines the joined expression. A built-in appending slot, and `/==`, still append. The two Lisp lists that can block this heuristic start empty and are not consulted, so the gate stays open. The Lisp scores every permutation of the two value lists before it pairs them. This pass takes the first shared source it finds. The review's phrase "merge with `&&`" is wider than that gate: the lists are not combined with `&&`, and `clone-built-from` does not enter this pass.

A translated explanation is dropped when its `cloned-from` record's second element is not a prototype. The Lisp comment names a load flag for that check. The Lisp code does not read the flag, and this check runs during a load too. The older same-node test stays omitted. A clone's ordinary `cloned-from` explanation, whose second element is still the prototype, is kept.

An `&` expression's pieces are linked in the situation chosen for the situation that is current. The situation already chosen for the assertion is left outside that call. The outer value stays where the assertion put it.

A class with nothing stored and no built-in link has Thing as its superclass. A stored list wins, and a built-in link in the side table wins over that fallthrough. `get-vals` of a built-in superclass or subclass slot stays empty. `(the superclasses of ...)` and `(the subclasses of ...)` are those walks, with `remove-subsumers` or `remove-subsumees` applied when the slot asks for it. `(the subclasses of Sequence)` follows the side table, so Pair comes before Triple. Thing is not a subclass of Thing, so the fallthrough does not loop. `(every Thing)` includes an instance of an unplaced class. It also includes the class frame, and a slot, because a frame with no `instance-of` is a Thing and Slot's built-in parent is Thing. A class stored as its own subclass throws on `(the subclasses of Cat)` and on `(the all-subclasses of Cat)`. The `has` that stored the link still answers `(Cat)`. The Lisp reports that cycle and continues with the name removed.

`reset` notes the built-in classes in list order, so Integer stays the first object. It does not store the side-table links on the frames.

## Lisp files this step used

`frame-io.lisp` supplies the earlier duplicate on a supersituation climb, the Thing fallthrough, the side table of built-in links, and the situation left outside an `&` inverse. `interpreter.lisp` supplies the looping residue. `get-slotvals.lisp` supplies the immediate superclass and subclass walks. `prototypes.lisp` supplies the second unify and `remove-clone-cycles`. `lazy-unify.lisp` supplies the appending-slot merge.

## What is still absent

Explanation records stay oldest first. `(comment ...)`, `(show-comment ...)`, `(explain-all)`, and `(clear-explanations)` stay refused. `(justify)` still omits the from-classes suffix. `(sanity-check ...)` answers `(t)` and leaves its body unread. `(anonymous-instancep ...)`, `(has-value ...)`, and `(function ...)` stay refused. `showme` and `showme-all` stay refused. `do-script` and `in-every-situation` stay refused. The same explanation is the next wrap-up step.

## How to try it

`clojure -M:test` runs the suite, including these survivors. At the `KM>` prompt, the color climb in the section above answers `(red blue)`. `(Thing subsumes Cat)` answers `(t)`. `(the subclasses of Sequence)` answers `(Pair Triple)`. `q` leaves. `POST /query` with `(Thing subsumes Cat)` returns HTTP 200 and the value `[{"symbol": "t"}]`.
