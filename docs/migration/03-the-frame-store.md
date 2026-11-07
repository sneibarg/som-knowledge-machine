# Step 3: The frame store

The port can now store frames. A knowledge base is a value the caller holds and passes back in. `put-vals`, `get-vals`, `add-val`, and `delete-val` return that value together with the Lisp result. The prompt and the HTTP service still only read an expression and print it. `som.km.engine/evaluate` does not read the knowledge base. The build still reports its evaluator as `read-print`.

## What you can do now

`som.km.frame/knowledge-base` builds an empty knowledge base. The current situation is `*Global`. The gensym counter is 0. Dereferencing is on, inverses are installed, and ununification stays off. One caller uses a given value at a time.

A frame has four facets, in the Lisp order: `own-properties`, `member-properties`, `own-definition`, and `member-definition`. A facet holds an ordered list of `(slot (value ...))`. In `*Global` the facet name is the facet. In another situation the name is the two symbol names written one after the other. A situation called `_Sit1` stores own properties under `own-properties_Sit1`. The underscore belongs to the situation name. The joined name is cached on the knowledge base, so a later call returns the same symbol. `get-vals` and `put-vals` use that situation when the caller leaves `:situation` out. A caller who passes `:situation` stores exactly there. `target-situation` returns the situation it was given. A later step can send a non-fluent or a prototype to `*Global` without moving this argument. `add-slotsvals` already passes the values into that function.

`add-val` appends on an ordinary slot. On `instance-of`, `classes`, `superclasses`, `member-type`, `subclasses`, `prototype-of`, `domain`, or `range`, the new value goes at the front. A value that is already there under structural equality is left where it is, and the result is the tail that starts at that value. `1` and `1.0` are both kept. Two copies of `(a Dog)` collapse. A single-valued slot, cardinality `1-to-1` or `N-to-1`, joins the values with `&` and installs an inverse only for the new value. The default cardinality is `N-to-N`. A built-in single-valued slot such as `cardinality` is `N-to-1` before any frame is stored. A declared cardinality is read in `*Global`. Two declarations use the first. An invalid declaration uses `N-to-N`. The inverse slot's cardinality is inverted when the slot itself has none. `wife-of` declared `1-to-N` makes `wife` `N-to-1`.

A ground instance receives an inverse link. `(Fred has (loves (Sue)))` stores `(Sue has (loves-of (Fred)))`. `instance-of` pairs with `instances`. A name that does not have a built-in inverse gains or loses the suffix `-of`. An `:args` value links its first argument, and a further argument when `inverse2`, `inverse12`, or `inverse3` is declared. The built-in `inverse2` pairs are `next-situation` with `after-situation`, and `prev-situation` with `before-situation`. An existential is left as data. `t`, the cardinalities, and the fluent statuses do not receive inverse links, so `(t has (open-of ...))` is not stored. `prototype-scope`, `ignore-inverses`, `cardinality`, and the other slots on that list do not install inverses. A member facet does not either.

`put-vals` replaces the values. An equal replacement leaves the slot as it is. Nil removes the slot and leaves the frame known. The inverses of values that leave are left in place. `delete-val` and an `overwriting` assertion remove them. `delete-val` of a missing value returns nil and a `:message`, and prints nothing. It de-duplicates with `km-equal?` first, so `1` followed by `1.0` collapses to `1` before the membership test. Deleting `1.0` finds nothing and leaves both numbers. Deleting `1` removes the slot.

`add-slotsvals` merges. Adding `(red)` twice leaves `(red)`. Adding `(<> 23)` onto `(red)` stores `(red (<> 23))`. Adding `(_Dog1)` and then `((a Dog))` stores `(((_Dog1) && ((a Dog))))`. `(a Dog)` does not cover `_Dog1`. Two copies of `(a Dog)` still match, because they are structurally equal. `==` appends, so `(a)` then `(b)` stores `(a b)`. `instance-of` through `add-slotsvals` appends and keeps the earlier value. The same slot through `add-val` inserts at the front. A more specific class is not removed. That filter is `is-subclass-of`, which waits for the taxonomy. On an own facet, `Self` is replaced by the frame, including `Self` inside `quote`. A member facet leaves `Self` alone. `instance-of` is written first. `domain` and `range` are copied onto the inverse slot in `*Global` from the pairs as they were written, before `Self` is replaced. `(loves has (domain (Person)) (range (Person)))` stores both on `loves-of`, and `Person` receives `domain-of` and `range-of` for `loves` and for `loves-of`.

`km-bind` records a binding beside the frames. The same object is left unchanged. A name that was never stored stays unknown: `_X` bound to `Fred` dereferences to `Fred`, and `known-frame?` stays false. A known frame that is bound stays known and loses its slot values. `get-vals` follows the binding, so it reads the target. A list is walked, and the same list is returned when nothing in it changed. Dereferencing can be turned off for later calls. A binding cycle is an error. Ununification stays off, so `ununify` returns nil and does not change the knowledge base. There is no setter for that flag.

`known-frame?` is membership in this knowledge base. `Thing` is a class by its name, and it is not a frame until a later step installs the vocabulary. `class?`, `slot?`, `simple-slot?`, `an-instance?`, `orphan?`, `anonymous-instance?`, and `named-instance?` read the store. `slot?` counts a built-in slot, and a frame whose global `instance-of` includes `Slot`. Subclasses of `Slot` are not walked. An unknown symbol is an orphan. `_Car1` is an anonymous instance even when it has no frame. A number, a string, a function, `(the-class ...)`, and a structured list are instances too.

`create-instance-name` advances the counter. The first name for `Person` is `_Person1`. The name is not added to the knowledge base. A name that is already known is skipped. An unknown parent draws no warning. The classifying `create-instance` is not ported.

`delete-frame` removes a known frame, clears the inverse links on `own-properties` and `own-definition` in every situation and theory, takes the name off the object stack, and records it on the deleted list. The name stays on the situation and theory lists. It is not uninterned. Other frames keep bindings that point at it. An unknown frame is an error. `delete-slot` removes one slot and uninstalls its inverses. A single-valued slot is split on `&` first, so each piece is uninstalled.

A stored expression is left as data. `(the age of Fred)` is stored as written. `(*black (@ Car color))` stores `*black`, because the stripped symbol is fully evaluated. `(the age of Fred (@ Car))` stays intact, because `(the ...)` is not fully evaluated. `prototype-scope` keeps its tags. The explanation those tags would have recorded waits.

The object stack lives on the query. Storage does not read it. A frame already on the stack stays where it is. Classes, slots, and `t` are not recorded. With the stack inactive, a new frame is recorded when its values change, and an inverse frame is recorded when it is created. With the stack active, the frame and its values are recorded even when the values are unchanged. The values are pushed from left to right, so the last value is at the front. Known frames are listed in the order they were first stored.

A frame name, a slot name, or a reserved keyword that cannot be stored is an error. The caller's knowledge base is left as it was. `get-unique-val` of several values returns the first and a `:message`. `:fail-mode :error` throws when the slot has no value.

## Where this port differs from the Lisp

The functions return a map with `:kb`, `:value`, and `:query`. A deleted value that was not present also has `:message`. The Lisp prints that line and returns nil. A bad frame or slot throws. The Lisp prints the error and returns nil. Cardinality and inverse messages are not printed.

An `&` expression is opened and its pieces are installed in the situation already chosen for the assertion. The Lisp writes `:situation` outside that call, so the pieces would be installed in the current situation.

The joined situation facet is cached on the knowledge base. The Lisp caches it on the facet symbol's property list. Known frames are returned in insertion order. The Lisp walks a hash table, so its order is not this order.

`known-frame` here is membership only. The Lisp also treats a built-in name as known. Those frames arrive with the vocabulary. `valset-subsumes-valset` compares structure. An existential does not cover a different value. Subsumption replaces this in a later step. `is-subclass-of` is not called, so a subsumers or subsumees slot only drops a value that is structurally equal.

`delete-frame` always clears inverses on `own-definition` as well as `own-properties`. The Lisp walks `own-definition` only when `*are-some-definitions*` is set, and that flag starts nil. Storage does not set it. The deleted name stays on the situation and theory lists.

`add-slotsvals` returns the frame. The Lisp discards its return value. `put-vals` returns the frame, including when the values were already stored. A binding cycle throws. The Lisp loops. Binding to nil clears a known frame's slots. A stored nil is not followed, which is the same result as an absent binding. Ununification data is not recorded.

`classify`, explanations, the `un-done` cache, and `km-int` are not called. A stored expression stays data. `create-instance` is not ported.

## Lisp files this step used

`frame-io.lisp` supplies the facets, the store operations, cardinality, inverses, situations, bindings, and deletion. `loadkb.lisp` supplies the idea of a known frame and of deleting one frame's properties. The hash-table log and undo wait. `kbutils.lisp` supplies `classp`, `slotp`, `simple-slotp`, `is-an-instance`, `orphanp`, and `anonymous-instancep`. `explain.lisp` supplies `desource+decomment-top-level`, used when an own facet stores a fully evaluated value. `header.lisp` supplies the flag defaults: dereferencing on, inverses installed, the object stack inactive, and ununification off.

## What is still absent

The built-in vocabulary and `reset-kb`. The goal stack. A query that runs. Inheritance, unification, constraints, prototypes, and recorded explanations. Situations beyond a name on the knowledge base. Loading and saving.

## How to try it

`clojure -M:test` runs the suite, including the store examples. At the `KM>` prompt, `(Fred has (color (red)))` is still printed as text. It is not stored.
