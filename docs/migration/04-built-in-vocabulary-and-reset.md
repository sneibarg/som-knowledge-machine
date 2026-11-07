# Step 4: Built-in vocabulary and reset

`reset` clears a knowledge base and rebuilds the built-in vocabulary. The caller passes the value in and uses the value that comes back. `som.km.engine/reset` and `som.km.frame/reset` are that function. The prompt and the HTTP service still only read an expression and print it. `(reset-kb)` is printed as text. It becomes a command when the interpreter can dispatch one.

## What you can do now

`knowledge-base` is still an empty frame store. Its default fluent status is `*Fluent`, `instance-of` is a non-fluent, and the optimization flags are clear. Classification starts enabled. `reset` is what installs the frames.

`reset` drops user frames, bindings, and the situation and theory name lists. The gensym counter returns to 0. The current situation returns to `*Global`. The default fluent status returns to `*Fluent`. `instance-of` returns to non-fluent. The flags `definitions`, `prototype-definitions`, `prototypes`, `subslots`, `constraints`, `tags`, and `defaults` return to false. A later query skips that work while the matching flag is false. Classification returns to enabled. The deleted-name list is kept. Dereferencing, inverse installation, and the active object stack keep the settings they had. `:value` is true. The returned query has an empty object stack. The goal stack is not stored on the query yet.

The rebuilt frames follow the tables at the top of `frame-io.lisp`. Every built-in class is stored with its superclass. `Thing` has none. `Integer` is a `Number`, and `Number` is a `Thing`. `Pair` and `Triple` are `Sequence`s. `Sequence`, `Aggregate`, and `Bag` are collection classes under `Thing`, and so are `Partition`, `Boolean`, `Situation`, `Cardinality`, `Fluent-Status`, `Class`, `Slot`, `String`, `Theory`, and `Function`. `Aggregation-Slot` is a `Slot`. The three aggregation classes sit under it. `Exhaustive-Partition` is a `Partition`.

A superclass assertion inserts the inverse at the front of `subclasses`. The link list names `Function` last among the direct subclasses of `Thing`, so `Function` is the first stored subclass. `Sequence` stores `(Triple Pair)`.

Every built-in slot is an instance of `Slot`, except the bag aggregators (`min`, `max`, `sum`, `average`, `difference`, `product`, `quotient`), which are instances of `Bag-Aggregation-Slot`, and the set aggregators (`first` through `number`), which are instances of `Set-Aggregation-Slot`. There is no seq aggregator. `domain`, `range`, `cardinality`, `inverse`, `inverse2`, and `inverse3` are ordinary `Slot` instances. After reset, `simple-slot?` is true for `domain`, because `Slot`'s `instances` include it.

`t` and `f` are instances of `Boolean`. `*Fluent`, `*Non-Fluent`, and `*Inertial-Fluent` are instances of `Fluent-Status`. `*Global` is an instance of `Situation`. The cardinalities `1-to-N`, `1-to-1`, `N-to-1`, and `N-to-N`, and the symbol `T`, are known frames with no `instance-of`. One hundred thirty-one frames are stored. `Integer` is the first.

A built-in slot other than `nowexists`, `add-list`, `del-list`, `pcs-list`, `ncs-list`, and `block-projection-for` has fluent status `*Non-Fluent`. `nowexists` is `*Inertial-Fluent`. Those five list slots and `block-projection-for` are `*Fluent`. Turning `instance-of` fluent moves `instance-of` and `instances` to `*Inertial-Fluent`. A user slot with no declaration has no stored status. Under the default `*Fluent` it is fluent. Under `*Non-Fluent` it is fluent only when its status is `*Fluent` or `*Inertial-Fluent`.

A non-fluent is stored in `*Global` when the caller leaves the situation out. `color` in `_Sit1` stays in `_Sit1`. `superclasses` is written in `*Global`. An `age` slot declared `*Non-Fluent` is written in `*Global` too. A caller who passes `:situation` stores in that situation. `add-slotsvals` runs the same choice on an explicit situation, and it passes the values. Once `instance-of` is fluent, adding `(instance-of (Situation))` stores the value in `*Global`. Adding `(instance-of (Dog))` stays in the current situation. `put-vals` does not pass the values, so the same `Situation` assertion stays in the current situation. A subclass of `Situation`, such as `MySit`, stays in the current situation as well. The subclass walk waits for the taxonomy. A prototype is not redirected. A theory is not recognized, so a non-fluent is stored in `*Global` while the current name is a theory.

An invalid default fluent status, an unknown optimization flag, and two disagreeing fluent statuses are errors. Several stored statuses use the first. That message is not printed.

## Where this port differs from the Lisp

The Lisp keeps the superclass and instance-of links in tables. `get-vals` of `Integer`'s superclasses is empty until something stores them, and `immediate-superclasses` reads the table when the slot is empty. `reset` here writes the links onto the frames, so `get-vals` returns them. Deleting the stored slot leaves it empty. The name lists still answer `class?` and `slot?`.

`known-frame?` is membership in this knowledge base. Deleting `Thing` makes it unknown until `reset` builds it again. The Lisp still answers yes from the name list. The cardinalities and `T` are stored as empty frames so membership can see them. The Lisp treats those names as known without a stored frame. `simple-slot?` of `domain` is true after `reset`, because `Slot`'s instances were stored. The Lisp slot frame starts empty, so `simple-slotp` is false until a user assertion fills it.

`append` is a built-in slot and a reserved keyword. `put-vals` refuses that name. The vocabulary writes the frame directly and links `Set-Aggregation-Slot`'s instances without calling `put-vals` on `append`. A later `put-vals` of `append` is still an error.

A symbol whose name contains `/` is one symbol. `/==` is built with no namespace, in the reader and in the vocabulary. The one-argument Clojure constructor would treat the slash as a namespace marker, and the name would no longer be a knowledge-base object.

`target-situation` takes the knowledge base so it can read fluent status. A prototype is not sent to `*Global`. A theory is not recognized. The `instance-of` exception matches `Situation`, `Slot`, `Partition`, or `Theory` by name. `is-subclass-of` is not called. `put-vals`, `get-vals`, `add-val`, and `delete-val` call it without the values. `add-slotsvals` passes the values.

`reset` returns a map whose `:value` is true. The Lisp returns `t` and prints a line. Nothing is printed. An invalid fluent status throws. The Lisp prints the error and returns nil. The situation and theory name lists return to `*Global` and empty. The Lisp recomputes situations from the instances of `Situation`, which the clear has removed. The object stack on the query is cleared. The goal stack is not stored yet. The Lisp clears both. No second banner is printed.

## Lisp files this step used

`frame-io.lisp` supplies the vocabulary tables, fluent status, and `target-situation`. `loadkb.lisp` supplies `reset-kb`. `initkb.lisp` calls `(reset-kb)` at startup and prints the banner. The banner is already printed by the prompt. This step does not print another one. `header.lisp` supplies the optimization flags and their initial values. `interpreter.lisp` supplies the four classes whose `instance-of` stays in `*Global` when that slot is fluent.

## What is still absent

The goal stack. A query that runs. `(reset-kb)` as a command. Inheritance, unification, constraints, prototypes, and recorded explanations. The part of `target-situation` that recognizes a prototype or a theory. Loading and saving.

## How to try it

`clojure -M:test` runs the suite, including the vocabulary. At the `KM>` prompt, `(reset-kb)` is still printed as text. It is not run. A test calls `som.km.engine/reset`.
