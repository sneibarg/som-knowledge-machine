# Conventions of the Knowledge Machine sources

This note records the runtime settings, the data layouts, and the syntactic sugar used across `src/knowledge-machine/packages`. The roles of the files are in [Architecture.md](Architecture.md).

## Package and readtables

All of the engine is in the Lisp package `:km`. `header.lisp` creates it and stores the package in `*km-package*`. `*using-km-package*` is true in this build. `fastsave-kb` reads that flag.

`*km-readtable*` is a writable copy of the host readtable. Nearly every file selects it while loading so that `#$` is recognized:

```lisp
(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq *readtable* *km-readtable*))
```

`*case-preserving-readtable*` is a second copy whose readtable case is `:preserve`. `#$` switches to it for the duration of one form. Symbols are interned in `:km`, so `Car` and `car` are different frames.

## Reader macros

| Form | Where it is defined | What it does |
| --- | --- | --- |
| `#$form` | `case.lisp`, `hash-dollar-reader` | Reads `form` with case preserved and symbols in the `km` package. |
| `#tname` | `case.lisp`, `hash-t-reader`, only inside `#$` | Reads `name` in the package that was current outside the `#$`. Used to insert a Lisp variable. |
| `#,form` | `case.lisp`, `hash-comma-reader`, only inside `#$` | Reads `form` as `(unquote form)`. KM evaluates the unquote when the surrounding quoted expression is processed. It yields a list, so splicing into a surrounding list uses `#,` together with a dotted tail. |

`#$` inside `#$` also works, because the case-preserving readtable has the same dispatch entry. Calling `(hash-dollar)` from a Lisp prompt points the current readtable at `*km-readtable*` for interactive use.

A block comment is Lisp's `#| ... |#`. KM reuses that syntax as a comment tag on a value. `[tag]` attached to an expression is stored internally as `(comm [tag] Self)`. `Self` is rewritten to the concrete instance when the expression is applied to an instance or when a prototype is cloned. `km-format` prints a Skolem with a trailing comment `#|"a Car"|#` when `*add-comments-to-names*` is true.

A source annotation `(@ frame class slot ...)` may sit as the last element of an expression. It records the frame the expression was inherited from. `explain.lisp` reads it. It is not a value of the slot.

## Names

| Pattern | Meaning |
| --- | --- |
| `Car`, `parts` | A class, slot, or named instance. Case is significant. |
| `_Car23` | A Skolem instance of `Car`. The trailing digits are stripped by `skolem-root` to recover `_Car`. |
| `_ProtoCar4` | A prototype root or prototype participant. The marker is `*proto-marker-string*`, which is `_Proto`. |
| `_SomeCar2` | An instance created for a fluent in a situation. The marker is `_Some`. |
| `\|*Global\|` | The global situation, bound to `*global-situation*`. |
| `parts-of` | The inverse of `parts`. The suffix is `*inverse-suffix*`, which is `"-of"`. |
| `*Fluent`, `*Inertial-Fluent`, `*Non-Fluent` | The three fluent-status instances. |
| `It`, `It2` | The element bound by `forall` and by the nested `forall2` forms. |

`*var-marker-char*` is the character `_`. `*reserved-keywords*` in `interpreter.lisp` may not be used as class or slot names. `*additional-keywords*` may be used as slot names. That list includes `called`, `uniquely-called`, `Self`, `==`, `/==`, `>`, and `<`.

The gensym counter is `*km-gensym-counter*`. It is part of the saved knowledge-base state.

## Expressions

A KM expression is a list or an atom. Evaluation returns a list of values. These shapes are the ones the rest of the engine tests for:

| Shape | Test | Meaning |
| --- | --- | --- |
| `(_Car3)` or `Car` or `4` or `"wheel"` | `is-simple-km-term` when it is not a reserved word | A finished simple term. |
| `(a Class with (slot (values)))` | description | An existential description. Inside subsumption it does not create a Skolem. |
| `(:set a b)` | `km-setp` | A set. Duplicates are removed. Order is not significant. |
| `(:seq a b)`, `(:bag a b)` | `km-structured-list-valp` | A sequence or a bag. Duplicates and order are kept. |
| `(:pair a b)`, `(:triple f s v)` | `km-structured-list-valp` | A pair, or a triple used by `assert` and by explanations. |
| `(:args a b)`, `(:function ...)` | `km-structured-list-valp` | An argument list, or a function left for later application. |
| `(must-be-a Class)`, `(exactly 1 Class)`, `(at-least 1 Class)`, `(at-most 1 Class)` | `constraint-exprp` | A constraint. The interpreter does not evaluate it. `constraints.lisp` does. |
| `(quote ...)` and `(unquote ...)` | `quoted-expressionp` | A quoted KM expression, with `#,` already turned into `unquote`. |

`:set` is also how a caller asks for a set when a bare list would otherwise be read as a path. `(the slot of frame)` returns a list. `km-unique` requires that list to have one element.

Slot values on a frame are always a list. `(color red)` is a malformed slot-value pair. The required shape is `(color (red))`. `vals-in` reports an error when the second element is not a list.

## Frames

```
symbol property          value
_Car3  own-properties    ((color (*red)) (wheels (4)))
_Car3  binding           _SportsCar1          ; present only after unification
```

`slot-in` is the first element of a pair. `vals-in` is the second. `make-slotvals` builds a pair. `are-slotsvals` checks a list of pairs and reports a user error when the shape is wrong.

The property name for a facet depends on the situation:

- In `|*Global|`, the property is the facet symbol itself: `own-properties`, `member-properties`, `own-definition`, or `member-definition`.
- In situation `_Situation3`, the property is the interned concatenation of the two names, such as `own-properties_Situation3`. `curr-situation-facet` caches that symbol on the facet's own property list, keyed by the situation.

`own-properties` holds facts about the frame. `member-properties` holds facts that instances of a class inherit. The two `definition` facets hold definitions used by `has-definition` and by classification, as opposed to ordinary inherited rules.

`target-situation` decides where a read or write actually goes. The global situation is used for the global situation itself, for a universal slot, for any slot of a prototype instance, and for a non-fluent slot when the current situation is not a theory. `instance-of` of `Slot`, `Partition`, `Theory`, and `Situation` is also stored globally.

## Inverses, cardinality, and fluent status

Asserting `(parts (_Engine1))` on `_Car3` also asserts `(parts-of (_Car3))` on `_Engine1`, unless the slot is in `*non-inverse-recording-slot*` or the concept is in `*non-inverse-recording-concept*`. `inverse2` and `inverse3` cover relations that are not binary.

`*valid-cardinalities*` is `1-to-N`, `1-to-1`, `N-to-1`, and `N-to-N`. The default is `N-to-N`. `single-valued-slotp` is true for `1-to-1` and `N-to-1`.

`*default-fluent-status*` starts as `*Fluent`. An inertial fluent projects its previous-situation value forward. A non-fluent is stored in the global situation. `*instance-of-is-fluent*` defaults to nil, so `instance-of` is a non-fluent unless that flag is set.

## Situations, theories, and prototypes

`*curr-situation*` is the situation queries read and write. `in-situation` evaluates one expression there and restores the previous situation. `new-situation` creates a situation whose `prev-situation` is the current one. Actions use `add-list`, `del-list`, `pcs-list`, and `ncs-list` on the situation to describe additions, deletions, and preconditions.

A theory is a situation opened with `in-theory`. `*visible-theories*` is the set of theories currently visible. Prototype mode is `*curr-prototype*` being non-nil. The prompt shows `[prototype-mode]`, `[situation]`, or `{theory}` to match. Prototype mode and a local situation together are an error. Prototype mode and a theory together are an error.

## Unification and bindings

`&` merges two values and must succeed. `&&` merges two sets and requires the classes on one side to subsume the classes on the other. `==` and `===` are the eager forms of those two. `&!` and `&&!` are eager and must succeed. `&?` tests `&` with no side effects. `&+` is `&` with the class-subsumption test, and it is allowed to fail. `&+?` tests `&+`. `&+!` tests with `&+?` and then performs `&!`.

A merged instance keeps one symbol. The other symbol's `binding` property points at the survivor. `dereference` follows the chain. `*dereferencing-on*` can be turned off during cloning, where following bindings would be wrong. `*allow-ununify*` defaults to nil. When it is true, `ununify-data` on the survivor remembers the pre-merge slot values.

Lazy unification may leave `(_A & _B)` or a `&&` residue on a slot. The residue is finished when the slot is next read, unless the caller passed `:eagerlyp t`.

## Constraints

Value constraints are `must-be-a`, `mustnt-be-a`, `<>`, `possible-values`, and `excluded-values`. Set constraints are `at-least`, `at-most`, `exactly`, `set-constraint`, `sometimes`, and `set-filter`. The full list is `*constraint-keywords*`. The slots that may themselves carry constraints are `==`, `/==`, `<`, `>`, `called`, and `uniquely-called`.

Consistency means the values could still be made to fit. Satisfaction means they fit now. `(at-least n Class)` and `(exactly n Class)` will mint missing instances up to `*max-padding-instances*`. That parameter is `0`, so minting is off.

## Explanations

Stored on the frame as a property:

```
(instance slot value explanation)
```

The property is `explanation` in the global situation and a situation-specific explanation property otherwise. Retrieval looks at both the frame and the value, so the inverse direction is found too.

`explanation` is one of:

- a KM expression, often carrying an `(@ ...)` source
- `(cloned-from prototype-root clone-root prototype-node)`
- `(added-at class comment-text)`
- `(projected-from situation)`

`*record-explanations*` and `*record-sources*` default to true. Turning them off saves memory. `*record-explanations-for-clones*` defaults to true.

## Goal stack

Each entry on `*goal-stack*` is five elements:

| Position | Accessor | Contents |
| --- | --- | --- |
| 1 | `stacked-canonical-expr` | The expression after canonicalization, used for loop detection. |
| 2 | `stacked-situation` | The situation the goal was asked in. |
| 3 | `stacked-expr` | The original expression. |
| 4 | `stacked-inference-number` | A counter for the trace. |
| 5 | `stacked-target` | `(the slot of frame)` when the result has a known destination, otherwise nil. |

`*obj-stack*` is the list of instances created or touched by the current top-level query. `*unstackable-kb-instances*` starts as `(t)`, so the Boolean `t` is not pushed.

## Failures

`*default-fail-mode*` is `fail`. A handler then returns nil when it cannot answer. `*top-level-fail-mode*` is also `fail`, and that is what `(km ...)` uses. `(fail-noisily)` sets the top-level mode to `error`, and a missing answer is reported. `(fail-quietly)` sets it back to `fail`. `*on-error*` is `debug`. A reported error may instead be `abort`, `abort-silently`, `continue`, `continue-silently`, `ignore`, or `break`. `continue` lets a failed unification proceed.

`*km-depth-limit*` is nil, meaning no depth limit. When a limit is set, exceeding it is handled like a detected loop.

## Behavior parameters

These are the user-tunable flags collected on `*km-behavior-parameters*`. The value shown is the value this source actually binds.

| Parameter | Bound value | Effect |
| --- | --- | --- |
| `*recursive-classification*` | t | Classification may classify the values it just inferred. |
| `*indirect-classification*` | t | Classification considers indirect evidence. |
| `*recursive-prototypes*` | nil | A prototype lookup does not itself trigger another prototype lookup. |
| `*eagerly-unify-prototypes*` | t | Prototype clones are unified immediately. |
| `*sanity-checks*` | nil | The `sanity-check` constraint wrapper is off. |
| `*slot-checking-enabled*` | nil | Slot declarations are not required. |
| `*logging*` | nil | The undo history log is off until `start-logging`. |
| `*max-padding-instances*` | 0 | `(exactly n Class)` does not mint missing instances. |
| `*tolerance*` | 0.0001 | Numbers within this distance compare equal. |
| `*output-precision*` | 3 | Decimal places used by `make-sentence`. |
| `*instance-of-is-fluent*` | nil | `instance-of` is stored as a non-fluent. |
| `*km-depth-limit*` | nil | Queries have no depth limit. |
| `*linear-paths*` | nil | Linear path notation is not recognized. |
| `*project-cached-values-only*` | nil | Projection may compute, not only reuse a cache. |
| `*record-explanations-for-clones*` | t | Cloned triples record `cloned-from`. |
| `*coerce-undeclared-slots*` | nil | An unknown slot is not automatically declared as a `Slot`. |
| `*record-explanations*` | t | Explanations are stored. |
| `*record-sources*` | t | Source annotations are kept. |
| `*add-comments-to-names*` | t | Printed Skolems include a `#\|"..."\|#` comment. |
| `*check-kb*` | nil | Extra knowledge-base checking is off. `checkkbon` turns it on. |
| `*classify-slotless-instances*` | t | An instance with no slots is still classified. |
| `*default-fluent-status*` | `*Fluent` | Slots are fluent unless declared otherwise. |
| `*called-forces-unification*` | t | `called` and `uniquely-called` can force two instances to merge. |
| `*use-inheritance*` | t | Class rules are used. Ignored inside prototype mode. |
| `*use-prototypes*` | t | Prototypes are cloned in during slot lookup. Ignored inside prototype mode. |
| `*classification-enabled*` | t | Classification runs. |
| `*prototype-classification-enabled*` | t | Prototype triggers run. |
| `*developer-mode*` | nil | Source info on frame structures stays hidden. |

`*km-state-parameters*` lists the variables a saved knowledge base must restore. It includes `*km-gensym-counter*`, `*visible-theories*`, `*curr-prototype*`, `*curr-situation*`, and the `*are-some-*` optimization flags. Those flags are nil until the engine sees a definition, a prototype, a subslot, a constraint, a tag, or a default, and later queries skip the corresponding machinery while the flag stays nil.

`*km-runtime-variables*` lists variables that change during a single query and are not part of the saved knowledge base: `*trace*`, `*depth*`, `*am-classifying*`, `*looping*`, `*show-comments*`, `*partially-included-prototype*`, `*deferred-unifications*`, `*instances-being-unified*`, and `*failed-unification-attempts*`.

## Trace and statistics

`*trace*` is the master trace switch. `*depth*` is the indentation depth. Finer switches in `trace.lisp` are `*trace-classify*`, `*trace-unify*`, `*trace-subsumes*`, `*trace-constraints*`, `*trace-other-situations*`, and `*interactive-trace*`. `*show-comments*` includes comment tags in the trace.

The statistic counters in `header.lisp` are `*statistics-classification-inferences*`, `*statistics-query-directed-inferences*`, `*statistics-kb-access*`, `*statistics-cpu-time*`, `*statistics-skolems*`, `*statistics-max-depth*`, `*statistics-unifications*`, `*statistics-classifications-attempted*`, and `*statistics-classifications-succeeded*`. A top-level `(km ...)` resets them when `*reset-statistics-enabled*` is true.

## Dispatch

Handlers live in `*km-handler-alist*`, the append of `*km-handler-alist1*` and `*km-handler-alist2*`. A pattern uses `?name` for one piece and `&rest` for the tail. `minimatch` returns the matched pieces in encounter order and does not bind a variable to a single object, so a repeated `?x` may match two different forms.

Arithmetic operators are left-associative. The alist rewrites `x + y + z` to `(x + y) + z` before the two-argument handler runs. The same rewrite gives `*` and `/` precedence over `+` and `-`, and gives `^` precedence over the other four. `/` of zero by zero is `1`. A non-zero numerator over zero is `*infinity*` (`999999`). Zero over a non-zero denominator is `0`.

`*compile-handlers*` is nil until `compiled-handlers.lisp` is loaded. That file sets it true and defines `compiled-km-handler-function`, which is the same alist written as nested equality tests. The generated file is not edited by hand. `compiler.lisp` regenerates it with `write-compiled-handlers`.

## Pattern variables in minimatch

| Token | Match |
| --- | --- |
| `?name` | One item. The name is not remembered. The item is returned. |
| `?any` | One item. The item is not returned. |
| `?*` | A run of items. They are not returned. The first successful match is kept. |
| `&rest` | The rest of the list. It is returned. |

A second matcher in `minimatch.lisp` returns a binding list for callers that need a variable to mean the same object every time it appears.
