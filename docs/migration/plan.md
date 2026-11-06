# Migration plan

This is the order in which the Knowledge Machine 2.5.45 sources are ported. The roles of the files are in `src/knowledge-machine/packages/Architecture.md`. The flags, frame layout, and reader macros are in `src/knowledge-machine/packages/Conventions.md`. The index of finished steps stays in [README.md](README.md).

The Lisp source is the specification. A step is written so that a Knowledge Machine expression it claims to support returns the same values the Lisp engine returns. Where the languages differ, this note says what the port does and which answers can change. Those differences are part of the step that introduces them, and the migration note for that step repeats the ones that step can hit.

`loadme.lisp` is a load order, not a build order. Lisp can call a function that is defined later in the image. The call graph below has cycles. Each cycle is broken by writing the data and the pure tests first, and by leaving a stub at the edge that calls back.

## Dependencies

A question still moves along the path in the architecture note: `km`, then `km-int`, then one handler, then `km-slotvals-from-kb`, then `get-vals` and `put-vals`, with unification beside that path. The files do not sit in layers underneath that path. Two clusters call each other.

The memory cluster:

| From | Calls | In |
| --- | --- | --- |
| `frame-io.lisp` | `known-frame`, `get-all-objects` | `loadkb.lisp` |
| `frame-io.lisp` | `push-to-obj-stack` | `stack.lisp` |
| `frame-io.lisp` | `minimatch` | `minimatch.lisp` |
| `frame-io.lisp` | `desource+decomment` | `explain.lisp` |
| `frame-io.lisp` | `valset-subsumes-valset`, which calls `is0` | `subsumes.lisp` |
| `frame-io.lisp` | `km-int` for classification, situation bodies, and slot expressions | `interpreter.lisp` |
| `loadkb.lisp` | `km-eval-print`, and `reset-kb` rebuilds the vocabulary declared in `frame-io.lisp` | `interpreter.lisp`, `frame-io.lisp` |

The reasoning cluster:

| From | Calls | In |
| --- | --- | --- |
| `interpreter.lisp` | the handler table, `minimatch`, the goal stack, and almost every other module | |
| `get-slotvals.lisp` | `unify-in-prototypes`, `lazy-unify`, `record-explanation-for`, `km-int` | `prototypes.lisp`, `lazy-unify.lisp`, `explain.lisp`, `interpreter.lisp` |
| `lazy-unify.lisp` | `km-bind`, `get-vals`, `km-int`, constraint tests | `frame-io.lisp`, `interpreter.lisp`, `constraints.lisp` |
| `constraints.lisp` | `km-int`, including `&?` | `interpreter.lisp`, `lazy-unify.lisp` |
| `subsumes.lisp` | `km-int`, `get-vals`, constraint tests, `record-explanation-for` | `interpreter.lisp`, `frame-io.lisp`, `constraints.lisp`, `explain.lisp` |
| `prototypes.lisp` | `get-vals`, `lazy-unify`, explanation records, `km-int` | `frame-io.lisp`, `lazy-unify.lisp`, `explain.lisp`, `interpreter.lisp` |
| `explain.lisp` | frame properties, and `anglify` when a reason is printed | `frame-io.lisp`, `anglify.lisp` |

`strings.lisp` and `utils.lisp` do not know about frames. `minimatch.lisp` does not know about frames. `case.lisp` knows about printing and the reader. Those four, plus the syntactic tests in `kbutils.lisp`, can be written before any knowledge base exists.

`kbutils.lisp` is split by that fact. `km-equal`, `km-null`, `val-to-vals`, `vals-to-val`, `val-sets-to-expr`, and `kb-objectp` look at the shape of a value. `classp`, `slotp`, and `is-an-instance` ask the store. The second group waits for the store.

`header.lisp` is not a step. Its readtable behavior is part of reading. Each flag is implemented in the step that first reads it, at the value bound in the source. Three comments in `*km-behavior-parameters*` disagree with the bindings that follow them. The bindings are the specification:

| Flag | Comment in the list | Binding that runs |
| --- | --- | --- |
| `*sanity-checks*` | default t | `nil` |
| `*tolerance*` | default 0.001 | `0.0001` |
| `*record-explanations-for-clones*` | default nil | `t` |

`compiler.lisp` and `compiled-handlers.lisp` are a second spelling of the handler table. They are not ported. `htextify.lisp` stays a function that returns nothing, which is what the stub does today.

## Lisp and Clojure

The differences below are the ones that change an answer, a printed form, or the knowledge base left behind after a query. A step that can hit one of them names it again in its own note.

### Truth, `nil`, and the Boolean instances

In Lisp the empty list and false are the same object, `nil`. A handler that found nothing returns `nil`. A `cond` or `if` test treats that return as failure. In Clojure `()` and `[]` are true. A straight translation of `(cond ((km-int expr) ...))` succeeds on an empty collection.

KM also has a symbol `nil`, written `#$nil` in the sources. `km-equal` treats Lisp `nil` and that symbol as the same empty value, in either position. Two symbols that are not `eq` are otherwise never equal. `kb-objectp` rejects the symbol `nil` and accepts the symbol `t`. The Boolean instances are the symbols `t` and `f`. `T` is not an instance. The comment in `kbutils.lisp` says later versions allow information on `t`.

The port keeps one emptiness test, the equivalent of `km-null`, and uses it wherever the Lisp uses a value list as a Boolean. Failure is Clojure `nil`. A successful answer is a sequence, and the sequence is success only when it is not empty. The symbol `nil` and the symbol `t` remain symbols. They are not Clojure `nil` and `true`.

`val-to-vals` maps both empties to `nil`, unwraps a `:set`, and wraps anything else in a one-element list. `vals-to-val` maps `nil` to `nil`, a singleton to its element, and a longer list to `(:set ...)`. Those two functions are the boundary between "one KM value" and "the list `km-int` returns".

### Equality and which duplicate survives

`km-equal` in `kbutils.lisp` is the equality that slot values use. The rules, in order, are:

1. `eq` succeeds.
2. Lisp `nil` equals the symbol `#$nil`, either way.
3. If either argument is a symbol and the two are not `eq`, they are not equal.
4. Two numbers are equal when the absolute difference is at most `min(0.0001, 0.0001 * max(|x|, |y|))`. One number and a non-number are not equal.
5. `equal` succeeds for the remaining atoms and proper lists, except an existential expression and a structured list (`:seq`, `:bag`, `:pair`, `:triple`, `:args`). Two separately written `(a Car)` expressions are not equal.
6. Sets compare as sets. Bags, sequences, pairs, triples, and `:args` compare by length and by `km-equal` on the elements in order.

Clojure `=` does not apply the tolerance, does not treat the symbol `nil` as empty, and treats `(a Car)` lists as equal to each other. Clojure `==` is numeric only. Using either one as `km-equal` changes which slot values collapse and which unification candidates match.

`remove-dup-instances` copies the list and then calls `delete-duplicates` with `:from-end t` and `:test #'km-equal`. The Common Lisp rule is that `:from-end t` discards the later duplicate and keeps the earlier one. The survivor stays in its original position. The Allegro branch, used only for a list of more than twenty symbols, walks forward and keeps the first symbol. For symbols that matches `km-equal`, because two distinct symbols are never equal. The portable rule and the Allegro shortcut therefore agree on symbol lists. The portable rule still matters for numbers inside the tolerance and for sets.

`val-sets-to-expr` uses `remove-duplicates` with `:from-end t` and `:test #'equal`, so the first structurally equal value-set survives.

`get-all-concepts` uses `remove-duplicates` with the default `:from-end nil`. That discards the earlier duplicate and keeps the later one. The spec's own example is `(a b c b d d e)` becoming `(A C B D E)`. Clojure `distinct` would produce `(a b c d e)`. A walk over concepts in that order can classify or display a different instance first.

Ordinary `add-val` appends. The comment on that clause says the append is there to preserve order. Slots in `*built-in-remove-subsumers-slots*` and `*built-in-remove-subsumees-slots*` insert the new value at the front. `(the1 ...)` and `(theNth ...)` read by position. A single `conj` on every slot reverses one of those two families and changes the answer.

Slot values stay a sequence of pairs in the order the Lisp list had. A hash map of slots changes iteration order once a frame has more than a handful of slots, and a set of values drops both order and the `km-equal` rule.

`member` in `add-val` uses `equal`, not `km-equal`. A later retrieval that runs `remove-dup-instances` can still collapse two numbers that were both stored. The port keeps that split.

### Numbers

Lisp integers grow. Clojure `+` and `*` throw once a long overflows. The arithmetic handlers use `+`, `-`, `*`, `/`, and `expt`. The port uses the arbitrary-precision operations, and an exact ratio where Lisp would produce a ratio. `(/ 1 2)` stays `1/2`. A double changes `km-equal` for large integers, because the tolerance test is then comparing a rounded magnitude.

The handlers rewrite an operator list before they evaluate it. `^` is tighter than `*` and `/`, and those are tighter than `+` and `-`. Several of the same operator associate to the left: `(2 - 3 - 4)` is `((2 - 3) - 4)`. A left-to-right walk that ignores the rewrite table evaluates `(2 + 3 * 4)` as 20. The Lisp rules evaluate the product first and return 14.

Division by zero is special-cased before `/` is called. `0 / 0` yields `1`. `0` divided by a non-zero number yields `0`. A non-zero number divided by `0` yields `*infinity*`, the integer `999999`. A legitimate value of `999999` is the same integer. Replacing it with an infinity double makes later arithmetic and `km-equal` diverge.

The zero test is a Lisp `cond` whose first clause has a test and no body. The test is `(and (zerop x) (zerop y) (list 1))`, and a clause with no body returns the value of the test, which is the list `(1)`. A Clojure `cond` needs an explicit result. Copying the test across without a result returns a Boolean and the answer becomes true instead of `(1)`.

### Reading and names

The reader is `case.lisp`. `#$` reads one form with the case preserved and interns symbols in the `km` package. `#t` reads the next name in the package that was current outside `#$`. `#,` reads the next form as `(unquote form)` and returns a list, so a splice uses a dotted tail. Vertical bars escape a symbol. `#| ... |#` is a comment, discarded on read. The printer later emits `#|"a Car"|#` as a display comment when `*add-comments-to-names*` is true. That display comment is not a stored value.

`clojure.core/read` and EDN are the wrong readers. `#` starts a different dispatch, `nil` and `true` and `false` are their Clojure selves, and the read-eval switch would evaluate forms while reading. A `.km` file is read by the KM reader only.

Clojure has no dotted list. The splice example in `case.lisp` depends on one:

```
'(:set (a Car) . #,(a Car))
```

reads as a form whose tail is the unquote, and the result has no extra pair of parentheses. A proper list around that unquote adds a pair. The reader represents an improper tail explicitly.

`#t` in Lisp names a variable in the surrounding Lisp image. The port has no such image. `#t` looks up a name in a map the caller supplies. The map is empty at the prompt and on HTTP. An unknown name is an error. A knowledge base that used `#t` to splice a Lisp variable does not load unchanged.

Skolem names come from `*km-gensym-counter*`, which starts at 0 and increases by one. `create-instance-name` interns the prefix, the class name, and the counter. The prefixes are `_`, `_Proto`, and `_Some`. Clojure `gensym` produces a different name, and any later unification or explanation that mentions the Skolem changes with it.

`[Tag]` is a symbol whose name starts with `[` and ends with `]`. It is stored as `(comm [Tag] Self)`. `Self` is rewritten when the expression is applied or when a prototype is cloned. `(@ frame class slot ...)` is a source annotation, not a slot value. Both of those shapes are recognized while reading, even though the functions that strip them live in `explain.lisp`.

### State, threads, and laziness

Frames are symbol property lists in Lisp. The port stores them in the knowledge base value the caller passes. One caller uses a given value at a time. The prompt holds one value. The HTTP service holds one value. A query runs to the end on the thread that started it. The result is a realized map. A lazy sequence that read or wrote the store would see whatever bindings and knowledge base existed on the thread that forced it.

`in-situation` saves the current situation, switches, evaluates the body, and switches back with `prog1`. `prog1` does not run its cleanup if the body throws. An abort therefore leaves `*curr-situation*` on the temporary situation. `unwind-protect` would restore it, and that would be a different knowledge base after the error. The port uses the `prog1` pattern: a normal return restores the situation, and a KM abort leaves it where the abort happened. The HTTP adapter treats a finished request as the boundary. It keeps the knowledge base the engine returned, including a situation an abort left behind, and it does not share that value with another request that is still running.

Keyword defaults such as `(situation (curr-situation))` run at the call, against the situation in force then. A default closed over when the function was defined would store into the wrong situation.

`mapc` returns its list. `doseq` returns `nil`. The return value of `mapc` is part of the result only where the Lisp uses it. `add-vals` discards it. The places that return it need the list back.

Several helpers mutate a cons that another variable still holds (`nconc`, `delete`, `delete-duplicates`, `setf` of a `car` or `cdr`). `remove-dup-instances` copies before it deletes, so that one is safe. A persistent update of a vector that the store alone holds matches the intended slot. A persistent update of a vector that two slots alias does not match a Lisp destructive change of their shared tail. Each step that translates a destructive list function says whether any other live pointer shared that tail.

### Control and recursion

`(km expr)` returns one value when nothing went wrong, and four values when it did: the answer, the error strings, the error structures, and the warnings. `km-int` returns the answer list only. The port always returns one map. The answer is `:value`. The other three Lisp values are `:errors`, `:error-structures`, and `:warnings`. An aborted query has `:ok` false and a message. The prompt prints the answer and then the errors. HTTP returns the map.

`*default-fail-mode*` and `*top-level-fail-mode*` are both `fail`. A handler that cannot answer returns `nil`. `(fail-noisily)` sets the top-level mode to `error`. `*on-error*` is `debug`. The legal modes are `abort`, `abort-silently`, `debug`, `continue`, `continue-silently`, `ignore`, and `break`. `continue` lets a failed unification proceed. `abort` throws to the `km-abort` catch at the top of `km`, which prints `(Execution aborted)` and returns `nil`.

`debug` and `break` enter the Lisp debugger and the interactive trace menu (`g`, `r`, `a`, `o`, `A`). The port has no debugger. Those two modes record the error, turn trace on for `debug`, and follow `abort` when the mode is `break` only in the sense that the query stops. They do not stop the process, and HTTP has no menu. A person cannot resume a query at a Lisp restart. That is a different session after an error, and the same answer when the mode is `continue`, `ignore`, or `abort` and the caller does not depend on the restart.

`*km-depth-limit*` is `nil`, meaning the Lisp does not stop for depth. The interpreter recurs through `km-int` and is not in tail position: it dereferences, removes duplicates, and traces around the recursive call. The JVM stack is finite. A recursive rule that Lisp answers can overflow the JVM. The port counts depth and, when it is near the stack limit, returns the same failure a set `*km-depth-limit*` would return. The default limit stays unset for queries that fit. The overflow case is the gap.

### Embedded Lisp

`*km-lisp-exprs*` is a set of names that work as KM commands and as Lisp functions, including `reset-kb`, `save-kb`, `load-kb`, `tracekm`, and `eval`. The interpreter `eval`s that call. `setq`, `km-setq`, and `fastload-kb` also `eval` Lisp. `fastsave-kb` writes `setq` forms for the property lists.

The port implements the knowledge-base commands as functions. `eval` of arbitrary Common Lisp, `setq` of an arbitrary variable, and a `fastsave` file are refused with an error that names the form. A `.km` file of KM expressions still loads. A file that contains a Lisp definition, a Lisp `setq`, or a `fastsave` image does not. `save-kb` text, which `writer.lisp` prints as KM syntax, is the form that round-trips.

### Printing, files, and walks

`km-format` prints a symbol without vertical bars, then puts the bars back when the name contains `() ,;:'"`, a space, or is all digits. Strings stay quoted. `*print-case*` is set so that the stored case is what appears. `pr-str` and `cl-format` escape a different set of names. The printer is tested against the examples in `case.lisp`.

Lisp opens a `.km` file in the implementation's default encoding. The port reads UTF-8. Bytes that are not UTF-8 are read as ISO-8859-1. A file whose encoding was a third character set can change a string or a comment.

`*kb-objects*` is an `eq` hash table. `get-all-objects` pushes every key while hashing, so the order is the hash order, reversed, and it already differs between Lisp implementations. The port records insertion order and walks that. `showme-all`, classification over every instance, and a save that follows this walk can choose a different instance first when several are equally eligible. Slot order inside one frame is still the list order from `add-val`, and `(the1 ...)` follows that, not the object-table order.

## Order of work

Step 0 is done. The engine accepts text and does not evaluate it. Later steps extend `som.km.engine/evaluate`. The prompt and HTTP both reach the new behavior through that function.

A stub returns a refusal the tests can see, or a conservative value that the step's own note justifies. A stub is replaced in the step named here. It is not left as a silent success.

### 1. Read and print

Files: `case.lisp`, the string and character helpers it calls from `strings.lisp`, and the comment and source recognizers from `explain.lisp` (`comment-tagp`, `user-commentp`, `sourcep`, `desource`, `decomment`, `convert-comments-to-internal-form`).

The reader turns a string into a KM form. The printer turns a form back into the text `km-format` would produce. `evaluate` can return the printed form of a term it understood and still refuse to run it.

Clojure differences this step can hit: the reader is not `clojure.core/read`. `nil`, `t`, and `f` are symbols, and Lisp `nil` is a separate empty value. Dotted tails are preserved. `#t` sees only the caller-supplied map. Display comments `#|"..."|#` are printer output. Case is preserved. The symbol `|*Global|` is the global situation's name.

### 2. Patterns, lists, and equality

Files: `minimatch.lisp`, `utils.lisp`, and the syntactic half of `kbutils.lisp`.

`minimatch` returns matched pieces in the order the variables were encountered. Variable names are ignored, so two uses of `?x` do not have to match the same object. `?any` and `?*` match and return nothing. `&rest` returns the tail. `full-match` is the second matcher. It returns real bindings, and a repeated variable must match the same object. The handler table uses `minimatch`. Code that needs a variable to repeat uses `full-match`. One matcher in place of both changes which handler runs, or binds the wrong piece.

`utils.lisp` contributes the list and set helpers those tests need. Multiple values in that file become maps or a pair of sequences at the function that produces them.

This step includes `km-equal`, `remove-dup-instances`, `val-to-vals`, `vals-to-val`, and `val-sets-to-expr`. Tests cover the tolerance, the symbol `nil`, sets against sequences, `:from-end t` keeping the earlier survivor, and the default `remove-duplicates` keeping the later survivor for the concept-list case.

`classp` and the other store questions stay unimplemented until step 3 has a store, and they move there.

### 3. The frame store

File: the storage operations in `frame-io.lisp`.

The knowledge base value holds frames, the gensym counter, the current situation, and the situation and theory names. A frame has the four facets. A facet value is an ordered sequence of `(slot (value ...))`. In `|*Global|` the facet name is the property name. In another situation the name is the concatenation `curr-situation-facet` builds, cached on the facet. `put-vals`, `get-vals`, `add-val`, and `delete-val` operate on that value and return an updated knowledge base along with their Lisp return value.

`add-val` appends on an ordinary slot and inserts at the front on a subsumers or subsumees slot. `member` uses structural equality here. Inverses are installed for ground instances. `single-valued-slotp` is true for cardinality `1-to-1` or `N-to-1`. The default cardinality is `N-to-N`. Non-fluent data is stored in the global situation once fluent status exists. Until step 4, every slot is stored in the situation the caller names.

`binding` and `dereference` live here. `*dereferencing-on*` can be turned off for a call. `*allow-ununify*` stays `nil`.

Stubs at the edges:

| Edge | Stub until |
| --- | --- |
| `known-frame` | this step, as membership in the knowledge base value. `loadkb.lisp` later adds the hash-table log and undo. |
| `push-to-obj-stack` | recorded on the query, ignored by storage. Step 5 reads it. |
| `valset-subsumes-valset` | structural `equal` only. An existential value is kept. Step 8 replaces this. |
| `km-int` | not called. A stored expression is left as data. Steps 6 and 7 evaluate it. |
| `desource+decomment` | the functions from step 1. |

`target-situation` for prototypes and non-fluents is completed in steps 4, 10, and 12. The argument is already on the store calls, so later steps do not rearrange the map.

### 4. Built-in vocabulary and reset

Files: the vocabulary at the top of `frame-io.lisp`, `reset-kb` in `loadkb.lisp`, and the `(reset-kb)` call in `initkb.lisp`.

`reset-kb` clears frames, sets the gensym counter to 0, returns to `|*Global|`, and rebuilds `Thing`, `Slot`, `Class`, `Situation`, `Theory`, the collection classes, `Boolean`, `Cardinality`, `Fluent-Status`, and the slots that describe slots (`domain`, `range`, `cardinality`, `inverse`, `inverse2`, `inverse3`). The fluent statuses are `*Fluent`, `*Inertial-Fluent`, and `*Non-Fluent`. `*default-fluent-status*` is `*Fluent`. `t` and `f` are the Boolean instances.

The `*are-some-*` flags start `nil`. A later query skips prototypes, constraints, subslots, definitions, and defaults while the matching flag is still `nil`.

`initkb.lisp` also prints a banner and tells a Lisp user to enter the `km` package. The prompt already prints the version banner. This step does not add a second banner. It does make `(reset-kb)` work as a command once step 6 can dispatch a built-in command. Until then the engine function `reset` is what tests call.

### 5. The goal stack

File: `stack.lisp`.

A stack entry has five elements: the canonical expression, the situation, the original expression, the inference number, and the target. The target is `(the slot of frame)` or empty. Unification goals are stacked under the situation marker `|all situations|`. `looping-on` compares the canonical form after `dereference`, so `(the parts of _X)` and `(the parts of _Engine1)` are the same goal once `_X` is bound.

`&+!` is not canonicalized to the same form as `&`. The interpreter decomposes it into a test and then `&!`, and those two must remain visible as separate goals. Folding them together makes a legal query look like a loop.

`*goal-stack*` and `*obj-stack*` belong to the query, not to the saved knowledge base. `*unstackable-kb-instances*` starts as the list `(t)`, so the Boolean `t` is not pushed. The loop check is on before any recursive handler runs. A query that loops returns the Lisp failure for a loop instead of growing the JVM stack.

The known gap in `stack.lisp` stays. An `or` between a goal and its repeat is still treated as a loop. The file comments describe a revised check and do not implement it.

### 6. The interpreter, in groups

File: `interpreter.lisp`, together with the local-value path in `get-slotvals.lisp` and the store calls that path needs.

`km` and `km-int` share one dispatcher. The handler table is the append of `*km-handler-alist1*` and `*km-handler-alist2*`, in that order. The first `minimatch` win is the handler. Patterns are not reordered by specificity.

The table is ported in groups. Each group is callable from the prompt and from HTTP before the next group starts. A form in a later group returns the `not-ported` refusal.

1. Literals, `nil`, the symbol `#$nil`, quote, unquote, and the structure tags `:set`, `:seq`, `:bag`, `:pair`, `:triple`, `:args`, and `:function`.
2. Arithmetic, including the precedence rewrites, exact ratios, arbitrary-precision integers, and the three division-by-zero results.
3. `and`, `or`, `not`, `numberp`, and the comparisons that do not look at the store.
4. `assert`, `delete`, `has`, and `(the slot of frame)` for values stored on that frame. Inheritance, prototypes, projection, and supersituations are off in this group. The six-source function exists, and sources other than the local store return nothing.
5. The constraint patterns. They return `nil` and set `*are-some-constraints*`. They do not enforce anything. Step 7 enforces them.
6. Dispatch of the built-in commands that steps 4 and 5 implemented (`reset-kb`, and the stack inspectors). `eval`, `setq`, and the other embedded Lisp names return the refusal from the embedded-Lisp section.

`km-unique` demands one value and reports an error when it finds another number. Fail modes follow `*default-fail-mode*` and `*top-level-fail-mode*`.

This step changes the result map. `:value` is the answer list. `:errors`, `:error-structures`, and `:warnings` carry the extra Lisp return values. `docs/reference/Architecture.md` is updated in the same step.

### 7. Unification and constraints

Files: `lazy-unify.lisp` and `constraints.lisp`.

These two files are one step. Unification calls the constraint test, and the constraint interpreter calls back into unification and into `km-int`.

`&` and `&!` must succeed. `&+` may fail and leave the knowledge base unchanged. `&?` and `&+?` only test. `&+!` tests with `&+?` and then performs `&!`. `&&` and `&+` require one side's classes to subsume the other's. Plain `&` combines the classes. Class subsumption for that test uses the taxonomy built in step 4 and extended in step 9. Until step 9, two instances unify under `&` by combining classes, and `&&` succeeds only when the classes already on the instances pass the test available then. The step note records any `&&` case that waits for inheritance.

Lazy unification may leave `(_A & _B)` or `((_A _B) && (_C))` on a slot. The residue is finished when a later read of that slot reaches it. `*eagerly-unify-prototypes*` does not apply until step 10. Eager unification, when a caller asks for it, leaves no residue.

`try-lazy-unify` has no side effects. The implementation computes it against a copy of the knowledge base value and discards the copy. A bug that writes the live value changes answers that Lisp would leave untouched.

Constraints distinguish consistency from satisfaction. `test-constraints` is the shared predicate. `filter-using-constraints` drops projected values. `enforce-constraints` reports a violation. `*sanity-checks*` stays `nil`. `*remove-violating-instances*` stays `nil`. `*max-padding-instances*` stays `0`, so `at-least` and `exactly` do not invent filler instances.

`*on-error*` of `continue` is honored here. `abort` returns `nil` and keeps the knowledge base at the abort point.

### 8. Subsumption

File: `subsumes.lisp`.

`is0` answers whether an existing instance matches a description. It does not create a Skolem for an `(a Class)` inside the description, and it does not unify. `(the Class with ...)` asks this test before it creates an instance. The constraint check runs in satisfaction mode.

Replacing the step 3 stub matters. `valset-subsumes-valset` then drops a newly added value when an existing value already covers it, including through an existential. Turning that on changes which values `(the slot of frame)` returns for descriptions. The tests for step 3 are ground values, so they stay stable.

### 9. Inheritance and subslots

Files: the class walks in `frame-io.lisp` (`immediate-classes`, `all-superclasses`, `all-instances`, `all-subslots`) and sources 3, 5, and 6 of `get-slotvals.lisp`.

Source 5 is the local store from step 6. Source 3 is values on subslots. Source 6 is rules inherited from classes. `*use-inheritance*` is `t`. Inheritance is skipped while prototype mode is on. Prototype mode is still a flag that nothing sets until step 10, so this step runs with it off.

`*recursive-classification*` and `*indirect-classification*` are `t`. `*classify-slotless-instances*` is `t`. Classification reads `*obj-stack*` when it is active. `*active-obj-stack*` is `nil`, so the eager push inside `put-vals` stays off and the stack records the frames `known-frame` did not already know.

Inherited expressions keep their `(@ ...)` source. The explanation store is step 11. Until then the source is preserved on the expression and `(why)` is still a refusal.

### 10. Prototypes

File: `prototypes.lisp`, and source 1 of `get-slotvals.lisp`.

`(a-prototype ...)` creates a root named with `_Proto`, records `prototype-of` and `prototype-scope`, and adds the root to its own `prototype-participants`. Cloning copies the participant graph and skips `*unclonable-slots*` and `*slots-not-to-clone-for*`. `cloned-from` links are recorded. `*record-explanations-for-clones*` is `t`, so the links are written in the form step 11 will read. Writing them in step 10 means step 11 does not have to rediscover clones.

`*use-prototypes*` is `t`. `*are-some-prototypes*` stays `nil` until the first prototype exists, and `get-slotvals` skips this source while it is `nil`. `*eagerly-unify-prototypes*` is `t`. `*recursive-prototypes*` is `nil`, so a prototype lookup does not start another prototype lookup. `*add-cloned-from-links*` and `*propogate-explanations-to-clones*` are `t`.

`a-prototype` is an error inside a situation, a theory, or a prototype. Situation entry is step 12. The flag is enough to reject the nested case.

`*dereferencing-on*` is off during the part of cloning that must not follow bindings.

### 11. Explanations

File: the rest of `explain.lisp`.

The syntax from step 1 now has a store. In the global situation the property is `explanation`. In another situation it is the situation-specific explanation property. A record is `(instance slot value explanation)`. Retrieval looks in both directions so an inverse triple can answer `(why)`.

An explanation is a KM expression, `(cloned-from prototype-root clone-root prototype-node)`, `(added-at class comment)`, or `(projected-from situation)`. Projection records appear once step 12 projects. `(why)`, `(justify)`, and `(get-justification)` print through the explanation store. English rendering waits for step 14, so until then the printer from step 1 prints the KM form.

`explain.lisp` gathers explanation records and then removes duplicates. On a non-Allegro Lisp that call is `remove-duplicates` with `:from-end t` and `:test #'equal`, so the earlier record survives. The Allegro helper `remove-duplicates-from-end` keeps the earlier record as well: a long list is filtered by a hash walk that collects the first sighting, and a short list pushes new items and `nreverse`s them back. The name of the helper describes the scan. The survivor is the earlier explanation. The port keeps that earlier record, in its original position.

### 12. Situations, actions, and theories

Files: the situation transitions in `frame-io.lisp`, the situation and theory handlers in `interpreter.lisp`, and sources 2 and 4 of `get-slotvals.lisp`.

`in-situation`, `new-situation`, `global-situation`, `in-theory`, `see-theory`, `hide-theory`, and `end-theory` update the current situation on the knowledge base value. A body uses the `prog1` cleanup from the state section, so an abort leaves the temporary situation in force. `next-situation`, `prev-situation`, and the action lists `add-list`, `del-list`, `pcs-list`, and `ncs-list` support `do`, `do-and-next`, `try-do`, and `do-concurrently`.

Source 2 projects a fluent from the previous situation. A single-valued slot keeps a projected value only when `maybe-project-value` accepts it. Source 4 reads supersituations. `*default-fluent-status*` is `*Fluent`. Non-fluents, prototypes, and universal slots stay in `|*Global|`. `*instance-of-is-fluent*` is `nil`. `*project-cached-values-only*` is `nil`.

`*visible-theories*` is saved with the knowledge base. It is on `*km-state-parameters*`.

### 13. Load, save, and undo

Files: `loadkb.lisp` and `writer.lisp`.

`load-kb` reads KM expressions with the step 1 reader and evaluates them with the step 6 interpreter. `with-morphism` renames symbols during the load. `save-kb` and `write-kb` print frames through `writer.lisp`, including explanations unless asked not to. `write-frame` emits `(frame has (slot (values)))`, plus situation and theory assertions when those are requested. HTML output calls `htextify`, which returns nothing, and otherwise wraps names only when `*html-action*` is set. The stub stays.

`checkpoint`, `undo`, the history log, and the creations log are this step. `*logging*` is `nil` until `start-logging`. `keeping-kb` runs a body and restores the previous value afterward, which is a natural fit for a value that is passed in.

`fastsave-kb` and `fastload-kb` are the embedded-Lisp gap. They are refused. A knowledge base round-trips through `save-kb` text.

Object-table walks use insertion order. Two saves of one knowledge base produce the same text. That text can differ from a Lisp image whose `maphash` order differed. Slot order inside a frame follows the store, so `(the1 ...)` after a reload matches `(the1 ...)` before the save.

A file is read as UTF-8, and as ISO-8859-1 when the bytes are not UTF-8.

### 14. English and the taxonomy listing

Files: `anglify.lisp` and `taxonomy.lisp`.

`make-phrase` and `make-sentence` flatten a KM expression, or a `:set` or `:seq` of them, into one string. An instance is replaced by `(the name of instance)` until that lookup returns the instance itself. `*verbose-number-to-text*` chooses between a bare number and `the value N`. `make-sentence` capitalizes and terminates. `pluralize` is the morphology helper. `(why)` from step 11 uses these functions once they exist.

`(taxonomy)` prints the subclass tree under `Thing`, three spaces per level. A second argument selects another relation, so the same walk prints subslots. The walk follows `subclasses` or the named relation in list order. It does not follow hash order.

### 15. Trace, statistics, SADL, and the license

Files: `trace.lisp`, `stats.lisp`, `sadl.lisp`, `licence.lisp`.

Trace wraps the same calls. It is not a second interpreter. `*trace*` is the master switch. The finer switches are `*trace-classify*`, `*trace-unify*`, `*trace-subsumes*`, `*trace-constraints*`, `*trace-other-situations*`, and `*interactive-trace*`. Spy and profile restrict what is printed. The interactive menu is the gap already stated under control: the port records the trace and does not break into a debugger. `t2f-on` writes the trace to a file the caller names.

The counters declared in `header.lisp` are reset and printed here: classification inferences, query-directed inferences, knowledge-base accesses, Skolems created, unifications, maximum goal depth, and classifications attempted and succeeded. `*reset-statistics-enabled*` keeps them across a top-level query when set. `(km ...)` resets them unless asked not to.

`do-plan` reads `first-subevent`, evaluates `do-and-next`, and follows `next-event`. `next-event-test` selects among `:args` pairs. The walk returns the situation it finished in. It is a thin caller of steps 6 and 12.

`(license)` prints the Simplified BSD Licence and the contact addresses. The text is the same text as `LICENSE`.

## Files that are not a step

| File | Treatment |
| --- | --- |
| `compiler.lisp` | Not ported. It prints `compiled-handlers.lisp`. |
| `compiled-handlers.lisp` | Not ported. The handler table in `interpreter.lisp` is the implementation. `*compile-handlers*` stays off. |
| `htextify.lisp` | Remains a function of the same arguments that returns nothing. |
| `loadme.lisp` | Documentation of the Lisp load order. The running image is the Clojure namespaces. |
| `header.lisp` | Split across the steps that read each flag, as the dependency section says. |

## What each step records

The note for a finished step says what a person can do, which Lisp files it comes from, what is still absent, and how to try it. It repeats the Clojure differences from this plan that the step can actually hit. The index in `README.md` gains the step. `docs/reference/Architecture.md` is updated when the result map, the knowledge base value, or the adapter boundary changes. Tests cover the engine and both adapters, and `clojure -M:test` passes before the step is done.
