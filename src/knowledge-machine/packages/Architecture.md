# Architecture of the Knowledge Machine sources

These files are Knowledge Machine 2.5.45, the Lisp inference engine by Peter Clark and Bruce Porter. `loadme.lisp` names the load order. The engine is one Lisp package, `:km`. A question enters through `interpreter.lisp`, the interpreter matches it to a handler, and the handler reads and writes frames stored by `frame-io.lisp`.

```
KM> line
  km                         interpreter.lisp
  km-int                     interpreter.lisp, with the goal stack from stack.lisp
  handler                    *km-handler-alist*, optionally flattened by compiled-handlers.lisp
  km-slotvals-from-kb        get-slotvals.lisp
  get-vals / put-vals        frame-io.lisp
  lazy-unify                 lazy-unify.lisp, checked by constraints.lisp and subsumes.lisp
```

A handler returns a list of values. `(km ...)` is the external call and returns that list as its first value, plus an error string and an error structure when something fails. `(km-int ...)` is the internal recursive call. `(km-unique ...)` and `(km-unique-int ...)` demand exactly one value.

## The knowledge base

A frame is a Lisp symbol. Its slots live on that symbol's property list. `frame-io.lisp` is the only module that should read and write those properties. The four facets are:

| Facet | What it holds |
| --- | --- |
| `own-properties` | Facts about this frame as an instance. |
| `member-properties` | Facts inherited by instances of this class. |
| `own-definition` | A definition of this frame. |
| `member-definition` | A definition inherited by instances of this class. |

A facet's value is a list of slot-value pairs, `(slot (value ...))`. In the global situation the facet name is the property name. In another situation the property name is the facet name joined to the situation name, for example `own-properties_Situation3`. `curr-situation-facet` builds and caches that name.

Unification does not copy one frame onto another. It sets the `binding` property of the losing symbol to the winning symbol. Later reads follow that chain with `dereference`. The `ununify-data` property remembers enough to undo a binding when `*allow-ununify*` is set.

The current situation is `*curr-situation*`. It starts as `|*Global|`. A non-fluent slot is stored in the global situation even when the query is inside a local situation. Prototype graphs are stored globally. Theories are a second kind of situation: they hold assumptions that can be made visible with `see-theory`, rather than a new version of the whole knowledge base.

## Load order

`loadme.lisp` loads the files in this order. The body of that file is commented out, because the concatenated `km-2-5-45-packaged.lisp` already contains every file. The order still describes the intended build.

| Order | File | Role in the running system |
| --- | --- | --- |
| 1 | `header.lisp` | Package, readtable, version, and the flags every other file reads. |
| 2 | `htextify.lisp` | Empty stub so a reference to `htextify` still compiles. |
| 3 | `case.lisp` | Case-preserving reader, `#$`, `#t`, `#,`, and printing. |
| 4 | `interpreter.lisp` | The query language and the handler table. |
| 5 | `get-slotvals.lisp` | How `(the slot of frame)` is computed. |
| 6 | `frame-io.lisp` | Frame storage, built-in vocabulary, situations, inverses. |
| 7 | `trace.lisp` | Trace, spy, and profile output. |
| 8 | `lazy-unify.lisp` | Merging two instances or two sets of instances. |
| 9 | `constraints.lisp` | `must-be-a`, `exactly`, and the other slot constraints. |
| 10 | `explain.lisp` | Why a triple was believed. |
| 11 | `kbutils.lisp` | Tests for "is this a class, an instance, a slot, a constraint?" |
| 12 | `stack.lisp` | Goal stack, object stack, and `showme`. |
| 13 | `stats.lisp` | Counters for unifications, classifications, and depth. |
| 14 | `sadl.lisp` | Walks an event chain declared with `first-subevent` and `next-event`. |
| 15 | `anglify.lisp` | Turns a KM value into an English fragment. |
| 16 | `writer.lisp` | Prints a frame back out as KM syntax. |
| 17 | `taxonomy.lisp` | Prints the subclass tree. |
| 18 | `subsumes.lisp` | Asks whether an existing instance already satisfies a description. |
| 19 | `prototypes.lisp` | Prototype graphs and cloning. |
| 20 | `loadkb.lisp` | Load, save, reset, and undo of a knowledge base. |
| 21 | `minimatch.lisp` | The pattern matcher the handler table uses. |
| 22 | `utils.lisp` | List, set, and equality helpers. |
| 23 | `strings.lisp` | String and character helpers. |
| 24 | `compiler.lisp` | Turns the handler table into straight-line Lisp. |
| 25 | `compiled-handlers.lisp` | The generated result of that compiler. Optional at run time. |
| 26 | `licence.lisp` | Prints the license. |
| 27 | `initkb.lisp` | Calls `(reset-kb)` and prints the banner. Loaded last. |

## header.lisp

`header.lisp` creates the `:km` package, records it in `*km-package*`, and copies the Lisp readtable into `*km-readtable*` so later files can add reader macros without changing the host Lisp readtable on every implementation. It declares the handler-table variables that `interpreter.lisp` fills in, the version string `2.5.45`, and the naming markers `_`, `_Proto`, and `_Some`.

It also holds the flags the rest of the engine consults: whether inheritance and prototypes are on, whether explanations are recorded, how deep a query may go, and the numeric tolerance. Those flags are listed in [Conventions.md](Conventions.md). Three lists name which variables belong to lasting behavior, to saved knowledge-base state, and to the inside of a single query. `loadkb.lisp` uses those lists when it writes and restores a knowledge base.

## htextify.lisp

`htextify` is called when HTML frame output wants a hyperlink. In the stand-alone engine the function ignores its arguments and returns nothing. It exists so the call compiles.

## case.lisp

Every other KM file begins by selecting `*km-readtable*`. `case.lisp` installs the reader macros on that readtable and on a second, case-preserving readtable. `#$` reads the following form with case preserved and with symbols interned in the `km` package. `#t`, usable inside `#$`, reads the next token in the surrounding package, which is how a Lisp variable is spliced into a KM form. `#,` reads the next form as an `unquote`.

The same file prints KM values. `km-format` prints symbols without the vertical bars Lisp would normally add, and it can append a comment such as `#|"a Car"|#` to a Skolem name when `*add-comments-to-names*` is true. `*inverse-suffix*` is `"-of"`. A slot `parts` has the inverse slot `parts-of`.

## interpreter.lisp

This is the language. `(km)` with no argument starts the read-eval-print loop. The prompt is `KM>`, or a situation or prototype prefix when one of those modes is active. The symbol `q` leaves the loop. `(fail-quietly)` and `(fail-noisily)` set whether a missing answer is `nil` or an error. The default inside reasoning is `*default-fail-mode*`, which is `fail`.

`km-int` strips comments, pushes the goal, and refuses to re-enter a goal already on the stack. `km1` walks `*km-handler-alist*` and applies the first matching handler. When `compiled-handlers.lisp` has been loaded, `*compile-handlers*` is true and `km1` calls `compiled-km-handler-function` instead of walking the alist.

The alist is split into `*km-handler-alist1*` and `*km-handler-alist2*` and then appended. Each entry is a pattern and a function. The pattern is matched by `minimatch.lisp`. The function receives the fail mode, a target of the form `(the slot of frame)` when the caller knows where the result will be stored, and the matched pieces.

The patterns fall into these groups:

- Lookup and creation: `(the slot of frame)`, `(the class slot of frame)`, `(a class)`, `(a class with ...)`, `(every class)`, `(the class with ...)`, and the `the+` / `a+` find-or-create forms.
- Class rules: `(every class has ...)`, `also-has`, `now-has`, `has-definition`, `now-has-definition`. Instance rules: `(frame has ...)`, `also-has`, `also-hasnt`.
- Unification: `&`, `&&`, `==`, `===`, and the variants `&!`, `&&!`, `&?`, `&+`, `&+?`, `&+!`. The bodies call `lazy-unify.lisp`. `&` and `&!` must succeed. `&+` may fail and leave no change. `&?` and `&+?` only test.
- Constraints left unevaluated for `constraints.lisp`: `must-be-a`, `mustnt-be-a`, `possible-values`, `excluded-values`, `at-least`, `at-most`, `exactly`, `constraint`, `set-constraint`, `set-filter`, `sanity-check`.
- Prototypes: `a-prototype`, `end-prototype`, `clone`, `evaluate-paths`.
- Situations and actions: `new-situation`, `in-situation`, `end-situation`, `global-situation`, `in-every-situation`, `do`, `do-and-next`, `try-do`, `do-concurrently`, and the same forms with `-and-next`.
- Theories: `in-theory`, `see-theory`, `hide-theory`, `end-theory`, `visible-theories`.
- Quantification: `allof`, `oneof`, `theoneof`, `forall`, `forall-seq`, `forall-bag`, and the `2` variants that bind `It2` so a query can nest. `It` is the element under test.
- Structures: `:set`, `:seq`, `:bag`, `:pair`, `:triple`, `:args`, `:function`.
- Arithmetic, left-associative: `+`, `-`, `*`, `/`, `^`. Division by zero yields `*infinity*`, which is `999999`.
- Tests and logic: `and`, `or`, `not`, `numberp`, `isa`, `is`, `subsumes`, `covers`, `is-true`, `all-true`, `some-true`, `=`, `/==`.
- Explanation and display: `why`, `justify`, `get-justification`, `explanation`, `comment`, `showme`, `showme-all`, `make-sentence`, `make-phrase`, `taxonomy`.
- Bookkeeping: `assert`, `delete`, `evaluate`, `checkpoint`, `undo`, `spy`, `profile`, `ignore-result`.

`*reserved-keywords*` is the set of words that may not be used as class or slot names. `*additional-keywords*` is a smaller set that may be used as slot names, including `called`, `Self`, `==`, and `/==`. `*km-lisp-exprs*` is the set of commands that work both at the KM prompt and as Lisp functions, such as `save-kb`, `reset-kb`, and `tracekm`.

## get-slotvals.lisp

`(the slot of instance)` ends in `km-slotvals-from-kb`. The comment at the top of the file names the six sources, applied in this order:

1. Prototypes, by cloning a matching prototype onto the instance (`prototypes.lisp`).
2. Projection from the previous situation, for a fluent slot.
3. Values on subslots of this slot.
4. Values inherited from supersituations.
5. Values already stored on the instance.
6. Rules inherited from the instance's classes.

For a single-valued slot, a projected value is kept only when it is consistent with the values from the other sources. Inheritance and prototypes are skipped while KM is inside prototype mode, and each can be switched off with `*use-inheritance*` and `*use-prototypes*`. The file is long because each source is traced separately. The reasoning itself is the six-step sequence above.

## frame-io.lisp

This is the memory. `put-vals`, `get-vals`, `add-val`, `delete-val`, `put-slotsvals`, and `get-slotsvals` are the local operations. They affect the situation chosen by `target-situation`, which sends non-fluent data and prototype data to `|*Global|`.

The file also declares the built-in vocabulary: classes such as `Thing`, `Slot`, `Class`, `Situation`, `Theory`, `Sequence`, `Bag`, `Pair`, `Triple`, and `Fluent-Status`; the slots that describe slots (`domain`, `range`, `cardinality`, `inverse`, `inverse2`, `inverse3`); and the fluent-status instances `*Fluent`, `*Inertial-Fluent`, and `*Non-Fluent`. The default cardinality is `N-to-N`. A slot is single-valued when its cardinality is `1-to-1` or `N-to-1`.

Inverses are installed by `add-val` unless the slot or the concept is on the non-inverse lists. `instance-of` and `superclasses` are the taxonomy links. `immediate-classes`, `all-superclasses`, `all-instances`, and `all-subslots` walk those links.

`create-instance` mints a Skolem. Ordinary instances are named from the class, prototypes from `_Proto`, and situational fluent instances from `_Some`. The counter is `*km-gensym-counter*`.

Situation transitions live here too: `new-situation`, `next-situation`, `prev-situation`, and the action lists `add-list`, `del-list`, `pcs-list`, and `ncs-list` that `do` uses.

## trace.lisp

Tracing is a wrapper around the same calls, not a second interpreter. `*trace*` is the master switch. Separate switches cover classification, unification, subsumption, constraints, and situations other than the current one. `tracekm` and `untracekm` are the Lisp entry points. `t2f-on` sends the trace to a file. Spy points, also reachable as the KM command `spy`, suspend the trace except for selected expressions. The interactive trace can stop on a goal and offer redo and fail, which `interpreter.lisp` honors when it processes a handler result.

## lazy-unify.lisp

Unification merges two graphs that may reach the rest of the knowledge base, so KM does not eagerly walk them. `lazy-unify` binds two atomic instances. Residues of the form `(_A & _B)` or `((_A _B) && (_C))` can remain on a slot and are finished when a later query reads the slot, unless the caller asked for eager unification.

`try-lazy-unify` is the test used by `&?`. It has no side effects. `lazy-unify-exprs` handles `&` and `&+`. `lazy-unify-expr-sets` handles `&&`. For `&&` and `&+`, one side's classes must subsume the other's, so a cat and a dog do not merge. For plain `&`, the classes are combined.

A successful bind calls `km-bind` in `frame-io.lisp`, merges explanations, and deletes the losing frame's slot data while leaving the symbol in the object list so the binding can still be found. `*less-aggressive-constraint-checking*` and `*overriding-in-prototypes*` change how strict that merge is.

## constraints.lisp

Constraints are KM expressions stored on a slot and interpreted here rather than by the normal handlers. The handlers for `must-be-a`, `exactly`, and the rest return `nil` and only set `*are-some-constraints*`, so the constraint survives as data.

Two questions are distinct. Consistency asks whether a value could still be made to fit. Satisfaction asks whether it fits now. `filter-using-constraints` drops projected values that are inconsistent. `enforce-constraints` applies the constraints to the values `get-slotvals.lisp` collected, and a violation is an error. `test-constraints` is the shared predicate used by subsumption and by unification. `*sanity-checks*` gates the `sanity-check` wrapper. `*remove-violating-instances*` controls whether a violating value is deleted when error reporting is silent.

## explain.lisp

When `*record-explanations*` is true, a triple can carry reasons. They are stored on the frame's property list under `explanation` in the global situation and under a situation-specific explanation property otherwise. One stored record is `(instance slot value explanation)`. Retrieval gathers records in both directions, so a value can explain the inverse triple as well.

An explanation is one of: a KM expression that computed the value, `(cloned-from prototype-root clone-root prototype-node)`, `(added-at class comment)`, or `(projected-from situation)`. A comment tag written `[tag]` is stored as `(comm [tag] Self)` so that cloning a prototype rewrites `Self` to the clone. A source annotation `(@ frame class slot ...)` records where an inherited expression came from. `(why)` and `(justify)` print these records. `anglify.lisp` supplies the English.

## kbutils.lisp

The other modules ask this file what a piece of data is, instead of repeating the tests. `is-km-term` accepts an atom, a description, a quoted expression, a structured list, a set, a function, or a constraint. `fully-evaluatedp` is stricter: constraints and bare functions are not finished values. `classp`, `slotp`, `is-an-instance`, `anonymous-instancep`, and `protoinstancep` distinguish the kinds of symbol. `kb-objectp` is the test frame storage uses before it will touch a name. `km-null` treats both Lisp `nil` and the KM symbol `nil` as empty.

## stack.lisp

`*goal-stack*` is the loop detector. Each entry keeps the canonical expression, the situation, the original expression, an inference number, and the target. `looping-on` dereferences the expression before comparing, so a query that starts as `(the parts of _X)` and continues as `(the parts of _Engine1)` is recognized as the same goal after `_X` has been bound.

`*obj-stack*` records instances touched during the current top-level query. Classification and `showme` use it. `showme` prints the current values of a frame. `showme-all` and `evaluate-all` also force inherited rules to run. `*show-inference-numbers*` includes the stack's inference numbers in the trace.

## stats.lisp

The counters declared in `header.lisp` are reset and printed here. They count classification inferences, query-directed inferences, knowledge-base accesses, Skolems created, unifications, the maximum goal depth, and classifications attempted and succeeded. `*reset-statistics-enabled*` lets a caller keep the counters across a top-level query. `(km ...)` resets them unless asked not to.

## sadl.lisp

SADL execution is a thin walker over ordinary KM slots. `do-plan` reads `first-subevent` of an event, then repeatedly evaluates `do-and-next` and follows `next-event`. When several next events exist, `next-event-test` selects among `:args` pairs. The walk returns the situation it finished in. The handler for `do-plan` in the interpreter calls this file.

## anglify.lisp

`make-phrase` and `make-sentence` flatten a KM expression, or a `:set` or `:seq` of expressions, into one string. An instance is replaced by `(the name of instance)` until that lookup returns the instance itself. `*verbose-number-to-text*` chooses between `3` and `the value 3`. `make-sentence` capitalizes and terminates. `make-phrase` does not. The KM commands of the same names are handlers that call these functions. `pluralize` is the morphology helper used when a sentence names a class.

## writer.lisp

`write-frame` prints a frame in the syntax `load-kb` can read back: `(frame has (slot (values)))`, including situation-specific and theory-specific assertions when those situations are requested. `expr2string` and `objwrite` render one KM expression. `list-definitions` walks from `Thing` and prints class definitions. HTML output calls `htextify` and otherwise wraps names in links controlled by `*html-action*` and `*html-window*`.

## taxonomy.lisp

`(taxonomy)` prints the subclass tree under `Thing`, indented by three spaces per level. A second argument selects another relation to follow, so the same walk can print subslots. The file warns that the walk is expensive. The KM command `taxonomy` is a handler that calls this function.

## subsumes.lisp

Subsumption answers "does this existing instance already match this description?" without unifying and without creating a Skolem for an `(a class)` inside the description. That distinction matters: "a car owned by a person" can match many owners, while "a car owned by `_person23`" can match only that owner. `(the class with ...)` in the interpreter asks `subsumes.lisp` first and only creates a new instance when no existing instance qualifies. The test uses `constraints.lisp` in satisfaction mode. `*trace-subsumes*` turns on its trace.

## prototypes.lisp

A prototype is an instance graph that stands for a typical member of a class. `(a-prototype Car with ...)` creates a root named with the `_Proto` marker, records `prototype-of` and `prototype-scope`, and adds the root to its own `prototype-participants`. The graph may mention other prototype instances. Those participants are cloned together.

When `get-slotvals.lisp` looks up a slot and `*are-some-prototypes*` is set, `unify-in-prototypes` clones the matching prototype onto the instance being queried. Slots in `*unclonable-slots*`, including `prototype-of`, `prototype-participants`, and `prototype-scope`, are not copied. `cloned-from` links record which prototype node produced which clone, and `explain.lisp` can turn those links into explanations when `*record-explanations-for-clones*` is true. `*eagerly-unify-prototypes*` controls whether the clone is merged immediately.

## loadkb.lisp

This is how a knowledge base enters and leaves the process. `load-kb` reads a `.km` file of expressions and evaluates them. `with-morphism` renames symbols during the load. `save-kb` and `write-kb` write frames back out through `writer.lisp`, including explanations unless asked not to. `fastsave-kb` writes a Lisp form that `fastload-kb` can read without re-running the inference. `load-triples` reads a file of triples.

`reset-kb` clears frames, the gensym counter, and the situation, then rebuilds the built-in vocabulary. `initkb.lisp` calls it at startup. `store-kb` and `restore-kb` keep an in-memory snapshot.

Two logs support undo. The history log records KM commands between checkpoints and `undo` walks it backward. The creations log records frames minted since a checkpoint and `undo-creations` deletes them. `keeping-kb` runs a body and restores the knowledge base afterward. `*kb-objects*` is the hash table of frames KM currently considers to exist.

## minimatch.lisp

`minimatch` matches an s-expression against a pattern and returns the matched pieces in the order the variables were encountered. Variable names are ignored, so two uses of `?x` do not have to match the same object. `?any` matches one item and does not return it. `?*` matches a run of items and does not return them. `&rest` matches the tail and returns it. This is the matcher `km1` uses on handler patterns. A second, slower matcher in the same file returns real bindings when a caller needs a variable to repeat.

## utils.lisp

Shared list and set operations: flatten, member from the end, set union and difference, `neq`, and the small predicates the rest of the engine uses instead of repeating Lisp idioms. Nothing here knows about frames. `lazy-unify.lisp` and `interpreter.lisp` both depend on these helpers.

## strings.lisp

String, character, and file-name helpers: concatenation, stripping, reading a file of s-expressions, and the character tests used by the Skolem-name parser in `case.lisp`. Like `utils.lisp`, this file is independent of the knowledge base.

## compiler.lisp

Adam Farquhar's compiler walks `*km-handler-alist*` and writes a single function whose tests are nested `eql` checks instead of a linear pattern match. `write-compiled-handlers` emits `compiled-handlers.lisp`. The compiler understands the same pattern variables as `minimatch.lisp`, including `&rest`. Loading the generated file is optional. The interpreter behaves the same without it and is slower.

## compiled-handlers.lisp

Generated output. It sets `*compile-handlers*` to true and defines `compiled-km-handler-function`. The readable source of the same behavior is the handler alist in `interpreter.lisp`. This file should be regenerated rather than edited.

## licence.lisp

`(license)` prints the Simplified BSD Licence and the contact addresses for Peter Clark and Bruce Porter. The KM prompt command of that name calls this function.

## initkb.lisp

Loaded last. `(reset-kb)` builds the empty knowledge base and the built-in classes and slots. `(version)` prints the banner with `*km-version-str*` and `*year*`. The file then tells the user to enter the `km` package and call `(km)`.

## Where a change belongs

A new query form is a handler in `interpreter.lisp`. If it reads a slot, the reading rule belongs in `get-slotvals.lisp` and the storage rule belongs in `frame-io.lisp`. A new way for two instances to merge belongs in `lazy-unify.lisp`. A new restriction on a slot value belongs in `constraints.lisp`. A new reason recorded on a triple belongs in `explain.lisp`. A new prototype-cloning rule belongs in `prototypes.lisp`. Printing and English stay in `writer.lisp` and `anglify.lisp`. Flags that every module reads belong in `header.lisp`, and if a saved knowledge base must remember them they also belong on `*km-state-parameters*` or `*km-behavior-parameters*`.

## Porting order

`loadme.lisp` loads these files in an order that assumes the whole image exists. The running call graph has cycles: `frame-io.lisp` calls `loadkb.lisp`, `subsumes.lisp`, and `km-int`, and the interpreter calls back into the store, unification, constraints, prototypes, and explanations. The port order that breaks those cycles, and the Lisp behaviors Clojure will not reproduce on its own, are in `docs/migration/plan.md`. The short list is in `docs/migration/README.md`.
