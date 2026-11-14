# Step 23: The same explanation

Explanation records are stored newest first. A `:set` is collapsed before the store decides whether to keep it, and a record whose triple has vanished is dropped when two frames are bound. `(comment ...)` and `(show-comment ...)` store and show comment text. `(why)` prints the because line. `(justify)` names the class a triple came from when `justify-leaves` is on, and with both flags off it omits the developer subgoal line. `(explain-all)` and `(clear-explanations)` run. A situation-local explanation is written back into that situation. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(explanation (:triple Fred color red) ((added-at Cat "older")))`, then the same triple with `"newer"`, then the older text again, leaves two records. The newer record is first. `(why (:triple Fred color red))` prints `newer` before `older`.

`(explanation (:triple Fred color red) ((:set (a Cat))))` stores `(a Cat)`. `(:set (a Cat) (a Dog))` stays a `:set`. `(a Cat)` is not a term, so that call records `PROGRAM ERROR!` and `not-fully-evaluated` and stores nothing. `(:set red blue)` stays a `:set` of terms, stores nothing, and records no error. `(:set green)` collapses to the atom `green` and stores nothing. `(:set (the color of Fred))` collapses to the list `(the color of Fred)` and stores that list. `(:set (the color of Fred) (a Dog))` stays a `:set`, records the same program error, and stores nothing.

`(_Spec has (instance-of (Tabby)))` and `(Tabby has (superclasses (Cat)))`, then an `instance-of` Cat explanation on `_Gen`, then a color explanation on `_Gen`. Binding `_Gen` away onto `_Spec` copies the color explanation and drops the `instance-of` Cat explanation. `_Gen` is removed from Cat's `instances`. `_Gen` stays a frame. Its slot values are cleared, and the records that were already on `_Gen` stay there. A user slot that carries `remove-subsumers` is left in place. The drop runs in `*Global`.

`(comment [Pet] "owned by someone" "a pet is owned" (:triple Sue color blue))` stores that list. `(show-comment [Pet])` answers it. `(show-comment [None])` answers nil. `(comment Fred "a")` records that the tag should be a symbol in square brackets and answers nil. `(comment [x])` answers nil. `(write-kb)` writes the comments section in the order the tags were first stored: `[Pet]` before a later `[Dog]`. An internal `(comm ...)` tag is accepted by the command and is left out of the file.

`(explanation (:triple Fred color red) ((red (comm [Pet] Fred))))` then `(why (:triple Fred color red))` prints `ENTRY TEXT: ("a pet is owned")` and `EXIT TEXT: ("owned by someone")`, then the rule. Several sources on one explanation record the "More than one source path" sentence and the rule still uses the first source. A rule with no top-level source still prints `(|<location unknown>| ...)`.

`(justify (:triple Fred color red))` with both flags off answers `(t)` and does not print `subgoal`. `(get-justification ...)` answers nil on that path. Developer mode prints the subgoal line and the rule. With `justify-leaves` on, `(explanation (:triple Fred color red) ((added-at Cat "by hand")))` then `(justify ...)` prints `The color of fred = red. (from Cat)`. An ordinary `(every Cat has (color (black)))` rule has no top-level source after it is turned into a rule, so that English sentence has no `(from ...)` suffix. A comment tag is walked before the leaf: the call text comes before the exit text, and `(comm [subslot-reasoning] ...)` prints `is a subslot of`. A chain of comment subgoals stops with `(depth limit for justification reached...no further details below this)`.

`(explain-all)` after an inherited color prints `(every Cat has (color (black)))` and does not print `RULE:`. `(explain-all :include-globalp nil)` leaves that global rule out. `(clear-explanations)` leaves the global record and drops a situation-local one. `(clear-explanations :clear-globalp t)` drops the global record too. A theory-local explanation is left out of `(explain-all)`. `(clear-explanations)` clears a theory.

`(new-situation)` then `(explanation (:triple Fred color red) ((added-at Cat "local")))` then `(save-kb ...)` writes that record inside `(in-situation _Situation1 ...)`. Loading the file puts the record back on Fred in that situation. Fred's global explanations stay empty. A theory wraps the same way with `(in-theory ...)`.

On the HTTP service, `(comment [Pet] "a pet" "owned")` is HTTP 200, the value is `["a pet", "owned"]`, and the statistics line contains `inferences`.

## Where this port differs from the Lisp

Records are newest first. A duplicate under `equal` stays where it is. A clone copies a translated explanation onto the end, so a list that is already newest first stays in that order. A fresh explanation is placed first.

`modify-set-explanation` desources each element of a `:set`, appends the distinct sources, and turns one remaining value into that value. A longer result stays a `:set`. The store then refuses a remaining `:set`, and it refuses an atom. A list that is still a cons is stored. The program-error check runs after that collapse, and only when the result is still a `:set` and some element is not a term.

A vanished triple is dropped only for the built-in `remove-subsumers` slots (`instance-of`, `classes`, `superclasses`, `member-type`) and the built-in `remove-subsumees` slots (`subclasses`, `prototype-of`, `domain`, `range`). The class test is the installed subclass walk. When the record is dropped, the recessive frame is removed from the inverse slot with inverse installation left off. The recessive frame itself stays. The Lisp deletes that frame.

`originated-from-classes` reads `prototype-of` on a `cloned-from` root. A prototype triple is not passed through `in-prototype`. `added-at` contributes its class. `projected-from` contributes none. Any other expression contributes the class named by each source.

`(why)` prints the triple, then the entry texts and the exit texts of the top-level comment tags, then the rule. `(justify)` walks those tags, then a leaf. With both flags off the leaf is empty. Developer mode prints the subgoal. `justify-leaves` prints one English sentence and the from-classes suffix when a class was found. The depth sentence is printed on the text. `(get-justification)` returns the collected lines, so that depth sentence is not in its value.

`(explain-all)` walks situations and skips theories. `(clear-explanations)` clears theories as well as situations. Prototypes are cleared with every other frame. A situation-local explanation is saved inside `(in-situation ...)` or `(in-theory ...)`, which is what puts it back on load. The Lisp save writes the global facet and has no wrapper.

Comment tags are written in the order they were first stored.

## Lisp files this step used

`explain.lisp` supplies `modify-set-explanation`, the comment and show-comment commands, `originated-from-classes`, `(why)`, `(justify)`, `(explain-all)`, and `(clear-explanations)`. `frame-io.lisp` supplies the explanation property, the newest-first store, and the merge inside `km-bind`. `interpreter.lisp` supplies the handlers and the comment-tag walker. `prototypes.lisp` supplies `in-prototype`, which this step does not call, and the clone's copy of an explanation. The writer supplies the situation wrapper and the comments section.

## What is still absent

A cached explanation stays unported, and `(explained-by ...)` stays refused. `(why)` reads the explanation database. A rule with no top-level source still prints `(|<location unknown>| ...)`. Sorting comment tags, the taxonomy, and each save group with `string<` waits for the file step, as do `a-prototoype`, the partition reattach, the load counter reset, and `:on-error` for a not-ported form inside a load. `(sanity-check ...)` answers `(t)` and leaves its body unread. `(anonymous-instancep ...)`, `(has-value ...)`, and `(function ...)` stay refused. `showme` and `showme-all` stay refused. `do-script` and `in-every-situation` stay refused. The same file is the next wrap-up step.

## How to try it

`clojure -M:test` runs the suite, including these explanations. At the `KM>` prompt, `(explanation (:triple Fred color red) ((:set (a Cat))))` then `(why (:triple Fred color red))` prints the collapsed `(a Cat)` rule. `(comment [Pet] "a pet" "owned")` then `(show-comment [Pet])` answers `("a pet" "owned")`. `q` leaves. `POST /query` with `(comment [Pet] "a pet" "owned")` returns HTTP 200 and the value `["a pet", "owned"]`.
