# Step 24: The same file

An empty prototype is stored and written as `(a-prototoype Class)`, and that form runs. `(taxonomy)` prints each level in symbol-name order and checks partitions. A save sorts each group, and the comments section, with the case-insensitive order. `load-kb` resets the inference engine once at the start. A form that is not ported yet follows `:on-error`. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(a-prototype Cat)` and `(a-prototoype Cat)` each answer a `_Proto` name. The stored definition, and the prototype comment in `(write-kb)`, use `(a-prototoype Cat)`. `(a-prototype Dog with (fur (brown)))` stays `(a-prototype Dog with ...)`.

`(Moth has (superclasses (Thing)))` then `(Yak has (superclasses (Thing)))` then `(taxonomy)` prints `Moth` before `Yak`. `(Zebra has (color (striped)))` then `(Ant has (color (black)))` prints `?  Ant` before `?  Zebra`. `(Fish has (subclasses (Goldfish)))` prints `Fish` as a child of Thing. Fish has no stored superclass, and Thing's stored subclasses do not gain Fish. Goldfish's stored superclass is Fish.

`(Animal has (superclasses (Thing)))`, Cat and Dog under Animal, Mutt under Cat and Dog, then `(a Partition with (members (Cat Dog)))`, then `(taxonomy)`, records one warning. The warning names Mutt and the partition, and the members line reaches column 25 before `(Cat Dog)`. Cat alone is one membership, so Cat is not a violation.

`(Zebra has (color (striped)))` then `(Apple has (color (red)))` then `(write-kb)` writes `(Apple has` before `(Zebra has`. `(comment [Pet] "a pet" "owned")` then `(comment [Dog] "d")` writes `[Dog]` before `[Pet]`. `(show-comment [Pet])` still answers `("a pet" "owned")`. Two saves of one value match, and the file omits `(now)`.

`(1 + 2)` then `(load-kb ... :print-statistics t)` of a file that holds `(1 + 2)` reports `(2 inferences`. The load command runs before a goal is pushed, so the report is the file. With reset statistics already off, that same file leaves the count at 4 and turns inverses on. A save that had inverses off still reloads with them off, because the file writes `(disable-installing-inverses)` after the enable line.

A file `(retain-expr (1 + 2))` then `(Fred has (color (red)))` loads as `(t)` under the default `:on-error`. Fred's color is red. The errors include the not-ported sentence, and the text does not say aborted. The same file with `:on-error` `:abort` answers nil, says aborted, and does not create Fred. Either result is ok and includes statistics.

On the HTTP service, `(a-prototoype Cat)` is HTTP 200, the symbol name starts with `_Proto`, and the statistics line contains `inferences`.

## Where this port differs from the Lisp

The review asked for `string<` on the taxonomy and on each save group. The live predicates differ. `(taxonomy)` sorts each printed level with `string<` on the symbol name, which is case-sensitive. Each save group and the comments section sort with `string-lessp`, which is case-insensitive. A tie keeps the earlier name. The stored slot order, `(the1 ...)`, and `(show-comment ...)` stay in the order the values were stored.

`(taxonomy)` cleanup removes a redundant superclass or subclass link and then runs the partition check. The check walks the classes under Thing, collects `member-of` over each class and the classes above it, and records a `user-warning` when one partition appears more than once. `update-subclasses-of-thing` is not called, so an unplaced class is not stored as a subclass of Thing. The `?` mark is a named frame the walk did not reach. An unplaced class is already walked as a child of Thing, so it is printed without `?`.

`load-kb` calls the same reset the Lisp uses, after the loading line and before the file is opened. A missing file still resets. Inverses are turned on, the goal stack and the trace are cleared, and the counters are zeroed only when reset statistics is enabled. Expressions inside the file keep the counters running. A not-ported form records its sentence on `:errors` and drops the not-ported flag. `:continue`, `:continue-silently`, `:ignore`, `:debug`, and `:break` keep reading the file. `:abort` and `:abort-silently` stop and answer nil.

## Lisp files this step used

`interpreter.lisp` stores `a-prototoype` when a prototype has no slot pairs. `taxonomy.lisp` sorts the printed tree with `string<`. `loadkb.lisp` sorts each save group and the comment tags with `string-lessp`, and `reset-inference-engine` runs at the start of `load-kb`. `frame-io.lisp` supplies `clean-taxonomy` and the partition warning. `lazy-unify.lisp` supplies `disjoint-classes`. `update-subclasses-of-thing` is defined and is not called.

## What is still absent

A cached explanation stays unported, and `(explained-by ...)` stays refused. `(why)` reads the explanation database. A rule with no top-level source still prints `(|<location unknown>| ...)`. `(sanity-check ...)` answers `(t)` and leaves its body unread. `(anonymous-instancep ...)`, `(has-value ...)`, and `(function ...)` stay refused. `showme` and `showme-all` stay refused. `do-script` and `in-every-situation` stay refused. The remaining commands are the next wrap-up step.

## How to try it

`clojure -M:test` runs the suite, including these file forms. At the `KM>` prompt, `(a-prototoype Cat)` answers a `_Proto` name. `(write-kb)` includes `(a-prototoype Cat)`. `q` leaves. `POST /query` with `(a-prototoype Cat)` returns HTTP 200 and a symbol whose name starts with `_Proto`.
