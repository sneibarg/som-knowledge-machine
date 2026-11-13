# Step 14: English text and the taxonomy listing

`make-sentence` and `make-phrase` turn a Knowledge Machine expression into one string. `(taxonomy)` prints the subclass tree. `(justify)` can print one English sentence when `justify-leaves` is on.

## What you can do now

`(make-sentence (:seq "a" "cat"))` answers `("A cat.")`. `(make-phrase (:seq "a" "cat"))` answers `("a cat")`. `(make-sentence "hello")` answers `("Hello.")`. `(make-phrase "hello")` answers `("hello")`. `(make-sentence 3)` answers `("3.")`. `(make-sentence 1.5)` answers `("1.500.")`, because the output precision starts at 3. `(make-sentence (:seq "a" "cat" "." "the" "dog"))` answers `("A cat. The dog.")`. `(make-sentence (:seq "cat" "nospace" "'s"))` answers `("Cat's.")`.

`(make-phrase (andify (:set "a" "b")))` answers `("a and b")`. Three items answer `("a, b, and c")`. The comma is part of the joining word.

`(_Cat1 has (instance-of (Cat)))`, then `(make-phrase _Cat1)`, answers `("the cat")`. `(Fred has (name ("FRED")))`, then `(make-phrase Fred)`, answers `("FRED")`. `(make-sentence Fred)` answers `("FRED.")`.

A file that contains `(SETQ *VERBOSE-NUMBER-TO-TEXT* t)`, loaded with `(load-kb ...)`, makes `(make-sentence 3)` answer `("The value 3.")`. The same SETQ at the prompt stays an embedded-Lisp refusal. The message contains `setq is not evaluated`.

`(pluralize "cat")` stays `:ok`, answers nil, and records that pluralize is no longer defined in KM1.4. The error names the `"-s"` suffix. It is a recorded user error, and the command stays in the handler table.

`(taxonomy)` prints `Removing redundant superclasses...`, `Removing redundant subclasses...`, and `Computing subclasses of Thing...`, then a line `Thing`, then the subclasses. `(Moth has (superclasses (Thing)))`, then `(Yak has (superclasses (Thing)))`, prints Yak before Moth, because a new subclass is stored at the front of the list. `(Fred has (instance-of (Yak)))` prints Fred on a line that starts with `I` and five spaces. `_Cat9` and `_Hidden1` do not appear. `(the superclasses of Integer)` is still `(Number)` after a fresh `(taxonomy)`. Two `(taxonomy)` calls on one unchanged value print the same text.

`(color has (subslots (hue)))`, then `(taxonomy color subslots)`, prints `color` and then `hue` indented three spaces. That call leaves out the Removing lines. `(taxonomy Thing subclasses extra)` records that there are too many arguments and answers nil.

`(every Cat has (color (black)))`, an instance, a color read, then `(justify)`, still prints the subgoal line and the rule. With `justify-leaves` set on that value, `(justify)` prints `The color of the cat = black.`

On the HTTP service, `(make-phrase (:seq "a" "cat"))` is HTTP 200 and the value is `["a cat"]`. `(taxonomy)` is HTTP 200 and the text contains `Thing`. `(a Cat)` stays HTTP 501.

## Where this port differs from the Lisp

`pluralize` records the user error from KM 2.5.45 and names the `"-s"` suffix. There is no morphology table. The migration plan's one-line description of a morphology helper is the older behavior.

`(why)` still prints the KM rule. The because line and the RULE line are the step 11 text. `(make-phrase)` is used by `(make-sentence)`, `(make-phrase)`, `(andify)`, and by `(justify)` when `justify-leaves` is on. Comment storage stays refused, so the ENTRY TEXT and EXIT TEXT lines stay absent.

`(justify)` builds the English sentence when `justify-leaves` is true, `developer-mode` is false, and the slot is not `instance-of`. The sentence is `The <slot> of <phrase> = <phrase>.` The Lisp can add `(from Class, ...)`. That suffix needs `originated-from-classes`, which stays unported, so the sentence omits it. When `justify-leaves` is off, the subgoal line is still printed, including when `developer-mode` is off. The Lisp prints that line only in developer mode. An `instance-of` leaf keeps the subgoal line.

The taxonomy walk follows the relation's stored list. An unplaced frame follows the order frames were first stored. The Lisp sorts both with `string<`. The walk does not follow hash order. A later superclass of Thing appears earlier, because `add-val` inserts at the front.

`(taxonomy)` with `subclasses` runs the cleanup first. The three progress lines are always printed. A redundant superclass or subclass link is deleted. A link that is already minimal stays, including its order. The Lisp then checks partitions and can reattach an unplaced class. This cleanup leaves that check out and leaves the unplaced frames where they are. `(taxonomy color subslots)` does not clean. `(clean-taxonomy)` at the prompt stays an embedded-Lisp refusal. The cleanup runs from `(taxonomy)` when the relation is `subclasses`.

Thing is printed as the word `Thing`. A named instance is marked `I`. An unplaced named frame is marked `?`. Three spaces is one level. An instance of a direct subclass of Thing is indented with `I` and five spaces. `*ignore-items*` and `*prune-points*` stay empty, so the ignore branch does not run. The depth limit stays 9999. `htmlify` writes an empty name for a known frame, because `htextify` returns nothing. `(taxonomy)` does not pass `htmlify`.

A number uses signed comparisons. An integer stays an integer. A value of at least 1 uses fixed decimals, so 1.5 with precision 3 is `1.500`. A smaller positive value that is at least 10 to the minus precision trims trailing zeros. Any other number, including a negative below 1, uses scientific form. Java writes a two-digit exponent, so 0.0001 is `1.000e-04` and -0.5 is `-5.000e-01`. A nil precision skips that formatting. A SETQ of `*OUTPUT-PRECISION*` to a non-number records the refused-setq error and leaves the stored precision alone.

`*verbose-number-to-text*` starts false. `*output-precision*` starts at 3. `*default-km-behavior-for-expand-text*` starts true. `*justify-leaves*` and `*developer-mode*` start false. `load-kb` accepts a SETQ of each of those names. `save-kb` does not write them. `reset` restores the defaults. When the default expansion is off, a symbol that is not a frame, a triple, `:seq`, `:set`, or NIL becomes a string with its case kept. `developer-mode`'s nil name `??` stays unused while that flag is false.

A name lookup that returns the concept stops. The comparison is structural equality. Trace is still later, so the Lisp binding that suspends `*trace*` around a name does nothing here. Several names keep the first. The comment for that is not printed. An anonymous instance becomes `the` plus the lower-case name of its first immediate class. A symbol that starts with `*` drops the star and is lower case, so `*pete` becomes `pete`.

A sentence is still returned when a user error was recorded during the expansion. A not-ported expression inside the sentence is returned as that refusal. An expansion deeper than 100 records the infinite-recursion error. `(taxonomy)` checkpoints when logging is on. It is an ordinary command.

## Lisp files this step used

`anglify.lisp` supplies `make-sentence`, `make-phrase`, and the name expansion. `taxonomy.lisp` supplies the tree walk. `interpreter.lisp` supplies the handlers and the justify leaf. `strings.lisp` supplies `andify`. `header.lisp` supplies the output precision and the behavior flags.

## What is still absent

Trace, statistics, SADL, and the license text. `fastsave-kb`, `fastload-kb`, `faslsave-kb`, and `load-newest-kb`. Arbitrary `eval` and `setq` at the prompt. `do-script`, `do-plan`, and `in-every-situation`. `is-true`, `all-true`, and `some-true` as commands. `(a Cat)` outside prototype mode. `also-has` as a user command. `showme`, `(comment ...)`, `(show-comment ...)`, and `(the1 ...)`. `explain-all` and `clear-explanations`. The partition check, `originated-from-classes`, and the comment-tag justification walker. The step 10 and step 11 gaps stay.

## How to try it

`clojure -M:test` runs the suite, including English and taxonomy. At the `KM>` prompt, `(make-phrase (:seq "a" "cat"))` prints `("a cat")`. `(taxonomy)` prints the tree under Thing. `q` leaves. `POST /query` with `(make-phrase (:seq "a" "cat"))` returns that string. `(taxonomy)` on that service returns text that contains Thing. `(a Cat)` is still refused. `(pluralize "cat")` records the error and answers nil.
