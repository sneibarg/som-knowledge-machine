# Step 2: Patterns, lists, and equality

The port can now compare Knowledge Machine values, walk lists, and match a pattern. These are library functions. The prompt and the HTTP service still only read an expression and print it. `som.km.engine/evaluate` does not call the new functions. The build still reports its evaluator as `read-print`.

## What you can do now

`som.km.minimatch/minimatch` matches one value against a pattern and returns the captured pieces, in the order the variables were met. The variable names are ignored, so `(a ?x ?x)` against `(a b c)` returns `(b c)`. `?any`, `?ANY`, and `?*` match and return nothing. A pattern that captures nothing returns the symbol `t`. A failure returns nil, the empty list.

`?*` can consume several elements of a list. The first way that succeeds is the one that is kept. `(1 2 3 4 5 6 7 8)` against `(?* 3 ?x ?* 6 ?y ?z ?*)` returns `(4 7 8)`.

`&rest`, and `&rest1` through `&rest5`, capture the rest of the list as one piece. The names are lowercase. `&REST` is an ordinary symbol.

`full-match` is the other matcher. It returns a list of pairs, `(var . value)`. A success that bound nothing returns `((t . t))`, which is a real list, so a caller can tell success from failure. `?any` adds no pair. `&rest` binds the tail. `?*` is an anonymous variable here. It does not swallow several elements. `val-of` reads the value of a variable. The header in `minimatch.lisp` says a repeated variable must match the same object. The function that is defined, `add-binding`, records both pairs. `(a b)` against `(?x ?x)` returns `((?x . a) (?x . b))`, and `val-of` of `?x` is `a`, the earlier one. Later subsumption checks a repeated variable itself before it calls `add-binding`.

`string-match` matches a string against pieces of text and variables. It ignores case unless asked to be case-sensitive. Lower case follows the Java rule for one character, so the match does not depend on the locale. `(or "x" "a")` tries each alternative. A variable uses the first place its following text occurs, and a later copy of that text is left unused when the rest of the pattern fails. A bad pattern returns nil. The Lisp prints an error line. This port returns nil and prints nothing.

`find-handler` walks a table of patterns and functions, using `minimatch`. It returns a map with `:handler`, `:bindings`, and `:pattern`. When the pattern captures nothing, `:bindings` is nil. `:fail-mode :fail` returns nil when nothing matches. `:fail-mode :error` throws. The Lisp prints the error and returns nil. `apply-handler` calls the function with the captured pieces.

## Equality

`km-equal?` is the comparison slot values use. The tolerance is `0.0001`, the binding in `header.lisp`. Two numbers match when the absolute difference is within that tolerance, or within that fraction of the larger absolute value, whichever bound is smaller. `0.00001` and `0.00002` differ. `4.99999` and `5.0` match. `499999` and `500000` differ. `1` and `1.0` match here. They do not match under Lisp `equal` or `eql`.

The empty list and the symbol `nil` match. A symbol matches only the symbol of the same name, so `t` and `T` differ. Each read builds a fresh symbol object. `eql?` compares the name. `identical?` does not.

A list matches a list of the same shape, except an existential and a structured value. `(the age of Fred)` matches a copy. `(a Car)` does not, and `(some Cat)` does not. `(an Car)` is not an existential. The interpreter rewrites `an` before this test matters.

`:set` is not a structured value. Two sets match as sets: order does not matter, and a repeated element does not matter. A set that is written the same way twice, including `(:set (a Car) (a Dog))`, matches by structural equality before the set rule runs. The same set with the classes swapped does not match, because each `(a ...)` fails `km-equal?`. A bag keeps counts and ignores order. `(:bag a a)` does not match `(:bag a)`. A sequence, a pair, a triple, and `:args` match in order, so `(:seq 1)` matches `(:seq 1.0)` and `(:seq a b)` does not match `(:seq b a)`. `:function` is structured, and `km-equal?` has no clause for it, so two copies of `(:function foo)` do not match.

## Lists and which duplicate survives

`remove-duplicates` keeps the survivor in its original place. The default walks from the end and keeps the later copy. `(a b c b d d e)` becomes `(a c b d e)`. That is the rule `get-all-concepts` uses. The letters stay lowercase. `:from-end? true` keeps the earlier copy, so the same list becomes `(a b c d e)`. The default test is `eql?`. Pass `equal?` to compare structure.

`remove-dup-instances` uses `km-equal?` and keeps the earlier value. `5.0` followed by `4.99999` stays `5.0`. It does not dereference. There is no frame store yet, so there is no binding to follow. The Allegro shortcut that hashes a long list of symbols is not ported. The portable walk covers those lists too.

`val-to-vals` unwraps one `:set` and leaves a nested set nested. `flatten-sets` flattens nested sets. `vals-to-val` turns nil into nil, one value into that value, and a longer list into `(:set ...)`. A dotted tail stays dotted. A bare atom is an error.

`val-sets-to-expr` drops empty lists, drops a later list that is structurally the same, and keeps the earlier one. One remaining list becomes the value `vals-to-val` would produce. A single-valued slot joins with `&`. Anything else joins with `&&`. Appending the lists and then removing later `km-equal?` duplicates is available through `:combine-values-by-appending?`. The comment above the Lisp function says `((a b) (c))` with a single-valued slot becomes `(a & c)` after an error. The function that is defined joins the long list and continues, so the result is `((a & b) & c)`. The trace line and the user-error line are not printed.

## Where this port differs from the Lisp

`find-handler` returns a map. The Lisp returns a list of three values. `apply-handler` reads that map.

A cons cell is a Clojure record. A record answers `map?`, so any test that accepts a map checks for a cons cell first. The handler table does this. A list of `(pattern function)` pairs is the Lisp shape. A vector of pairs and a sequence of maps are accepted as well.

The multiple-value wrappers `mv-minimatch`, `mv-string-match`, and `mv-minimatch-pattern` are not separate functions. The caller uses the list the matcher returns.

`unquote` on a value that is not quoted returns the value. The Lisp also prints a warning. An `&` expression that is longer than three elements continues with the first and third elements. The Lisp prints that and continues. `val-sets-to-expr` does the same with its warnings.

`classp`, `slotp`, `simple-slotp`, `is-an-instance`, `orphanp`, `anonymous-instancep`, and `named-instancep` are not implemented. They ask the frame store. `anonymous-instancep` also dereferences.

## Lisp files this step used

`minimatch.lisp` supplies both matchers, the handler lookup, and `string-match`. `utils.lisp` supplies the list and binding helpers those tests need: `equal`, `eql`, `remove-duplicates`, `listify`, `append-lists`, `my-mapcan`, `member`, `remove`, `set-exclusive-or`, `quotep`, `unquote`, and the binding list. File I/O, permutations, and the rest of that file wait. `kbutils.lisp` supplies the shape tests, `km-equal`, `remove-dup-instances`, `val-to-vals`, `vals-to-val`, `val-sets-to-expr`, and the `&` / `&&` conversions. The reserved words are the list in `interpreter.lisp`, with the reader comments removed, so `sometimes`, `expand-text`, and `override` are not reserved. `It` and `It2` keep their capitals.

## What is still absent

The frame store. Loading a knowledge base. A query that runs. Inheritance, unification, constraints, prototypes, and recorded explanations. `get-all-concepts` itself. The store questions named above.

## How to try it

`clojure -M:test` runs the suite, including the examples from the Lisp headers. At the `KM>` prompt, `(a ?x ?x)` is still printed as text. It is not matched.
