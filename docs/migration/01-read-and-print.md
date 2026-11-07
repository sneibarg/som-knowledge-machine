# Step 1: Read and print

The prompt and the HTTP service can now read one Knowledge Machine expression and print it back. The expression is not evaluated. There is still no knowledge base.

`som.km.engine/evaluate` does the work. Both fronts call it. The build reports its evaluator as `read-print`.

## What you can do now

At the `KM>` prompt, a finished expression is printed in the form `km-format` would write. `(a Cat)` prints as `(a Cat)`. `(a cat)` prints as `(a cat)`. Case is part of the name.

A line that is only the start of an expression, such as `(every Car has`, waits for the rest. The prompt prints `>` and reads another line. `q` still leaves the prompt. The reader discards a comment first, so `q ; done` and `#|note|# q` leave as well. `Q` is a different symbol, and `(q)` is a list, so neither one leaves. A second expression on the same line is an error, so `q extra` does not leave.

`POST /query` returns status 200 and the same printed text in `:value`. Posting `q` returns that symbol and does not stop the service. A blank body is still status 400 with `:error "empty"`. A broken expression is status 400 with `:error "read"`. `:incomplete` is true when the text is only a prefix of an expression. A body that is not plain text is still status 415.

`:message` on a successful read is `Read the expression and did not evaluate it.`

## What a term looks like

The reader is written for this port. It keeps the case of every symbol. `t` and `f` are symbols. `T` is a different symbol. The empty list `()` is the empty value and prints as `nil`. The token `nil` is the symbol `nil`. Printing the empty list and then reading that text produces the symbol, which is the same split the Lisp reader has when case is preserved.

A dotted tail stays a dotted tail. `(baz . bar)` keeps `bar` in the final position. `(a . ())` is the proper list `(a)`. `(a . nil)` keeps the symbol `nil` as the tail. A dot whose tail is a list continues that list, so `(a b . (c))` is `(a b c)`. The splice form `(:set (a Car) . #,(a Car))` is the proper list `(:set (a Car) unquote (a Car))`. Written without the dot, `#,(a Car)` is one nested element.

`'Fred` reads as the list `(quote Fred)`. `#'dog` reads as `(function dog)`. `#,` reads as `(unquote ...)`. Those three names are lowercase, which is how a case-sensitive Lisp reads them. The printer writes the names. It does not write the short forms `'` and `#,`.

`#$(the Car)` reads one form with the same reader. `#t` looks up a name in a map the caller supplies. The lookup ignores case. The prompt and the HTTP service pass an empty map, so `#tcar-instance` is an error there until a caller supplies the binding. `#:Car` is read as the ordinary symbol `Car`. `#:1943` is the symbol `1943`, because the token after `#:` is a name.

Vertical bars store a name as written. `|the Dog|` prints as `|the Dog|`. `|*Global|` prints as `*Global`, and that symbol is the global situation's name. `|1943|` prints with bars, because a name that is all digits needs them. A name whose only special character is an internal bar prints with a backslash and without surrounding bars, so `|a\|b|` prints as `a\|b`.

A string keeps `\"` and `\\` as escapes. A newline inside quotes stays a newline. A ratio stays exact, so `1/2` is one half. `+3` prints as `3`. `1.` prints as `1.0`. `1e2` prints as `100.0`. An integer that fits in a long is a long. A larger integer prints without a trailing `N`. `#\A` prints as `A`, because `km-format` uses `~a`.

`(The BIG big "car" 2)` round-trips through the printer.

## Comments and sources

`#| ... |#` is a comment, and the comments nest. A semicolon comment runs to the end of the line. Both are discarded while reading. A display comment such as `#|"a Car"|#` is the same kind of comment, so the reader drops it. The printer does not put display comments back. That happens later, in `write-km-vals`, once a knowledge base can say what a name means.

The comment and source walks from `explain.lisp` are available for later steps. A user comment is a symbol whose name starts with `[` and ends with `]`. `[]` is a comment. `[` is not. A source is a list whose first element is `@`. `desource` removes sources and collapses a pair whose second element is only a source. `decomment` removes comment tags. By default it leaves a commented pair as a list. `convert-comments` rewrites a user comment to `(comm [tag] Self)`.

`desource-decomment` removes both, then collapses a one-element list when a comment or source was removed. `(:seq [1])` stays `(:seq)`. `(no-inheritance [1])` stays `(no-inheritance)`. `(*cat [1])` becomes `*cat`. `(instance-of (Thing [cat]))` becomes `(instance-of (Thing))`, and the inner list is left as a list. The comment in `explain.lisp` still shows `(cat [1] (dog [3] ([4] [45] man)))` becoming `(cat (dog (man)))`. The function that is defined delistifies `([4] [45] man)` to `man`, so the result is `(cat (dog man))`. The same comment writes `*Large` for an input of `*large`. The walk keeps the stored case, `*large`.

A walk that follows `mapcar` reports a dotted list as an error. The tail walk inside `desource-decomment` can keep a dotted tail.

## What the reader refuses

`#.` would evaluate Lisp while reading. The refusal names the form, so `#.foo` says it is refusing `foo`. `#=` and `##` label objects while reading, and they are refused. Reader conditionals `#+` and `#-`, the vector reader `#(`, and a numeric argument such as `#1` are refused.

Backquote and a bare comma are refused. Knowledge Machine unquotes with `#,`.

A symbol in a package other than `km` is an error. `km::Car` and `KM::Car` are the symbol `Car`. `#:km::Car` is an error, because an uninterned symbol does not name a package. A ratio with a zero denominator is an error. Numbers are read in base 10.

## Where this port differs from the Lisp

`#t` in the Lisp binds the current package and reads the next name with the standard readtable. Here `#t` looks the name up in the caller's map, and the comparison is uppercase. `#t|Foo|` therefore matches a binding stored as `foo`. A Lisp that preserved an escaped name would not fold that spelling.

The head symbols `quote`, `function`, and `unquote` are lowercase. A Lisp image that folds symbols to uppercase while loading `case.lisp` would intern `UNQUOTE` instead. This port is case-sensitive, and the lowercase names round-trip.

A keyword whose name needs bars is printed by the symbol rule before the colon is added, so a keyword named `1943` prints as `|1943|`.

The string helpers ported here are `explode`, `concat-list`, and `substitute-string`. The rest of `strings.lisp` waits. The Lisp workaround for `apply`'s argument limit is unnecessary on the JVM.

## Lisp files this step used

`case.lisp` supplies the reader macros and `add-quotes` / `km-format`. `strings.lisp` supplies the three helpers the printer calls. `explain.lisp` supplies the comment and source recognizers: `comment-tagp`, `user-commentp`, `sourcep`, `desource`, `decomment`, `convert-comments-to-internal-form`, and `desource+decomment`. The active definitions are the ones ported. Older definitions left in comments are not.

## What is still absent

Patterns, equality, and the frame store. Loading a knowledge base. Inheritance, unification, constraints, prototypes, and recorded explanations. An answer that comes from running the expression. Display comments on printed names. `write-km-vals`.
