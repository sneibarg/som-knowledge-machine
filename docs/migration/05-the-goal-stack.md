# Step 5: The goal stack

A query can record the goals it is working on, and it can see when a goal repeats. The goal stack and the object stack both live on the query. They are not part of the saved knowledge base. The prompt and the HTTP service still only read an expression and print it. `(show-goal-stack)` is printed as text. It becomes a command when the interpreter can dispatch one.

## What you can do now

`push-to-goal-stack` records five elements: the canonical expression, the situation, the expression that was pushed, the inference number, and the target. The target is `(the slot of frame)`, or empty. Comments and sources are removed before the goal is stored. The newest goal is at the front. `top-level-goal` is the canonical form of the oldest goal. `pop-from-goal-stack` returns the newest goal. An empty pop returns nil.

A two-element path `(_Car23 parts)` is stored as `(the parts of _Car23)`, unless the first element is a reserved keyword. `&&`, `&&!`, and `===` become `set-unified-with`, in the written order. `&`, `&?`, `&!`, `&+`, `&+?`, and `==` become `unified-with`. When both sides are symbols, the name that sorts later is moved second, so `(_Engine1 & _X)` and `(_X & _Engine1)` are one goal. `&+!` is left as written. The interpreter will split it into a test and then `&!`, and those two goals have to stay visible.

A unification is recorded under `|all situations|`. Any other goal uses the current situation. The inference number is one more than the classification counter plus the query counter on the query. Both counters start at 0, so the first goal is inference 1. This step does not increment the counters. `reset` does not clear them.

`looping-on?` removes comments and sources, then asks whether that goal is already stacked. The canonical forms are compared after bindings are followed, and the situations must match. `(the parts of _X)` and `(the parts of _Engine1)` are the same goal once `_X` is bound to `_Engine1`. Turning dereferencing off keeps them apart. A new `set-unified-with` repeats an old `unified-with` when the elements are the same values wrapped in lists, in either order. An old `set-unified-with` does not make a new `unified-with` a repeat. An `or` between a goal and its copy is still a loop.

Pushing `&`, `&!`, or `==` records both sides on `:instances-being-unified` when both are knowledge-base objects. The right-hand side is recorded first. A side that is not an object, and an operator such as `&+` or `&?`, records nothing. Popping that goal drops the two objects. `clear-goal-stack` drops the goals and leaves the instance list. `reset` does the same: both stacks come back empty, and the instance list stays.

`pending-equality?` is true when the two values are the sides of `&`, `&+`, `&+!`, `&!`, or `==` still on the stack, in either order. Bindings are followed. A `:set` goal is searched for an equality inside it. `&?` is a test, so it does not count.

`handle-looping` sets `:looping?` on the query and returns the value a repeated goal produces. `(the age of Fred)`, and the path `(Fred age)`, return the values already stored when every value is fully evaluated. A stored value that still has to be evaluated is left alone: `:value` is nil and `:message` says the remaining expression is not evaluated yet. If that remaining expression is itself a goal, the value is nil and there is no message. `&?` and `&+?` return `(t)`. Another value unification returns a list of the first knowledge-base object in the expression. `(Fred & Sue)` returns `(Fred)`. `&+!` is a value unification, and the expression is not opened, so `(Fred &+! Sue)` returns nil. `((a b) && (c 1))` returns `(a b)`, the first set whose elements are all objects. Any other goal returns nil. Nothing is printed. The depth-limit reason accepts the same answers. The check that a query has run too deep waits for the interpreter.

`show-goal-stack` returns the text the Lisp function prints. `:value` is nil. The oldest goal is first, indented one more space at each level. A situation is shown when any goal sits outside `*Global`, which includes a unification under `|all situations|`. A target is shown on the following line. `show-inference-numbers?` prints the recorded number in front of the arrow. `show-obj-stack` follows bindings, writes that stack back onto the query, and returns the text. `:value` is true. `show-context` is that same function. `new-context` clears the object stack and leaves the goal stack.

The object stack's unstackable list starts as `(t)`. `reset` keeps a list the caller replaced. Reading the object stack follows bindings and writes the followed names back. Duplicates stay. `delete-frame` removes the dereferenced name, so a stacked `_X` bound to `Fred` leaves with `Fred`.

## Where this port differs from the Lisp

The functions return a map with `:kb`, `:query`, and `:value`. An empty pop returns nil. `show-goal-stack` and `show-obj-stack` return the text under `:text` and print nothing. The Lisp prints it. A dotted list is an error.

The inference counters and `:looping?` live on the query. The unstackable list lives on the knowledge base. `reset` keeps all three, and it clears both stacks. The Lisp `reset-kb` clears both stacks and does not reset the counters, the looping flag, or `*unstackable-kb-instances*`.

`handle-looping` does not print the trace lines. When a stored value is not fully evaluated, the Lisp evaluates it and may write the result back. That call is the interpreter. This step returns nil and a `:message` instead, and it does not write the slot. `&+!` returns nil for the same reason the Lisp does: the value splitter does not open that operator.

The object stack is followed when it is read, and the followed list is stored on the returned query. The Lisp writes the global variable.

## Lisp files this step used

`stack.lisp` supplies the goal stack, the canonical form, the loop test, pending equality, the object-stack reader, and the two show functions. `lazy-unify.lisp` supplies the operator lists. `stats.lisp` supplies the inference number. `interpreter.lisp` supplies `handle-looping` and the `or` that this check does not special-case. `loadkb.lisp` clears the goal stack from `reset-kb` and leaves the instances-being-unified list for `reset-inference-engine`.

## What is still absent

A query that runs. `(reset-kb)`, `(show-goal-stack)`, and `(show-obj-stack)` as commands. The part of a loop that evaluates a stored expression and writes it back. The depth limit. `showme`, `showme-all`, `evaluate-all`, and `search-stack`. Inheritance, unification, constraints, prototypes, and recorded explanations. The part of `target-situation` that recognizes a prototype or a theory. Loading and saving.

## How to try it

`clojure -M:test` runs the suite, including the goal stack. At the `KM>` prompt, `(show-goal-stack)` is still printed as text. It is not run. A test calls `som.km.stack`.
