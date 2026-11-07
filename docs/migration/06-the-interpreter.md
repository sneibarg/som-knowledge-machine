# Step 6: The interpreter

An expression now runs. The prompt and the HTTP service both call `som.km.engine/evaluate`, and that function calls one dispatcher. `:value` is the answer list. A form this step does not run is still in the handler table, in the original order, and it returns the not-ported refusal.

## What you can do now

`(1 + 2)` answers `(3)`. `(1 + 2 + 3)` answers `(6)`. `(1 - 2 - 3)` answers `(-4)`, because the left-grouping rewrite runs before the subtraction. `(1 / 2)` is the exact ratio `1/2`. `(2 ^ 10)` is `1024`. `(2 ^ 100)` is the full integer. `(2 ^ -2)` is `1/4`. `0` divided by `0` is `1`, a nonzero number divided by `0` is `999999`, and `0` divided by a nonzero number is `0`. The same three results hold for `0.0`. A power that uses a float base or a float exponent is a double.

`(1 > 0)`, `(1 = 1)`, `(1 = 1.0)`, `(1 /= 2)`, and `(1 = 2 +/- 1)` answer `(t)` or nil. `(1 and 2)` answers `(2)`. `(nil and (a Cat))` answers nil and does not ask for the cat. `(f or 2)` answers `(f)`. `(not nil)` answers `(t)`. `(numberp (1 + 2))` answers `(t)`.

`(Fred has (color (red)))` stores the color on Fred and answers `(Fred)`. `(the color of Fred)` answers `(red)`. `(assert (:triple Sue age 30))` is that same store and answers `(Sue)`. `(delete Sue)` answers `(t)` when Sue is a frame. `(the subclasses of Sequence)` answers `(Triple Pair)`, the subclasses stored on Sequence. A value that exists only on a class is not visible: `(every Cat has (color (black)))` is refused, and `(the color of Cat)` is nil. `(the number of (:set 1 2))` answers `(2)`. `(the sum of (:bag 1 2 3))` answers `(6)`. `(the min of 3)` answers `(3)`.

`(must-be-a Cat)`, `(sometimes (1 + 2))`, and the other constraint forms answer nil and set the constraints flag. `(sometimes (1 + 2))` does not answer `(3)`. `(sanity-check (Fred has (color (red))))` answers `(t)` and does not store the color. A constraint stored on a slot is put back after a read, so `(the color of Pat)` stays nil while `(must-be-a Color)` remains on Pat.

`(reset-kb)` answers `(t)` and rebuilds the vocabulary. `(show-goal-stack)` at the prompt shows an empty stack, because a top-level call clears the stack before the command runs. `(show-obj-stack)` shows the frames touched since the last clear, and answers `(t)`. `(new-context)` clears that stack and answers `(t)`. `(fail-noisily)` answers `(t)`, and the next expression on the same query reports an empty lookup. `(fail-quietly)` puts the quiet mode back. `(eval ...)`, `(setq ...)`, and `(function ...)` are refused by name. `(load-kb ...)` is refused as a later load step. `(fastsave-kb ...)` says fastsave stays unported. `(trace)` says tracing is not ported yet.

`(a Cat)` is refused. `(an Cat)` is a syntax error: the handler table has no `(an ?class)` pattern, so the answer is nil, `:ok` stays true, and HTTP stays 200. `(an instance of Cat)` is a pattern, and it is refused.

## Where this port differs from the Lisp

The result is one map. `:value` is the answer list. `:errors`, `:error-structures`, and `:warnings` are the extra Lisp return values, in the order they were recorded. An error is recorded and reasoning continues. Nothing is printed, and the debugger is not entered. The continuation sentence is not added. The prompt prints the answer, then `   ; (WARNING: Errors occurred during reasoning)` on the same line when `:errors` is not empty.

Each adapter holds the knowledge base and the query for its own caller. A call that omits them starts from the built-in vocabulary. Two requests on one running service see each other's assertions. A separate `evaluate` does not. The JSON body leaves `:kb` and `:query` out. A proper list is an array. A symbol, a keyword, a dotted cons, and a ratio are objects. An integer that fits in a long is a number. A larger integer is decimal text.

A top-level call clears the goal stack, the instances being unified, both inference counters, the depth, and the looping flag. It leaves the object stack, the fail mode, and a caller's depth limit. It does not turn inverse installation back on. The Lisp re-enables inverses on each top-level call. `(reset-kb)` then rebuilds the vocabulary and clears both stacks. The counters stay at zero because the top-level clear already ran. `som.km.engine/reset`, called directly, still keeps the counters and the unification list.

The depth limit starts unset, as in the Lisp. A query deeper than 400 stops the way a set limit would. A caller can also set `:km-depth-limit` on the query. The test is depth greater than the limit.

`(1 + 2)` counts two inferences. The sum is one, and the tail `(2)` is evaluated as its own expression. A fully evaluated atom, and a command such as `(reset-kb)` or `(show-goal-stack)`, does not count. `(new-context)` does, because it is a handler.

A repeated `(the age of Fred)` whose stored value is that same expression answers nil, sets `:looping?`, and the final write of nil removes the slot. The recovery that would evaluate the residue and write it back is not done. A fully evaluated stored value is returned.

The six sources of a slot value exist. Prototypes, projection, subslots, supersituations, and inheritance contribute nothing. There is no done-cache. One read writes the local result once. A ground value read again is the same value. A unification of four or more elements is rewritten before it is walked, and the "badly formed" sentence is not reported. `called` and `uniquely-called` are read from the local store. `most-specific` and `most-general` are refused. A custom aggregation function is not evaluated. `(the Cat color of Fred)` is refused until class membership exists. `(the color)` matches `(the ?frame)` and is refused.

`(show-goal-stack)` is dispatched even though it is not in the Lisp command list. Extra arguments on a command are ignored. An `or` already on the stack does not hide a repeated goal. `&+!` is not opened by the value splitter.

## Lisp files this step used

`interpreter.lisp` supplies `km`, `km-int`, `km1`, `km-unique`, the handler table, and `report-error`. `get-slotvals.lisp` supplies the local read and the aggregation slots. `frame-io.lisp` supplies `are-slotsvals`. `km.lisp` supplies the arithmetic rewrites. The load and save names, and the trace commands, are recognized here and refused until their own steps.

## What is still absent

Unification. `&`, `&!`, `&&`, and the other equality operators are in the table and refused. Constraint enforcement. Inheritance, prototypes, projection, and supersituations. Classification. Explanations. Situations, actions, and theories. Loading and saving. English answers. Trace and statistics. Embedded Lisp.

## How to try it

`clojure -M:test` runs the suite, including the interpreter. At the `KM>` prompt, `(Fred has (color (red)))` stores the color, and the next line `(the color of Fred)` answers `(red)`. `q` leaves. The HTTP service on `127.0.0.1` port `8080` evaluates `POST /query` the same way. Two posts share the service's knowledge base.
