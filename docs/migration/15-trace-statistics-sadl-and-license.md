# Step 15: Trace, statistics, the event-chain walker, and the licence

`(trace)` records a line for each goal the interpreter enters. The counters from the header are reset and printed. `(do-plan)` walks a chain of events. `(license)` prints the repository licence.

## What you can do now

`(trace)` answers `(t)` and prints `(Tracing of KM switched on)`. A second `(trace)` prints `(Tracing of KM is already switched on)`. `(untrace)` prints `(Tracing of KM switched off)`. A second `(untrace)` prints `(Tracing of KM is already switched off)`. `(tracekm)` and `(untracekm)` are the same commands. `(trace)` itself is not a traced goal.

After `(Fred has (color (red)))` and `(trace)`, `(the color of Fred)` records a call line `-> (the color of Fred)` and an exit line. The answer is still `(red)`. `(Fred has (name ("FRED")))`, `(trace)`, and `(make-phrase Fred)` record the `make-phrase` line and leave out `(the name of Fred)`. The next `(the name of Fred)` records that lookup.

`(spy (the color of Fred))` lists the pattern. The next `(the color of Fred)` prints `(Spypoint reached!)` and `(Tracing of KM switched on)`, then the call line. A later hit prints `(Tracing of KM is already switched on)`. `(unspy)` prints `(All spypoints removed)`.

`(profile (1 + 2))` answers `(3)`. The text contains `(1 + 2)`, `CPU-TIME`, and `# CALLS`. `(profile-report)` answers `(t)` and prints the same table.

`(t2f-on "path")` prints `(Trace-to-file switched on)` and answers `(t)`. A later traced slot read is appended to that file and kept on `:text`. `(t2f-off)` prints `(Trace-to-file switched off)`.

`(comments)` prints that comment display is already on, which is the start. `(nocomments)` prints `(Display of comments is switched off)`.

`(license)` and `(licence)` print the repository `LICENSE` file and answer nil. The text starts with the port preamble and includes `Simplified BSD`, copyright 1994-2015, and `peterc@allenai.org`.

A successful top-level answer carries `:statistics`. The prompt prints the answer, then that line. The line contains `inferences` and `KB accesses`. `(a Cat)` stays the not-ported refusal and has no statistics line.

`(load-kb "file" :print-statistics t)` appends that same line. The text contains `inferences`. A file `(SETQ *TRACE* t)` followed by a slot read traces that read and leaves interactive trace off. A file `(SETQ *RESET-STATISTICS-ENABLED* nil)` makes the next two `(1 + 2)` queries accumulate query-directed inferences, 2 then 4. A file `(SETQ *INFERENCE-REPORT-FREQUENCY* 1)` makes the next slot read print `logical inferences done`.

`(1 & 1)` leaves the unification count at 0. `(_Cat1 & _Cat2)`, after both are Cats, leaves it at 1 or more. `(the color of Fred)` leaves the knowledge-base access count at 1 or more. `(new-situation)` leaves the Skolem count at 1 or more. `(trace)` leaves the maximum trace depth at 0. `(1 + 2)` leaves it at 1 or more.

Inside a situation, `(do-plan _Plan)` walks `first-subevent`, runs `(do-and-next)` for each event, and follows `next-event`. A two-step plan whose second event asserts `(blue)` answers the situation it finished in, and `(the color of Fred)` there is `(blue)`. The text contains `(COMMENT: Executing event`. `(nocomments)` before the walk leaves that comment out. A `next-event-test` of `(quote (the color of Fred))` with `(:args green _OnGreen)` selects `_OnGreen`. A frame with no `first-subevent` records the error and answers nil.

On the HTTP service, `(license)` is HTTP 200, the value is nil, and the text contains `Simplified BSD` and `peterc@allenai.org`. A form that ran includes a `:statistics` string that contains `inferences`. `(a Cat)` stays HTTP 501.

## Where this port differs from the Lisp

The interactive menu is not read. A trace line is recorded and evaluation continues. Nothing returns redo or fail from that menu. The finer comment lines inside inheritance, unification, constraints, and classification are not printed. The five switches are stored, and `(trace)` clears them. `(why)` still prints the KM rule. `(pluralize)` is unchanged.

Trace indent uses `:trace-depth`. The depth ceiling still uses `:depth`, and the limit of 400 is unchanged. A one-element list such as `(1)` is not fully evaluated, so it enters the interpreter and the trace depth moves. `(trace)` and `(untrace)` do not.

A name lookup runs with tracing off and restores the flag afterwards. Step 14 left that binding as a no-op.

The short report is stored on `:statistics`, not appended to `:text`. A zero interval prints `(N inferences and M KB accesses in 0.0 sec)`. A positive interval adds the lips and kaps clause. That clause already ends with a parenthesis, and the sentence adds another. The seconds come from `System/nanoTime`. A test checks the words, not the seconds. Classifications attempted and succeeded stay 0. The classifier that would increment them is not ported.

A knowledge-base access is one successful `get-vals`, not one Lisp `getobj`. A Skolem count is one `create-instance`. Naming a clone does not count. A class description's parent counts, because the port uses that class as the parent. A top-level query zeroes the access count when reset statistics is enabled, so a later query's knowledge base can differ in that counter when the frames are unchanged.

`load-kb` still does not reset the counters for the expressions inside the file. The printed statistics line is the counters since the top-level prepare that ran before the load. A spot line is written on `:text` only when `*INFERENCE-REPORT-FREQUENCY*` is a positive number. A zero elapsed interval prints 0 lips.

`(profile expr)` profiles the nested calls. The outer `(profile ...)` goal is not in the table. The tables survive the next query and clear on `(reset-kb)`. The looping comment `Looping on ...!` and the depth-limit comment are recorded. The comments inside the loop handler stay unprinted.

A traced form that is not ported yet still carries `:text`. The prompt then prints that text and `nil`. The refusal sentence is not the reply.

`(do-plan)` calls `(do-and-next)` through the interpreter. The multiple-next-events sentence prints its two values in the opposite order from the English, which is the Lisp call. After that error, the finishing comment still runs and the answer is the current situation. A test that matches nothing prints both `Ending simulation` and `Finishing simulation`, and the answer is still the current situation. `(evaluate)` runs a quoted expression. It is not Lisp `eval`.

`*SHOW-COMMENTS*` starts true. Older messages that this port never printed stay silent. Only `(do-plan)` uses the new comment writer.

`*TRACE*` inside `load-kb` stores only the trace flag. It does not turn on interactive trace, and it does not call the trace command. The next top-level query's reset turns interactive trace on as well, because either flag being on sets both. A `SETQ` of these flags is accepted only inside `load-kb`. `save-kb` does not write them. `reset` restores the defaults. `(SETQ ...)` at the prompt stays an embedded-Lisp refusal.

`(license)` prints the `LICENSE` file captured when `som.km.license` loads. `licence.lisp` still says copyright 1994-2011 and `peterc@vulcan.com`. The command does not print that older body. The answer is nil. `version` stays unported.

Trace lines are kept on `:text` and, when trace-to-file is on, appended to the named file. The file is UTF-8. A write failure records a user error and the query continues.

## Lisp files this step used

`trace.lisp` supplies the trace flag, the spy list, and the line format. `stats.lisp` supplies the counters and the profile table. `sadl.lisp` supplies `(do-plan)`. `licence.lisp` names the command. The printed text is the repository `LICENSE` file. `interpreter.lisp` supplies the call and exit around one goal. `header.lisp` declares the counters.

## What is still absent

`fastsave-kb`, `fastload-kb`, `faslsave-kb`, and `load-newest-kb`. Arbitrary `eval` and `setq` at the prompt. `do-script` and `in-every-situation`. `is-true`, `all-true`, and `some-true` as commands. `(a Cat)` outside prototype mode. `also-has` as a user command. `showme`, `(comment ...)`, `(show-comment ...)`, and `(the1 ...)`. `explain-all` and `clear-explanations`. The partition check, `originated-from-classes`, and the comment-tag justification walker. The interactive trace menu, and the detailed classify, unify, constraint, and other-situation trace comments. `version`. The step 10 through step 14 gaps stay. `compiled-handlers.lisp`, `compiler.lisp`, and the `htextify.lisp` stub stay unported.

## How to try it

`clojure -M:test` runs the suite, including trace, statistics, `(do-plan)`, and `(license)`. At the `KM>` prompt, `(trace)` prints `(Tracing of KM switched on)` and `(t)`, then a statistics line. `(the color of Fred)` after a stored color records the call line. `(license)` prints the Simplified BSD text and then `nil`. `q` leaves. `POST /query` with `(license)` returns HTTP 200, a nil value, and text that contains `Simplified BSD`. A sum on that service includes a statistics string that contains `inferences`. `(a Cat)` is still refused.
