# Step 13: Load, save, and undo

A knowledge base can be written as KM text and read back. Undo restores a snapshot of the value the caller holds. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(start-logging)` turns the undo log on and answers `(t)`. The text says it started, or that it was already on. While it is on, each top-level command except `showme`, `undo`, and `why` stores a snapshot of the knowledge base before the command runs. `(Fred has (color (red)))`, then `(undo)`, answers `(t)`, prints `Undone (Fred has (color (red)))...`, and the color is empty again. A second assertion after the first is the only one a single `(undo)` removes.

`(checkpoint here)`, then an assertion, then `(undo here)` returns to the value from before that assertion. `(checkpoint)` uses the id `t` and answers `(t)` even when logging is off. The checkpoint is stored only while logging is on. `(checkpoint nil)` records that the argument cannot be NIL and answers nil. `(stop-logging)` drops the history and turns the log off.

`(keeping-kb (Fred has (color (red))))` answers `(Fred)`. The color is then empty. The body's value is kept, including a refusal, and the frames return to the checkpoint taken before the body.

`(start-creations-logging)`, then `(set-creations-checkpoint)`, then `(a Situation)`, then `(undo-creations)` deletes `_Situation1`. The next `(a Situation)` is `_Situation1` again. A named frame such as Fred is left in place. `(undo-creations)` while command logging is on answers nil and says to call `(stop-logging)` first. Creation logging starts by itself when a checkpoint is requested and it was off. The two warning lines come first.

`(store-kb)` remembers the value on itself and answers `(t)`. `(Fred has (color (red)))`, then `(restore-kb)`, clears that color and answers `(t)`. A second restore returns to the same snapshot. With nothing stored, the text says there is no stored KB state and the answer is nil.

`(write-kb)` puts the KM text on `:text` and answers `(t)`. Two writes of one value are the same text. The header is `;;; Current state of the KB (KM 2.5.45)` and it has no clock. `(save-kb "path")` writes that text as UTF-8 and says the path was saved. `(reload-kb "path")` resets, then loads the file. `(Fred has (color (red)))`, then `(Fred has (color (green)))`, then `(new-situation)`, then a local `(Fred has (color (blue)))`, then save and reload, keeps red before green on the global color, keeps blue on `_Situation1`, and restores situations mode, the current situation, and the gensym counter.

`(load-kb "path" :with-morphism ((Node -> Device)))` renames Node to Device before each expression runs. `:load-patterns ((?x has (color (red))))` evaluates only the matching expressions. A missing file records `No such file`, answers nil, and stays `:ok`. A file is read as UTF-8. Bytes that are not UTF-8 are read as ISO-8859-1, so a lone `0xE9` byte in a string is `é`. A UTF-8 `café` string round-trips.

`(every Cat has (color (black)))`, an instance, a color read, then save and reload, keeps an explanation record. `(the color of _Cat1)`, then `(why)`, still prints the rule. A `(SETQ *KM-GENSYM-COUNTER* '41)` in a file sets the counter to 41. `(SETQ *NOT-A-PARAMETER* '1)` in a file records that the setq is refused. The same SETQ at the prompt stays an embedded-Lisp refusal.

`(fastsave-kb "x.fkm")` and `(fastload-kb "x.fkm")` stay refused, with `fastsave stays unported`. `(load-newest-kb)` stays refused. On the HTTP service, after Fred's color is stored, `(write-kb)` is HTTP 200 and the text contains `(Fred has`. `(fastsave-kb "x.fkm")` is HTTP 501. `(a Cat)` on that service stays HTTP 501.

## Where this port differs from the Lisp

Undo restores the snapshot taken at the checkpoint, including the done flags. The Lisp replays the undo commands it logged and then clears done flags. A checkpoint here is the whole value, so a mutation that did not pass through a top-level command is undone only back to the last snapshot. `(undo)` at the prompt prints the Undone line. A nested `(undo)` answers `(t)` or nil and does not print that line.

Two saves of one value match. The Lisp header includes `(now)`, so two saves of one image can differ. Frames are grouped as slots, theories, situations, prototypes, and then the rest, so a situation exists before an `(in-situation ...)` form. Inside each group the order is the order the frames were first stored. The Lisp sorts each group by symbol name. `*Global` is written with the situations because it is an instance of Situation. A bound name is a comment and is not bound again on load.

`append` is a reserved name, so its own frame is a comment and the vocabulary value from `(reset-kb)` is what reloads. A reserved name that is already a frame can still appear as a slot value, so the instances list that names `append` reloads. A reserved name that is not a frame is still refused.

The file disables slot checking, classification, and inverse installation, then the SETQ lines restore the flags this port stores, and `(enable-installing-inverses)` turns inverses on. The inverse flag is not one of the saved parameters, so a knowledge base whose inverses were off ends with them on. `*LOGGING*` is written and ignored on load. The load forces both logging flags off and puts the caller's flags back, including when the file contains `(reset-kb)`.

A situation-local explanation is written and then recorded in `*Global` on reload. `(has-definition ...)` and `(in-every-situation ...)` are written when those slots are stored, and both commands stay refused, so a file that contains one of them stops. A not-ported form stops the load even when `:on-error` is continue. A read error in the file is a user error on the load command. It is not an HTTP 400 for the `(load-kb ...)` text itself.

The load does not clear the inference counters. The Lisp resets them at the start of `load-kb`. `:print-statistics t` adds `Statistics are not ported yet.` and does not fail. `:eval-instances t` re-reads slot values that are not fully evaluated. It does not classify. `with-morphism` replaces the renaming alist stored on the value. It does not add to an older table. The table is cleared when that load finishes.

`keeping-kb` evaluates the KM expressions and restores the value. The Lisp macro wraps Lisp forms. The caller's logging flag is put back. `undo-creations` does not take a dont-delete list. It does not switch the current situation to `*Global`. The count in the timing line is the position of the checkpoint. `store-kb` keeps the snapshot on this value, including the undo history. The Lisp keeps one process-wide copy of the property lists and the parameters, and it does not keep the undo log. The stored-state comment is not printed.

Save writes UTF-8. The Lisp uses the implementation's default encoding. `htextify` returns nothing. A save does not ask for HTML, so names are written as KM text. The comments section stays empty because `(comment ...)` stays refused. `(the1 ...)` stays unported. Order is checked with `get-vals`.

## Lisp files this step used

`loadkb.lisp` supplies load, save, the undo log, the creation log, and `keeping-kb`. `writer.lisp` supplies the frame text and the knowledge-base text. `interpreter.lisp` supplies the prompt checkpoint and the checkpoint and undo handlers. `header.lisp` supplies the behavior and state parameters the SETQ lines restore.

## What is still absent

English sentences and `(taxonomy)`. Trace, statistics, SADL, and the license text. `fastsave-kb`, `fastload-kb`, `faslsave-kb`, and `load-newest-kb`. Arbitrary `eval` and `setq` at the prompt. `do-script`, `do-plan`, and `in-every-situation`. `is-true`, `all-true`, and `some-true` as commands. `(a Cat)` outside prototype mode. `also-has` as a user command. `showme`, `(comment ...)`, and `(the1 ...)`. The step 10 and step 11 gaps stay.

## How to try it

`clojure -M:test` runs the suite, including load, save, and undo. At the `KM>` prompt, `(start-logging)`, then `(Fred has (color (red)))`, then `(undo)`. The color is empty and the text says what was undone. `(write-kb)` prints the knowledge base. `q` leaves. `POST /query` with `(write-kb)` on a service that already stored Fred returns that text. `(fastsave-kb "x.fkm")` is still refused. `(a Cat)` is still refused.
