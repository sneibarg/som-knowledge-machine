# Step 26: The small texts

A number below 1 uses the Lisp exponent width. A positive statistics line keeps the extra closing parenthesis. `(version)` prints the Knowledge Machine banner and answers `(t)`. The prompt and the HTTP service both call the same engine function.

## What you can do now

`(make-phrase 0.0001)` is `1.000e-4`. `(make-phrase -0.5)` is `-5.000e-1`. `(make-phrase 1.0e-10)` is `1.000e-10`. `(make-phrase 1.5)` is `1.500`. `(make-phrase 0.5)` is `0.5`. `(make-phrase 0.0)` is `0.000e+0`. `(make-phrase -5.0)` is `-5.000e+0`.

A statistics line for a zero interval is `(0 inferences and 0 KB accesses in 0.0 sec)`. A positive interval ends with `kaps]))`. The lips clause already closes, and the sentence adds the parenthesis after it.

`(version)` prints six spaces, a rule of fifty-two equals signs, `KM - THE KNOWLEDGE MACHINE - INFERENCE ENGINE v2.5.45`, the same rule, and the 1994-2015 copyright. The answer is `(t)`. `(VERSION)` prints the same text. `(version extra)` stays the embedded-Lisp refusal.

On the HTTP service, `(version)` is HTTP 200, the value is the symbol `t`, the text contains `INFERENCE ENGINE v2.5.45`, and the statistics line contains `inferences`.

## Where this port differs from the Lisp

`anglify.lisp` formats a number below 1 with `~,Ne`. The exponent field is omitted, so the printer uses as few digits as the exponent needs, and at least one. `0.0001` is `1.000e-4`. `-0.5` is `-5.000e-1`.

`report-statistics` writes the lips clause as ` [n lips, m kaps])` and then adds `)`. That extra parenthesis stays. A zero interval has the one parenthesis on `sec)`.

`(version)` is the function in `initkb.lisp`. It returns `t`, and the prompt path makes that `(t)`. The `.km` files in this tree do not call it. The command returns when a transcript contains it. The session banner printed at startup stays the prompt's own text. Loading the engine does not print the `(version)` banner as well.

## Lisp files this step used

`anglify.lisp` formats the number inside `expand-text0`. `stats.lisp` supplies `report-statistics`. `initkb.lisp` supplies `(version)`. `header.lisp` supplies `*km-version-str*` (`2.5.45`) and `*year*` (`2015`). `interpreter.lisp` lists `version` among the expressions that run at the `KM>` prompt.

## What is still absent

`(anonymous-instancep ...)` stays refused, and `(function ...)` stays refused. `(sanity-check ...)` answers `(t)` and leaves its body unread. An action precondition that goes through `(a Thing with ...)` still stops the action. `fastsave-kb`, `fastload-kb`, `faslsave-kb`, and `load-newest-kb` stay refused. `(SETQ ...)` at the prompt stays refused. A custom aggregation function stays refused. `(explained-by ...)` stays refused. A cached explanation stays unported. The numbered wrap-up list is complete. The corpus comparison in the outcome review is the acceptance condition for the port.

## How to try it

`clojure -M:test` runs the suite, including these texts. At the `KM>` prompt, `(make-phrase 0.0001)` answers `1.000e-4`. `(version)` prints the banner and `(t)`. `q` leaves. `POST /query` with `(version)` returns HTTP 200 and the symbol `t`.
