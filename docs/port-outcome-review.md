# Where the port still differs, and how to wrap it up

The planned steps are finished, and a large part of the engine already matches Knowledge Machine 2.5.45. What still changes an outcome is concentrated in a few unfinished reasoning paths. A query that Lisp answers by filtering a slot comes back here as a refusal, a different value, or a knowledge base with different links. Loading a file that contains one of those forms stops, even when error handling is set to continue.

This report reviews the "where this port differs" sections in `docs/migration/`. Notes 00 through 05 describe the engine before a query ran. Later notes close many of those gaps. The open differences below are the ones no later note takes back. Two of those later closures are worth naming so they are not redone: a name lookup now runs with tracing off and restores the flag, and `(load-kb ... :print-statistics t)` prints the real counter line. Ordinary instances are created. That note is [Ordinary instances](migration/16-ordinary-instances.md). Definitions are stored and classification runs. That note is [Definitions and classification](migration/17-definitions-and-classification.md). Rule bodies run. That note is [Rule bodies](migration/18-rule-bodies.md). Instance edits and position reads run. That note is [Edits and position](migration/19-edits-and-position.md). Stored flags change the read. That note is [Stored flags](migration/20-stored-flags.md). One survivor is kept when several sources contribute. That note is [One survivor](migration/22-one-survivor.md). Two quoted descriptions are tested, including when they name slots, and the temporary instance is removed. `Door.km` in the component library loads and answers the parts its rules name. `Entity.km` still uses `anonymous-instancep` and `has-value`.

## Where an answer or the knowledge base diverges

**An action precondition still stops.** An action precondition that goes through `(a Thing with ...)` still stops the action instead of counting as an unsatisfied precondition.

**Several forms inside a normal rule are still refused.** `(if ...)`, the `allof` / `oneof` / `forall` family, `called`, `uniquely-called`, and `(the Class slot of frame)` now run. Instance `also-has`, `also-hasnt`, and `now-has`, `(the1 ...)`, `(the2 ...)`, `(the3 ...)`, `(theN ...)`, `(theNth ...)`, and sequence `append` and `reverse` now run. `(anonymous-instancep ...)`, `(has-value ...)`, `(function ...)`, and `showme` stay refused. The later wrap-up steps still cover explanations, file order, and the remaining commands. `Entity.km` still stops where it calls `anonymous-instancep` or `has-value`.

**`(sanity-check ...)` leaves its body unread.** It answers `(t)` while the sanity flag is unset.

**Explanations cite a different record.** Records are stored oldest first. Lisp stores newest first, and the same duplicate check therefore keeps the other record. `(why)` prints that record as a KM rule. A binding copies the bound-away frame's records onto the survivor and also leaves them on the bound-away frame. Lisp deletes that frame. A `remove-subsumers` record whose triple has disappeared is kept. A cached explanation and a `:set` explanation are not stored, so `(why)` reports that nothing was recorded for a value Lisp can explain. `(result-of ...)` and `(precondition-for ...)` print as `(|<location unknown>| ...)`.

**`(justify)` prints a different sentence.** With both flags at their defaults, the port prints the subgoal line. Lisp prints that line only in developer mode. When `justify-leaves` is on and developer mode is off, the sentence is `The <slot> of <phrase> = <phrase>.` and the `(from Class, ...)` suffix is missing, because `originated-from-classes` is unported. `(comment ...)` and `(show-comment ...)` are refused, so the because line and the ENTRY TEXT and EXIT TEXT lines are absent, and a save writes an empty comments section. `(explain-all)` and `(clear-explanations)` are refused.

**Order changes which instance is first.** `(taxonomy)` walks the stored list. Lisp sorts with `string<`. A later superclass of Thing appears earlier, because that slot inserts at the front. The cleanup deletes a redundant link and does not reattach an unplaced class to its partition, so the class stays marked `?` and the subclass links stay unplaced. A save groups frames by insertion order. Lisp sorts each group by symbol name. `(the1 ...)`, `(the2 ...)`, `(the3 ...)`, `(theN ...)`, and `(theNth ...)` read by the stored order. `showme` and `showme-all` stay refused, so a listing that would print that order still stops. Two saves of one value match. Lisp includes the time, so two saves of one image differ as text. That determinism is the better file; it is a transcript difference only.

**A round trip moves facts.** A situation-local explanation is written and then stored in `*Global` on reload, so `(why)` after the load looks in the wrong situation. The empty prototype is saved as `(a-prototype Class)`. Lisp writes the misspelled head `a-prototoype` when there are no slot pairs, so that form does not reload on the other side. `(has-definition ...)` is written when a definition is stored, and that command loads. `(in-every-situation ...)` is written when that form is stored, and the command is refused, so a file that contains it still stops. `undo` restores the snapshot, including done flags. Lisp replays the log and then clears those flags. `undo-creations` does not accept a dont-delete list and does not return to `*Global`. `store-kb` keeps the undo history on the value. A binding cycle throws. Lisp loops. The throw is the outcome to keep.

**Smaller command gaps still change a session.** Instance `also-has`, `also-hasnt`, and `now-has` run. Class-level `also-has` and `now-has` already append or replace the rule. `do-script`, `in-every-situation`, `nowexists`, `is-true`, `all-true`, and `some-true` are refused. `most-specific`, `most-general`, and a custom aggregation function are refused. `(function ...)` is refused. `fastsave-kb`, `fastload-kb`, `faslsave-kb`, and `load-newest-kb` are refused, and `(SETQ ...)` or `eval` at the prompt is refused. A `.km` file of Knowledge Machine expressions is the load path the plan chose. A fastsave image or a file that splices a Lisp variable with `#t` does not load. `#t` at the prompt and on HTTP looks in an empty map. A file in an encoding other than UTF-8 or ISO-8859-1 can change a string.

**Printed text differs while the answer list stays.** A number below 1 uses a two-digit Java exponent, so `0.0001` is `1.000e-04`. A positive statistics line keeps the extra closing parenthesis from the Lisp format. The access count is one successful `get-vals`, and a top-level query zeroes it, so two knowledge-base values can differ in that counter when the frames are the same. `(license)` prints the repository `LICENSE` file (1994–2015, `peterc@allenai.org`). The Lisp function prints the older `licence.lisp` body. `(pluralize ...)` records the KM 1.4 error and answers nil, which is what 2.5.45 does. `(trace)` records the line and continues. The menu is not read, so a session cannot redo or fail at that point. Finer classify, unify, constraint, and other-situation comments are not printed. A traced form that is not ported yet makes the prompt print the trace and `nil`. A query deeper than 400 stops. Lisp has no default depth ceiling. Queries that fit match.

## What to leave alone

These are already the same outcome, or they are a boundary the plan recorded on purpose.

- One handler table. `compiled-handlers.lisp` and `compiler.lisp` stay out. `htextify` returns nothing, and ordinary `(taxonomy)` does not ask it for HTML.
- No interactive debugger. `continue`, `ignore`, and `abort` already match when the caller does not resume a Lisp restart.
- Saves stay deterministic and omit `(now)`.
- A binding cycle throws.
- `(pluralize)` stays the 2.5.45 error.
- The multiple-next-events sentence keeps the Lisp argument order.
- `(license)` keeps the repository licence.
- `km-equal`, the ratio and overflow arithmetic, and `0 / 0` yielding `(1)` already follow the Lisp.
- Insertion order replaces hash order. Hash order already differs between Lisp implementations. Sorts that Lisp does with `string<` are a separate change, listed below.

## Next steps

Each step is done when the queries in its note return the same answer list and the same frames on both sides, and `clojure -M:test` is green.

1. **Ordinary instances.** Done in [Ordinary instances](migration/16-ordinary-instances.md). `(a Class)` and `(a Class with ...)` create an anonymous instance outside prototype mode, including the Skolem and the object stack. A path is stored and evaluated when the slot is read. `(the+ ...)` on a miss, an inherited `(a Cat)`, and a leftover existential in `&&` return an instance. Two quoted descriptions are tested, including when they name slots, and the temporary instance is removed.

2. **Definitions and classification.** Done in [Definitions and classification](migration/17-definitions-and-classification.md). `has-definition` and `now-has-definition` store a definition. Classification runs on a slot read, after a successful `&`, and when load is asked to evaluate instances. A prototype applies through that test, including when the description has slots. Those attempts are counted.

3. **The rule bodies those definitions contain.** Done in [Rule bodies](migration/18-rule-bodies.md). `(if ... then ... else ...)`, `allof`, `oneof`, `forall` and their `?var in` forms, the sequence and bag forms, `called`, `uniquely-called`, and `(the Class slot of frame)` run. `(anonymous-instancep ...)` and `(has-value ...)` stay refused, so `Entity.km` still stops on those calls.

4. **Edits and position.** Done in [Edits and position](migration/19-edits-and-position.md). Instance `also-has` appends, `also-hasnt` deletes, and `now-has` replaces. `(the1)`, `(the2)`, `(the3)`, `(theN)`, and `(theNth)` read by position. Sequence `append` and `reverse` build one sequence.

5. **Make the stored flags affect the read.** Done in [Stored flags](migration/20-stored-flags.md). `(no-inheritance)` skips inheritance and subslots. `set-filter` filters. `(sometimes ...)` evaluates its body. A default is applied once. A top-level query turns inverse installation back on. Load leaves inverses off when the knowledge base had them off. The inverse of `<>` is written. `(sanity-check ...)` still answers `(t)`.

6. **One survivor when several sources contribute.** Done in [One survivor](migration/22-one-survivor.md). A supersituation or theory climb keeps the earlier duplicate. A looping residue that is not the current goal is evaluated and written back. A prototype reached through `cloned-from` is unified again, a user appending slot joins values that share a cloned source, and `remove-clone-cycles` drops a cyclic clone explanation. Pieces of an `&` expression are linked in the situation that was current. A class with nothing stored has Thing as its superclass, and the built-in superclass slots stay empty until stored.

7. **The same explanation.** Store explanation records newest first, drop a record whose triple is gone, and store a `:set` explanation. Port `(comment ...)`, `(show-comment ...)`, `originated-from-classes`, and the comment-tag walker. `(why)` then prints the because line. `(justify)` adds the from-classes suffix and, with both flags off, omits the developer subgoal line. Port `explain-all` and `clear-explanations`. Put a situation-local explanation back into that situation on load.

8. **The same file.** Accept `a-prototoype` as the empty prototype head, and write it when saving that form. Sort taxonomy and each save group with `string<`, and reattach an unplaced class during `(taxonomy)` cleanup. Reset the inference counters at the start of `load-kb`. After the forms in real files run, a not-ported form inside a load should follow `:on-error` instead of always aborting.

9. **The remaining commands a transcript calls.** `showme`, `showme-all`, `evaluate-all`, `is-true`, `all-true`, `some-true`, `do-script`, `in-every-situation`, `nowexists`, `thelast`, `exists`, `has-value`, and `print` / `format`. `do-script` and `in-every-situation` matter because a save already emits the second of those.

10. **Lock the small texts.** Format a number below 1 with the Lisp exponent width. Leave the extra statistics parenthesis in place, since that is the Lisp sentence. Add `(version)` if a transcript needs the command to return.

The port is wrapped up when a corpus of `.km` files that use creation, definitions, `(if ...)`, and quantifiers loads on both sides, and a fixed set of queries agrees on the answer list under `km-equal`, on which frames are instances of each class, and on `(why)` where the corpus records an explanation. The permanent list above is the residue that comparison is allowed to show.
