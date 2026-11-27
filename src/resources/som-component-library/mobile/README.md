# Remembered mobiles

This package supports finding previously encountered mobs for an active level
goal. The player asserts encounter records inside its `Som-Agentic-Player`
situation. The level view identifies experience sources, questions requiring
more evidence, and a route to a selected last-known room. Fresh room readings
and the existing hunt policy still determine whether to consider or engage a
mobile. A remembered encounter does not establish current presence or safety.

Load the complete `src/resources/som-component-library` with `(load-lib)`.
This package depends on the level, situation, and route vocabulary. Its files
are `Som-Mobile.km`, `som-player-mobile.km`, and `Som-Mobile-Choice.km`.

## Assert encounters in the player's situation

Use stable encounter identifiers supplied by the caller. Two mobs with the same
display name can be different records. KM does not infer identity from names.

```lisp
(*PlayerA has (instance-of (Som-Agentic-Player)))
(in-situation *PlayerA
  (*Rat-17 has (instance-of (Som-Mobile))
              (som-mobile-name (rat))
              (som-player (f))
              (som-mobile-last-room (*Cellar))
              (som-mobile-experience (50))
              (som-mobile-experience-level (1))))
(in-situation *PlayerA
  (*PlayerA has (som-known-mobile ((:seq *Rat-17)))))
```

`som-mobile-name` and `som-player` reuse the existing reading vocabulary.
`som-player = f` explicitly identifies a nonplayer. Leave unknown classification
unset; a missing flag is not evidence that a character is a mob.
`som-mobile-experience` is an observed experience gain, not a prediction from
the mob's name or level. `som-mobile-experience-level` is the character's level
when that gain occurred. Zero is a known nonpositive result; an unset value is
unknown. Numeric observations must be numbers in the units used by the caller.
`som-mobile-last-room` is the last observed room, not a claim that the mob is
still there, alive, or available to fight. Use the existing explored-room and
exit records to describe the map in that same player situation.

The caller updates changing facts with `now-has`, including the entire
`som-known-mobile` sequence when adding/removing encounters. A second `has`
does not replace an existing N-to-1 sequence. The sequence is an index of
encounters in caller order; its members are the mobile records.

## Ask from an active level view

Create a normal goal, progress projection, and `Som-Goal-View`, as described in
the [library guide](../README.md). The progress needs the character level and
the clock's kind and target. Add the search origin to the view:

```lisp
(in-situation *PlayerA
  (*View has (som-mobile-search-from (*Temple))))
(in-situation *PlayerA (the som-mobile-search-status of *View))
(in-situation *PlayerA (the som-mobile-needs-evidence of *View))
(in-situation *PlayerA (the som-experience-mobile of *View))
(in-situation *PlayerA (the som-reachable-mobile of *View))
(in-situation *PlayerA (the som-mobile-target of *View))
(in-situation *PlayerA (the som-mobile-destination of *View))
(in-situation *PlayerA (the som-mobile-route of *View))
```

## Conclusion contracts

These contracts follow [Conclusion Driven Development](../../../../docs/reference/ConclusionDrivenDevelopment.md).
The consumer is an agent deciding where to look for experience. All conclusions
apply to one view's goal/projection and the current player's remembered mobs
and explored map. Class rules are shared; evidence and computed values are
fluent and remain in that player's situation.

| Conclusion | Question and evidence | Selection, absence, and limits |
| --- | --- | --- |
| `som-mobile-search-status` | Does this view support a level-experience search? Reads the goal kind/target, projection level/clock identity, and met conclusion. | `ready`, `needs-goal`, `needs-progress`, `unsupported-goal`, `incomplete`, `stale`, or `met`. A changed target invalidates an old clock. Other conclusions produce no answer until status is ready. |
| `som-experience-mobile` | Which records support experience gain at the present character level? Requires a name, explicit nonplayer flag, positive observed gain, and matching observation level. | A sequence in encounter order; an empty sequence means none of the supplied records establishes that claim. It does not prove there are no experience sources elsewhere. A missing location does not invalidate an observed gain. |
| `som-mobile-needs-evidence` | Which nonplayer or unclassified records lack a name, classification, current-level gain evidence, or location? | Encounter order. Known players are excluded. A current-level zero gain with complete location is a negative result, not missing evidence. This conclusion identifies gaps; it issues no survey command. |
| `som-reachable-mobile` | Which evidenced sources have a path from the search origin to their last-known room? Uses the existing route chain and the player's explored rooms. | Encounter order. Missing/unknown origin or absent map context gives no answer; a usable map with no reachable candidates gives an empty sequence. A route may contain exits requiring open/unlock, so connectivity does not establish immediate traversability. |
| `som-mobile-target` | Which reachable source should the caller investigate first? | Greatest observed gain, then encounter order. No candidate gives no answer. This heuristic does not optimize gain per minute, danger, availability, or travel cost. |
| `som-mobile-destination` | Where was the target last seen? | The selected record's room, or no answer without a target. Arrival requires a new observation of the room. |
| `som-mobile-route` | Which exits lead to that room? | Reuses `som-route-exits` and its listed-exit order. Same origin/destination is a valid empty `:seq`; no target or known connection gives no answer. Exit prerequisites remain on the exit records. |

The decision sequence is evidence -> experience sources -> reachable sources ->
target -> last-known room -> route -> external movement -> fresh room evidence.
The existing consider/engage conclusions consume that fresh evidence. This
package neither bypasses health/risk policy nor licenses a kill from memory.
Measured experience is evidence of a past result, not a promise of another one.

## Validity, feedback, and verification

After an encounter, movement, disappearance, kill, experience result, level
change, goal change, or map edit, replace the affected evidence and ask with a
new view and projection. KM caches inferred values and does not perform general
truth maintenance. Context isolation does not invalidate an old view. Treat
contradictory incoming observations as a reconciliation task for the caller:
keep the authoritative latest assertion with `now-has`; the package does not
resolve competing sources or report a general conflict outcome.

A failed move, absent mob, or refused attack is new evidence. Update location
or map records and reconsider; a licensed or sent command is not observed
completion of the level goal. The caller decides when a historical location is
too old to investigate and removes it or retracts its location. No spawn timing
or absence of observation is interpreted as proof of current availability.

Run `clojure -M:test -n som.km.mobile-goal-test`. Its examples verify positive,
zero, negative, missing, and level-mismatched experience; player exclusion;
reachable versus unreachable rooms; yield ordering/ties; same-room empty paths;
door flags; incomplete/stale/met goals; changing level, evidence, and map;
and independent player situations. The suite ends at conclusions. Live movement,
combat outcomes, recursive routing on arbitrary maps, and source reconciliation
are outside its acceptance claim.
