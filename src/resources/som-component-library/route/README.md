# Routes through explored rooms

This package answers which known exits connect an origin room to a destination.
The player asserts explored rooms and their outgoing exits inside its
`Som-Agentic-Player` situation. A `Som-Route` request returns exit objects in
travel order. The caller decides whether traveling serves its goal, checks
current prerequisites, sends commands, and observes the result.

Load the complete `src/resources/som-component-library` with `(load-lib)`.
The player-situation class comes from the situation package. Routing does not
require a level goal. The [mobile package](../mobile/README.md) consumes routes
when selecting a last-known location to investigate.

| File | Responsibility |
| --- | --- |
| `Som-Explored-Room.km` | Room identities and caller-supplied `som-place-name`. |
| `Som-Room-Exit.km` | Exit direction, destination, and open/unlock prerequisites. |
| `som-player-room.km` | The player's ordered `som-explored-room` sequence and inverse. |
| `som-explored-exit.km` | Each room's ordered `som-room-exit` sequence and inverse. |
| `Som-Route.km` | Route requests, search context, and path conclusions. |

## Assert the map in the player's situation

Start the prompt from the repository root and load the library:

```lisp
(load-lib "src/resources/som-component-library" :silent t)
```

Use stable room and exit identifiers supplied by the caller. A display name
does not establish that two rooms are the same. Each exit belongs to its source
room's sequence; `som-exit-to` supplies the directed connection. Reverse exits
must be observed and asserted separately.

```lisp
(*PlayerA has (instance-of (Som-Agentic-Player)))
(in-situation *PlayerA
  (*Temple has (instance-of (Som-Explored-Room))
               (som-place-name ("Temple"))
               (som-room-exit ((:seq *East-square)))))
(in-situation *PlayerA
  (*Square has (instance-of (Som-Explored-Room))
               (som-place-name ("Square"))
               (som-room-exit ((:seq *North-shop)))))
(in-situation *PlayerA
  (*Shop has (instance-of (Som-Explored-Room))
             (som-place-name ("Shop"))))
(in-situation *PlayerA
  (*Unconnected has (instance-of (Som-Explored-Room))))
(in-situation *PlayerA
  (*East-square has (instance-of (Som-Room-Exit))
                    (som-exit-direction (east))
                    (som-exit-to (*Square))))
(in-situation *PlayerA
  (*North-shop has (instance-of (Som-Room-Exit))
                   (som-exit-direction (north))
                   (som-exit-to (*Shop))
                   (som-requires-open (t))))
(in-situation *PlayerA
  (*PlayerA has
    (som-explored-room ((:seq *Temple *Square *Shop *Unconnected)))))
```

`som-explored-room` and `som-room-exit` each hold one N-to-1 sequence. The rooms
and exits are members of those sequences. Replace a sequence with `now-has`
when its membership or order changes; another `has` does not replace it.
All package slots are fluent, so assertions and computed results stay in the
player's situation. Shared class rules remain visible from the global library.

## Ask for a route

Create a request with an origin and destination in the same player situation:

```lisp
(in-situation *PlayerA
  (*To-shop has (instance-of (Som-Route))
                (som-route-from (*Temple))
                (som-route-to (*Shop))))
(in-situation *PlayerA (the som-route-exits of *To-shop))
; => ((:seq *East-square *North-shop))
(in-situation *PlayerA
  (the som-exit-direction of (the som-route-exits of *To-shop)))
; => ((:seq east north))
(in-situation *PlayerA (the som-requires-open of *North-shop))
; => (t)
```

The result contains exit objects rather than commands. A locked door is
represented by both `som-requires-unlock` and `som-requires-open` set to `t`.
A closed door has the open flag. An unset flag records no requirement for that
step; it does not establish the current physical state of the door. Routing
does not insert `open` or `unlock`, check keys, or issue movement commands.

```lisp
(in-situation *PlayerA
  (*Already-here has (instance-of (Som-Route))
                     (som-route-from (*Temple))
                     (som-route-to (*Temple))))
(in-situation *PlayerA (the som-route-exits of *Already-here))
; => ((:seq))
(in-situation *PlayerA
  (*No-connection has (instance-of (Som-Route))
                      (som-route-from (*Temple))
                      (som-route-to (*Unconnected))))
(in-situation *PlayerA (the som-route-exits of *No-connection))
; => nil
```

## Conclusion contracts

These contracts follow [Conclusion Driven Development](../../../../docs/reference/ConclusionDrivenDevelopment.md).
The consumer is an agent that has chosen a destination and needs a known path.
The context is one root request, its endpoints, and the map visible in the
current player's situation. The caller owns map observations and their ordering.

| Conclusion | Question and supporting evidence | Selection, absence, and limits |
| --- | --- | --- |
| `som-route-found` | Which departing exits support a continuation to the destination? Reads endpoints, room exit sequences, exit destinations, the player's explored-room sequence, and recursive route conclusions. | A sequence of supported exit sequences in outgoing-exit order. Each successful exit prefixes the first supported continuation; this is not an enumeration of every possible path. No connection or equal endpoints leaves this slot empty. |
| `som-route-exits` | Which known exits should be followed, in order? Consumes `som-route-found`, except for equal endpoints. | The first supported sequence. Equal endpoints give a valid empty `:seq` without searching or verifying explored-map membership. Otherwise nil can mean no supported connection or incomplete input/map evidence. It does not prove that no path exists in the world. |
| `som-route-context` | Which root request owns this recursive search? | The request itself for a root, or the supplied `som-route-context-in` for a child. Recursive lookup includes this context, separating cached child results from other requests and enabling repeated-query loop checks. Callers normally leave the internal context input unset. |

The paired `som-route-found-rule`, `som-route-exits-rule`, and
`som-route-context-rule` slots hold the reasoning expressions. Public path
conclusions carry `dont-cache-values`; their rule results can still be cached
within a request. This is why changed evidence requires a fresh root request.

The search skips an exit with no destination, an immediate self-loop, or a far
room absent from the player's explored-room sequence. Recursive requests share
the root context so the engine can detect repeated searches. Selection follows
listed exit order, not distance, danger, travel time, or goal value. A found
connection does not establish that its next transition is currently feasible.

## Validity, feedback, and verification

After a map edit, replace the affected facts and create a new root route. Do not
reuse the identity of an already-queried request or share its internal context
with the new search. KM does not perform general truth maintenance. Player
isolation, request isolation, and reconsideration after new evidence are separate
responsibilities.

```lisp
(in-situation *PlayerA
  (*Shortcut has (instance-of (Som-Room-Exit))
                  (som-exit-direction (up))
                  (som-exit-to (*Shop))))
(in-situation *PlayerA
  (*Temple now-has (som-room-exit ((:seq *Shortcut)))))
(in-situation *PlayerA
  (*To-shop-again has (instance-of (Som-Route))
                      (som-route-from (*Temple))
                      (som-route-to (*Shop))))
(in-situation *PlayerA (the som-route-exits of *To-shop-again))
; => ((:seq *Shortcut))
(in-situation *PlayerA (the som-route-context of *To-shop-again))
; => (*To-shop-again)
```

After moving, the caller checks the observed room against the expected endpoint.
A refusal, blocked door, or unexpected room updates the evidence and prompts a
new search. A returned path or sent command does not establish arrival or goal
completion. Conflicting observations require caller reconciliation; the package
does not rank competing sources or provide a general conflict outcome.

Existing acceptance examples are documented in the [agent test guide](../../../../test/agent-goals/README.md):

| Test | What it establishes |
| --- | --- |
| `exits-to-a-destination-follow-the-listed-order` | Listed-order selection, a cycle, missing exit destinations, same-room empty paths, disconnected rooms, door flags, and a new request after an edit. |
| `a-players-rooms-stay-in-that-situation` | Independent maps and answers when players reuse frame names. |
| `a-new-view-reconsiders-replaced-evidence-and-a-changed-map` | A mobile consumer's fresh view recomputes a route with the same endpoints. |
| `a-new-view-reconsiders-an-intermediate-route-change` | Changed intermediate exits do not reuse an earlier root's cached path. |

Run `clojure -M:test -d test/agent-goals` for these tests and their consumers.
The examples establish inference results, not live navigation, optimal paths,
termination for arbitrary recursive inputs, or successful execution of door and
movement commands. See the [library guide](../README.md) for prompt and loading
instructions and the [object catalog](../../../../docs/reference/som-component-architecture/objects.md)
for the complete vocabulary.
