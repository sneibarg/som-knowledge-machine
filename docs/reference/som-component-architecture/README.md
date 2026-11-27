# Springs of MUD component architecture

These notes describe the components in `src/resources/som-component-library`. How to load the directory and how to ask one question are in the [library README](../../../src/resources/som-component-library/README.md).

- [Vocabulary](vocabulary.md) lists the classes, the relations, and the slots the caller asserts.
- [Objects](objects.md) names every class, relation, inverse, conclusion, helper, and `*-rule` slot.
- [Reasoning](reasoning.md) lists pace, the notch, the hunt rules that license a directive, the explored-area choice, the commands that serve a goal, and the exits to a destination.

The caller owns the clock. Each query is one score, one death, or one view. The returned knowledge base holds that answer. The next event asserts a fresh projection with the notch, cooldown, and counters the caller stored.

## Conclusion driven development

The general architecture is described in [Conclusion Driven Development](../ConclusionDrivenDevelopment.md). This section describes its application to this component library.

Conclusion driven development builds an inference chain that automation can follow. The caller asserts the facts. A rule reads those facts and writes a conclusion. Automation reads the conclusion and acts. The component that writes the conclusion sits with the components that supply its facts.

`(load-lib)` walks this library recursively. The load path remains `src/resources/som-component-library`. Each folder below is one chain. A folder name differs from every component pathname-name, because a file `Name.km` is probed as the directory `Name/`.

| Folder | What the chain decides | Components |
| --- | --- | --- |
| `situation` | The partition for one player. `som-bootstrap` is asserted here when bootstrap has completed. | `Som-Agentic-Player.km` |
| `level` | Pace, the notch, and the directive for one score, death, or view. | `Som-Level-Goal.km`, `som-goal.km`, `Som-Progress-Projection.km`, `som-progress.km`, `Som-Mobile-Reading.km`, `som-reading.km`, `Som-Goal-View.km`, `Som-Level-Directive.km`, `som-licensed-directive.km` |
| `area` | The explored area whose range contains the character's level. | `Som-Area.km`, `som-known-area.km`, `Som-Area-Choice.km` |
| `command` | The known commands that serve a goal, and the exploration attempts hunt rules 10 and 12 send. | `Som-Known-Command.km`, `som-player-command.km`, `Som-Command-Choice.km` |
| `route` | The exits to take from one explored room to another. | `Som-Explored-Room.km`, `Som-Room-Exit.km`, `som-explored-exit.km`, `som-player-room.km`, `Som-Route.km` |
| `mobile` | Evidence-backed experience sources and a route to a selected last-known mobile location. | `Som-Mobile.km`, `som-player-mobile.km`, `Som-Mobile-Choice.km` |
| `gear` | Gear observations and sources, observed equipment, and bounded re-gearing through shops, corpses, rooms, and intermediate mobs. | See the [gear guide](../../../src/resources/som-component-library/gear/README.md). |
| `practice` | The facts a later practice conclusion will read. No rule reads these components yet. | `Som-Learned-Ability.km`, `Som-Practice-State.km`, `Som-Gain-Offer.km`, `Som-Practice-Room.km` |
| `personality` | The disposition and one bond. No rule reads these components yet. | `Som-Personality.km`, `Som-Social-Connection.km` |

A later chain reads a conclusion an earlier chain wrote.

- Rules 10 and 12 are written in `level/Som-Level-Directive.km`. Their attempts are `(the som-exploration-attempt of Self)`. That slot is written in `command/Som-Command-Choice.km` from the commands stored on the current situation.
- `som-optimal-area` is written in `area/Som-Area-Choice.km`. The exploration attempts do not read it. When one explored area fits the level, that conclusion remains the area those steps serve.
- `som-known-command` is held by the player's situation and declared in `command/som-player-command.km`. `som-area` is held by the projection and declared in `area/som-known-area.km`.
- `som-route-exits` is the conclusion of the route chain, written in `route/Som-Route.km`. It is the `:seq` of exits to take from one explored room to another. `som-requires-open` and `som-requires-unlock` stay on the exits in that seq.

Nine legacy classes retain declarations without behavior of their own. Gear piece and goal metadata now supports re-gearing rules in the same gear folder; practice and personality policies remain absent.

The level chain is the chain automation follows today. The caller reads `som-licensed-directive` and sends the first attempt. The clock stays with the caller.

## Remembered mobile chain

The [mobile contract](../../../src/resources/som-component-library/mobile/README.md)
defines player-owned encounter evidence and conclusions on `Som-Goal-View`.
`som-known-mobile` belongs to the player situation. Mobile records reuse
`som-mobile-name` and `som-player`; positive experience is qualified by the
character level where it was observed. Sources -> reachable sources -> target
-> last-known room -> route is an investigation chain. It reuses `Som-Route`,
preserves door prerequisites, and supplies no attack directive. The consumer
must observe the room again before using existing consider/engage rules.
New evidence, map, or goal requires a new view. No truth maintenance is claimed.

## Gear recovery chain

The [gear contracts](../../../src/resources/som-component-library/gear/README.md)
separate studied pieces and source sightings from actual possessions. One
confirmed player snapshot and an existing `Som-Gear-Goal` feed a fresh
`Som-Regear-Request`. Tasks satisfy equipment prerequisites, reserve purchase
funds, reuse routes, and project acquisition/equip transitions. Only supported
complete strategies are returned. Examined player gear remains observation-only;
mobile loot additionally needs an evidence-backed conditional combat model.
After death or any attempted transition, the caller supplies a new observation
and request. Projected equipment is never installed as actual equipment.
