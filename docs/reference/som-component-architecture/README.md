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
| `gear` | The facts a later gear conclusion will read, including the side stored from score. No rule reads these components yet. | `Som-Gear-Piece.km`, `Som-Gear-Report.km`, `Som-Weapon-Skill.km`, `Som-Gear-Goal.km`, `Som-Alignment.km` |
| `practice` | The facts a later practice conclusion will read. No rule reads these components yet. | `Som-Learned-Ability.km`, `Som-Practice-State.km`, `Som-Gain-Offer.km`, `Som-Practice-Room.km` |
| `personality` | The disposition and one bond. No rule reads these components yet. | `Som-Personality.km`, `Som-Social-Connection.km` |

A later chain reads a conclusion an earlier chain wrote.

- Rules 10 and 12 are written in `level/Som-Level-Directive.km`. Their attempts are `(the som-exploration-attempt of Self)`. That slot is written in `command/Som-Command-Choice.km` from the commands stored on the current situation.
- `som-optimal-area` is written in `area/Som-Area-Choice.km`. The exploration attempts do not read it. When one explored area fits the level, that conclusion remains the area those steps serve.
- `som-known-command` is held by the player's situation and declared in `command/som-player-command.km`. `som-area` is held by the projection and declared in `area/som-known-area.km`.
- `som-route-exits` is the conclusion of the route chain, written in `route/Som-Route.km`. It is the `:seq` of exits to take from one explored room to another. `som-requires-open` and `som-requires-unlock` stay on the exits in that seq.

The eleven components in `gear`, `practice`, and `personality` declare slots and have no rules. A later conclusion for one of those chains is a rule in that folder, beside the facts it reads.

The level chain is the chain automation follows today. The caller reads `som-licensed-directive` and sends the first attempt. The clock stays with the caller.

