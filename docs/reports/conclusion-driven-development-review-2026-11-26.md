# Conclusion Driven Development Review

Date: 2026-11-26

## Assessment

The [component architecture README](../reference/som-component-architecture/README.md) establishes a useful architectural direction: facts support named conclusions, and automation consumes those conclusions. Its main opportunity is to define conclusion-driven development as a method for designing and validating behavior, beyond organizing components into inference chains.

The defining question is: **What must the agent be able to conclude before it can make this decision?** That question leads backward to the required evidence and rules, then forward to an observable outcome.

This report preserves the review that informed the separate [Conclusion Driven Development architecture](../reference/ConclusionDrivenDevelopment.md). The proposed concepts below describe an expansion of the approach; they do not claim that all of these capabilities are implemented.

## Proposed definition

Conclusion-driven development starts with a question an agent needs answered to pursue an intention. Each conclusion has a defined meaning, supporting facts, applicable situation, and conditions under which it becomes invalid. Rules derive the conclusion from evidence. Other conclusions or automation consume it. Observations from acting supply evidence for the next decision.

Development proceeds backward from the required conclusion to its dependencies. Acceptance proceeds forward from asserted facts through inference to the resulting behavior.

This separates three concerns:

- **Intention:** What outcome is the agent pursuing?
- **Knowledge:** What does the available evidence support?
- **Action:** What can the agent reasonably do next?

A route demonstrates why these distinctions matter. Knowing a path exists does not establish that the character can traverse it, or that traveling there serves its current goal.

## What the components establish

| Conclusion | What it establishes | What remains separate |
| --- | --- | --- |
| `som-optimal-area` | An explored area selected by the level-range ranking. | Travel feasibility or measured leveling effectiveness. |
| `som-command-for-goal` | Allowed known commands in the category associated with a goal. | Which command produces the desired effect now. |
| `som-route-exits` | A path through the known room graph, selected by exit order. | Shortest path, traversability, or permission to execute. |
| `som-licensed-directive` | The level policy's selected directive. | Successful execution or achieved progress. |

A conclusion promises exactly what its evidence and rules establish.

For example, [Som-Area-Choice.km](../../src/resources/som-component-library/area/Som-Area-Choice.km) describes `som-optimal-area` as the area that shortens the time to the next level. Its rule compares level ranges; it does not evaluate travel time, opponent availability, deaths, or experience gained per minute. The selection can be useful, but its specification should identify it as a heuristic rather than an established optimum.

## Composition that expresses intention

The README states that exploration attempts do not consume `som-optimal-area`. Routing separately connects room instances. The components therefore supply building blocks without yet establishing the complete conclusion:

> This destination serves my goal, I know how to reach it, and this is the appropriate next step.

The next useful chain connects these questions:

1. Which destination serves the active goal?
2. Which known route connects the current location to that destination?
3. Can the character perform the next transition under current conditions?
4. Which action is licensed now?
5. Did the observed outcome match the expected result?

This requires an explicit connection between an area and its destination rooms or entrances. An area name alone cannot supply the room identity that `Som-Route` needs.

Destination selection explains why a place serves the goal. Routing explains how the known graph connects to it. A further conclusion determines whether the next transition is currently feasible. Observations after execution update the evidence for all three.

## Contracts for conclusions

Each public conclusion should have a small, repeatable contract:

| Contract element | Question it answers |
| --- | --- |
| Question and meaning | What precisely does this conclusion establish? |
| Consumer | Which decision or later conclusion needs it? |
| Evidence | Which asserted facts and derived conclusions support it? |
| Scope | For which subject, situation, and observation state does it hold? |
| Selection policy | How are multiple valid answers ranked? |
| Absence | What does an empty answer mean? |
| Invalidation | Which changes require reconsideration? |
| Verification | Which examples demonstrate the promise and its limits? |

For [Som-Route.km](../../src/resources/som-component-library/route/Som-Route.km), the implementation already supplies several parts: room endpoints, a player's explored graph, exit-order preference, door flags, and a distinct empty sequence for an identical start and destination. These belong together in its contract.

Two distinctions need particular care:

- **No known route is not proof that no route exists.** An unexplored connection, missing endpoint, disconnected known graph, and search failure should not silently become the same belief. A negative conclusion needs an explicit boundary, such as no path in this explored graph.
- **A route is conditional knowledge.** Closed or locked exits remain in the returned path. Door flags describe requirements; they do not establish that the character knows the command, possesses a key, or can perform the transition.

## Evidence acquisition and feedback

Dynamic behavior needs conclusions that identify what the agent must learn next. A suitable destination with no known route can justify investigating an unexplored exit. A route requiring an unlock can expose missing knowledge about the required key.

These are productive results. Missing knowledge can lead to investigation rather than an indefinite yield or an unjustified movement command.

Execution then supplies new evidence:

1. Conclude that a transition is feasible.
2. Attempt one action.
3. Observe whether the expected transition occurred.
4. Update the relevant facts.
5. Reconsider the remaining route.

Arrival must be established from observation. Sending the final direction is insufficient evidence.

## Development and acceptance

A practical development sequence is:

1. State the question and its intended consumer.
2. Write examples of supported, unsupported, and ambiguous answers.
3. Define the conclusion contract.
4. Identify existing conclusions it can reuse.
5. Add the missing facts and inference rules.
6. Test changed evidence and interactions with other chains.
7. Connect the consumer and verify the resulting feedback cycle.

For routing, acceptance examples should cover identical endpoints, disconnected rooms, directed exits, cycles, multiple paths, door requirements, graph changes, player isolation, and failed movement followed by reconsideration. Recursive chains need an explicit termination policy; conclusions do not always form a linear sequence.

The existing folder organization is useful as an ownership boundary. Each folder should own a coherent body of reasoning and its public conclusions. Cross-folder dependencies should reuse those conclusions rather than duplicate facts or policy.

The general specification should make meaning, evidence, scope, reconsideration, and observable consequences the units of development. Those contracts provide a concrete standard for deciding whether a component enables purposeful behavior.

## Review scope

This was a document and source review of the component architecture README, the area, command, route, and situation components, and the relevant routing tests. It did not execute a new behavioral test run. Its purpose was to expand the development concept rather than certify routing correctness or implement new components.
