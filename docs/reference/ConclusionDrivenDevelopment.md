# Conclusion Driven Development

Status: Architectural foundation for a future general specification.

## Purpose

Conclusion-Driven Development is a software engineering methodology in which evidence-supported conclusions, their semantic contracts and their dependencies constitute the primary abstractions through which reasoning-intensive systems are designed, composed, verified and maintained.

Development starts with a required conclusion, works backward to the evidence and reasoning that support it, and verifies the resulting behavior forward from evidence to outcome.

A conclusion is an answer supported by evidence under stated rules and conditions. It may inform another conclusion, a human decision, or automation. This approach applies to systems that reason about changing conditions, regardless of language, inference engine, or application domain.

## Architectural model

The architecture separates five responsibilities:

| Responsibility | Meaning |
| --- | --- |
| Intention | The desired outcome and the constraints governing its pursuit. |
| Evidence | Observations, assertions, and assumptions available in a defined context. |
| Reasoning | Rules that derive conclusions from evidence and other conclusions. |
| Decision and execution | Selection and performance of an action consistent with the intention and supported conclusions. |
| Observation | Evidence of what happened, including success, refusal, failure, or changed conditions. |

An intention determines which questions matter. Evidence supports answers. Conclusions inform decisions. Execution changes the world, and observation supplies evidence for reconsideration. Systems that only advise may end the cycle at a human decision.

A conclusion about what is known, a conclusion about what is feasible, and a decision about what should happen have distinct meanings. A known plan can have unmet prerequisites. A feasible action can still be unsuitable for the current intention. Issuing an action does not establish that its intended outcome occurred.

## Conclusion contracts

Each public conclusion has a contract that defines its meaning and limits. The representation may vary by implementation, but the contract answers these questions:

| Element | Required definition |
| --- | --- |
| Question and answer | What question is answered, and what does the answer establish? |
| Consumer | Which decision or dependent conclusion needs the answer? |
| Evidence and assumptions | Which inputs support the answer, and which assumptions qualify it? |
| Context | To which subject, situation, time, or state does the answer apply? |
| Selection | How are competing answers ranked, combined, or left unresolved? |
| Absence and uncertainty | What do missing, incomplete, conflicting, and negative results mean? |
| Validity | Which changes require the answer and its dependents to be reconsidered? |
| Verification | Which examples demonstrate the contract and its limits? |

The strength of a conclusion must match its support. A heuristic preference does not establish an optimum without a defined objective and sufficient evidence. Failure to find an answer does not establish that no answer exists unless the relevant search space is complete and the search is adequate.

The system must distinguish a supported answer from insufficient evidence, conflicting evidence, and an incomplete evaluation. An empty collection can be a valid answer; it must not silently acquire the meaning of failure or uncertainty.

## Composition and ownership

A reasoning component owns a coherent set of conclusions and the rules that derive them. Other components consume those conclusions through their contracts. Evidence has an identified owner and source; composition does not require duplicating facts or reimplementing another component's reasoning.

Dependencies form a graph. A conclusion may support several consumers, and several conclusions may support one decision. Recursive reasoning requires a defined termination strategy and a way to report incomplete evaluation. A fixed linear pipeline is not required.

Reasoning determines what the evidence supports. Decision policy determines which supported alternative serves the intention. Execution owns effects and reports observations. These boundaries keep policy explainable and prevent transport or execution details from becoming hidden inference rules.

## Change and feedback

A conclusion is valid within its declared context and assumptions. Changes to evidence, goals, constraints, or reasoning policy can require reconsideration. Cached answers must follow a defined invalidation strategy, including dependent conclusions. Context separation and cache invalidation are separate responsibilities.

Insufficient evidence can support a decision to investigate. The system identifies the missing observation and, when appropriate, selects an action that obtains it. Unknown conditions therefore become explicit questions rather than unsupported beliefs.

After acting, the system compares observed outcomes with expected outcomes. A refusal, unexpected result, or unmet prerequisite updates the relevant evidence and prompts reconsideration. Repeated attempts require a reason to expect a different outcome. Completion is established through an appropriate observation or authoritative acknowledgment.

## Development method

1. State the intention and the decision that needs support.
2. Name the conclusion required by that decision and define its contract.
3. Write examples of supported, absent, uncertain, and conflicting answers.
4. Work backward through dependencies, reusing existing conclusion contracts.
5. Implement the missing evidence representations and reasoning rules.
6. Verify conclusions, composition, and behavior under changing evidence.
7. Connect consumers and verify observation and reconsideration after execution.

Acceptance covers both individual conclusions and sequences of decisions. Relevant cases include alternative answers, missing evidence, failed prerequisites, changed constraints, recursive dependencies, context isolation, stale results, and unsuccessful actions.

A consumer should be able to explain which intention a decision serves, which conclusions support it, and what new evidence would change it. Use existing provenance and explanation facilities where available.

## Path to a general specification

A future specification should formalize conclusion outcomes, provenance, context identity, validity and dependency tracking, conflict handling, recursive evaluation limits, and conformance examples. These are semantic contracts; this architecture does not prescribe one storage model, type system, rule syntax, or execution framework.

