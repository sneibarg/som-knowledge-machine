---
name: km-knowledge-representation
description: >-
  Applies the Knowledge Machine representation rules in docs/userman.pdf and
  docs/situations.pdf when authoring ontology components: classes, slots,
  frames, inheritance, prototypes, constraints, and situations. Use when the
  user runs /km-knowledge-representation or asks to build, author, extend, or
  review a KM ontology, component library, .km component, class, slot, frame,
  or situation.
---

# KM knowledge representation

Read the parts of `docs/userman.pdf` and `docs/situations.pdf` that apply to the component you are changing. Those manuals are the representation rules. Do not copy them into this skill or into a second checklist.

Author the component as Knowledge Machine frames in a `.km` file. Match the declarations already used by the component library you are editing. A situation is the partition of assertions and of the values a query computes. A slot whose values must differ across those partitions is a fluent. A slot whose value is the same in every situation stays a non-fluent.

Leave the interpreter, the taxonomy walker, and the shipped `km-component-library` tree unchanged unless the task asks for that change.
