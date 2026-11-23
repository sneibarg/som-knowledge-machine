# Springs of MUD component architecture

These notes describe the components in `src/resources/som-component-library`. How to load the directory and how to ask one question are in the [library README](../../../src/resources/som-component-library/README.md).

- [Vocabulary](vocabulary.md) lists the classes, the relations, and the slots the caller asserts.
- [Objects](objects.md) names every class, relation, inverse, conclusion, helper, and `*-rule` slot.
- [Reasoning](reasoning.md) lists pace, the notch, and the hunt rules that license a directive.

The caller owns the clock. Each query is one score, one death, or one view. The returned knowledge base holds that answer. The next event asserts a fresh projection with the notch, cooldown, and counters the caller stored.
