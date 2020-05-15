---
title: "Reasoning Principles for InteractionTrees"
speaker: "Lucas Silver"
semester: "SP20"
---

Developing denotational semantics and reasoning inference rules for programming
languages are both highly useful, but difficult tasks. Denotational semantics are one way to
reason about compiler correctness, and reasoning inference are useful when you want to
reason about individual programs following specifications. To make things worse, you need to
prove, at the very least, soundness of your reasoning principles with respect to your
denotational semantics.

In this talk, I will discuss how we can derive the type of specifications, as well as reasoning
principles for programming languages with semantics expressed in Interaction Trees. These
specifications are rich enough to reason directly about convergence and divergence behavior.
For example, we can verify that a given program halts on a correct output if its input satisfies
a precondition, and that it diverges if it violates that precondition.
