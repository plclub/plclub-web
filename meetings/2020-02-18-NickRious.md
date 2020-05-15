---
title: "Goldilocks and the Three Inference Systems"
speaker: "Nick Rioux"
semester: "SP20"
---

Inductive definitions are a crucial tool that describe sets using least fixed
points. But induction gives us sets that are too small to effectively describe mathematical
objects of infinite size.

Dually, coinductive definitions make use of greatest fixed points to describe
infinite objects and processes. But as we will see, there are many circumstances
in which coinduction yields sets that are too large!

This talk introduces generalized inference systems, which blend the inductive
and coinductive styles to get definitions that are just right. Using "corules"
-- rules which are applicable only at infinite depth depth in a derivation --
one can concisely interpret recursive definitions as fixed points which need be
neither the least nor the greatest. This approach has been applied to address open
problems with big-step operational semantics, enabling an alternative approach
to type soundness proofs.

Homework:

Familiarize yourself with big-step operational semantics and the basics of coinduction.
* Big-step operational semantics: TAPL Chapter 3 Section 5
* Coinduction: TAPL Chapter 21

If you are already familiar with these topics then you can get a head start
by reading sections 1 and 2.1 of "Coaxioms: Flexible Coinductive Definitions by Inference Systems" by Francesco Dagnino.
