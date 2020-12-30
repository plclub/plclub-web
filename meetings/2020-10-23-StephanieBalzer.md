---
title: "Petr4: Formal Foundations for P4 Data Planes"
speaker: "Nate Foster"
semester: "FA20"
---

Abstract:

Shared session types generalize the Curry-Howard correspondence between intuitionistic linear logic and the session-typed pi-calculus with adjoint modalities that mediate between linear and shared session types, giving rise to a programming model where shared channels must be used according to an acquire-release discipline.  The resulting language recovers the expressiveness of the untyped asynchronous pi-calculus and accommodates practical programming scenarios, such as shared servers, file systems etc.  The resulting language is implemented as a prototype in C0 (a safe subset for C used to teach freshmen at CMU) and as a DSL in Rust [1].

The generalization, however, comes at the cost of deadlock-freedom, a property which holds for the purely linear fragment.  In this talk, I report on recent work that makes up for this deficiency and introduces a type system of linear and shared session types in which the adjoint modalities are complemented with possible worlds to rule out cyclic dependencies between acquires and synchronizations.  I distill the key abstractions to reason about cyclic dependencies and the key invariants enforced by the type system to guarantee deadlock-freedom.  Time permitted, I report on ongoing work that also uses possible world modalities for type-based verification of program properties of interest.

Homework:

Please see attached file.

Bio:

Stephanie Balzer is a research faculty in the Principles of Programming group in the Computer Science Department at Carnegie Mellon University.  Stephanie obtained her PhD from ETH Zurich under the supervision of Thomas R. Gross. In her PhD work, Stephanie developed the sequential relationship-based programming language Rumer and an invariant-based verification technique for Rumer.  Stephanie’s current work focuses on the development of type systems and logics for verifying properties of concurrent programs.

References:

[1] https://github.com/maybevoid/ferrite
