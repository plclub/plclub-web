---
title: "Formalizing syntax-independent syntax theory with monads and Tealeaves"
speaker: "Lawrence Dunn"
semester: "SP21"
---

Abstract:
Formal reasoning about syntax with variable binding is difficult. More importantly it is difficult to reuse, chiefly because it is unclear how to formalize this reasoning except in terms of a specific grammar, and definitions and proofs specific to one grammar are not easily usable for another one. We describe decorated traversable monads (DTMs), an abstraction we suggest captures the essence of syntax with variable binding; and Tealeaves, a work-in-progress Coq library for formal syntax theory that represents syntax as an arbitrary DTM. Tealeaves can be used to implement and reason about variable representations (like named variables and de Bruijn indices, though we have not implemented these examples) independently of a concrete grammar. Such implementations form Tealeaves backends and provide definitions and proofs specific to the representation of variables but polymorphically in the DTM, hence in the underlying syntax. To use these backends, a user only needs to provide the DTM structure of their syntax as a typeclass instance, which we believe is easy to synthesize from a typical BNF grammar annotated with information about binders.

This talk will examine the DTM structure of the syntax of simply-typed lambda calculus (STLC). We demonstrate how to use this to instantiate our first finished backend, locally nameless variables, over STLC. The exact range of possible backends is not yet clear, though it is clear we can handle de Bruijn indices and levels as well. We will conclude by examining whether Tealeaves can be used to reason about alpha convertibility by using traversals to define (something resembling) logical relations over syntax.

Homework:
If you are not familiar with the use of monads in functional programming, please read this blog post http://blog.sigfpe.com/2006/08/you-could-have-invented-monads-and.html
If you are somewhat familiar with monads or just feel ambitious, try completing some of the exercises in the attached document. Answers can be found at the end.
Github repo in case I need to amend something: https://github.com/dunnl/dtm-exercises
