---
title: "Combining Deep and Shallow Embedding for Domain-Specific Languages"
speaker: "Hengchu Zhang"
semester: "SP20"
---

This week I am presenting a versatile language embedding technique from the paper Combining Deep and Shallow Embedding for Domain-Specific Languages.

We will study how this technique provides both a shallow embedding that borrows Haskell's syntax and datatypes for programming a DSL, and a deep representation that allows us to perform program analysis on the resulting code of the DSL. Furthermore, we will see how this embedding technique allows us to embed both pure and effectful computations.

As a concrete example, I will present a toy DSL implemented using this technique, and I will demonstrate an implementation of symbolic evaluation that detects program crashes in our toy DSL.

Finally, we will venture outside the norm a bit, and see how Haskell's laziness allows us to represent recursive programs with infinite syntax trees, and discuss how infinite syntax trees affect the symbolic execution analysis on our toy DSL.

Your homework is to review Haskell GADTs:
[https://downloads.haskell.org/ghc/8.8.3/docs/html/users_guide/glasgow_exts.html#generalised-algebraic-data-types-gadts](https://downloads.haskell.org/ghc/8.8.3/docs/html/users_guide/glasgow_exts.html#generalised-algebraic-data-types-gadts)

And read the first 2 sections of the linked paper: Introduction, and Shallow and Deep --- Pros and Cons.
