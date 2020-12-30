---
title: "Constraint Solving in GHC"
speaker: "Richard Eisenberg"
semester: "FA20"
---

This Friday, I will be presenting work I've been up to recently about constraint solving within GHC. We'll discuss how GHC's type inference engine works (spoiler: it generate constraints and solves them) and then look at a series of illuminating examples of where things get difficult. Along the way, I'll share details about two significant simplifications I've been working on, which should hopefully result in several thousand lines of code deleted but with no change in behavior.

Because many of our challenges will involve Haskell's type families, your homework is a quick review of https://www.microsoft.com/en-us/research/wp-content/uploads/2005/01/at-syns.pdf (Associated Type Synonyms, by Chakravarty, Keller, and Peyton Jones, ICFP'05) through Section 3.1.
