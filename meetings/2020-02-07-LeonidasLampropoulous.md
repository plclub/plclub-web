---
title: "Software Correctness at Scale through Testing and Verification "
speaker: "Leonidas Lampropoulous"
semester: "SP20"
---

Software correctness is becoming an increasingly important concern as our society
grows more and more reliant on computer systems. Even the simplest of software
errors can have devastating financial or security implications. How can we find errors
in real-world applications?  How can we guarantee that such errors don't exist?  To
even begin to answer these questions we need a specification: a description of what
it means for a piece of code to be correct, stated either explicitly (e.g. my private data
are never leaked to third parties) or implicitly (e.g. this code will not terminate with an
uncaught exception).

In this talk, I will discuss efficient ways to debug and reason about software and
specifications, focusing on two techniques and their interplay: property-based
testing and mechanized formal verification. Testing can quickly uncover errors
in complex software, but it cannot guarantee their absence.  Formal verification
provides strong correctness guarantees, but is still very expensive in time and effort. 
Together, they are a match made in heaven.
