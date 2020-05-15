---
title: "A Simple Quantitative Calculus"
speaker: "Pritam Choudhury"
semester: "SP20"
---

The simply typed lambda calculus is a well-studied type system. But it
is resource agnostic, meaning the type system does not track the usage
of variables in terms. What happens if we make the type system resource
aware? We can definitely have distinct function types varying just in
argument usage. How then should we modify our abstraction and
application rules? Further, there may be a natural ordering of the
resources. In such a case, what happens if we allow sub-usaging? Going
forward, how can we generalize this to dependent types? This question is
of considerable interest. It is at the heart of the Granule Project. It
is also being explored in the context of other programming languages
like Haskell.


Homework (Optional) :- Consider the typing rules of the simply typed
lambda calculus. How would you modify them to track resource usage? Do
you need to impose some conditions on the resources? If you have more
time, you can try proving preservation via a suitable substitution
lemma.
