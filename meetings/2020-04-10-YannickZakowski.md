---
title: "A Foretaste of Vellvm 2"
speaker: "Yannick Zakowski"
semester: "SP20"
---

As most of you know, there has been some work on a new version of Vellvm going on for quite some time, involving around Steve several people of this very club.
This Friday, I would like to take the opportunity to paint an overview of what this work has been consisting of and where it is going.
To this end, I will try to give a quick introduction to the wonders of verified compilers, and to the Vellvm project in particular.
I'll then try to motivate the rationals behind a complete rework of the semantics of Vellvm, compared to its first iteration. This will lead us to paint a bird-eyed view of the structure of the new project, and of its semantics in particular.
Finally, we will take a more technical focus on three semantic peculiarities that led us to work on ongoing extensions of itrees.

In lieu of homework, I would suggest the following:

* Take a quick peak at the specification of the language we are formalizing, just to give you a sense of what we are working with: [https://llvm.org/docs/LangRef.html](https://llvm.org/docs/LangRef.html)
* Read at least the introduction of the original Vellvm paper (back in 2012): [https://www.cis.upenn.edu/~stevez/papers/ZNMZ12.pdf](https://www.cis.upenn.edu/~stevez/papers/ZNMZ12.pdf)
* (optional a.) If you are already familiar with itrees, you may refresh your memory of Section 5, and in particular of the denotation of the [asm] language described in this Section: [https://www.cis.upenn.edu/~stevez/papers/XZHH+20.pdf](https://www.cis.upenn.edu/~stevez/papers/XZHH+20.pdf)
* (optional b.) If you are not yet familiar with itrees, but willing to, reading as much as you would like of the corresponding paper would help: [https://www.cis.upenn.edu/~stevez/papers/XZHH+20.pdf](https://www.cis.upenn.edu/~stevez/papers/XZHH+20.pdf)
* (optional?)    If you find a clever, better name than Vellvm 2 for this project, I offer a beer as soon as logistically possible!
