---
title: "Typing Gödel pt 1: Typing Logic"
speaker: "Lawrence Dunn"
semester: "SP20"
---

At this Friday's talk, we will reach new levels of clarity in logical matters by using Coq as a metalogic. We will think of a logic as a guest within its host, Coq, consisting of a few parts: Two inductive types called "proposition" and "proof," plus a semantics which translates guest-level "propositions" into actual (i.e. Coq-level) propositions. Finally, a soundness theorem maps "proofs" to proofs, showing that a logic defines a kind of sublogic of Coq.

This mindset is a stepping stone towards solving the "paradoxes" arising from too naïve a statement of Gödel's theorems: If there is a sentence of Peano arithmetic that is true but unprovable, how can we prove it's true? Wait, no---doesn't it follow from Gödel's completeness theorem that all valid statements of first order Peano arithmetic are provable? (Yes it does.) So do Gödel's completeness and incompleteness theorems contradict each other? (No they don't.) So the Gödel sentence  of PA is true, unprovable, and invalid, and we can prove this? (Correct, but we'll delay this proof and others for a future talk.)

Don't worry, it's just type theory!

Homework:

[https://github.com/dunnl/dprop/](https://github.com/dunnl/dprop/)

[https://dunnl.github.io/dprop/DProp.Prop.html](https://dunnl.github.io/dprop/DProp.Prop.html)

Please take a look at the Coq file in this Github repo, which implements propositional logic as a "guest" in Coq. Skim the contents and try some exercises. (You probably won't finish everything in 30 minutes, but take a look.) I'll use this file during the talk.

Furthermore it would be helpful if you gently re-acquaint yourself with the syntax of first-order logic. Van Dalen's "Logic and Structure" is a good reference (see the *#logic-reading-group on Slack*). How would you extend the semantics to such a logic?
