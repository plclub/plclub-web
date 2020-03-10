---
title: R E S P E C T : Find Out What It Means To The Coq Standard Library
author: Lucas Silver
---
In informal mathematics rewriting is so ubiquitous that it is not really even explicitly taught. We do it all the time without bothering to justify it. However, in a formal logical system like Coq, we cannot do anything without justification. In order to justify something, we must first understand what it is. Suppose, we have some relation $R$, two values $x,y$ such that $(x,y) \in R$  Luckily, the Coq's `rewrite` tactic can make providing this justification easier. 


The `rewrite` tactic can be used for rewriting arbitrary relations



```coq
Goal forall (a b c d : nat), a = b -> b = c -> c = d -> a = d.
Proof.
  intros a b c d Hab Hbc Hcd. rewrite Hab. rewrite Hbc. auto.
Qed.
```
