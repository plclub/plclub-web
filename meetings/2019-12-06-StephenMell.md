---
title: "Enforcing Convex I/O Constraints on Differentiable Models"
speaker: "Stephen Mell"
---

We present an approach for designing correct-by-construction neural networks (and other machine learning models) that are guaranteed to be consistent with a collection of input-output specifications before, during, and after algorithm training. Our method involves designing a constrained predictor for each set of compatible constraints, and combining them safely via a convex combination of their predictions. We demonstrate our approach on synthetic datasets and an aircraft collision avoidance problem.