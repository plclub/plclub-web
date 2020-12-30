---
title: "The Simple Essence of Algebraic Subtyping"
speaker: "Nick Rioux"
semester: "FA20"
---
Abstract
For quite some time, incorporating subtyping into languages using Hindley-Milner type inference has posed a thorny problem. Ideally, a type inference algorithm would be complete and calculate compact principal types. Until recently, type systems and inference algorithms supporting subtyping and polymorphism have had to compromise on one of these goals.

In his thesis Algebraic Subtyping, Stephen Dolan designed MLSub, an ML-style language with global type inference supporting polymorphism, subtyping, and compact principal types. But the design was complicated: it seemed to require intersection/union types and a stratified syntax of types, and its type inference algorithm was unorthodox.

This talk will be focused on this year's ICFP paper, The Simple Essence of Algebraic Subtyping. In this functional pearl, Lionel Parreaux describes a reformulation of Algebraic Subtyping which shows many of the complexities of MLSub are inessential and uses a type inference algorithm very close to Milner's algorithm W.


Homework
TAPL Chapter 22, Type Reconstruction
