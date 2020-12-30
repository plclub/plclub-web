---
title: "Datatype Invariants with hs-to-coq"
speaker: "Eric Giovannini"
semester: "FA20"
---
Abstract: Many data structures have invariants that should be maintained, and an important part of program verification is to prove that functions over these datatypes preserve these invariants. The usual workflow for proving properties about Haskell code is to translate the code to Coq and then formulate and prove properties about the translated code. However, manually stating these invariants and writing theorems that the functions preserve the invariants can be tedious, especially if the original Haskell code changes. There is a different approach, in which (1) the datatypes that have invariants are replaced by sigma types that combine a value of the original datatype with a proof that it satisfies the invariant, and (2) the theorems stating that functions preserve invariants (and the corresponding proofs of these theorems) are themselves bundled with the translated code — in fact, each “theorem” is built right into the corresponding function's definition! The idea of the extension I’ve worked on is to facilitate this approach, so that the work of formulating theorems about the preservation of invariants can be largely automated. I hope to make it easier to incorporate theorems about invariants and maintain them as the source code changes. The original motivation for the extension arose from a translation of Haskell’s Containers library.


Plan: I will first give a high-level overview of hs-to-coq, since I don’t expect everyone to be familiar with it. Of particular importance here is the concept of an edit file; these play a major role in the extension I have developed. After discussing invariants and motivating this new extension, I will review some notions from dependent type theory, and then discuss how the extension utilizes sigma types and Coq’s Program mode to “embed" theorems about invariants into function definitions. I’ll then walk through a simple example of the extension in action, and discuss benefits and drawbacks to its approach. If there is time, I may discuss alternate approaches and future work.


Homework:
Read about hs-to-coq. An excellent intro is this PLClub Blog post by Li-yao Xia: https://www.cis.upenn.edu/~plclub/blog/2020-10-09-hs-to-coq/.
Review the notion of a sigma type (a.k.a. dependent pair type).
Review the definition of a red-black tree, as this will be used as an example throughout. (See for example https://doi.org/10.1017/S0956796899003494.)
