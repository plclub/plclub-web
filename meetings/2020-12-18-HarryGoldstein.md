---
title: "Quick Predicate Types"
speaker: "Harrison Goldstein"
semester: "FA20"
---
Abstract
Property-based testing is a powerful tool for gaining confidence that code is correct, but it is often difficult to know exactly which properties one should test. Worse, as code evolves over time, the programmer needs to manually keep track of whether or not their function-level properties still imply whole-program correctness.

This work aims to solve these problems by thinking of tests as types. Our "Quick" Predicate Type system, allows programmers to annotate types with predicates that are tested at compile time. Unlike standard QuickCheck properties, these annotations flow through the program enforcing that implications are checked automatically. While these predicate "types" are technically unsound (unlike in a true refinement type system, e.g. Liquid Haskell), they are extremely expressive and practically useful.

Homework
Make sure you are very familiar with QuickCheck and property-based testing in general.
If you've never heard of QuickCheck:
http://www.cse.chalmers.se/~rjmh/QuickCheck/manual.html
If you want to explore the package: https://hackage.haskell.org/package/QuickCheck
If you want some further reading: https://www.tfp2019.org/resources/tfp2019-how-to-specify-it.pdf
Check out Liquid Haskell, and play around with it using their online demo:
https://ucsd-progsys.github.io/liquidhaskell-blog/
Extra Credit: Try to come up with a relatively simple refinement type that you'd want to check, but that Liquid Haskell can't verify.
