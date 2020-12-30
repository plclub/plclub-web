---
title: "A Separation Logic for Probabilistic Inference"
speaker: "Justin Hsu"
semester: "FA20"
---
ABSTRACT: Probabilistic independence is a useful concept for describing the result of random sampling---a basic operation in all probabilistic languages---and for reasoning about groups of random variables. Nevertheless, existing verification methods handle independence poorly, if at all. We propose a probabilistic separation logic PSL, where separation models probabilistic independence, based on a new, probabilistic model of the logic of bunched implications (BI). The program logic PSL is capable of verifying information-theoretic security of cryptographic constructions for several well-known tasks, including private information retrieval, oblivious transfer, secure multi-party addition, and simple oblivious RAM, while reasoning purely in terms of independence and uniformity. If time permits, we will also discuss ongoing work for reasoning about conditional independence

HOMEWORK:

1. We'll use the following simple definition of probabilistic independence. Two random variables X and Y are independent in a distribution d over X and Y if for all values a and b, we have:

Pr [ X = a and Y = b ] = Pr [ X = a ] * Pr [ Y = b ]

where all probabilities are taken over samples from d.

Check whether X and Y are independent or not at the end of each of the following imperative probabilistic programs. Below, "Z <$ flip" flips a fair coin (true/false with 50/50 probability) and assigns the result to the variable Z.

a) X <$ flip ; Y <$ flip

b) X <$ flip ; Y <- not X

c) X <$ flip; Y <$ flip ; Y <- not Y

Bonus: X <$ flip; Z <$ flip; Y <- X xor Z (exclusive or).

2. Take a look at 3.1 in the paper: https://arxiv.org/pdf/1907.10708.pdf

In the heap model of BI, the set of worlds is the set H of all partial maps from Nat -> Val, and:

h \circ h' is defined to be the union of  iff domain(h) and domain(h') are disjoint. When defined, h \circ h' is the union of heaps h and h'.

h < h' iff domain(h) is a subset of domain(h'), and the partial maps h and h' agree on domain(h).

a) Convince yourself that this data can be turned into a model of BI. (What is the identity?)

b) What other models of BI can you think of?

3. If you have more time or curiosity, take a quick look at 3.2. (You may need some notation from 2.1 and 2.2.)
