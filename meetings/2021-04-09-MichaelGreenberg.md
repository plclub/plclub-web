---
title: "JankyScript: turning X2JS into X2WASM"
speaker: "Michael Greenberg"
semester: "SP21"
---
Abstract: Once you have js_of_ocaml and bucklescript, it's hard to
justify writing wasm_of_ocaml, too... even if it would offer some
performance and sandboxing benefits. We take an existing JS-generating
compiler and translate its output to WASM. Prior work by Manuel Serrano
has already shown that AOT JS compilation is hard if you do a good
job. But what our work presupposes is... what if you _didn't_ do a good
job?

This talk has two parts: an overview of Jankyscript, followed by a deep
dive on gradual typing.

Homework est omnis divisa in partes duas:

- Part I:

  Read Henglein's "Dynamic typing: syntax and proof theory" up to and
  including Section 2.2 (6pp in PDF; 197-202). You should try to
  understand how coercions implement the "type tagging" regime commonly
  found in dynamic languages. Don't spend more than twnety minutes.

  https://www.sciencedirect.com/science/article/pii/0167642394000042

- Part II:

  For each of the following programs, try to come up with a monomorphic
  type where (a) you could insert coercions to get the program to have
  that type, and (b) your coercions' checks won't introduce any _new_
  errors. Draw your types from this set:

  T ::= bool | int | T1 -> T2 | dyn

  1. (fun f. f true) (fun x. x + 100)

  2. (fun i. (fun a. (i true)) (i 5)) (fun x. x)

  3. (fun b. b (fun c. 5 5) (fun d. 0)) (fun t. fun f. f)

  4. (fun f. (fun y. f) (f 5)) (fun x. 10 + x)

  5. fun f. fun x. x (f x)

  6. fun t. fun x. if t then x + 1 else (if x then 1 else 0)