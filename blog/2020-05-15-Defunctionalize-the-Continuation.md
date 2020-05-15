---
title: Defunctionalize the Continuation
author: Li-yao Xia
withtoc: true
tags: haskell
description: Using defunctionalization to emulate higher-order functions using first-order language features
---

This post details a little example of refactoring a program using
*defunctionalization*.

## Defunctionalization

Defunctionalization is a programming technique that emulates higher-order functions
using only first-order language features.

A higher-order function (HOF) can be defunctionalized in two steps:

1. for every location where the HOF is used and applied to a function, replace
   that function with a value of a dedicated data type to *represent* that
   function---we call this a "defunctionalization symbol"; and
2. in the HOF's definition, wherever a function parameter is applied,
   replace that application with a call to a dedicated first-order function
   which will *interpret* the defunctionalization symbol that this parameter
   now stands for---this function is often called `apply`, sometimes `eval`.

For a more fulfilling introduction, check out [*The best refactoring you've
never heard of*][tbrynho], by James Koppel;
the title of this post comes from that talk.
We are about to see another example of that refactoring technique.

Defunctionalization makes functional programming ideas---from a world where
higher-order functions are the norm---applicable even in first-order
languages.
However, defunctionalization also has a lot of value in languages that
already have higher-order functions, *i.e.*, functional languages.
This is what we wish to demonstrate.

## The Problem

Here is the well-known `sum` function which computes the sum of a list of numbers.
The code is in Haskell for concreteness, but this could be written in pretty
much any programming language.

```haskell
sum :: [Int] -> Int
sum []       = 0
sum (x : xs) = x + sum xs
```

This is a basic example of a recursive function that also illustrates
one of their common pitfalls.

If we evaluate it, say, on a list `1 : 2 : 3 : []`, we can see two distinct
phases in the computation:
first, the recursive calls are unfolded, and only after all of that unfolding
do we start adding the numbers in the list, starting from the end.
Hence, during the first phase, the function `sum` will consume
additional space that grows linearly with the length of the input list.

```haskell
  sum (1 : 2 : 3 : [])
= 1 + sum (2 : 3 : [])
= 1 + (2 + (sum (3 : [])))
= 1 + (2 + (3 + sum []))
= 1 + (2 + (3 + 0))         -- end of the first phase
= 1 + (2 + 3)
= 1 + 5
= 6
```

As you might already be aware, the solution is to rewrite the `sum`
function to be tail-recursive. This is a common technique to allow functional
programs to compile down to efficient machine code, as efficient as a
regular loop in imperative programming.

In fact, this simple transformation can be decomposed into two even more
elementary and (at least partially) mechanical steps.
We will illustrate them using the very small example of `sum`, but the
underlying ideas are readily applicable to bigger refactoring and
optimization problems.

If we really only cared about making the function tail-recursive,
we might do so in a fully mechanical manner:

1. Rewrite the function in continuation-passing style (CPS).

As we will soon see, tail recursion alone is technically not sufficient to
make `sum` run more efficiently. Another transformation is necessary.
What makes CPS valuable is that it enables further code transformations.

The rest of this post is going to illustrate that defunctionalization
provides a reasonable second step:

2. Defunctionalize the continuation.

### On problem-solving

In general, problems have solutions made up of two kinds of ideas:
"standard strategies" are general methods to decompose problems, and "creative
tactics" are domain-specific insights to push a solution to completion.

The two steps presented here thus constitute a "standard strategy" to make
functions tail-recursive---and efficient. As we will soon see, only the second
step calls for "creative tactics" (using knowledge specific to "adding numbers").

---

As a reminder, here is the `sum` function again:

```haskell
-- Reminder
sum :: [Int] -> Int
sum []       = 0
sum (x : xs) = x + sum xs
```

## Continuation-passing style

This first step is entirely mechanical, and those familiar with it are free to
skip this section. The following explanation is geared to those who are new to
the idea of continuation-passing style.

Instead of producing the *result* directly, we construct a *function* whose
parameter `k` is to be called with the result. `k` is commonly named
"continuation", because it stands for what the "rest of the world" is going to
do with the result of our function.[^world]

[^world]: "The rest of the world" may sound grand and daunting.
  The idea of continuations turns out to be fittingly grand and daunting.

We can already give the type of the transformed function, where
a continuation has type `Int -> r` for an abstract type parameter `r`.
The only way for the function to terminate is to call the continuation:

```haskell
sum' :: [Int] -> (Int -> r) -> r
```

In the base case `[]`, of course, we call the continuation to return[^return]
the known result `0`:

[^return]: `return` is another cute way to name a continuation.

```haskell
sum' [] k = k 0
```

In the inductive step `(x : xs)`, we first compute the sum of the tail `xs`
recursively, via `sum' xs`. Now that we're in CPS, `sum' xs` is not
literally the sum of `xs`: it is another function expecting a continuation.
This continuation is defined here as a lambda: provided a result `y`,
adding `x` to it yields the result we expect from `sum' (x : xs)`,
so we pass that to its own continuation `k`:

```haskell
sum' (x : xs) k = sum' xs (\y -> k (x + y))
```

To use the "rest of the world" analogy again,
the expression `k (x + y)` is how we tell the rest of the world that the result
is `x + y`. Moreover, from the perspective of the recursive call `sum' xs`,
what the surrounding call `sum' (x : xs)` wants to do (add `x` to the result)
is also part of "the rest of the world", so it makes sense that this logic goes
into the continuation of `sum' xs`.

Put those three lines together:

```haskell
sum' :: [Int] -> (Int -> r) -> r
sum' []       k = k 0
sum' (x : xs) k = sum' xs (\y -> k (x + y))
```

In continuation-passing style, all function calls are *tail calls*:
when the recursive call `sum' xs ...` returns (some value of type `r`),
it can return directly to the caller of `sum' (x : xs) k`.
Thanks to that, [tail calls][tc] can be compiled to efficient code,
which is one of the reasons that make continuation-passing style valuable,
for both compiling and programming.

[tc]: https://en.wikipedia.org/wiki/Tail_call

## Defunctionalize the continuation

This second step cannot be fully automated: we will need to think creatively in
order to simplify the structure of the continuation as much as possible.

We've just rewritten the original and naive `sum` function into `sum'` by
CPS transformation. Let's take a look at how `sum'` evaluates on an example.
At every step, `sum'` adds the next element of the list (its first argument) to
the continuation (its second argument):

```haskell
  sum' (1 : 2 : 3 : []) k0
= sum'     (2 : 3 : []) (\y -> k0 (1 + y))
= sum'         (3 : []) (\y -> k0 (1 + (2 + y)))
= sum'              []  (\y -> k0 (1 + (2 + (3 + y))))
= k0 (1 + (2 + (3 + 0)))
= k0 6
```

Evaluation still blows up by spelling out the whole sum in the continuation.
That's how we can tell that we are not done yet, and further effort is
necessary.

But notice also that the continuation always takes the same form at every step:

```haskell
(\y -> k0 (1 + y))
(\y -> k0 (1 + (2 + y)))
(\y -> k0 (1 + (2 + (3 + y))))
```

Now, these continuations can be simplified:

```haskell
(\y -> k0 (1 + y))
(\y -> k0 (3 + y))
(\y -> k0 (6 + y))
```

In other words, the continuations actually used by this program really consist
only of:

1. an initial continuation `k0`;
2. an integer `n` to add to the final result `y`.

The continuation `k0` is fixed throughout one top-level invocation of `sum'`,
so we will treat it as a global constant from the point of view of `sum'`.

That leaves the integer `n`, which is really the only data needed to describe
each continuation that occurs during the evaluation of `sum'`.

*Defunctionalization* replaces continuations by the corresponding integers.
Skipping some details in the transformation, where we manage to remove any
reference to `k0`, we are left with the following:

```haskell
sum_ :: [Int] -> Int -> Int
sum_ []       n = apply n 0
sum_ (x : xs) n = sum_ xs (n + x)

apply :: Int -> Int -> Int
apply n y = n + y
```

Even though the initial continuation `k0` disappeared, `n` still stands for
some sort of continuation; in that sense, `sum_` is still in CPS and we didn't
actually undo the previous step.

### Side-by-side comparison

If we look carefully enough, `sum'` and `sum_` should really appear as
the same thing "modulo defunctionalization".
For comparison, here is `sum'` again:

```haskell
-- Reminder
sum' :: [Int] -> (Int -> r) -> r
sum' []       k = k 0
sum' (x : xs) k = sum' xs (\y -> k (x + y))
```

Where we had a continuation `k` in `sum'`, we now have a number `n` to
represent it in `sum_`, assuming that `k` has the form `\y -> k0 (n + y)`.

Where we had an application `k 0` in `sum'`, we now have `apply n 0` in `sum_`.
The function `apply` is defined so that `k` is equal to
`\y -> k0 (apply n y)`, or equivalently, `k0 . apply n`,
so `apply = (+)`.
Technically, if we wanted to replace `k 0` with something literally equal,
we would write `k0 (apply n 0)`, but we secretly dropped `k0` at some point
in the (skipped) derivation of `sum_`.
Even so, `apply` formally relates `n` to the `k` it defunctionalizes.

Where we had a continuation `\y -> k (x + y)` in the second case of `sum'`,
we now have `(n + x)` in `sum_`. They are also related by `apply`:
the continuation `\y -> k (x + y)` is equal to `k0 . apply (n + x)`,
under the assumption that `k` is equal to `k0 . apply n`.

### Finishing touch

All that remains is to clean up `sum_` in the base case:
inline `apply` and simplify `n + 0` to `n`.
We obtain the final version, the optimized `sum''`:

```haskell
sum'' :: [Int] -> Int -> Int
sum'' []       n = n
sum'' (x : xs) n = sum'' xs (n + x)
```

Nice and tidy.

```haskell
  sum'' (1 : 2 : 3 : []) 0
= sum''     (2 : 3 : []) 1
= sum''         (3 : []) 3
= sum''              []  6
= 6
```

*Exercises for the reader*:

1. Some facts about arithmetic are crucial to allow this optimization to take
   place. Where were they used above?

2. What would happen if `sum'` were defunctionalized naively,
   without simplifying the continuation beforehand?

## Continuations as evaluation contexts

A fair question to ask is whether all of this is not a bit indirect.
Indeed, to go from the naive `sum` to the tail-recursive `sum''`,
CPS is not necessarily the first solution that comes to mind.
A more direct way to think about the problem is to look again at how `sum`
evaluates (instead of `sum'`):

```haskell
  sum (1 : 2 : 3 : [])
= 1 + sum (2 : 3 : [])
= 1 + (2 + sum (3 : []))
= 1 + (2 + (3 + sum []))
```

and notice that the *evaluation contexts* around `sum` have a common shape:

```haskell
1 + _
1 + (2 + _)
1 + (2 + (3 + _))
```

It is hopefully evident here that *evaluation contexts* in `sum` play the same
role as *continuations* in `sum'`.
Nevertheless, to go from recognizing the shape of the evaluation context to
coming up with the optimized `sum''`, there remains a small gap.
How do we logically finish the story from this point?

1. We must compress such an evaluation context to a plain number.

2. We must carry explicitly the compressed evaluation context to achieve
   tail recursion.

These two steps correspond exactly to defunctionalization and CPS
transformation, just in the reverse order of what we detailed previously.

It might be that spelling out these remaining steps is more trouble than
necessary for such a trivial example, but it's nice to know that we can, and
that this technique now has a name.

Besides,
"defunctionalize the evaluation context"
doesn't sound nearly as catchy as
"defunctionalize the continuation".

---

## References

- [*The best refactoring you've never heard of*][tbrynho],
  a talk and transcript by James Koppel (2019), where he popularized the phrase
  "defunctionalize the continuation".

- [Slides from a PLClub talk I gave (Google Slides)][slides], with more references at the end.

- [*Defunctionalization at work*](https://www.brics.dk/RS/01/23/),
  by Olivier Danvy and Lasse R. Nielsen (PPDP 2001, extended version),
  with many more examples of defunctionalization of continuations.

[tbrynho]: http://www.pathsensitive.com/2019/07/the-best-refactoring-youve-never-heard.html

[slides]: https://docs.google.com/presentation/d/e/2PACX-1vSmSFQ3BnHOAKi6-ITLj55VdnNb-IZDSCPjM-C1miaavq-Ku9lxqjbtLFBAEQKGHrWmTsQO4asxf-3P/pub?start=false&loop=false&delayms=5000
