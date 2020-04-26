---
title: Defunctionalize the continuation
author: Li-yao Xia
---

This post presents a little example of defunctionalization.

This is taken from a PLClub talk I gave recently.[^dejavu]
I wanted to unpack this example in more space than a single slide.

[^dejavu]: See also links in references. I probably saw this `sum` example
  somewhere else originally but I can't remember.

## Defunctionalization

Defunctionalization is a programming technique to emulate higher-order functions
using only first-order language features.

In short:

1. replace all lambdas with unique constructors of a dedicated algebraic
   data type; and
2. replace all function applications with calls to a dedicated first-order
   function---often called `apply`, sometimes `eval`.

For a more fulfilling introduction, check out [*The best refactoring you've
never heard of*][tbrynho], by James Koppel.
The title of this post comes from there;
we are about to see another example of that refactoring technique.

Defunctionalization allows functional programming ideas---from a world where
higher-order functions are the norm---to be applied even in first-order
languages.
However, there's also a lot of room for defunctionalization in languages that
already have higher-order functions, *i.e.*, functional languages.
This is what we wish to demonstrate.

## The Problem

Here is the well-known `sum` function, which computes the sum of a list of numbers.
The code is in Haskell for concreteness, but this could be written in pretty
much any programming language.

```haskell
sum :: [Int] -> Int
sum []       = 0
sum (x : xs) = x + sum xs
```

This is a basic example of a recursive function that also illustrates
one of their common pitfalls.

If we evaluate it, say, on a list `1 : 2 : 3 : []`, we can see the computation
split in two phases:
first the recursive calls are unfolded, and only after that phase
do we start adding the numbers in the list, starting from the end.
That means that during the first phase, the function `sum` will consume
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

As you might already be aware of, the solution is to rewrite the `sum`
function to be tail-recursive. (Oops, spoilers. Too late!)
The goal here is to decompose this simple transformation into two even more
elementary steps.
In choosing such a straightforward example, we can focus on this decomposition
without getting bogged down in domain-specific details. The underlying ideas
are then more readily applicable to attack bigger problems.[^motivation]

[^motivation]: This is clearly not because I can't be bothered to come
  up with a more interesting example.

To make recursive functions run fast, a common advice is thus:

1. Make the function tail-recursive.

We can reword that advice to be more actionable.
In fact, if we take it literally, the above can even be achieved in a fully mechanical
way:

1. Rewrite the function in continuation-passing style (CPS).

But we must still do something more beyond that.
CPS matters because it is a first step to enable further transformations.

The rest of this post is going to illustrate that defunctionalization
provides a reasonable second step:

2. Defunctionalize the continuation.

### On problem-solving

In general, problems have solutions made up of two kinds of ideas:
"standard strategies" are general methods to decompose problems, and "creative
tactics" are domain-specific insights to push a solution to completion.

The two steps presented here thus constitute a "standard strategy" to make
functions tail-recursive---and efficient. As we will soon see, only the second
step calls for "creative tactics" (where the specific domain is "adding
numbers").

---

As a reminder, here is the `sum` function again:

```haskell
-- Reminder
sum :: [Int] -> Int
sum []       = 0
sum (x : xs) = x + sum xs
```

## Continuation-passing style

Those familiar with it are free to skip this section. Therefore, this
explanation is geared to those who are new to the idea of continuation-passing
style.

This first step is entirely mechanical.

Instead of producing the *result* directly, we construct a *function* whose
parameter `k` is to be called with the result. `k` is commonly named
"continuation", because it stands for what the "rest of the world" is going to
do with the result of our function.[^world]

[^world]: "The rest of the world" may sound grand and daunting.
  The idea of continuations turns out to be fittingly grand and daunting.

We can already give the type of the transformed function:

```haskell
sum' :: [Int] -> (Int -> r) -> r
```

In the base case `[]`, of course, we call the continuation to return[^return]
the known result `0`:

[^return]: `return` is another cute way to name a continuation.

```haskell
sum' [] k = k 0
```

In the inductive step `(x : xs)`, we must compute the sum of the tail `xs`
recursively, so we write `sum' xs`. Now that we're in CPS, `sum' xs` is not
literally the sum of `xs`: it is another function expecting a continuation,
so we write such a continuation. Provided a result `y`, adding `x` to it yields
the result of `sum' (x : xs)`, which we pass to its own continuation `k`:

```haskell
sum' (x : xs) k = sum' xs (\y -> k (x + y))
```

To use the "rest of the world" analogy again,
the expression `k (x + y)` is how we tell the rest of the world that the result
is `x + y`. Moreover, from the perspective of the recursive call `sum' xs`,
what the surrounding call `sum' (x : xs)` wants to do (add `x` to the result)
is also part of "the rest of the world", so it makes sense that this logic goes
into the continuation.

Put those three lines together:

```haskell
sum' :: [Int] -> (Int -> r) -> r
sum' []       k = k 0
sum' (x : xs) k = sum' xs (\y -> k (x + y))
```

CPS transformation turns recursive functions into tail-recursive functions:
when the recursive call `sum' xs ...` returns (some value of type `r`),
it can return directly to the caller of `sum' (x : xs) k`.

## Defunctionalize the continuation

This second step cannot be fully automated: we will need to think creatively in
order to simplify the structure of the continuation as much as possible.

Let's look at how `sum'` evaluates on an example.
At every step, the continuation grows with the next element of the list:

```haskell
  sum' (1 : 2 : 3 : []) k0
= sum'     (2 : 3 : []) (\y -> k0 (1 + y))
= sum'         (3 : []) (\y -> k0 (1 + (2 + y)))
= sum'              []  (\y -> k0 (1 + (2 + (3 + y))))
= k0 (1 + (2 + (3 + 0)))
= k0 6
```

Evaluation still blows up by spelling out the whole sum,
which is how we can tell that we are not done yet:

```haskell
1 + (2 + (3 + 0))
```

But notice also that the continuation always takes the same form at every step:

```haskell
(\y -> k0 (1 + y))
(\y -> k0 (1 + (2 + y)))
(\y -> k0 (1 + (2 + (3 + y))))
```

Now, using properties of addition (associativity),
they can be simplified:

```haskell
(\y -> k0 (1 + y))
(\y -> k0 (3 + y))
(\y -> k0 (6 + y))
```

In other words, the continuation really consists only of:

1. the initial continuation `k0` which comes from "outside";
2. an integer `n` to add to the final result `y`.

From now on, we will assume that continuations `k` have the form
`\y -> k0 (n + y)` for some integer `n`.

Defunctionalization then replaces the continuation by that integer.
We don't need to also keep the initial continuation `k0` around:
we can ask for it later, in the `apply` function.
With that change, it turns out we can drop all references to `k0` and the
continuation type parameter `r`.
Skipping those details, we are left with the following:

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

If we look carefully enough, `sum'` and `sum_` should really appear as
the same thing "modulo defunctionalization".
For comparison, here is `sum'` again:

```haskell
-- Reminder
sum' :: [Int] -> (Int -> r) -> r
sum' []       k = k 0
sum' (x : xs) k = sum' xs (\y -> k (x + y))
```

Where we had a continuation `k` in `sum'`, we now have `n` in `sum_`,
assuming that `k` has the form `\y -> k0 (n + y)`.

Where we had an application `k 0` in `sum'`, we now have `apply n 0` in `sum_`.
The function `apply` is defined so that `k` is equal to
`\y -> k0 (apply n y)`, or equivalently, `k0 . apply n`.
Technically, if we wanted to replace `k 0` with something literally equal,
we would write `k0 (apply n 0)`, but we secretly dropped `k0` at some point
in the (skipped) derivation of `sum_`.
Thus, `n` is related to the `k` it defunctionalizes by `apply`,
which is equal to `(+)`.

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
CPS is not necessarily the first thing that comes to mind.
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
role as *continuations* in `sum'`
Nevertheless, to go from recognizing the shape of the evaluation context to
coming up with the optimized `sum''`, there remains a small gap.
How do we actually finish the story from this point?

1. We must compress such an evaluation context to a plain number.

2. We must carry explicitly the compressed evaluation context to achieve
   tail-recursion.

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

- [Slides from the PLClub talk (Google Slides)][slides], with more references at the end.

- [*The best refactoring you've never heard of*][tbrynho],
  a talk and transcript by James Koppel (2019), where he popularized the phrase
  "defunctionalize the continuation".

- [*Defunctionalization at work*](https://www.brics.dk/RS/01/23/),
  by Olivier Danvy and Lasse R. Nielsen (PPDP 2001, extended version),
  with many more examples of defunctionalization of continuations.

[tbrynho]: http://www.pathsensitive.com/2019/07/the-best-refactoring-youve-never-heard.html

[slides]: https://docs.google.com/presentation/d/e/2PACX-1vSmSFQ3BnHOAKi6-ITLj55VdnNb-IZDSCPjM-C1miaavq-Ku9lxqjbtLFBAEQKGHrWmTsQO4asxf-3P/pub?start=false&loop=false&delayms=5000
