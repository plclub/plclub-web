---
title: "R E S P E C T : Find Out What It Means To The Coq Standard Library"
author: Lucas Silver
tags: coq, tutorials
---

This blog post is a companion to the following [code](https://github.com/lag47/Rewrite-Tutorial). Please follow along with that file.

Prerequisites:

* Basic Mathematical Maturity: At least one proof based mathematics course
* Basic Coq Knowledge: at least through `Relations.v` from [Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/toc.html)
* Basic Type Class Knowledge: background from any language should be fine


In informal mathematics rewriting is so ubiquitous that it is not really even explicitly taught. We do it all the time without bothering to justify it. However, in a formal logical system like Coq, we cannot do anything without justification. In order to justify something, we must first understand what it is. 

Suppose, we have some relation `R : A -> A -> Prop`, two values `x y : A` such that `R x y`. We have some context `K`. Our goal is `K[x]` and we would prefer our goal to be `K[y]`. To do this we want to rewrite `x` into `y` under `K`. In order for this to be justified, we need to know that as long as we know `R x y`, we also know that `K[y]` implies `K[x]`. To introduce some other vocabularly, to say `R` is proper with respect to `K` is the same as the previous sentence.

The `=` relation in Coq is strong enough that it is proper under any relation. This means that, if we know `x = y`, then for any ontext `K`, we can transform a goal of `K[x]` into one of `K[y]`


These notions are implemented as type classes in the Coq standard library. We will go over the exact instances we will need to provide later. For now,just keep in mind that Coq has provided a series of tactics that, given certain type class instances, will do all of the justification work for you, and transform your goal for you.

Luckily, the Coq's `rewrite` tactic can make providing this justification easier. 

So let us go through some concrete examples showing the strength of rewriting. Consider the following proposition and proof script


```coq
Goal forall (a b c d : Z), a = b -> b = c -> c = d -> a = d.
Proof.
  intros a b c d Hab Hbc Hcd. rewrite Hab. rewrite Hbc. auto.
Qed.
```

That is essentially just the transitivity property of equality extendend to 4 elements. Note how we prove this using two rewrites instead of two applications of the transitivity property.

Now let's look at a slightly more complicated example. The following proposition is trivially simple if we are given the ability to rewrite.

```coq
Goal forall (a b c x y z : Z), a = x -> b = y -> c = z -> 
                                           a + b + c = x + y + z.
Proof.
  intros a b c x y z Hax Hby Hcz. rewrite Hax. rewrite Hby. rewrite Hcz.
  reflexivity.
Qed.
```

Unlike the previous example, it is not immediately obvious how we would prove this proposition without rewriting. In this case we are rewriting integers under the context of addition.

Now that we've seen what we can do with rewriting in its most flexible and powerful form, let's see how we can recover that for other relations.

Suppose we have an integer `k` and consider modular arithmetic modulo `k`. So our relation will be `x ≡ y` means that `x` is equivalent to `y` mod `k`. The definition given in the file is equivalent to a division based definition and comes for [Bezout coefficients](https://en.wikipedia.org/wiki/B%C3%A9zout%27s_identity). However, this is not really important for our purposes. `≡` is the notation we will be using for the relation, defined in the file as `equiv`.

We can start by showing the `≡` is an equivalence relation and registering that fact as a type class.

```coq
Instance equiv_equiv : Equivalence equiv.
Proof.
  ...
Qed.
```

The proof is unrelated to the subject of this post, so it has been left out. Now we can try something similar to our first example. Once again we will be able to complete the proof only using rewrites, without needing to specifically apply any lemmas or needing to know anything about the structure of our relation.

```coq
Goal forall (a b c d : Z), a ≡ b -> b ≡ c -> c ≡ d -> a ≡ d.
Proof.
  intros a b c d Hab Hcb Hcd. rewrite Hab. rewrite Hcb. auto.
Qed.
```

In fact, all we needed to do the above rewrites was the transitivity of `≡`. You can rearrange the companion file and see this for yourself. However, the fact that it is an equivalence relation gives us some extra useful tactics. If we want to flip the relation in either a goal or a hypothesis, we can use the `symmetry` tactic, and we can use `reflexivity` to prove that too expressions that are syntactically equal are related by `≡`.

Now let us proceed to a more complicated example. We can start by observing and proving that `k ≡ 0`.

```coq
Lemma k_equiv_0 : k ≡ 0.
Proof.
  ...
Qed.
```

Now we might want to prove some basic propositions by rewriting `k` into `0`. But follow in the companion code what happens with the following proof script.

```coq
Goal forall x, x + k ≡ x.
Proof.
  intros. Fail rewrite k_equiv_0. 
Abort.
```

So it didn't work. The terrifying error message you should have seen is just related to type class resolution in Coq and is not obviously helpful.

So, without useful error messages to guide us, let's try to figure out what is wrong. Recall what I wrote earlier about rewriting under different contexts. We need to prove that addition is proper with respect to `≡`. It makes sense that we should need to prove this, because we can easily construct functions that are not proper. For instance, consider 

```coq
Definition f x y := 
  if x ?= 0 && y ?= 0 
  then 0
  else 1.
```
which clearly distinguishes between `0` and `k` in general.

In the scary error message you may have noticed the term `Proper` and the notation `==>`. So we can start our search there.

```coq
Definition Proper {A : Type} (R : A -> A -> Prop) : A -> Prop := 
  fun a => R a a
```

So it is the function that takes a relation `R`, a single element `a` and uses `a` for both of `R`'s inputs. We provide some more basic examples in the  We haven't gotten very fair with this function. Now note that `==>` is notation for the function `respectful`. 

```coq 
Definition respectful {A B : Type} (R : A -> A -> Prop)
  (R' : B -> B -> Prop) : (A -> B) -> (A -> B) -> Prop :=
    fun f g => forall x y, R x y -> R' (f x) (g y)
```

Now we have found an interesting looking definition! So this is a function that lifts relations over inputs and outputs to relations over functions. In fact if we apply `respectful` to the same `f` twice, we get the proposition
```coq
forall x y, R x y -> R' (f x) (f y)
```

This should start to look like the informal definitions from the beginning of this post. Consider the following proposition

```coq
Goal Proper (equiv ==> equiv) (fun x => x + 2).
Proof.
    intros ? ? ?.
    ...
Qed. 
```

Intuitively, this proposition says that given any `x` and `y` such that `x ≡ y`, then `x + 2 ≡ y + 2`. For a general rule consider the following proposition

```coq
  Proper (R1 ==> R2 ==> ... ==> Rn ==> Rm) f
```

It means that given two sequences of variables `x1 ... xn` and `y1 .. yn` such that given any `i`, `Ri xi yi`,
```coq 
 Rm (f x1 .. xn) (f y1 .. yn) 
```
So all of the relations to the left of a `==>` relate arguments and the rightmost relation relates the outputs.

Now we can return to our modular aritmetic example. First let us prove that addition respects `≡` in its second argument.

```coq
Instance add_proper_r {x: Z} : Proper (equiv ==> equiv) (Z.add x).
Proof.
  ...
Qed.
```

Now we can rewrite in the second argument of addition. Let us put that to the test in a simple example.

```coq
Goal forall x, x + k ≡ x.
Proof.
  intros. rewrite k_equiv_0.
  rewrite Z.add_comm. simpl. reflexivity.
Qed.
```

Note that we still can't rewrite in the left argument.

```coq
Goal forall x, k + x ≡ x.
Proof.
  intros. 
  Fail rewrite k_equiv_0. 
Abort.  
```

In order to rewrite in the left argument, we need to show that addition is proper in all of its arguments. This proof is made simple by our existing proper instance and the fact that addition is commutative.

```coq
Instance add_proper : Proper (equiv ==> equiv ==> equiv) Z.add.
Proof.
  intros x y  Hxy z w Hzw.
  rewrite <- Hzw. Fail rewrite Hxy. 
  rewrite Z.add_comm. rewrite Hxy. rewrite Z.add_comm.
  reflexivity.
Qed.
```

Now we can stress test our rewriting with the following example.
```coq
 Goal forall x : Z, 
  k + (x + ( k + k ) + k) ≡ 
  k + k + (k + k) + ( (k + k) + (k + k)  ) + x. 
  Proof.
    intros. rewrite k_equiv_0. simpl. rewrite Z.add_comm. simpl.
    rewrite Z.add_comm. reflexivity.
  Qed.
```

Note that there is only one `x` on each side of the equivalence, so once we replace all `k`'s with `0`, the proof is vastly simpler.

Now, to wrap up I will introduce another, possibly less familiar, example where rewriting is incredibly useful. Suppose we want to model stateful computations in Coq (where our type of states is `S`), where there are no stateful operations. We can do that with the following type.

```coq
Definition State (A : Type) := S -> (S * A).
```
This captures the notion that all stateful computations require an input state to run and return an output state as well as a result. We can give this type a monadic structure with the following functions

```coq
Definition ret {A} (a : A) := fun s : S => (s,a).

Definition bind {A B} (m : State A) (f : A -> State B) :=
  fun s => let '(s',a) := m s in f a s'.
```

`ret` captures the notion of a pure computation returning `a`, and therefore leaves its input state alone.

`bind` captures the notion of concatenating two stateful computations by running the first one and threading the output state as input to the next one. It actually generalizes that notion a bit, taking as its argument a function `f : A -> State B`, which can be views as a family of stateful computations indexed over `A`. As is custumary, we denote `bind` with the infix operator `>>=`

We can create a notion of stateful computation equivalence with the following function.

```coq
Definition state_eq {A : Type} (m1 m2 : State A) :=
  forall (s : S), m1 s = m2 s.
```

We can denote this equivalence with `≈`, and provide an instance of the `Equivalence` type class.

We can also define some equations that all monads must satisfy.

```coq
Lemma bind_ret : forall (A B : Type) (a : A) (f : A -> State B),
    ret a >>= f ≈ f a.
Proof.
  ...
Qed.

Lemma ret_bind : forall (A : Type) (m : State A),
    m >>= ret ≈ m.
Proof.
  ...
Qed.

Lemma bind_bind : forall (A B C : Type) (m : State A) 
                          (f : A -> State B) (g : B -> State C),
    (m >>= f) >>= g ≈ (m >>= (fun a => f a >>= g)).
Proof.
  ...
Qed.
```

Now suppose we want to rewrite these equations. This would be a nice thing to have because these equations require no knowledge of the definitions of `ret` and `bind`.

First, we can lift our equivalence over `State B` to an equivalence  over `A -> State B` using the `pointwise_relation` function.

```coq
Definition {A B : Type} (R : B -> B -> Prop) : 
  (A -> B) -> (A -> B) -> Prop :=
  fun f g => forall a, R (f a) (g a)
```
This captures the notion that given equal inputs, `f` and `g` produce related outputs.

Now we want to show that `bind` respects the stateful equivalence relation given arguments that are similarly equivalent. 

```coq
Instance proper_monad {A B: Type} : Proper 
  (@state_eq A ==> pointwise_relation A state_eq ==> @state_eq B) 
    (bind).
Proof.
  ...
Qed.
```

Now we can rewrite the monad laws under bind. Consider the following example.
```coq
Goal forall (A B :Type) (a : A) (f : A -> State B),
    ret a >>= (fun a' => f a') >>= ret ≈ f a.
Proof.
  intros. rewrite bind_bind. rewrite bind_ret. rewrite ret_bind.
  reflexivity.
Qed.
```

Hopefully, you found this to be a useful introduction to rewriting in Coq. There is much more to learn, but you should have a strong enough foundation to learn it on your own. Good luck proving things!
