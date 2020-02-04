(* Copyright (c) 2008 University of Pennsylvania PLClub

   This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   $Id: Atom.v 2189 2008-07-15 12:57:07Z baydemir $ *)

Require Import Arith.
Require Import DecidableTypeEx.
Require Import List.
Require Import Max.


(* ********************************************************************** *)
(** * Main definition (and implementation) *)

(** Atoms are structureless objects such that we can always generate
    one fresh from a finite collection.  Equality on atoms is [eq] and
    decidable.  We use Coq's module system to make abstract the
    implementation of atoms.  The module type [ATOM], defined below,
    is compatible with [UsualDecidableType].  *)

Module Type ATOM.

  Parameter t : Set.

  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.

  Parameter atom_fresh_for_list :
    forall (xs : list t), {x : t | ~ List.In x xs}.

End ATOM.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module AtomImpl : ATOM.

  (* begin hide *)

  Definition t := nat.

  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    induction x. auto with arith.
    induction y. auto with arith.
      simpl. induction z. omega. auto with arith.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, In x xs -> x <= n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists 0. inversion 1.
    (* case: cons x xs *)
    exists (max x y). intros z J. simpl in J. destruct J as [K | K].
      subst. auto with arith.
      auto using max_lt_r.
  Qed.

  Lemma atom_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ List.In n xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). omega. trivial.
  Qed.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y} :=
    eq_nat_dec.

  (* end hide *)

End AtomImpl.


(* ********************************************************************** *)
(** * Auxiliary definitions *)

(** We give more suggestive names to some of the constants provided by
    the [AtomImpl] module. *)

Definition atom := AtomImpl.t.
Definition eq_atom_dec := AtomImpl.eq_dec.
