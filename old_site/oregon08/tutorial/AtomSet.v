(* Copyright (c) 2008 University of Pennsylvania PLClub

   This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   $Id: AtomSet.v 2189 2008-07-15 12:57:07Z baydemir $ *)

Require Import AdditionalTactics.
Require Import Atom.
Require Import FSetWeak.
Require Import FSetWeakDecide.
Require Import FSetWeakNotin.
Require Import ListFacts.


(* ********************************************************************** *)
(** * Definitions *)

(** We use our implementation of atoms to obtain an implementation of
    finite sets of atoms.  We give the resulting type an intuitive
    name, as well as import names of set operations for use within
    this library. *)

Module Import AtomSetImpl := FSetWeakList.Make AtomImpl.
Definition atoms := AtomSetImpl.t.

(** From our implementation of finite sets of atoms, we can
    instantiate the decision procedures for solving facts about such
    finite sets. *)

Module AtomSetDecide := FSetWeakDecide.Decide AtomSetImpl.
Ltac atomsetdec := AtomSetDecide.fsetdec.

Module AtomSetNotin := FSetWeakNotin.Notin AtomSetImpl.
Ltac simpl_notin_hyps := AtomSetNotin.simpl_notin_hyps.
Ltac solve_atomset_notin := AtomSetNotin.solve_notin.

(** Given the [atomsetdec] tactic, we typically do not need to refer
    to specific lemmas about finite sets.  However, instantiating the
    [FSetWeakFacts.Facts] functor makes a number of setoid rewrites
    available.  These rewrites are crucial to developments since they
    allow us to replace a set with an extensionally equal set (see the
    [Equal] relation on finite sets) in propositions about finite
    sets. *)

Module AtomSetProperties := FSetWeakFacts.Facts AtomSetImpl.


(* ********************************************************************** *)
(** * Properties *)

(** We can generate an atom fresh for any given finite set of
    atoms. *)

Lemma atom_fresh_for_set : forall L : atoms, { x : atom | ~ In x L }.
Proof.
  intros L. destruct (AtomImpl.atom_fresh_for_list (elements L)) as [a H].
  exists a. intros J. contradiction H.
  rewrite <- InA_iff_In. auto using elements_1.
Qed.


(* ********************************************************************** *)
(** * Tactic support *)


(** The auxiliary tactic [simplify_list_of_atom_sets] takes a list of
    finite sets of atoms and unions everything together, returning the
    resulting single finite set.  It's rarely used by itself; see the
    example below.  The tactic does assume that [L], after
    simplification using [simpl], is built using only [nil] and
    [cons].  This is the case when used following the pattern
    below. *)

Ltac simplify_list_of_atom_sets L :=
  ltac_fold_and_simpl AtomSetImpl.union AtomSetImpl.empty L.

(** The tactic [(pick fresh Y for L)] takes a finite set of atoms [L]
    and a fresh name [Y], and adds to the context an atom with name
    [Y] and a proof that [(~ In Y L)], i.e., that [Y] is fresh for
    [L].  The tactic will fail if [Y] is already declared in the
    context. *)

Tactic Notation "pick" "fresh" ident(Y) "for" constr(L) :=
  let Fr := fresh "Fr" in
  (destruct (atom_fresh_for_set L) as [Y Fr]).


(* ********************************************************************** *)
(** ** Example *)

(** The [example_pick_fresh] tactic below illustrates the general
    pattern for collecting together atoms in a context and picking an
    atom fresh for them.

    We first define a tactic that gathers the atoms in the current
    context and returns them as a finite set.  We repeatedly invoke
    the tactic [ltac_map], using each time a unary function that
    returns a finite set of atoms.  The type of the function
    determines the hypotheses that are processed.  Each invocation
    returns a list of finite sets of atoms.  We append everything
    together and use [simplify_list_of_atom_sets] to obtain a single
    finite set. *)

Ltac example_gather_atoms :=
  let A := ltac_map (fun x : atoms => x) in
  let B := ltac_map (fun x : atom => singleton x) in
  simplify_list_of_atom_sets (A ++ B).

(** Given [example_gather_atoms], we can implement a specialized
    version of "[pick fresh]". *)

Ltac example_pick_fresh Y :=
  let L := example_gather_atoms in
  pick fresh Y for L.

(** Finally, we gave a trivial example of using
    [example_pick_fresh]. *)

Lemma example_pick_fresh_use : forall (x y z : atom) (L1 L2 L3: atoms), True.
(* begin show *)
Proof.
  intros x y z L1 L2 L3.
  example_pick_fresh k.

  (** At this point in the proof, we have a new atom [k] and a
      hypothesis [Fr : ~ In k (union L1 (union L2 (union L3 (union
      (singleton x) (union (singleton y) (union (singleton z)
      empty)))))]. *)

  trivial.
Qed.
(* end show *)
