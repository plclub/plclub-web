(* Copyright (c) 2008 University of Pennsylvania PLClub

   This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   $Id: Metatheory.v 2189 2008-07-15 12:57:07Z baydemir $ *)

Require Import Peano_dec.

Require Export AdditionalTactics.
Require Export Atom.
Require Export AtomSet.
Require Export AtomEnv.
Require Export List.
Require Export ListFacts.


(* ********************************************************************** *)
(** * Modules *)

(** We export the types, functions, lemmas, etc. provided by the
    implementations of association lists whose keys are atoms (from
    [AtomEnv]).

    Implementation note: We specifically do not [Export] the
    [AtomImpl] and [AtomSetImpl] modules in order to avoid polluting
    Coq's namespace.  Commonly used items from those files are given
    convenient definitions and notations, either here or in the
    libraries that implement those modules. *)

Export AtomEnvImpl.


(* ********************************************************************** *)
(** * Notations *)

(** Decidable equality on atoms and natural numbers may be written
    using suggestive notation. *)

Notation "x == y" :=
  (AtomImpl.eq_dec x y) (at level 67) : metatheory_scope.
Notation "i === j" :=
  (Peano_dec.eq_nat_dec i j) (at level 67) : metatheory_scope.

(** We can use list-like notation to write association lists
    consisting of a single binding. *)

Notation "[ x ]" := (AtomEnvImpl.one x) : metatheory_scope.

(** Common set operations may be written using infix notation.  The
    ones for equality and subset match the notations used in the FSets
    library.  Implementation note: Since we do not [Export] the
    [AtomSetImpl] module, we have to (re)define notations as
    needed. *)

Notation "E `union` F" :=
  (AtomSetImpl.union E F)
  (at level 69, right associativity, format "E  `union`  '/' F")
  : set_scope.
Notation "x `in` E" :=
  (AtomSetImpl.In x E) (at level 69) : set_scope.
Notation "x `notin` E" :=
  (~ AtomSetImpl.In x E) (at level 69) : set_scope.
Notation "E [=] F" :=
  (AtomSetImpl.Equal E F) (at level 70, no associativity) : set_scope.
Notation "E [<=] F" :=
  (AtomSetImpl.Subset E F) (at level 70, no associativity) : set_scope.

(** We define some abbreviations for the empty set, singleton
    sets, and the union of two sets. *)

Notation empty := AtomSetImpl.empty.
Notation singleton := AtomSetImpl.singleton.
Notation union := AtomSetImpl.union.

(** We define some abbreviations for some lemmas about set
    non-membership. *)

Notation notin_empty := AtomSetNotin.notin_empty.
Notation notin_union := AtomSetNotin.notin_union.
Notation notin_singleton := AtomSetNotin.notin_singleton.
Notation notin_add := AtomSetNotin.notin_add.

(** Open the notation scopes declared above. *)

Open Scope metatheory_scope.
Open Scope set_scope.


(* ********************************************************************** *)
(** * Tactic for working with cofinite quantification *)

(** Consider a rule [H] (equivalently, constructor, lemma, etc.) whose
    type begins with [forall L, ...] and contains hypotheses of the
    form [(forall y, y `notin` L -> ...)].

    The tactic [(pick fresh x excluding F and apply H)] applies [H] to
    the current goal, instantiating [H]'s first argument ([L]) with
    the finite set of atoms [F].  In each new subgoal of the form
    [(forall y, y `notin` F -> ...)], the atom [y] is introduced as
    [x], and [(y `notin` F)] is introduced using a generated name.

    If we view [H] as a rule that uses cofinite quantification, the
    tactic can be read as picking a sufficiently fresh atom to open a
    term with. *)

Tactic Notation
  "pick" "fresh" ident(atom_name)
  "excluding" constr(L)
  "and" "apply" constr(H)
  :=
    first [apply (@H L) | eapply (@H L)];
      match goal with
        | |- forall _, _ `notin` _ -> _ =>
          let Fr := fresh "Fr" in intros atom_name Fr
        | |- forall _, _ `notin` _ -> _ =>
          fail 1 "because" atom_name "is already defined"
        | _ =>
          idtac
      end.


(* ********************************************************************** *)
(** * Automation *)

(** The next two blocks of hints should discharge many of the
    freshness and inequality goals that arise in programming language
    metatheory proofs, in particular those arising from cofinite
    quantification.

    Implementation note: The invocation of [simpl_env] is risky since
    [autorewrite] does not interact nicely with the existential
    variables introduced by [eauto].  In practice, this does not seem
    to be a problem.  However, practice also shows that a similar
    problem does occurs if we use [atomsetdec] instead of
    solve_atomset_notin. *)

Hint Resolve AtomSetNotin.notin_empty.
Hint Resolve AtomSetNotin.notin_union.
Hint Resolve AtomSetNotin.notin_singleton.
Hint Resolve AtomSetNotin.notin_add.

Hint Extern 4 (_ `notin` _) => simpl_env in *; solve_atomset_notin.
Hint Extern 4 (_ <> _ :> atom) => simpl_env in *; solve_atomset_notin.
Hint Extern 4 (_ <> _ :> AtomSetImpl.elt) => simpl_env in *; solve_atomset_notin.

(** The following are hints for equalities on environments. *)

Hint Resolve app_assoc app_nil_1 app_nil_2.
Hint Resolve nil_neq_one_mid one_mid_neq_nil.
Hint Resolve map_nil map_one map_app.
Hint Resolve dom_nil dom_one dom_app dom_map.

(** The following hints are primarily about [uniq]. *)

Hint Resolve uniq_nil uniq_cons uniq_one uniq_push.
Hint Resolve uniq_insert_mid.
Hint Immediate uniq_remove_mid.

(** The following hints are primarily about [binds]. *)

Hint Resolve binds_one_1 binds_app_1 binds_app_2.
Hint Resolve binds_map binds_weaken.
Hint Immediate binds_remove_mid.
