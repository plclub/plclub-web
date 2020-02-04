(* Copyright (c) 2008 University of Pennsylvania PLClub

   This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   $Id: FSetWeakNotin.v 2189 2008-07-15 12:57:07Z baydemir $ *)

(** Lemmas and tactics for working with and solving goals related to
    non-membership in finite sets.  The main tactic of interest here
    is [solve_notin].

    Implicit arguments are declared by default in this library. *)

Set Implicit Arguments.
Require Import FSetWeakInterface.


(* *********************************************************************** *)
(** * Implementation *)

Module Notin (Import X : FSetWeakInterface.S).


(* *********************************************************************** *)
(** ** Facts about set non-membership *)

Lemma notin_empty : forall x,
  ~ In x empty.
Proof.
  auto using empty_1.
Qed.

Lemma notin_union : forall x E F,
  ~ In x E -> ~ In x F -> ~ In x (union E F).
Proof.
  intros x E F H J K.
  destruct (union_1 K); intuition.
Qed.

Lemma elim_notin_union : forall x E F,
  ~ In x (union E F) -> (~ In x E) /\ (~ In x F).
Proof.
  intros x E F H. split; intros J; contradiction H.
  auto using union_2.
  auto using union_3.
Qed.

Lemma notin_singleton : forall x y,
  ~ E.eq x y -> ~ In x (singleton y).
Proof.
  intros x y H J. assert (K := singleton_1 J). intuition.
Qed.

Lemma elim_notin_singleton : forall x y,
  ~ In x (singleton y) -> ~ E.eq x y.
Proof.
  intros x y H J. contradiction H. auto using singleton_2.
Qed.

Lemma elim_notin_singleton' : forall x y,
  ~ In x (singleton y) -> x <> y.
Proof.
  intros. assert (~ E.eq x y). auto using singleton_2.
  intros J. subst. intuition.
Qed.

Lemma notin_add : forall x y F,
  ~ E.eq y x -> ~ In x F -> ~ In x (add y F).
Proof.
  intros x y F H J K. contradiction J. eauto using add_3.
Qed.

Lemma elim_notin_add : forall x y F,
  ~ In x (add y F) -> ~ E.eq y x /\ ~ In x F.
Proof.
  intros. split; intros J; contradiction H.
  auto using add_1.
  auto using add_2.
Qed.

Lemma elim_notin_add' : forall x y F,
  ~ In x (add y F) -> y <> x /\ ~ In x F.
Proof.
  intros. split; intros J; contradiction H.
  subst. auto using add_1.
  auto using add_2.
Qed.


(* *********************************************************************** *)
(** ** Tactics *)

(** The tactic [simpl_notin_hyps] destructs all hypotheses of the form
    [(~ In x E)], where [E] is built using only [empty], [add],
    [union], and [singleton]. *)

Ltac simpl_notin_hyps :=
  match goal with
    | H: In ?x ?E -> False |- _ =>
      change (~ In x E) in H;
      simpl_notin_hyps
    | H: ~ In _ empty |- _ =>
      clear H;
      simpl_notin_hyps
    | H: ~ In ?x (union ?E ?F) |- _ =>
      destruct (@elim_notin_union x E F H);
      clear H;
      simpl_notin_hyps
    | H: ~ In ?x (singleton ?y) |- _ =>
      let F1 := fresh in
      let F2 := fresh in
      assert (F1 := @elim_notin_singleton x y H);
      assert (F2 := @elim_notin_singleton' x y H);
      clear H;
      simpl_notin_hyps
    | H: ~ In ?x (add ?y ?F) |- _ =>
      destruct (@elim_notin_add x y F H);
      destruct (@elim_notin_add' x y F H);
      clear H;
      simpl_notin_hyps
    | _ =>
      idtac
  end.

(** The tactic [solve_notin] solves goals of them form [(x <> y)] and
    [(~ In x E)] that are provable from hypotheses of the form
    destructed by [simpl_notin_hyps]. *)

Ltac solve_notin :=
  simpl_notin_hyps;
  repeat (progress (  apply notin_empty
                   || apply notin_union
                   || apply notin_singleton
                   || apply notin_add));
  solve [ trivial | congruence | intuition auto ].


(* *********************************************************************** *)
(** ** Examples and test cases *)

(** These examples and test cases are not meant to be exhaustive. *)

Lemma test_solve_notin_1 : forall x E F G,
  ~ In x (union E F) -> ~ In x G -> ~ In x (union E G).
Proof.
  intros. solve_notin.
Qed.

Lemma test_solve_notin_2 : forall x y E F G,
  ~ In x (union E (union (singleton y) F)) -> ~ In x G ->
  ~ In x (singleton y) /\ ~ In y (singleton x).
Proof.
  intros. split. solve_notin. solve_notin.
Qed.

Lemma test_solve_notin_3 : forall x y,
  ~ E.eq x y -> ~ In x (singleton y) /\ ~ In y (singleton x).
Proof.
  intros. split. solve_notin. solve_notin.
Qed.

Lemma test_solve_notin_4 : forall x y E F G,
  ~ In x (union E (union (singleton x) F)) -> ~ In y G.
Proof.
  intros. solve_notin.
Qed.

Lemma test_solve_notin_5 : forall x y E F,
  ~ In x (union E (union (singleton y) F)) -> ~ In y E ->
  ~ E.eq y x /\ ~ E.eq x y.
Proof.
  intros. split. solve_notin. solve_notin.
Qed.

Lemma test_solve_notin_6 : forall x y E,
  ~ In x (add y E) -> ~ E.eq x y /\ ~ In x E.
Proof.
  intros. split. solve_notin. solve_notin.
Qed.

End Notin.
