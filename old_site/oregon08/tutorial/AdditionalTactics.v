(* Copyright (c) 2008 University of Pennsylvania PLClub

   This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   $Id: AdditionalTactics.v 2189 2008-07-15 12:57:07Z baydemir $ *)

(** A library of additional tactics. *)

Require Export String.
Open Scope string_scope.


(* *********************************************************************** *)
(** * Extensions and variations of standard tactics *)

(** "[remember c as x in |-]" replaces the term [c] by the identifier
    [x] in the conclusion of the current goal and introduces the
    hypothesis [x=c] into the context.  This tactic differs from a
    similar one in the standard library in that the replacement is
    made only in the conclusion of the goal; the context is left
    unchanged. *)

Tactic Notation "remember" constr(c) "as" ident(x) "in" "|-" :=
  let x := fresh x in
  let H := fresh "Heq" x in
  (set (x := c); assert (H : x = c) by reflexivity; clearbody x).

(** "[unsimpl E]" replaces all occurence of [X] by [E], where [X] is
    the result that tactic [simpl] would give when used to evaluate
    [E]. *)

Tactic Notation "unsimpl" constr(E) :=
  let F := (eval simpl in E) in change F with E.

(** The following tactics call the [(e)apply] tactic with the first
    hypothesis that succeeds, "first" meaning the hypothesis that
    comes earliest in the context, i.e., higher up in the list. *)

Ltac apply_first_hyp :=
  match reverse goal with
    | H : _ |- _ => apply H
  end.

Ltac eapply_first_hyp :=
  match reverse goal with
    | H : _ |- _ => eapply H
  end.


(* *********************************************************************** *)
(** * Variations on [auto] *)

(** The [auto*] and [eauto*] tactics are intended to be "stronger"
    versions of the [auto] and [eauto] tactics.  Similar to [auto] and
    [eauto], they each take an optional "depth" argument.

    Implementation note: if we declare these tactics using a single
    string, e.g., "auto*", then the resulting tactics are unusable
    since they fail to parse. *)

Tactic Notation "auto" "*" :=
  try solve [ congruence | auto | intuition auto ].

Tactic Notation "auto" "*" integer(n) :=
  try solve [ congruence | auto n | intuition (auto n) ].

Tactic Notation "eauto" "*" :=
  try solve [ congruence | eauto | intuition eauto ].

Tactic Notation "eauto" "*" integer(n) :=
  try solve [ congruence | eauto n | intuition (eauto n) ].


(* *********************************************************************** *)
(** * Delineating cases in proofs *)

(** ** Tactic definitions *)

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name
  | fail 1 "because we are working on a different case." ].

Ltac Case name := Case_aux case name.
Ltac SCase name := Case_aux subcase name.
Ltac SSCase name := Case_aux subsubcase name.
Ltac SSSCase name := Case_aux subsubsubcase name.
Ltac SSSSCase name := Case_aux subsubsubsubcase name.

(** ** Example

    One mode of use for the above tactics is to wrap Coq's [induction]
    tactic such that it automatically inserts "case" markers into each
    branch of the proof.  For example:

<<
 Tactic Notation "induction" "nat" ident(n) :=
   induction n; [ Case "O" | Case "S" ].
 Tactic Notation "sub" "induction" "nat" ident(n) :=
   induction n; [ SCase "O" | SCase "S" ].
 Tactic Notation "sub" "sub" "induction" "nat" ident(n) :=
   induction n; [ SSCase "O" | SSCase "S" ].
>>

    If you use such customized versions of the induction tactics, then
    the [Case] tactic will verify that you are working on the case
    that you think you are.  You may also use the [Case] tactic with
    the standard version of [induction], in which case no verification
    is done. *)


(* *********************************************************************** *)
(** * Tactics for working with lists and proof contexts *)

(** [ltac_map] applies a unary, non-dependently typed function [F] to
    everything in the context such that the application type checks.
    The tactic returns a [list] containing the results of the
    applications.

    Implementation note: The check for duplicates in the accumulator
    ([match acc with ...]) is necessary to ensure that the tactic does
    not go into an infinite loop. *)

Ltac ltac_map F :=
  let rec map acc :=
    match goal with
      | H : ?S |- _ =>
        let FH := constr:(F H) in
          match acc with
            | context [FH] => fail 1
            | _ => map (List.cons FH acc)
          end
      | _ => acc
    end
  in
  match type of F with
    | ?A -> ?B => let res := map (@List.nil B) in (eval simpl in res)
  end.

(** [ltac_remove_dups] takes a [list] and removes duplicate items from
    it.  The supplied list must, after simplification via [simpl], be
    built from only [nil] and [cons].  Duplicates are recognized only
    "up to syntax," i.e., the limitations of Ltac's [context]
    check. *)

Ltac ltac_remove_dups xs :=
  let rec remove xs acc :=
    match xs with
      | List.nil => acc
      | List.cons ?x ?xs =>
        match acc with
          | context [x] => remove xs acc
          | _ => remove xs (List.cons x acc)
        end
    end
  in
  match type of xs with
    | List.list ?A =>
      let xs := (eval simpl in xs) in
      let xs := remove xs (@List.nil A) in
      eval simpl in (List.rev xs)
  end.

(** [ltac_fold_and_simpl] is a wrapper for [List.fold_right] that does
    some preliminary simplification and removal of duplicates on the
    supplied list. *)

Ltac ltac_fold_and_simpl f start xs :=
  let xs := (eval simpl in xs) in
  let xs := ltac_remove_dups xs in
  let xs := eval simpl in (List.fold_right f start xs) in
  xs.
