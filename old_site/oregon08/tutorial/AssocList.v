(* Copyright (c) 2008 University of Pennsylvania PLClub

   This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   $Id: AssocList.v 2202 2008-07-17 16:29:38Z baydemir $ *)

Require Import Decidable.
Require Import FSetWeak.
Require Import List.

Require Import AdditionalTactics.
Require Import ListFacts.
Require Import FSetWeakDecide.


(* *********************************************************************** *)
(** * Implementation *)

(** We implement association lists as a functor over an implementation
    of finite sets of keys.  This allows us to define a domain
    function on association lists that returns a finite set of keys,
    as opposed to, say, a list of keys.  Note that the
    [UsualDecidableType] argument requires that equality on keys be
    [eq] (Coq's "built-in" equality) and decidable. *)

(** Note that our library has an implicit convention for the "normal
    form" of an association list.  This normal form requires that a
    list be built only from [nil] (the empty list), [one] (the
    singleton list), and [app] (concatenation).  Additionally,
    concatenations should be associated to the right and the list
    should not contain any [nil] terms, unless it is the empty list
    itself.

    This allows association lists to be written in a slightly more
    uniform manner when compared to using both [cons] and [app] to
    build them.  The downsides are that Coq's [simpl] tactic will
    simplify instances of [one] down to [cons] and that there are
    instances in which one needs to write association lists that are
    not in normal form (typically, some concatenation will need to be
    associated to the left).  The [simpl_alist] and [rewrite_alist]
    tactics below are designed to minimize the impact of these
    downsides.

    We have considered other alternative implementations, but the scheme
    described above seems to work the best in practice. *)

(*  >> Purposefully not including this in generated HTML documentation. <<

    Implementation notes:

    There are various mechanisms for enforcing that [one] is never
    simplified down to [cons], e.g., by making its definition
    abstract.  However, this is undesirable because it interacts
    poorly with Coq's [inversion] tactic.  For example, in order to
    sensibly invert the conclusion of [uniq_push], Coq needs to reduce
    [((x ~ a) ++ E)] down to a term with a constructor at its head.
    This is impossible if Coq cannot unfold the definition of [one].

    Alternatively, we could could define a completely new inductive
    datatype for association lists that had three constructors---one
    each corresponding to [nil], [one], and [app].  Associativity of
    [app] then becomes a problem because we need to define a suitable
    equality relation on association lists, instead of simply being
    able to use [eq]. *)

Module Make
  (X : UsualDecidableType)
  (Import KeySet : FSetWeakInterface.S with Module E := X).

  Module Import D := Decide KeySet.
  Module KeySetProperties := Properties KeySet.


  (* ********************************************************************* *)
  (** ** Basic definitions *)

  (** This section defines the following basic operations and
      predicates on association lists.

        - [one]: Constructs an association list consisting of exactly
          one binding.
        - [map]: Maps a function over the values in an association list.
        - [dom]: Computes the domain of an association list, i.e., the
          set consisting of its keys.
        - [disjoint]: Binary predicate that holds when the domains of
          two association lists are disjoint.
        - [binds]: Ternary predicate that holds when a key-value pair
          appears somewhere in an association list.
        - [uniq]: Unary predicate that holds when an association list
          binds any given key at most once.  Note that [uniq_push] is
          defined in terms of [one], due to our normal form for
          association lists.

      Implicit arguments are declared by default for these
      definitions.  We define some local notations to make the
      definition of [uniq] easier to read and to be consistent with
      the notations used in the rest of this library. *)

  Section Definitions.
    Set Implicit Arguments.
    Variables A B C : Type.

    Definition one (C : Type) (item : C) : list C := cons item nil.

    Definition map (f : A -> B) (E : list (X.t*A)) : list (X.t*B) :=
      List.map (fun b => match b with (x, a) => (x, f a) end) E.

    Fixpoint dom (A : Type) (E : list (X.t*A)) {struct E} : KeySet.t :=
      match E with
        | nil => empty
        | (x, _) :: E' => add x (dom E')
      end.

    Definition disjoint (E : list (X.t*A)) (F : list (X.t*B)) : Prop :=
      Subset (inter (dom E) (dom F)) empty.

    Definition binds (x : X.t) (a : A) (E : list (X.t*A)) : Prop :=
      List.In (x, a) E.

    Notation Local "x ~ a" := (one (x, a)) (at level 68).
    Notation Local "x `notin` E" := (~ KeySet.In x E) (at level 69).

    Inductive uniq : list (X.t*A) -> Prop :=
      | uniq_nil :
          uniq nil
      | uniq_push : forall x a E,
          uniq E ->
          x `notin` dom E ->
          uniq ((x ~ a) ++ E).

    Unset Implicit Arguments.
  End Definitions.


  (* ********************************************************************* *)
  (** ** Local notations *)

  (** We make a local notation for [one], and for operations and
      predicate on finite sets, in order to make the statements of the
      lemmas below more readable.  The notations are local so that
      users of this functor may choose their own notations. *)

  Notation Local "[ i ]" := (one i).
  Notation Local "x ~ T" := (one (x, T)) (at level 68).

  Notation Local "E `union` F" :=
     (KeySet.union E F) (at level 69, right associativity).
  Notation Local "x `in` E" :=
     (KeySet.In x E) (at level 69).
  Notation Local "x `notin` E" :=
     (~ KeySet.In x E) (at level 69).
  Notation Local "E [=] F" :=
     (KeySet.Equal E F) (at level 70, no associativity).
  Notation Local "E [<=] F" :=
     (KeySet.Subset E F) (at level 70, no associativity).


  (* ********************************************************************* *)
  (** ** List properties *)

  (** The following block of properties is used mainly for rewriting
      association lists into the normal form described above.  See the
      [simpl_alist] and [rewrite_alist] tactics below. *)

  Section ListProperties.
    Variables X : Type.
    Variables x y : X.
    Variables l l1 l2 l3 : list X.

    Lemma cons_app_one :
      cons x l = [ x ] ++ l.
    Proof. clear. reflexivity. Qed.

    Lemma cons_app_assoc :
      (cons x l1) ++ l2 = cons x (l1 ++ l2).
    Proof. clear. reflexivity. Qed.

    Lemma app_assoc :
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
    Proof. clear. apply app_ass. Qed.

    Lemma app_nil_1 :
      nil ++ l = l.
    Proof. clear. reflexivity. Qed.

    Lemma app_nil_2 :
      l ++ nil = l.
    Proof. clear. auto with datatypes. Qed.

    Lemma in_one :
      List.In x [ y ] <-> x = y.
    Proof. clear. simpl. intuition congruence. Qed.

    Lemma in_app :
      List.In x (l1 ++ l2) <-> List.In x l1 \/ List.In x l2.
    Proof. clear. split; auto using in_or_app, in_app_or. Qed.

  End ListProperties.

  Hint Rewrite cons_app_one cons_app_assoc app_assoc : rewr_list.
  Hint Rewrite app_nil_1 app_nil_2 : rewr_list.
  Hint Rewrite in_one in_app : rewr_list_in.

  (** The following block of properties is an assortment of
      structural properties about lists. *)

  Section AssortedListProperties.
    Variables X : Type.
    Variables x y : X.
    Variables l l1 l2 l3 : list X.

    Lemma one_eq_app :
      [ x ] ++ l1 = l2 ++ l3 ->
      (exists qs, l2 = x :: qs /\ l1 = qs ++ l3) \/
      (l2 = nil /\ l3 = x :: l1).
    Proof. simpl. auto using cons_eq_app. Qed.

    Lemma app_eq_one :
      l2 ++ l3 = [ x ] ++ l1 ->
      (exists qs, l2 = x :: qs /\ l1 = qs ++ l3) \/
      (l2 = nil /\ l3 = x :: l1).
    Proof. simpl. auto using app_eq_cons. Qed.

    Lemma nil_neq_one_mid :
      nil <> l1 ++ [ x ] ++ l2.
    Proof. destruct l1; simpl; intros H; discriminate. Qed.

    Lemma one_mid_neq_nil :
      l1 ++ [ x ] ++ l2 <> nil.
    Proof. destruct l1; simpl; intros H; discriminate. Qed.

  End AssortedListProperties.


  (* ********************************************************************* *)
  (** ** Properties of [map] and [dom] *)

  (** The following lemmas are used mainly to simplify applications of
      [map] and [dom] to association lists.  See also the [simpl_alist]
      and [rewrite_alist] tactics below. *)

  Section Properties.
    Variables A B : Type.
    Variables f : A -> B.
    Variables x : X.t.
    Variables b : A.
    Variables E F G : list (X.t*A).

    Lemma map_nil :
      map f nil = nil.
    Proof. clear. reflexivity. Qed.

    Lemma map_cons :
      map f ((x, b) :: E) = (x, f b) :: map f E.
    Proof. clear. reflexivity. Qed.

    Lemma map_one :
      map f (x ~ b) = (x ~ f b).
    Proof. clear. reflexivity. Qed.

    Lemma map_app :
      map f (E ++ F) = map f E ++ map f F.
    Proof. clear. unfold map. rewrite -> List.map_app. reflexivity. Qed.

    Lemma dom_nil :
      (@dom A nil) = empty.
    Proof. clear. reflexivity. Qed.

    Lemma dom_cons :
      dom ((x, b) :: E) [=] singleton x `union` dom E.
    Proof. clear. simpl. fsetdec. Qed.

    Lemma dom_one :
      dom (x ~ b) [=] singleton x.
    Proof. clear. simpl. fsetdec. Qed.

    Lemma dom_app :
      dom (E ++ F) [=] dom E `union` dom F.
    Proof. clear. induction E as [ | [x1 a1] ]; simpl; fsetdec. Qed.

    Lemma dom_map :
      dom (map f E) [=] dom E.
    Proof. clear. induction E as [ | [x1 a1] ]; simpl; fsetdec. Qed.

  End Properties.

  Hint Rewrite map_nil map_cons map_one map_app : rewr_map.
  Hint Rewrite dom_nil dom_cons dom_one dom_app dom_map : rewr_dom.


  (* ********************************************************************* *)
  (** ** The [simpl_alist] tactic *)

  (** The [simpl_alist] tactic rewrites association lists so that they
      are in the normal form described above.  Similar to the [simpl]
      tactic, we define "[in *]" and "[in H]" variants of the tactic. *)

  Ltac simpl_alist :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom.
  Tactic Notation "simpl_alist" "in" hyp(H) :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom in H.
  Tactic Notation "simpl_alist" "in" "*" :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom in *.


  (* ********************************************************************* *)
  (** ** The [rewrite_alist] tactic *)

  (** The tactic [(rewrite_alist E)] replaces an association list in
      the conclusion of the goal with [E].  Suitability for
      replacement is determined by whether [simpl_alist] can put [E]
      and the chosen environment in the same normal form, up to
      convertibility's in Coq.  We also define an "[in H]" variant
      that performs the replacement in a hypothesis [H].  *)

  Tactic Notation "rewrite_alist" constr(E) :=
    match goal with
      | |- context[?x] =>
        change x with E
      | |- context[?x] =>
        replace x with E;
          [ | try reflexivity; simpl_alist; reflexivity ]
    end.

  Tactic Notation "rewrite_alist" constr(E) "in" hyp(H) :=
    match type of H with
      | context[?x] =>
        change x with E in H
      | context[?x] =>
        replace x with E in H;
          [ | try reflexivity; simpl_alist; reflexivity ]
    end.


  (* ********************************************************************* *)
  (** ** Basic facts about [disjoint] *)

  Section BasicDisjointFacts.
    Implicit Types A B C : Type.

    Lemma disjoint_sym_1 :
      forall A B (E : list (X.t*A)) (F : list (X.t*B)),
        disjoint E F ->
        disjoint F E.
    Proof. unfold disjoint. fsetdec. Qed.

    Lemma disjoint_sym :
      forall A B (E : list (X.t*A)) (F : list (X.t*B)),
      disjoint E F <-> disjoint F E.
    Proof. intuition auto using disjoint_sym_1. Qed.

    Lemma disjoint_one_1 :
      forall A B (x : X.t) (a : A) (F : list (X.t*B)),
      disjoint (x ~ a) F ->
      x `notin` dom F.
    Proof. unfold disjoint. intros. simpl_alist in *. fsetdec. Qed.

    Lemma disjoint_one_2 :
      forall A B (x : X.t) (a : A) (F : list (X.t*B)),
      x `notin` dom F ->
      disjoint (x ~ a) F.
    Proof. unfold disjoint. intros. simpl_alist in *. fsetdec. Qed.

    Lemma disjoint_one_l :
      forall A B (x : X.t) (a : A) (E : list (X.t*B)),
      disjoint (x ~ a) E <-> x `notin` dom E.
    Proof. intros. unfold disjoint; simpl_alist; split; fsetdec. Qed.

    Lemma disjoint_one_r :
      forall A B (x : X.t) (a : A) (E : list (X.t*B)),
      disjoint E (x ~ a) <-> x `notin` dom E.
    Proof. intros. rewrite -> disjoint_sym. apply disjoint_one_l. Qed.

    Lemma disjoint_app_1 :
      forall A B (E F : list (X.t*A)) (G : list (X.t*B)),
      disjoint (E ++ F) G ->
      disjoint E G.
    Proof. intros. unfold disjoint in *. simpl_alist in *. fsetdec. Qed.

    Lemma disjoint_app_2 :
      forall A B (E F : list (X.t*A)) (G : list (X.t*B)),
      disjoint (E ++ F) G ->
      disjoint F G.
    Proof. intros. unfold disjoint in *. simpl_alist in *. fsetdec. Qed.

    Lemma disjoint_app_3 :
      forall A B (E F : list (X.t*A)) (G : list (X.t*B)),
      disjoint E G ->
      disjoint F G ->
      disjoint (E ++ F) G.
    Proof. intros. unfold disjoint in *. simpl_alist in *. fsetdec. Qed.

    Lemma disjoint_app_l :
      forall A B (E F : list (X.t*A)) (G : list (X.t*B)),
      disjoint (E ++ F) G <-> disjoint E G /\ disjoint F G.
    Proof.
      intros; intuition eauto using
        disjoint_app_1, disjoint_app_2, disjoint_app_3.
    Qed.

    Lemma disjoint_app_r :
      forall A B (E F : list (X.t*A)) (G : list (X.t*B)),
      disjoint G (E ++ F) <-> disjoint E G /\ disjoint F G.
    Proof. intros. rewrite -> disjoint_sym. apply disjoint_app_l. Qed.

    Lemma disjoint_map_1 :
      forall A B C (E : list (X.t*A)) (F : list (X.t*B)) (f : A -> C),
      disjoint (map f E) F ->
      disjoint E F.
    Proof. unfold disjoint. intros. simpl_alist in *. trivial. Qed.

    Lemma disjoint_map_2 :
      forall A B C (E : list (X.t*A)) (F : list (X.t*B)) (f : A -> C),
      disjoint E F ->
      disjoint (map f E) F.
    Proof. unfold disjoint. intros. simpl_alist in *. trivial. Qed.

    Lemma disjoint_map_l :
      forall A B C (E : list (X.t*A)) (F : list (X.t*B)) (f : A -> C),
      disjoint (map f E) F <-> disjoint E F.
    Proof. intros; intuition eauto using disjoint_map_1, disjoint_map_2. Qed.

    Lemma disjoint_map_r :
      forall A B C (E : list (X.t*A)) (F : list (X.t*B)) (f : A -> C),
      disjoint F (map f E) <-> disjoint E F.
    Proof. intros. rewrite -> disjoint_sym. apply disjoint_map_l. Qed.

  End BasicDisjointFacts.


  (* ********************************************************************* *)
  (** ** Basic facts about [uniq] *)

  (** The following lemmas are facts about [uniq] with respect to the
      basic functions ([one], [app], and [map]) that can be used to
      build association lists. *)

  Section UniqProperties.
    Variables A B : Type.
    Variables f : A -> B.
    Variables x : X.t.
    Variables b : A.
    Variables E F G : list (X.t*A).

    Lemma uniq_one :
      uniq (x ~ b).
    Proof.
      clear. rewrite_alist ((x ~ b) ++ nil). auto using uniq_nil, uniq_push.
    Qed.

    Lemma uniq_app_1 :
      uniq (E ++ F) -> uniq E.
    Proof.
      clear. intros H; induction E as [ | [x1 a1] E']; simpl_alist in *.
        apply uniq_nil.
        apply uniq_push; inversion H; subst.
          auto.
          simpl_alist in *. fsetdec.
    Qed.

    Lemma uniq_app_2 :
      uniq (E ++ F) -> uniq F.
    Proof.
      clear. intros H; induction E as [ | [x1 a1] E'].
        apply H.
        inversion H; subst. auto.
    Qed.

    Lemma uniq_app_3 :
      uniq (E ++ F) -> disjoint E F.
    Proof.
      clear. intros H. red. induction E as [ | [x1 a1] E'].
        fsetdec.
        inversion H; subst. simpl_alist in *. lapply IHE'.
          fsetdec.
          assumption.
    Qed.

    Lemma uniq_app_4 :
      uniq E ->
      uniq F ->
      disjoint E F ->
      uniq (E ++ F).
    Proof.
      clear. intros HE HF Hd.
      induction E as [ | [x1 a1] E']; simpl_alist in *.
        assumption.
        rewrite -> disjoint_app_l in Hd.
          inversion HE; subst. apply uniq_push.
            intuition.
            rewrite disjoint_one_l in Hd. simpl_alist. fsetdec.
    Qed.

    Lemma uniq_app :
      uniq (E ++ F) <-> uniq E /\ uniq F /\ disjoint E F.
    Proof.
      clear; intuition eauto using
        uniq_app_1, uniq_app_2, uniq_app_3, uniq_app_4.
    Qed.

    Lemma uniq_map_1 :
      uniq (map f E) ->
      uniq E.
    Proof.
      clear. intros H. induction E as [ | [x1 a1] E']; simpl_alist in *.
        apply uniq_nil.
        inversion H; subst. apply uniq_push; simpl_alist in *; auto.
    Qed.

    Lemma uniq_map_2 :
      uniq E ->
      uniq (map f E).
    Proof.
      clear. intros H. induction E as [ | [x1 a1] E']; simpl_alist in *.
        apply uniq_nil.
        inversion H; subst. apply uniq_push; simpl_alist in *; auto.
    Qed.

    Lemma uniq_map :
      uniq (map f E) <-> uniq E.
    Proof.
      clear. intuition eauto using uniq_map_1, uniq_map_2.
    Qed.

  End UniqProperties.

  Hint Rewrite
    disjoint_one_l disjoint_one_r
    disjoint_app_l disjoint_app_r
    disjoint_map_l disjoint_map_r
    uniq_app uniq_map
  : rewr_uniq.


  (* ********************************************************************* *)
  (** ** The [solve_uniq] tactic *)

  (** This tactic attempts to solve goals about [uniq].  Given its
      definition, it's likely to work only when the hypotheses in the
      goal already contain all the relevant [uniq] propositions.
      Thus, the tactic may not be generally useful.  It is useful,
      however, for proving facts about [uniq] such as the ones below.

      Implementation note: The second [simpl_alist] in the definition
      is because of [disjoint_one_{l,r}].  The "[|| fail]" at the end
      is so that in the case of failure, the error message reported to
      the user is not the one from [fsetdec]. *)

  Ltac solve_uniq :=
    try trivial;
    simpl_alist in *;
    autorewrite with rewr_uniq in *;
    simpl_alist in *;
    intuition (
      auto using uniq_nil, uniq_one ||
      (rewrite -> disjoint_sym; auto) ||
      (unfold disjoint in *; fsetdec))
    || fail.


  (* ********************************************************************* *)
  (** ** Facts about [uniq] *)

  Section UniqDerived.
    Variables A : Type.
    Variables x y : X.t.
    Variables a b : A.
    Variables E F G : list (X.t*A).

    Lemma uniq_cons :
      uniq E ->
      x `notin` dom E ->
      uniq ((x, a) :: E).
    Proof. clear. solve_uniq. Qed.

    Lemma uniq_insert_mid :
      uniq (G ++ E) ->
      x `notin` dom (G ++ E) ->
      uniq (G ++ (x ~ a) ++ E).
    Proof. clear. solve_uniq. Qed.

    Lemma uniq_remove_mid :
      uniq (E ++ F ++ G) ->
      uniq (E ++ G).
    Proof. clear. solve_uniq. Qed.

    Lemma uniq_map_app_l : forall (f : A -> A),
      uniq (F ++ E) ->
      uniq (map f F ++ E).
    Proof. clear. intros. solve_uniq. Qed.

    Lemma fresh_mid_tail :
      uniq (F ++ (x ~ a) ++ E) ->
      x `notin` dom E.
    Proof. clear. solve_uniq. Qed.

    Lemma fresh_mid_head :
      uniq (F ++ (x ~ a) ++ E) ->
      x `notin` dom E.
    Proof. clear. solve_uniq. Qed.

  End UniqDerived.


  (* ********************************************************************* *)
  (** ** Basic facts about [binds] *)

  (** The following lemmas are facts about [binds] with respect to the
      basic functions ([one] and [app]) that can be used to build
      association lists.

      Note: [map] is treated further below. *)

  Section BindsProperties.
    Variables A : Type.
    Variables x y : X.t.
    Variables a b : A.
    Variables E F G : list (X.t*A).

    Lemma binds_nil :
      binds x a nil <-> False.
    Proof. clear. split. inversion 1. intuition. Qed.

    Lemma binds_one_1 :
      x = y ->
      a = b ->
      binds x a (y ~ b).
    Proof. clear. intros. red. simpl. left. congruence. Qed.

    Lemma binds_one_2 :
      binds x a (y ~ b) ->
      x = y.
    Proof. clear. intros H1. inversion H1; intuition congruence. Qed.

    Lemma binds_one_3 :
      binds x a (y ~ b) ->
      a = b.
    Proof. clear. intros H1. inversion H1; intuition congruence. Qed.

    Lemma binds_one :
      binds x a (y ~ b) <-> x = y /\ a = b.
    Proof.
      clear. split.
        intros H1. intuition eauto using binds_one_2, binds_one_3.
        intros H1. intuition auto using binds_one_1.
    Qed.

    Lemma binds_app_1 :
      binds x a E ->
      binds x a (E ++ F).
    Proof. clear. intros H. red in H |- *. rewrite -> in_app. auto. Qed.

    Lemma binds_app_2 :
      binds x a F ->
      binds x a (E ++ F).
    Proof. clear. intros H. red in H |- *. rewrite -> in_app. auto. Qed.

    Lemma binds_app_3 :
      binds x a (E ++ F) ->
      binds x a E \/ binds x a F.
    Proof.
      clear. induction E as [ | [x1 a1] E' ].
        auto.
        unfold binds. simpl. intros [H | H].
          inversion H; subst. auto.
          unfold binds in *. apply IHE' in H. intuition.
    Qed.

    Lemma binds_app :
      binds x a (E ++ F) <-> binds x a E \/ binds x a F.
    Proof.
      clear. intuition auto using binds_app_1, binds_app_2, binds_app_3.
    Qed.

  End BindsProperties.

  Hint Rewrite binds_nil binds_one binds_app : rewr_binds.
  Hint Rewrite binds_nil binds_one : rewr_binds_uniq.


  (* ********************************************************************* *)
  (** ** Additional lemmas and tactics for working with [binds] *)

  Section MoreBindsProperties.
    Variables A : Type.
    Variables x y : X.t.
    Variables a b : A.
    Variables E F G : list (X.t*A).

    Lemma binds_dom_contradiction: forall (E : list (X.t*A)),
      binds x a E ->
      x `notin` dom E ->
      False.
    Proof.
      clear. induction E as [ | [x1 a1] E' ]; simpl.
        intros H. inversion H.
        unfold binds in *. simpl. intros [H | H] J.
          inversion H; subst. fsetdec.
          apply IHE' in H. trivial. fsetdec.
    Qed.

    Lemma binds_app_uniq :
      uniq (E ++ F) ->
      (binds x a (E ++ F) <->
        (binds x a E /\ x `notin` dom F) \/
        (binds x a F /\ x `notin` dom E)).
    Proof with intuition (fsetdec || eauto using binds_dom_contradiction).
      clear. intros H1.
      autorewrite with rewr_uniq in H1. unfold disjoint in H1.
      assert (H : x `notin` dom F \/ x `notin` dom E) by fsetdec.
      rewrite binds_app...
    Qed.

  End MoreBindsProperties.

  Hint Rewrite binds_app_uniq using solve_uniq : rewr_binds_uniq.


  (** The [apply_binds_dom_contradiction] tactic solves a goal by
      applying the [binds_dom_contradiction] lemma.  The tactic
      succeeds only if the the hypotheses of the lemma are immediately
      satisfied. *)

  Ltac apply_binds_dom_contradiction :=
    match goal with
      | H : binds ?x ?a ?E, J : ?x `notin` (dom ?E) |- _ =>
        assert False by apply (@binds_dom_contradiction _ _ _ _ H J);
        intuition
      | H : binds ?x ?a ?E, J : ?x `in` (dom ?E) -> False |- _ =>
        assert False by apply (@binds_dom_contradiction _ _ _ _ H J);
        intuition
    end.


  (** The [solve_binds] tactic attempts to solve goals about [binds].
      Given its definition, it's likely to work only when the
      hypotheses in the goal already contain all the relevant [binds]
      propositions.  Thus, the tactic may not be generally useful.  It
      is useful, however, for proving facts about [binds] such as the
      ones below. *)

  Ltac solve_binds :=
    simpl_alist in *;
    autorewrite with rewr_binds in *;
    intuition (auto || fsetdec || apply_binds_dom_contradiction)
    || fail.


  (** The tactics [analyze_binds] and [analyze_binds_uniq] tactics
      take as an argument a hypotheses about [binds] and perform a
      case analysis based on the structure of the association list.
      In the case of [analyze_binds_uniq], the analysis is performed
      assuming that the association list is [uniq].  The lemmas
      [binds_app] and [binds_app_uniq] are examples of such case
      analysis.

      Implementation notes:

        - The initial calls to [simpl_alist] put the relevant
          association lists into normal form.
        - In the case of [binds_app_uniq], we assert that the
          association list is [uniq].  This enables the [autorewrite]
          step to succeed.
        - Rather than work on [H] itself, we copy it and work on the
          copy.  Thus, in instances where the analysis leaves unsolved
          subgoals, it is still possible to see the original
          hypothesis.
        - The rest of the tactic breaks apart the copy of H and tries
          several simple means for solving the resulting subgoals. *)

  Ltac analyze_binds H :=
    simpl_alist;
    simpl_alist in H;
    match type of H with
      | binds ?x ?a ?E =>
        let J := fresh in
        pose proof H as J;
        autorewrite with rewr_binds in J;
        simpl_alist in J;
        try (progress decompose [and or] J; clear J);
        try solve [trivial | discriminate | intuition | fsetdec]
    end.

  Ltac analyze_binds_uniq H :=
    simpl_alist;
    simpl_alist in H;
    match type of H with
      | binds ?x ?a ?E =>
        match goal with
          | H : uniq ?E |- _ => idtac
          | _ => assert (uniq E); [ try solve_uniq | ]
        end;
        let J := fresh in
        pose proof H as J;
        autorewrite with rewr_binds_uniq in J;
        simpl_alist in J;
        try (progress decompose [and or] J; clear J);
        try solve [trivial | discriminate | intuition | fsetdec]
    end.


  (* ********************************************************************* *)
  (** ** Facts about [binds] *)

  Section BindsDerived.
    Variables A B : Type.
    Variables f : A -> B.
    Variables x y : X.t.
    Variables a b : A.
    Variables E F G : list (X.t*A).

    Lemma binds_dec :
      (forall a b : A, {a = b} + {a <> b}) ->
      {binds x a E} + {~ binds x a E}.
    Proof.
      intros. unfold binds. apply List.In_dec.
      decide equality.
      apply E.eq_dec.
    Qed.

    Lemma binds_lookup_dec :
      decidable (exists a, binds x a E).
    Proof.
      clear. unfold decidable. induction E as [ | [x1 a1] E' ].
        right. intros [x' H]. inversion H.
        destruct IHE' as [[a' H] | H].
          left. exists a'. solve_binds.
          destruct (E.eq_dec x x1); unfold E.eq in *.
            left. exists a1. solve_binds.
            right. intros [a' J]. unfold binds in *; simpl in *.
              destruct J as [K | K].
                inversion K. intuition.
                apply H. exists a'. auto.
    Qed.

    Lemma binds_lookup_dec_specif :
      {a : A | binds x a E} + (forall a, ~ binds x a E).
    Proof.
      clear. induction E as [ | [x1 a1] E' ].
        right. intros a' H. inversion H.
        destruct IHE' as [[a' H] | H].
          left. exists a'. solve_binds.
          destruct (E.eq_dec x x1); unfold E.eq in *.
            left. exists a1. solve_binds.
            right. intros a' J. unfold binds in *; simpl in *.
              destruct J as [K | K].
                inversion K. intuition.
                apply H with (a := a'). auto.
    Qed.

    Lemma binds_map :
      binds x a E ->
      binds x (f a) (map f E).
    Proof.
      clear. induction E as [ | [x1 a1] E' ]; simpl; intros H.
        analyze_binds H.
        analyze_binds H.
          left. congruence.
          solve_binds.
    Qed.

    Lemma binds_map_inv :
      (forall a b, f a = f b -> a = b) ->
      binds x (f a) (map f E) ->
      binds x a E.
    Proof.
      clear. induction E as [ | [x1 a1] E' ]; simpl; intros J H.
        analyze_binds H.
        analyze_binds H.
          left. f_equal; auto.
          solve_binds.
    Qed.

    Lemma binds_weaken :
      binds x a (E ++ G) ->
      binds x a (E ++ F ++ G).
    Proof. clear. intros. solve_binds. Qed.

    Lemma binds_mid_eq :
      binds x a (F ++ (x ~ b) ++ E) ->
      uniq (F ++ (x ~ b) ++ E) ->
      a = b.
    Proof. clear. intros. analyze_binds_uniq H. Qed.

    Lemma binds_remove_mid :
      binds x a (F ++ (y ~ b) ++ G) ->
      x <> y ->
      binds x a (F ++ G).
    Proof. clear. intros. solve_binds. Qed.

    Lemma binds_In : forall x a (E : list (X.t*A)),
      binds x a E ->
      x `in` dom E.
    Proof.
      clear. intros x' a' E'.
      induction E' as [ | [x1 a1] E' ]; intros H; analyze_binds H.
    Qed.

    Lemma binds_unique :
      binds x a E ->
      binds x b E ->
      uniq E ->
      a = b.
    Proof.
      clear. induction E as [ | [x1 a1] E' ].
        inversion 1.
        unfold binds. simpl. intros [H | H] [J | J] K.
          Case "left / left".
            congruence.
          Case "left / right".
            inversion K; subst.
            assert (x `in` dom E'). eapply binds_In. unfold binds. apply J.
            inversion H; subst.
            intuition.
          Case "right / left".
            inversion K; subst.
            assert (x `in` dom E'). eapply binds_In. unfold binds. apply H.
            inversion J; subst.
            intuition.
          Case "right / right".
            unfold binds in *.
            apply IHE'; eauto.
            inversion K; auto.
    Qed.

    Lemma fresh_app_l :
      uniq (F ++ E) ->
      binds x a E ->
      x `notin` dom F.
    Proof.
      clear. intros.
      assert (x `in` dom E) by eauto using binds_In.
      solve_uniq.
    Qed.

    Lemma fresh_app_r :
      uniq (F ++ E) ->
      binds x a F ->
      x `notin` dom E.
    Proof.
      clear. intros.
      assert (x `in` dom F) by eauto using binds_In.
      solve_uniq.
    Qed.

  End BindsDerived.

End Make.
