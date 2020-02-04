(* Copyright (c) 2008 University of Pennsylvania PLClub

   This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   $Id: AtomEnv.v 2202 2008-07-17 16:29:38Z baydemir $ *)

Require Import Decidable.
Require Import FSetWeak.
Require Import List.

Require Import AdditionalTactics.
Require Import ListFacts.
Require Import FSetWeakDecide.
Require Import AssocList.
Require Import Atom.
Require Import AtomSet.
Import AtomSetImpl.


(* *********************************************************************** *)
(** * Signature *)

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
    associated to the left).  The [simpl_env] and [rewrite_env]
    tactics below are designed to minimize the impact of these
    downsides.

    We have considered other alternative implementations, but the scheme
    described above seems to work the best in practice. *)



Module Type ENVIRONMENT.


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

    Definition map (f : A -> B) (E : list (atom*A)) : list (atom*B) :=
      List.map (fun b => match b with (x, a) => (x, f a) end) E.

    Fixpoint dom (A : Type) (E : list (atom*A)) {struct E} : atoms :=
      match E with
        | nil => empty
        | (x, _) :: E' => add x (dom E')
      end.

    Definition disjoint (E : list (atom*A)) (F : list (atom*B)) : Prop :=
      Subset (inter (dom E) (dom F)) empty.

    Definition binds (x : atom) (a : A) (E : list (atom*A)) : Prop :=
      List.In (x, a) E.

    Notation Local "x ~ a" := (one (x, a)) (at level 68).
    Notation Local "x `notin` E" := (~ AtomSetImpl.In x E) (at level 69).

    Inductive uniq : list (atom*A) -> Prop :=
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
     (AtomSetImpl.union E F) (at level 69, right associativity).
  Notation Local "x `in` E" :=
     (AtomSetImpl.In x E) (at level 69).
  Notation Local "x `notin` E" :=
     (~ AtomSetImpl.In x E) (at level 69).
  Notation Local "E [=] F" :=
     (AtomSetImpl.Equal E F) (at level 70, no associativity).
  Notation Local "E [<=] F" :=
     (AtomSetImpl.Subset E F) (at level 70, no associativity).


  (* ********************************************************************* *)
  (** ** List properties *)

  (** The following block of properties is used mainly for rewriting
      association lists into the normal form described above.  See the
      [simpl_env] and [rewrite_env] tactics below. *)

  Section ListProperties.
    Variables X : Type.
    Variables x y : X.
    Variables l l1 l2 l3 : list X.

    Axiom cons_app_one :
      cons x l = [ x ] ++ l.

    Axiom cons_app_assoc :
      (cons x l1) ++ l2 = cons x (l1 ++ l2).

    Axiom app_assoc :
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).

    Axiom app_nil_1 :
      nil ++ l = l.

    Axiom app_nil_2 :
      l ++ nil = l.

    Axiom in_one :
      List.In x [ y ] <-> x = y.

    Axiom in_app :
      List.In x (l1 ++ l2) <-> List.In x l1 \/ List.In x l2.

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

    Axiom one_eq_app :
      [ x ] ++ l1 = l2 ++ l3 ->
      (exists qs, l2 = x :: qs /\ l1 = qs ++ l3) \/
      (l2 = nil /\ l3 = x :: l1).

    Axiom app_eq_one :
      l2 ++ l3 = [ x ] ++ l1 ->
      (exists qs, l2 = x :: qs /\ l1 = qs ++ l3) \/
      (l2 = nil /\ l3 = x :: l1).

    Axiom nil_neq_one_mid :
      nil <> l1 ++ [ x ] ++ l2.

    Axiom one_mid_neq_nil :
      l1 ++ [ x ] ++ l2 <> nil.

  End AssortedListProperties.


  (* ********************************************************************* *)
  (** ** Properties of [map] and [dom] *)

  (** The following lemmas are used mainly to simplify applications of
      [map] and [dom] to association lists.  See also the [simpl_env]
      and [rewrite_env] tactics below. *)

  Section Properties.
    Variables A B : Type.
    Variables f : A -> B.
    Variables x : atom.
    Variables b : A.
    Variables E F G : list (atom*A).

    Axiom map_nil :
      map f nil = nil.

    Axiom map_cons :
      map f ((x, b) :: E) = (x, f b) :: map f E.

    Axiom map_one :
      map f (x ~ b) = (x ~ f b).

    Axiom map_app :
      map f (E ++ F) = map f E ++ map f F.

    Axiom dom_nil :
      (@dom A nil) = empty.

    Axiom dom_cons :
      dom ((x, b) :: E) [=] singleton x `union` dom E.

    Axiom dom_one :
      dom (x ~ b) [=] singleton x.

    Axiom dom_app :
      dom (E ++ F) [=] dom E `union` dom F.

    Axiom dom_map :
      dom (map f E) [=] dom E.

  End Properties.

  Hint Rewrite map_nil map_cons map_one map_app : rewr_map.
  Hint Rewrite dom_nil dom_cons dom_one dom_app dom_map : rewr_dom.


  (* ********************************************************************* *)
  (** ** The [simpl_env] tactic *)

  (** The [simpl_env] tactic rewrites association lists so that they
      are in the normal form described above.  Similar to the [simpl]
      tactic, we define "[in *]" and "[in H]" variants of the tactic. *)

  Ltac simpl_env :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom.
  Tactic Notation "simpl_env" "in" hyp(H) :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom in H.
  Tactic Notation "simpl_env" "in" "*" :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom in *.


  (* ********************************************************************* *)
  (** ** The [rewrite_env] tactic *)

  (** The tactic [(rewrite_env E)] replaces an association list in
      the conclusion of the goal with [E].  Suitability for
      replacement is determined by whether [simpl_env] can put [E]
      and the chosen environment in the same normal form, up to
      convertibility's in Coq.  We also define an "[in H]" variant
      that performs the replacement in a hypothesis [H].  *)

  Tactic Notation "rewrite_env" constr(E) :=
    match goal with
      | |- context[?x] =>
        change x with E
      | |- context[?x] =>
        replace x with E;
          [ | try reflexivity; simpl_env; reflexivity ]
    end.

  Tactic Notation "rewrite_env" constr(E) "in" hyp(H) :=
    match type of H with
      | context[?x] =>
        change x with E in H
      | context[?x] =>
        replace x with E in H;
          [ | try reflexivity; simpl_env; reflexivity ]
    end.


  (* ********************************************************************* *)
  (** ** Basic facts about [disjoint] *)

  Section BasicDisjointFacts.
    Implicit Types A B C : Type.

    Axiom disjoint_sym_1 :
      forall A B (E : list (atom*A)) (F : list (atom*B)),
        disjoint E F ->
        disjoint F E.

    Axiom disjoint_sym :
      forall A B (E : list (atom*A)) (F : list (atom*B)),
      disjoint E F <-> disjoint F E.

    Axiom disjoint_one_1 :
      forall A B (x : atom) (a : A) (F : list (atom*B)),
      disjoint (x ~ a) F ->
      x `notin` dom F.

    Axiom disjoint_one_2 :
      forall A B (x : atom) (a : A) (F : list (atom*B)),
      x `notin` dom F ->
      disjoint (x ~ a) F.

    Axiom disjoint_one_l :
      forall A B (x : atom) (a : A) (E : list (atom*B)),
      disjoint (x ~ a) E <-> x `notin` dom E.

    Axiom disjoint_one_r :
      forall A B (x : atom) (a : A) (E : list (atom*B)),
      disjoint E (x ~ a) <-> x `notin` dom E.

    Axiom disjoint_app_1 :
      forall A B (E F : list (atom*A)) (G : list (atom*B)),
      disjoint (E ++ F) G ->
      disjoint E G.

    Axiom disjoint_app_2 :
      forall A B (E F : list (atom*A)) (G : list (atom*B)),
      disjoint (E ++ F) G ->
      disjoint F G.

    Axiom disjoint_app_3 :
      forall A B (E F : list (atom*A)) (G : list (atom*B)),
      disjoint E G ->
      disjoint F G ->
      disjoint (E ++ F) G.

    Axiom disjoint_app_l :
      forall A B (E F : list (atom*A)) (G : list (atom*B)),
      disjoint (E ++ F) G <-> disjoint E G /\ disjoint F G.

    Axiom disjoint_app_r :
      forall A B (E F : list (atom*A)) (G : list (atom*B)),
      disjoint G (E ++ F) <-> disjoint E G /\ disjoint F G.

    Axiom disjoint_map_1 :
      forall A B C (E : list (atom*A)) (F : list (atom*B)) (f : A -> C),
      disjoint (map f E) F ->
      disjoint E F.

    Axiom disjoint_map_2 :
      forall A B C (E : list (atom*A)) (F : list (atom*B)) (f : A -> C),
      disjoint E F ->
      disjoint (map f E) F.

    Axiom disjoint_map_l :
      forall A B C (E : list (atom*A)) (F : list (atom*B)) (f : A -> C),
      disjoint (map f E) F <-> disjoint E F.

    Axiom disjoint_map_r :
      forall A B C (E : list (atom*A)) (F : list (atom*B)) (f : A -> C),
      disjoint F (map f E) <-> disjoint E F.

  End BasicDisjointFacts.


  (* ********************************************************************* *)
  (** ** Basic facts about [uniq] *)

  (** The following lemmas are facts about [uniq] with respect to the
      basic functions ([one], [app], and [map]) that can be used to
      build association lists. *)

  Section UniqProperties.
    Variables A B : Type.
    Variables f : A -> B.
    Variables x : atom.
    Variables b : A.
    Variables E F G : list (atom*A).

    Axiom uniq_one :
      uniq (x ~ b).

    Axiom uniq_app_1 :
      uniq (E ++ F) -> uniq E.

    Axiom uniq_app_2 :
      uniq (E ++ F) -> uniq F.

    Axiom uniq_app_3 :
      uniq (E ++ F) -> disjoint E F.

    Axiom uniq_app_4 :
      uniq E ->
      uniq F ->
      disjoint E F ->
      uniq (E ++ F).

    Axiom uniq_app :
      uniq (E ++ F) <-> uniq E /\ uniq F /\ disjoint E F.

    Axiom uniq_map_1 :
      uniq (map f E) ->
      uniq E.

    Axiom uniq_map_2 :
      uniq E ->
      uniq (map f E).

    Axiom uniq_map :
      uniq (map f E) <-> uniq E.

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

      Implementation note: The second [simpl_env] in the definition
      is because of [disjoint_one_{l,r}].  The "[|| fail]" at the end
      is so that in the case of failure, the error message reported to
      the user is not the one from [atomsetdec]. *)

  Ltac solve_uniq :=
    try trivial;
    simpl_env in *;
    autorewrite with rewr_uniq in *;
    simpl_env in *;
    intuition (
      auto using uniq_nil, uniq_one ||
      (rewrite -> disjoint_sym; auto) ||
      (unfold disjoint in *; atomsetdec))
    || fail.


  (* ********************************************************************* *)
  (** ** Facts about [uniq] *)

  Section UniqDerived.
    Variables A : Type.
    Variables x y : atom.
    Variables a b : A.
    Variables E F G : list (atom*A).

    Axiom uniq_cons :
      uniq E ->
      x `notin` dom E ->
      uniq ((x, a) :: E).

    Axiom uniq_insert_mid :
      uniq (G ++ E) ->
      x `notin` dom (G ++ E) ->
      uniq (G ++ (x ~ a) ++ E).

    Axiom uniq_remove_mid :
      uniq (E ++ F ++ G) ->
      uniq (E ++ G).

    Axiom uniq_map_app_l : forall (f : A -> A),
      uniq (F ++ E) ->
      uniq (map f F ++ E).

    Axiom fresh_mid_tail :
      uniq (F ++ (x ~ a) ++ E) ->
      x `notin` dom E.

    Axiom fresh_mid_head :
      uniq (F ++ (x ~ a) ++ E) ->
      x `notin` dom E.

  End UniqDerived.


  (* ********************************************************************* *)
  (** ** Basic facts about [binds] *)

  (** The following lemmas are facts about [binds] with respect to the
      basic functions ([one] and [app]) that can be used to build
      association lists.

      Note: [map] is treated further below. *)

  Section BindsProperties.
    Variables A : Type.
    Variables x y : atom.
    Variables a b : A.
    Variables E F G : list (atom*A).

    Axiom binds_nil :
      binds x a nil <-> False.

    Axiom binds_one_1 :
      x = y ->
      a = b ->
      binds x a (y ~ b).

    Axiom binds_one_2 :
      binds x a (y ~ b) ->
      x = y.

    Axiom binds_one_3 :
      binds x a (y ~ b) ->
      a = b.

    Axiom binds_one :
      binds x a (y ~ b) <-> x = y /\ a = b.

    Axiom binds_app_1 :
      binds x a E ->
      binds x a (E ++ F).

    Axiom binds_app_2 :
      binds x a F ->
      binds x a (E ++ F).

    Axiom binds_app_3 :
      binds x a (E ++ F) ->
      binds x a E \/ binds x a F.

    Axiom binds_app :
      binds x a (E ++ F) <-> binds x a E \/ binds x a F.

  End BindsProperties.

  Hint Rewrite binds_nil binds_one binds_app : rewr_binds.
  Hint Rewrite binds_nil binds_one : rewr_binds_uniq.


  (* ********************************************************************* *)
  (** ** Additional lemmas and tactics for working with [binds] *)

  Section MoreBindsProperties.
    Variables A : Type.
    Variables x y : atom.
    Variables a b : A.
    Variables E F G : list (atom*A).

    Axiom binds_dom_contradiction: forall (E : list (atom*A)),
      binds x a E ->
      x `notin` dom E ->
      False.

    Axiom binds_app_uniq :
      uniq (E ++ F) ->
      (binds x a (E ++ F) <->
        (binds x a E /\ x `notin` dom F) \/
        (binds x a F /\ x `notin` dom E)).

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
    simpl_env in *;
    autorewrite with rewr_binds in *;
    intuition (auto || atomsetdec || apply_binds_dom_contradiction)
    || fail.


  (** The tactics [analyze_binds] and [analyze_binds_uniq] tactics
      take as an argument a hypotheses about [binds] and perform a
      case analysis based on the structure of the association list.
      In the case of [analyze_binds_uniq], the analysis is performed
      assuming that the association list is [uniq].  The lemmas
      [binds_app] and [binds_app_uniq] are examples of such case
      analysis.

      Implementation notes:

        - The initial calls to [simpl_env] put the relevant
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
    simpl_env;
    simpl_env in H;
    match type of H with
      | binds ?x ?a ?E =>
        let J := fresh in
        pose proof H as J;
        autorewrite with rewr_binds in J;
        simpl_env in J;
        try (progress decompose [and or] J; clear J);
        try solve [trivial | discriminate | intuition | atomsetdec]
    end.

  Ltac analyze_binds_uniq H :=
    simpl_env;
    simpl_env in H;
    match type of H with
      | binds ?x ?a ?E =>
        match goal with
          | H : uniq ?E |- _ => idtac
          | _ => assert (uniq E); [ try solve_uniq | ]
        end;
        let J := fresh in
        pose proof H as J;
        autorewrite with rewr_binds_uniq in J;
        simpl_env in J;
        try (progress decompose [and or] J; clear J);
        try solve [trivial | discriminate | intuition | atomsetdec]
    end.


  (* ********************************************************************* *)
  (** ** Facts about [binds] *)

  Section BindsDerived.
    Variables A B : Type.
    Variables f : A -> B.
    Variables x y : atom.
    Variables a b : A.
    Variables E F G : list (atom*A).

    Axiom binds_dec :
      (forall a b : A, {a = b} + {a <> b}) ->
      {binds x a E} + {~ binds x a E}.

    Axiom binds_lookup_dec :
      decidable (exists a, binds x a E).

    Axiom binds_lookup_dec_specif :
      {a : A | binds x a E} + (forall a, ~ binds x a E).

    Axiom binds_map :
      binds x a E ->
      binds x (f a) (map f E).

    Axiom binds_map_inv :
      (forall a b, f a = f b -> a = b) ->
      binds x (f a) (map f E) ->
      binds x a E.

    Axiom binds_weaken :
      binds x a (E ++ G) ->
      binds x a (E ++ F ++ G).

    Axiom binds_mid_eq :
      binds x a (F ++ (x ~ b) ++ E) ->
      uniq (F ++ (x ~ b) ++ E) ->
      a = b.

    Axiom binds_remove_mid :
      binds x a (F ++ (y ~ b) ++ G) ->
      x <> y ->
      binds x a (F ++ G).

    Axiom binds_In : forall x a (E : list (atom*A)),
      binds x a E ->
      x `in` dom E.

    Axiom binds_unique :
      binds x a E ->
      binds x b E ->
      uniq E ->
      a = b.

    Axiom fresh_app_l :
      uniq (F ++ E) ->
      binds x a E ->
      x `notin` dom F.

    Axiom fresh_app_r :
      uniq (F ++ E) ->
      binds x a F ->
      x `notin` dom E.

  End BindsDerived.

End ENVIRONMENT.


(* ********************************************************************** *)
(** * Module instantiation *)

(** We can use our implementation of association lists (in [AssocList]) to
    implement a module with the above signature.   Note that the tactics
    provided end in [_env], not [_alist] as the implementation of
    [AssocList.Make] might suggest.  (Tactics do not need to agree between a
    module's signature and its implementaiton.) *)

Module AtomEnvImpl : ENVIRONMENT := AssocList.Make AtomImpl AtomSetImpl.
