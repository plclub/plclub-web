(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Coq.Lists.List.

(* Converted imports: *)

Module GHC.
  Module List.
    Definition reverse {a} (xs : list a) := List.rev xs.
    Lemma hs_coq_reverse {a} (xs : list a) : reverse xs = List.rev xs.
    Proof. reflexivity. Qed.
  End List.
End GHC.

(* Converted type declarations: *)

Inductive Queue a : Type
  := | MkQueue (front : list a) (back : list a) : Queue a.

Arguments MkQueue {_} _ _.

Definition back {a} (arg_0__ : Queue a) :=
  let 'MkQueue _ back := arg_0__ in
  back.

Definition front {a} (arg_0__ : Queue a) :=
  let 'MkQueue front _ := arg_0__ in
  front.

(* Converted value declarations: *)

Definition push {a} : a -> Queue a -> Queue a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, MkQueue front back => MkQueue front (cons x back)
    end.

Definition pop {a} : Queue a -> option (a * Queue a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | MkQueue (cons y front) back => Some (pair y (MkQueue front back))
    | MkQueue nil back =>
        match GHC.List.reverse back with
        | nil => None
        | cons y front => Some (pair y (MkQueue front nil))
        end
    end.

Definition empty {a} : Queue a :=
  MkQueue nil nil.

(* External variables:
     None Some cons list nil op_zt__ option pair GHC.List.reverse
*)
