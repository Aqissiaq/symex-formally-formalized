(** * Expressions *)

(** Doing the expressions in their own file to avoid some clutter and facilitate reuse
*)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

Module BasicExpr.
  Inductive Aexpr : Type :=
  | AConst (n:nat)
  | AVar (x:string)
  | APlus (a1 a2:Aexpr)
  | AIte (b:Bexpr) (a1 a3:Aexpr)
  with Bexpr : Type :=
  | BTrue
  | BFalse
  | BNot (b:Bexpr)
  | BAnd (b1 b2:Bexpr)
  | BOr (b1 b2:Bexpr)
  | BLeq (a1 a2:Aexpr).

  Scheme expr_aexpr_rec := Induction for Aexpr Sort Prop
    with expr_bexpr_rec := Induction for Bexpr Sort Prop.
  Combined Scheme aexpr_bexpr_mutind from expr_aexpr_rec, expr_bexpr_rec.

  Coercion AVar : string >-> Aexpr.
  Coercion AConst : nat >-> Aexpr.

  Declare Custom Entry com.
  Declare Scope com_scope.

  Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
  Notation "( x )" := x (in custom com, x at level 99) : com_scope.
  Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
  Notation "x + y"   := (APlus x y) (in custom com at level 70, no associativity).
  Notation "x <= y"  := (BLeq x y) (in custom com at level 70, no associativity).
  Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).
  Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
  Notation "x | y"  := (BOr x y) (in custom com at level 80, left associativity).

  Definition X : string := "x".
  Definition Y : string := "y".
  Definition Z : string := "z".

End BasicExpr.
