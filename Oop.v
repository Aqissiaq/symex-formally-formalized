(** * 4. Object Orientation *)

(** We next extend the language of the previous section with object-oriented features. We first introduce a distinction
between variables x , y, . . . , e.g., the formal parameters of methods, including the keyword this, and fields f , f ′, . . .
(of the classes of a program)

 I am less interested in OOP and more in trace semantics*)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Program.   (* for `dependent induction` *)
From Coq Require Import Relations.

From SymEx Require Import Expr.
From SymEx Require Import Maps.

Inductive Oexpr : Type :=
| PNil
| PThis
| PVar (h:Heap)
| PCond (b:Bexpr) (e1 e2:Oexpr)
with Heap :=
| HVar (x:string)
| HExpr (e:Oexpr) (f:string)
with  Bexpr  :=
| BTrue
| BFalse
| BNot (b:Bexpr)
| BAnd (b1 b2:Bexpr)
| BEq (e1 e2:Oexpr).

Definition r : Oexpr := PVar (HVar "r").

Inductive Stmt : Type :=
| SAsgn (h:Heap) (e:Oexpr)
| SNew (h:Heap) (C:Class)
| SMethod (h:Heap) (m:Class) (e0:Oexpr)
| SReturn (e:Oexpr)
| SSeq (s1 s2:Stmt)
| SIf (b:Bexpr) (s1 s2:Stmt)
| SLoop (b:Bexpr) (s:Stmt)
  with Class : Type :=
  (*just one method with no parameters per class for now*)
  | CDec (body:Stmt).

Open Scope com_scope.

Notation "x '==' y" := (BEq x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "'if' b 'then' e1 'else' e2 'fi'" := (PCond b e1 e2)
           (in custom com at level 89, b at level 99,
            e1 at level 99, e2 at level 99) : com_scope.
Notation "e '->' f" := (HExpr e f) : com_scope.
Notation "'nil'" := PNil : com_scope.
Notation "'this'" := PThis : com_scope.
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).

Notation "x := y"  :=
         (SAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "h ':=' 'new' C" := (SNew h C)
            (in custom com at level 0, h constr at level 0,
             C at level 85, no associativity) : com_scope.
Notation "h '<-' m '(' e ')'" := (SMethod h m e)
            (in custom com at level 0, h constr at level 0,
             m at level 80, no associativity) : com_scope.
Notation "'return' e" := (SReturn e) (in custom com at level 85) : com_scope.
Notation "x ; y" :=
         (SSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x '{' y '}' '{' z '}'" :=
         (SIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x '{' y '}'" :=
         (SLoop x y)
           (in custom com at level 89, x at level 99,
               y at level 99) : com_scope.
Notation "'class' '{' b '}'"  :=
         (CDec b)
            (in custom com at level 0,
                b at level 85, no associativity) : com_scope.

Fixpoint Oexpr_subst (e e0:Oexpr) : Oexpr :=
  match e with
  | PNil => PNil
  | PThis => e0
  | PVar (HExpr e' f) => Oexpr_subst e' e0
  | PVar x => PVar x
  | PCond b e1 e2 => PCond (Bexpr_subst b e0) (Oexpr_subst e1 e0) (Oexpr_subst e2 e0)
  end
  with Bexpr_subst (b:Bexpr) (e0:Oexpr) : Bexpr :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b => BNot (Bexpr_subst b e0)
  | BAnd b1 b2 => BAnd (Bexpr_subst b1 e0) (Bexpr_subst b2 e0)
  | BEq e1 e2 => BEq (Oexpr_subst e1 e0) (Oexpr_subst e2 e0)
  end.

Fixpoint Heap_subst (h:Heap) (e0:Oexpr) : Heap :=
  match h with
  | HVar x => HVar x
  | HExpr e f => HExpr (Oexpr_subst e e0) f
  end.

Fixpoint method_subst (body:Stmt) (e0:Oexpr) : Stmt :=
  match body with
  | SAsgn h e => SAsgn (Heap_subst h e0) (Oexpr_subst e e0)
  | SNew h C => SNew (Heap_subst h e0) C
  | SMethod h m e'0 => SMethod (Heap_subst h e0) m (Oexpr_subst e'0 e0)
  | SReturn e => SReturn (Oexpr_subst e e0)
  | SSeq s1 s2 => SSeq (method_subst s1 e0) (method_subst s2 e0)
  | SIf b s1 s2 => SIf (Bexpr_subst b e0) (method_subst s1 e0) (method_subst s2 e0)
  | SLoop b s => SLoop (Bexpr_subst b e0) (method_subst s e0)
  end.

Definition TraceStep : Type := (Bexpr + (Heap * Class) + (Heap * Oexpr)).

Definition pc : Bexpr -> TraceStep :=
  fun b => inl (inl b).
Definition new : (Heap * Class) -> TraceStep :=
  fun x => inl (inr x).
Definition asgn : (Heap * Oexpr) -> TraceStep :=
  fun x => inr x.

Open Scope list_scope.
Definition Trace : Type := list TraceStep.

Definition SState : Type := Stmt * Trace.

Reserved Notation " c '->s' c' " (at level 40).

Inductive Sstep : relation SState :=
| SAsgn_step : forall h e s p,
    (<{ h := e ; s }>, p) ->s (s, asgn (h, e) :: p)
| SNew_step : forall h C s p x,
    (*maybe an "x fresh" condition here*)
    (<{ h := new C ; s }>, p) ->s (s, asgn (h, PVar x) :: new (x, C) :: p)
| SMethod_step : forall h e0 s s' p,
    (<{ h <- class { s } (e0) ; s'}>, p)
    ->s (SSeq (method_subst s e0) <{ h := r ; s'}>, pc (BNot (BEq e0 PNil)):: p)
  where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40).
