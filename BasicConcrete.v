(** * 2. Basic Symbolic Execution *)

(** We introduce a formal model of symbolic execution for a basic programming
language with a statically fixed number of programming variables. A configuration of the symbolic transition
system consists of the program statement to be executed, a substitution, and a path condition. Correctness then
states that for every reachable symbolic configuration and state which satisfies the path condition, there exists a
corresponding concrete execution. Conversely, completeness states that for every concrete execution there exists
a corresponding symbolic configuration such that the initial state of the concrete execution satisfies the path
condition and its final state can be obtained as a composition of the initial state and the generated substitution.
 *)

(** This file contains a second take, trying to move more elegantly between symbolic and concrete states
 by being less general *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From SymEx Require Import BinaryRelation.

Inductive Aexpr : Type :=
| AConst (n:nat)
| AVar (x:string)
| APlus (a1 a2:Aexpr).

Inductive Bexpr : Type :=
| BTrue
| BFalse
| BVar (x:string)
| BNot (b:Bexpr)
| BAnd (b1 b2:Bexpr)
| BLeq (a1 a2:Aexpr).

Coercion AVar : string >-> Aexpr.
Coercion AConst : nat >-> Aexpr.
Coercion BVar : string >-> Bexpr.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 70, no associativity).
Notation "x <= y"   := (BLeq x y) (in custom com at level 70, no associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".

Inductive Stmt : Type :=
| SSkip
| SAsgn (x:string) (e:Aexpr)
| SSeq (s1 s2:Stmt)
| SIf (b:Bexpr) (s1 s2:Stmt).

Notation "'skip'" := SSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (SAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (SSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x '{' y '}' '{' z '}'" :=
         (SIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Open Scope com_scope.

Definition Asub : Type := string -> Aexpr.
Definition Aid_sub : Asub := fun x => x.
Fixpoint Aapply (s:Asub) (e:Aexpr) : Aexpr :=
  match e with
  | AConst n => AConst n
  | AVar x => s x
  | APlus a1 a2 => APlus (Aapply s a1) (Aapply s a2)
  end.

Lemma Aid_id : forall e,
    Aapply Aid_sub e = e.
Proof.
  induction e; try reflexivity.
  simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Definition Bsub : Type := string -> Bexpr.
Definition Bid_sub : Bsub := fun x => x.
Fixpoint Bapply (s:Bsub) (s':Asub) (e:Bexpr) : Bexpr :=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | BVar x => s x
  | BNot b => BNot (Bapply s s' b)
  | BAnd b1 b2 => BAnd (Bapply s s' b1) (Bapply s s' b2)
  | BLeq a1 a2 => BLeq (Aapply s' a1) (Aapply s' a2)
  end.

Definition update {E:Type} (s: string -> E) (x:string) (e:E) : string -> E :=
  fun y => if String.eqb x y then e else s x.

Lemma Bid_id : forall e,
    Bapply Bid_sub Aid_sub e = e.
Proof.
  induction e; simpl;
    try (rewrite IHe);
    try (rewrite IHe1; rewrite IHe2);
    try (repeat rewrite Aid_id);
    reflexivity.
Qed.

Definition AValuation := string -> nat.
Definition BValuation := string -> bool.

Fixpoint Aeval (V:AValuation) (e:Aexpr) : nat :=
  match e with
  | AConst n => n
  | AVar x => V x
  | APlus a1 a2 => (Aeval V a1) + (Aeval V a2)
  end.

Fixpoint Beval (AV:AValuation) (BV:BValuation) (e:Bexpr) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BVar x => BV x
  | BNot b => negb (Beval AV BV b)
  | BAnd b1 b2 => (Beval AV BV b1) && (Beval AV BV b2)
  | BLeq a1 a2 => (Aeval AV a1) <=? (Aeval AV a2)
  end.

Definition AComp (V:AValuation) (s:Asub) : AValuation :=
  fun x => Aeval V (s x).

Definition BComp (AV:AValuation) (BV:BValuation) (s:Bsub) : BValuation :=
  fun x => Beval AV BV (s x).

(** Lemma 2.1 (in two parts)*)
Lemma comp_asub : forall V s e,
    Aeval (AComp V s) e = Aeval V (Aapply s e).
Proof.
  induction e; simpl;
  try (rewrite IHe1; rewrite IHe2); reflexivity.
Qed.

Lemma comp_bsub : forall AV BV s s' e,
    Beval (AComp AV s') (BComp AV BV s) e = Beval AV BV (Bapply s s' e).
Proof.
  induction e; simpl;
    try rewrite IHe;
    try (rewrite IHe1; rewrite IHe2);
    try (repeat rewrite comp_asub);
    reflexivity.
Qed.

(* Corollary 2.2 *)
Lemma asgn_soundA : forall V s x e y,
    AComp V (update s x (Aapply s e)) y = update (AComp V s) x (Aeval (AComp V s) e) y.
Proof. intros. unfold AComp. unfold update. destruct (x =? y)%string;
         try (rewrite <- comp_asub; unfold AComp);
         reflexivity.
Qed.

Lemma asgn_soundB : forall AV BV s s' x e y,
    BComp AV BV (update s x (Bapply s s' e)) y = update (BComp AV BV s) x (Beval (AComp AV s') (BComp AV BV s) e) y.
Proof. intros. unfold AComp. unfold BComp. unfold update. destruct (x =? y)%string;
         try (rewrite <- comp_bsub; unfold BComp; unfold AComp);
         reflexivity.
Qed.
