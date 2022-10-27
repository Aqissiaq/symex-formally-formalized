(** * Substitutions and Valuations *)

(** Definitions and notation for maps used for substitutions and valuations *)


From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)

From SymEx Require Import Expr.

(* Both substituions and valuations are maps /from/ strings and have some common
operations and notation *)

Definition update {E:Type} (s: string -> E) (x:string) (e:E) : string -> E :=
  fun y => if String.eqb x y then e else s x.

Notation "x '!->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).

Definition empty_map {A:Type} (x:A) : string -> A := fun _ => x.
Notation "'_' '!->' v" := (empty_map v) (at level 100, right associativity).

(* substitions map to (Arithmetic) expressions*)
Definition sub : Type := string -> Aexpr.
Definition id_sub : sub := fun x => x.

(* valuations map to concrete values *)
Definition Valuation := string -> nat.


Fixpoint Aapply (s:sub) (e:Aexpr) : Aexpr :=
  match e with
  | AConst n => AConst n
  | AVar x => s x
  | APlus a1 a2 => APlus (Aapply s a1) (Aapply s a2)
  end.

Lemma Aapply_id : forall e,
    Aapply id_sub e = e.
Proof.
  induction e; try reflexivity.
  simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Fixpoint Bapply  (s:sub) (e:Bexpr) : Bexpr :=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b => BNot (Bapply s b)
  | BAnd b1 b2 => BAnd (Bapply s b1) (Bapply s b2)
  | BLeq a1 a2 => BLeq (Aapply s a1) (Aapply s a2)
  end.

Lemma Bapply_id : forall e,
    Bapply id_sub e = e.
Proof.
  induction e; simpl;
    try (rewrite IHe);
    try (rewrite IHe1; rewrite IHe2);
    try (repeat rewrite Aapply_id);
    try reflexivity.
Qed.

Fixpoint Aeval (V:Valuation) (e:Aexpr) : nat :=
  match e with
  | AConst n => n
  | AVar x => V x
  | APlus a1 a2 => (Aeval V a1) + (Aeval V a2)
  end.

Fixpoint Beval (V:Valuation) (e:Bexpr) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BNot b => negb (Beval V b)
  | BAnd b1 b2 => (Beval V b1) && (Beval V b2)
  | BLeq a1 a2 => (Aeval V a1) <=? (Aeval V a2)
  end.

(** We can update a valuation with a substitution by composition
    and prove some useful properties *)

Definition Comp (V:Valuation) (s:sub) : Valuation :=
  fun x => Aeval V (s x).

(** Lemma 2.1 *)
Lemma comp_sub : forall V s e,
    Aeval (Comp V s) e = Aeval V (Aapply s e).
Proof.
  induction e; simpl;
  try (rewrite IHe1; rewrite IHe2); reflexivity.
Qed.

Lemma comp_subB : forall V s e,
    Beval (Comp V s) e = Beval V (Bapply s e).
Proof.
  induction e; simpl;
  try (rewrite IHe1; rewrite IHe2);
    try (rewrite IHe);
    try (repeat (rewrite comp_sub));
    reflexivity.
Qed.

(* Corollary 2.2 *)
Lemma asgn_sound : forall V s x e,
    Comp V (update s x (Aapply s e)) = update (Comp V s) x (Aeval (Comp V s) e).
Proof. intros. extensionality y.
  unfold Comp. unfold update. destruct (x =? y)%string;
    try (rewrite <- comp_sub; unfold Comp);
    reflexivity.
Qed.

Lemma comp_id : forall V,
    Comp V id_sub = V.
Proof. intros. extensionality x. reflexivity. Qed.
