(** * Substitutions and Valuations *)

(** Definitions and notation for maps used for substitutions and valuations *)


From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)

From SymEx Require Import Expr.

(** Basic definitions and lemmas from PLF *)

Definition total_map (A : Type) := string -> A.

Definition update {E:Type} (s: total_map E) (x:string) (e:E) : total_map E :=
  fun y => if String.eqb x y then e else s y.

Notation "x '!->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).

Definition empty_map {A:Type} (x:A) : total_map A := fun _ => x.
Notation "'_' '!->' v" := (empty_map v) (at level 100, right associativity).

Lemma apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof. intros. unfold empty_map. reflexivity. Qed.

Lemma update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof. intros. unfold update. rewrite String.eqb_refl. reflexivity. Qed.

Theorem update_neq : forall (A : Type) (m : total_map A) x y v,
    x <> y ->
    (x !-> v ; m) y = m y.
Proof.
  intros. unfold update. rewrite <- String.eqb_neq in H. destruct (x =? y)%string.
  - discriminate.
  - reflexivity.
Qed.

Lemma equal_maps {A : Type} {m m' : total_map A} :
  m = m' -> forall x, m x = m' x.
Proof. intros. subst. reflexivity. Qed.

Lemma update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. extensionality y. unfold update.
  destruct (x =? y)%string; reflexivity.
Qed.

Lemma update_comm: forall {A: Type} (m: total_map A) x1 x2 v1 v2,
    x1 <> x2 -> (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. extensionality y. unfold update.
  destruct (String.eqb_spec x1 y); destruct (String.eqb_spec x2 y);
    try reflexivity.
  exfalso. apply H. rewrite e, e0. reflexivity.
Qed.

Module BasicMaps.
  Import BasicExpr.

  (* substitions map to (Arithmetic) expressions*)
  Definition sub : Type := string -> Aexpr.
  Definition id_sub : string -> Aexpr := fun x => x.

  (* valuations map to concrete values *)
  Definition Valuation := string -> nat.

  Fixpoint Aapply (s:string -> Aexpr) (e:Aexpr) : Aexpr :=
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

  Fixpoint Bapply  (s:string -> Aexpr) (e:Bexpr) : Bexpr :=
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

  Definition Comp (V:Valuation) (s:string -> Aexpr) : Valuation :=
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
End BasicMaps.
