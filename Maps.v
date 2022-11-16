(** * Substitutions and Valuations *)

(** Definitions and notation for maps used for substitutions and valuations *)


From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)

From SymEx Require Import Expr.

Definition update {E:Type} (s: string -> E) (x:string) (e:E) : string -> E :=
  fun y => if String.eqb x y then e else s x.

Notation "x '!->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).

Definition empty_map {A:Type} (x:A) : string -> A := fun _ => x.
Notation "'_' '!->' v" := (empty_map v) (at level 100, right associativity).

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

Module ProcedureMaps.
  Import ProcedureExpr.

  Definition LSub := LVar -> Aexpr.
  Definition GSub := GVar -> Aexpr.

  Definition Gid_sub : GVar -> Aexpr := fun x => AGVar x.
  Definition Lid_sub : LVar -> Aexpr := fun x => ALVar x.

  Fixpoint Aapply (s:GVar -> Aexpr) (t:LVar -> Aexpr) (e:Aexpr) : Aexpr :=
    match e with
    | AConst n => AConst n
    | AGVar x => s x
    | ALVar x => t x
    | APlus a1 a2 => APlus (Aapply s t a1) (Aapply s t a2)
    end.

  Fixpoint Bapply  (s:GVar -> Aexpr) (t:LVar -> Aexpr) (e:Bexpr) : Bexpr :=
    match e with
    | BTrue => BTrue
    | BFalse => BFalse
    | BNot b => BNot (Bapply s t b)
    | BAnd b1 b2 => BAnd (Bapply s t b1) (Bapply s t b2)
    | BLeq a1 a2 => BLeq (Aapply s t a1) (Aapply s t a2)
    end.

  Lemma Aapply_id : forall e,
      Aapply Gid_sub Lid_sub e = e.
  Proof.
    induction e; try reflexivity.
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Qed.

  Lemma Bapply_id : forall e,
      Bapply Gid_sub Lid_sub e = e.
  Proof.
    induction e; simpl;
      try (rewrite IHe);
      try (rewrite IHe1; rewrite IHe2);
      try (repeat rewrite Aapply_id);
      try reflexivity.
  Qed.

  Lemma L_single_update : forall X Y,
      (X !-> Y ; Lid_sub) X = Y.
  Proof. intros. unfold update. rewrite String.eqb_refl. reflexivity. Qed.

  Lemma G_single_update : forall X Y,
      (X !-> Y ; Gid_sub) X = Y.
  Proof. intros. unfold update. rewrite String.eqb_refl. reflexivity. Qed.

  Definition GVal : Type := GVar -> nat.
  Definition LVal : Type := LVar -> nat.

  Fixpoint Aeval (G:GVal) (L:LVal) (e:Aexpr) : nat :=
    match e with
    | AConst n => n
    | AGVar x => G x
    | ALVar x => L x
    | APlus a1 a2 => (Aeval G L a1) + (Aeval G L a2)
    end.

  Fixpoint Beval (G:GVal) (L:LVal) (e:Bexpr) : bool :=
    match e with
    | BTrue => true
    | BFalse => false
    | BNot b => negb (Beval G L b)
    | BAnd b1 b2 => (Beval G L b1) && (Beval G L b2)
    | BLeq a1 a2 => (Aeval G L a1) <=? (Aeval G L a2)
    end.

  (** We can update a valuation with a substitution by composition *)

  Fixpoint Aeval_comp (G:GVal) (L:LVal) (s:GVar -> Aexpr) (t:LVar -> Aexpr) (e:Aexpr) : nat :=
    match e with
    | AConst n => n
    | AGVar x => Aeval G L (s x)
    | ALVar x => Aeval G L (t x)
    | APlus a1 a2 => (Aeval_comp G L s t a1) + (Aeval_comp G L s t a2)
    end.

  Fixpoint Beval_comp (G:GVal) (L:LVal) (s:GVar -> Aexpr) (t:LVar -> Aexpr) (e:Bexpr) : bool :=
    match e with
    | BTrue => true
    | BFalse => false
    | BNot b => negb (Beval_comp G L s t b)
    | BAnd b1 b2 => (Beval_comp G L s t b1) && (Beval_comp G L s t b2)
    | BLeq a1 a2 => (Aeval_comp G L s t a1) <=? (Aeval_comp G L s t a2)
    end.

  Definition GComp (G:GVal) (L:LVal) (s:GVar -> Aexpr) : GVal :=
    fun x => Aeval G L (s x).
  Definition LComp (G:GVal) (L:LVal) (t:LVar -> Aexpr) : LVal :=
    fun x => Aeval G L (t x).
End ProcedureMaps.
