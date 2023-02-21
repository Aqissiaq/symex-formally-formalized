(** * Sympaths - Trying out some stuff from Sympaths paper*)
(* No thread identifiers, idk how that complicates things yet*)

From Coq Require Import String Bool Datatypes Relations Program.Equality Classes.RelationClasses.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Parallel Traces.
Import TraceSemantics.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import ContextReduction.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.

Ltac splits := repeat (try split).

Fixpoint contains__A (e:Aexpr) (x:Var) : Prop :=
  match e with
  | AConst _ => False
  | AVar y => x = y
  | <{e1 + e2}> => contains__A e1 x \/ contains__A e2 x
  end.

Fixpoint contains__B (e:Bexpr) (x:Var) : Prop :=
  match e with
  | BTrue => False
  | BFalse => False
  | <{ ~ b }> => contains__B b x
  | <{ b1 && b2 }> => contains__B b1 x \/ contains__B b2 x
  | <{ a1 <= a2 }> => contains__A a1 x \/ contains__A a2 x
  end.

Definition reads_var (s:trace_step__S) (x:Var) : Prop :=
  match s with
  | Asgn__S _ e => contains__A e x
  | Cond b => contains__B b x
  end.

Definition writes_var (s:trace_step__S) (x:Var) : Prop :=
  match s with
  | Asgn__S y e => x = y
  | Cond b => False
  end.

Definition interference_free: relation trace_step__S :=
  fun s1 s2 =>
    forall x,
      ~ (reads_var s1 x /\ writes_var s2 x) /\
      ~ (writes_var s1 x /\ reads_var s2 x) /\
      ~ (writes_var s1 x /\ writes_var s2 x).

Global Instance sym_interference_free : Symmetric interference_free.
Proof.
  unfold interference_free. intros s1 s2 H x. specialize (H x). splits.
  - destruct H as [_ [contra _]]. intro. destruct H. apply contra. splits; assumption.
  - destruct H as [contra [_ _]]. intro. destruct H. apply contra. splits; assumption.
  - destruct H as [_ [_ contra]]. intro. destruct H. apply contra. splits; assumption.
Qed.

Lemma interference_free_different_var: forall x x' e e', interference_free (Asgn__S x e) (Asgn__S x' e') -> x <> x'.
Proof.
  intros. intro contra. subst.
  specialize (H x'). destruct H as [_ [_ H2]].
  simpl in H2. apply H2. split; reflexivity.
Qed.

Lemma interference_free_different_expr: forall x x' e x0, interference_free (Asgn__S x e) (Asgn__S x' (AVar x0)) -> x <> x0.
Proof.
  intros. intro contra. subst.
  specialize (H x0). destruct H as [_ [H1 _]].
  simpl in H1. apply H1. split; reflexivity.
Qed.

Lemma IF_add_monotone: forall x x' e e1 e2,
    interference_free (Asgn__S x e) (Asgn__S x' <{e1 + e2}>) ->
    interference_free (Asgn__S x e) (Asgn__S x' e1) /\ interference_free (Asgn__S x e) (Asgn__S x' e2).
Proof.
  intros. split.
  - intro y. specialize (H y). splits.
    + destruct H as [H _]. intro contra. destruct contra.
      apply H. split.
      * assumption.
      * inversion H1. reflexivity.
    + destruct H as [_ [H _]]. intro contra. destruct contra.
      apply H. split.
      * assumption.
      * unfold reads_var in *. destruct e2;
          simpl; left; assumption.
    + destruct H as [_ [_ H]]. intro contra. destruct contra.
      apply H. split.
      * assumption.
      * inversion H1. reflexivity.
  - intro y. specialize (H y). splits.
    + destruct H as [H _]. intro contra. destruct contra.
      apply H. split.
      * assumption.
      * inversion H1. reflexivity.
    + destruct H as [_ [H _]]. intro contra. destruct contra.
      apply H. split.
      * assumption.
      * unfold reads_var in *. destruct e1;
          simpl; right; assumption.
    + destruct H as [_ [_ H]]. intro contra. destruct contra.
      apply H. split.
      * assumption.
      * inversion H1. reflexivity.
Qed.

Lemma IF_apply: forall s x x' e e',
    interference_free (Asgn__S x e) (Asgn__S x' e') ->
    (Aapply s e') = (Aapply (x !-> Aapply s e; s) e').
Proof.
  induction e'; intro IF.
  - reflexivity.
  - symmetry. apply update_neq. eapply interference_free_different_expr. apply IF.
  - destruct (IF_add_monotone _ _ _ _ _ IF). simpl. rewrite IHe'1, IHe'2.
    reflexivity.
    all: assumption.
Qed.

Lemma IF_simultaneous_subst: forall s x x' e e',
    interference_free (Asgn__S x e) (Asgn__S x' e') ->
    (x' !-> Aapply (x !-> Aapply s e; s) e'; x !-> Aapply s e; s) =
    (x !-> Aapply (x' !-> Aapply s e'; s) e; x' !-> Aapply s e'; s).
Proof.
  intros. specialize (interference_free_different_var _ _ _ _ H). intro.
  rewrite update_comm.
  replace (Aapply (x !-> Aapply s e; s) e') with (Aapply s e').
  replace (Aapply (x' !-> Aapply s e'; s) e) with (Aapply s e).
  reflexivity.
  eapply IF_apply. symmetry in H. apply H.
  eapply IF_apply. apply H.
  intro. subst. apply H0. reflexivity.
Qed.

Reserved Notation " t '~' t' " (at level 40).
Inductive path_equiv: relation trace__S :=
| pe_refl: forall t, t ~ t
| pe_sym: forall t t', t ~ t' -> t' ~ t
| pe_trans: forall t1 t2 t3, t1 ~ t2 -> t2 ~ t3 -> t1 ~ t3
| pe_interference_free: forall t t' e1 e2,
    interference_free e1 e2 ->
    ((((t :: e1) :: e2)) ++ t') ~ ((((t :: e2) :: e1)) ++ t')
  where " t '~' t' " := (path_equiv t t').

Global Instance refl_path_eq: Reflexive path_equiv.
Proof. intro. apply pe_refl. Qed.

Global Instance sym_path_eq: Symmetric path_equiv.
Proof. intro. apply pe_sym. Qed.

Global Instance trans_path_eq: Transitive path_equiv.
Proof. intro. apply pe_trans. Qed.

Lemma path_equiv_extend: forall t t' a,
    t ~ t' -> (t :: a) ~ (t' :: a).
Proof.
  intros. induction H.
  - reflexivity.
  - symmetry. assumption.
  - transitivity (t2::a); assumption.
  - rewrite app_comm_cons. apply pe_interference_free. assumption.
Qed.

(* Seems like it will be useful *)
Theorem equiv_acc_subst: forall t t', t ~ t' -> acc_subst id_sub t = acc_subst id_sub t'.
Proof.
  intros. induction H; try auto. rewrite IHpath_equiv1. assumption.
  (* the interesting case*)
  induction t'.
  - destruct e1, e2; simpl; try reflexivity.
    apply IF_simultaneous_subst. assumption.
  - destruct a; simpl.
    + rewrite IHt'. reflexivity.
    + assumption.
Qed.

(* Framing, because it shows up in several proofs *)
(*
  Framing corresponds to accumulated substitutions with different initial states
  when working with (this style of) traces. We will see how hard/easy that is to incorporate
*)

Inductive DL : Type :=
  | DLExpr (b: Bexpr)
  | DLNeg (p: DL)
  | DLAnd (p1 p2: DL)
  | DLOr (p1 p2: DL)
  | DLExists (x:Var) (p: DL)
  | DLForall (x:Var) (p: DL)
  | DLBox (s: Stmt) (p: DL)
  | DLUpdate (s: sub) (p: DL)
.

Coercion DLExpr: Bexpr >-> DL.
Declare Custom Entry dl.
Declare Scope dl_scope.

Notation "{{ p }}" := p (at level 0, p custom dl at level 99) : dl_scope.
Notation "( x )" := x (in custom dl, x at level 99) : dl_scope.
Notation "x" := x (in custom dl at level 0, x constr at level 0) : dl_scope.
Notation "'~' p"   := (DLNeg p) (in custom dl at level 75, right associativity).
Notation "x /\ y"   := (DLAnd x y) (in custom dl at level 70, no associativity).
Notation "x \/ y"   := (DLOr x y) (in custom dl at level 70, no associativity).
Notation "'exists' x ':' p"  := (DLExists x p) (in custom dl at level 70, no associativity).
Notation "'forall' x ':' p"  := (DLForall x p) (in custom dl at level 70, no associativity).
Notation "[ s ] p"  := (DLBox s p) (in custom dl at level 70, no associativity) : dl_scope.
Notation "{ s } p"  := (DLUpdate s p) (in custom dl at level 70, no associativity) : dl_scope.

Open Scope dl_scope.

Fixpoint satisfies (V: Valuation) (p: DL) : Prop :=
  match p with
  | DLExpr b => Beval V b = true
  | {{ ~ p }} => ~ (satisfies V p)
  | {{ p1 /\ p2 }} => satisfies V p1 /\ satisfies V p2
  | {{ p1 \/ p2 }} => satisfies V p1 \/ satisfies V p2
  | {{ exists x : p }} => exists e, satisfies (x !-> Aeval V e ; V) p
  | {{ forall x : p }} => forall e, satisfies (x !-> Aeval V e ; V) p
  | {{ [ s ] p }} => forall V0 t, red_star__C V0 ([], s) (t, SSkip) -> satisfies (acc_val V0 t) p
  | {{ { s } p }} => satisfies (Comp V s) p
  end.
