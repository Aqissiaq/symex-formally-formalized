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

  Turns out we can make do without
*)

(* This is not quite confluence, but kind of step-wise *)
Theorem diamond_property: forall s1 s2 s1' s2' t e1 e2,
    red__S (t, <{s1 || s2}>) (t :: e1, <{s1' || s2}>) ->
    red__S (t, <{s1 || s2}>) (t :: e2, <{s1 || s2'}>) ->
    red__S (t :: e1, <{s1' || s2}>) ((t :: e1) :: e2, <{s1' || s2'}>) /\
    red__S (t :: e2, <{s1 || s2'}>) ((t :: e2) :: e1, <{s1' || s2'}>)
.
Proof.
  split.
  - dependent destruction H0. dependent destruction H1;
      inversion x0; inversion x; subst.
    + dependent destruction H0;
        apply cons_neq' in x; contradiction.
    + dependent destruction H0;
        apply context_injective in H5; try discriminate; try assumption; symmetry in H5;
        [ apply SIf_true_disjoint in H5
        | apply SIf_false_disjoint in H5
        | apply SSeq_disjoint in H5
        | apply SPar_right_disjoint in H5
        | apply SPar_left_disjoint in H5];
        contradiction.
    + dependent destruction H0;
        try (apply cons_neq' in x; contradiction);
        try (apply ctx_red_intro with (C := fun s => SPar s1' (C s));
             [constructor | constructor; assumption]).
  - dependent destruction H. dependent destruction H0;
      inversion x0; inversion x; subst.
    + dependent destruction H;
        apply cons_neq' in x; contradiction.
    + dependent destruction H;
        try (apply cons_neq' in x; contradiction);
        try (apply ctx_red_intro with (C := fun s => SPar (C s) s2');
             [constructor | constructor; assumption]).
    + dependent destruction H;
        apply context_injective in H6; try assumption; apply symmetry in H6;
        [ discriminate
        | apply SIf_true_disjoint in H6
        | apply SIf_false_disjoint in H6
        | symmetry in H6; apply SSeq_disjoint in H6
        | discriminate
        | apply SSeq_disjoint in H6
        | apply SPar_right_disjoint in H6
        | apply SPar_left_disjoint in H6];
        contradiction.
Qed.

Lemma equiv_step: forall s t1 s' t1' t2,
    t1 ~ t2 -> red__S (t1, s) (t1', s') ->
    exists t2', red__S (t2, s) (t2', s') /\ t1' ~ t2'.
Proof.
  intros. inversion H0; subst. inversion H4; subst; eexists; split;
    try (constructor; [constructor | assumption]);
    try (apply path_equiv_extend);
    assumption.
Qed.

Theorem equiv_star: forall s t1 s' t1' t2,
    t1 ~ t2 -> red_star__S (t1, s) (t1', s') ->
    exists t2', red_star__S (t2, s) (t2', s') /\ t1' ~ t2'.
Proof.
  intros. dependent induction H0.
  - exists t2. split; [constructor | assumption].
  - destruct y. edestruct (IHclos_refl_trans_n1 s t1 s0 t) as [t2' [IHcomp IHequiv]];
      try assumption; try reflexivity.
    destruct (equiv_step _ _ _ _ _ IHequiv H1) as [t2_final [comp_final equiv_final]].
    exists t2_final. split.
    + econstructor. apply comp_final. apply IHcomp.
    + assumption.
Qed.

Definition selection_function: Type := forall t, {t' : trace__S | t ~ t'}.
Definition select (f:selection_function) (t: trace__S) := proj1_sig (f t).

Definition id_select: selection_function.
  intro. econstructor. reflexivity.
Defined.

Variant head_red__POR (f: selection_function): relation (trace__S * Stmt) :=
  | POR_intro: forall s s' t t',
      head_red__S (select f t, s) (t', s') ->
      head_red__POR f (t, s) (t', s').

Definition red__POR f := context_red (head_red__POR f).
Definition red_star__POR f := clos_refl_trans_n1 _ (red__POR f).

Ltac solve_equivs := repeat (
      match goal with
      | _ : _ |- ?t ~ ?t => reflexivity
      | H : ?t ~ ?t' |- ?t' ~ ?t => symmetry
      | H1 : ?t1 ~ ?t2, H2 : ?t2 ~ ?t3 |- ?t1 ~ ?t3 => transitivity t2
      | H1 : ?t2 ~ ?t1, H2 : ?t2 ~ ?t3 |- ?t1 ~ ?t3 => symmetry in H1
      | _ : _ |- (?t :: _) ~ (?t' :: _) => apply path_equiv_extend
      (* dealing with selection functions*)
      | _ : _ |- ?t' ~ select ?f ?t => unfold select; destruct (f t); simpl
      | _ : _ |- select ?f ?t ~ ?t' => symmetry
      | H : ?T |- ?T => apply H
      | _ => fail
      end).

Theorem correctness__POR: forall f s0 t0 s t,
    red_star__POR f (t0, s0) (t, s) ->
    exists t', red_star__S (t0, s0) (t', s) /\ t ~ t'.
Proof.
  intros. dependent induction H.
  - exists t. split; constructor.
  - destruct y. destruct (IHclos_refl_trans_n1 s0 t0 s1 t1) as [t' [IHcomp IHequiv]];
      try reflexivity.
    dependent destruction H. dependent destruction H.
    specialize (equiv_step (C s2) (select f t1) (C s') t t'). intros.
    destruct H2 as [t2 [equiv_step Hequiv]].
    + solve_equivs.
    + constructor; assumption.
    + eexists. split.
      * econstructor.
        ** apply equiv_step.
        ** assumption.
      * assumption.
Qed.

Lemma completeness_step__POR: forall f t0 t0' s0 t s,
    t0 ~ t0' -> red__S (t0, s0) (t, s) ->
    exists t', red__POR f (t0', s0) (t', s)
        /\ t ~ t'.
Proof.
  intros. inversion H0; inversion H4; subst; eexists; split;
    try (constructor; [repeat constructor | assumption]);
    solve_equivs.
Qed.

Theorem completeness__POR: forall f t0 s0 t s,
    red_star__S (t0, s0) (t, s) ->
    exists t', red_star__POR f (t0, s0) (t', s)
        /\ t ~ t'.
Proof.
  intros. dependent induction H.
  - exists t. split; constructor.
  - destruct y.
    destruct (IHclos_refl_trans_n1 t0 s0 t1 s1) as [t' [IHcomp IHequiv]];
      try reflexivity.
    destruct (completeness_step__POR f t1 t' s1 t s) as [t_step [comp_step equiv_step]];
      try assumption; solve_equivs.
    exists t_step. split.
    + econstructor.
      * apply comp_step.
      * apply IHcomp.
    + assumption.
Qed.

(** * Dynamic Logic (section 4) *)

(* using Coq's propositions as (constructive) FOL over valuations *)
(* approach like Hoare logic in PLF *)
Definition Formula := Valuation -> Prop.
(* Notation "V |= p" := (p V) (at level 80). *)

Definition DLAnd (p1 p2: Formula): Formula := fun V => p1 V /\ p2 V.
Definition DLExists (x: Var) (p: Formula): Formula := fun V => exists e, p (x !-> Aeval V e ; V).
Definition DLForall (x: Var) (p: Formula): Formula := fun V => forall e, p (x !-> Aeval V e ; V).
(* this one is a bit experimental *)
Definition DLBox (s: Stmt) (p: Formula): Formula :=
  fun V => forall t, red_star__C V ([], s) (t, SSkip) -> p (acc_val V t).
Definition DLUpdate (s: sub) (p: Formula): Formula := fun V => p (Comp V s).
Definition Sequent (G P: Formula): Formula :=
  fun V => G V -> P V.

Definition DLpc (t : trace__S): Formula := fun V => Beval V (pc t) = true.

Inductive head__DLT: relation (Formula * trace__S * Stmt) :=
  (* this "stuttering step" causes problems with the DLT-S-correspondence *)
  (* | DLT_reduce: forall G P t sig, *)
      (* head__DLT (Sequent G (DLUpdate sig P), t, SSkip) (Sequent (DLAnd G (DLpc t)) (DLUpdate sig P), t, SSkip) *)
  | DLT_assign: forall G P t sig x e,
      head__DLT (Sequent G (DLUpdate sig P), t, <{x := e}>)
        (Sequent G (DLUpdate (x !-> Aapply sig e; sig) P), t :: Asgn__S x e, SSkip)
  | DLT_cond_true: forall G P t sig b s1 s2,
      head__DLT (Sequent G (DLUpdate sig P), t, <{if b {s1}{s2}}>)
              (Sequent G (DLUpdate sig P), t :: Cond b, <{s1}>)
  | DLT_cond_false: forall G P t sig b s1 s2,
      head__DLT (Sequent G (DLUpdate sig P), t, <{if b {s1}{s2}}>)
              (Sequent G (DLUpdate sig P), t :: Cond (BNot b), <{s2}>)
  | DLT_loop_true: forall G P t sig b s,
      head__DLT (Sequent G (DLUpdate sig P), t, <{while b {s}}>)
              (Sequent G (DLUpdate sig P), t :: Cond b, <{s ; while b {s}}>)
  | DLT_loop_false: forall G P t sig b s,
      head__DLT (Sequent G (DLUpdate sig P), t, <{while b {s}}>)
              (Sequent G (DLUpdate sig P), t :: Cond (BNot b), SSkip)
  | DLT_skip_seq: forall P t s,
      head__DLT (P, t, <{SSkip ; s}>) (P, t, s)
  | DLT_skip_par_l: forall P t s,
      head__DLT (P, t, <{SSkip || s}>) (P, t, s)
  | DLT_skip_par_r: forall P t s,
      head__DLT (P, t, <{s || SSkip}>) (P, t, s)
.

Definition DLT := context_red head__DLT.
Definition Derivable__DLT := clos_refl_trans_n1 _ DLT.

Lemma DL_S_correspondence: forall G P t t' sig0 s s',
    (exists sig, DLT (Sequent G (DLUpdate sig0 P), t, s) (Sequent G (DLUpdate sig P), t', s'))
    <-> red__S (t, s) (t', s').
Proof.
  intros. split; intro.
  - destruct H as [sig H]. dependent destruction H. inversion H; subst;
      (constructor; [constructor | assumption]).
  - dependent destruction H. inversion H; subst; eexists;
      (constructor; [constructor | assumption]).
Qed.

(* I do not understand the soundness and (relative) completeness formulations for DL(T) *)
