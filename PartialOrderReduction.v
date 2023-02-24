(** * Partial Order Reduction - Trying out some stuff from Sympaths paper*)
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

(** Symbolic POR *)
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

Definition interference_free__S: relation trace_step__S :=
  fun s1 s2 =>
    forall x,
      ~ (reads_var s1 x /\ writes_var s2 x) /\
      ~ (writes_var s1 x /\ reads_var s2 x) /\
      ~ (writes_var s1 x /\ writes_var s2 x).

Global Instance sym_interference_free__S : Symmetric interference_free__S.
Proof.
  unfold interference_free__S. intros s1 s2 H x. specialize (H x). splits.
  - destruct H as [_ [contra _]]. intro. destruct H. apply contra. splits; assumption.
  - destruct H as [contra [_ _]]. intro. destruct H. apply contra. splits; assumption.
  - destruct H as [_ [_ contra]]. intro. destruct H. apply contra. splits; assumption.
Qed.

Lemma interference_free__S_different_var: forall x x' e e',
    interference_free__S (Asgn__S x e) (Asgn__S x' e') -> x <> x'.
Proof.
  intros. intro contra. subst.
  specialize (H x'). destruct H as [_ [_ H2]].
  simpl in H2. apply H2. split; reflexivity.
Qed.

Lemma interference_free__S_different_expr: forall x x' e x0,
    interference_free__S (Asgn__S x e) (Asgn__S x' (AVar x0)) -> x <> x0.
Proof.
  intros. intro contra. subst.
  specialize (H x0). destruct H as [_ [H1 _]].
  simpl in H1. apply H1. split; reflexivity.
Qed.

Lemma IF_add_monotone: forall x x' e e1 e2,
    interference_free__S (Asgn__S x e) (Asgn__S x' <{e1 + e2}>) ->
    interference_free__S (Asgn__S x e) (Asgn__S x' e1) /\ interference_free__S (Asgn__S x e) (Asgn__S x' e2).
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
    interference_free__S (Asgn__S x e) (Asgn__S x' e') ->
    (Aapply s e') = (Aapply (x !-> Aapply s e; s) e').
Proof.
  induction e'; intro IF.
  - reflexivity.
  - symmetry. apply update_neq. eapply interference_free__S_different_expr. apply IF.
  - destruct (IF_add_monotone _ _ _ _ _ IF). simpl. rewrite IHe'1, IHe'2.
    reflexivity.
    all: assumption.
Qed.

Lemma IF_simultaneous_subst: forall s x x' e e',
    interference_free__S (Asgn__S x e) (Asgn__S x' e') ->
    (x' !-> Aapply (x !-> Aapply s e; s) e'; x !-> Aapply s e; s) =
    (x !-> Aapply (x' !-> Aapply s e'; s) e; x' !-> Aapply s e'; s).
Proof.
  intros. specialize (interference_free__S_different_var _ _ _ _ H). intro.
  rewrite update_comm.
  replace (Aapply (x !-> Aapply s e; s) e') with (Aapply s e').
  replace (Aapply (x' !-> Aapply s e'; s) e) with (Aapply s e).
  reflexivity.
  eapply IF_apply. symmetry in H. apply H.
  eapply IF_apply. apply H.
  intro. subst. apply H0. reflexivity.
Qed.

Definition path_equiv__S: relation trace__S := permute_events interference_free__S.
Notation " t '~' t' " := (path_equiv__S t t') (at level 40).

(* Seems like it will be useful *)
Theorem equiv_acc_subst: forall t t', t ~ t' -> acc_subst id_sub t = acc_subst id_sub t'.
Proof.
  intros. induction H; try auto. rewrite IHpermute_events1. assumption.
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
Lemma parallel_steps: forall s1 s2 s1' s2' t e1 e2,
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

(* I feel like this is just auto with some hints, but that didn't work as expected *)
(* maybe revisit *)
Ltac solve_equivs := repeat (
      match goal with
      | _ : _ |- ?t ~ ?t => reflexivity
      | H : ?t ~ ?t' |- ?t' ~ ?t => symmetry
      | H1 : ?t1 ~ ?t2, H2 : ?t2 ~ ?t3 |- ?t1 ~ ?t3 => transitivity t2
      | H1 : ?t2 ~ ?t1, H2 : ?t2 ~ ?t3 |- ?t1 ~ ?t3 => symmetry in H1
      | _ : _ |- (?t :: _) ~ (?t' :: _) => apply path_equiv_extend
      (* dealing with selection functions*)
      (* | _ : _ |- ?t' ~ select ?f ?t => unfold select; destruct (f t); simpl *)
      (* | _ : _ |- select ?f ?t ~ ?t' => symmetry *)
      | H : ?T |- ?T => apply H
      | _ => fail
      end).

(* do the non-selection_function formulation *)
(* - compose correct/completeness POR<->C *)
(* - define POR for concrete execution *)
(* - correct/completeness for POR__C <-> C*)
(* - compare / commute the square *)
Variant head_red__POR: relation (trace__S * Stmt) :=
  | POR_intro: forall s s' t0 t0' t,
      t0 ~ t0' -> head_red__S (t0, s) (t, s') ->
      head_red__POR (t0', s) (t, s').

Definition red__POR := context_red head_red__POR.
Definition red_star__POR := clos_refl_trans_n1 _ red__POR.

Theorem correctness__POR: forall s0 t0 s t,
    red_star__POR (t0, s0) (t, s) ->
    exists t', red_star__S (t0, s0) (t', s) /\ t ~ t'.
Proof.
  intros. dependent induction H.
  - exists t. split; constructor.
  - destruct y. destruct (IHclos_refl_trans_n1 s0 t0 s1 t1) as [t' [IHcomp IHequiv]];
      try reflexivity.
    dependent destruction H. dependent destruction H.
    specialize (equiv_step (C s2) t2 (C s') t t'). intros.
    destruct H3 as [t2' [equiv_step Hequiv]].
    + solve_equivs.
    + constructor; assumption.
    + eexists. split.
      * econstructor.
        ** apply equiv_step.
        ** assumption.
      * assumption.
Qed.

Lemma completeness_step__POR: forall t0 t0' s0 t s,
    t0 ~ t0' -> red__S (t0, s0) (t, s) ->
    exists t', red__POR (t0', s0) (t', s)
        /\ t ~ t'.
Proof.
  intros. inversion H0; inversion H4; subst; eexists; split;
    try (constructor;
         [ econstructor; [apply H | constructor]
         | assumption]);
    solve_equivs.
Qed.

Theorem completeness__POR: forall t0 s0 t s,
    red_star__S (t0, s0) (t, s) ->
    exists t', red_star__POR (t0, s0) (t', s)
        /\ t ~ t'.
Proof.
  intros. dependent induction H.
  - exists t. split; constructor.
  - destruct y.
    destruct (IHclos_refl_trans_n1 t0 s0 t1 s1) as [t' [IHcomp IHequiv]];
      try reflexivity.
    destruct (completeness_step__POR t1 t' s1 t s) as [t_step [comp_step equiv_step]];
      try assumption; solve_equivs.
    exists t_step. split.
    + econstructor.
      * apply comp_step.
      * apply IHcomp.
    + assumption.
Qed.

(** Concrete POR *)
Definition interference_free__C: relation (Var * Val) :=
  fun e1 e2 => fst e1 <> fst e2.

Definition path_equiv__C: relation trace__C := permute_events interference_free__C.
Notation " t '≃' t' " := (path_equiv__C t t') (at level 40).

Theorem equiv_acc_val: forall V0 t t', t ≃ t' -> acc_val V0 t = acc_val V0 t'.
Proof.
  intros. induction H; try auto. rewrite IHpermute_events1. assumption.
  (* the interesting case*)
  induction t'.
  - destruct e1, e2; simpl; try reflexivity.
    apply update_comm. unfold interference_free__C in H.
    simpl in H. apply not_eq_sym. assumption.
  - destruct a; simpl.
    + rewrite IHt'. reflexivity.
Qed.

Lemma equiv_step__C: forall V0 s t1 s' t1' t2,
    t1 ≃ t2 -> red__C V0 (t1, s) (t1', s') ->
    exists t2', red__C V0 (t2, s) (t2', s') /\ t1' ≃ t2'.
Proof.
  intros. inversion H0; inversion H4; subst;
    (* the skip cases *)
    try (eexists; split;
         [ constructor;
           [constructor | assumption]
         | assumption]);
    (* the conditional cases *)
    try (eexists; split;
         [ constructor;
           [ replace (Beval_t V0 t1' b) with (Beval_t V0 t2 b);
             [ constructor
             | unfold Beval_t; rewrite (equiv_acc_val V0 t1' t2);
               [ reflexivity | assumption ]]
           | assumption]
         | assumption]).
  (* assignment *)
  eexists. split.
  - constructor; [constructor | assumption].
  - unfold Aeval_t. rewrite (equiv_acc_val V0 t1 t2).
    + apply path_equiv_extend; assumption.
    + assumption.
Qed.

Theorem equiv_star__C: forall V0 s t1 s' t1' t2,
    t1 ≃ t2 -> red_star__C V0 (t1, s) (t1', s') ->
    exists t2', red_star__C V0 (t2, s) (t2', s') /\ t1' ≃ t2'.
Proof.
  intros. dependent induction H0.
  - exists t2. split; [constructor | assumption].
  - destruct y. edestruct (IHclos_refl_trans_n1 s t1 s0 t) as [t2' [IHcomp IHequiv]];
      try assumption; try reflexivity.
    destruct (equiv_step__C _ _ _ _ _ _ IHequiv H1) as [t2_final [comp_final equiv_final]].
    exists t2_final. split.
    + econstructor. apply comp_final. apply IHcomp.
    + assumption.
Qed.

Variant head_red__PORC (V: Valuation): relation (trace__C * Stmt) :=
  | POR_intro__C: forall s s' t0 t0' t,
      t0 ≃ t0' -> head_red__C V (t0, s) (t, s') ->
      head_red__PORC V (t0', s) (t, s').

Definition red__PORC V := context_red (head_red__PORC V).
Definition red_star__PORC V := clos_refl_trans_n1 _ (red__PORC V).

Theorem correctness__PORC: forall V0 s0 t0 s t,
    red_star__PORC V0 (t0, s0) (t, s) ->
    exists t', red_star__C V0 (t0, s0) (t', s) /\ t ≃ t'.
Proof.
  intros. dependent induction H.
  - exists t. split; constructor.
  - destruct y. destruct (IHclos_refl_trans_n1 s0 t0 s1 t1) as [t' [IHcomp IHequiv]];
      try reflexivity.
    dependent destruction H. dependent destruction H.
    specialize (equiv_step__C V0 (C s2) t2 (C s') t t'). intros.
    destruct H3 as [t2' [equiv_step Hequiv]].
    + transitivity t1; assumption.
    + constructor; assumption.
    + eexists. split.
      * econstructor.
        ** apply equiv_step.
        ** assumption.
      * assumption.
Qed.

Lemma completeness_step__PORC: forall V0 t0 t0' s0 t s,
    t0 ≃ t0' -> red__C V0 (t0, s0) (t, s) ->
    exists t', red__PORC V0 (t0', s0) (t', s)
        /\ t ≃ t'.
Proof.
  intros. inversion H0; inversion H4; subst; eexists; split;
    try (constructor;
         [ econstructor; [apply H | constructor]
         | assumption]);
    reflexivity.
Qed.

Theorem completeness__PORC: forall V0 t0 s0 t s,
    red_star__C V0 (t0, s0) (t, s) ->
    exists t', red_star__PORC V0 (t0, s0) (t', s)
        /\ t ≃ t'.
Proof.
  intros. dependent induction H.
  - exists t. split; constructor.
  - destruct y.
    destruct (IHclos_refl_trans_n1 t0 s0 t1 s1) as [t' [IHcomp IHequiv]];
      try reflexivity.
    destruct (completeness_step__PORC V0 t1 t' s1 t s) as [t_step [comp_step equiv_step]];
      try assumption; solve_equivs.
    exists t_step. split.
    + econstructor.
      * apply comp_step.
      * apply IHcomp.
    + assumption.
Qed.