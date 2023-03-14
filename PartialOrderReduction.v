(** * Partial Order Reduction - Trying out some stuff from Sympaths paper*)
(* No thread identifiers, idk how that complicates things yet*)

From Coq Require Import String Bool Datatypes Relations Program.Equality Classes.RelationClasses.

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

(* idk, but this seems like it might be useful *)
Lemma contains_dec__A: forall x e, contains__A e x \/ ~ (contains__A e x).
Proof.
  induction e.
  - right. auto.
  - destruct (String.eqb_spec x x0); subst.
    + left. reflexivity.
    + right. unfold contains__A. assumption.
  - destruct IHe1.
    + left. left. assumption.
    + destruct IHe2.
      * left. right. assumption.
      * right. intro. destruct H1; auto.
Qed.

Fixpoint contains__B (e:Bexpr) (x:Var) : Prop :=
  match e with
  | BTrue => False
  | BFalse => False
  | <{ ~ b }> => contains__B b x
  | <{ b1 && b2 }> => contains__B b1 x \/ contains__B b2 x
  | <{ a1 <= a2 }> => contains__A a1 x \/ contains__A a2 x
  end.

Lemma contains_dec__B: forall x e, contains__B e x \/ ~ (contains__B e x).
Proof.
  induction e.
  - right; auto.
  - right; auto.
  - destruct IHe.
    + left; auto.
    + right; auto.
  - destruct IHe1.
    + left. left. apply H.
    + destruct IHe2.
      * left. right. apply H0.
      * right. intro. destruct H1; auto.
  - destruct (contains_dec__A x a1).
    + left. left. apply H.
    + destruct (contains_dec__A x a2).
      * left. right. apply H0.
      * right. intro. destruct H1; auto.
Qed.

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

Lemma no_touch__A: forall s e x a, ~ (contains__A a x) -> Aapply (x !-> e ; s) a = Aapply s a.
Proof.
  induction a; intro.
  - reflexivity.
  - unfold contains__A in H. apply update_neq. assumption.
  - simpl. rewrite IHa1, IHa2.
    + reflexivity.
    + intro. apply H. right. assumption.
    + intro. apply H. left. assumption.
Qed.

Lemma no_touch__B: forall s e x b, ~ (contains__B b x) -> Bapply (x !-> e ; s) b = Bapply s b.
Proof.
  induction b; intro;
    try reflexivity.
  - simpl in *. rewrite IHb; [reflexivity | assumption].
  - simpl in *. rewrite IHb1, IHb2.
    + reflexivity.
    + intro. apply H. right. assumption.
    + intro. apply H. left. assumption.
  - simpl. rewrite (no_touch__A _ _ x a1), (no_touch__A _ _ x a2).
    + reflexivity.
    + intro. apply H. right. assumption.
    + intro. apply H. left. assumption.
Qed.

Lemma IF_apply: forall s x x' e e',
    interference_free__S (Asgn__S x e) (Asgn__S x' e') ->
    Aapply (x !-> Aapply s e; s) e' = Aapply s e'.
Proof.
  intros.
  assert (no_contains: ~ (contains__A e' x)). {
    destruct (H x) as [_ [Hcontains _]]. intro contra. apply Hcontains.
    split; [reflexivity | assumption].
  }
  apply (no_touch__A _ _ _ _ no_contains).
Qed.

Lemma IF_asgn_cond: forall x e b s,
    interference_free__S (Asgn__S x e) (Cond b) ->
    Bapply (x !-> Aapply s e; s) b = Bapply s b.
Proof.
  intros. apply no_touch__B.
  specialize (H x). destruct H as [_ [H _]]. intro contra.
  apply H. split; [reflexivity | assumption].
Qed.

Lemma IF_simultaneous_subst: forall s x x' e e',
    interference_free__S (Asgn__S x e) (Asgn__S x' e') ->
    (x' !-> Aapply (x !-> Aapply s e; s) e'; x !-> Aapply s e; s) =
    (x !-> Aapply (x' !-> Aapply s e'; s) e; x' !-> Aapply s e'; s).
Proof.
  intros.
  assert (different_vars: x <> x'). {
    destruct (H x) as [_ [_ Hw]]. intro. apply Hw. subst. split; reflexivity.
  }
  assert (H': interference_free__S (Asgn__S x' e') (Asgn__S x e)) by (symmetry; assumption).
  rewrite (IF_apply _ _ _ _ _ H).
  rewrite (IF_apply _ _ _ _ _ H').
  rewrite (update_comm _ _ _ _ _ different_vars).
  reflexivity.
Qed.

Definition path_equiv__S: relation trace__S := permute_events interference_free__S.
Notation " t '~' t' " := (path_equiv__S t t') (at level 40).

Theorem equiv_acc_subst: forall s t t', t ~ t' -> acc_subst s t = acc_subst s t'.
Proof. apply (equiv_acc_subst_generic _ IF_simultaneous_subst). Qed.

Theorem equiv_pc: forall V t t', t ~ t' -> Beval V (pc t) = true <-> Beval V (pc t') = true.
Proof. apply (equiv_pc_generic _ _ IF_simultaneous_subst IF_asgn_cond). Qed.

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

Corollary equiv_star: forall s t1 s' t1' t2,
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

Variant head_red__POR: relation (trace__S * Stmt) :=
  | POR_intro: forall s s' t0 t0' t,
      t0 ~ t0' -> head_red__S (t0, s) (t, s') ->
      head_red__POR (t0', s) (t, s').

Definition red__POR := context_red is_context head_red__POR.
Definition red_star__POR := clos_refl_trans_n1 _ red__POR.

(** actually both correctness and completeness here only relies on equiv_step aka prefix closedness! *)
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
    destruct H3 as [t2' [Hstep Hequiv]].
    + transitivity t1; assumption.
    + constructor; assumption.
    + eexists t2'. split.
      * econstructor.
        ** apply Hstep.
        ** assumption.
      * assumption.
Qed.

Lemma completeness_step__POR: forall t0 t0' s0 t s,
    t0 ~ t0' -> red__S (t0, s0) (t, s) ->
    exists t', red__POR (t0', s0) (t', s)
        /\ t ~ t'.
Proof.
  intros.
  destruct (equiv_step _ _ _ _ _ H H0) as [t' [Hstep Hequiv]].
  dependent destruction Hstep.
  exists t'. split.
  + eapply ctx_red_intro.
    apply POR_intro with (t0 := t0').
    * reflexivity.
    * apply H1.
    * assumption.
  + assumption.
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
      try assumption.
    exists t_step. split.
    + econstructor.
      * apply comp_step.
      * apply IHcomp.
    + assumption.
Qed.

(** but TOTAL relies on both equiv_pc and equiv_acc_subst *)
Theorem correctness__total: forall s s' t0 t0' t V0,
    red_star__POR (t0, s) (t, s') ->
    Beval V0 (pc t) = true ->
    is_abstraction V0 t0' t0 ->
    exists t', red_star__C V0 (t0', s) (t', s')
        /\ is_abstraction V0 t' t.
Proof.
  intros.
  destruct (correctness__POR _ _ _ _ H) as [ts [comp__S equiv__S]].
  destruct (correctness _ _ _ _ t0' V0 comp__S) as [tc [comp__C Habs]].
    - rewrite <- (equiv_pc V0 t ts); assumption.
    - assumption.
    - exists tc. splits; try assumption.
      + symmetry. rewrite equiv_acc_subst with (t' := ts); assumption.
Qed.

Theorem completeness__total : forall s s' t0 t t0' V0,
    red_star__C V0 (t0, s) (t, s') ->
    is_abstraction V0 t0 t0' ->
    exists t', red_star__POR (t0', s) (t', s')
          /\ is_abstraction V0 t t'.
Proof.
  intros.
  destruct (completeness _ _ _ _ t0' V0 H H0) as [ts [comp__S [Hpc Habs]]].
  destruct (completeness__POR _ _ _ _ comp__S) as [t__POR [comp__POR Hequiv]].
  exists t__POR. splits.
  + assumption.
  + rewrite <- (equiv_pc V0 ts _); assumption.
  + rewrite equiv_acc_subst with (t' := ts).
    * assumption.
    * symmetry. assumption.
Qed.

(** Concrete POR *)
Definition interference_free__C: relation (Var * Aexpr) :=
  fun p1 p2 => let (x1, e1) := p1 in
            let (x2, e2) := p2 in
            x1 <> x2 /\ ~ (contains__A e1 x2) /\ ~ (contains__A e2 x1).

Definition path_equiv__C: relation trace__C := permute_events interference_free__C.
Notation " t '≃' t' " := (path_equiv__C t t') (at level 40).

Lemma no_touch_Aeval: forall V v x a, ~ (contains__A a x) -> Aeval (x !-> v ; V) a = Aeval V a.
Proof.
  induction a; intro.
  - reflexivity.
  - unfold contains__A in H. apply update_neq. assumption.
  - simpl. rewrite IHa1, IHa2.
    + reflexivity.
    + intro. apply H. right. assumption.
    + intro. apply H. left. assumption.
Qed.

Theorem equiv_acc_val: forall V0 t t', t ≃ t' -> acc_val V0 t = acc_val V0 t'.
Proof.
  intros. induction H; try auto. rewrite IHpermute_events1. assumption.
  (* the interesting case*)
  induction t'.
  - destruct e1, e2; simpl; try reflexivity. destruct H as [H1 [H2 H3]].
    apply not_eq_sym in H1.
    rewrite update_comm. rewrite 2 no_touch_Aeval. reflexivity.
    all: assumption.
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
  - apply path_equiv_extend; assumption.
Qed.

Corollary equiv_star__C: forall V0 s t1 s' t1' t2,
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

Definition red__PORC V := context_red is_context (head_red__PORC V).
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
  intros.
  destruct (equiv_step__C _ _ _ _ _ _ H H0) as [t' [Hstep Hequiv]].
  dependent destruction Hstep.
  exists t'. split.
  + eapply ctx_red_intro.
    apply POR_intro__C with (t0 := t0').
    * reflexivity.
    * apply H1.
    * assumption.
  + assumption.
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
      try assumption.
    exists t_step. split.
    + econstructor.
      * apply comp_step.
      * apply IHcomp.
    + assumption.
Qed.

(** Relationship between PORC and POR *)
(* PORC-POR relies on all 3: equiv_pc, equiv_acc_subst and equiv_acc_val*)
(* and equiv_extends actually, through the PORC results*)
Lemma equiv_is_abstraction: forall V0 ts ts' tc tc',
    ts ~ ts' -> tc ≃ tc' -> is_abstraction V0 tc ts -> is_abstraction V0 tc' ts'.
Proof.
  intros. destruct H1. split.
  - rewrite <- (equiv_pc V0 ts ts'); assumption.
  - rewrite <- (equiv_acc_subst _ ts ts');
      [rewrite <- (equiv_acc_val V0 tc tc') |]; assumption.
Qed.

Theorem POR_correctness: forall V0 s s' t0 t0' t,
    red_star__POR (t0, s) (t, s') ->
    Beval V0 (pc t) = true ->
    is_abstraction V0 t0' t0 ->
    exists t', red_star__PORC V0 (t0', s) (t', s')
        /\ is_abstraction V0 t' t.
Proof.
  intros.
  destruct (correctness__total _ _ _ t0' _ V0 H H0 H1) as [tc [Hcomp__C Habs]].
  destruct (completeness__PORC V0 _ _ _ _ Hcomp__C) as [t__PORC [Hcomp__PORC Hequiv]].
  exists t__PORC. split.
  + assumption.
  + apply (equiv_is_abstraction V0 t t tc t__PORC).
    * reflexivity.
    * assumption.
    * assumption.
Qed.

Theorem POR_completeness: forall V0 s s' t0 t0' t,
    red_star__PORC V0 (t0, s) (t, s') ->
    is_abstraction V0 t0 t0' ->
    exists t', red_star__POR (t0', s) (t', s')
        /\ is_abstraction V0 t t'.
Proof.
  intros.
  destruct (correctness__PORC V0 _ _ _ _ H) as [tc [Hcomp__C Hequiv]].
  destruct (completeness__total _ _ _ _ _ V0 Hcomp__C H0) as [t__POR [Hcomp__POR Habs]].
  exists t__POR. split.
  + assumption.
  + apply (equiv_is_abstraction V0 t__POR t__POR tc t).
    * reflexivity.
    * symmetry; assumption.
    * assumption.
Qed.
