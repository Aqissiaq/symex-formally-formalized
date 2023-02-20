(** * Semantics by Head reductions in context *)

From Coq Require Import String Bool Datatypes Relations Program.Equality.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Parallel.

From SymEx Require Import Traces.
Import TraceSemantics.

From SymEx Require Import Maps.
Import BasicMaps.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.

Ltac splits := repeat (try split).

(** Generalized context unfolding *)
(** idea from: https://xavierleroy.org/cdf-mech-sem/CDF.FUN.html *)
Inductive is_context: (Stmt -> Stmt) -> Prop :=
| is_context_hole: is_context (fun x => x)
| is_context_seq: forall s C,
    is_context C -> is_context (fun x => SSeq (C x) s)
| is_context_par_left: forall s C,
    is_context C -> is_context (fun x => SPar (C x) s)
| is_context_par_right: forall s C,
    is_context C -> is_context (fun x => SPar s (C x))
.

Inductive context_red {X:Type} (head_red: relation (X * Stmt)): (X * Stmt) -> (X * Stmt) -> Prop :=
| ctx_red_intro: forall C t t' s s',
    head_red (t, s) (t', s') -> is_context C ->
    context_red head_red (t, C s) (t', C s')
.

(* properties of contexts *)
Lemma context_comp: forall C C', is_context C -> is_context C' -> is_context (fun s => C (C' s)).
Proof. intros. induction H; induction H0; constructor; assumption. Qed.

Lemma under_C {X: Type} (r: relation (X * Stmt)): forall C s s' t t',
    context_red r (t, s) (t', s') -> is_context C -> context_red r (t, C s) (t', C s').
Proof.
  intros. dependent destruction H. apply ctx_red_intro with (C := fun s => C (C0 s)).
  - assumption.
  - apply context_comp; assumption.
Qed.

Lemma context_injective: forall C s s',
    is_context C -> C s = C s' -> s = s'.
Proof.
  intros. induction H;
    try (inversion H0; apply IHis_context);
    assumption.
Qed.

(** Symbolic Semantics *)
Inductive head_red__S: (trace__S * Stmt) -> (trace__S * Stmt) -> Prop :=
| head_red_asgn__S: forall t x e,
    head_red__S (t, <{ x := e }>) (t :: Asgn__S x e, SSkip)
| head_red_cond_true__S: forall t b s1 s2,
    head_red__S (t, <{ if b {s1} {s2} }>) (t :: Cond b, s1)
| head_red_cond_false__S: forall t b s1 s2,
    head_red__S (t, <{ if b {s1} {s2} }>) (t :: Cond (BNot b), s2)
(* I don't love these cases, they're a bit inelegant *)
| head_red_skip_seq__S: forall s t,
    head_red__S (t, <{skip ; s}>) (t, s)
| head_red_skip_par_l__S: forall s t,
    head_red__S (t, <{skip || s}>) (t, s)
| head_red_skip_par_r__S: forall s t,
    head_red__S (t, <{s || skip }>) (t, s)
.

Definition red__S := context_red head_red__S.
Definition red_star__S := clos_refl_trans_n1 _ red__S.

Example X: Var := "x".
Example Y: Var := "y".

Example par_simple_0: red__S ([], <{ (X := 1 ; Y := 1 || Y := 2) || X := 2}>)
                        ([Asgn__S X 1], <{ (skip ; Y := 1 || Y := 2) || X := 2 }>).
Proof. apply ctx_red_intro with (C := fun x => <{ (x ; Y := 1 || Y := 2) || X := 2}>); repeat constructor. Qed.

Example par_simple_1: red__S ([Asgn__S X 1], <{ (Y := 1 || Y := 2) || X := 2 }>)
                        ([Asgn__S X 1 ; Asgn__S Y 2], <{ (Y := 1 || skip) || X := 2 }>).
Proof. apply ctx_red_intro with (C := fun x => <{ (Y := 1 || x) || X := 2 }>); repeat constructor. Qed.

Example par_simple_2: red__S ([Asgn__S X 1 ; Asgn__S Y 2], <{ Y := 1 || X := 2 }>)
                        ([Asgn__S X 1 ; Asgn__S Y 2 ; Asgn__S X 2], <{ Y := 1 || skip }>).
Proof. eapply ctx_red_intro; repeat constructor. Qed.

Example par_simple_3: red__S ([Asgn__S X 1 ; Asgn__S Y 2 ; Asgn__S X 2], <{ Y := 1 }>)
                        ([Asgn__S X 1 ; Asgn__S Y 2 ; Asgn__S X 2 ; Asgn__S Y 1], <{ skip }>) .
Proof. eapply ctx_red_intro with (C := fun x => x); repeat constructor. Qed.

Example par_simple: red_star__S ([], <{ (X := 1 ; Y := 1 || Y := 2) || X := 2}>)
                      ([Asgn__S X 1 ; Asgn__S Y 2 ; Asgn__S X 2 ; Asgn__S Y 1], <{ skip }>).
Proof.
  econstructor. apply par_simple_3.
  econstructor. apply ctx_red_intro with (C := fun x => x). apply head_red_skip_par_r__S. constructor.
  econstructor. apply par_simple_2.
  econstructor. apply ctx_red_intro with (C := fun x => <{ x || X := 2 }>);
    [ apply head_red_skip_par_r__S| repeat constructor].
  econstructor. apply par_simple_1.
  econstructor. apply ctx_red_intro with (C := fun x => <{ x || X := 2 }>);
    [ apply head_red_skip_seq__S | repeat constructor].
  econstructor. apply par_simple_0.
  constructor.
Qed.

(** Concrete Semantics *)

Inductive head_red__C (V0:Valuation): (trace__C * Stmt) -> (trace__C * Stmt) -> Prop :=
| head_red_asgn__C: forall t x e,
    head_red__C V0 (t, <{ x := e }>) (t :: (x, Aeval_t V0 t e), SSkip)
| head_red_cond__C: forall t b s1 s2,
    head_red__C V0 (t, <{ if b {s1} {s2} }>) (t, if (Beval_t V0 t b) then s1 else s2)
(* I don't love these cases, they're a bit inelegant *)
| head_red_skip_seq__C: forall s t,
    head_red__C V0 (t, <{skip ; s}>) (t, s)
| head_red_skip_par_l__C: forall s t,
    head_red__C V0 (t, <{skip || s}>) (t, s)
| head_red_skip_par_r__C: forall s t,
    head_red__C V0 (t, <{s || skip }>) (t, s)
.

Definition red__C (V0:Valuation) := context_red (head_red__C V0).
Definition red_star__C (V0:Valuation) := clos_refl_trans_n1 _ (red__C V0).

(** Properties *)
Lemma pc_monotone_step : forall V0 s1 s2 t1 t2, red__S (t1, s1) (t2, s2) -> Beval V0 (pc t2) = true -> Beval V0 (pc t1) = true.
Proof. intros. inversion H. inversion H4; subst;
         simpl in H0; try (apply andb_true_iff in H0; destruct H0); assumption.
Qed.

Theorem correctness_step : forall s s' t0 t t0' V0,
    red__S (t0, s) (t, s') ->
    Beval V0 (pc t) = true ->
    acc_val V0 t0' = Comp V0 (acc_subst id_sub t0) ->
    exists t', red__C V0 (t0', s) (t', s') /\ acc_val V0 t' = Comp V0 (acc_subst id_sub t).
Proof.
  intros. dependent destruction H. dependent induction H;
    (* the skips*)
    try (exists t0'; splits; [constructor | assumption | assumption]).
  - eexists. splits.
    + apply head_red_asgn__C.
    + assumption.
    + unfold Aeval_t. simpl. rewrite asgn_sound. rewrite H2. reflexivity.
  - simpl in H1. apply andb_true_iff in H1. destruct H1.
    unfold Bapply_t in H. rewrite <- comp_subB in H. rewrite <- H2 in H.
    exists t0'. splits.
    (* there's got to be a better way to do this...*)
    + assert (head_red__C V0 (t0', <{ if b {s'0}{s2} }>) (t0', if Beval_t V0 t0' b then s'0 else s2)) by constructor.
      unfold Beval_t in H3. rewrite H in H3. apply H3.
    + assumption.
    + simpl. assumption.
  - simpl in H1. apply andb_true_iff in H1. destruct H1.
    apply negb_true_iff in H.
    unfold Bapply_t in H. rewrite <- comp_subB in H. rewrite <- H2 in H.
    exists t0'. splits.
    (* there's got to be a better way to do this...*)
    + assert (head_red__C V0 (t0', <{ if b {s1}{s'0} }>) (t0', if Beval_t V0 t0' b then s1 else s'0)) by constructor.
      unfold Beval_t in H3. rewrite H in H3. apply H3.
    + assumption.
    + simpl. assumption.
Qed.

Theorem correctness : forall s s' t0 t t0' V0,
    red_star__S (t0, s) (t, s') ->
    Beval V0 (pc t) = true ->
    acc_val V0 t0' = Comp V0 (acc_subst id_sub t0) ->
    exists t', red_star__C V0 (t0', s) (t', s') /\ acc_val V0 t' = Comp V0 (acc_subst id_sub t).
Proof.
  intros. dependent induction H.
  - eexists. splits. apply rtn1_refl. assumption.
  - destruct y. remember (pc_monotone_step V0 _ _ _ _ H H1).
    edestruct IHclos_refl_trans_n1 as [t' [IHcomp IHabs]];
      try reflexivity; try assumption.
    destruct (correctness_step _ _ _ _ t' V0 H H1 IHabs) as [t_step [Hstep Habs_step]].
    eexists. splits.
    + econstructor. apply Hstep. apply IHcomp.
    + assumption.
Qed.

Lemma completeness_step : forall s s' t0 t t0' V0,
    red__C V0 (t0, s) (t, s') ->
    is_abstraction V0 t0 t0' ->
    exists t', red__S (t0', s) (t', s')
          /\ is_abstraction V0 t t'.
Proof.
  intros. dependent destruction H. dependent induction H;
    destruct H1;
    (* the skips*)
    try (exists t0'; splits; [constructor | assumption | assumption | assumption]).
  - eexists. splits.
    + constructor.
    + assumption.
    + simpl. assumption.
    + unfold Aeval_t. simpl. rewrite asgn_sound. rewrite H1. reflexivity.
  - destruct (Beval_t V0 t b) eqn:Hbranch; unfold Beval_t in Hbranch.
    + eexists. splits.
      * apply head_red_cond_true__S.
      * assumption.
      * simpl. apply andb_true_iff. split.
        ** unfold Bapply_t. rewrite <- comp_subB. rewrite H1. assumption.
        ** assumption.
      * simpl. assumption.
    + eexists. splits.
      * apply head_red_cond_false__S.
      * assumption.
      * simpl. apply andb_true_iff. split.
        ** unfold Bapply_t. rewrite <- comp_subB. rewrite H1. apply negb_true_iff. assumption.
        ** assumption.
      * simpl. assumption.
Qed.

Theorem completeness : forall s s' t0 t t0' V0,
    red_star__C V0 (t0, s) (t, s') ->
    is_abstraction V0 t0 t0' ->
    exists t', red_star__S (t0', s) (t', s')
          /\ is_abstraction V0 t t'.
Proof.
  intros. dependent induction H.
  - eexists. splits; destruct H0; try (apply rtn1_refl); assumption.
  - destruct y. edestruct IHclos_refl_trans_n1 as [t' [IHcomp [IHpc IHabs]]];
      try reflexivity; try assumption.
    destruct (completeness_step _ _ _ _ t' _ H) as [t_step [Hstep [Hpc Habs]]]; try assumption.
    split; assumption.
    eexists. splits.
    + econstructor. apply Hstep. apply IHcomp.
    + apply Hpc.
    + apply Habs.
Qed.

(** * Sympaths - Trying out some stuff from Sympaths paper*)
(* No thread identifiers, idk how that complicates things yet*)

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
        | apply SSeq_disjoint in H6
        | apply SPar_right_disjoint in H6
        | apply SPar_left_disjoint in H6];
        contradiction.
Qed.

Lemma POR_bisim_step: forall s t1 s' t1' t2,
    t1 ~ t2 -> red__S (t1, s) (t1', s') ->
    exists t2', red__S (t2, s) (t2', s') /\ t1' ~ t2'.
Proof.
  intros. inversion H0; subst. inversion H4; subst; eexists; split;
    try (constructor; [constructor | assumption]);
    try (apply path_equiv_extend);
    assumption.
Qed.

Theorem POR_bisim: forall s t1 s' t1' t2,
    t1 ~ t2 -> red_star__S (t1, s) (t1', s') ->
    exists t2', red_star__S (t2, s) (t2', s') /\ t1' ~ t2'.
Proof.
  intros. dependent induction H0.
  - exists t2. split; [constructor | assumption].
  - destruct y. edestruct (IHclos_refl_trans_n1 s t1 s0 t) as [t2' [IHcomp IHequiv]];
      try assumption; try reflexivity.
    destruct (POR_bisim_step _ _ _ _ _ IHequiv H1) as [t2_final [comp_final equiv_final]].
    exists t2_final. split.
    + econstructor. apply comp_final. apply IHcomp.
    + assumption.
Qed.


(* Framing, because it shows up in several proofs *)
(* Framing corresponds to accumulated substitutions with different initial states
   when working with (this style of) traces. We will see how hard/easy that is to incorporate
*)
