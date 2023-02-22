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
| head_red_loop_true__S: forall t b s,
    head_red__S (t, <{ while b {s} }>) (t :: Cond b, <{s ; while b {s}}>)
| head_red_loop_false__S: forall t b s,
    head_red__S (t, <{ while b {s} }>) (t :: Cond (BNot b), SSkip)
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
| head_red_loop__C: forall t b s,
    head_red__C V0 (t, <{while b {s}}>) (t, if (Beval_t V0 t b) then <{s ; while b {s}}> else SSkip)
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
  - simpl in H1. apply andb_true_iff in H1. destruct H1.
    unfold Bapply_t in H. rewrite <- comp_subB in H. rewrite <- H2 in H.
    exists t0'. splits.
    (* there's got to be a better way to do this...*)
    + assert (head_red__C V0 (t0', <{ while b {s} }>) (t0', if Beval_t V0 t0' b then <{s ; while b {s}}> else SSkip)) by constructor.
      unfold Beval_t in H3. rewrite H in H3. apply H3.
    + assumption.
    + simpl. assumption.
  - simpl in H1. apply andb_true_iff in H1. destruct H1.
    apply negb_true_iff in H.
    unfold Bapply_t in H. rewrite <- comp_subB in H. rewrite <- H2 in H.
    exists t0'. splits.
    (* there's got to be a better way to do this...*)
    + assert (head_red__C V0 (t0', <{ while b {s} }>) (t0', if Beval_t V0 t0' b then <{s ; while b {s}}> else SSkip)) by constructor.
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
  - destruct (Beval_t V0 t b) eqn:Hbranch; unfold Beval_t in Hbranch.
    + eexists. splits.
      * apply head_red_loop_true__S.
      * assumption.
      * simpl. apply andb_true_iff. split.
        ** unfold Bapply_t. rewrite <- comp_subB. rewrite H1. assumption.
        ** assumption.
      * simpl. assumption.
    + eexists. splits.
      * apply head_red_loop_false__S.
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
