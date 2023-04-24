(** * Partial Order Reduction - Defining POR semantics and proving bisimulation*)

From Coq Require Import String Bool Datatypes Relations Program.Equality Classes.RelationClasses.

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Parallel Traces.
Import TraceSemantics IndependenceEquiv.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import TraceSemantics.

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

Example independent_inc: forall s,
    (X !-> Aapply (X !-> Aapply s <{X + 1}>; s) <{X + 1}>; X !-> Aapply s <{X + 1}>; s) =
    (X !-> Aapply (X !-> Aapply s <{X + 1}>; s) <{X + 1}>; X !-> Aapply s <{X + 1}>; s).
Proof. intro. reflexivity. Qed.

Definition path_equiv__S: relation trace__S := permute_events interference_free__S.
Notation " t '~' t' " := (path_equiv__S t t') (at level 40).

Theorem equiv_acc_subst: forall s t t', t ~ t' -> acc_subst s t = acc_subst s t'.
Proof. apply (equiv_acc_subst_generic _ IF_simultaneous_subst). Qed.

Theorem equiv_pc: forall V t t', t ~ t' -> Beval V (pc t) = true <-> Beval V (pc t') = true.
Proof. apply (equiv_pc_generic _ _ IF_simultaneous_subst IF_asgn_cond). Qed.

(* These are identical to the generic case, and should be easily generalizable when time *)
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

Theorem bisim__POR: forall s s' t0 t0',
    t0 ~ t0' ->
    (forall t, red__POR (t0, s) (t, s') -> exists t', red__S (t0', s) (t', s') /\ t ~ t')
  /\ (forall t, red__S (t0, s) (t, s') -> exists t', red__POR (t0', s) (t', s') /\ t ~ t').
Proof.
  split; intros.
  - dependent destruction H0. dependent destruction H0.
    destruct (equiv_step (C s0) t1 (C s'0) t t0') as [t2' [Hstep Hequiv]];
      [transitivity t0 | constructor |]; try assumption.
    exists t2'. split; assumption.
  - destruct (equiv_step s t0 s' t t0' H H0) as [t2' [Hstep Hequiv]].
    dependent destruction Hstep.
    exists t2'. split.
    + eapply ctx_red_intro.
      * apply POR_intro with (t0 := t0').
        ** reflexivity.
        ** assumption.
      * assumption.
    + assumption.
Qed.

Corollary correctness__POR: forall s0 t0 s t,
    red_star__POR (t0, s0) (t, s) ->
    exists t', red_star__S (t0, s0) (t', s) /\ t ~ t'.
Proof.
  intros. dependent induction H.
  - exists t. split; constructor.
  - destruct y. destruct (IHclos_refl_trans_n1 s0 t0 s1 t1) as [t' [IHcomp IHequiv]];
      try reflexivity.
    destruct (bisim__POR s1 s t1 t' IHequiv) as [bisim_correct _].
    destruct (bisim_correct t H) as [t0' [bisim_step bisim_equiv]].
    exists t0'. split.
    + econstructor.
      * apply bisim_step.
      * apply IHcomp.
    + apply bisim_equiv.
Qed.

Corollary completeness__POR: forall t0 s0 t s,
    red_star__S (t0, s0) (t, s) ->
    exists t', red_star__POR (t0, s0) (t', s)
        /\ t ~ t'.
Proof.
  intros. dependent induction H.
  - exists t. split; constructor.
  - destruct y.
    destruct (IHclos_refl_trans_n1 t0 s0 t1 s1) as [t' [IHcomp IHequiv]];
      try reflexivity.
    destruct (bisim__POR s1 s t1 t' IHequiv) as [_ bisim_complete].
    destruct (bisim_complete t H) as [t0' [bisim_step bisim_equiv]].
    exists t0'. split.
    + econstructor.
      * apply bisim_step.
      * apply IHcomp.
    + apply bisim_equiv.
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
Proof. apply equiv_acc_val_generic. unfold sim_subst__C. intros.
       destruct H as [H1 [H2 H3]].
       rewrite (update_comm _ _ _ _ _ H1).
       rewrite (no_touch_Aeval _ _ _ _ H2).
       rewrite (no_touch_Aeval _ _ _ _ H3).
       reflexivity.
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

Theorem bisim__PORC: forall V s s' t0 t0',
    t0 ≃ t0' ->
    (forall t, red__PORC V (t0, s) (t, s') -> exists t', red__C V (t0', s) (t', s') /\ t ≃ t')
  /\ (forall t, red__C V (t0, s) (t, s') -> exists t', red__PORC V (t0', s) (t', s') /\ t ≃ t').
Proof.
  (* this proof (and formulation) is identical to the symbolic case *)
  split; intros.
  - dependent destruction H0. dependent destruction H0.
    destruct (equiv_step__C V (C s0) t1 (C s'0) t t0') as [t2' [Hstep Hequiv]];
      [transitivity t0 | constructor |]; try assumption.
    exists t2'. split; assumption.
  - destruct (equiv_step__C V s t0 s' t t0' H H0) as [t2' [Hstep Hequiv]].
    dependent destruction Hstep.
    exists t2'. split.
    + eapply ctx_red_intro.
      * apply POR_intro__C with (t0 := t0').
        ** reflexivity.
        ** assumption.
      * assumption.
    + assumption.
Qed.

Corollary correctness__PORC: forall V s0 t0 s t,
    red_star__PORC V (t0, s0) (t, s) ->
    exists t', red_star__C V (t0, s0) (t', s) /\ t ≃ t'.
Proof.
  intros. dependent induction H.
  - exists t. split; constructor.
  - destruct y. destruct (IHclos_refl_trans_n1 s0 t0 s1 t1) as [t' [IHcomp IHequiv]];
      try reflexivity.
    destruct (bisim__PORC V s1 s t1 t' IHequiv) as [bisim_correct _].
    destruct (bisim_correct t H) as [t0' [bisim_step bisim_equiv]].
    exists t0'. split.
    + econstructor.
      * apply bisim_step.
      * apply IHcomp.
    + apply bisim_equiv.
Qed.

Corollary completeness__PORC: forall V t0 s0 t s,
    red_star__C V (t0, s0) (t, s) ->
    exists t', red_star__PORC V (t0, s0) (t', s)
        /\ t ≃ t'.
Proof.
  intros. dependent induction H.
  - exists t. split; constructor.
  - destruct y.
    destruct (IHclos_refl_trans_n1 t0 s0 t1 s1) as [t' [IHcomp IHequiv]];
      try reflexivity.
    destruct (bisim__PORC V s1 s t1 t' IHequiv) as [_ bisim_complete].
    destruct (bisim_complete t H) as [t0' [bisim_step bisim_equiv]].
    exists t0'. split.
    + econstructor.
      * apply bisim_step.
      * apply IHcomp.
    + apply bisim_equiv.
Qed.

(** Relationship between PORC and POR *)

(* PORC-POR relies on all 3: equiv_pc, equiv_acc_subst and equiv_acc_val*)
Lemma equiv_is_abstraction: forall V0 ts ts' tc tc',
    ts ~ ts' -> tc ≃ tc' -> is_abstraction V0 tc ts -> is_abstraction V0 tc' ts'.
Proof.
  intros. destruct H1. split.
  - rewrite <- (equiv_pc V0 ts ts'); assumption.
  - rewrite <- (equiv_acc_subst _ ts ts');
      [rewrite <- (equiv_acc_val V0 tc tc') |]; assumption.
Qed.

Theorem POR_bisim: forall V s s' t0 t0',
    is_abstraction V t0 t0' ->
    (forall t, red__PORC V (t0, s) (t, s') ->
          exists t', (red__POR (t0', s) (t', s')) /\ is_abstraction V t t')
    /\ (forall t, red__POR (t0', s) (t, s') /\ Beval V (pc t) = true ->
            (exists t', red__PORC V (t0, s) (t', s') /\ acc_val V t' = Comp V (acc_subst id_sub t))).
Proof.
  intros.
  (* I suppose I could do this directly, but c'mon *)
  destruct (bisimulation V s s' t0 t0' H) as [complete correct].
  destruct (bisim__POR s s' t0' t0' (trace_eq_refl t0')) as [PORcomplete PORcorrect].
  destruct (bisim__PORC V s s' t0 t0 (trace_eq_refl t0)) as [PORCcomplete PORCcorrect].

  split; intros.
  - destruct (PORCcomplete t H0) as [t' [Ccomp Cequiv]].
    destruct (complete t' Ccomp) as [t'' [Scomp Habs]].
    destruct (PORcorrect t'' Scomp) as [ts [PORcomp PORequiv]].
    exists ts. split.
    + apply PORcomp.
    + symmetry in Cequiv. apply (equiv_is_abstraction V t'' ts t' t PORequiv Cequiv Habs).
  - destruct H0. destruct (PORcomplete t H0) as [t' [Scomp Sequiv]].
    destruct (correct t') as [t'' [Ccomp Habs]];
      [ split;
        [ apply Scomp
        | rewrite <- (equiv_pc V t t' Sequiv); apply H1] |].
    destruct (PORCcorrect t'' Ccomp) as [tc [PORCcomp Cequiv]].
      exists tc. split.
    * apply PORCcomp.
    * rewrite <- (equiv_acc_val V t'' tc Cequiv).
      rewrite (equiv_acc_subst _ t t' Sequiv).
      apply Habs.
Qed.

Lemma pc_monotone_step__POR : forall V0 s1 s2 t1 t2,
    red__POR (t1, s1) (t2, s2) -> Beval V0 (pc t2) = true -> Beval V0 (pc t1) = true.
Proof. intros. inversion H. inversion H4; inversion H12; subst;
         try (rewrite <- (equiv_pc _ t0 t1));
         try (rewrite <- (equiv_pc _ t2 t1));
         try (simpl in H0; assumption);
         try(eapply pc_monotone; apply H0).
Qed.

Corollary POR_correctness: forall V0 s s' t0 t0' t,
    red_star__POR (t0, s) (t, s') ->
    Beval V0 (pc t) = true ->
    is_abstraction V0 t0' t0 ->
    exists t', red_star__PORC V0 (t0', s) (t', s')
        /\ is_abstraction V0 t' t.
Proof.
  intros.
  dependent induction H.
  - eexists. split; [constructor | assumption].
  - destruct y. destruct (IHclos_refl_trans_n1 s s0 t0 t1 eq_refl eq_refl) as [t' [IHcomp [IHpc IHabs]]];
      try assumption.
    rewrite (pc_monotone_step__POR _ _ _ _ _ H H1). reflexivity.
    destruct (POR_bisim V0 s0 s' t' t1) as [_ bisim_correct];
      try assumption.
    split; assumption.
    edestruct (bisim_correct t) as [tc [Hstep Habs]]. split.
    + apply H.
    + assumption.
    + exists tc. splits.
      * econstructor.
        -- apply Hstep.
        -- apply IHcomp.
      * assumption.
      * symmetry. apply Habs.
Qed.

Corollary POR_completeness: forall V0 s s' t0 t0' t,
    red_star__PORC V0 (t0, s) (t, s') ->
    is_abstraction V0 t0 t0' ->
    exists t', red_star__POR (t0', s) (t', s')
        /\ is_abstraction V0 t t'.
Proof.
  intros.
  dependent induction H.
  - eexists. split; [constructor | assumption].
  - destruct y. destruct (IHclos_refl_trans_n1 s s0 t0 t1 eq_refl eq_refl) as [t' [IHcomp [IHpc IHabs]]];
      try assumption.
    destruct (POR_bisim V0 s0 s' t1 t') as [bisim_complete _];
      try assumption.
    split; assumption.
    edestruct (bisim_complete t) as [ts [Hstep Habs]].
    + apply H.
    + exists ts. splits.
      * econstructor.
        -- apply Hstep.
        -- apply IHcomp.
      * apply (proj1 Habs).
      * apply (proj2 Habs).
Qed.

(** total relies on both equiv_pc and equiv_acc_subst *)
Theorem bisim__total: forall V s s' t0 t0',
    is_abstraction V t0 t0' ->
    (forall t, red__C V (t0, s) (t, s') ->
          exists t', (red__POR (t0', s) (t', s')) /\ is_abstraction V t t')
    /\ (forall t, red__POR (t0', s) (t, s') /\ Beval V (pc t) = true ->
            (exists t', red__C V (t0, s) (t', s') /\ acc_val V t' = Comp V (acc_subst id_sub t))).
Proof.
  intros.
  destruct (bisimulation V s s' t0 t0' H) as [complete correct].
  destruct (bisim__POR s s' t0' t0' (trace_eq_refl t0')) as [PORcomplete PORcorrect].

  split; intros.
  - destruct (complete t H0) as [ts [Scomp Habs]].
    destruct (PORcorrect ts Scomp) as [t__POR [PORcomp Hequiv]].
    exists t__POR. split.
    + apply PORcomp.
    + apply (equiv_is_abstraction V ts t__POR t t Hequiv (trace_eq_refl t) Habs).
  - destruct H0. destruct (PORcomplete t H0) as [t__POR [PORcomp Hequiv]].
    destruct (correct t__POR) as [tc [Ccomp Habs]]. split.
    + apply PORcomp.
    + rewrite <- (equiv_pc V t t__POR); assumption.
    + exists tc. split.
      * apply Ccomp.
      * rewrite (equiv_acc_subst _ t t__POR); assumption.
Qed.

Corollary correctness__total: forall s s' t0 t0' t V0,
    red_star__POR (t0, s) (t, s') ->
    Beval V0 (pc t) = true ->
    is_abstraction V0 t0' t0 ->
    exists t', red_star__C V0 (t0', s) (t', s')
        /\ is_abstraction V0 t' t.
Proof.
  intros.
  dependent induction H.
  - eexists. split; [constructor | assumption].
  - destruct y. destruct (IHclos_refl_trans_n1 s s0 t0 t1 eq_refl eq_refl) as [t' [IHcomp [IHpc IHabs]]];
      try assumption.
    rewrite (pc_monotone_step__POR _ _ _ _ _ H H1). reflexivity.
    destruct (bisim__total V0 s0 s' t' t1) as [_ bisim_correct];
      try assumption.
    split; assumption.
    edestruct (bisim_correct t) as [tc [Hstep Habs]]. split.
    + apply H.
    + assumption.
    + exists tc. splits.
      * econstructor.
        -- apply Hstep.
        -- apply IHcomp.
      * assumption.
      * symmetry. apply Habs.
Qed.

Theorem completeness__total : forall s s' t0 t t0' V0,
    red_star__C V0 (t0, s) (t, s') ->
    is_abstraction V0 t0 t0' ->
    exists t', red_star__POR (t0', s) (t', s')
          /\ is_abstraction V0 t t'.
Proof.
  intros.
  dependent induction H.
  - eexists. split; [constructor | assumption].
  - destruct y. destruct (IHclos_refl_trans_n1 s s0 t0 t1 eq_refl eq_refl) as [t' [IHcomp [IHpc IHabs]]];
      try assumption.
    destruct (bisim__total V0 s0 s' t1 t') as [bisim_complete _];
      try assumption.
    split; assumption.
    edestruct (bisim_complete t) as [ts [Hstep Habs]].
    + apply H.
    + exists ts. splits.
      * econstructor.
        -- apply Hstep.
        -- apply IHcomp.
      * apply (proj1 Habs).
      * apply (proj2 Habs).
Qed.

Theorem completeness__total' : forall V s s' t0 t t0',
    red_star__C V (t0, s) (t, s') ->
    is_abstraction V t0 t0' ->
    exists t', red_star__POR (t0', s) (t', s')
          /\ is_abstraction V t t'.
Proof.
  intros.
  destruct (completeness__PORC V t0 s t s' H) as [tc [PORC_comp PORC_equiv]].
  destruct (POR_completeness V s s' _ _ _ PORC_comp H0) as [ts [POR_comp POR_abs]].
  exists ts. split.
  + assumption.
  + apply (equiv_is_abstraction V ts ts tc t).
    * reflexivity.
    * symmetry. apply PORC_equiv.
    * apply POR_abs.
Qed.

Theorem correctness__total': forall V s s' t0 t0' t,
    red_star__POR (t0, s) (t, s') ->
    Beval V (pc t) = true ->
    is_abstraction V t0' t0 ->
    exists t', red_star__C V (t0', s) (t', s')
        /\ is_abstraction V t' t.
Proof.
  intros.
  destruct (POR_correctness V s s' t0 t0' t H H0 H1) as [t__PORC [Hcomp Habs]].
  destruct (correctness__PORC V s t0' s' t__PORC Hcomp) as [tc [Ccomp Cequiv]].
  exists tc. split.
  + apply Ccomp.
  + eapply equiv_is_abstraction.
    * reflexivity.
    * apply Cequiv.
    * apply Habs.
Qed.
