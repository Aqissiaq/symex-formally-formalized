(** * Partial Order Reduction - Wrapping the POR stuff in a module with independence as parameter *)

From Coq Require Import String Bool Datatypes Relations Program.Equality Classes.RelationClasses.

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Parallel Traces.
Import TraceSemantics.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import ContextReduction.

Module Type INDEP_SIG.
  Parameter Indep : relation trace_step__S.
  Parameter sym: Symmetric Indep.
  Parameter has_sim_subst: sim_subst Indep.
  Parameter has_subst_bapply: subst_bapply Indep.
End INDEP_SIG.

Module POR (indep: INDEP_SIG).
  Definition path_equiv__S: relation trace__S := permute_events indep.Indep.
  Notation " t '~' t' " := (path_equiv__S t t') (at level 40).

  Theorem equiv_acc_subst: forall s t t', t ~ t' -> acc_subst s t = acc_subst s t'.
  Proof. apply (equiv_acc_subst_generic _ indep.has_sim_subst). Qed.

  Theorem equiv_pc: forall V t t', t ~ t' -> Beval V (pc t) = true <-> Beval V (pc t') = true.
  Proof. apply (equiv_pc_generic _ indep.sym indep.has_sim_subst indep.has_subst_bapply). Qed.

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

  (** actually bisimulation only relies on equiv_step aka prefix closedness! *)
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
End POR.
