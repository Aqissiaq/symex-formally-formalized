(** * Partial Order Reduction - Trying out some stuff from Sympaths paper*)

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

(** Symbolic POR *)
Definition path_equiv__S: relation trace__S :=
  fun t t' => (forall s, acc_subst s t = acc_subst s t') /\ forall V, Beval V (pc t) = Beval V (pc t').
Notation " t '~' t' " := (path_equiv__S t t') (at level 40).

Global Instance trace_eq_refl: Reflexive path_equiv__S.
Proof. intro. unfold path_equiv__S. split; reflexivity. Qed.

Global Instance trace_eq_sym: Symmetric path_equiv__S.
Proof. unfold path_equiv__S, Symmetric. intros. edestruct H as [Hsubst Hpc]. split; symmetry;
         [apply Hsubst | apply Hpc].
Qed.

Global Instance trace_eq_trans: Transitive path_equiv__S.
Proof. unfold path_equiv__S, Transitive. intros.
       edestruct H as [Hsubst Hpc].
       edestruct H0 as [Hsubst0 Hpc0].
       split; intros.
       - transitivity (acc_subst s y);
           [ apply Hsubst | apply Hsubst0].
       - transitivity (Beval V (pc y));
           [ apply Hpc |  apply Hpc0].
Qed.

Lemma path_equiv_extend: forall t t' e,
    path_equiv__S t t' -> path_equiv__S (t :: e) (t' :: e).
Proof.
  intros. unfold path_equiv__S in *. intros.
  edestruct H as [Hsubst Hpc]. split; intros.
  - destruct e; simpl; rewrite Hsubst; reflexivity.
  - destruct e; simpl; rewrite Hpc.
    + reflexivity.
    + unfold Bapply_t. rewrite Hsubst. reflexivity.
Qed.

Theorem equiv_acc_subst: forall s t t', t ~ t' -> acc_subst s t = acc_subst s t'.
Proof. intros. edestruct H as [Hsubst _]. apply Hsubst. Qed.

Theorem equiv_pc: forall V t t', t ~ t' -> Beval V (pc t) = true <-> Beval V (pc t') = true.
Proof. intros. edestruct H as [_ Hpc]. rewrite Hpc. reflexivity. Qed.

Lemma equiv_step: forall s t1 s' t1' t2,
    t1 ~ t2 -> red__S (t1, s) (t1', s') ->
    exists t2', red__S (t2, s) (t2', s') /\ t1' ~ t2'.
Proof.
  intros. inversion H0; subst.
  inversion H4; subst; eexists; split;
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
  - exists t. split; constructor; reflexivity.
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
  - exists t. split; constructor; reflexivity.
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
Definition path_equiv__C: relation trace__C := fun t t' => forall V, acc_val V t = acc_val V t'.
Notation " t '≃' t' " := (path_equiv__C t t') (at level 40).

Theorem equiv_acc_val: forall V0 t t', t ≃ t' -> acc_val V0 t = acc_val V0 t'.
Proof. intros. apply H. Qed.

Theorem path_equiv_extend__C: forall t t' e, t ≃ t' -> (t :: e) ≃ (t' :: e).
Proof. intros. unfold path_equiv__C. intro. destruct e. simpl.
       rewrite H. reflexivity.
Qed.

Global Instance trace_eq_refl__C: Reflexive path_equiv__C.
Proof. intros x V. reflexivity. Qed.

Global Instance trace_eq_sym__C: Symmetric path_equiv__C.
Proof. unfold path_equiv__C, Symmetric. intros. symmetry. apply H. Qed.

Global Instance trace_eq_trans__C: Transitive path_equiv__C.
Proof. unfold path_equiv__C, Transitive. intros.
       transitivity (acc_val V y);
         [apply H | apply H0].
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
  - apply path_equiv_extend__C; assumption.
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
  destruct (bisim__PORC V s s' t0 t0 (trace_eq_refl__C t0)) as [PORCcomplete PORCcorrect].

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
    + apply (equiv_is_abstraction V ts t__POR t t Hequiv (trace_eq_refl__C t) Habs).
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
