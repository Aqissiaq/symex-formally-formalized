(** * Context Reduction Basics *)

(** Reformulation of de Boer and Bonsangue's basic setup in the context-reduction setting *)

From Coq Require Import String Bool Datatypes Relations Program.Equality.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import Parallel.

From SymEx Require Import ContextReduction.

Definition merge_sub (b: Bexpr) (s1 s2: sub): sub :=
  fun x => AIte b (s1 x) (s2 x).

Lemma merge_sub_true: forall V b s s',
    Beval V b = true -> Comp V (merge_sub b s s') = Comp V s.
Proof.
  intros.
  unfold Comp, merge_sub.
  cbn; rewrite H.
  reflexivity.
Qed.

Lemma merge_sub_false: forall V b s s',
    Beval V b = false -> Comp V (merge_sub b s s') = Comp V s'.
Proof.
  intros.
  unfold Comp, merge_sub.
  cbn; rewrite H.
  reflexivity.
Qed.

Definition separates (p1 p2 b: Bexpr): Prop := forall V,
    (Beval V p1 = true -> Beval V b = true)
    /\ (Beval V p2 = true -> Beval V b = false).

Inductive head_red__S: relation (sub * Bexpr * Stmt) :=
| SAsgn_step: forall x e sig phi,
    head_red__S (sig, phi, <{x := e}>) ((x !-> Aapply sig e; sig), phi, SSkip)
| SIfTrue_step: forall b s1 s2 sig phi,
    head_red__S (sig, phi, <{if b {s1} {s2}}>) (sig, BAnd phi (Bapply sig b), s1)
| SIfFalse_step: forall b s1 s2 sig phi,
    head_red__S (sig, phi, <{if b {s1} {s2}}>) (sig, BAnd phi (BNot (Bapply sig b)), s2)
| SWhileTrue_step: forall b s sig phi,
    head_red__S (sig, phi, <{while b {s}}>) (sig, BAnd phi (Bapply sig b), <{s ; while b {s}}>)
| SWhileFalse_step: forall b s sig phi,
    head_red__S (sig, phi, <{while b {s}}>) (sig, BAnd phi (BNot (Bapply sig b)), SSkip)
| SSeq_skip: forall s sig phi,
    head_red__S (sig, phi, <{skip ; s}>) (sig, phi, s)
| SPar_left_skip: forall s sig phi,
    head_red__S (sig, phi, <{skip || s}>) (sig, phi, s)
| SPar_right_skip: forall s sig phi,
    head_red__S (sig, phi, <{s || skip}>) (sig, phi, s)
(* we have to explicitly give b (which separates phi and phi'), the pcs and the states*)
| SMerge_step: forall s sig sig' phi phi' b,
    separates phi phi' b ->
    head_red__S (sig, phi, s) (merge_sub b sig sig', <{phi | phi'}>, s).

Definition Sstep: relation (sub * Bexpr * Stmt) := context_red is_context head_red__S.
Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.

Notation " c '->s' c'" := (Sstep c c') (at level 40).
Notation " c '->*' c'" := (multi_Sstep c c') (at level 40).

Lemma x_not_y: X <> Y. Admitted.

Example merge_sub_ex: merge_sub (BLeq Y 1) (Y !-> 2 ; X !-> 1 ; id_sub) (X !-> 4 ; id_sub)
                      = (X !-> AIte (BLeq Y 1) 1 4 ; Y !-> AIte (BLeq Y 1) 2 Y ; merge_sub (BLeq Y 1) id_sub id_sub).
Proof.
  extensionality x. unfold merge_sub, update.
  destruct (String.eqb_spec X x), (String.eqb_spec Y x).
    - rewrite <- e0 in e. apply x_not_y in e. contradiction.
    - reflexivity.
    - rewrite e. reflexivity.
    - reflexivity.
Qed.

Example if_merge_example:
  (id_sub, BTrue, <{if (Y <= 1) {X := 1 ; Y := 2} {X := 4} ; Z := 3}>) ->*
    ((X !-> AIte (BLeq Y 1) 1 4 ; Y !-> AIte (BLeq Y 1) 2 Y ; merge_sub (BLeq Y 1) id_sub id_sub),
      <{Y <= 1 | ~ (Y <= 1)}>,
      <{Z := 3}>).
Proof.
  econstructor.
  - apply ctx_red_intro with (C := fun x => x).
    + rewrite <- merge_sub_ex.
      apply SMerge_step.
      split; intro.
      * assumption.
      * apply negb_true_iff in H. apply H.
    + constructor.
      (* and we don't care about teh rest rn *)
Admitted.

Inductive head_red__C: relation (Valuation * Stmt) :=
| CAsgn_step: forall x e V,
    head_red__C (V, <{x := e}>) ((x !-> Aeval V e ; V), SSkip)
| CIfTrue_step: forall b s1 s2 V,
    Beval V b = true ->
    head_red__C (V, <{if b {s1} {s2}}>) (V, s1)
| CIfFalse_step: forall b s1 s2 V,
    Beval V b = false ->
    head_red__C (V, <{if b {s1} {s2}}>) (V, s2)
| CWhileTrue_step: forall b s V,
    Beval V b = true ->
    head_red__C (V, <{while b {s}}>) (V, <{s ; while b {s}}>)
| CWhileFalse_step: forall b s V,
    Beval V b = false ->
    head_red__C (V, <{while b {s}}>) (V, SSkip)
| CSeq_skip: forall s V,
    head_red__C (V, <{skip ; s}>) (V, s)
| CPar_left_skip: forall s V,
    head_red__C (V, <{skip || s}>) (V, s)
| CPar_right_skip: forall s V,
    head_red__C (V, <{s || skip}>) (V, s)
.

Definition Cstep: relation (Valuation * Stmt) := context_red is_context head_red__C.
Definition multi_Cstep := clos_refl_trans_n1 _ Cstep.

Notation " c '=>c' c'" := (Cstep c c') (at level 40).
Notation " c '=>*' c'" := (multi_Cstep c c') (at level 40).

Definition pc_equiv (b1 b2: Bexpr): Prop := forall V, Beval V b1 = Beval V b2.

Theorem correctness : forall s s' sig phi V,
    (id_sub, BTrue, s) ->* (sig, phi, s') ->
    exists V' phi',
      V' = (Comp V sig)
      /\ pc_equiv phi phi'
      /\ (Beval V phi' = true ->
         (V, s) =>* (V', s')).
Proof.
  intros. dependent induction H.
  - exists V, BTrue. splits. constructor.
  - dependent destruction H. destruct x as [sig0 phi0]. dependent destruction H.

    + destruct (IHclos_refl_trans_n1 _ _ _ _ JMeq_refl eq_refl) as (V' & phi' & ? & ? & ?).
      eexists. eexists. splits.
      * econstructor.
      -- constructor.
        ++ rewrite asgn_sound. constructor.
        ++  assumption.
      -- rewrite <- H. apply H3. rewrite <- H2. apply H4.

    + destruct (IHclos_refl_trans_n1 _ _ _ _ JMeq_refl eq_refl) as (V' & phi' & ? & ? & ?).
      eexists. eexists. splits.
      * intro Hpc. simpl in Hpc; apply andb_true_iff in Hpc; destruct Hpc as [Hpc1 Hpc2];
          rewrite <- comp_subB in Hpc2.
        econstructor.
       -- constructor.
          ++ apply CIfTrue_step. apply Hpc2.
          ++ assumption.
       -- rewrite <- H. apply H3. rewrite <- H2. apply Hpc1.

    + destruct (IHclos_refl_trans_n1 _ _ _ _ JMeq_refl eq_refl) as (V' & phi' & ? & ? & ?).
      eexists. eexists. splits.
      * intro Hpc. simpl in Hpc; apply andb_true_iff in Hpc; destruct Hpc as [Hpc1 Hpc2];
          rewrite <- comp_subB, negb_true_iff in Hpc2.
        econstructor.
       -- constructor.
          ++ apply CIfFalse_step. apply Hpc2.
          ++ assumption.
       -- rewrite <- H. apply H3. rewrite <- H2. apply Hpc1.

    + destruct (IHclos_refl_trans_n1 _ _ _ _ JMeq_refl eq_refl) as (V' & phi' & ? & ? & ?).
      eexists. eexists. splits.
      * intro Hpc. simpl in Hpc; apply andb_true_iff in Hpc; destruct Hpc as [Hpc1 Hpc2];
          rewrite <- comp_subB in Hpc2.
        econstructor.
       -- constructor.
          ++ apply CWhileTrue_step. apply Hpc2.
          ++ assumption.
       -- rewrite <- H. apply H3. rewrite <- H2. apply Hpc1.

    + destruct (IHclos_refl_trans_n1 _ _ _ _ JMeq_refl eq_refl) as (V' & phi' & ? & ? & ?).
      eexists. eexists. splits.
      * intro Hpc. simpl in Hpc; apply andb_true_iff in Hpc; destruct Hpc as [Hpc1 Hpc2];
          rewrite <- comp_subB, negb_true_iff in Hpc2.
        econstructor.
       -- constructor.
          ++ apply CWhileFalse_step. apply Hpc2.
          ++ assumption.
       -- rewrite <- H. apply H3. rewrite <- H2. apply Hpc1.

    + destruct (IHclos_refl_trans_n1 _ _ _ _ JMeq_refl eq_refl) as (V' & phi' & ? & ? & ?).
      eexists. eexists. splits.
      * econstructor.
        -- constructor.
           ++ apply CSeq_skip.
           ++ assumption.
        -- rewrite <- H. apply H3. rewrite <- H2. apply H4.

    + destruct (IHclos_refl_trans_n1 _ _ _ _ JMeq_refl eq_refl) as (V' & phi' & ? & ? & ?).
      eexists. eexists. splits.
      * econstructor.
        -- constructor.
           ++ apply CPar_left_skip.
           ++ assumption.
        -- rewrite <- H. apply H3. rewrite <- H2. apply H4.

    + destruct (IHclos_refl_trans_n1 _ _ _ _ JMeq_refl eq_refl) as (V' & phi' & ? & ? & ?).
      eexists. eexists. splits.
      * econstructor.
        -- constructor.
           ++ apply CPar_right_skip.
           ++ assumption.
        -- rewrite <- H. apply H3. rewrite <- H2. apply H4.

    + destruct (IHclos_refl_trans_n1 _ _ _ _ JMeq_refl eq_refl) as (V' & phi0' & ? & ? & ?).
      eexists. eexists. splits.
      * intro. simpl in H5. apply orb_true_iff in H5.
        destruct (H V), H5.
        -- specialize (H6 H5).
           rewrite (merge_sub_true _ _ _ _ H6), <- H2.
           apply H4. rewrite <- H3. apply H5.
        -- specialize (H7 H5).
           rewrite (merge_sub_false _ _ _ _ H7).
           (* what more do we need to know about sig'? *)
Qed.

Theorem completeness : forall s s' V0 V,
    (V0, s) =>* (V, s') ->
    exists sig phi, (id_sub, BTrue, s) ->* (sig, phi, s') /\ Beval V0 phi = true /\ V = Comp V0 sig.
Proof.
  intros. dependent induction H.
  - exists id_sub. exists BTrue. splits. constructor.
  - dependent destruction H. dependent destruction H.
    + destruct (IHclos_refl_trans_n1 s (C <{x0 := e}>) V0 x) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      eexists. eexists. splits.
      * econstructor.
        ** constructor; [apply SAsgn_step
                        | assumption].
        ** apply IHcomp.
      * assumption.
      * rewrite asgn_sound. rewrite IHupd. reflexivity.
    + destruct (IHclos_refl_trans_n1 s (C <{if b {s'0}{s2}}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      eexists. eexists. splits.
      * econstructor.
        ** constructor; [apply SIfTrue_step
                        | assumption].
        ** apply IHcomp.
      * simpl. apply andb_true_iff. split.
        ** assumption.
        ** rewrite <- comp_subB. rewrite <- IHupd. assumption.
      * assumption.
    + destruct (IHclos_refl_trans_n1 s (C <{if b {s1}{s'0}}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      eexists. eexists. splits.
      * econstructor.
        ** constructor; [apply SIfFalse_step
                        | assumption].
        ** apply IHcomp.
      * simpl. apply andb_true_iff. split.
        ** assumption.
        ** rewrite <- comp_subB. rewrite <- IHupd. apply negb_true_iff. assumption.
      * assumption.
    + destruct (IHclos_refl_trans_n1 s (C <{while b {s1}}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      eexists. eexists. splits.
      * econstructor.
        ** constructor; [apply SWhileTrue_step
                        | assumption].
        ** apply IHcomp.
      * simpl. apply andb_true_iff. split.
        ** assumption.
        ** rewrite <- comp_subB. rewrite <- IHupd. assumption.
      * assumption.
    + destruct (IHclos_refl_trans_n1 s (C <{while b {s1}}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      eexists. eexists. splits.
      * econstructor.
        ** constructor; [apply SWhileFalse_step
                        | assumption].
        ** apply IHcomp.
      * simpl. apply andb_true_iff. split.
        ** assumption.
        ** rewrite <- comp_subB. rewrite <- IHupd. apply negb_true_iff. assumption.
      * assumption.
    + destruct (IHclos_refl_trans_n1 s (C <{skip ; s'0}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      exists sig. exists phi. splits; try assumption.
      econstructor.
      * constructor; [apply SSeq_skip | assumption].
      *  apply IHcomp.
    + destruct (IHclos_refl_trans_n1 s (C <{skip || s'0}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      exists sig. exists phi. splits; try assumption.
      econstructor.
      * constructor; [apply SPar_left_skip | assumption].
      *  apply IHcomp.
    + destruct (IHclos_refl_trans_n1 s (C <{s'0 || skip}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      exists sig. exists phi. splits; try assumption.
      econstructor.
      * constructor; [apply SPar_right_skip | assumption].
      *  apply IHcomp.
Qed.
