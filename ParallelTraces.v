(** * Trace Semantics for a Simple Parallel Language *)

(** Building on the skeleton from TraceSemantics.v,
we include a parallel statement to allow for more interesting abstraction/reduction
 *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Program.Equality.   (* for `dependent induction` *)
(* which apparently (CTrees) smuggles in UIP(-equivalent) *)
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)
From Coq Require Import Relations.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Sets.Ensembles.

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import Parallel.

From SymEx Require Import Traces.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.

Ltac splits := repeat (try split).

(** Symbolic semantics *)
Inductive STrace_step : Type :=
| STAsgn (x:Var) (e:Aexpr)
| STCond (b:Bexpr).

Definition STrace := trace STrace_step.

Fixpoint acc_subst (s0:sub) (t:STrace) : sub :=
  match t with
  | [] => s0
  | t :: STAsgn x e => let s := acc_subst s0 t in
                     (x !-> Aapply s e ; s)
  | t :: _ => acc_subst s0 t
  end.

Definition acc_subst_id := acc_subst id_sub.

Definition Aapply_t (t:STrace) (e:Aexpr) : Aexpr :=
  Aapply (acc_subst_id t) e.

Definition Bapply_t (t:STrace) (e:Bexpr) : Bexpr :=
  Bapply (acc_subst_id t) e.

Fixpoint pc (t:STrace) : Bexpr :=
  match t with
  | [] => BTrue
  | t :: STCond b => BAnd (Bapply_t t b) (pc t)
  | t :: _ => pc t
  end.

Definition SConfig : Type := Stmt * STrace.

Reserved Notation " c '->s' c' " (at level 40).
Inductive Sstep : relation SConfig  :=
| SAsgn_step : forall x e t,
    (<{x := e}>, t) ->s (<{skip}>, t :: STAsgn x e)
| SSeq_step : forall s1 s2 s t1 t2,
    (s1, t1) ->s (s2, t2) ->
    (<{s1 ; s}>, t1) ->s (<{s2 ; s}>, t2)
| SSeq_done : forall s t,
    (<{skip ; s}>, t) ->s (s, t)
| SParLeft_step : forall s s' s'' t t',
  (s, t) ->s (s', t') ->
  (<{s || s''}>, t) ->s (<{s' || s''}>, t')
| SParRight_step : forall s s' s'' t t',
  (s, t) ->s (s', t') ->
  (<{s'' || s}>, t) ->s (<{s'' || s'}>, t')
| SParLeft_done : forall s t,
    (<{ skip || s }>, t) ->s (s, t)
| SParRight_done : forall s t,
    (<{ s || skip }>, t) ->s (s, t)
| SIfTrue_step : forall b s1 s2 t,
    (<{if b {s1}{s2}}>, t) ->s (s1, t :: STCond b)
| SIfFalse_step : forall b s1 s2 t,
    (<{if b {s1}{s2}}>, t) ->s (s2, t :: STCond (BNot b))
where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40) : trace_scope.

(** Properties *)

Lemma progress__S : forall s t, s = SSkip \/ exists s' t', (s, t) ->s (s', t').
Proof.
  induction s; intros.
  - right. exists SSkip. eexists. constructor.
  - right. edestruct IHs1.
    + exists s2. eexists. rewrite H. constructor.
    + destruct H as [s' [t' IH]].
      exists <{s'; s2}>. exists t'. apply SSeq_step. apply IH.
  - right. edestruct IHs1.
    + exists s2. eexists. rewrite H. constructor.
    + destruct H as [s' [t' IH]].
      exists <{s'|| s2}>. exists t'. apply SParLeft_step. apply IH.
  - right. exists s1. eexists. apply SIfTrue_step.
  - left. reflexivity.
Qed.

(* not deterministic, maybe prove later*)

(* characterizing stuff in terms of sets of traces *)
Definition Concatenate (A B: Ensemble STrace) : Ensemble STrace :=
  fun t => exists t1 t2, t = t1 ++ t2 /\ A t1 /\ B t2.

Lemma Concatenate_empty_left : forall S, Concatenate (Singleton _ []) S = S.
Proof.
  intros. apply Extensionality_Ensembles. split; intros t H.
  - destruct H as [t1 [t2 [Happ [Hempty HS]]]].
    inversion Hempty; subst. rewrite app_nil_l. assumption.
  - exists []. exists t. splits.
    + rewrite app_nil_l. reflexivity.
    + assumption.
Qed.

Inductive is_interleaving : STrace -> STrace -> STrace -> Prop :=
| both_empty : is_interleaving [] [] []
| left_empty : forall t, is_interleaving [] t t
| right_empty : forall t, is_interleaving t [] t
| left_step : forall t1 t2 t x,
    is_interleaving t1 t2 t ->
    is_interleaving (t1::x) t2 (t::x)
| right_step : forall t1 t2 t x,
    is_interleaving t1 t2 t ->
    is_interleaving t1 (t2::x) (t::x)
.

Definition Interleave (A B: Ensemble STrace) : Ensemble STrace :=
  fun t => exists t1 t2, is_interleaving t1 t2 t /\ A t1 /\ B t2.

Definition traces__S (s:Stmt) : Ensemble STrace := fun t => (s, []) ->* (<{skip}>, t).

Lemma skip_stuck : forall t, ~ (exists s t', (SSkip, t) ->s (s, t')).
Proof. intros t H. destruct H as [s [t' comp]]. inversion comp. Qed.

Theorem skip_traces_spec : Same_set _ (traces__S <{ skip }>) (Singleton _ []).
Proof. split.
       - intros t H. unfold In, traces__S in H.
         (* transform to look at FIRST step of computation *)
         apply clos_rtn1_rt in H. apply clos_rt_rt1n in H.
         inversion H. apply In_singleton.
         destruct y. destruct (skip_stuck []).
         exists s. exists s0. assumption.
       - intros t H. inversion H; subst. apply rtn1_refl.
Qed.

Theorem asgn_traces_spec : forall x e, Same_set _ (traces__S <{ x := e }>) (Singleton _ [STAsgn x e]).
Proof.
  split; intros t H.
  - unfold In, traces__S in H.
    apply clos_rtn1_rt in H. apply clos_rt_rt1n in H.
    inversion H. inversion H0; subst.
    assert (t_spec: t = [STAsgn x e])
      by (dependent induction H1; [reflexivity| inversion H0]).
    rewrite t_spec. apply In_singleton.
  - inversion H. econstructor. apply SAsgn_step. constructor.
Qed.

Lemma step_traces_spec : forall s1 s2 t1 t2,
    (s1, []) ->s (SSkip, t1) ->
    (s2, t1) ->s (SSkip, t2) ->
    (<{s1 ; s2}>, []) ->* (SSkip, t2).
Proof.
  intros.
  apply clos_rt_rtn1. apply clos_rt1n_rt.
  econstructor. apply SSeq_step. apply H.
  econstructor. apply SSeq_done.
  econstructor.  apply H0. constructor.
Qed.

Lemma seq_first : forall s1 s2 s t t',
    (s1, t) ->* (s2, t') ->
    (<{s1; s}>, t) ->* (<{s2;s}>, t').
Proof.
  intros. dependent induction H.
  - constructor.
  - destruct y. eapply Relation_Operators.rtn1_trans. apply SSeq_step. apply H.
    apply IHclos_refl_trans_n1; reflexivity.
Qed.

Lemma seq_second : forall s1 s2 t t',
    (s1, []) ->* (SSkip, t) ->
    (s2, t) ->* (SSkip, t') ->
    (<{s1; s2}>, []) ->* (SSkip, t').
Proof.
  intros. apply seq_first with (s := s2) in H.
  (* juggling transitivity properties *)
  apply clos_rt_rtn1. apply rt_trans with (y := (<{skip ; s2}>, t)).
  apply clos_rtn1_rt. apply H.
  apply clos_rt1n_rt. econstructor. apply SSeq_done.
  apply clos_rt_rt1n. apply clos_rtn1_rt. apply H0.
Qed.

(** pipe dreams *)
(* Theorem seq_traces_spec : forall s1 s2, Same_set _ (traces__S <{s1 ; s2}>) (Concatenate (traces__S s1) (traces__S s2)). *)
(* Theorem par_traces_spec : forall s1 s2, Same_set _ (traces__S <{s1 || s2}>) (Interleave (traces__S s1) (traces__S s2)). *)


(** Concrete Semantics *)

Definition Val : Type := nat.
Definition CTrace := trace (Var * Val).

Fixpoint acc_val (V0:Valuation) (t:CTrace) : Valuation :=
  match t with
  | [] => V0
  | t :: (x, v) => let V := acc_val V0 t in
                 (x !-> v ; V)
  end.

Definition Aeval_t (V0:Valuation) (t:CTrace) (e:Aexpr) : nat :=
  Aeval (acc_val V0 t) e.

Definition Beval_t (V0:Valuation) (t:CTrace) (e:Bexpr) : bool :=
  Beval (acc_val V0 t) e.

Definition CConfig : Type := Stmt * CTrace.

Inductive Cstep (V0:Valuation) : relation CConfig :=
| CAsgn_step : forall x e t,
    Cstep V0 (<{x := e}>, t) (SSkip, t :: (x, Aeval_t V0 t e))
| CSeq_step : forall s1 s2 s t1 t2,
    Cstep V0 (s1, t1) (s2, t2) ->
    Cstep V0 (<{s1;s}>, t1) (<{s2;s}>, t2)
| CSeq_done : forall s t,
    Cstep V0 (<{skip;s}>, t) (s, t)
| CParLeft_step : forall s s' s'' t t',
    Cstep V0 (s, t) (s'', t') ->
    Cstep V0 (<{s || s'}>, t) (<{s'' || s'}>, t')
| CParRight_step : forall s s' s'' t t',
    Cstep V0 (s, t) (s'', t') ->
    Cstep V0 (<{s' || s}>, t) (<{s' || s''}>, t')
| CIfTrue_step : forall b s1 s2 t,
    Beval_t V0 t b = true ->
    Cstep V0 (<{if b {s1}{s2}}>, t) (s1, t)
| CIfFalse_step : forall b s1 s2 t,
    Beval_t V0 t b = false ->
    Cstep V0 (<{if b {s1}{s2}}>, t) (s2, t)
| CParLeft_done : forall s t,
    Cstep V0 (<{skip || s}>, t) (s, t)
| CParRight_done : forall s t,
    Cstep V0 (<{s || skip}>, t) (s, t).

Definition multi_Cstep (V0:Valuation) := clos_refl_trans_n1 _ (Cstep V0).
Notation " c '=>*' V c'" := (multi_Cstep V c c') (at level 40).

Lemma pc_monotone : forall V s s' t t',
    (s, t) ->s (s', t') ->
    Beval V (pc t') = true ->
    Beval V (pc t) = true.
Proof.
  intros. dependent induction H;
    try (simpl in H0; assumption).
  - eapply IHSstep. reflexivity. reflexivity. assumption.
  - eapply IHSstep. reflexivity. reflexivity. assumption.
  - eapply IHSstep. reflexivity. reflexivity. assumption.
  - simpl in H0. apply andb_true_iff in H0. destruct H0. assumption.
  - simpl in H0. apply andb_true_iff in H0. destruct H0. assumption.
Qed.

(* Lemma par_step_correct : forall s s' t t' t0 V0, *)
(*     (s, t) ->s (s', t') -> *)
(*     Beval V0 (pc t') = true -> *)
(*     acc_val V0 t0 = Comp V0 (acc_subst id_sub t) -> *)
(*     forall s0, exists tc, *)
(*       Cstep V0 (<{s || s0}>, t0) (<{s' || s0}>, tc) *)
(*       /\ Cstep V0 (<{s0 || s}>, t0) (<{s0 || s'}>, tc) *)
(*       /\ acc_val V0 tc = Comp V0 (acc_subst_id t'). *)
(* Proof. *)
(*   intros. dependent induction H. *)
(*   - exists (t0 :: (x, Aeval_t V0 t0 e)). splits. *)
(*     + apply CParLeft_step. apply CAsgn_step. *)
(*     + apply CParRight_step. apply CAsgn_step. *)
(*     + unfold acc_subst_id, Aeval_t. simpl. rewrite asgn_sound. rewrite H1. reflexivity. *)
(*   - edestruct (IHSstep s1 s2 t t') as [tc [comp [_ trace]]]; *)
(*       try reflexivity; try assumption. *)
(*     exists tc. splits. *)
(*     + apply CParLeft_step. apply comp. *)
(*     + apply CParRight_step. apply comp. *)
(*     + assumption. *)
(*   - edestruct (IHSstep s0 s'0 t t') as [tc [_ [comp trace]]]; *)
(*       try reflexivity; try assumption. *)
(*     exists tc. splits. *)
(*     + apply CParLeft_step. apply comp. *)
(*     + apply CParRight_step. apply comp. *)
(*     + assumption. *)
(*   - exists t0. *)
(*     (* rewrite path condition just once *) *)
(*     simpl in H0. apply andb_true_iff in H0. destruct H0. *)
(*     unfold Bapply_t in H. rewrite <- comp_subB in H. *)
(*     unfold acc_subst_id in H. rewrite <- H1 in H. unfold Beval_t. *)
(*     splits; *)
(*       [ apply CParLeft_step; apply CIfTrue_step *)
(*       | apply CParRight_step; apply CIfTrue_step *)
(*       | unfold acc_subst_id; simpl]; *)
(*       assumption. *)
(*   - exists t0. *)
(*     simpl in H0. apply andb_true_iff in H0. destruct H0. *)
(*     apply negb_true_iff in H. *)
(*     unfold Bapply_t in H. rewrite <- comp_subB in H. *)
(*     unfold acc_subst_id in H. rewrite <- H1 in H. unfold Beval_t. *)
(*     splits; *)
(*       [ apply CParLeft_step; apply CIfFalse_step *)
(*       | apply CParRight_step; apply CIfFalse_step *)
(*       | unfold acc_subst_id; simpl]; *)
(*       assumption. *)
(*   - exists t0. splits. *)
(*     + apply CParLeft_step. apply CSkipLeft_step. *)
(*     + apply CParRight_step. apply CSkipLeft_step. *)
(*     + assumption. *)
(*   - exists t0. splits. *)
(*     + apply CParLeft_step. apply CSkipRight_step. *)
(*     + apply CParRight_step. apply CSkipRight_step. *)
(*     + assumption. *)
(* Qed. *)

Lemma pc_monotone_step : forall V0 s1 s2 t1 t2, (s1, t1) ->s (s2, t2) -> Beval V0 (pc t2) = true -> Beval V0 (pc t1) = true.
Proof.
  intros. dependent induction H; simpl in H0;
    try (apply andb_true_iff in H0; destruct H0);
    try assumption.
  - eapply IHSstep. reflexivity. reflexivity. assumption.
  - eapply IHSstep. reflexivity. reflexivity. assumption.
  - eapply IHSstep. reflexivity. reflexivity. assumption.
Qed.

(** Correctness *)
Theorem correctness_step : forall s s' t0 t t0' V0,
    (s, t0) ->s (s', t) ->
    Beval V0 (pc t) = true ->
    acc_val V0 t0' = Comp V0 (acc_subst_id t0) ->
    exists t', Cstep V0 (s, t0') (s', t') /\ acc_val V0 t' = Comp V0 (acc_subst_id t).
Proof.
  intros. dependent induction H;
    try (eexists; splits; [constructor | assumption]).
  - eexists. splits.
    + apply CAsgn_step.
    + unfold acc_subst_id, Aeval_t. simpl. rewrite asgn_sound.
      rewrite H1. reflexivity.
  - edestruct IHSstep as [t' [IHcomp IHabs]]; try reflexivity; try assumption.
    eexists. splits.
    + apply CSeq_step. apply IHcomp.
    + assumption.
  - edestruct IHSstep as [t' [IHcomp IHabs]]; try reflexivity; try assumption.
    eexists. splits.
    + apply CParLeft_step. apply IHcomp.
    + assumption.
  - edestruct IHSstep as [t' [IHcomp IHabs]]; try reflexivity; try assumption.
    eexists. splits.
    + apply CParRight_step. apply IHcomp.
    + assumption.
  - simpl in H0. apply andb_true_iff in H0. destruct H0. unfold Bapply_t in H.
    rewrite <- comp_subB in H. unfold Beval_t. rewrite H1. assumption.
  - simpl in H0. apply andb_true_iff in H0. destruct H0. apply negb_true_iff in H. unfold Bapply_t in H.
    rewrite <- comp_subB in H. unfold Beval_t. rewrite H1. assumption.
Qed.

Theorem correctness : forall s s' t0 t t0' V0,
    (s, t0) ->* (s', t) ->
    Beval V0 (pc t) = true ->
    acc_val V0 t0' = Comp V0 (acc_subst_id t0) ->
    exists t', multi_Cstep V0 (s, t0') (s', t') /\ acc_val V0 t' = Comp V0 (acc_subst_id t).
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

Definition is_abstraction (V0:Valuation) (t:CTrace) (t':STrace) : Prop :=
  Beval V0 (pc t') = true /\ Comp V0 (acc_subst_id t') = acc_val V0 t.

Lemma completeness_step : forall s s' t0 t t0' V0,
    Cstep V0 (s, t0) (s', t) ->
    is_abstraction V0 t0 t0' ->
    exists t', (s, t0') ->s (s', t')
        /\ is_abstraction V0 t t'.
Proof.
  intros. dependent induction H;
    try (eexists; splits; destruct H0; [constructor | assumption | assumption]).
  - eexists. splits; destruct H0.
    + constructor.
    + simpl. assumption.
    + unfold acc_subst_id in *. simpl. unfold Aeval_t.
      rewrite asgn_sound. rewrite e1. reflexivity.
  - edestruct IHCstep as [step_t [step_comp [step_pc step_abs]]];
      try reflexivity; try assumption.
    eexists. splits;
      try (apply SSeq_step; apply step_comp); assumption.
  - edestruct IHCstep as [step_t [step_comp [step_pc step_abs]]];
      try reflexivity; try assumption.
    eexists. splits;
      try (apply SParLeft_step; apply step_comp); assumption.
  - edestruct IHCstep as [step_t [step_comp [step_pc step_abs]]];
      try reflexivity; try assumption.
    eexists. splits;
      try (apply SParRight_step; apply step_comp); assumption.
  - eexists. splits; destruct H0.
    + apply SIfTrue_step.
    + simpl. apply andb_true_iff. splits.
      * unfold Bapply_t. rewrite <- comp_subB. rewrite e0. unfold Beval_t in H. assumption.
      * assumption.
    + unfold acc_subst_id. simpl. assumption.
  - eexists. splits; destruct H0.
    + apply SIfFalse_step.
    + simpl. apply andb_true_iff. splits.
      * apply negb_true_iff. unfold Bapply_t. rewrite <- comp_subB. rewrite e0. unfold Beval_t in H. assumption.
      * assumption.
    + unfold acc_subst_id. simpl. assumption.
Qed.

Theorem completeness : forall s s' t0 t t0' V0,
    multi_Cstep V0 (s, t0) (s', t) ->
    is_abstraction V0 t0 t0' ->
    exists t', (s, t0') ->* (s', t')
        /\ is_abstraction V0 t t'.
Proof.
  intros. dependent induction H.
  - eexists. splits; destruct H0; try (apply rtn1_refl); assumption.
  - destruct y. edestruct IHclos_refl_trans_n1 as [t' [IHcomp [IHpc IHabs]]];
      try reflexivity; try assumption.
    destruct (completeness_step _ _ _ _ t' _ H) as [t_step [Hstep [Hpc Habs]]]; try assumption.
    split. assumption. assumption.
    eexists. splits.
    + econstructor. apply Hstep. apply IHcomp.
    + apply Hpc.
    + apply Habs.
Qed.

Definition subst_equiv (s s': sub) := forall V0, Comp V0 s = Comp V0 s'.
Definition pc_equiv (t t': STrace) := forall V0, Beval V0 (pc t) = true <-> Beval V0 (pc t') = true.

Definition STrace_equiv : relation STrace :=
  fun t t' => subst_equiv (acc_subst_id t) (acc_subst_id t') /\ pc_equiv t t'.

Global Instance Reflexive_substeq : Reflexive subst_equiv.
Proof. unfold subst_equiv. intros s x. reflexivity. Qed.

Global Instance Reflexive_traceq : Reflexive STrace_equiv.
Proof. intro. splits; intro; assumption. Qed.

Notation "t ~ t'" := (STrace_equiv t t') (at level 40) : trace_scope.

(** Correctness modulo trace equivalance*)
Theorem correctness_reduced : forall s s' t0 t0' t tc V0,
    (s, t0) ->* (s', t) ->
    Beval V0 (pc t) = true ->
    (* equivalent start trace is concretely reachable *)
    t0 ~ t0' ->
    acc_val V0 tc = Comp V0 (acc_subst_id t0') ->
    exists t', multi_Cstep V0 (s, tc) (s', t')
          /\ acc_val V0 t' = Comp V0 (acc_subst_id t).
Proof.
  intros.
  destruct H1 as [Hsubst _].
  unfold subst_equiv in Hsubst. rewrite <- Hsubst in H2.
  apply correctness with (t0 := t0);
    try assumption.
Qed.

(** Completeness modulo trace equivalence *)
(* now that concrete computations are also nondeterministic, result is maybe useful... *)

Lemma if_wf_s1 : forall b s' s, s <> <{if b {s} {s'}}>.
Proof. dependent induction s; try discriminate.
       intro. inversion H; subst. apply IHs1. assumption.
Qed.

Lemma if_wf_s2 : forall b s s', s' <> <{if b {s} {s'}}>.
Proof. dependent induction s'; try discriminate.
       intro. inversion H; subst. apply IHs'2. assumption.
Qed.

Lemma no_stuttering__S : forall s t t',
    (s, t) ->s (s, t') -> t = t'.
Proof.
  intros. dependent induction H; try auto.
  - eapply IHSstep; reflexivity.
  - eapply IHSstep; reflexivity.
  - eapply IHSstep; reflexivity.
  - apply if_wf_s1 in x. contradiction.
  - apply if_wf_s2 in x. contradiction.
Qed.

Lemma par_skip_left_wf : forall s t t', (<{skip || s}>, t) ->s (s, t') -> t = t'.
Proof.
  intros. dependent induction H; try auto.
  - apply SPar_right_disjoint in x. contradiction.
  - eapply IHSstep; reflexivity.
Qed.

Lemma par_skip_right_wf : forall s t t', (<{s || skip}>, t) ->s (s, t') -> t = t'.
Proof.
  intros. dependent induction H; try auto.
  - eapply IHSstep; reflexivity.
  - apply SPar_left_disjoint in x. contradiction.
Qed.

(* if two traces are both abstractions, then they are equivalent *)

Theorem completeness_reduced_step : forall V0 s s' t0 t0' t t' t'',
    Cstep V0 (s, t0) (s', t) ->
    is_abstraction V0 t0 t0' ->
    (* if t' is an abstraction… *)
    (s, t0') ->s (s', t') -> is_abstraction V0 t t' ->
    (* … and t'' is an abstraction… *)
    (s, t0') ->s (s', t'') -> is_abstraction V0 t t'' ->
    (* then they must be equivalent *)
    t' ~ t''.
Proof.
  intros. dependent induction H.
  - inversion H1; inversion H3; subst. reflexivity.
  - inversion H1; inversion H3; subst; try reflexivity.
    + edestruct IHCstep; try reflexivity; try assumption.
      split; assumption.
    + exfalso. destruct (skip_stuck t''). exists s2. exists t'. assumption.
    + exfalso. destruct (skip_stuck t'). exists s2. exists t''. assumption.
  - inversion H1; inversion H3; subst; try reflexivity.
    + exfalso. destruct (skip_stuck t0'). exists s2. exists t'. assumption.
    + exfalso. destruct (skip_stuck t''). exists s2. exists t'. assumption.
    + exfalso. destruct (skip_stuck t'). exists s2. exists t''. assumption.
  - inversion H1; inversion H3; subst; try reflexivity;
      try (apply no_stuttering__S in H1; apply no_stuttering__S in H3;
           subst; reflexivity).
    + edestruct IHCstep; try reflexivity; try assumption.
      split; assumption.
    + exfalso. destruct (skip_stuck t''). exists s''. exists t'. assumption.
    + edestruct IHCstep; try reflexivity; try assumption. constructor.
      split; assumption.
    + exfalso. destruct (skip_stuck t'). exists s''. exists t''. assumption.
    + edestruct IHCstep; try reflexivity; try assumption. constructor.
      split; assumption.
    + apply no_stuttering__S in H11. subst. reflexivity.
  - inversion H1; inversion H3; subst; try reflexivity;
      try (apply no_stuttering__S in H1; apply no_stuttering__S in H3;
           subst; reflexivity).
    + edestruct IHCstep; try reflexivity; try assumption.
      split; assumption.
    + edestruct IHCstep; try reflexivity; try assumption. constructor.
      split; assumption.
    + exfalso. destruct (skip_stuck t''). exists s''. exists t'. assumption.
    + exfalso. destruct (skip_stuck t'). exists SSkip. exists t''. assumption.
    + edestruct IHCstep; try reflexivity; try assumption. constructor.
      split; assumption.
    + exfalso. destruct (skip_stuck t'). exists s''. exists t''. assumption.
  - inversion H1; inversion H3; subst; try reflexivity.
    + (* a bit technical, but basically unfolding defs to show:
       the false branch cannot be an abstraction in this starting configuration *)
      (* TODO: wrap these up in a useful lemma*)
      destruct H0, H4. simpl in H4. apply andb_true_iff in H4. destruct H4.
      apply negb_true_iff in H4. unfold Beval_t in H. rewrite <- comp_subB in H4.
      rewrite <- H5 in H. rewrite H in H4. discriminate.
    + destruct H0, H2. simpl in H2. apply andb_true_iff in H2. destruct H2.
      apply negb_true_iff in H2. unfold Beval_t in H. rewrite <- comp_subB in H2.
      rewrite <- H5 in H. rewrite H in H2. discriminate.
  - inversion H1; inversion H3; subst; try reflexivity.
    + destruct H0, H2. simpl in H2. apply andb_true_iff in H2. destruct H2.
      unfold Beval_t in H. unfold Bapply_t in H2. rewrite <- comp_subB in H2.
      rewrite <- H5 in H. rewrite H in H2. discriminate.
    + destruct H0, H4. simpl in H4. apply andb_true_iff in H4. destruct H4.
      unfold Beval_t in H. unfold Bapply_t in H4. rewrite <- comp_subB in H4.
      rewrite <- H5 in H. rewrite H in H4. discriminate.
  - inversion H1; inversion H3; subst; try reflexivity;
      try (exfalso; destruct (skip_stuck t0'); eexists; eexists; apply H5);
      try (exfalso; destruct (skip_stuck t''); eexists; eexists; apply H5).
    + exfalso; destruct (skip_stuck t0'); eexists; eexists; apply H11.
    + inversion H14; subst. apply par_skip_left_wf in H11. apply par_skip_left_wf in H5. subst. reflexivity.
    + apply par_skip_left_wf in H5. subst. reflexivity.
    + symmetry in H12. apply SPar_left_disjoint in H12. contradiction.
    + apply SPar_right_disjoint in H11. contradiction.
    + apply par_skip_left_wf in H8. subst. reflexivity.
    + apply SPar_right_disjoint in H12. contradiction.
    + apply SPar_left_disjoint in H12. contradiction.
  - inversion H1; inversion H3; subst; try reflexivity;
      try (exfalso; destruct (skip_stuck t0'); eexists; eexists; apply H5);
      try (exfalso; destruct (skip_stuck t''); eexists; eexists; apply H5);
      try (apply par_skip_right_wf in H5; subst; reflexivity);
      try (apply SPar_right_disjoint in H12; contradiction);
      try (apply SPar_left_disjoint in H12; contradiction).
    + inversion H14; subst. apply par_skip_right_wf in H11. apply par_skip_right_wf in H5. subst. reflexivity.
    + exfalso; destruct (skip_stuck t0'); eexists; eexists; apply H11.
    + apply par_skip_right_wf in H8. subst. reflexivity.
    + apply SPar_left_disjoint in H11. contradiction.
Qed.

Lemma skip_stuck_star : forall s t t', (SSkip, t) ->* (s, t') -> t = t' /\ s = SSkip.
Proof.
  intros. apply clos_rtn1_rt in H. apply clos_rt_rt1n in H.
  dependent destruction H.
  - split; reflexivity.
  - destruct (skip_stuck t), y. exists s0. exists s1. apply H.
Qed.

Theorem completeness_reduced : forall V0 s s' t0 t0' t t' t'',
    multi_Cstep V0 (s, t0) (s', t) ->
    is_abstraction V0 t0 t0' ->
    (* if t' is an abstraction… *)
    (s, t0') ->* (s', t') -> is_abstraction V0 t t' ->
    (* … and t'' is an abstraction… *)
    (s, t0') ->* (s', t'') -> is_abstraction V0 t t'' ->
    (* then they must be equivalent *)
    t' ~ t''.
Proof.
  intros. dependent induction H.
  - inversion H1; inversion H3; subst.
  - destruct y.
    (* problem: the symbolic execution steps might not follow the concrete steps exactly *)
    (* solution: another big mess of excluding cases? *)
    edestruct IHclos_refl_trans_n1; try reflexivity; try assumption.
    edestruct (completeness_reduced_step V0 _ _ _ t0' _ t' t'' H).
