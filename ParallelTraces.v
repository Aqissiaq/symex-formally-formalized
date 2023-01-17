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

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import Parallel.

From SymEx Require Import Traces.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.

(** Symbolic semantics *)
Definition Var : Type := string.

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
| SAsgn_step : forall x e s t,
    (<{x := e ; s}>, t) ->s (s, t :: STAsgn x e)
| SParLeft_step : forall s s' s'' t t',
  (s, t) ->s (s', t') ->
  (<{s || s''}>, t) ->s (<{s' || s''}>, t')
| SParRight_step : forall s s' s'' t t',
  (s, t) ->s (s', t') ->
  (<{s'' || s}>, t) ->s (<{s'' || s'}>, t')
| SIfTrue_step : forall b s1 s2 s t,
    (<{if b {s1}{s2} ; s}>, t) ->s (<{s1 ; s}>, t :: STCond b)
| SIfFalse_step : forall b s1 s2 s t,
    (<{if b {s1}{s2} ; s}>, t) ->s (<{s2 ; s}>, t :: STCond (BNot b))
| SSkipLeft : forall s t,
    (<{skip || s}>, t) ->s (s, t)
| SSkipRight : forall s t,
    (<{s || skip}>, t) ->s (s, t)
where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40) : trace_scope.

(** Properties *)
Lemma Sstep_progress : forall s s' t t',
    (s, t) ->s (s', t') ->
    s <> s' \/ t <> t'.
Proof.
  intros. dependent induction H; subst;
    try (left; apply SSeq_disjoint);
    try (right; apply cons_neq').
  destruct (IHSstep s0 s'0 t t'); try reflexivity.
  (* get back to this*)
Admitted.

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
| CAsgn_step : forall x e t s,
    Cstep V0 (<{x := e ; s}>, t) (s, t :: (x, Aeval_t V0 t e))
| CParLeft_step : forall s s' s'' t t',
    Cstep V0 (s, t) (s'', t') ->
    Cstep V0 (<{s || s'}>, t) (<{s'' || s'}>, t')
| CParRight_step : forall s s' s'' t t',
    Cstep V0 (s, t) (s'', t') ->
    Cstep V0 (<{s' || s}>, t) (<{s' || s''}>, t')
| CIfTrue_step : forall b s1 s2 s t,
    Beval_t V0 t b = true ->
    Cstep V0 (<{if b {s1}{s2} ; s}>, t) (<{s1 ; s}>, t)
| CIfFalse_step : forall b s1 s2 s t,
    Beval_t V0 t b = false ->
    Cstep V0 (<{if b {s1}{s2} ; s}>, t) (<{s2 ; s}>, t)
| CSkipLeft_step : forall s t,
    Cstep V0 (<{skip || s}>, t) (s, t)
| CSkipRight_step : forall s t,
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
  - simpl in H0. apply andb_true_iff in H0. destruct H0. assumption.
  - simpl in H0. apply andb_true_iff in H0. destruct H0. assumption.
Qed.

Ltac splits := repeat (try split).

Lemma par_step_correct : forall s s' t t' t0 V0,
    (s, t) ->s (s', t') ->
    Beval V0 (pc t') = true ->
    acc_val V0 t0 = Comp V0 (acc_subst id_sub t) ->
    forall s0, exists tc,
      Cstep V0 (<{s || s0}>, t0) (<{s' || s0}>, tc)
      /\ Cstep V0 (<{s0 || s}>, t0) (<{s0 || s'}>, tc)
      /\ acc_val V0 tc = Comp V0 (acc_subst_id t').
Proof.
  intros. dependent induction H.
  - exists (t0 :: (x, Aeval_t V0 t0 e)). splits.
    + apply CParLeft_step. apply CAsgn_step.
    + apply CParRight_step. apply CAsgn_step.
    + unfold acc_subst_id, Aeval_t. simpl. rewrite asgn_sound. rewrite H1. reflexivity.
  - edestruct (IHSstep s0 s'0 t t') as [tc [comp [_ trace]]];
      try reflexivity; try assumption.
    exists tc. splits.
    + apply CParLeft_step. apply comp.
    + apply CParRight_step. apply comp.
    + assumption.
  - edestruct (IHSstep s0 s'0 t t') as [tc [_ [comp trace]]];
      try reflexivity; try assumption.
    exists tc. splits.
    + apply CParLeft_step. apply comp.
    + apply CParRight_step. apply comp.
    + assumption.
  - exists t0.
    (* rewrite path condition just once *)
    simpl in H0. apply andb_true_iff in H0. destruct H0.
    unfold Bapply_t in H. rewrite <- comp_subB in H.
    unfold acc_subst_id in H. rewrite <- H1 in H. unfold Beval_t.
    splits;
      [ apply CParLeft_step; apply CIfTrue_step
      | apply CParRight_step; apply CIfTrue_step
      | unfold acc_subst_id; simpl];
      assumption.
  - exists t0.
    simpl in H0. apply andb_true_iff in H0. destruct H0.
    apply negb_true_iff in H.
    unfold Bapply_t in H. rewrite <- comp_subB in H.
    unfold acc_subst_id in H. rewrite <- H1 in H. unfold Beval_t.
    splits;
      [ apply CParLeft_step; apply CIfFalse_step
      | apply CParRight_step; apply CIfFalse_step
      | unfold acc_subst_id; simpl];
      assumption.
  - exists t0. splits.
    + apply CParLeft_step. apply CSkipLeft_step.
    + apply CParRight_step. apply CSkipLeft_step.
    + assumption.
  - exists t0. splits.
    + apply CParLeft_step. apply CSkipRight_step.
    + apply CParRight_step. apply CSkipRight_step.
    + assumption.
Qed.

(** Correctness *)
Theorem correctness : forall s s' t0 t t0' V0,
    (s, t0) ->* (s', t) ->
    Beval V0 (pc t) = true ->
    acc_val V0 t0' = Comp V0 (acc_subst_id t0) ->
    exists t', multi_Cstep V0 (s, t0') (s', t') /\ acc_val V0 t' = Comp V0 (acc_subst_id t).
Proof.
  intros. dependent induction H.
  - exists t0'. split.
    + constructor.
    + assumption.
  - dependent destruction H.
    + (* x := e*)
      destruct (IHclos_refl_trans_n1 s <{x := e ; s'}> t0 t1) as [t' [comp IHV]];
        try reflexivity; try assumption.
      exists (t' :: (x, Aeval_t V0 t' e)). split.
      * eapply Relation_Operators.rtn1_trans. apply CAsgn_step. assumption.
      * unfold acc_subst_id, Aeval_t in *. simpl.
        rewrite asgn_sound. rewrite <- IHV. reflexivity.
    + (* s0 || s' *)
      destruct (IHclos_refl_trans_n1 s <{ s0 || s''}> t0 t1) as [t' [comp IHV]];
        try (apply (pc_monotone _ _ _ _ _ H));
        try assumption; try reflexivity.
      edestruct (par_step_correct _ _ _ _ t' V0 H H1 IHV) as [tc [stepL [_ IHV']]].
      exists tc. split.
      * eapply Relation_Operators.rtn1_trans. apply stepL. apply comp.
      * apply IHV'.
    + (* s' || s0 *)
      destruct (IHclos_refl_trans_n1 s <{ s'' || s0}> t0 t1) as [t' [comp IHV]];
        try (apply (pc_monotone _ _ _ _ _ H));
        try assumption; try reflexivity.
      edestruct (par_step_correct _ _ _ _ t' V0 H H1 IHV) as [tc [_ [stepR IHV']]].
      exists tc. split.
      * eapply Relation_Operators.rtn1_trans. apply stepR. apply comp.
      * apply IHV'.
    + (* if true*)
      simpl in H1. apply andb_true_iff in H1. destruct H1.
      destruct (IHclos_refl_trans_n1 s <{if b {s1}{s2} ; s0}> t0 t1) as [t' [comp IHV]];
        try reflexivity; try assumption.
      exists t'. splits.
      * eapply Relation_Operators.rtn1_trans. apply CIfTrue_step;
          unfold Bapply_t in H; rewrite <- comp_subB in H;
          rewrite <- IHV in H; unfold Beval_t; apply H.
        apply comp.
      * unfold acc_subst_id. simpl. assumption.
    + (* if false*)
      simpl in H1. apply andb_true_iff in H1. destruct H1.
      apply negb_true_iff in H.
      destruct (IHclos_refl_trans_n1 s <{if b {s1}{s2} ; s0}> t0 t1) as [t' [comp IHV]];
        try reflexivity; try assumption.
      exists t'. splits.
      * eapply Relation_Operators.rtn1_trans. apply CIfFalse_step;
          unfold Bapply_t in H; rewrite <- comp_subB in H;
          rewrite <- IHV in H; unfold Beval_t; apply H.
        apply comp.
      * unfold acc_subst_id. simpl. assumption.
    (* skips *)
    + destruct (IHclos_refl_trans_n1 s <{ skip || s' }> t0 t) as [t' [comp IHV]];
        try reflexivity; try assumption.
      exists t'. splits.
      * eapply Relation_Operators.rtn1_trans. apply CSkipLeft_step. apply comp.
      * assumption.
    + destruct (IHclos_refl_trans_n1 s <{ s' || skip }> t0 t) as [t' [comp IHV]];
        try reflexivity; try assumption.
      exists t'. splits.
      * eapply Relation_Operators.rtn1_trans. apply CSkipRight_step. apply comp.
      * assumption.
Qed.

(** skipping "simple" completeness for now
 to instead do trace equivalence *)

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

Definition is_abstract_trace {V0:Valuation} {s s': Stmt} {t':CTrace} (c : multi_Cstep V0 (s, []) (s', t')) (t: STrace) :=
  (s, []) ->* (s', t) /\ Beval V0 (pc t) = true /\ Comp V0 (acc_subst_id t) = acc_val V0 t'.

Lemma foo : forall V V' s s' x, Comp V s x = Comp V s' x -> Comp V' s x = Comp V' s' x.
Proof. intros. unfold Comp in *.
       destruct (s x); induction (s' x); simpl in *; try assumption.
       - admit.
         - inversion H; subst.

(* empty starting trace for convenience *)
Theorem completeness_reduced : forall s s' tc t t' V0
    (* there is a concrete computation *)
    (C : multi_Cstep V0 (s, []) (s', tc)),
    is_abstract_trace C t ->
    is_abstract_trace C t' ->
    t ~ t'.
Proof.
  intros.
  destruct H as [HComp [HPC HSub]]. destruct H0 as [HComp' [HPC' HSub']].
  remember (s, []) as p. destruct p. apply pair_equal_spec in Heqp. destruct Heqp.
  remember (s', tc) as p. destruct p. apply pair_equal_spec in Heqp. destruct Heqp.
  induction C; subst.
  - splits.
    intro.
