(** * Trace Sets *)

(** Building a different sort of trace semantics by looking at inductively generated (prefix-closed?) sets of traces
and then trying to do some reduction of that set

TL;DR:
> the semantics of a program is a set of traces, S
> we define some equivalence on traces ~ and obtain S/~
>> (and prove it complete)
> now any reduction S' should be between the two S/~ <= S' <= S
>> S' <= S guarantees completeness
>> S/~ <= S guarantees soundness
*)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Program.Equality.   (* for `dependent induction` *)
(* which apparently (CTrees) smuggles in UIP(-equivalent) *)
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)
From Coq Require Import Relations.
From Coq Require Import Sets.Ensembles.
(* From Coq Require Import Classes.RelationClasses. *)

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import Parallel.

From SymEx Require Import Traces.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.

Example X : Var := "x".
Example Y : Var := "y".

Ltac splits := repeat (try split).

(** Symbolic semantics *)
Definition Var : Type := string.

Inductive STrace_step : Type :=
| STAsgn (x:Var) (e:Aexpr)
| STCond (b:Bexpr).

Definition STrace : Type := trace STrace_step.

Definition Concatenate (A B: Ensemble STrace) : Ensemble STrace :=
  fun t => exists t1 t2, t = t1 ++ t2 /\ A t1 /\ B t2.

Example concat_ex : In _  (Concatenate
                                (Singleton _ [STAsgn X 0])
                                (Union _
                                      (Singleton _ [STAsgn Y 0])
                                      (Singleton _ [STAsgn X 1])))
                         [STAsgn X 0; STAsgn Y 0].
Proof.
  exists [STAsgn X 0]. exists [STAsgn Y 0]. splits.
  apply Union_introl. apply In_singleton.
Qed.

Example concat_ex' : In _  (Concatenate
                                (Singleton _ [STAsgn X 0])
                                (Union _
                                      (Singleton _ [STAsgn Y 0])
                                      (Singleton _ [STAsgn X 1])))
                         [STAsgn X 0; STAsgn X 1].
Proof.
  exists [STAsgn X 0]. exists [STAsgn X 1]. splits.
  apply Union_intror. apply In_singleton.
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

Fixpoint has_trace__S (s:Stmt) : Ensemble STrace :=
  match s with
  | <{ x := e }> => Singleton _ [STAsgn x e]
  | <{ s1 ; s2 }> => Concatenate (has_trace__S s1) (has_trace__S s2)
  | <{s1 || s2}> => Interleave (has_trace__S s1) (has_trace__S s2)
  | <{if b {s1}{s2}}> => Union _
                              (Concatenate (Singleton _ [STCond b]) (has_trace__S s1))
                              (Concatenate (Singleton _ [STCond (BNot b)]) (has_trace__S s2))
  | <{ skip }> => Empty_set STrace
  end.

Example branch_ex : In _ (has_trace__S <{if X <= 1 {Y := X} {Y := 1}}>) [STCond <{X <= 1}> ; STAsgn Y X].
Proof. unfold has_trace__S, In. simpl. apply Union_introl. eexists. eexists. splits. reflexivity. Qed.

Example par_x : has_trace__S <{(X := 1 ; Y := 2) || (X := Y ; Y := X)}> [STAsgn X 1 ; STAsgn X Y ; STAsgn Y X ; STAsgn Y 2].
Proof. unfold has_trace__S, In. exists [STAsgn X 1; STAsgn Y 2]. exists [STAsgn X Y; STAsgn Y X]. splits.
       - repeat constructor.
       - eexists. eexists. splits. reflexivity.
       - eexists. eexists. splits. reflexivity.
Qed.

(* Concrete Semantics *)
Definition Val : Type := nat.

Inductive CTrace_step : Type :=
  | CTAsgn (x:Var) (v:Val).

Definition CTrace : Type := trace CTrace_step.

Fixpoint acc_val (V0:Valuation) (t:CTrace) : Valuation :=
  match t with
  | [] => V0
  | t :: CTAsgn x v => let V := acc_val V0 t in
                 (x !-> v ; V)
  end.

Definition Aeval_t (V0:Valuation) (t:CTrace) (e:Aexpr) : nat :=
  Aeval (acc_val V0 t) e.

Definition Beval_t (V0:Valuation) (t:CTrace) (e:Bexpr) : bool :=
  Beval (acc_val V0 t) e.

Fixpoint trace_of' (V0: Valuation) (t:CTrace) (s:Stmt) : CTrace :=
  match s with
  | <{ x := e }> => [CTAsgn x (Aeval_t V0 t e)]
  | <{s1 ; s2}> => let t1 := trace_of' V0 t s1 in
                  let t2 := trace_of' V0 t1 s2 in
                  t1 ++ t2
  (* deterministic big-step parallelism*)
  | <{s1 || s2}> => let t1 := trace_of' V0 t s1 in
                  let t2 := trace_of' V0 t1 s2 in
                  t1 ++ t2
  | <{ if b {s1} {s2}}> => if Beval_t V0 t b then trace_of' V0 t s1 else trace_of' V0 t s2
  | <{ skip }> => []
  end.

Definition trace_of (V0:Valuation) (s:Stmt) : CTrace :=
  trace_of' V0 [] s.

Definition has_trace__C (V0:Valuation) (s:Stmt) : Ensemble CTrace := Singleton _ (trace_of V0 s).


Example branch_ex__C : has_trace__C (_ !-> 0) <{if X <= 1 {Y := X ; skip} {Y := 1}}> [CTAsgn Y 0].
Proof. unfold has_trace__C, trace_of. simpl. unfold Aeval_t. simpl. reflexivity. Qed.

Example par_ex__C : has_trace__C (_ !-> 0) <{(X := 1 ; Y := 2) || (X := Y ; Y := X)}> [CTAsgn X 1 ; CTAsgn Y 2 ; CTAsgn X 2 ; CTAsgn Y 2].
Proof. unfold has_trace__C, trace_of, trace_of', Aeval_t. simpl. reflexivity. Qed.

(** Properties *)
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

Definition Bapply_t (s0:sub) (t:STrace) (e:Bexpr) : Bexpr :=
  Bapply (acc_subst s0 t) e.

Definition Bapply_t_id (t:STrace) (e:Bexpr) : Bexpr :=
  Bapply (acc_subst_id t) e.

Fixpoint pc (s0:sub) (t:STrace) : Bexpr :=
  match t with
  | [] => BTrue
  | t :: STCond b => BAnd (Bapply_t s0 t b) (pc s0 t)
  | t :: _ => pc s0 t
  end.

Definition pc_id := pc id_sub.

Definition is_abstraction (V0:Valuation) (tc:CTrace) (ts:STrace) : Prop :=
  acc_val V0 tc = Comp V0 (acc_subst_id ts).

Example completeness_branch_ex : is_abstraction (_ !-> 0) [CTAsgn Y 0] [STCond <{X <= 1}> ; STAsgn Y X]
                       /\ Beval (_ !-> 0) (pc_id [STCond <{X <= 1}> ; STAsgn Y X]) = true.
Proof. splits.
  unfold is_abstraction, acc_subst_id, Comp. simpl. extensionality x.
  unfold update. destruct (Y =? x); reflexivity.
Qed.

Example s_trace_ex := [STAsgn X 1 ; STAsgn Y 2; STAsgn X Y ; STAsgn Y X].
Example completeness_par_ex : has_trace__S <{(X := 1 ; Y := 2) || (X := Y ; Y := X)}> s_trace_ex
                              /\ is_abstraction (_ !-> 0) (trace_of (_ !-> 0) <{(X := 1 ; Y := 2) || (X := Y ; Y := X)}>) s_trace_ex
                              /\ Beval (_ !-> 0) (pc_id s_trace_ex) = true.
Proof.
  splits.
  - unfold has_trace__S, In. exists [STAsgn X 1; STAsgn Y 2]. exists [STAsgn X Y; STAsgn Y X]. splits.
       + repeat constructor.
       + eexists. eexists. splits. reflexivity.
       + eexists. eexists. splits. reflexivity.
  - unfold trace_of. simpl. unfold Aeval_t. simpl. rewrite 2 update_eq.
    unfold is_abstraction. simpl.
    unfold acc_subst_id, acc_subst, s_trace_ex. simpl. rewrite 2 update_eq.
    extensionality x. unfold Comp, update.
    (* lol *)
    destruct (Y =? x); destruct (X =? X); destruct (Y =? Y); destruct (Y =? X); destruct (X =? Y); destruct (X =? x);
      reflexivity.
Qed.

Lemma cond_idemp : forall b t s,
    acc_subst s (t :: STCond b) = acc_subst s t.
Proof. intros. reflexivity. Qed.

Lemma acc_subst_empty : forall s,
    acc_subst s [] = s.
Proof. intros. reflexivity. Qed.

Lemma acc_subst_app : forall s0 t1 t2,
    acc_subst s0 (t1 ++ t2) = acc_subst (acc_subst s0 t1) t2.
Proof.
  intros. induction t2.
  - reflexivity.
  - destruct a.
    + simpl. rewrite IHt2. reflexivity.
    + assumption.
Qed.

Lemma pc_app : forall V0 t1 t2, Beval V0 (pc_id (t1 ++ t2)) = Beval V0 (pc_id t1) && Beval V0 (pc (acc_subst_id t1) t2).
Proof.
  induction t2.
  - simpl. destruct (Beval V0 (pc_id t1)); reflexivity.
  - destruct a.
    + assumption.
    + unfold pc_id in *. simpl. rewrite IHt2. simpl. unfold Bapply_t, acc_subst_id. rewrite acc_subst_app.
      (* this is a mess, but it's just rearranging some conjunctions *)
      rewrite 2 andb_assoc. rewrite andb_comm. rewrite andb_assoc. rewrite andb_comm.
      rewrite andb_comm with (b1 := Beval V0 (pc (acc_subst id_sub t1) t2)). rewrite andb_assoc. reflexivity.
Qed.

Lemma trace_seq_app : forall V s1 s2, trace_of V <{s1 ; s2}> = trace_of V s1 ++ trace_of' V (trace_of V s1) s2.
Proof.
  intros. destruct(trace_of V s1) eqn:H;
    unfold trace_of in *; simpl; rewrite H; reflexivity.
Qed.

Lemma acc_val_app : forall V0 t1 t2,
    acc_val V0 (t1 ++ t2) = acc_val (acc_val V0 t1) t2.
Proof.
  induction t2;
    [|destruct a; simpl; rewrite IHt2]; reflexivity.
Qed.

Lemma interleave_degen : forall t1 t2, is_interleaving t1 t2 (t1 ++ t2).
Proof.
  intros. induction t2.
  - constructor.
  - simpl. constructor. assumption.
Qed.

Lemma par_all_left : forall s1 s2 t1 t2, has_trace__S s1 t1 -> has_trace__S s2 t2 -> has_trace__S <{s1 || s2}> (t1 ++ t2).
Proof.
  intros. exists t1. exists t2. splits.
  - apply interleave_degen.
  - assumption.
  - assumption.
Qed.

Lemma is_abstraction_asgn : forall V0 t t' x e,
    is_abstraction V0 t t' -> is_abstraction V0 (t::CTAsgn x (Aeval_t V0 t e)) (t'::STAsgn x e).
Proof.
  intros. unfold is_abstraction, acc_subst_id in *. simpl. unfold Aeval_t. rewrite H. simpl.
  rewrite asgn_sound. reflexivity.
Qed.

Lemma is_abstraction_step : forall V0 t t' x, exists y,
    is_abstraction V0 t t' -> is_abstraction V0 (t::x) (t'::y).
Proof.
  intros. dependent destruction x.
  - exists (STAsgn x v). intro.
    assert (v = Aeval_t V0 t v). { unfold Aeval_t. reflexivity. }
    rewrite H0. apply is_abstraction_asgn. assumption.
Qed.

Lemma trace_acc_val : forall V0 t s, trace_of' V0 t s = trace_of (acc_val V0 t) s.
Proof.
  intros. induction t.
  - simpl. unfold trace_of. reflexivity.
  - destruct a; induction s.
    + simpl. unfold trace_of. simpl. unfold Aeval_t. reflexivity.
    + simpl in *. rewrite IHs1. unfold trace_of. subst; simpl.
Admitted.

Lemma pc_monotone : forall V0 t t', Beval V0 (pc_id (t ++ t')) = true ->
                               Beval V0 (pc_id t) = true /\ Beval V0 (pc (acc_subst_id t) t') = true.
Proof. intros. rewrite pc_app in H. apply andb_true_iff in H. assumption. Qed.

Theorem soundness : forall V0 s t,
    has_trace__S s t ->
    Beval V0 (pc_id t) = true ->
    exists t', has_trace__C V0 s t'
          /\ is_abstraction V0 t' t.
Proof.
  intros. dependent induction s.
  - exists [CTAsgn x (Aeval V0 e)]. splits.
    + inversion H; subst. unfold is_abstraction, acc_subst_id. simpl.
      rewrite asgn_sound. rewrite comp_id. reflexivity.
  - inversion H. destruct H1 as [t' [Happ [Hs1 Hs2]]].
    rewrite Happ in H0. apply pc_monotone in H0. destruct H0.
    destruct (IHs1 x) as [t1 [t1Comp t1Abs]]; try assumption.
    destruct (IHs2 t') as [t2 [t2Comp t2Abs]]; try assumption.
    shelve.
    exists (t1 ++ t2). splits.
    + unfold has_trace__C in *. unfold trace_of in *. simpl.
      rewrite trace_acc_val. rewrite <- t1Comp. rewrite <- t2Comp. simpl.
      (* did I fuck up the definitions somehow? this all seems very off *)

Theorem completeness : forall s V0 , exists ts,
    has_trace__S s ts /\ is_abstraction V0 (trace_of V0 s) ts /\ Beval V0 (pc_id ts) = true.
Proof.
  intros.
  (* unfold trace_of, trace_of'. *)
  dependent induction s.
  - (* x := e *)
    exists [STAsgn x e]. splits.
    + unfold trace_of. simpl. unfold is_abstraction, Aeval_t, acc_subst_id.
      simpl. rewrite asgn_sound. rewrite comp_id. reflexivity.
  - (* s1 ; s2 *)
    destruct (IHs1 V0) as [ts1 [comp [IH1 IHpc1]]].
    destruct (IHs2 (acc_val V0 (trace_of V0 s1))) as [ts2 [comp2 [IH2 IHpc2]]].
    exists (ts1 ++ ts2). splits.
    + eexists. eexists. splits; [apply comp | apply comp2].
    + rewrite trace_seq_app. admit.
    + rewrite pc_app. rewrite andb_true_iff. splits.
      * assumption.
      * unfold is_abstraction in IH1. rewrite IH1 in IHpc2.
        rewrite comp_subB in IHpc2. unfold pc_id in IHpc2.

  - (* s1 || s2 *)
    destruct (IHs1 V0) as [ts1 [comp [IH1 IHpc1]]].
    destruct (IHs2 (acc_val V0 (trace_of V0 s1))) as [ts2 [comp2 [IH2 IHpc2]]].
    exists (ts1 ++ ts2). splits.
    + apply par_all_left; assumption.
    + unfold trace_of. simpl. unfold is_abstraction in *. rewrite acc_val_app.

      (* need some lemmas about multiple composition but I cannot formulate them separate from acc_*
       which is worrying *)


(* maybe needed later *)
Fixpoint is_prefix {A:Type} (t0 t:list A) : Prop :=
  match t0 with
  | [] => True
  | x :: xs => match t with
             | [] => False
             | y :: ys => x = y /\ is_prefix xs ys
             end
  end.

Definition prefix_closure (sem: STrace -> Prop) (t:STrace) : Prop :=
  exists t', sem t' /\ is_prefix t t'.
