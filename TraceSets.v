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

From SymEx Require Import Traces.

From SymEx Require Import Parallel.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.

Definition Var : Type := string.
Example X : Var := "x".
Example Y : Var := "y".

Ltac splits := repeat (try split).

(* Trying out the "continuation" style from mechanized semantics *)
Inductive Program : Type :=
| PStop
| PSeq (s:Stmt) (p:Program)
| PParL (s:Stmt) (p:Program)
| PParR (s:Stmt) (p:Program)
.

(** Symbolic semantics *)
Inductive STrace_step : Type :=
| STAsgn (x:Var) (e:Aexpr)
| STCond (b:Bexpr).

Definition STrace : Type := trace STrace_step.

Definition Concatenate (A B: Ensemble STrace) : Ensemble STrace :=
  fun t => exists t1 t2, t = t1 ++ t2 /\ A t1 /\ B t2.

Example concat_ex : In _  (Concatenate
                                (Union _
                                      (Singleton _ [STAsgn X 0])
                                      (Singleton _ [STAsgn Y 1]))
                                (Union _
                                      (Singleton _ [STAsgn Y 0])
                                      (Singleton _ [STAsgn X 1])))
                         [STAsgn X 0; STAsgn Y 0].
Proof.
  exists [STAsgn X 0]. exists [STAsgn Y 0]. splits.
  apply Union_introl. apply In_singleton.
  apply Union_introl. apply In_singleton.
Qed.

Example concat_ex' : In _  (Concatenate
                                (Union _
                                      (Singleton _ [STAsgn X 0])
                                      (Singleton _ [STAsgn Y 1]))
                                (Union _
                                      (Singleton _ [STAsgn Y 0])
                                      (Singleton _ [STAsgn X 1])))
                         [STAsgn Y 1; STAsgn X 1].
Proof.
  exists [STAsgn Y 1]. exists [STAsgn X 1]. splits.
  apply Union_intror. apply In_singleton.
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

Fixpoint prog_traces__S (p:Program) : Ensemble STrace :=
  match p with
  | PNil => Singleton _ []
  | PStep p s => Concatenate (prog_traces__S p) (stmt_traces__S s)
  end
with stmt_traces__S (s:Stmt) : Ensemble STrace :=
       match s with
       | <{ x := e }> => Singleton _ [STAsgn x e]
       | <{s1 || s2}> => Interleave (prog_traces__S s1) (prog_traces__S s2)
       | <{if b s1 s2 fi}> => Union _
                                  (Concatenate (Singleton _ [STCond b]) (prog_traces__S s1))
                                  (Concatenate (Singleton _ [STCond (BNot b)]) (prog_traces__S s2))
       end
.

Example branch_ex : In _ (stmt_traces__S <{if X <= 1 {X := Y} {Y := 1} fi}>) [STCond <{X <= 1}> ; STAsgn X Y].
Proof. unfold stmt_traces__S, prog_traces__S. apply Union_introl. eexists. eexists [STAsgn X Y]. splits.
       eexists. eexists. splits. reflexivity.
Qed.

Example left_ex : Program := PStep (PStep PNil <{X := 1}>) <{Y := 2}>.
Example right_ex : Program := PStep (PStep PNil <{X := Y}>) <{Y := X}>.

Example par_ex : stmt_traces__S <{left_ex || right_ex}> [STAsgn X 1 ; STAsgn X Y ; STAsgn Y X ; STAsgn Y 2].
Proof.
  unfold left_ex, right_ex. unfold stmt_traces__S, prog_traces__S.
  exists [STAsgn X 1 ; STAsgn Y 2]. exists [STAsgn X Y ; STAsgn Y X]. splits.
  - repeat (constructor).
  - eexists. eexists. splits. reflexivity.
    + eexists. eexists. splits. reflexivity.
  - eexists. eexists. splits. reflexivity.
    + eexists. eexists. splits. reflexivity.
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

Fixpoint prog_trace__C (V0 : Valuation) (p:Program) : CTrace :=
  match p with
  | PNil => []
  | PStep p s => let t1 := prog_trace__C V0 p in
      t1 ++ stmt_trace__C (acc_val V0 t1) s
  end
with stmt_trace__C (V0 : Valuation) (s:Stmt) : CTrace :=
       match s with
       | <{ x := e }> => [CTAsgn x (Aeval V0 e)]
       | <{ p1 || p2 }> => let t1 := prog_trace__C V0 p1 in
      t1 ++ prog_trace__C (acc_val V0 t1) p2
       | <{ if b p1 p2 fi }> => if Beval V0 b then prog_trace__C V0 p1 else prog_trace__C V0 p2
       end.

Example branch_ex__C : stmt_trace__C (_ !-> 0) <{if X <= 1 {Y := X} {Y := 1} fi}> = [CTAsgn Y 0].
Proof. simpl. reflexivity. Qed.

Example par_ex__C : stmt_trace__C (_ !-> 0) <{left_ex || right_ex}> = [CTAsgn X 1 ; CTAsgn Y 2 ; CTAsgn X 2 ; CTAsgn Y 2].
Proof. simpl. rewrite 2 update_eq. reflexivity. Qed.

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
Example completeness_par_ex : stmt_traces__S <{left_ex || right_ex}> s_trace_ex
                              /\ is_abstraction (_ !-> 0) (stmt_trace__C (_ !-> 0) <{left_ex || right_ex}>) s_trace_ex
                              /\ Beval (_ !-> 0) (pc_id s_trace_ex) = true.
Proof.
  splits.
  - unfold stmt_traces__S. exists [STAsgn X 1; STAsgn Y 2]. exists [STAsgn X Y; STAsgn Y X]. splits.
    + repeat constructor.
    + eexists. eexists. splits. reflexivity.
      * eexists. eexists. splits. reflexivity.
    + eexists. eexists. splits. reflexivity.
      * eexists. eexists. splits. reflexivity.
  - simpl. rewrite 2 update_eq.
    unfold is_abstraction, s_trace_ex. simpl.
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

Lemma pc_app : forall V0 s t1 t2, Beval V0 (pc s (t1 ++ t2)) = Beval V0 (pc s t1) && Beval V0 (pc (acc_subst s t1) t2).
Proof.
  induction t2.
  - simpl. destruct (Beval V0 (pc s t1)); reflexivity.
  - destruct a.
    + assumption.
    + unfold pc_id in *. simpl. rewrite IHt2. simpl. unfold Bapply_t, acc_subst_id. rewrite acc_subst_app.
      (* this is a mess, but it's just rearranging some conjunctions *)
      rewrite 2 andb_assoc. rewrite andb_comm. rewrite andb_assoc. rewrite andb_comm.
      rewrite andb_comm with (b1 := Beval V0 (pc (acc_subst s t1) t2)). rewrite andb_assoc. reflexivity.
Qed.

(* Lemma trace_seq_app : forall V s1 s2, trace_of V <{s1 ; s2}> = trace_of V s1 ++ trace_of' V (trace_of V s1) s2. *)
(* Proof. *)
(*   intros. destruct (trace_of V s1) eqn:H; *)
(*     unfold trace_of in *; simpl; rewrite H; reflexivity. *)
(* Qed. *)

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

Lemma par_all_left : forall s1 s2 t1 t2, prog_traces__S s1 t1 -> prog_traces__S s2 t2 -> stmt_traces__S <{s1 || s2}> (t1 ++ t2).
Proof.
  intros. exists t1. exists t2. splits.
  - apply interleave_degen.
  - assumption.
  - assumption.
Qed.

Lemma pc_monotone : forall V0 t t', Beval V0 (pc_id (t ++ t')) = true ->
                               Beval V0 (pc_id t) = true /\ Beval V0 (pc (acc_subst_id t) t') = true.
Proof. intros. unfold pc_id, acc_subst_id in *. rewrite pc_app in H. apply andb_true_iff in H. assumption. Qed.

Theorem soundness : forall p t V0,
    prog_traces__S p t ->
    Beval V0 (pc_id t) = true ->
    exists t', prog_trace__C V0 p = t'
        /\ is_abstraction V0 t' t.
Proof.
  dependent induction p; intros.
  - exists []. splits. inversion H. unfold is_abstraction. simpl. apply comp_id.
  - dependent induction s;
      destruct H as [t1 [t2 [Happ [Hprog Hstep]]]];
      rewrite Happ in H0; unfold pc_id in H0; rewrite pc_app in H0; rewrite andb_true_iff in H0; destruct H0;
      destruct (IHp t1 V0 Hprog H) as [t' [IHprog IHabs]].
    + exists (t' :: CTAsgn x (Aeval_t V0 t' e)). splits.
      * simpl. rewrite IHprog. unfold Aeval_t. reflexivity.
      * inversion Hstep. unfold is_abstraction in *. simpl. rewrite Happ. rewrite <- H1. unfold acc_subst_id in *. rewrite acc_subst_app.
        simpl. rewrite asgn_sound. unfold Aeval_t. rewrite IHabs. reflexivity.
    + destruct Hstep; destruct H1 as [branch [cont [HApp1 [Hbranch Hcont]]]];
        inversion Hbranch; subst; rewrite pc_app in H0;
        rewrite andb_true_iff in H0; destruct H0; simpl in H0; rewrite andb_true_r in H0.
      * exists (prog_trace__C V0 p ++ prog_trace__C (acc_val V0 (prog_trace__C V0 p)) s1). splits.
        ** simpl. unfold Bapply_t in H0. simpl in H0. rewrite 2 IHabs. rewrite comp_subB. unfold acc_subst_id.
           rewrite H0. reflexivity.
        ** admit. (* true branch maintaints abstraction *)
      * exists (prog_trace__C V0 p ++ prog_trace__C (acc_val V0 (prog_trace__C V0 p)) s2). splits.
        ** simpl. unfold Bapply_t in H0. simpl in H0. rewrite 2 IHabs. rewrite comp_subB. unfold acc_subst_id.
           apply negb_true_iff in H0. rewrite H0. rewrite IHabs. unfold acc_subst_id. reflexivity.
        ** admit. (* false branch maintains abstraction *)
    + (* this is actually not true, since an abstract trace may choose a concretely "impossible" order of execution, huh *)
Admitted.

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
