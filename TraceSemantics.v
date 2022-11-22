(** * Trace Semantics *)

(** Anticipating the need for trace semantics for reduction in a concurrent setting,
    we develop them for the language extended with procedures from Recursion.v
 *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Program.   (* for `dependent induction` *)
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)
From Coq Require Import Relations.

From SymEx Require Import Expr.
Import ProcedureExpr.

From SymEx Require Import Maps.
Import ProcedureMaps.

From SymEx Require Import Recursion.

From SymEx Require Import Traces.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.

(** Symbolic semantics *)

Fixpoint Stmt_sub (s:Stmt) (u y:LVar) : Stmt :=
  let t : LSub := (u !-> (ALVar y) ; Lid_sub) in
  match s with
  | SGAsgn x e => SGAsgn x (Aapply Gid_sub t e)
  | SLAsgn x e => SLAsgn (if u =? x then y else x) (Aapply Gid_sub t e)
  | SProc P e => SProc P (Aapply Gid_sub t e)
  | SSeq s1 s2 => SSeq (Stmt_sub s1 u y) (Stmt_sub s2 u y)
  | SIf b s1 s2 => SIf (Bapply Gid_sub t b) (Stmt_sub s1 u y) (Stmt_sub s2 u y)
  | SWhile b s => SWhile (Bapply Gid_sub t b) (Stmt_sub s u y)
  | SReturn => SReturn
  end.

Definition STrace_step : Type := (Bexpr + (GVar * Aexpr) + (LVar * Aexpr)).

Definition cond  : Bexpr -> STrace_step := fun x => inl (inl x).
Definition asgnG : GVar -> Aexpr -> STrace_step := fun x e => inl (inr (x, e)).
Definition asgnL : LVar -> Aexpr -> STrace_step := fun x e => inr (x, e).

Definition STrace := trace STrace_step.

Fixpoint acc_GSubst (G:GSub) (L:LSub) (t:STrace) : GSub :=
  match t with
  | [] => G
  | t' :: inl (inr (x, e)) => let l := acc_LSubst G L t' in
                            let g := acc_GSubst G L t' in
                            (x !-> Aapply g l e ; g)
  | t' :: _ => acc_GSubst G L t'
  end
with acc_LSubst (G:GSub) (L:LSub) (t:STrace) : LSub :=
  match t with
  | [] => L
  | t' :: inr (x, e) => let l := acc_LSubst G L t' in
                      let g := acc_GSubst G L t' in
                      (x !-> Aapply g l e ; l)
  | t' :: _ => acc_LSubst G L t'
  end.

Definition acc_GSubst_id := acc_GSubst Gid_sub Lid_sub.
Definition acc_LSubst_id := acc_LSubst Gid_sub Lid_sub.

Definition X : GVar := "X".
Definition Y : GVar := "Y".
Definition Z : GVar := "Z".

Definition A : LVar := "A".
Definition B : LVar := "B".
Definition C : LVar := "C".

Definition Aapply_t : STrace -> Aexpr -> Aexpr :=
  fun t e => Aapply (acc_GSubst_id t) (acc_LSubst_id t) e.

Definition Bapply_t : STrace -> Bexpr -> Bexpr :=
  fun t e => Bapply (acc_GSubst_id t) (acc_LSubst_id t) e.

Fixpoint pc (t:STrace) : Bexpr :=
  match t with
  | [] => BTrue
  | t' :: inr _ => pc t'
  | t' :: inl (inr _) => pc t'
  | t' :: inl (inl p) => BAnd (Bapply_t t' p) (pc t')
  end.

Definition SConfig : Type := Stmt * STrace.

Reserved Notation " c '->s' c' " (at level 40).
Inductive Sstep : relation SConfig  :=
| SGAsgn_step : forall x e s t,
    (<{ x :=G e ; s }>, t) ->s (s, (t :: asgnG x e))
| SLAsgn_step : forall x e s t,
    (<{ x :=L e ; s }>, t) ->s (s, t :: asgnL x e)
| SProc_step : forall (t:STrace) u y body e s t,
    (* "y fresh", somehow *)
    (<{ proc(u){body}(e) ; s }>, t) ->s (SSeq (Stmt_sub body u y) s, t :: asgnL y e)
| SReturn_step : forall s t,
    (<{ return ; s }>, t) ->s (s, t)
| SIfTrue_step : forall b s1 s2 s t,
    (<{ if b {s1}{s2} ; s}>, t) ->s (<{ s1 ; s }>, t :: cond b)
| SIfFalse_step : forall b s1 s2 s t,
    (<{ if b {s1}{s2} ; s}>, t) ->s (<{ s2 ; s }>, t :: cond (BNot b))
| SWhileTrue_step : forall b s s' t,
    (<{ while b {s} ; s' }>, t) ->s (<{ s ; while b {s} ; s' }>, t :: cond b)
| SWhileFalse_step : forall b s s' t,
    (<{ while b {s} ; s' }>, t) ->s (s', t :: cond (BNot b))
where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40).

(** Concrete semantics *)

Definition Val : Type := nat.
Definition CTrace_step : Type := (GVar * Val) + (LVar * Val).

Definition CTrace := trace CTrace_step.

Fixpoint acc_GVal (G0:GVal) (L0:LVal) (t:CTrace) : GVal :=
  match t with
  | Tnil => G0
  | Tcons t' (inr _) => acc_GVal G0 L0 t'
  | Tcons t' (inl (x, v)) => let G' := acc_GVal G0 L0 t' in
                            (x !-> v ; G')
  end
with acc_LVal (G0:GVal) (L0:LVal) (t:CTrace) : LVal :=
  match t with
  | Tnil => L0
  | Tcons t' (inl _) => acc_LVal G0 L0 t'
  | Tcons t' (inr (x, v)) => let L' := acc_LVal G0 L0 t' in
                            (x !-> v ; L')
  end.

Definition Aeval_t (G0:GVal) (L0:LVal) (t:CTrace) (e:Aexpr) : nat :=
  Aeval (acc_GVal G0 L0 t) (acc_LVal G0 L0 t) e.

Definition Beval_t (G0:GVal) (L0:LVal) (t:CTrace) (b:Bexpr) : bool :=
  Beval (acc_GVal G0 L0 t) (acc_LVal G0 L0 t) b.

Lemma Gcomp_update_comm : forall G L x (v:Val) s,
    GComp G L (update s x (AConst v)) = update (GComp G L s) x v.
Proof.
  intros. extensionality y.
  unfold GComp. unfold update. destruct (x =? y); simpl; reflexivity.
Qed.

Lemma Lcomp_update_comm : forall G L x (v:Val) s,
    LComp G L (update s x (AConst v)) = update (LComp G L s) x v.
Proof.
  intros. extensionality y.
  unfold LComp. unfold update. destruct (x =? y); simpl; reflexivity.
Qed.

Definition CConfig : Type := Stmt * CTrace.

Inductive Cstep (G0:GVal) (L0:LVal) : relation CConfig :=
| CGAsgn_step : forall x e s t,
    Cstep G0 L0 (<{ x :=G e ; s }>, t) (s, t :: inl (x, Aeval_t G0 L0 t e))
| CLAsgn_step : forall x e s t,
    Cstep G0 L0 (<{ x :=L e ; s }>, t) (s, t :: inr (x, Aeval_t G0 L0 t e))
| CProc_step : forall u body e s' t y,
    (* y fresh *)
    Cstep G0 L0 (<{ proc(u){body}(e) ; s' }>, t)  (SSeq (Stmt_sub body u y) s', t :: inr (y, Aeval_t G0 L0 t e))
| CReturn_step : forall s t,
    Cstep G0 L0 (<{ return ; s }>, t)  (s, t)
| CIfTrue_step : forall b s1 s2 s t,
    Beval_t G0 L0 t b = true ->
    Cstep G0 L0 (<{ if b {s1}{s2} ; s }>, t)  (<{s1 ; s}>, t)
| CIfFalse_step : forall b s1 s2 s t,
    Beval_t G0 L0 t b = false ->
    Cstep G0 L0 (<{ if b {s1}{s2} ; s }>, t)  (<{s2 ; s}>, t)
| CWhileTrue_step : forall b s s' t,
    Beval_t G0 L0 t b = true ->
    Cstep G0 L0 (<{ while b {s} ; s' }>, t)  (<{s ; while b {s} ; s'}>, t)
| CWhileFalse_step : forall b s s' t,
    Beval_t G0 L0 t b = false ->
    Cstep G0 L0 (<{ while b {s} ; s' }>, t)  (s', t).

Definition multi_Cstep {G0:GVal} {L0:LVal} := clos_refl_trans_n1 _ (Cstep G0 L0).
Notation " c '=>c' c'" := (Cstep _ _ c c').
Notation " c '=>*' c' " := (multi_Cstep c c') (at level 40).

(** an aside with examples to verify semantics *)

(* not sure how to elegantly incorporate this assumption without semantics *)
Axiom Seq_Assoc : forall s1 s2 s3,
    <{ (s1 ; s2) ; s3 }> = <{ s1 ; s2 ; s3 }>.

Definition foo_body : Stmt := <{
      B :=L A ;
      Y :=G B + 1;
      return }>.

Example test_program : Stmt :=
  <{ if X <= 1
              {proc(A){ foo_body }(Y + 1)}
              {proc(A){ foo_body }(2)} ;
       Y :=G 0
    }>.

Definition test_Strace :=
  [ cond <{ X <= 1 }>;
    asgnL C <{Y + 1}>;
    asgnL B C;
    asgnG Y <{ B + 1 }>].

Definition test_Ctrace :=
  [ inr (C, 1);
     inr (B, 1);
     inl (Y, 2)].

Example test_Scomp : (test_program, [])
                        ->* (<{Y :=G 0}>,
                                test_Strace).
Proof.
  eapply Relation_Operators.rtn1_trans. apply SReturn_step.
  eapply Relation_Operators.rtn1_trans. apply SGAsgn_step.
  eapply Relation_Operators.rtn1_trans. apply SLAsgn_step.
  assert (proc_subst : <{ B :=L C; Y :=G B + 1; return; Y :=G 0 }>
                       = SSeq (Stmt_sub foo_body A C) <{ Y :=G 0 }>).
  {simpl. rewrite update_eq. repeat (rewrite Seq_Assoc). reflexivity. }
  eapply Relation_Operators.rtn1_trans. rewrite proc_subst. eapply SProc_step.
  exact [].
  eapply Relation_Operators.rtn1_trans. apply SIfTrue_step.
  apply rtn1_refl.
Qed.


Example test_Ccomp : @multi_Cstep (_ !-> 0) (_ !-> 0)
                       (test_program, [])
                       (<{Y :=G 0}>,
                           test_Ctrace).
Proof.
  unfold test_Ctrace.
  eapply Relation_Operators.rtn1_trans. apply CReturn_step.
  eapply Relation_Operators.rtn1_trans.
    assert (ev1 : Aeval_t (_ !-> 0) (_ !-> 0) [inr (C, 1);inr (B, 1)] <{B + 1}> = 2).
    { unfold Aeval_t. simpl. reflexivity. }
    assert (step1 : Cstep (_ !-> 0) (_ !-> 0) (<{ Y :=G B + 1; return; Y :=G 0 }>, [inr (C, 1);inr (B, 1)])
            (<{ return; Y :=G 0 }>, [inr (C, 1);inr (B, 1);inl (Y, Aeval_t (_ !-> 0) (_ !-> 0) [inr (C, 1);inr (B, 1)] <{B + 1}> )])).
    { apply CGAsgn_step. }
  rewrite <- ev1. apply step1.
  eapply Relation_Operators.rtn1_trans.
    assert (ev2: Aeval_t (_ !-> 0) (_ !-> 0) [inr (C, 1)] C = 1).
    { unfold Aeval_t. simpl. rewrite update_eq. reflexivity. }
    assert (step2 : Cstep (_ !-> 0) (_ !-> 0) (<{ B :=L C; Y :=G B + 1; return; Y :=G 0 }>, [inr (C, 1)])
            (<{ Y :=G B + 1; return; Y :=G 0 }>, [inr (C, 1);inr (B, Aeval_t (_ !-> 0) (_ !-> 0) [inr (C, 1)] C)])).
    { apply CLAsgn_step. }
  rewrite <- ev2. apply step2.
  eapply Relation_Operators.rtn1_trans.
    assert (ev3 : Aeval_t (_ !-> 0) (_ !-> 0) [] <{Y + 1}> = 1). {
      unfold Aeval_t. reflexivity. }
    assert (step3: Cstep (_ !-> 0) (_ !-> 0) (<{proc(A){foo_body}(Y + 1) ; Y :=G 0}>, [])
                     (SSeq (Stmt_sub foo_body A C) <{Y :=G 0}>, [inr (C, 1)])).
    { rewrite <- ev3. eapply CProc_step. }
  simpl in step3. repeat (rewrite Seq_Assoc in step3). apply step3.
    eapply Relation_Operators.rtn1_trans.
    assert (Beval_t (_ !-> 0) (_ !-> 0) [] <{ X <= 1 }> = true). { unfold Beval_t. reflexivity. }
    eapply CIfTrue_step. apply H.
  apply rtn1_refl.
Qed.

(** Correctness *)
Ltac splits := repeat (try split).

Example test_correct_GVal : acc_GVal (_ !-> 0) (_ !-> 0) test_Ctrace = GComp (_ !-> 0) (_ !-> 0) (acc_GSubst_id test_Strace).
Proof.
  extensionality x.
  unfold acc_GSubst_id. unfold GComp. simpl. unfold update.
  repeat (rewrite String.eqb_refl). destruct (Y =? x).
  - reflexivity.
  - apply apply_empty.
Qed.

Example test_correct_LVal : acc_LVal (_ !-> 0) (_ !-> 0) test_Ctrace = LComp (_ !-> 0) (_ !-> 0) (acc_LSubst_id test_Strace).
Proof.
  extensionality x.
  unfold acc_LSubst_id. unfold LComp. simpl. unfold update.
  repeat (rewrite String.eqb_refl). destruct (B =? x).
  - reflexivity.
  - destruct (C =? x).
    + reflexivity.
    + apply apply_empty.
Qed.

(* May be possible to extend to any initial trace *)
Theorem correctness : forall s s' t G0 L0,
    (s, []) ->* (s', t) ->
    Beval G0 L0 (pc t) = true ->
    exists t', @multi_Cstep G0 L0 (s, []) (s', t')
          /\ acc_GVal G0 L0 t' = GComp G0 L0 (acc_GSubst_id t)
          /\ acc_LVal G0 L0 t' = LComp G0 L0 (acc_LSubst_id t).
Proof.
  intros. dependent induction H.
  - exists []. splits. apply rtn1_refl.
  - dependent destruction H.
    + (* global assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=G e ; s'}> t0) as [t' [comp [IHG IHL]]];
        try reflexivity;
        try assumption.
      exists (t' :: inl (x, Aeval_t G0 L0 t' e)). splits.
      * eapply Relation_Operators.rtn1_trans. apply CGAsgn_step.
        assumption.
      * unfold acc_GSubst_id in *. unfold acc_LSubst_id in *. unfold Aeval_t.
        simpl. rewrite Gasgn_sound. rewrite eval_comp.
        rewrite <- IHG. rewrite <- IHL. reflexivity.
      * simpl. assumption.
    + (* local assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=L e ; s'}> t0) as [t' [comp [IHG IHL]]];
        try reflexivity;
        try assumption.
      exists (t' :: inr (x, Aeval (acc_GVal G0 L0 t') (acc_LVal G0 L0 t') e)). splits.
      * eapply Relation_Operators.rtn1_trans. apply CLAsgn_step.
        assumption.
      * simpl. assumption.
      * unfold acc_GSubst_id in *. unfold acc_LSubst_id in *. unfold Aeval_t.
        simpl. rewrite Lasgn_sound. rewrite eval_comp.
        rewrite <- IHG. rewrite <- IHL. reflexivity.
    + (* proc *)
      destruct (IHclos_refl_trans_n1 s <{ proc(u){body}(e) ; s0}> t1) as [t' [comp [IHG IHL]]];
        try reflexivity;
        try assumption.
      exists (t' :: inr (y, Aeval_t G0 L0 t' e)). splits.
      * eapply Relation_Operators.rtn1_trans;
          [apply CProc_step | assumption].
      * simpl. assumption.
      * unfold acc_GSubst_id in *. unfold acc_LSubst_id in *. unfold Aeval_t.
        simpl. rewrite Lasgn_sound. rewrite eval_comp.
        rewrite <- IHG. rewrite <- IHL. reflexivity.
    + (* return *)
      destruct (IHclos_refl_trans_n1 s <{ return ; s'}> t) as [t' [comp [IHG IHL]]];
        try reflexivity;
        try assumption.
      exists t'. splits.
      * eapply Relation_Operators.rtn1_trans;
          [apply CReturn_step | assumption].
      * assumption.
      * assumption.
    + (* if true *)
      simpl in H1. apply andb_true_iff in H1. destruct H1.
      destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0}> t0) as [t' [comp [IHG IHL]]];
        try reflexivity;
        try assumption.
      exists t'. splits.
      * eapply Relation_Operators.rtn1_trans.
        ** eapply CIfTrue_step. unfold Beval_t.
           unfold Bapply_t in H. rewrite IHG. rewrite IHL.
           rewrite <- eval_compB. rewrite Comp_subB. apply H.
        ** apply comp.
      * assumption.
      * assumption.
    + (* if false *)
      simpl in H1. apply andb_true_iff in H1. destruct H1. apply negb_true_iff in H.
      destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0}> t0) as [t' [comp [IHG IHL]]];
        try reflexivity;
        try assumption.
      exists t'. splits.
      * eapply Relation_Operators.rtn1_trans.
        ** eapply CIfFalse_step. unfold Beval_t.
           unfold Bapply_t in H. rewrite IHG. rewrite IHL.
           rewrite <- eval_compB. rewrite Comp_subB. apply H.
        ** apply comp.
      * simpl. assumption.
      * simpl. assumption.
    + (* while true *)
      simpl in H1. apply andb_true_iff in H1. destruct H1.
      destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'0}> t0) as [t' [comp [IHG IHL]]];
        try reflexivity;
        try assumption.
      exists t'. splits.
      * eapply Relation_Operators.rtn1_trans.
        ** eapply CWhileTrue_step. unfold Beval_t.
           unfold Bapply_t in H. rewrite IHG. rewrite IHL.
           rewrite <- eval_compB. rewrite Comp_subB. apply H.
        ** assumption.
      * simpl. assumption.
      * simpl. assumption.
    + (* while false *)
      simpl in H1. apply andb_true_iff in H1. destruct H1. apply negb_true_iff in H.
      destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'}> t0) as [t' [comp [IHG IHL]]];
        try reflexivity;
        try assumption.
      exists t'. splits.
      * eapply Relation_Operators.rtn1_trans.
        ** eapply CWhileFalse_step. unfold Beval_t.
           unfold Bapply_t in H. rewrite IHG. rewrite IHL.
           rewrite <- eval_compB. rewrite Comp_subB. apply H.
        ** apply comp.
      * simpl. assumption.
      * simpl. assumption.
Qed.

Example test_complete_B : Beval (_ !-> 0) (_ !-> 0) (pc test_Strace) = true.
Proof. reflexivity. Qed.

Theorem completeness : forall s s' t G0 L0,
    @multi_Cstep G0 L0 (s, []) (s', t) ->
    exists (t':STrace),
      (s, []) ->* (s', t')
      /\ Beval G0 L0 (pc t') = true
      /\ GComp G0 L0 (acc_GSubst_id t') = acc_GVal G0 L0 t
      /\ LComp G0 L0 (acc_LSubst_id t') = acc_LVal G0 L0 t.
Proof.
  intros. dependent induction H.
  - exists []. splits.
    apply rtn1_refl.
  - inversion H; subst.
    + (* global assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=G e ; s'}> t0) as [t' [comp [pc_true [IHG IHL]]]];
        try reflexivity.
      exists (t' :: asgnG x e). splits.
      * eapply Relation_Operators.rtn1_trans. apply SGAsgn_step.
        assumption.
      * simpl. assumption.
      * unfold acc_GSubst_id in *. unfold acc_LSubst_id in *. unfold Aeval_t.
        simpl. rewrite Gasgn_sound. rewrite eval_comp.
        rewrite IHG. rewrite IHL. reflexivity.
      * simpl. assumption.
      + (* local assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=L e ; s'}> t0) as [t' [comp [pc_true [IHG IHL]]]];
        try reflexivity.
      exists (t' :: asgnL x e). splits.
      * eapply Relation_Operators.rtn1_trans. apply SLAsgn_step.
        assumption.
      * simpl. assumption.
      * simpl. assumption.
      * unfold acc_GSubst_id in *. unfold acc_LSubst_id in *. unfold Aeval_t.
        simpl. rewrite Lasgn_sound. rewrite eval_comp.
        rewrite IHG. rewrite IHL. reflexivity.
      + (* procedure call *)
      destruct (IHclos_refl_trans_n1 s <{ proc(u){body}(e) ; s'0}> t0) as [t' [comp [pc_true [IHG IHL]]]];
        try reflexivity.
      exists (t' :: asgnL y0 e). splits.
      * eapply Relation_Operators.rtn1_trans. apply SProc_step. exact [].
        assumption.
      * simpl. assumption.
      * simpl. assumption.
      * unfold acc_LSubst_id in *. unfold acc_GSubst_id in *. unfold Aeval_t.
        simpl. rewrite Lasgn_sound. rewrite eval_comp.
        rewrite IHG. rewrite IHL. reflexivity.
      + (* return *)
      destruct (IHclos_refl_trans_n1 s <{ return ; s'}> t) as [t' [comp [pc_true [IHG IHL]]]];
        try reflexivity.
      exists t'. splits;
        try assumption.
      eapply Relation_Operators.rtn1_trans. apply SReturn_step. assumption.
      + (* if true *)
      destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0}> t) as [t' [comp [pc_true [IHG IHL]]]];
        try reflexivity.
      exists (t' :: cond b). splits.
      * eapply Relation_Operators.rtn1_trans. apply SIfTrue_step. apply comp.
      * simpl. apply andb_true_iff. split.
        ** unfold Beval_t in H3. rewrite <- IHG in H3. rewrite <- IHL in H3. rewrite <- eval_compB in H3.
           rewrite Comp_subB in H3. unfold Bapply_t. assumption.
        ** assumption.
      * simpl. assumption.
      * simpl. assumption.
      + (* if false *)
      destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0}> t) as [t' [comp [pc_true [IHG IHL]]]];
        try reflexivity.
      exists (t' :: cond (BNot b)). splits.
      * eapply Relation_Operators.rtn1_trans. apply SIfFalse_step. apply comp.
      * simpl. apply andb_true_iff. split.
        ** unfold Beval_t in H3. rewrite <- IHG in H3. rewrite <- IHL in H3. rewrite <- eval_compB in H3.
           rewrite Comp_subB in H3. unfold Bapply_t. apply negb_true_iff. assumption.
        ** assumption.
      * simpl. assumption.
      * simpl. assumption.
      + (* while true *)
      destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'0}> t) as [t' [comp [pc_true [IHG IHL]]]];
        try reflexivity.
      exists (t' :: cond b). splits.
      * eapply Relation_Operators.rtn1_trans. apply SWhileTrue_step. apply comp.
      * simpl. apply andb_true_iff. split.
        ** unfold Beval_t in H3. rewrite <- IHG in H3. rewrite <- IHL in H3. rewrite <- eval_compB in H3.
           rewrite Comp_subB in H3. unfold Bapply_t. assumption.
        ** assumption.
      * simpl. assumption.
      * simpl. assumption.
      + (* while false *)
      destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'}> t) as [t' [comp [pc_true [IHG IHL]]]];
        try reflexivity.
      exists (t' :: cond (BNot b)). splits.
      * eapply Relation_Operators.rtn1_trans. apply SWhileFalse_step. apply comp.
      * simpl. apply andb_true_iff. split.
        ** unfold Beval_t in H3. rewrite <- IHG in H3. rewrite <- IHL in H3. rewrite <- eval_compB in H3.
           rewrite Comp_subB in H3. unfold Bapply_t. apply negb_true_iff. assumption.
        ** assumption.
      * simpl. assumption.
      * simpl. assumption.
Qed.
