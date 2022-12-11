(** * Trace Semantics Examples *)
(** *)
(** Some examples of trace semantics to reduce clutter in TraceSemantics.v
 *)
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)
From Coq Require Import Relations.

From SymEx Require Import Expr.
Import ProcedureExpr.

From SymEx Require Import Maps.
Import ProcedureMaps.

From SymEx Require Import Recursion.

From SymEx Require Import Traces.

From SymEx Require Import TraceSemantics.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.
(** Semantics *)
Definition X : GVar := "X".
Definition Y : GVar := "Y".
Definition Z : GVar := "Z".

Definition A : LVar := "A".
Definition B : LVar := "B".
Definition C : LVar := "C".
(* not sure how to elegantly incorporate this assumption *)
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
                        ->* (<{Y :=G 0}>, test_Strace).
Proof with (unfold test_Strace).
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
                       (<{Y :=G 0}>, test_Ctrace).
Proof.
  unfold test_Ctrace.
  eapply Relation_Operators.rtn1_trans. apply CReturn_step.
  eapply Relation_Operators.rtn1_trans.
    assert (ev1 : Aeval_t (_ !-> 0) (_ !-> 0) [inr (C, 1);inr (B, 1)] <{B + 1}> = 2).
    { unfold Aeval_t. simpl. reflexivity. }
  rewrite <- ev1. apply CGAsgn_step.
  eapply Relation_Operators.rtn1_trans.
    assert (ev2: Aeval_t (_ !-> 0) (_ !-> 0) [inr (C, 1)] C = 1).
    { unfold Aeval_t. simpl. rewrite update_eq. reflexivity. }
  rewrite <- ev2. apply CLAsgn_step.
  eapply Relation_Operators.rtn1_trans with (y := (<{proc(A){foo_body}(Y + 1) ; Y :=G 0}>, [])).
    assert (ev3 : Aeval_t (_ !-> 0) (_ !-> 0) [] <{Y + 1}> = 1). {
      unfold Aeval_t. reflexivity. }
    assert (step3: Cstep (_ !-> 0) (_ !-> 0) (<{proc(A){foo_body}(Y + 1) ; Y :=G 0}>, [])
                     (SSeq (Stmt_sub foo_body A C) <{Y :=G 0}>, [inr (C, 1)])).
    { rewrite <- ev3. eapply CProc_step. }
  simpl in step3. repeat (rewrite Seq_Assoc in step3). rewrite <- ev3. eapply step3.
  eapply Relation_Operators.rtn1_trans.
  eapply CIfTrue_step with (b := <{ X <= 1 }>). unfold Beval_t. reflexivity.
  apply rtn1_refl.
Qed.


(** Correctness *)
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

(** Partial traces *)
(* an attempt to help formulate correct/complete-ness results for non-empty start traces*)

Example test_partial_Strace0 :=
  [ cond <{ X <= 1 }>;
    asgnL C <{ Y + 1 }>].

Example test_partial_Scomp :
  (<{ B :=L C;
      Y :=G B + 1;
      return;
      Y :=G 0 }>, test_partial_Strace0)
    ->* (<{ Y :=G 0 }>, test_Strace).
Proof.
  eapply Relation_Operators.rtn1_trans. apply SReturn_step.
  eapply Relation_Operators.rtn1_trans. apply SGAsgn_step.
  eapply Relation_Operators.rtn1_trans. apply SLAsgn_step.
  apply rtn1_refl.
Qed.

Example test_partial_Ccomp :
  @multi_Cstep (_ !-> 0) (C !-> 1 ; _ !-> 0)
    (<{ B :=L C;
        Y :=G B + 1;
        return;
        Y :=G 0 }>, [inr (C,1)])
    (<{ Y :=G 0 }>, test_Ctrace).
Proof.
  unfold test_Ctrace.
  eapply Relation_Operators.rtn1_trans. apply CReturn_step.
  eapply Relation_Operators.rtn1_trans.
    assert (ev1 : Aeval_t (_ !-> 0) (C !-> 1; _ !-> 0) [inr (C, 1);inr (B, 1)] <{B + 1}> = 2).
    { unfold Aeval_t. simpl. reflexivity. }
  rewrite <- ev1. apply CGAsgn_step.
  eapply Relation_Operators.rtn1_trans.
    assert (ev2: Aeval_t (_ !-> 0) (C !-> 1; _ !-> 0) [inr (C, 1)] C = 1).
    { unfold Aeval_t. simpl. rewrite update_eq. reflexivity. }
  rewrite <- ev2. apply CLAsgn_step.
  unfold Aeval_t. simpl. rewrite update_shadow.
  apply rtn1_refl.
Qed.

Example test_correct_partial_GVal :
  acc_GVal (_ !-> 0) (C !-> 1; _ !-> 0) [inr (B,1) ; inl (Y,2)]
  = GComp (_ !-> 0) (C !-> 1; _ !-> 0) (acc_GSubst_id [asgnL B C ; asgnG Y <{ B + 1 }>]).
Proof.
  extensionality x.
  unfold acc_GSubst_id. unfold GComp. simpl. unfold update.
  repeat (rewrite String.eqb_refl). destruct (Y =? x).
  - reflexivity.
  - apply apply_empty.
Qed.

Example test_complete_B : Beval (_ !-> 0) (_ !-> 0) (pc test_Strace) = true.
Proof. reflexivity. Qed.
