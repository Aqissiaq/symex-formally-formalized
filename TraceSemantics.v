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

(** How should a /trace/ keep track of the current stack frame? *)

(* keep the substitutions around? feels cheat-y *)
(* record "procedure call" in the trace? *)
(* inline the procedure body like in OOP.v? <-- easier implementation? *)
(* continuations like in LAGC? <-- probably better suited to parallelism *)

(** last two both seem reasonable, but lets try the easiest *)

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
    (<{ if b {s1}{s2} ; s}>, t) ->s (<{ s1 ; s }>, t :: cond  b)
| SIfFalse_step : forall b s1 s2 s t,
    (<{ if b {s1}{s2} ; s}>, t) ->s (<{ s2 ; s }>, t :: cond  (BNot b))
| SWhileTrue_step : forall b s s' t,
    (<{ while b {s} ; s' }>, t) ->s (<{ s ; while b {s} ; s' }>, t :: cond  b)
| SWhileFalse_step : forall b s s' t,
    (<{ while b {s} ; s' }>, t) ->s (s', t :: cond  (BNot b))
  where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40).

(** Concrete semantics *)

Definition Val : Type := nat.
Definition CTrace_step : Type := (GVar * Val) + (LVar * Val).

Definition CTrace := trace CTrace_step.

(* for now, let's just "cheat" in totality *)
Fixpoint acc_GVal (t:CTrace) : GVal :=
  match t with
  | Tnil => (_ !-> 0)
  | Tcons t' (inr _) => acc_GVal t'
  | Tcons t' (inl (x, e)) => update (acc_GVal t') x e
  end.

Fixpoint acc_LVal (t:CTrace) : LVal :=
  match t with
  | Tnil => (_ !-> 0)
  | Tcons t' (inl _) => acc_LVal t'
  | Tcons t' (inr (x, e)) => update (acc_LVal t') x e
  end.

Definition Aeval_t (t:CTrace) (e:Aexpr) : nat :=
  Aeval (acc_GVal t) (acc_LVal t) e.

Definition Beval_t (t:CTrace) (b:Bexpr) : bool :=
  Beval (acc_GVal t) (acc_LVal t) b.

Definition CConfig : Type := Stmt * CTrace.

Reserved Notation " c '=>c' c' " (at level 40).

Inductive Cstep : relation CConfig :=
| CGAsgn_step : forall x e s t,
    (<{ x :=G e ; s }>, t) =>c (s, t :: inl (x, Aeval_t t e))
| CLAsgn_step : forall x e s t,
    (<{ x :=L e ; s }>, t) =>c (s, t :: inr (x, Aeval_t t e))
| CProc_step : forall u body e s t y,
    (<{ proc(u){body}(e) ; s }>, t) =>c (SSeq (Stmt_sub body u y) s, t :: inr (y, Aeval_t t e))
| CReturn_step : forall s t,
    (<{ return ; s }>, t) =>c (s, t)
| CIfTrue_step : forall b s1 s2 s t,
    Beval_t t b = true ->
    (<{ if b {s1}{s2} ; s }>, t) =>c (<{s1 ; s}>, t)
| CIfFalse_step : forall b s1 s2 s t,
    Beval_t t b = false ->
    (<{ if b {s1}{s2} ; s }>, t) =>c (<{s2 ; s}>, t)
| CWhileTrue_step : forall b s s' t,
    Beval_t t b = true ->
    (<{ while b {s} ; s' }>, t) =>c (<{s ; while b {s} ; s'}>, t)
| CWhileFalse_step : forall b s s' t,
    Beval_t t b = false ->
    (<{ while b {s} ; s' }>, t) =>c (s', t)
  where " c '=>c' c' " := (Cstep c c').

Definition multi_Cstep := clos_refl_trans_n1 _ Cstep.
Notation " c '=>*' c' " := (multi_Cstep c c') (at level 40).

(** an aside with examples to verify semantics *)

Definition X : GVar := "X".
Definition Y : LVar := "Y".
Definition U : LVar := "U".

Example test_program : Stmt :=
  <{proc(U){ U :=L U + 1;
              X :=G U + 2;
              return}
       (X + 1);
     X :=G 0}>.

Lemma test_body_subst :
    <{ Y :=L Y + 1;
       X :=G Y + 2;
       return}>
    = Stmt_sub <{ U :=L U + 1;
                  X :=G U + 2;
                  return}>
        U Y.
Proof. simpl. rewrite L_single_update. reflexivity. Qed.

(* not sure how to elegantly incorporate this assumption without semantics *)
Lemma seq_assoc : forall s1 s2 s3,
    <{(s1; s2); s3}> = <{s1 ; (s2 ; s3)}>. Admitted.

Example Stest_trace : (test_program, [])
                        ->* (<{X :=G 0}>,
                                [inr (Y, <{X + 1}>);
                                  inr (Y, <{Y + 1}>);
                                  inl (inr (X, <{Y + 2}>))]).
Proof.
  eapply Relation_Operators.rtn1_trans. apply SReturn_step.
  eapply Relation_Operators.rtn1_trans. apply SGAsgn_step.
  eapply Relation_Operators.rtn1_trans. apply SLAsgn_step.
  eapply Relation_Operators.rtn1_trans.
  assert (<{ Y :=L Y + 1; X :=G Y + 2; return; X :=G 0 }> = <{ (Y :=L Y + 1; X :=G Y + 2; return); X :=G 0 }>). {
    repeat (rewrite seq_assoc). reflexivity. }
  rewrite H. rewrite test_body_subst. apply SProc_step.
  exact [].
  apply rtn1_refl.
Qed.

Example Ctest_trace : (test_program, [])
                        =>* (<{X :=G 0}>,
                                [inr (Y, 1) ;
                                  inr (Y, 2);
                                 inl (X, 4)]).
Proof.
  eapply Relation_Operators.rtn1_trans. apply CReturn_step.
  assert (step1 : (test_program, []) =>c (<{Y :=L Y + 1; X :=G Y + 2; return ; X :=G 0}>, [inr (Y, 1)])).
  {assert (<{ Y :=L Y + 1; X :=G Y + 2; return; X :=G 0 }> = <{ (Y :=L Y + 1; X :=G Y + 2; return); X :=G 0 }>). {
    repeat (rewrite seq_assoc). reflexivity. }
    rewrite H. rewrite test_body_subst. apply CProc_step. }
  assert (step2 : (<{Y :=L Y + 1; X :=G Y + 2; return ; X :=G 0}>, [inr (Y, 1)])
          =>c (<{ X :=G Y + 2; return; X :=G 0}>, [inr (Y,1) ; inr (Y, 2)])).
  { apply CLAsgn_step. }
  assert (step3 : (<{ X :=G Y + 2; return; X :=G 0}>, [inr (Y,1) ; inr (Y, 2)])
          =>c (<{return; X :=G 0}>, [inr (Y,1) ; inr (Y, 2) ; inl (X, 4)])).
  { apply CGAsgn_step. }
  eapply Relation_Operators.rtn1_trans. apply step3.
  eapply Relation_Operators.rtn1_trans. apply step2.
  eapply Relation_Operators.rtn1_trans. apply step1.
  apply rtn1_refl.
Qed.

(** Correctness *)

Fixpoint pc (t:STrace) : Bexpr :=
  match t with
  | [] => BTrue
  | t' :: inr _ => pc t'
  | t' :: inl (inr _) => pc t'
  | t' :: inl (inl p) => BAnd p (pc t')
  end.

(*Cheated totality again*)
Fixpoint acc_GSubst (t:STrace) : GSub :=
  match t with
  | [] => (_ !-> 0) (* this needs to be 0 to work with valuations*)
  | t' :: inl (inr (x, e)) => update (acc_GSubst t') x (Aapply (acc_GSubst t') (acc_LSubst t') e)
  | t' :: _ => acc_GSubst t'
  end
with acc_LSubst (t:STrace) : LSub :=
  match t with
  | [] => (_ !-> 0) (* this needs to be 0 to work with valuations*)
  | t' :: inr (x, e) => update (acc_LSubst t') x (Aapply (acc_GSubst t') (acc_LSubst t') e)
  | t' :: _ => acc_LSubst t'
  end.

Theorem correctness : forall t G0 L0,
    Beval G0 L0 (pc t) = true ->
    exists t',
      acc_GVal t' = GComp G0 L0 (acc_GSubst t)
      /\ acc_LVal t' = LComp G0 L0 (acc_LSubst t).
Proof.
  intros. induction t.
  - exists []. split; reflexivity.
  - dependent destruction a; try (dependent destruction s); try (dependent destruction p).
    (* branching *)
    + inversion H; subst. apply andb_true_iff in H1. destruct H1.
      destruct (IHt H1) as [t' IH]. exists t'. simpl. assumption.
    (* global assignment *)
    + inversion H; subst. destruct (IHt H1) as [t' [IHG IHL]].
      exists (t' :: inl (g, Aeval_t t' a)). split.
      * simpl. rewrite Gasgn_sound. rewrite eval_comp.
        rewrite <- IHG. rewrite <- IHL. unfold Aeval_t. reflexivity.
      * simpl. assumption.
    (* local assignment *)
    + inversion H; subst. destruct (IHt H1) as [t' [IHG IHL]].
      exists (t' :: inr (l, Aeval_t t' a)). split.
      * simpl. assumption.
      * simpl. rewrite Lasgn_sound. rewrite eval_comp.
        rewrite <- IHG. rewrite <- IHL. unfold Aeval_t. reflexivity.
Qed.

Ltac splits := repeat (try split).

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

Theorem completeness : forall (t:CTrace) G0 L0,
  exists (t':STrace), Beval G0 L0 (pc t') = true
                 /\ GComp G0 L0 (acc_GSubst t') = acc_GVal t
                 /\ LComp G0 L0 (acc_LSubst t') = acc_LVal t.
Proof.
  intros. induction t.
  - exists []. splits.
  - dependent destruction a; destruct p.
    + destruct IHt as [t' [IHpc [IHG IHL]]].
      exists (t' :: asgnG g (AConst v)). splits; simpl.
      * assumption.
      * simpl. rewrite <- IHG. rewrite Gcomp_update_comm. reflexivity.
      * assumption.
    + destruct IHt as [t' [IHpc [IHG IHL]]].
      exists (t' :: asgnL l (AConst v)). splits; simpl.
      * assumption.
      * assumption.
      * simpl. rewrite Lcomp_update_comm. rewrite <- IHL. reflexivity.
Qed.
