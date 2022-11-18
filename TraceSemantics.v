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
  | t' :: inl (inr (x, e)) => update (acc_GSubst G L t') x (Aapply (acc_GSubst G L t') (acc_LSubst G L t') e)
  | t' :: _ => acc_GSubst G L t'
  end
with acc_LSubst (G:GSub) (L:LSub) (t:STrace) : LSub :=
  match t with
  | [] => L
  | t' :: inr (x, e) => update (acc_LSubst G L t') x (Aapply (acc_GSubst G L t') (acc_LSubst G L t') e)
  | t' :: _ => acc_LSubst G L t'
  end.

Definition Aapply_t : STrace -> Aexpr -> Aexpr :=
fun t e => Aapply (acc_GSubst Gid_sub Lid_sub t) (acc_LSubst Gid_sub Lid_sub t) e.

Definition Bapply_t : STrace -> Bexpr -> Bexpr :=
fun t e => Bapply (acc_GSubst Gid_sub Lid_sub t) (acc_LSubst Gid_sub Lid_sub t) e.

Definition SConfig : Type := Stmt * STrace.

Reserved Notation " c '->s' c' " (at level 40).
Inductive Sstep : relation SConfig  :=
| SGAsgn_step : forall x e s t,
    (<{ x :=G e ; s }>, t) ->s (s, (t :: asgnG x (Aapply_t t e)))
| SLAsgn_step : forall x e s t,
    (<{ x :=L e ; s }>, t) ->s (s, t :: asgnL x (Aapply_t t e))
| SProc_step : forall (t:STrace) u y body e s t,
    (* "y fresh", somehow *)
    (<{ proc(u){body}(e) ; s }>, t) ->s (SSeq (Stmt_sub body u y) s, t :: asgnL y (Aapply_t t e))
| SReturn_step : forall s t,
    (<{ return ; s }>, t) ->s (s, t)
| SIfTrue_step : forall b s1 s2 s t,
    (<{ if b {s1}{s2} ; s}>, t) ->s (<{ s1 ; s }>, t :: cond  (Bapply_t t b))
| SIfFalse_step : forall b s1 s2 s t,
    (<{ if b {s1}{s2} ; s}>, t) ->s (<{ s2 ; s }>, t :: cond  (BNot (Bapply_t t b)))
| SWhileTrue_step : forall b s s' t,
    (<{ while b {s} ; s' }>, t) ->s (<{ s ; while b {s} ; s' }>, t :: cond  (Bapply_t t b))
| SWhileFalse_step : forall b s s' t,
    (<{ while b {s} ; s' }>, t) ->s (s', t :: cond  (BNot (Bapply_t t b)))
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
  | Tcons t' (inl (x, e)) => let G' := acc_GVal G0 L0 t' in
                            let L' := acc_LVal G0 L0 t' in update G' x (Aeval G' L' e)
  end
with acc_LVal (G0:GVal) (L0:LVal) (t:CTrace) : LVal :=
  match t with
  | Tnil => L0
  | Tcons t' (inl _) => acc_LVal G0 L0 t'
  | Tcons t' (inr (x, e)) => let G' := acc_GVal G0 L0 t' in
                            let L' := acc_LVal G0 L0 t' in update L' x (Aeval G' L' e)
  end.

Definition Aeval_t (G0:GVal) (L0:LVal) (t:CTrace) (e:Aexpr) : nat :=
  Aeval (acc_GVal G0 L0 t) (acc_LVal G0 L0 t) e.

Definition Beval_t (G0:GVal) (L0:LVal) (t:CTrace) (b:Bexpr) : bool :=
  Beval (acc_GVal G0 L0 t) (acc_LVal G0 L0 t) b.

Definition CConfig : Type := Stmt * CTrace.

Reserved Notation " c '=>c' c' " (at level 40).

Inductive Cstep : relation CConfig :=
| CGAsgn_step : forall x e s t G0 L0 v,
    Aeval_t G0 L0 t e = v ->
    (<{ x :=G e ; s }>, t) =>c (s, t :: inl (x, v))
| CLAsgn_step : forall x e s t G0 L0 v,
    Aeval_t G0 L0 t e = v ->
    (<{ x :=L e ; s }>, t) =>c (s, t :: inr (x, v))
| CProc_step : forall u body e s s' t y G0 L0 v,
    (* y fresh *)
    Aeval_t G0 L0 t e = v ->
    Stmt_sub body u y = s ->
    (<{ proc(u){body}(e) ; s' }>, t) =>c (<{s ; s'}>, t :: inr (y, v))
| CReturn_step : forall s t,
    (<{ return ; s }>, t) =>c (s, t)
| CIfTrue_step : forall b s1 s2 s t G0 L0,
    Beval_t G0 L0 t b = true ->
    (<{ if b {s1}{s2} ; s }>, t) =>c (<{s1 ; s}>, t)
| CIfFalse_step : forall b s1 s2 s t G0 L0,
    Beval_t G0 L0 t b = false ->
    (<{ if b {s1}{s2} ; s }>, t) =>c (<{s2 ; s}>, t)
| CWhileTrue_step : forall b s s' t G0 L0,
    Beval_t G0 L0 t b = true ->
    (<{ while b {s} ; s' }>, t) =>c (<{s ; while b {s} ; s'}>, t)
| CWhileFalse_step : forall b s s' t G0 L0,
    Beval_t G0 L0 t b = false ->
    (<{ while b {s} ; s' }>, t) =>c (s', t)
  where " c '=>c' c' " := (Cstep c c').

Definition multi_Cstep := clos_refl_trans_n1 _ Cstep.
Notation " c '=>*' c' " := (multi_Cstep c c') (at level 40).

(** an aside with examples to verify semantics *)

Definition X : GVar := "X".
Definition Y : LVar := "Y".
Definition U : LVar := "U".

(* not sure how to elegantly incorporate this assumption without semantics *)
Axiom Seq_Assoc : forall s1 s2 s3,
    <{ (s1 ; s2) ; s3 }> = <{ s1 ; s2 ; s3 }>.

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


Example Stest_trace : (test_program, [])
                        ->* (<{X :=G 0}>,
                                [inr (Y, <{X + 1}>);
                                  inr (Y, <{(X + 1) + 1}>);
                                  inl (inr (X, <{(X + 1) + 1 + 2}>))]).
Proof.
  assert (step1 : (test_program, [])
                  ->s (<{ (Y :=L Y + 1; X :=G Y + 2; return); X :=G 0 }>, [inr (Y, <{ X + 1 }>)])).
  { rewrite test_body_subst. apply SProc_step. exact []. }
  assert (step2 : (<{ Y :=L Y + 1; X :=G Y + 2; return; X :=G 0 }>, [inr (Y, <{ X + 1 }>)])
                  ->s (<{ X :=G Y + 2; return; X :=G 0 }>, [inr (Y, <{ X + 1 }>)] :: inr (Y, <{ (X + 1) + 1 }>))).
   { apply SLAsgn_step. }
   assert (step3 : (<{ X :=G Y + 2; return; X :=G 0 }>, [inr (Y, <{ X + 1 }>) ; inr (Y, <{ (X + 1) + 1 }>)])
          ->s (<{ return; X :=G 0 }>, [inr (Y, <{ X + 1 }>) ; inr (Y, <{ (X + 1) + 1 }>)] :: inl (inr (X, <{ ((X + 1) + 1) + 2 }>)))).
   { apply SGAsgn_step. }
   eapply Relation_Operators.rtn1_trans. apply SReturn_step.
   eapply Relation_Operators.rtn1_trans. apply step3.
   eapply Relation_Operators.rtn1_trans. apply step2.
   assert (assoc : <{ (Y :=L Y + 1; X :=G Y + 2; return); X :=G 0 }> = <{ Y :=L Y + 1; X :=G Y + 2; return; X :=G 0 }>).
   { repeat (rewrite Seq_Assoc). reflexivity. }
   eapply Relation_Operators.rtn1_trans. rewrite <- assoc. apply step1.
   apply rtn1_refl.
Qed.

Example Ctest_trace : (test_program, [])
                        =>*  (<{X :=G 0}>,
                                 [inr (Y, 1) ;
                                   inr (Y, 2);
                                   inl (X, 4)]).
Proof.
  assert (step1 : (test_program, [])
                  =>c (<{ (Y :=L Y + 1; X :=G Y + 2; return); X :=G 0 }>, [inr (Y, 1)])).
  { rewrite test_body_subst. apply CProc_step with (G0 := (_ !-> 0)) (L0 := (_ !-> 0)); reflexivity. }
  assert (step2 : (<{ Y :=L Y + 1; X :=G Y + 2; return; X :=G 0 }>, [inr (Y, 1)])
                  =>c (<{ X :=G Y + 2; return; X :=G 0 }>, [inr (Y, 1)] :: inr (Y, 2))).
   { apply CLAsgn_step with (G0 := (_ !-> 0)) (L0 := (_ !-> 0)); reflexivity. }
   assert (step3 : (<{ X :=G Y + 2; return; X :=G 0 }>, [inr (Y, 1) ; inr (Y, 2)])
          =>c (<{ return; X :=G 0 }>, [inr (Y, 1) ; inr (Y, 2)] :: inl (X, 4))).
   { apply CGAsgn_step with (G0 := (_ !-> 0)) (L0 := (_ !-> 0)); reflexivity. }
   eapply Relation_Operators.rtn1_trans. apply CReturn_step.
   eapply Relation_Operators.rtn1_trans. apply step3.
   eapply Relation_Operators.rtn1_trans. apply step2.
   assert (assoc : <{ (Y :=L Y + 1; X :=G Y + 2; return); X :=G 0 }> = <{ Y :=L Y + 1; X :=G Y + 2; return; X :=G 0 }>).
   { repeat (rewrite Seq_Assoc). reflexivity. }
   eapply Relation_Operators.rtn1_trans. rewrite <- assoc. apply step1.
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

Ltac splits := repeat (try split).

Theorem correctness : forall s s' t G0 L0,
    (s, []) ->* (s', t) ->
    Beval G0 L0 (pc t) = true ->
    exists t', (s, []) =>* (s', t')
              /\ acc_GVal G0 L0 t' = GComp G0 L0 (acc_GSubst Gid_sub Lid_sub t)
              /\ acc_LVal G0 L0 t' = LComp G0 L0 (acc_LSubst Gid_sub Lid_sub t).
Proof.
  intros. dependent induction H.
  - exists []. splits. apply rtn1_refl.
  - dependent destruction H.
    + (* global assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=G e ; s'}> t0) as [t' [comp [IHG IHL]]];
        try reflexivity;
        try assumption.
      exists (t' :: inl (x, Aeval_t (acc_GVal G0 L0 t') (acc_LVal G0 L0 t') t' e)). splits.
      * eapply Relation_Operators.rtn1_trans. apply CGAsgn_step with (e := e) (G0 := acc_GVal G0 L0 t') (L0 := acc_LVal G0 L0 t').
        reflexivity. assumption.
      * simpl. unfold Aeval_t. rewrite Gasgn_sound. rewrite eval_comp. rewrite <- IHG. rewrite <- IHL.
      * simpl. rewrite IHL. reflexivity.


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
