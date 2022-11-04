(** * 3. Recursion *)

(** We extend our basic programming language with procedures. We assume a finite set of Var of
program variables x , y, u, . . . to be partitioned in global variables GVar and local variables LVar , without name
clashes between them. Global variables are visible within the entire program while local variables are used as
formal parameters of the procedure declarations, and their scope lie within the procedure body itself.

In the formalization we let both GVar and LVar be string *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Program.   (* for `dependent induction` *)
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)
From Coq Require Import Relations.
From Coq Require Import Lists.List.
Import ListNotations.

From SymEx Require Import Expr.
Import ProcedureExpr.

From SymEx Require Import Maps.
Import ProcedureMaps.

Inductive Stmt : Type :=
| SGAsgn (x:GVar) (e:Aexpr)
| SLAsgn (u:LVar) (e:Aexpr)
| SProc (P:Proc) (e:Aexpr) (*just one parameter for simplicity*)
| SSeq (s1 s2:Stmt)
| SIf (b:Bexpr) (s1 s2:Stmt)
| SWhile (b:Bexpr) (s:Stmt)
| SReturn
  with Proc : Type :=
    | PDec (u:LVar) (s':Stmt).


Notation "x :=G y"  :=
         (SGAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x :=L y"  :=
         (SLAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (SSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "P '(' e ')'" := (SProc P e) (in custom com at level 85) : com_scope.
Notation "'if' x '{' y '}' '{' z '}'" :=
         (SIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x '{' y '}'" :=
         (SWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.
Notation "'return'" := SReturn (in custom com at level 80) : com_scope.

Notation "'proc' '(' u ')' '{' b '}'"  :=
         (PDec u b)
            (in custom com at level 0, u constr at level 0,
             b at level 85, no associativity) : com_scope.

(** Symbolic semantics *)
Open Scope com_scope.
Open Scope list_scope.

Definition Sstack := list (LSub * Stmt).

Definition SConfig : Type := Sstack * GSub * Bexpr.

Reserved Notation " c '->s' c' " (at level 40).

Inductive Sstep : relation SConfig :=
| SGAsgn_step : forall x e S t D sig phi,
    ((t, <{ x :=G e ; S }>) :: D, sig, phi) ->s ((t, S) :: D, update sig x (Aapply sig t e), phi)
| SLAsgn_step : forall x e S t D sig phi,
    ((t, <{ x :=L e ; S }>) :: D, sig, phi) ->s ((update t x (Aapply sig t e), S) :: D, sig, phi)
| SProc_step : forall t u body e S D sig phi,
    ((t, <{ proc(u){body}(e) ; S }>) :: D, sig, phi)
      (* we choose to extend the current scope *)
    ->s ((update t u (Aapply sig t e), body) :: (t , S) :: D , sig, phi)
| SReturn_step : forall t D sig phi,
    ((t, <{ return }>) :: D, sig, phi) ->s ( D , sig, phi)
| SIfTrue_step : forall t b s1 s2 s D sig phi,
    ((t, <{ if b {s1} {s2} ; s }>) :: D, sig, phi)
      ->s ((t, <{ s1 ; s }>) :: D, sig, BAnd phi (Bapply sig t b))
| SIfFalse_step : forall t b s1 s2 s D sig phi,
    ((t, <{ if b {s1} {s2} ; s }>) :: D, sig, phi)
      ->s ((t, <{ s2 ; s }>) :: D, sig, BAnd phi (BNot (Bapply sig t b)))
| SWhileTrue_step : forall t b s s' D sig phi,
    ((t, <{ while b {s} ; s' }>) :: D, sig, phi)
      ->s ((t, <{ s ; while b {s} ; s' }>) :: D, sig, BAnd phi (Bapply sig t b))
| SWhileFalse_step : forall t b s s' D sig phi,
    ((t, <{ while b {s} ; s' }>) :: D, sig, phi)
      ->s ((t, s') :: D, sig, BAnd phi (BNot (Bapply sig t b)))
  where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40).

(* this is an unnecessary aside since GVar and LVar are disjoint by construction *)
Fixpoint Ano_local (e:Aexpr) : bool :=
  match e with
  | AConst n => true
  | AGVar x => true
  | ALVar x => false
  | APlus a1 a2 => Ano_local a1 && Ano_local a2
  end.

Fixpoint Bno_local (phi:Bexpr) : bool :=
  match phi with
  | BTrue => true
  | BFalse => true
  | BNot b => Bno_local b
  | BAnd b1 b2 => Bno_local b1 && Bno_local b2
  | BLeq a1 a2 => Ano_local a1 && Ano_local a2
  end.

Fixpoint Sno_local (s:Stmt) : bool :=
  match s with
  | SGAsgn _ a => Ano_local a
  | SLAsgn _ _ => false
  | SSeq s1 s2 => Sno_local s1 && Sno_local s2
  | SIf b s1 s2 => Bno_local b && Sno_local s1 && Sno_local s2
  | SWhile b s => Bno_local b && Sno_local s
  | _ => true
  end.

Definition is_initial (s:Stmt) := Sno_local s = true.

(** Concrete semantics *)

Definition Cstack := list (LVal * Stmt).
Definition CConfig : Type := Cstack * GVal.

Fixpoint EvalStack (G:GVal) (L:LVal) (s:Sstack) : Cstack :=
  match s with
  | [] => []
  | (t, s) :: ss => (LComp G L t, s) :: EvalStack G L ss
  end.

Lemma stack_eval : forall G L s t D,
    (LComp G L t, s) :: EvalStack G L D = EvalStack G L ((t, s) :: D).
Proof. induction D; reflexivity. Qed.

Lemma stack_eval_empty : forall G L D,
    [] = EvalStack G L D <-> [] = D.
Proof.
  split; intros.
  - destruct D.
    + reflexivity.
    + destruct p. simpl in H.
      apply nil_cons in H. contradiction.
  - rewrite <- H. reflexivity.
Qed.

Reserved Notation " c '=>c' c' " (at level 40).

Inductive Cstep : relation CConfig :=
| CGAsgn_step : forall L x e s C G,
    ((L,  <{ x :=G e ; s }>) :: C, G) =>c ((L, s) :: C, update G x (Aeval G L e))
| CLAsgn_step : forall L x e s C G,
    ((L,  <{ x :=L e ; s }>) :: C, G) =>c ((update L x (Aeval G L e), s) :: C, G)
| CProc_step : forall L u body e s C G,
    ((L, <{ proc(u){body}(e) ; s }>) :: C, G)
  =>c ((update L u (Aeval G L e), body) :: (L, s) :: C, G)
| CProc_return : forall L C G,
    ((L, <{return}>) :: C, G) =>c (C, G)
| CIfTrue_step : forall L b s1 s2 s C G,
    Beval G L b = true ->
    ((L, <{ if b {s1}{s2} ; s }>) :: C, G) =>c ((L, <{s1 ; s}>) :: C, G)
| CIfFalse_step : forall L b s1 s2 s C G,
    Beval G L b = false ->
    ((L, <{ if b {s1}{s2} ; s }>) :: C, G) =>c ((L, <{s2 ; s}>) :: C, G)
| CWhileTrue_step : forall L b s s' C G,
    Beval G L b = true ->
    ((L, <{ while b {s} ; s' }>) :: C, G) =>c ((L, <{s ; while b {s} ; s'}>) :: C, G)
| CWhileFalse_step : forall L b s s' C G,
    Beval G L b = false ->
    ((L, <{ while b {s} ; s' }>) :: C, G) =>c ((L, s') :: C, G)
  where " c '=>c' c' " := (Cstep c c').

Definition multi_Cstep := clos_refl_trans_n1 _ Cstep.
Notation " c '=>*' c' " := (multi_Cstep c c') (at level 40).

Lemma LComp_id : forall G L,
    LComp G L Lid_sub = L.
Proof. intros. extensionality x. unfold LComp. reflexivity. Qed.

Lemma GComp_id : forall G L,
    GComp G L Gid_sub = G.
Proof. intros. extensionality x. unfold GComp. reflexivity. Qed.

Lemma eval_comp : forall G L s t e,
    Aeval_comp G L s t e = Aeval (GComp G L s) (LComp G L t) e.
Proof.
  induction e; simpl;
   try (rewrite IHe1; rewrite IHe2);
   reflexivity.
Qed.

Lemma eval_compB : forall G L s t e,
    Beval_comp G L s t e = Beval (GComp G L s) (LComp G L t) e.
Proof.
  induction e; simpl;
   try (rewrite IHe);
   try (rewrite IHe1; rewrite IHe2);
   repeat (rewrite eval_comp);
   reflexivity.
Qed.

Lemma Comp_sub : forall G L s t e,
    Aeval_comp G L s t e = Aeval G L (Aapply s t e).
Proof.
  induction e; simpl; try reflexivity.
   try (rewrite IHe1; rewrite IHe2). reflexivity.
Qed.

Lemma Comp_subB : forall G L s t e,
    Beval_comp G L s t e = Beval G L (Bapply s t e).
Proof.
  induction e; simpl;
  try (rewrite IHe);
   try (rewrite IHe1; rewrite IHe2);
   repeat (rewrite Comp_sub);
   reflexivity.
Qed.

(* Corollary 3.4 *)
Lemma Lasgn_sound : forall G L s t x e,
    LComp G L (update t x (Aapply s t e)) = update (LComp G L t) x (Aeval_comp G L s t e).
Proof.
  intros. extensionality y.
  unfold LComp. unfold update. destruct (x =? y)%string;
  try rewrite Comp_sub; reflexivity.
Qed.

Lemma Gasgn_sound : forall G L s t x e,
    GComp G L (update s x (Aapply s t e)) = update (GComp G L s) x (Aeval_comp G L s t e).
Proof.
  intros. extensionality y.
  unfold GComp. unfold update. destruct (x =? y)%string;
  try (rewrite Comp_sub); reflexivity.
Qed.

(* note: we turn out not to need the fact that s is initial *)
(* presumably because separation of local and global vars is enforced at the type level
 *)
Theorem correctness : forall s s' t D sig phi G L,
    ([(Lid_sub, s)], Gid_sub, BTrue) ->* ((t, s') :: D, sig, phi) ->
    Beval G L phi = true ->
    ([(L, s)], G) =>* ((LComp G L t, s') :: EvalStack G L D, GComp G L sig).
Proof.
  intros. dependent induction H.
  - rewrite LComp_id. rewrite GComp_id. apply rtn1_refl.
  - dependent destruction H.
    + eapply Relation_Operators.rtn1_trans.
      * rewrite Gasgn_sound. rewrite eval_comp. apply CGAsgn_step.
      * apply IHclos_refl_trans_n1 with (phi := phi); try assumption; reflexivity.
    + eapply Relation_Operators.rtn1_trans.
      * rewrite Lasgn_sound. rewrite eval_comp. apply CLAsgn_step.
      * apply IHclos_refl_trans_n1 with (phi := phi); try assumption; reflexivity.
    + eapply Relation_Operators.rtn1_trans.
      * rewrite Lasgn_sound. rewrite eval_comp. apply CProc_step.
      * apply IHclos_refl_trans_n1 with (phi := phi); try assumption; reflexivity.
    + eapply Relation_Operators.rtn1_trans.
      * apply CProc_return.
      * rewrite stack_eval. apply IHclos_refl_trans_n1 with (phi := phi); try assumption; reflexivity.
    + eapply Relation_Operators.rtn1_trans.
           * apply CIfTrue_step. inversion H1. rewrite H2.
             apply andb_true_iff in H2. auto. destruct H2. rewrite <- eval_compB. rewrite Comp_subB. apply H2.
           * eapply IHclos_refl_trans_n1; try reflexivity.
             apply andb_true_iff in H1. destruct H1. apply H.
    + eapply Relation_Operators.rtn1_trans.
           * apply CIfFalse_step. inversion H1. apply andb_true_iff in H2. destruct H2.
             apply negb_true_iff in H2. rewrite <- eval_compB. rewrite Comp_subB. apply H2.
           * eapply IHclos_refl_trans_n1; try reflexivity.
             inversion H1. rewrite H2. apply andb_true_iff in H2. destruct H2. apply H.
         + eapply Relation_Operators.rtn1_trans.
           * apply CWhileTrue_step. inversion H1. rewrite H2.
             apply andb_true_iff in H2. destruct H2. rewrite <- eval_compB. rewrite Comp_subB. apply H2.
           * eapply IHclos_refl_trans_n1; try reflexivity. inversion H1. rewrite H2.
             apply andb_true_iff in H2. destruct H2. apply H.
         + eapply Relation_Operators.rtn1_trans.
           * apply CWhileFalse_step. inversion H1. apply andb_true_iff in H2. destruct H2.
             apply negb_true_iff in H2. rewrite <- eval_compB. rewrite Comp_subB. apply H2.
           * eapply IHclos_refl_trans_n1; try reflexivity. inversion H1. rewrite H2.
             apply andb_true_iff in H2. destruct H2. apply H.
Qed.

Ltac splits := repeat (try split).

(* automatically solves the steps that don't really care about processes *)
(* could incorporate more steps to solve all of them, but - like de Boer - I want to spell out the interesting cases *)
Ltac solve_cases IH :=
      destruct IH as [t [sig [phi [D [comp [stack [pc [gVal lVal]]]]]]]];
      eexists; eexists; eexists; eexists; splits;
       try (eapply Relation_Operators.rtn1_trans; [constructor | apply comp]);
       try (simpl; apply andb_true_iff; split);
       try (apply negb_true_iff);
       try (rewrite <- Comp_subB; rewrite eval_compB; rewrite <- gVal; rewrite <- lVal);
       try assumption;
       try reflexivity.

Theorem completeness : forall G G' L L' s s' C,
    ([(L, s)], G) =>* ((L', s') :: C, G') ->
    exists t sig phi D, ([(Lid_sub, s)], Gid_sub, BTrue) ->* ((t,s') :: D, sig, phi)
                 /\ C = EvalStack G L D
                 /\ Beval G L phi = true
                 /\ G' = GComp G L sig
                 /\ L' = LComp G L t.
Proof.
  intros. dependent induction H.
  - exists Lid_sub. exists Gid_sub. exists BTrue. exists []. splits; apply rtn1_refl.
  - dependent destruction H.
    + assert (IH : exists t sig phi D, ([(Lid_sub, s)], Gid_sub, BTrue) ->* ((t, <{ x :=G e ; s'}>) :: D, sig, phi)
                                  /\ C = EvalStack G L D
                                  /\ Beval G L phi = true
                                  /\ G0 = GComp G L sig
                                  /\ L' = LComp G L t)
      by (eapply IHclos_refl_trans_n1; reflexivity).
      destruct IH as [t [sig [phi [D [comp [stackV [pc [gVal lVal]]]]]]]].
      eexists. eexists. eexists. eexists. splits;
       try (eapply Relation_Operators.rtn1_trans; [apply SGAsgn_step | apply comp]);
       try (rewrite Gasgn_sound; rewrite eval_comp; rewrite gVal; rewrite lVal);
       try assumption;
       try reflexivity.
    + assert (IH : exists t sig phi D, ([(Lid_sub, s)], Gid_sub, BTrue) ->* ((t, <{ x :=L e ; s'}>) :: D, sig, phi)
                                  /\ C = EvalStack G L D
                                  /\ Beval G L phi = true
                                  /\ G' = GComp G L sig
                                  /\ L0 = LComp G L t)
      by (eapply IHclos_refl_trans_n1; reflexivity).
      destruct IH as [t [sig [phi [D [comp [stackV [pc [gVal lVal]]]]]]]].
      eexists. eexists. eexists. eexists. splits;
       try (eapply Relation_Operators.rtn1_trans; [apply SLAsgn_step | apply comp]);
       try (rewrite Lasgn_sound; rewrite eval_comp; rewrite gVal; rewrite lVal);
       try assumption;
       try reflexivity.
    + assert (IH : exists t sig phi D, ([(Lid_sub, s)], Gid_sub, BTrue) ->* ((t, <{ proc(u){s'}(e) ; s0}>) :: D, sig, phi)
                                  /\ C0 = EvalStack G L D
                                  /\ Beval G L phi = true
                                  /\ G' = GComp G L sig
                                  /\ L0 = LComp G L t)
      by (eapply IHclos_refl_trans_n1; reflexivity).
      destruct IH as [t [sig [phi [D [comp [stackV [pc [gVal lVal]]]]]]]].
      eexists. eexists. eexists. eexists. splits;
       try (eapply Relation_Operators.rtn1_trans; [apply SProc_step | apply comp]);
       try (rewrite stackV; rewrite <- stack_eval; rewrite lVal);
       try (rewrite Lasgn_sound; rewrite eval_comp; rewrite gVal; rewrite lVal);
       try assumption;
       reflexivity.
    + assert (IH : exists t sig phi D, ([(Lid_sub, s)], Gid_sub, BTrue) ->* ((t, <{ return }>) :: D, sig, phi)
                                  /\ (L', s') :: C = EvalStack G L D
                                  /\ Beval G L phi = true
                                  /\ G' = GComp G L sig
                                  /\ L0 = LComp G L t)
      by (eapply IHclos_refl_trans_n1; reflexivity).
      destruct IH as [t [sig [phi [D [comp [stackV [pc [gVal lVal]]]]]]]].
      destruct D.
        * simpl in stackV. symmetry in stackV. apply nil_cons in stackV. contradiction.
        * destruct p. exists l. exists sig. exists phi. exists D. splits;
           try (assumption);
           try (rewrite <- stack_eval in stackV; inversion stackV; reflexivity).
          eapply Relation_Operators.rtn1_trans; [
              apply SReturn_step
            | assert (s' = s0) by (rewrite <- stack_eval in stackV; inversion stackV; reflexivity);
              rewrite H; apply comp].
    + assert (IH : exists t sig phi D, ([(Lid_sub, s)], Gid_sub, BTrue) ->* ((t, <{ if b {s1}{s2} ; s0}>) :: D, sig, phi)
                                  /\ C = EvalStack G L D
                                  /\ Beval G L phi = true
                                  /\ G' = GComp G L sig
                                  /\ L' = LComp G L t)
      by (eapply IHclos_refl_trans_n1; reflexivity).
      solve_cases IH.
    + assert (IH : exists t sig phi D, ([(Lid_sub, s)], Gid_sub, BTrue) ->* ((t, <{ if b {s1}{s2} ; s0}>) :: D, sig, phi)
                                  /\ C = EvalStack G L D
                                  /\ Beval G L phi = true
                                  /\ G' = GComp G L sig
                                  /\ L' = LComp G L t)
      by (eapply IHclos_refl_trans_n1; reflexivity).
      solve_cases IH.
    + assert (IH : exists t sig phi D, ([(Lid_sub, s)], Gid_sub, BTrue) ->* ((t, <{ while b {s0} ; s'0 }>) :: D, sig, phi)
                                  /\ C = EvalStack G L D
                                  /\ Beval G L phi = true
                                  /\ G' = GComp G L sig
                                  /\ L' = LComp G L t)
      by (eapply IHclos_refl_trans_n1; reflexivity).
      solve_cases IH.
    + assert (IH : exists t sig phi D, ([(Lid_sub, s)], Gid_sub, BTrue) ->* ((t, <{ while b {s0} ; s'}>) :: D, sig, phi)
                                  /\ C = EvalStack G L D
                                  /\ Beval G L phi = true
                                  /\ G' = GComp G L sig
                                  /\ L' = LComp G L t)
      by (eapply IHclos_refl_trans_n1; reflexivity).
      solve_cases IH.
Qed.
