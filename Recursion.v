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

(*... actually I need to redo everything to account for local/global separation*)
Definition LVar := string.
Definition GVar := string.

Inductive Aexpr : Type :=
| AConst (n:nat)
| AGVar (x:GVar)
| ALVar (x:LVar)
| APlus (a1 a2:Aexpr).

Coercion AConst : nat >-> Aexpr.

Inductive Bexpr : Type :=
| BTrue
| BFalse
| BNot (b:Bexpr)
| BAnd (b1 b2:Bexpr)
| BLeq (a1 a2:Aexpr).

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 70, no associativity).
Notation "x <= y"   := (BLeq x y) (in custom com at level 70, no associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).

Open Scope com_scope.

Definition update {E:Type} (s: string -> E) (x:string) (e:E) : string -> E :=
  fun y => if String.eqb x y then e else s x.

Notation "x '!->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).

Definition empty_map {A:Type} (x:A) : string -> A := fun _ => x.
Notation "'_' '!->' v" := (empty_map v) (at level 100, right associativity).

(* substitions map to (Arithmetic) expressions*)
Definition LSub := LVar -> Aexpr.
Definition GSub := GVar -> Aexpr.

Definition Gid_sub : GVar -> Aexpr := fun x => AGVar x.
Definition Lid_sub : LVar -> Aexpr := fun x => ALVar x.

Fixpoint Aapply (s:GVar -> Aexpr) (t:LVar -> Aexpr) (e:Aexpr) : Aexpr :=
  match e with
  | AConst n => AConst n
  | AGVar x => s x
  | ALVar x => t x
  | APlus a1 a2 => APlus (Aapply s t a1) (Aapply s t a2)
  end.

Fixpoint Bapply  (s:GVar -> Aexpr) (t:LVar -> Aexpr) (e:Bexpr) : Bexpr :=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b => BNot (Bapply s t b)
  | BAnd b1 b2 => BAnd (Bapply s t b1) (Bapply s t b2)
  | BLeq a1 a2 => BLeq (Aapply s t a1) (Aapply s t a2)
  end.

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

Definition Sstack := list (LSub * Stmt).

Open Scope list_scope.

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
    ((t, <{ if b {s1} {s2} ; s }>) :: D, sig, phi) ->s ((t, <{ s1 ; s }>) :: D, sig, BAnd phi (Bapply sig t b))
| SIfFalse_step : forall t b s1 s2 s D sig phi,
    ((t, <{ if b {s1} {s2} ; s }>) :: D, sig, phi) ->s ((t, <{ s2 ; s }>) :: D, sig, BAnd phi (BNot (Bapply sig t b)))
| SWhileTrue_step : forall t b s s' D sig phi,
    ((t, <{ while b {s} ; s' }>) :: D, sig, phi) ->s ((t, <{ s ; while b {s} ; s' }>) :: D, sig, BAnd phi (Bapply sig t b))
| SWhileFalse_step : forall t b s s' D sig phi,
    ((t, <{ while b {s} ; s' }>) :: D, sig, phi) ->s ((t, s') :: D, sig, BAnd phi (BNot (Bapply sig t b)))
  where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40).

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

Definition GVal : Type := GVar -> nat.
Definition LVal : Type := LVar -> nat.

Definition LVal_e : LVal := fun _ => 0.
Definition GVal_e : GVal := fun _ => 0.

Fixpoint Aeval (G:GVal) (L:LVal) (e:Aexpr) : nat :=
  match e with
  | AConst n => n
  | AGVar x => G x
  | ALVar x => L x
  | APlus a1 a2 => (Aeval G L a1) + (Aeval G L a2)
  end.

Fixpoint Beval (G:GVal) (L:LVal) (e:Bexpr) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BNot b => negb (Beval G L b)
  | BAnd b1 b2 => (Beval G L b1) && (Beval G L b2)
  | BLeq a1 a2 => (Aeval G L a1) <=? (Aeval G L a2)
  end.

(** We can update a valuation with a substitution by composition *)

Fixpoint Aeval_comp (G:GVal) (L:LVal) (s:GVar -> Aexpr) (t:LVar -> Aexpr) (e:Aexpr) : nat :=
  match e with
  | AConst n => n
  | AGVar x => Aeval G L (s x)
  | ALVar x => Aeval G L (t x)
  | APlus a1 a2 => (Aeval_comp G L s t a1) + (Aeval_comp G L s t a2)
  end.

Fixpoint Beval_comp (G:GVal) (L:LVal) (s:GVar -> Aexpr) (t:LVar -> Aexpr) (e:Bexpr) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BNot b => negb (Beval_comp G L s t b)
  | BAnd b1 b2 => (Beval_comp G L s t b1) && (Beval_comp G L s t b2)
  | BLeq a1 a2 => (Aeval_comp G L s t a1) <=? (Aeval_comp G L s t a2)
  end.

Definition GComp (G:GVal) (L:LVal) (s:GVar -> Aexpr) : GVal :=
  fun x => Aeval G L (s x).
Definition LComp (G:GVal) (L:LVal) (t:LVar -> Aexpr) : LVal :=
  fun x => Aeval G L (t x).

Lemma eval_comp : forall G L s t e,
    Aeval_comp G L s t e = Aeval (GComp G L s) (LComp G L t) e.
Proof.
  induction e; simpl;
   try (rewrite IHe1; rewrite IHe2);
   try reflexivity.
Qed.

Lemma eval_compB : forall G L s t e,
    Beval_comp G L s t e = Beval (GComp G L s) (LComp G L t) e.
Proof.
  induction e; simpl;
   try (rewrite IHe);
   try (rewrite IHe1; rewrite IHe2);
   repeat (rewrite eval_comp);
   try reflexivity.
Qed.

(** might need some substitution / composition / asgn_sound lemmas **)

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
           * eapply IHclos_refl_trans_n1 with (phi := phi0); try reflexivity.
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
