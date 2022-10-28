(** * 3. Recursion *)

(** We extend our basic programming language with procedures. We assume a finite set of Var of
program variables x , y, u, . . . to be partitioned in global variables GVar and local variables LVar , without name
clashes between them. Global variables are visible within the entire program while local variables are used as
formal parameters of the procedure declarations, and their scope lie within the procedure body itself.

In the formalization we let both GVar and LVar be string *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Datatypes.
From Coq Require Import Program.   (* for `dependent induction` *)
From Coq Require Import Relations.

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

Fixpoint Aapply (t:LVar -> Aexpr) (s:GVar -> Aexpr) (e:Aexpr) : Aexpr :=
  match e with
  | AConst n => AConst n
  | AGVar x => s x
  | ALVar x => t x
  | APlus a1 a2 => APlus (Aapply t s a1) (Aapply t s a2)
  end.

Fixpoint Bapply  (t:LVar -> Aexpr) (s:GVar -> Aexpr) (e:Bexpr) : Bexpr :=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b => BNot (Bapply t s b)
  | BAnd b1 b2 => BAnd (Bapply t s b1) (Bapply t s b2)
  | BLeq a1 a2 => BLeq (Aapply t s a1) (Aapply t s a2)
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

Notation "'proc(' u ')' '{' b '}'"  :=
         (PDec u b)
            (in custom com at level 0, u constr at level 0,
             b at level 85, no associativity) : com_scope.

Inductive Cstack : Type :=
| CSEmpty
| CSPush (clos: LSub * Stmt) (s: Cstack).

Notation "[ x ]" := (CSPush x CSEmpty) : com_scope.
Notation "[ x ; y ; .. ; z ]" := (CSPush x (CSPush y .. (CSPush z CSEmpty) ..)) : com_scope.

Example test (x y z: LSub * Stmt) : Cstack := [ x ; y ; z ].

Definition SConfig : Type := Cstack * GSub * Bexpr.

Reserved Notation " c '->s' c' " (at level 40).

Inductive Sstep : relation SConfig :=
| SGAsgn_step : forall x e S t D sig phi,
    ([(t, <{ x :=G e ; S }>) ; D], sig, phi) ->s ([(t, S) ; D], update sig x (Aapply t sig e), phi)
| SLAsgn_step : forall x e S t D sig phi,
    ([(t, <{ x :=L e ; S }>) ; D], sig, phi) ->s ([(update t x (Aapply t sig e), S) ; D], sig, phi)
| SProc_step : forall t u body e S D sig phi,
    ([(t, <{ proc(u){body}(e) ; S }>) ; D], sig, phi)
    ->s ([ ((u !-> (Aapply t sig e) ; Lid_sub), body) ; (t , S) ; D ], sig, phi)
| SReturn_step : forall t D sig phi,
    ([(t, <{ return }>) ; D], sig, phi) ->s ([ D ], sig, phi)
| SIfTrue_step : forall t b s1 s2 s D sig phi,
    ([(t, <{ if b {s1} {s2} ; s }>) ; D], sig, phi) ->s ([(t, <{ s1 ; s }>) ; D], sig, BAnd phi (Bapply t sig b))
| SIfFalse_step : forall t b s1 s2 s D sig phi,
    ([(t, <{ if b {s1} {s2} ; s }>) ; D], sig, phi) ->s ([(t, <{ s1 ; s }>) ; D], sig, BAnd phi (BNot (Bapply t sig b)))
| SWhileTrue_step : forall t b s s' D sig phi,
    ([(t, <{ while b {s} ; s' }>) ; D], sig, phi) ->s ([(t, <{ s ; while b {s} ; s' }>) ; D], sig, BAnd phi (Bapply t sig b))
| SWhileFalse_step : forall t b s s' D sig phi,
    ([(t, <{ while b {s} ; s' }>) ; D], sig, phi) ->s ([(t, s') ; D], sig, BAnd phi (BNot (Bapply t sig b)))
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

(* Proposition 3.2 *)
(* slightly clunky statement(s) to denote *non-empty* computation, but proof is immediate *)
Lemma no_local_in_computation : forall s t s' D sig phi c u x,
    ([(Lid_sub, s)], Gid_sub, BTrue) ->s c ->
    c ->* ([(t, s') ; D], sig, phi) ->
    Ano_local (t u) = true /\ Ano_local (sig x) = true.
Proof.
  intros. split; inversion H; subst.
Qed.

Lemma Bno_local_in_computation : forall s t s' D sig phi c b,
    ([(Lid_sub, s)], Gid_sub, BTrue) ->s c ->
    c ->* ([(t, s') ; D], sig, phi) ->
    Bno_local (Bapply t sig b) = true.
Proof.
  intros. inversion H; subst.
Qed.

(* more convenient statements, less convenient proofs *)
(* - c'est la vie *)
Lemma  no_local_in_computation' : forall s t s' D sig phi c u x,
    ([(Lid_sub, s)], Gid_sub, BTrue) ->* c ->
    c ->s ([(t, s') ; D], sig, phi) ->
    Ano_local (t u) = true /\ Ano_local (sig x) = true.
Proof.
  intros.
  unfold multi_Sstep in H.
  rewrite <- clos_rt_rtn1_iff in H. rewrite clos_rt_rt1n_iff in H.
  destruct H.
  - split; inversion H0; subst.
  - eapply no_local_in_computation.
    + apply H.
    + rewrite <- clos_rt_rt1n_iff in H1. rewrite clos_rt_rtn1_iff in H1.
      eapply Relation_Operators.rtn1_trans. apply H0. apply H1.
Qed.

Lemma Bno_local_in_computation' : forall s t s' D sig phi c b,
    ([(Lid_sub, s)], Gid_sub, BTrue) ->* c ->
    c ->s ([(t, s') ; D], sig, phi) ->
    Bno_local (Bapply t sig b) = true.
Proof.
  intros.
  unfold multi_Sstep in H.
  rewrite <- clos_rt_rtn1_iff in H. rewrite clos_rt_rt1n_iff in H.
  destruct H.
  - inversion H0; subst.
  - eapply Bno_local_in_computation.
    + apply H.
    + rewrite <- clos_rt_rt1n_iff in H1. rewrite clos_rt_rtn1_iff in H1.
      eapply Relation_Operators.rtn1_trans. apply H0. apply H1.
Qed.

Definition is_initial (s:Stmt) := Sno_local s = true.

(* Corollary 3.2 *)
Theorem no_local_in_pc : forall s s' t D sig phi,
    ([(Lid_sub, s)], Gid_sub, BTrue) ->* ([(t, s') ; D], sig, phi) ->
    is_initial s ->
    Bno_local phi = true.
Proof.
  intros. dependent induction H.
  inversion H; subst;
  try (simpl; apply andb_true_iff; split);
    try (eapply IHclos_refl_trans_n1; try reflexivity; assumption);
    try (eapply Bno_local_in_computation'; try apply H0; apply H).
Qed.
