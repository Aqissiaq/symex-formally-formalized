(** * 2. Basic Symbolic Execution *)

(** We introduce a formal model of symbolic execution for a basic programming
language with a statically fixed number of programming variables. A configuration of the symbolic transition
system consists of the program statement to be executed, a substitution, and a path condition. Correctness then
states that for every reachable symbolic configuration and state which satisfies the path condition, there exists a
corresponding concrete execution. Conversely, completeness states that for every concrete execution there exists
a corresponding symbolic configuration such that the initial state of the concrete execution satisfies the path
condition and its final state can be obtained as a composition of the initial state and the generated substitution.
 *)

(** This file contains a second take, trying to move more elegantly between symbolic and concrete states
 by being less general *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)
From Coq Require Import Relations.
From Coq Require Import Wellfounded.Transitive_Closure.

Inductive Aexpr : Type :=
| AConst (n:nat)
| AVar (x:string)
| APlus (a1 a2:Aexpr).

Inductive Bexpr : Type :=
| BTrue
| BFalse
| BNot (b:Bexpr)
| BAnd (b1 b2:Bexpr)
| BLeq (a1 a2:Aexpr).

Coercion AVar : string >-> Aexpr.
Coercion AConst : nat >-> Aexpr.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 70, no associativity).
Notation "x <= y"   := (BLeq x y) (in custom com at level 70, no associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".

Open Scope com_scope.

Definition sub : Type := string -> Aexpr.
Definition id_sub : sub := fun x => x.
Fixpoint Aapply (s:sub) (e:Aexpr) : Aexpr :=
  match e with
  | AConst n => AConst n
  | AVar x => s x
  | APlus a1 a2 => APlus (Aapply s a1) (Aapply s a2)
  end.

Lemma Aapply_id : forall e,
    Aapply id_sub e = e.
Proof.
  induction e; try reflexivity.
  simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Fixpoint Bapply  (s:sub) (e:Bexpr) : Bexpr :=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b => BNot (Bapply s b)
  | BAnd b1 b2 => BAnd (Bapply s b1) (Bapply s b2)
  | BLeq a1 a2 => BLeq (Aapply s a1) (Aapply s a2)
  end.

Definition update {E:Type} (s: string -> E) (x:string) (e:E) : string -> E :=
  fun y => if String.eqb x y then e else s x.

Notation "x '!->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).

Definition empty_map {A:Type} (x:A) : string -> A := fun _ => x.
Notation "'_' '!->' v" := (empty_map v) (at level 100, right associativity).

Lemma Bapply_id : forall e,
    Bapply id_sub e = e.
Proof.
  induction e; simpl;
    try (rewrite IHe);
    try (rewrite IHe1; rewrite IHe2);
    try (repeat rewrite Aapply_id);
    try reflexivity.
Qed.

Definition Valuation := string -> nat.

Fixpoint Aeval (V:Valuation) (e:Aexpr) : nat :=
  match e with
  | AConst n => n
  | AVar x => V x
  | APlus a1 a2 => (Aeval V a1) + (Aeval V a2)
  end.

Fixpoint Beval (V:Valuation) (e:Bexpr) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BNot b => negb (Beval V b)
  | BAnd b1 b2 => (Beval V b1) && (Beval V b2)
  | BLeq a1 a2 => (Aeval V a1) <=? (Aeval V a2)
  end.

Definition Comp (V:Valuation) (s:sub) : Valuation :=
  fun x => Aeval V (s x).

(** Lemma 2.1 *)
Lemma comp_sub : forall V s e,
    Aeval (Comp V s) e = Aeval V (Aapply s e).
Proof.
  induction e; simpl;
  try (rewrite IHe1; rewrite IHe2); reflexivity.
Qed.

(* Corollary 2.2 *)
Lemma asgn_sound : forall V s x e y,
    Comp V (update s x (Aapply s e)) y = update (Comp V s) x (Aeval (Comp V s) e) y.
Proof. intros. unfold Comp. unfold update. destruct (x =? y)%string;
         try (rewrite <- comp_sub; unfold Comp);
         reflexivity.
Qed.

Lemma comp_id : forall V,
    Comp V id_sub = V.
Proof. intros. extensionality x. reflexivity. Qed.

Inductive Stmt : Type :=
| SAsgn (x:string) (e:Aexpr)
| SSeq (s1 s2:Stmt)
| SIf (b:Bexpr) (s1 s2:Stmt)
| SWhile (b:Bexpr) (s:Stmt).

Notation "x := y"  :=
         (SAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (SSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x '{' y '}' '{' z '}'" :=
         (SIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x '{' y '}'" :=
         (SWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

(** Symbolic semantics *)

Definition SConfig : Type := Stmt * sub * Bexpr.

Reserved Notation " c '->s' c' " (at level 40).

Inductive Sstep : relation SConfig :=
| SAsgn_step : forall s x e sig phi,
    (<{ x := e ; s }>, sig , phi) ->s (s, (update sig x (Aapply sig e)), phi)
| SIfTrue_step : forall b s1 s2 s sig phi,
    (<{ if b {s1} {s2} ; s }>, sig, phi) ->s (<{ s1 ; s }>, sig, BAnd phi (Bapply sig b))
| SIfFalse_step : forall b s1 s2 s sig phi,
    (<{ if b {s1} {s2} ; s }>, sig, phi) ->s (<{ s2 ; s }>, sig, BAnd phi (BNot (Bapply sig b)))
| SWhileTrue_step : forall b s s' sig phi,
    (<{ while b {s} ; s' }>, sig, phi) ->s (<{ s ; while b {s} ; s' }>, sig, BAnd phi (Bapply sig b))
| SWhileFalse_step : forall b s s' sig phi,
    (<{ while b {s} ; s' }>, sig, phi) ->s (<{ s' }>, sig, BAnd phi (BNot (Bapply sig b)))
  where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40).

Example example_program : Stmt := <{ while (X <= 2) { X := X + 1 } ; Y := 1 }>.
Example Sexample_run : (example_program, id_sub, BTrue)
                        ->* (<{ Y := 1 }>, (X !-> <{X + 1 + 1}> ; X !-> <{X + 1}> ; id_sub ),
                       <{ BTrue && X <= 2 && X + 1 <= 2 && ~ (X + 1 + 1 <= 2) }>).
Proof. eapply rt_trans. eapply rt_trans. eapply rt_trans. eapply rt_trans. eapply rt_trans. apply rt_refl.
       apply rt_step. apply SWhileTrue_step.
       apply rt_step. apply SAsgn_step.
       apply rt_step. apply SWhileTrue_step.
       apply rt_step. apply SAsgn_step.
       apply rt_step. apply SWhileFalse_step.
Qed.

Definition CConfig : Type := Stmt * Valuation.

Reserved Notation " c '=>c' c'" (at level 40).

Inductive Cstep : relation CConfig :=
| CAsgn_step : forall s x e V,
    (<{ x := e ; s }>, V) =>c (s, update V x (Aeval V e))
| CIfTrue_step : forall b s1 s2 s V,
    Beval V b = true ->
    (<{ if b {s1} {s2} ; s }>, V) =>c (<{ s1 ; s }>, V)
| CIfFalse_step : forall b s1 s2 s V,
    Beval V b = false ->
    (<{ if b {s1} {s2} ; s }>, V) =>c (<{ s2 ; s }>, V)
| CWhileTrue_step : forall b s s' V,
    Beval V b = true ->
    (<{ while b {s} ; s' }>, V) =>c (<{ s ; while b {s} ; s' }>, V)
|CWhileFalse_step : forall b s s' V,
    Beval V b = false ->
    (<{ while b {s} ; s' }>, V) =>c (s' , V)
where " c '=>c' c'" := (Cstep c c').

Definition multi_Cstep := clos_refl_trans _ Cstep.
Notation " c '=>*' c' " := (multi_Cstep c c') (at level 40).

Example example_V : Valuation := (_ !-> 1).
Example Cexample_run : (example_program, example_V) =>* (<{ Y := 1 }>, (X !-> 3 ; X !-> 2 ; example_V)).
Proof. eapply rt_trans. eapply rt_trans. eapply rt_trans. eapply rt_trans. eapply rt_trans. apply rt_refl.
       apply rt_step. apply CWhileTrue_step. reflexivity.
       apply rt_step. apply CAsgn_step.
       apply rt_step. apply CWhileTrue_step. reflexivity.
       apply rt_step. apply CAsgn_step.
       apply rt_step. apply CWhileFalse_step. reflexivity.
Qed.

Lemma comp_is_update : forall V x e,
    update V x (Aeval V e) = Comp V (update id_sub x e).
Proof. intros. extensionality y. destruct (x =? y)%string. Admitted.

Theorem correctness : forall S S' sig phi V,
    (S, id_sub, BTrue) ->* (S', sig, phi) ->
    Beval V phi = true ->
    (S, V) =>* (S', Comp V sig).
Proof. intros. remember (S, id_sub, BTrue) as config0. remember (S', sig, phi) as config1.
       induction H.
       (* rt_step *)
       - inversion H; subst; inversion H1; inversion H2; subst;
           try (rewrite Bapply_id in *).
         + eapply rt_trans. apply rt_refl. apply rt_step.
           rewrite <- comp_is_update.
           rewrite Aapply_id.
           apply CAsgn_step.
         + eapply rt_trans. apply rt_refl. apply rt_step.
           apply CIfTrue_step. inversion H0. reflexivity.
         + eapply rt_trans. apply rt_refl. apply rt_step.
           apply CIfFalse_step. inversion H0. apply negb_true_iff in H4. assumption.
         + eapply rt_trans. apply rt_refl. apply rt_step.
           apply CWhileTrue_step. inversion H0. rewrite comp_id. reflexivity.
         + eapply rt_trans. apply rt_refl. apply rt_step.
           apply CWhileFalse_step. rewrite comp_id. inversion H0.
           apply negb_true_iff in H4. assumption.
        (* rt_refl *)
        - inversion Heqconfig1; subst. inversion H; subst.
          apply rt_refl.
        (* rt_trans *)
        - rewrite Heqconfig0 in *. rewrite Heqconfig1 in *.
          inversion H; subst; inversion H1; subst.
          +
