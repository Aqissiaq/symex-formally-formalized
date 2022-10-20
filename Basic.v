(** * 2. Basic Symbolic Execution *)

(** We introduce a formal model of symbolic execution for a basic programming
language with a statically fixed number of programming variables. A configuration of the symbolic transition
system consists of the program statement to be executed, a substitution, and a path condition. Correctness then
states that for every reachable symbolic configuration and state which satisfies the path condition, there exists a
corresponding concrete execution. Conversely, completeness states that for every concrete execution there exists
a corresponding symbolic configuration such that the initial state of the concrete execution satisfies the path
condition and its final state can be obtained as a composition of the initial state and the generated substitution.
 *)
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Logic.FunctionalExtensionality.
From SymEx Require Import BinaryRelation.

Inductive Expr : Type :=
  | EVar (x:string)
  | ENot (e:Expr)
  | EAnd (e1 e2:Expr)
  | EEq (e1 e2:Expr).

Inductive Stmt : Type :=
  | SSkip
  | SAsgn (x:string) (e:Expr)
  | SSeq (s1 s2:Stmt)
  | SChoice (b:Expr) (s1 s2:Stmt)
  | SLoop (b:Expr) (s:Stmt).

Coercion EVar : string >-> Expr.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "x = y"   := (EEq x y) (in custom com at level 70, no associativity).
Notation "'~' b"   := (ENot b) (in custom com at level 75, right associativity).
Notation "x && y"  := (EAnd x y) (in custom com at level 80, left associativity).

Notation "'skip'" := SSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (SAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (SSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x '{' y '}' '{' z '}'" :=
         (SChoice x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x '{' y '}'" :=
         (SLoop x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
Open Scope com_scope.

Definition X : string := "x".
Definition Y : string := "y".
Definition Z : string := "z".

Definition Substitution := string -> Expr.

Definition id_sub : Substitution :=
  fun x => EVar x.

Definition empty_sub (e:Expr) : Substitution := fun _ => e.
Notation "'_' '!->' v" := (empty_sub v) (at level 100, right associativity).

Fixpoint apply (s:Substitution) (e:Expr) : Expr :=
  match e with
  | EVar x => s x
  | ENot e => ENot (apply s e)
  | EAnd e1 e2 => EAnd (apply s e1) (apply s e2)
  | EEq e1 e2 => EEq (apply s e1) (apply s e2)
  end.


Definition update (s:Substitution) (x:string) (e:Expr) : Substitution :=
  fun y => if String.eqb x y then e else s y.

Notation "x '!->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).

Lemma state_apply : forall st x e,
    (x !-> e ; st) x = e.
Proof. intros. unfold update. rewrite String.eqb_refl. reflexivity. Qed.

Inductive PathCondition : Type :=
  | PCTrue
  | PCFalse
  | PCVar (x:string)
  | PCNot (p:PathCondition)
  | PCAnd (p1 p2: PathCondition).

Fixpoint expr_eqb (e1 e2:Expr) : bool :=
  match e1 with
  | EVar x => match e2 with
             | EVar y => String.eqb x y
             | _ => false
             end
  | ENot e => match e2 with
             | ENot e' => expr_eqb e e'
             | _ => false
             end
  | EAnd e11 e12 => match e2 with
                   | EAnd e21 e22 => andb (expr_eqb e11 e21) (expr_eqb e12 e22)
                   | _ => false
                   end
  | EEq e11 e12 => match e2 with
                  | EEq e21 e22 => andb (expr_eqb e11 e21) (expr_eqb e12 e22)
                  | _ => false
                  end
  end.


Fixpoint expr_to_pc (e:Expr) : PathCondition :=
  match e with
  | EVar x => PCVar x
  | ENot e => PCNot (expr_to_pc e)
  | EAnd e1 e2 => PCAnd (expr_to_pc e1) (expr_to_pc e2)
  | EEq e1 e2 => if expr_eqb e1 e2 then PCTrue else PCFalse
  end.

Coercion expr_to_pc : Expr >-> PathCondition.

Definition SConfig : Type := Stmt * Substitution * PathCondition.

(** Symbolic Transition Relation *)
Reserved Notation " t '-->' t' " (at level 40).

Inductive Sstep : Relation SConfig :=
  | Asgn_Sstep : forall x e s sig phi,
      (<{ x := e ; s }>, sig, phi) --> (s, update sig x (apply sig e), phi)
  | IfTrue_Sstep : forall b s1 s2 s sig phi,
      (<{ if b {s1} {s2} ; s }>, sig, phi) --> (<{ s1 ; s }>, sig, PCAnd phi (apply sig b))
  | IfFalse_Sstep : forall b s1 s2 s sig phi,
      (<{ if b {s1} {s2} ; s }>, sig, phi) --> (<{ s2 ; s }>, sig, PCAnd phi (PCNot (apply sig b)))
  | Loop_Sstep : forall b s s' sig phi,
      (<{ while b {s} ; s' }>, sig, phi) --> (<{ s ; while b {s} ; s'}>, sig, PCAnd phi (apply sig b))
  | Loop_End : forall b s s' sig phi,
      (<{ while b {s} ; s' }>, sig, phi) --> (s', sig, PCAnd phi (PCNot (apply sig b)))
  where " t '-->' t' " := (Sstep t t').

Definition multi_Sstep := Trans_Ref_Closure Sstep.
Notation " c '-->*' c' " := (multi_Sstep c c') (at level 40).

Example example_program : Stmt := <{ X := Y ; if X = Z {Y := X} {Y := Z} ; skip}>.

Example Sstep_refl : (example_program, empty_sub (EVar "0"), PCTrue)
                 -->* (example_program, empty_sub (EVar "0"), PCTrue).
Proof. apply Rrefl. Qed.

Example Sstep_true : (example_program, empty_sub (EVar "0"), PCTrue)
                      -->* (<{ skip }> , Y !-> (EVar "0"); X !-> (EVar "0"); _ !-> (EVar "0"), PCAnd PCTrue PCTrue).
Proof. eapply Rtrans. eapply Rtrans. eapply Rtrans. apply Rrefl.
       apply Asgn_Sstep.
       apply IfTrue_Sstep.
       apply Asgn_Sstep.
Qed.

(* valuation *)
Definition Valuation (Val:Type) := Expr -> Val.

Definition comp : forall Val, Valuation Val -> Substitution -> Valuation Val :=
  fun _ V s e => match e with
            | EVar x => V (s x)
            | ENot e' => V (ENot (apply s e'))
            | EAnd e1 e2 => V (EAnd (apply s e1) (apply s e2))
            | EEq e1 e2 => V (EEq (apply s e1) (apply s e2))
              end.

(* Lemma 2.1 - a little silly, since it basically follows by definition *)
Lemma comp_compose : forall Val (V: Valuation Val) s e,
    comp Val V s e = V (apply s e).
Proof. intros. induction e; reflexivity. Qed.

Definition update_valuation {Val:Type} (V:Valuation Val) (x:string) (e:Expr) :=
  comp _ V (update id_sub x e).

Fixpoint test_V (e:Expr) : nat :=
match e with
      | EVar _ => 1
      | ENot e' => 2 * (test_V e')
      | EAnd e1 e2 => (test_V e1) + (test_V e2)
      | EEq e1 e2 => (test_V e1) - (test_V e2)
      end.

Example test_V' : Valuation nat := test_V.
Compute update_valuation test_V X (ENot (EVar X)) (EAnd X X).

(* Corollary 2.2 (of lemma 2.1) *)
Lemma update_valuation_sound : forall Val (V:Valuation Val) s x e,
    comp _ V (update s x (apply s e)) x = update_valuation (comp _ V s) x e x.
Proof. intros. simpl. repeat (rewrite state_apply). rewrite comp_compose. reflexivity. Qed.

Definition V_True {Val:Type} := Val -> bool.

(** Concrete Transition Relation *)
Definition CConfig (Val:Type) : Type := Stmt * Valuation Val.

Reserved Notation " c '==>' c'" (at level 40).

Inductive CStep {Val:Type} {truth:@V_True Val} : Relation (CConfig Val) :=
  | Asgn_Cstep : forall x e s V,
      (<{ x := e ; s }>, V) ==> (s, update_valuation V x e)
  | IfTrue_Cstep : forall b s1 s2 s V,
      truth (V b) = true ->
      (<{ if b {s1} {s2} ; s }>, V) ==> (<{ s1 ; s }>, V)
  | IfFalse_Cstep : forall b s1 s2 s V,
      truth (V b) = false ->
      (<{ if b {s1} {s2} ; s }>, V) ==> (<{ s2 ; s }>, V)
  | Loop_Cstep : forall b s s' V,
      truth (V b) = true ->
      (<{ while b {s} ; s' }>, V) ==> (<{ s ; while b {s} ; s' }>, V)
  | Loop_Cend : forall b s s' V,
      truth (V b) = false ->
      (<{ while b {s} ; s' }>, V) ==> (<{ s' }>, V)
  where " c '==>' c' " := (CStep c c').

Definition multi_Cstep {Val:Type} {tt:@V_True Val} := Trans_Ref_Closure (@CStep Val tt).
Notation " c '==>*' c' " := (multi_Cstep c c') (at level 40).

Fixpoint pc_truth {Val:Type} (V: Valuation Val) (truth:@V_True Val) (pc:PathCondition) : bool :=
  match pc with
  | PCVar x => truth (V x)
  | PCTrue => true
  | PCFalse => false
  | PCNot pc' => negb (pc_truth V truth pc')
  | PCAnd pc1 pc2 => andb (pc_truth V truth pc1) (pc_truth V truth pc2)
  end.

Theorem correct : forall S sig phi S' Val (V:Valuation Val) (truth:@V_True Val),
    (S, id_sub, PCTrue) -->* (S', sig, phi) ->
    pc_truth V truth phi = true ->
    @multi_Cstep Val truth (S, V) (S', comp _ V sig).
Proof. intros. induction H.
       - admit. (* I don't understand why this 0-step case does not bind variables *)
       - inversion H; subst;
           apply IHTrans_Ref_Closure.
         all: fail "goals remaining".
Admitted.

Theorem complete : forall S S' Val (V0 V: Valuation Val) truth,
    @multi_Cstep Val truth (S, V0) (S', V) ->
    exists sig phi, (S, id_sub, PCTrue) -->* (S', sig, phi).
Proof.
  intros. induction H.
  - admit.
  - apply IHTrans_Ref_Closure.
Admitted.

(* These proofs are
 1) annoying, because the 0-step case should be trivial
 2) suspicious, because the multi-step one should not be
 *)
