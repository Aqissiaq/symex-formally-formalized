(** * Simple Parallel Logic *)
(* testing out this framework for Einar's SPL *)

From Coq Require Import String Bool Datatypes Relations Program.Equality.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Parallel.

From SymEx Require Import Traces.
Import TraceSemantics.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import ContextReduction.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.

Ltac splits := repeat (try split).

(* using Coq's propositions as (constructive?) FOL over traces *)
(* this is like Hoare logic in PLF *)
Definition Formula := Valuation -> Prop.

(* Notation magic from PLF *)
Definition Aexp : Type := Valuation -> nat.
Definition assert_of_Prop (P : Prop) : Formula := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

(* Definition Aexp_of_aexp (a : Aexp) : Aexp := fun st => Aeval st a. *)
(* Coercion Aexp_of_aexp : aexp >-> Aexp. *)

Coercion assert_of_Prop : Sortclass >-> Formula.
Coercion Aexp_of_nat : nat >-> Aexp.
Add Printing Coercion Aexp_of_nat assert_of_Prop.
Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Add Printing Coercion Aexp_of_nat assert_of_Prop.
Declare Scope assertion_scope.
Bind Scope assertion_scope with Formula.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.
Notation assert P := (P%assertion : Formula).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st -> assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <-> assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

Definition Box (s: Stmt) (p: Formula): Formula :=
  fun V => forall t, red_star__C V ([], s) (t, SSkip) -> p (acc_val V t).

Inductive head_red__SPL: relation (Formula * trace__S * Stmt) :=
| Asgn__SPL: forall p t x e,
    head_red__SPL (p, t, <{x := e}>) (p, t :: Asgn__S x e, SSkip)
| Cond_true__SPL: forall p t b s1 s2,
    head_red__SPL (p, t, <{if b {s1} {s2}}>) (p, t :: Cond b, s1)
| Cond_false__SPL: forall p t b s1 s2,
    head_red__SPL (p, t, <{if b {s1} {s2}}>) (p, t :: Cond (BNot b), s2)
(* ... and those annoying skip-rules *)
| Skip_seq__SPL: forall p t s,
    head_red__SPL (p, t, <{skip ; s}>) (p, t, s)
| Skip_par_l__SPL: forall p t s,
    head_red__SPL (p, t, <{skip || s}>) (p, t, s)
| Skip_par_r__SPL: forall p t s,
    head_red__SPL (p, t, <{s || skip }>) (p, t, s)
.

Definition red__SPL := context_red head_red__SPL.
(* stepwise? to the left? lets see what's most useful *)
Definition Derivable := clos_refl_trans_n1 _ red__SPL.

Theorem soundness__SPL: forall p t s,
    Derivable (fun _ => True, Tnil, s) (p, t, SSkip) ->
    forall V, Box s p V.
Proof.
  unfold Box. intros. induction H.
  - destruct H0.
Admitted.
