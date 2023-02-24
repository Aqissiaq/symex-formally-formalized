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


(** * Dynamic Logic (section 4) *)

(* using Coq's propositions as (constructive) FOL over valuations *)
(* approach like Hoare logic in PLF *)
Definition Formula := Valuation -> Prop.
(* Notation "V |= p" := (p V) (at level 80). *)

Definition DLAnd (p1 p2: Formula): Formula := fun V => p1 V /\ p2 V.
Definition DLExists (x: Var) (p: Formula): Formula := fun V => exists e, p (x !-> Aeval V e ; V).
Definition DLForall (x: Var) (p: Formula): Formula := fun V => forall e, p (x !-> Aeval V e ; V).
(* this one is a bit experimental *)
Definition DLBox (s: Stmt) (p: Formula): Formula :=
  fun V => forall t, red_star__C V ([], s) (t, SSkip) -> p (acc_val V t).
Definition DLUpdate (s: sub) (p: Formula): Formula := fun V => p (Comp V s).
Definition Sequent (G P: Formula): Formula :=
  fun V => G V -> P V.

Definition DLpc (t : trace__S): Formula := fun V => Beval V (pc t) = true.

Inductive head__DLT: relation (Formula * trace__S * Stmt) :=
  (* this "stuttering step" causes problems with the DLT-S-correspondence *)
  (* | DLT_reduce: forall G P t sig, *)
      (* head__DLT (Sequent G (DLUpdate sig P), t, SSkip) (Sequent (DLAnd G (DLpc t)) (DLUpdate sig P), t, SSkip) *)
  | DLT_assign: forall G P t sig x e,
      head__DLT (Sequent G (DLUpdate sig P), t, <{x := e}>)
        (Sequent G (DLUpdate (x !-> Aapply sig e; sig) P), t :: Asgn__S x e, SSkip)
  | DLT_cond_true: forall G P t sig b s1 s2,
      head__DLT (Sequent G (DLUpdate sig P), t, <{if b {s1}{s2}}>)
              (Sequent G (DLUpdate sig P), t :: Cond b, <{s1}>)
  | DLT_cond_false: forall G P t sig b s1 s2,
      head__DLT (Sequent G (DLUpdate sig P), t, <{if b {s1}{s2}}>)
              (Sequent G (DLUpdate sig P), t :: Cond (BNot b), <{s2}>)
  | DLT_loop_true: forall G P t sig b s,
      head__DLT (Sequent G (DLUpdate sig P), t, <{while b {s}}>)
              (Sequent G (DLUpdate sig P), t :: Cond b, <{s ; while b {s}}>)
  | DLT_loop_false: forall G P t sig b s,
      head__DLT (Sequent G (DLUpdate sig P), t, <{while b {s}}>)
              (Sequent G (DLUpdate sig P), t :: Cond (BNot b), SSkip)
  | DLT_skip_seq: forall P t s,
      head__DLT (P, t, <{SSkip ; s}>) (P, t, s)
  | DLT_skip_par_l: forall P t s,
      head__DLT (P, t, <{SSkip || s}>) (P, t, s)
  | DLT_skip_par_r: forall P t s,
      head__DLT (P, t, <{s || SSkip}>) (P, t, s)
.

Definition DLT := context_red head__DLT.
Definition Derivable__DLT := clos_refl_trans_n1 _ DLT.

Lemma DL_S_correspondence: forall G P t t' sig0 s s',
    (exists sig, DLT (Sequent G (DLUpdate sig0 P), t, s) (Sequent G (DLUpdate sig P), t', s'))
    <-> red__S (t, s) (t', s').
Proof.
  intros. split; intro.
  - destruct H as [sig H]. dependent destruction H. inversion H; subst;
      (constructor; [constructor | assumption]).
  - dependent destruction H. inversion H; subst; eexists;
      (constructor; [constructor | assumption]).
Qed.

(* I do not understand the soundness and (relative) completeness formulations for DL(T) *)
