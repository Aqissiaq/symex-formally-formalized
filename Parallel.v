(** * Parallelism *)

(** We construct a very simple programming language with a parallel construct,
but without much else for now. The intent is to implement trace semantics.
*)

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
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

Definition Var : Type := string.

Inductive Stmt : Type :=
| SAsgn (x:Var) (e:Aexpr)
| SSeq (s1 s2: Stmt)
| SPar (s1 s2:Stmt)
| SIf (b:Bexpr) (s1 s2:Stmt)
| SSkip.

Notation "'skip'" := SSkip (in custom com at level 80) : com_scope.
Notation "x := y"  :=
         (SAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (SSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "x || y" :=
         (SPar x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x '{' y '}' '{' z '}'" :=
         (SIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.

(** Semantics would go here, but I am not interested yet *)

Open Scope com_scope.
(* useful lemma for progress in (trace) semantics *)
Lemma SSeq_disjoint : forall s s', <{s ; s'}> <> s'.
Proof. intros s s' contra. destruct s;
         induction s'; try discriminate;
         try (inversion contra; subst; exact (IHs'2 H1)).
Qed.

Lemma SPar_left_disjoint : forall s s', <{ s || s' }> <> s.
Proof. intros s s' contra. destruct s';
         induction s; try discriminate;
         inversion contra; subst;
         try (apply IHs1; assumption).
Qed.

Lemma SPar_right_disjoint : forall s s', <{ s || s' }> <> s'.
Proof. intros s s' contra. destruct s;
         induction s'; try discriminate;
         try (inversion contra; subst);
         apply IHs'2; assumption.
Qed.

Lemma SIf_true_disjoint : forall b s1 s2, <{if b {s1} {s2}}> <> s1.
Proof. intros b s s' contra. destruct s';
         induction s; try discriminate;
         inversion contra; subst;
         try (apply IHs1; assumption).
Qed.

Lemma SIf_false_disjoint : forall b s1 s2, <{ if b {s1}{s2} }> <> s2.
Proof. intros b s s' contra. destruct s;
         induction s'; try discriminate;
         try (inversion contra; subst);
         apply IHs'2; assumption.
Qed.
