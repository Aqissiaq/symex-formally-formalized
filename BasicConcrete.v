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

(* Suppresses an annoying warning in completeness'*)
Set Warnings "-unused-intro-pattern".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Datatypes.
From Coq Require Import Program.   (* for `dependent induction` *)
From Coq Require Import Relations.

From SymEx Require Import Expr.
Import BasicExpr.
From SymEx Require Import Maps.
Import BasicMaps.

Open Scope com_scope.

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

Definition SConfig : Type := Stmt * sub * Bexpr.

Reserved Notation " c '->s' c' " (at level 40).

Inductive Sstep : relation SConfig :=
| SAsgn_step : forall x e sig phi s,
    (<{ x := e ; s }>, sig , phi) ->s (s, (update sig x (Aapply sig e)), phi)
| SIfTrue_step : forall b s1 s2 sig phi s,
    (<{ if b {s1} {s2} ; s }>, sig, phi) ->s (<{ s1 ; s }>, sig, BAnd phi (Bapply sig b))
| SIfFalse_step : forall b s1 s2 sig phi s,
    (<{ if b {s1} {s2} ; s }>, sig, phi) ->s (<{ s2 ; s }>, sig, BAnd phi (BNot (Bapply sig b)))
| SWhileTrue_step : forall b s sig phi s',
    (<{ while b {s} ; s' }>, sig, phi) ->s (<{ s ; while b {s} ; s'}>, sig, BAnd phi (Bapply sig b))
| SWhileFalse_step : forall b s sig phi s',
    (<{ while b {s} ; s' }>, sig, phi) ->s (<{ s' }>, sig, BAnd phi (BNot (Bapply sig b)))
  where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40).

Example example_program : Stmt := <{ while (X <= 2) { X := X + 1 } ; Y := 1 }>.
Example Sexample_run : (example_program, id_sub, BTrue)
                        ->* (<{ Y := 1 }>, (X !-> <{X + 1 + 1}> ; X !-> <{X + 1}> ; id_sub ),
                       <{ BTrue && X <= 2 && X + 1 <= 2 && ~ (X + 1 + 1 <= 2) }>).
Proof.
  assert (step1 : (example_program, id_sub, BTrue)
                  ->s (<{ X := X + 1 ; example_program }>, id_sub, <{ BTrue && X <= 2 }>)) by apply SWhileTrue_step.
  assert (step2 : (<{ X := X + 1 ; example_program }>, id_sub, <{ BTrue && X <= 2 }>)
                  ->s (example_program, (X !-> <{ X + 1 }> ; id_sub), <{ BTrue && X <= 2 }>)) by (apply SAsgn_step).
  assert (step3 : (example_program, (X !-> <{ X + 1 }> ; id_sub), <{ BTrue && X <= 2 }>)
                  ->s (<{ X := X + 1 ; example_program }>, (X !-> <{ X + 1 }> ; id_sub), <{ BTrue && X <= 2 && X + 1 <= 2 }>))
    by apply SWhileTrue_step.
  assert (step4 : (<{ X := X + 1 ; example_program }>, (X !-> <{ X + 1 }> ; id_sub), <{ BTrue && X <= 2 && X + 1 <= 2 }>)
                  ->s (example_program, (X !-> <{X + 1 + 1}> ; X !-> <{X + 1}> ; id_sub), <{ BTrue && X <= 2 && X + 1 <= 2 }>))
    by (apply SAsgn_step).
  assert (step5 : (example_program, (X !-> <{X + 1 + 1}> ; X !-> <{X + 1}> ; id_sub), <{ BTrue && X <= 2 && X + 1 <= 2 }>)
                  ->s (<{ Y := 1 }>, (X !-> <{X + 1 + 1}> ; X !-> <{X + 1}> ; id_sub ), <{ BTrue && X <= 2 && X + 1 <= 2 && ~ (X + 1 + 1 <= 2) }>))
    by (apply SWhileFalse_step).
  eapply Relation_Operators.rtn1_trans. apply step5.
  eapply Relation_Operators.rtn1_trans. apply step4.
  eapply Relation_Operators.rtn1_trans. apply step3.
  eapply Relation_Operators.rtn1_trans. apply step2.
  eapply Relation_Operators.rtn1_trans. apply step1.
  apply rtn1_refl.
Qed.

Definition CConfig : Type := Stmt * Valuation.

Reserved Notation " c '=>c' c'" (at level 40).

Inductive Cstep : relation CConfig :=
| CAsgn_step : forall x e V s,
    (<{ x := e ; s }>, V) =>c (s, update V x (Aeval V e))
| CIfTrue_step : forall b s1 s2 V s,
    Beval V b = true ->
    (<{ if b {s1} {s2} ; s }>, V) =>c (<{ s1 ; s }>, V)
| CIfFalse_step : forall b s1 s2 V s,
    Beval V b = false ->
    (<{ if b {s1} {s2} ; s }>, V) =>c (<{ s2 ; s }>, V)
| CWhileTrue_step : forall b s V s',
    Beval V b = true ->
    (<{ while b {s} ; s'}>, V) =>c (<{ s ; while b {s} ; s'}>, V)
|CWhileFalse_step : forall b s V s',
    Beval V b = false ->
    (<{ while b {s} ; s'}>, V) =>c (s', V)
where " c '=>c' c'" := (Cstep c c').

Definition multi_Cstep := clos_refl_trans_n1 _ Cstep.
Notation " c '=>*' c' " := (multi_Cstep c c') (at level 40).

Example example_V : Valuation := (_ !-> 1).
Example Cexample_run : (example_program, example_V) =>* (<{ Y := 1 }>, (X !-> 3 ; X !-> 2 ; example_V)).
Proof.
  assert (step1 : (example_program, example_V) =>c (<{ X := X + 1 ; example_program }>, example_V))
    by (apply CWhileTrue_step; auto).
  assert (step2 : (<{ X := X + 1 ; example_program }>, example_V) =>c (example_program, (X !-> 2 ; example_V)))
    by (apply CAsgn_step).
  assert (step3 : (example_program, (X !-> 2 ; example_V)) =>c (<{ X := X + 1 ; example_program }>, (X !-> 2 ; example_V)))
    by (apply CWhileTrue_step; auto).
  assert (step4 : (<{ X := X + 1 ; example_program }>, (X !-> 2 ; example_V))
          =>c (example_program, (X !-> 3 ; X !-> 2 ; example_V))) by (apply CAsgn_step).

  eapply Relation_Operators.rtn1_trans. apply CWhileFalse_step with (b := <{X <= 2}>). reflexivity.
  eapply Relation_Operators.rtn1_trans. apply step4.
  eapply Relation_Operators.rtn1_trans. apply step3.
  eapply Relation_Operators.rtn1_trans. apply step2.
  eapply Relation_Operators.rtn1_trans. apply step1.
  apply rtn1_refl.
Qed.

Theorem correctness : forall S S' sig phi V,
    (S, id_sub, BTrue) ->* (S', sig, phi) ->
    Beval V phi = true ->
    (S, V) =>* (S', Comp V sig).
Proof. intros. dependent induction H.
       - rewrite comp_id. constructor.
       - dependent destruction H.
         + eapply Relation_Operators.rtn1_trans.
           * rewrite asgn_sound. apply CAsgn_step.
           * eapply IHclos_refl_trans_n1; try reflexivity; try assumption.
         + eapply Relation_Operators.rtn1_trans.
           * apply CIfTrue_step. inversion H1. rewrite H2.
             apply andb_true_iff in H2. auto. destruct H2. rewrite comp_subB. apply H2.
           * eapply IHclos_refl_trans_n1; try reflexivity.
             apply andb_true_iff in H1. destruct H1. apply H.
         + eapply Relation_Operators.rtn1_trans.
           * apply CIfFalse_step. inversion H1. apply andb_true_iff in H2. destruct H2.
             apply negb_true_iff in H2. rewrite comp_subB. apply H2.
           * eapply IHclos_refl_trans_n1; try reflexivity.
             inversion H1. rewrite H2. apply andb_true_iff in H2. destruct H2. apply H.
         + eapply Relation_Operators.rtn1_trans.
           * apply CWhileTrue_step. inversion H1. rewrite H2.
             apply andb_true_iff in H2. destruct H2. rewrite comp_subB. apply H2.
           * eapply IHclos_refl_trans_n1; try reflexivity. inversion H1. rewrite H2.
             apply andb_true_iff in H2. destruct H2. apply H.
         + eapply Relation_Operators.rtn1_trans.
           * apply CWhileFalse_step. inversion H1. apply andb_true_iff in H2. destruct H2.
             apply negb_true_iff in H2. rewrite comp_subB. apply H2.
           * eapply IHclos_refl_trans_n1; try reflexivity. inversion H1. rewrite H2.
             apply andb_true_iff in H2. destruct H2. apply H.
Qed.

(* concise (but not very readable) proof *)
Theorem correctness' : forall S S' sig phi V,
    (S, id_sub, BTrue) ->* (S', sig, phi) ->
    Beval V phi = true ->
    (S, V) =>* (S', Comp V sig).
Proof. intros. dependent induction H.
       - rewrite comp_id. constructor.
       - dependent destruction H; eapply Relation_Operators.rtn1_trans;
           (* solves the =>* case *)
           try (eapply IHclos_refl_trans_n1; try reflexivity; try assumption;
               apply andb_true_iff in H1; destruct H1; apply H);
           (* apply a step *)
           try (rewrite asgn_sound);
           try constructor;
           (* solves the preconditions for if/while *)
           try (inversion H1; try (rewrite H2); apply andb_true_iff in H2; destruct H2;
             try (apply negb_true_iff in H2); rewrite comp_subB; apply H2).
Qed.

Ltac splits := repeat (try split).

Theorem completeness : forall S S' V0 V,
    (S, V0) =>* (S', V) ->
    exists sig phi, (S, id_sub, BTrue) ->* (S', sig, phi) /\ Beval V0 phi = true /\ V = Comp V0 sig.
Proof.
  intros. dependent induction H.
  - exists id_sub. exists BTrue. splits.
    + apply rtn1_refl.
  - dependent destruction H.
    + assert (IH : exists sig phi, (S, id_sub, BTrue) ->* (<{ x := e ; S' }>, sig, phi)
                         /\ Beval V0 phi = true
                         /\ V1 = Comp V0 sig) by (eapply IHclos_refl_trans_n1; reflexivity).
      destruct IH as [sig [phi [comp [val upd]]]].
      eexists. eexists. splits.
      * eapply Relation_Operators.rtn1_trans.
        apply SAsgn_step. apply comp.
      * assumption.
      * rewrite upd. rewrite asgn_sound. rewrite comp_sub. reflexivity.
    + assert (IH : exists sig phi, (S, id_sub, BTrue) ->* (<{ if b {s1} {s2} ; s }>, sig, phi)
                         /\ Beval V0 phi = true
                         /\ V = Comp V0 sig) by (eapply IHclos_refl_trans_n1; reflexivity).
      destruct IH as [sig [phi [comp [val upd]]]].
      eexists. eexists. splits.
      * eapply Relation_Operators.rtn1_trans.
        apply SIfTrue_step. apply comp.
      * simpl. rewrite <- comp_subB. rewrite <- upd. apply andb_true_iff. split; assumption.
      * assumption.
    + assert (IH : exists sig phi, (S, id_sub, BTrue) ->* (<{ if b {s1} {s2} ; s }>, sig, phi)
                         /\ Beval V0 phi = true
                         /\ V = Comp V0 sig) by (eapply IHclos_refl_trans_n1; reflexivity).
      destruct IH as [sig [phi [comp [val upd]]]].
      eexists. eexists. splits.
      * eapply Relation_Operators.rtn1_trans.
        apply SIfFalse_step. apply comp.
      * simpl. rewrite <- comp_subB. rewrite <- upd. apply andb_true_iff. rewrite negb_true_iff.
        split; assumption.
      * assumption.
    + assert (IH : exists sig phi, (S, id_sub, BTrue) ->* (<{ while b {s}; s' }>, sig, phi)
                         /\ Beval V0 phi = true
                         /\ V = Comp V0 sig) by (eapply IHclos_refl_trans_n1; reflexivity).
      destruct IH as [sig [phi [comp [val upd]]]].
      eexists. eexists. splits.
      * eapply Relation_Operators.rtn1_trans.
        apply SWhileTrue_step. apply comp.
      * simpl. rewrite andb_true_iff. rewrite  <- comp_subB. rewrite <- upd.
        split; assumption.
      * assumption.
    + assert (IH : exists sig phi, (S, id_sub, BTrue) ->* (<{ while b {s}; S' }>, sig, phi)
                         /\ Beval V0 phi = true
                         /\ V = Comp V0 sig) by (eapply IHclos_refl_trans_n1; reflexivity).
      destruct IH as [sig [phi [comp [val upd]]]].
      eexists. eexists. splits.
      * eapply Relation_Operators.rtn1_trans.
        apply SWhileFalse_step. apply comp.
      * simpl. rewrite <- comp_subB. rewrite <- upd. rewrite andb_true_iff. rewrite negb_true_iff.
        split; assumption.
      * assumption.
Qed.

(* another concise, but unreadable proof *)
(* keeping it because just the computation might be useful *)
Theorem completeness' : forall S S' V0 V,
    (S, V0) =>* (S', V) ->
    exists sig phi, (S, id_sub, BTrue) ->* (S', sig, phi).
Proof.
  intros. dependent induction H.
  - exists id_sub. exists BTrue. apply rtn1_refl.
  - dependent destruction H;
    try (assert (exists sig phi, (S, id_sub, BTrue) ->* (<{ x := e ; S' }>, sig, phi)) by (eapply IHclos_refl_trans_n1; reflexivity));
    try (assert (exists sig phi, (S, id_sub, BTrue) ->* (<{ if b {s1}{s2} ; s }>, sig, phi)) by (eapply IHclos_refl_trans_n1; reflexivity));
    try (assert (exists sig phi, (S, id_sub, BTrue) ->* (<{ while b {s} ; s' }>, sig, phi)) by (eapply IHclos_refl_trans_n1; reflexivity));
    try (assert (exists sig phi, (S, id_sub, BTrue) ->* (<{ while b {s} ; S' }>, sig, phi)) by (eapply IHclos_refl_trans_n1; reflexivity));
      (* this is annoying, but naming messes it up *)
      try (destruct H as [sig [phi comp]]);
      try (destruct H1 as [sig [phi comp]]);
      eexists; eexists; eapply Relation_Operators.rtn1_trans;
      try (apply comp); try constructor.
Qed.
