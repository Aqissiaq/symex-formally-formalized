(** * Trace Sets *)

(** Building a different sort of trace semantics by looking at inductively generated (prefix-closed?) sets of traces
and then trying to do some reduction of that set

TL;DR:
> the semantics of a program is a set of traces, S
> we define some equivalence on traces ~ and obtain S/~
>> (and prove it complete)
> now any reduction S' should be between the two S/~ <= S' <= S
>> S' <= S guarantees completeness
>> S/~ <= S guarantees soundness
*)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Program.Equality.   (* for `dependent induction` *)
(* which apparently (CTrees) smuggles in UIP(-equivalent) *)
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)
From Coq Require Import Relations.
(* From Coq Require Import Classes.RelationClasses. *)

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import Parallel.

From SymEx Require Import Traces.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.

Ltac splits := repeat (try split).

(** Symbolic semantics *)
Definition Var : Type := string.

Inductive STrace_step : Type :=
| STAsgn (x:Var) (e:Aexpr)
| STCond (b:Bexpr).

Definition STrace : Type := trace STrace_step.

Inductive has_trace__S : Stmt -> STrace -> Prop :=
| htr_asgn : forall x e,
    has_trace__S <{x := e}> [STAsgn x e]
| htr_seq : forall s1 s2 t1 t2,
    has_trace__S s1 t1 ->
    has_trace__S s2 t2 ->
    has_trace__S <{s1 ; s2}> (t1 ++ t2)
| htr_par_step_left : forall s1 s2 s t1 t,
    has_trace__S s1 t1 ->
    has_trace__S <{s2 || s}> t ->
    has_trace__S <{(s1 ; s2) || s}> (t1 ++ t)
| htr_par_step_right : forall s1 s2 s t1 t,
    has_trace__S s1 t1 ->
    has_trace__S <{s || s2}> t ->
    has_trace__S <{s || s1 ; s2}> (t1 ++ t)
| htr_par_left : forall s1 s2 t1 t2,
    has_trace__S s1 t1 ->
    has_trace__S s2 t2 ->
    has_trace__S <{s1 || s2}> (t1 ++ t2)
| htr_par_right : forall s1 s2 t1 t2,
    has_trace__S s1 t1 ->
    has_trace__S s2 t2 ->
    has_trace__S <{s1 || s2}> (t2 ++ t1)
| htr_if_true : forall b s1 s2 t1,
    has_trace__S s1 t1 ->
    has_trace__S <{if b {s1}{s2}}> ([STCond b] ++ t1)
| htr_if_false : forall b s1 s2 t2,
    has_trace__S s2 t2 ->
    has_trace__S <{if b {s1}{s2}}> ([STCond (BNot b)] ++ t2)
.
(* no need for skip, maybe remove it from def if we need to recurse on s*)

(** Attempted functional def, runs into non-termination problems in parallel case
 probably redeemable, but not easily *)
(* Fixpoint trace__S (s:Stmt) (t: STrace) : Prop := *)
(*   match s with *)
(*   | <{ x := e }> => t = [STAsgn x e] *)
(*   | <{ s1 ; s2 }> => *)
(*       exists t1 t2, t1 ++ t2 = t /\ trace__S s1 t1 /\ trace__S s2 t2 *)
(*   | <{(s1 ; s2) || s}> => *)
(*       exists t1 t2, t1 ++ t2 = t /\ trace__S s1 t1 /\ trace__S <{s2 || s}> t2 *)
(*   | <{s || (s1 ; s2)}> => *)
(*       exists t1 t2, t1 ++ t2 = t /\ trace__S s1 t1 /\ trace__S <{s || s2}> t2 *)
(*   | <{ s1 || s2 }> => exists t1 t2 x s s', t = (t1 ++ t2 :: x) /\ trace__S <{s ; s'}> t1 /\ s1 = <{s ; s'}> *)
(*   | <{if b {s1}{s2}}> => (exists t1, [STCond b] ++ t1 = t /\ trace__S s1 t1) *)
(*                       \/ (exists t2, [STCond (BNot b)] ++ t2 = t /\ trace__S s2 t2) *)
(*   | <{skip}> => t = [] *)
(*   end. *)


Example X : Var := "x".
Example Y : Var := "y".
Example branch_ex : has_trace__S <{if X <= 1 {Y := X} {Y := 1}}> [STCond <{X <= 1}> ; STAsgn Y X].
Proof.
  assert ([STCond <{X <= 1}> ; STAsgn Y X] = [STCond <{X <= 1}>] ++ [STAsgn Y X]) by reflexivity.
  rewrite H. apply htr_if_true. apply htr_asgn.
Qed.

Example par_x : has_trace__S <{(X := 1 ; Y := 2) || (X := Y ; Y := X)}> [STAsgn X 1 ; STAsgn X Y ; STAsgn Y X ; STAsgn Y 2].
Proof.
  assert ([STAsgn X 1 ; STAsgn X Y ; STAsgn Y X ; STAsgn Y 2] = [STAsgn X 1] ++ [STAsgn X Y ; STAsgn Y X ; STAsgn Y 2]) by reflexivity.
  rewrite H. apply htr_par_step_left. apply htr_asgn.
  assert ([STAsgn X Y;STAsgn Y X;STAsgn Y 2] = [STAsgn X Y] ++ [STAsgn Y X;STAsgn Y 2]) by reflexivity.
  rewrite H0. apply htr_par_step_right. apply htr_asgn.
  assert ([STAsgn Y X;STAsgn Y 2] = [STAsgn Y X] ++ [STAsgn Y 2]) by reflexivity.
  rewrite H1. apply htr_par_right; apply htr_asgn.
Qed.

(* Concrete Semantics *)
Definition Val : Type := nat.

Inductive CTrace_step : Type :=
  | CTAsgn (x:Var) (v:Val).

Definition CTrace : Type := trace CTrace_step.

Fixpoint acc_val (V0:Valuation) (t:CTrace) : Valuation :=
  match t with
  | [] => V0
  | t :: CTAsgn x v => let V := acc_val V0 t in
                 (x !-> v ; V)
  end.

Definition Aeval_t (V0:Valuation) (t:CTrace) (e:Aexpr) : nat :=
  Aeval (acc_val V0 t) e.

Definition Beval_t (V0:Valuation) (t:CTrace) (e:Bexpr) : bool :=
  Beval (acc_val V0 t) e.

Fixpoint trace_of' (V0: Valuation) (t:CTrace) (s:Stmt) : CTrace :=
  match s with
  | <{ x := e }> => [CTAsgn x (Aeval_t V0 t e)]
  | <{s1 ; s2}> => let t1 := trace_of' V0 t s1 in
                  let t2 := trace_of' V0 t1 s2 in
                  t1 ++ t2
  (* deterministic big-step parallelism*)
  | <{s1 || s2}> => let t1 := trace_of' V0 t s1 in
                  let t2 := trace_of' V0 t1 s2 in
                  t1 ++ t2
  | <{ if b {s1} {s2}}> => if Beval_t V0 t b then trace_of' V0 t s1 else trace_of' V0 t s2
  | <{ skip }> => []
  end.

Definition trace_of (V0:Valuation) (s:Stmt) : CTrace :=
  trace_of' V0 [] s.

Definition has_trace__C (V0:Valuation) (s:Stmt) (t:CTrace) : Prop := t = trace_of V0 s.

Example branch_ex__C : has_trace__C (_ !-> 0) <{if X <= 1 {Y := X ; skip} {Y := 1}}> [CTAsgn Y 0].
Proof. unfold has_trace__C, trace_of. simpl. unfold Aeval_t. simpl. reflexivity. Qed.

Example par_ex__C : has_trace__C (_ !-> 0) <{(X := 1 ; Y := 2) || (X := Y ; Y := X)}> [CTAsgn X 1 ; CTAsgn Y 2 ; CTAsgn X 2 ; CTAsgn Y 2].
Proof. unfold has_trace__C, trace_of, trace_of', Aeval_t. simpl. reflexivity. Qed.

(** Properties *)
Fixpoint acc_subst (s0:sub) (t:STrace) : sub :=
  match t with
  | [] => s0
  | t :: STAsgn x e => let s := acc_subst s0 t in
                     (x !-> Aapply s e ; s)
  | t :: _ => acc_subst s0 t
  end.

Definition acc_subst_id := acc_subst id_sub.

Definition Aapply_t (t:STrace) (e:Aexpr) : Aexpr :=
  Aapply (acc_subst_id t) e.

Definition Bapply_t (s0:sub) (t:STrace) (e:Bexpr) : Bexpr :=
  Bapply (acc_subst s0 t) e.

Definition Bapply_t_id (t:STrace) (e:Bexpr) : Bexpr :=
  Bapply (acc_subst_id t) e.

Fixpoint pc (s0:sub) (t:STrace) : Bexpr :=
  match t with
  | [] => BTrue
  | t :: STCond b => BAnd (Bapply_t s0 t b) (pc s0 t)
  | t :: _ => pc s0 t
  end.

Definition pc_id := pc id_sub.

Definition is_abstraction (V0:Valuation) (tc:CTrace) (ts:STrace) : Prop :=
  acc_val V0 tc = Comp V0 (acc_subst_id ts).

Lemma cond_idemp : forall b t s,
    acc_subst s (t :: STCond b) = acc_subst s t.
Proof. intros. reflexivity. Qed.

Lemma acc_subst_empty : forall s,
    acc_subst s [] = s.
Proof. intros. reflexivity. Qed.

Lemma acc_subst_app : forall s0 t1 t2,
    acc_subst s0 (t1 ++ t2) = acc_subst (acc_subst s0 t1) t2.
Proof.
  intros. induction t2.
  - reflexivity.
  - destruct a.
    + simpl. rewrite IHt2. reflexivity.
    + assumption.
Qed.

Lemma pc_app : forall V0 t1 t2, Beval V0 (pc_id (t1 ++ t2)) = Beval V0 (pc_id t1) && Beval V0 (pc (acc_subst_id t1) t2).
Proof.
  induction t2.
  - simpl. destruct (Beval V0 (pc_id t1)); reflexivity.
  - destruct a.
    + assumption.
    + unfold pc_id in *. simpl. rewrite IHt2. simpl. unfold Bapply_t, acc_subst_id. rewrite acc_subst_app.
      (* this is a mess, but it's just rearranging some conjunctions *)
      rewrite 2 andb_assoc. rewrite andb_comm. rewrite andb_assoc. rewrite andb_comm.
      rewrite andb_comm with (b1 := Beval V0 (pc (acc_subst id_sub t1) t2)). rewrite andb_assoc. reflexivity.
Qed.

Lemma trace_seq_app : forall V s1 s2, trace_of V <{s1 ; s2}> = trace_of V s1 ++ trace_of' V (trace_of V s1) s2.
Proof.
  intros. destruct(trace_of V s1) eqn:H;
    unfold trace_of in *; simpl; rewrite H; reflexivity.
Qed.

Lemma acc_val_app : forall V0 t1 t2,
    acc_val V0 (t1 ++ t2) = acc_val (acc_val V0 t1) t2.
Proof.
  induction t2;
    [|destruct a; simpl; rewrite IHt2]; reflexivity.
Qed.

Theorem soundness : forall s V0 , exists ts,
    has_trace__S s ts /\ is_abstraction V0 (trace_of V0 s) ts /\ Beval V0 (pc_id ts) = true.
Proof.
  intros.
  (* unfold trace_of, trace_of'. *)
  dependent induction s.
  - (* x := e *)
    exists [STAsgn x e]. splits.
    + apply htr_asgn.
    + unfold is_abstraction. simpl. unfold acc_subst_id, acc_subst. simpl.
      rewrite asgn_sound. rewrite comp_id. reflexivity.
  - (* s1 ; s2 *)
    destruct (IHs1 V0) as [ts1 [comp [IH1 IHpc1]]].
    destruct (IHs2 (acc_val V0 (trace_of V0 s1))) as [ts2 [comp2 [IH2 IHpc2]]].
    exists (ts1 ++ ts2). splits.
    + apply htr_seq; assumption.
    + unfold is_abstraction in *. rewrite trace_seq_app. rewrite acc_val_app.
      unfold acc_subst_id. rewrite acc_subst_app.
      rewrite IH1 in *. admit.
    + rewrite pc_app. apply andb_true_iff. splits.
      * assumption.
      * unfold is_abstraction in *. rewrite IH1 in IHpc2. rewrite comp_subB in IHpc2.

      (* need some lemmas about multiple composition but I cannot formulate them separate from acc_*
       which is worrying *)


(* maybe needed later *)
Fixpoint is_prefix {A:Type} (t0 t:list A) : Prop :=
  match t0 with
  | [] => True
  | x :: xs => match t with
             | [] => False
             | y :: ys => x = y /\ is_prefix xs ys
             end
  end.

Definition prefix_closure (sem: STrace -> Prop) (t:STrace) : Prop :=
  exists t', sem t' /\ is_prefix t t'.
