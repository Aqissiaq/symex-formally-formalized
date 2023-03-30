
From Coq Require Import String Bool.

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Parallel Traces.
Import TraceSemantics.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import ContextReduction PartialOrderReduction.

Open Scope com_scope.
Open Scope trace_scope.

Example par_simple_0: red__S ([], <{ (X := 1 ; Y := 1) || Y := 2 || X := 2}>)
                        ([Asgn__S X 1], <{ (skip ; Y := 1) || Y := 2 || X := 2 }>).
Proof. apply ctx_red_intro with (C := fun x => <{ (x ; Y := 1) || Y := 2 || X := 2}>); repeat constructor. Qed.

Example par_simple_1: red__S ([Asgn__S X 1], <{ Y := 1 || Y := 2 || X := 2 }>)
                        ([Asgn__S X 1 ; Asgn__S Y 2], <{ Y := 1 || skip || X := 2 }>).
Proof. apply ctx_red_intro with (C := fun x => <{ Y := 1 || x || X := 2 }>); repeat constructor. Qed.

Example par_simple_2: red__S ([Asgn__S X 1 ; Asgn__S Y 2], <{ Y := 1 || skip || X := 2 }>)
                        ([Asgn__S X 1 ; Asgn__S Y 2 ; Asgn__S X 2], <{ Y := 1 || skip || skip }>).
Proof. apply ctx_red_intro with (C := fun x => <{Y := 1 || skip || x}>); repeat constructor. Qed.

Example par_simple_3: red__S ([Asgn__S X 1 ; Asgn__S Y 2 ; Asgn__S X 2], <{ Y := 1 || skip || skip }>)
                        ([Asgn__S X 1 ; Asgn__S Y 2 ; Asgn__S X 2 ; Asgn__S Y 1], <{ skip || skip || skip }>) .
Proof. eapply ctx_red_intro with (C := fun x => <{x || skip || skip}>); repeat constructor. Qed.

Example par_simple: red_star__S ([], <{ (X := 1 ; Y := 1) || Y := 2 || X := 2}>)
                      ([Asgn__S X 1 ; Asgn__S Y 2 ; Asgn__S X 2 ; Asgn__S Y 1], <{ skip }>).
Proof.
  econstructor. apply ctx_red_intro with (C := fun x => x);
    [apply head_red_par__S | constructor].
  econstructor. apply ctx_red_intro with (C := fun x => <{skip || x}>);
    [apply head_red_par__S | repeat constructor].
  econstructor. apply par_simple_3.
  econstructor. apply par_simple_2.
  econstructor. apply par_simple_1.
  econstructor. apply ctx_red_intro with (C := fun x => <{x || Y := 2 || X := 2}>);
    [apply head_red_seq__S | repeat constructor].
  econstructor. apply par_simple_0.
  constructor.
Qed.

Definition final_trace (s: Stmt) (t: trace__S): Prop := red_star__S ([], s) (t, SSkip).

Example example2_stmt: Stmt := <{ Y := X || Z := X || X := 2 }>.

Example example2_t1: final_trace example2_stmt [Asgn__S Y X ; Asgn__S Z X ; Asgn__S X 2].
Proof.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X;Asgn__S Z X ; Asgn__S X 2], <{ skip || skip }>)).
  apply ctx_red_intro with (C := fun x => x);
    [apply head_red_par__S | constructor].
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X;Asgn__S Z X ; Asgn__S X 2], <{ skip || skip || skip }>)).
  apply ctx_red_intro with (C := fun x => <{skip || x}>);
    [apply head_red_par__S | repeat constructor].
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X;Asgn__S Z X], <{ skip || skip || X := 2 }>)).
  apply ctx_red_intro with (C := fun x => <{skip || skip || x}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X], <{ skip || Z := X || X := 2}>)).
  apply ctx_red_intro with (C := fun x => <{skip || x || X := 2}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([], <{ Y := X || Z := X || X := 2}>)).
  apply ctx_red_intro with (C := fun x => <{ x || Z := X || X := 2 }>); repeat constructor.
  constructor.
Qed.

Example example2_t2: final_trace example2_stmt [Asgn__S Z X ; Asgn__S Y X ; Asgn__S X 2].
Proof.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Z X;Asgn__S Y X ; Asgn__S X 2], <{ skip || skip }>)).
  apply ctx_red_intro with (C := fun x => x);
    [apply head_red_par__S | constructor].
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Z X;Asgn__S Y X ; Asgn__S X 2], <{ skip || skip || skip }>)).
  apply ctx_red_intro with (C := fun x => <{skip || x}>);
    [apply head_red_par__S | repeat constructor].
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Z X;Asgn__S Y X], <{ skip || skip || X := 2 }>)).
  apply ctx_red_intro with (C := fun x => <{skip || skip || x}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Z X], <{ Y := X || skip || X := 2 }>)).
  apply ctx_red_intro with (C := fun x => <{x || skip || X := 2}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([], <{ Y := X || Z := X || X := 2 }>)).
  apply ctx_red_intro with (C := fun x => <{Y := X || x || X := 2}>); repeat constructor.
  constructor.
Qed.

Example example2_t3: final_trace example2_stmt [Asgn__S Y X ; Asgn__S X 2 ; Asgn__S Z X].
Proof.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X ; Asgn__S X 2 ; Asgn__S Z X], <{ skip || skip }>)).
  apply ctx_red_intro with (C := fun x => x); constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X ; Asgn__S X 2 ; Asgn__S Z X], <{ skip || skip || skip }>)).
  apply ctx_red_intro with (C := fun x => <{skip || x}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X ; Asgn__S X 2], <{ skip || Z := X || skip }>)).
  apply ctx_red_intro with (C := fun s => <{ skip || s || skip }>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X], <{ skip || Z := X || X := 2 }>)).
  apply ctx_red_intro with (C := fun s => <{ skip || Z := X || s }>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([], <{ Y := X || Z := X || X := 2 }>)).
  apply ctx_red_intro with (C := fun s => <{ s || Z := X || X := 2 }>); repeat constructor.
  constructor.
Qed.

Example example2_t4: final_trace example2_stmt [Asgn__S Z X ; Asgn__S X 2 ; Asgn__S Y X].
Proof.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Z X ; Asgn__S X 2 ; Asgn__S Y X], <{ skip || skip }>)).
  apply ctx_red_intro with (C := fun s => s); constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Z X ; Asgn__S X 2 ; Asgn__S Y X], <{ skip || skip || skip }>)).
  apply ctx_red_intro with (C := fun x => <{skip || x}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Z X ; Asgn__S X 2], <{ Y := X || skip || skip }>)).
  apply ctx_red_intro with (C := fun s => <{s || skip || skip}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Z X], <{ Y := X || skip || X := 2 }>)).
  apply ctx_red_intro with (C := fun s => <{Y := X || skip || s}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([], <{ Y := X || Z := X || X := 2 }>)).
  apply ctx_red_intro with (C := fun s => <{Y := X || s || X := 2}>); repeat constructor.
  constructor.
Qed.

Example example2_t5: final_trace example2_stmt [Asgn__S X 2 ; Asgn__S Y X ; Asgn__S Z X].
Proof.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S X 2 ; Asgn__S Y X ; Asgn__S Z X], <{ skip || skip }>)).
  apply ctx_red_intro with (C := fun s => s); constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S X 2 ; Asgn__S Y X ; Asgn__S Z X], <{ skip || skip || skip }>)).
  apply ctx_red_intro with (C := fun x => <{skip || x}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S X 2 ; Asgn__S Y X], <{ skip || Z := X || skip }>)).
  apply ctx_red_intro with (C := fun s => <{skip || s || skip}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S X 2], <{ Y := X || Z := X || skip }>)).
  apply ctx_red_intro with (C := fun s => <{s || Z := X || skip}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([], <{ Y := X || Z := X || X := 2 }>)).
  apply ctx_red_intro with (C := fun s => <{ Y := X || Z := X || s}>); repeat constructor.
  constructor.
Qed.

Example example2_t6: final_trace example2_stmt [Asgn__S X 2 ; Asgn__S Z X ; Asgn__S Y X].
Proof.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S X 2 ; Asgn__S Z X ; Asgn__S Y X], <{ skip || skip }>)).
  apply ctx_red_intro with (C := fun s => s); constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S X 2 ; Asgn__S Z X ; Asgn__S Y X], <{ skip || skip || skip }>)).
  apply ctx_red_intro with (C := fun x => <{skip || x}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S X 2 ; Asgn__S Z X], <{ Y := X || skip || skip }>)).
  apply ctx_red_intro with (C := fun s => <{s || skip || skip}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S X 2], <{ Y := X || Z := X || skip }>)).
  apply ctx_red_intro with (C := fun s => <{ Y := X || s || skip}>); repeat constructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([], <{ Y := X || Z := X || X := 2 }>)).
  apply ctx_red_intro with (C := fun s => <{ Y := X || Z := X || s}>); repeat constructor.
  constructor.
Qed.

Example example_IF: interference_free__S (Asgn__S Z X) (Asgn__S Y X).
Proof. splits; unfold reads_var, writes_var, contains__A; intro contra;
         destruct contra; subst; discriminate.
Qed.

Definition final_trace__POR (s: Stmt) (t: trace__S): Prop := red_star__POR ([], s) (t, SSkip).

Example example2_t1__POR: final_trace__POR example2_stmt [Asgn__S Y X ; Asgn__S Z X ; Asgn__S X 2].
Proof.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X ; Asgn__S Z X ; Asgn__S X 2], <{ skip || skip }>)).
  apply ctx_red_intro with (C := fun s => s); repeat econstructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X ; Asgn__S Z X ; Asgn__S X 2], <{ skip || skip || skip }>)).
  apply ctx_red_intro with (C := fun s => <{skip || s}>); repeat econstructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X ; Asgn__S Z X], <{ skip || skip || X := 2 }>)).
  apply ctx_red_intro with (C := fun s => <{skip || skip || s}>); repeat econstructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([Asgn__S Y X], <{ skip || Z := X || X := 2 }>)).
  apply ctx_red_intro with (C := fun s => <{skip || s || X := 2}>); repeat econstructor.
  apply Relation_Operators.rtn1_trans with
    (y := ([], <{ Y := X || Z := X || X := 2 }>)).
  apply ctx_red_intro with (C := fun s => <{s || _ || _}>); repeat econstructor.
  constructor.
Qed.
