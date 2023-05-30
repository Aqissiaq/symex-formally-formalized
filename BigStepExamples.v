From Coq Require Import
                 Strings.String
                 Bool.Bool
                 Psatz
                 ZArith
                 Ensembles.

From SymEx Require Import BigStepClassical.

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import While.
Open Scope com_scope.

(* concrete *)
Compute option_apply (denot_fun
                      <{if X <= 10 {X := X + 1;
                                       if X <= 5 {Y := X + X}
                                              { skip }}
                               { Y := 42 }}>
                        (_ !-> 11)) Y.

Compute option_apply (denot_fun
                      <{while X <= 10 {X := X + 1;
                                       if X <= 5 {Y := X + X}
                                                { skip }} }>
                        (_ !-> 0)) X.

(* symbolic *)
Example branch_example: Stmt := <{
    if X <= 0
           {if 1 <= 0 {X := 42} {X := 0}}
           {if 1 <= 0 {X := 42} {X := 1}}
    }>.


Example branch_1: denot__S branch_example (fun V => (X !-> 42 ; V), Empty_set _).
Proof.
    left. exists (fun V => (X !-> 42 ; V)). eexists. repeat split.
    - left. exists (fun V => (X !-> 42 ; V)). eexists. repeat split.
    - simpl. apply Extensionality_Ensembles. split.
      + intros V H. inversion H.
      + intros V H. inversion H; subst; inversion H0; inversion H3.
Qed.

Example branch_2: denot__S branch_example (fun V => (X !-> 42 ; V), Empty_set _).
Proof.
    right. eexists. eexists. repeat split.
    - left. eexists. eexists. repeat split.
    - simpl. apply Extensionality_Ensembles. split.
      + intros V H. inversion H.
      + intros V H. inversion H; subst; inversion H0; inversion H3.
Qed.

Example branch_3: denot__S branch_example (fun V => (X !-> 0 ; V), fun V => V X = 0).
Proof.
    left. eexists. eexists. repeat split.
    - right. eexists. eexists. repeat split.
    - apply Extensionality_Ensembles. split; intros V H.
      + inversion H. split.
        * split.
          -- apply Full_intro.
          -- intro. rewrite H1 in H0. inversion H0.
        * rewrite H1. unfold denot__B, In. simpl. rewrite H1. reflexivity.
      + inversion H. inversion H1. apply leb_complete in H4. inversion H4. reflexivity.
Qed.

Lemma leb_correct_neg: forall n m, n <=? m <> true -> ~ (n <= m).
Proof. intros n m H contra. apply H. apply leb_correct. apply contra. Qed.

Example branch_4: denot__S branch_example (fun V => (X !-> 1 ; V), fun V => V X > 0).
Proof.
    right. eexists. eexists. repeat split.
    - right. eexists. eexists. repeat split.
    - apply Extensionality_Ensembles. split; intros V H.
      + inversion H; repeat split; intro; inversion H0.
        * rewrite <- H1 in H3. discriminate.
        * inversion H2.
        * inversion H2. rewrite <- H0 in H5. discriminate.
      + inversion H. unfold In. simpl.
        unfold Complement, In, denot__B in H1. simpl in H1.
        apply leb_correct_neg in H1. apply not_le in H1.
        assumption.
Qed.

Example loop_example: Stmt :=
         <{ while X <= 10 {X := X + 1} }>.

Example loop_0: denot__S loop_example (fun V => V, fun V => V X > 10).
Proof. apply Fam_intro with (i := 0). cbn.
       assert (Complement _ (denot__B <{ X <= 10 }>) = fun V => V X > 10).
         { apply Extensionality_Ensembles. repeat split; intros V H.
           - unfold Complement, In, denot__B in H. simpl in H. apply leb_correct_neg in H.
             apply not_le in H. apply H.
           - intro H'. unfold In, denot__B in *. simpl in *. apply leb_complete in H'. lia.
         }
         rewrite H. constructor.
Qed.
