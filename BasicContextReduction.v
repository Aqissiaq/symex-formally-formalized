(** * Context Reduction Basics *)

(** Reformulation of de Boer and Bonsangue's basic setup in the context-reduction setting *)

From Coq Require Import String Bool Datatypes Relations Program.Equality.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import ContextReduction.

Open Scope com_scope.

Inductive Stmt : Type :=
| SAsgn (x:string) (e:Aexpr)
| SSeq (s1 s2:Stmt)
| SIf (b:Bexpr) (s1 s2:Stmt)
| SWhile (b:Bexpr) (s:Stmt)
| SSkip.

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
Notation "'skip'" := SSkip (in custom com at level 80) : com_scope.

Inductive is_context: (Stmt -> Stmt) -> Prop :=
| is_context_hole: is_context (fun x => x)
| is_context_seq: forall s C,
    is_context C -> is_context (fun x => SSeq (C x) s).

Inductive head_red__S: relation (sub * Bexpr * Stmt) :=
| SAsgn_step: forall x e sig phi,
    head_red__S (sig, phi, <{x := e}>) ((x !-> Aapply sig e; sig), phi, SSkip)
| SIfTrue_step: forall b s1 s2 sig phi,
    head_red__S (sig, phi, <{if b {s1} {s2}}>) (sig, BAnd phi (Bapply sig b), s1)
| SIfFalse_step: forall b s1 s2 sig phi,
    head_red__S (sig, phi, <{if b {s1} {s2}}>) (sig, BAnd phi (BNot (Bapply sig b)), s2)
| SWhileTrue_step: forall b s sig phi,
    head_red__S (sig, phi, <{while b {s}}>) (sig, BAnd phi (Bapply sig b), <{s ; while b {s}}>)
| SWhileFalse_step: forall b s sig phi,
    head_red__S (sig, phi, <{while b {s}}>) (sig, BAnd phi (BNot (Bapply sig b)), SSkip)
| SSeq_skip: forall s sig phi,
    head_red__S (sig, phi, <{skip ; s}>) (sig, phi, s)
.

Definition Sstep: relation (sub * Bexpr * Stmt) := context_red is_context head_red__S.
Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.

Notation " c '->s' c'" := (Sstep c c') (at level 40).
Notation " c '->*' c'" := (multi_Sstep c c') (at level 40).

Inductive head_red__C: relation (Valuation * Stmt) :=
| CAsgn_step: forall x e V,
    head_red__C (V, <{x := e}>) ((x !-> Aeval V e ; V), SSkip)
| CIfTrue_step: forall b s1 s2 V,
    Beval V b = true ->
    head_red__C (V, <{if b {s1} {s2}}>) (V, s1)
| CIfFalse_step: forall b s1 s2 V,
    Beval V b = false ->
    head_red__C (V, <{if b {s1} {s2}}>) (V, s2)
| CWhileTrue_step: forall b s V,
    Beval V b = true ->
    head_red__C (V, <{while b {s}}>) (V, <{s ; while b {s}}>)
| CWhileFalse_step: forall b s V,
    Beval V b = false ->
    head_red__C (V, <{while b {s}}>) (V, SSkip)
| CSeq_skip: forall s V,
    head_red__C (V, <{skip ; s}>) (V, s)
.

Definition Cstep: relation (Valuation * Stmt) := context_red is_context head_red__C.
Definition multi_Cstep := clos_refl_trans_n1 _ Cstep.

Notation " c '=>c' c'" := (Cstep c c') (at level 40).
Notation " c '=>*' c'" := (multi_Cstep c c') (at level 40).

Theorem correctness : forall s s' sig phi V,
    (id_sub, BTrue, s) ->* (sig, phi, s') ->
    Beval V phi = true ->
    (V, s) =>* (Comp V sig, s').
Proof.
  intros. dependent induction H.
  - rewrite comp_id. constructor.
  - dependent destruction H. destruct x as [sig0 phi0]. dependent destruction H; econstructor;
    try (simpl in H2; apply andb_true_iff in H2; destruct H2; try (apply negb_true_iff in H2);
      rewrite <- comp_subB in H2).
    + constructor.
      * rewrite asgn_sound. constructor.
      * assumption.
    + eapply IHclos_refl_trans_n1; try reflexivity; assumption.
    + constructor.
      * constructor. apply H2.
      * assumption.
    + eapply IHclos_refl_trans_n1; try reflexivity; assumption.
    + constructor.
      * apply CIfFalse_step. apply H2.
      * assumption.
    + eapply IHclos_refl_trans_n1; try reflexivity; assumption.
    + constructor.
      * apply CWhileTrue_step. apply H2.
      * assumption.
    + eapply IHclos_refl_trans_n1; try reflexivity; assumption.
    + constructor.
      * apply CWhileFalse_step. apply H2.
      * assumption.
    + eapply IHclos_refl_trans_n1; try reflexivity; assumption.
    + constructor.
      * apply CSeq_skip.
      * assumption.
    + eapply IHclos_refl_trans_n1; try reflexivity; assumption.
Qed.

Ltac splits := repeat (try split).

Theorem completeness : forall s s' V0 V,
    (V0, s) =>* (V, s') ->
    exists sig phi, (id_sub, BTrue, s) ->* (sig, phi, s') /\ Beval V0 phi = true /\ V = Comp V0 sig.
Proof.
  intros. dependent induction H.
  - exists id_sub. exists BTrue. splits. constructor.
  - dependent destruction H. dependent destruction H.
    + destruct (IHclos_refl_trans_n1 s (C <{x0 := e}>) V0 x) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      eexists. eexists. splits.
      * econstructor.
        ** constructor; [apply SAsgn_step
                        | assumption].
        ** apply IHcomp.
      * assumption.
      * rewrite asgn_sound. rewrite IHupd. reflexivity.
    + destruct (IHclos_refl_trans_n1 s (C <{if b {s'0}{s2}}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      eexists. eexists. splits.
      * econstructor.
        ** constructor; [apply SIfTrue_step
                        | assumption].
        ** apply IHcomp.
      * simpl. apply andb_true_iff. split.
        ** assumption.
        ** rewrite <- comp_subB. rewrite <- IHupd. assumption.
      * assumption.
    + destruct (IHclos_refl_trans_n1 s (C <{if b {s1}{s'0}}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      eexists. eexists. splits.
      * econstructor.
        ** constructor; [apply SIfFalse_step
                        | assumption].
        ** apply IHcomp.
      * simpl. apply andb_true_iff. split.
        ** assumption.
        ** rewrite <- comp_subB. rewrite <- IHupd. apply negb_true_iff. assumption.
      * assumption.
    + destruct (IHclos_refl_trans_n1 s (C <{while b {s1}}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      eexists. eexists. splits.
      * econstructor.
        ** constructor; [apply SWhileTrue_step
                        | assumption].
        ** apply IHcomp.
      * simpl. apply andb_true_iff. split.
        ** assumption.
        ** rewrite <- comp_subB. rewrite <- IHupd. assumption.
      * assumption.
    + destruct (IHclos_refl_trans_n1 s (C <{while b {s1}}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      eexists. eexists. splits.
      * econstructor.
        ** constructor; [apply SWhileFalse_step
                        | assumption].
        ** apply IHcomp.
      * simpl. apply andb_true_iff. split.
        ** assumption.
        ** rewrite <- comp_subB. rewrite <- IHupd. apply negb_true_iff. assumption.
      * assumption.
    + destruct (IHclos_refl_trans_n1 s (C <{skip ; s'0}>) V0 V) as [sig [phi [IHcomp [IHval IHupd]]]];
        try reflexivity.
      exists sig. exists phi. splits; try assumption.
      econstructor.
      * constructor; [apply SSeq_skip | assumption].
      *  apply IHcomp.
Qed.
