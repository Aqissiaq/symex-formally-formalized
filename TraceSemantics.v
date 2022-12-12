(** * Trace Semantics *)

(** Anticipating the need for trace semantics for reduction in a concurrent setting,
    we develop them for the language extended with procedures from Recursion.v
 *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Program.   (* for `dependent induction` *)
(* which apparently (CTrees) smuggles in UIP(-equivalent) *)
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)
From Coq Require Import Relations.

From SymEx Require Import Expr.
Import ProcedureExpr.

From SymEx Require Import Maps.
Import ProcedureMaps.

From SymEx Require Import Recursion.

From SymEx Require Import Traces.

Open Scope com_scope.
Open Scope string_scope.
Open Scope trace_scope.

(** Symbolic semantics *)

Fixpoint Stmt_sub (s:Stmt) (u y:LVar) : Stmt :=
  let t : LSub := (u !-> (ALVar y) ; Lid_sub) in
  match s with
  | SGAsgn x e => SGAsgn x (Aapply Gid_sub t e)
  | SLAsgn x e => SLAsgn (if u =? x then y else x) (Aapply Gid_sub t e)
  | SProc P e => SProc P (Aapply Gid_sub t e)
  | SSeq s1 s2 => SSeq (Stmt_sub s1 u y) (Stmt_sub s2 u y)
  | SIf b s1 s2 => SIf (Bapply Gid_sub t b) (Stmt_sub s1 u y) (Stmt_sub s2 u y)
  | SWhile b s => SWhile (Bapply Gid_sub t b) (Stmt_sub s u y)
  | SReturn => SReturn
  end.

Definition STrace_step : Type := (Bexpr + (GVar * Aexpr) + (LVar * Aexpr)).

Definition cond  : Bexpr -> STrace_step := fun x => inl (inl x).
Definition asgnG : GVar -> Aexpr -> STrace_step := fun x e => inl (inr (x, e)).
Definition asgnL : LVar -> Aexpr -> STrace_step := fun x e => inr (x, e).

Definition STrace := trace STrace_step.

Fixpoint acc_GSubst (G:GSub) (L:LSub) (t:STrace) : GSub :=
  match t with
  | [] => G
  | t' :: inl (inr (x, e)) => let l := acc_LSubst G L t' in
                            let g := acc_GSubst G L t' in
                            (x !-> Aapply g l e ; g)
  | t' :: _ => acc_GSubst G L t'
  end
with acc_LSubst (G:GSub) (L:LSub) (t:STrace) : LSub :=
  match t with
  | [] => L
  | t' :: inr (x, e) => let l := acc_LSubst G L t' in
                      let g := acc_GSubst G L t' in
                      (x !-> Aapply g l e ; l)
  | t' :: _ => acc_LSubst G L t'
  end.

Definition acc_GSubst_id := acc_GSubst Gid_sub Lid_sub.
Definition acc_LSubst_id := acc_LSubst Gid_sub Lid_sub.

Definition Aapply_t : STrace -> Aexpr -> Aexpr :=
  fun t e => Aapply (acc_GSubst_id t) (acc_LSubst_id t) e.

Definition Bapply_t : STrace -> Bexpr -> Bexpr :=
  fun t e => Bapply (acc_GSubst_id t) (acc_LSubst_id t) e.

Fixpoint pc (t:STrace) : Bexpr :=
  match t with
  | [] => BTrue
  | t' :: inr _ => pc t'
  | t' :: inl (inr _) => pc t'
  | t' :: inl (inl p) => BAnd (Bapply_t t' p) (pc t')
  end.

Definition SConfig : Type := Stmt * STrace.

Reserved Notation " c '->s' c' " (at level 40).
Inductive Sstep : relation SConfig  :=
| SGAsgn_step : forall x e s t,
    (<{ x :=G e ; s }>, t) ->s (s, (t :: asgnG x e))
| SLAsgn_step : forall x e s t,
    (<{ x :=L e ; s }>, t) ->s (s, t :: asgnL x e)
| SProc_step : forall (t:STrace) u y body e s t,
    (* "y fresh", somehow *)
    (<{ proc(u){body}(e) ; s }>, t) ->s (SSeq (Stmt_sub body u y) s, t :: asgnL y e)
| SReturn_step : forall s t,
    (<{ return ; s }>, t) ->s (s, t)
| SIfTrue_step : forall b s1 s2 s t,
    (<{ if b {s1}{s2} ; s}>, t) ->s (<{ s1 ; s }>, t :: cond b)
| SIfFalse_step : forall b s1 s2 s t,
    (<{ if b {s1}{s2} ; s}>, t) ->s (<{ s2 ; s }>, t :: cond (BNot b))
| SWhileTrue_step : forall b s s' t,
    (<{ while b {s} ; s' }>, t) ->s (<{ s ; while b {s} ; s' }>, t :: cond b)
| SWhileFalse_step : forall b s s' t,
    (<{ while b {s} ; s' }>, t) ->s (s', t :: cond (BNot b))
where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40) : trace_scope.

(** Concrete semantics *)

Definition Val : Type := nat.
Definition CTrace_step : Type := (GVar * Val) + (LVar * Val).

Definition CTrace := trace CTrace_step.

Fixpoint acc_GVal (G0:GVal) (L0:LVal) (t:CTrace) : GVal :=
  match t with
  | Tnil => G0
  | Tcons t' (inr _) => acc_GVal G0 L0 t'
  | Tcons t' (inl (x, v)) => let G' := acc_GVal G0 L0 t' in
                            (x !-> v ; G')
  end.
Fixpoint acc_LVal (G0:GVal) (L0:LVal) (t:CTrace) : LVal :=
  match t with
  | Tnil => L0
  | Tcons t' (inl _) => acc_LVal G0 L0 t'
  | Tcons t' (inr (x, v)) => let L' := acc_LVal G0 L0 t' in
                            (x !-> v ; L')
  end.

Definition Aeval_t (G0:GVal) (L0:LVal) (t:CTrace) (e:Aexpr) : nat :=
  Aeval (acc_GVal G0 L0 t) (acc_LVal G0 L0 t) e.

Definition Beval_t (G0:GVal) (L0:LVal) (t:CTrace) (b:Bexpr) : bool :=
  Beval (acc_GVal G0 L0 t) (acc_LVal G0 L0 t) b.

Lemma Gcomp_update_comm : forall G L x (v:Val) s,
    GComp G L (update s x (AConst v)) = update (GComp G L s) x v.
Proof.
  intros. extensionality y.
  unfold GComp. unfold update. destruct (x =? y); simpl; reflexivity.
Qed.

Lemma Lcomp_update_comm : forall G L x (v:Val) s,
    LComp G L (update s x (AConst v)) = update (LComp G L s) x v.
Proof.
  intros. extensionality y.
  unfold LComp. unfold update. destruct (x =? y); simpl; reflexivity.
Qed.

Definition CConfig : Type := Stmt * CTrace.

Inductive Cstep (G0:GVal) (L0:LVal) : relation CConfig :=
| CGAsgn_step : forall x e s t,
    Cstep G0 L0 (<{ x :=G e ; s }>, t) (s, t :: inl (x, Aeval_t G0 L0 t e))
| CLAsgn_step : forall x e s t,
    Cstep G0 L0 (<{ x :=L e ; s }>, t) (s, t :: inr (x, Aeval_t G0 L0 t e))
| CProc_step : forall u body e s' t y,
    (* y fresh *)
    Cstep G0 L0 (<{ proc(u){body}(e) ; s' }>, t)  (SSeq (Stmt_sub body u y) s', t :: inr (y, Aeval_t G0 L0 t e))
| CReturn_step : forall s t,
    Cstep G0 L0 (<{ return ; s }>, t)  (s, t)
| CIfTrue_step : forall b s1 s2 s t,
    Beval_t G0 L0 t b = true ->
    Cstep G0 L0 (<{ if b {s1}{s2} ; s }>, t)  (<{s1 ; s}>, t)
| CIfFalse_step : forall b s1 s2 s t,
    Beval_t G0 L0 t b = false ->
    Cstep G0 L0 (<{ if b {s1}{s2} ; s }>, t)  (<{s2 ; s}>, t)
| CWhileTrue_step : forall b s s' t,
    Beval_t G0 L0 t b = true ->
    Cstep G0 L0 (<{ while b {s} ; s' }>, t)  (<{s ; while b {s} ; s'}>, t)
| CWhileFalse_step : forall b s s' t,
    Beval_t G0 L0 t b = false ->
    Cstep G0 L0 (<{ while b {s} ; s' }>, t)  (s', t).

Definition multi_Cstep {G0:GVal} {L0:LVal} := clos_refl_trans_n1 _ (Cstep G0 L0).
Notation " c '=>c' c'" := (Cstep _ _ c c').
Notation " c '=>*' c' " := (multi_Cstep c c') (at level 40).

(** an aside with examples to verify semantics *)

(** Correctness *)
Ltac splits := repeat (try split).

Theorem correctness : forall s s' t0 t G0 L0,
    (s, t0) ->* (s', t) ->
    Beval G0 L0 (pc t) = true ->
    (* start trace is concretely reachable *)
    (* this is a somewhat "brute force" solution *)
    (exists t', acc_GVal G0 L0 t' = GComp G0 L0 (acc_GSubst_id t0)
           /\ acc_LVal G0 L0 t' = LComp G0 L0 (acc_LSubst_id t0)) ->
    exists t'0 t', @multi_Cstep G0 L0 (s, t'0) (s', t')
          /\ acc_GVal G0 L0 t' = GComp G0 L0 (acc_GSubst_id t)
          /\ acc_LVal G0 L0 t' = LComp G0 L0 (acc_LSubst_id t).
Proof.
  intros. dependent induction H.
    - destruct H1 as [t' [HG HL]].
    exists t'. exists t'. splits.
    + apply rtn1_refl.
    + assumption.
    + assumption.
  - dependent destruction H.
    + (* global assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=G e ; s'}> t0 t1) as [t0' [t' [comp [IHG IHL]]]];
        try reflexivity;
        try assumption.
      eexists. exists (t' :: inl (x, Aeval (acc_GVal G0 L0 t') (acc_LVal G0 L0 t') e)). splits.
      * eapply Relation_Operators.rtn1_trans. apply CGAsgn_step. apply comp.
      * unfold acc_GSubst_id in *. unfold acc_LSubst_id in *. unfold Aeval_t.
        simpl. rewrite Gasgn_sound. rewrite eval_comp.
        rewrite <- IHG. rewrite <- IHL. reflexivity.
      * simpl. assumption.
    + (* local assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=L e ; s'}> t0 t1) as [t0' [t' [comp [IHG IHL]]]];
        try reflexivity;
        try assumption.
      eexists. exists (t' :: inr (x, Aeval (acc_GVal G0 L0 t') (acc_LVal G0 L0 t') e)). splits.
      * eapply Relation_Operators.rtn1_trans. apply CLAsgn_step. apply comp.
      * simpl. assumption.
      * unfold acc_GSubst_id in *. unfold acc_LSubst_id in *. unfold Aeval_t.
        simpl. rewrite Lasgn_sound. rewrite eval_comp.
        rewrite <- IHG. rewrite <- IHL. reflexivity.
    + (* proc *)
      destruct (IHclos_refl_trans_n1 s <{ proc(u){body}(e) ; s0}> t0 t2) as [t0' [t' [comp [IHG IHL]]]];
        try reflexivity;
        try assumption.
      eexists. exists (t' :: inr (y, Aeval_t G0 L0 t' e)). splits.
      * eapply Relation_Operators.rtn1_trans;
          [apply CProc_step | apply comp].
      * simpl. assumption.
      * unfold acc_GSubst_id in *. unfold acc_LSubst_id in *. unfold Aeval_t.
        simpl. rewrite Lasgn_sound. rewrite eval_comp.
        rewrite <- IHG. rewrite <- IHL. reflexivity.
    + (* return *)
      destruct (IHclos_refl_trans_n1 s <{ return ; s'}> t0 t) as [t0' [t' [comp [IHG IHL]]]];
        try reflexivity;
        try assumption.
      eexists. exists t'. splits.
      * eapply Relation_Operators.rtn1_trans;
          [apply CReturn_step | apply comp].
      * assumption.
      * assumption.
    + (* if true *)
      simpl in H1. apply andb_true_iff in H1. destruct H1.
      destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0}> t0 t1) as [t0' [t' [comp [IHG IHL]]]];
        try reflexivity;
        try assumption.
      eexists. exists t'. splits.
      * eapply Relation_Operators.rtn1_trans.
        ** eapply CIfTrue_step. unfold Beval_t.
           unfold Bapply_t in H. rewrite IHG. rewrite IHL.
           rewrite <- eval_compB. rewrite Comp_subB. apply H.
        ** apply comp.
      * assumption.
      * assumption.
    + (* if false *)
      simpl in H1. apply andb_true_iff in H1. destruct H1. apply negb_true_iff in H.
      destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0}> t0 t1) as [t0' [t' [comp [IHG IHL]]]];
        try reflexivity;
        try assumption.
      eexists. exists t'. splits.
      * eapply Relation_Operators.rtn1_trans.
        ** eapply CIfFalse_step. unfold Beval_t.
           unfold Bapply_t in H. rewrite IHG. rewrite IHL.
           rewrite <- eval_compB. rewrite Comp_subB. apply H.
        ** apply comp.
      * simpl. assumption.
      * simpl. assumption.
    + (* while true *)
      simpl in H1. apply andb_true_iff in H1. destruct H1.
      destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'0}> t0 t1) as [t0' [t' [comp [IHG IHL]]]];
        try reflexivity;
        try assumption.
      eexists. exists t'. splits.
      * eapply Relation_Operators.rtn1_trans.
        ** eapply CWhileTrue_step. unfold Beval_t.
           unfold Bapply_t in H. rewrite IHG. rewrite IHL.
           rewrite <- eval_compB. rewrite Comp_subB. apply H.
        ** apply comp.
      * simpl. assumption.
      * simpl. assumption.
    + (* while false *)
      simpl in H1. apply andb_true_iff in H1. destruct H1. apply negb_true_iff in H.
      destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'}> t0 t1) as [t0' [t' [comp [IHG IHL]]]];
        try reflexivity;
        try assumption.
      eexists. exists t'. splits.
      * eapply Relation_Operators.rtn1_trans.
        ** eapply CWhileFalse_step. unfold Beval_t.
           unfold Bapply_t in H. rewrite IHG. rewrite IHL.
           rewrite <- eval_compB. rewrite Comp_subB. apply H.
        ** apply comp.
      * simpl. assumption.
      * simpl. assumption.
Qed.

Theorem completeness : forall s s' t0 t G0 L0,
    @multi_Cstep G0 L0 (s, t0) (s', t) ->
    (exists t', Beval G0 L0 (pc t') = true
           /\ GComp G0 L0 (acc_GSubst_id t') = acc_GVal G0 L0 t0
           /\ LComp G0 L0 (acc_LSubst_id t') = acc_LVal G0 L0 t0) ->
    exists (t'0 t':STrace),
      (s, t'0) ->* (s', t')
      /\ Beval G0 L0 (pc t') = true
      /\ GComp G0 L0 (acc_GSubst_id t') = acc_GVal G0 L0 t
      /\ LComp G0 L0 (acc_LSubst_id t') = acc_LVal G0 L0 t.
Proof.
  intros. dependent induction H.
  - destruct H0 as [t' [HPC [HG HL]]].
    exists t'. exists t'. splits;
      try assumption. apply rtn1_refl.
  - inversion H; subst.
    + (* global assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=G e ; s'}> t0 t1) as [t0' [t' [comp [pc_true [IHG IHL]]]]];
        try reflexivity; try assumption.
      exists t0'. exists (t' :: asgnG x e). splits.
      * eapply Relation_Operators.rtn1_trans. apply SGAsgn_step. apply comp.
      * simpl. assumption.
      * unfold acc_GSubst_id in *. unfold acc_LSubst_id in *. unfold Aeval_t.
        simpl. rewrite Gasgn_sound. rewrite eval_comp.
        rewrite IHG. rewrite IHL. reflexivity.
      * simpl. assumption.
      + (* local assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=L e ; s'}> t0 t1) as [t0' [t' [comp [pc_true [IHG IHL]]]]];
        try reflexivity; try assumption.
      exists t0'. exists (t' :: asgnL x e). splits.
      * eapply Relation_Operators.rtn1_trans. apply SLAsgn_step. apply comp.
      * simpl. assumption.
      * simpl. assumption.
      * unfold acc_GSubst_id in *. unfold acc_LSubst_id in *. unfold Aeval_t.
        simpl. rewrite Lasgn_sound. rewrite eval_comp.
        rewrite IHG. rewrite IHL. reflexivity.
      + (* procedure call *)
      destruct (IHclos_refl_trans_n1 s <{ proc(u){body}(e) ; s'0}> t0 t1) as [t0' [t' [comp [pc_true [IHG IHL]]]]];
        try reflexivity; try assumption.
      exists t0'. exists (t' :: asgnL y0 e). splits.
      * eapply Relation_Operators.rtn1_trans. apply SProc_step. exact []. apply comp.
      * simpl. assumption.
      * simpl. assumption.
      * unfold acc_LSubst_id in *. unfold acc_GSubst_id in *. unfold Aeval_t.
        simpl. rewrite Lasgn_sound. rewrite eval_comp.
        rewrite IHG. rewrite IHL. reflexivity.
      + (* return *)
      destruct (IHclos_refl_trans_n1 s <{ return ; s'}> t0 t) as [t0' [t' [comp [pc_true [IHG IHL]]]]];
        try reflexivity; try assumption.
      exists t0'. exists t'. splits;
        try assumption.
      eapply Relation_Operators.rtn1_trans. apply SReturn_step. apply comp.
      + (* if true *)
      destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0}> t0 t) as [t0' [t' [comp [pc_true [IHG IHL]]]]];
        try reflexivity; try assumption.
      exists t0'. exists (t' :: cond b). splits.
      * eapply Relation_Operators.rtn1_trans. apply SIfTrue_step. apply comp.
      * simpl. apply andb_true_iff. split.
        ** unfold Beval_t in H4. rewrite <- IHG in H4. rewrite <- IHL in H4. rewrite <- eval_compB in H4.
           rewrite Comp_subB in H4. unfold Bapply_t. assumption.
        ** assumption.
      * simpl. assumption.
      * simpl. assumption.
      + (* if false *)
      destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0}> t0 t) as [t0' [t' [comp [pc_true [IHG IHL]]]]];
        try reflexivity; try assumption.
      exists t0'. exists (t' :: cond (BNot b)). splits.
      * eapply Relation_Operators.rtn1_trans. apply SIfFalse_step. apply comp.
      * simpl. apply andb_true_iff. split.
        ** unfold Beval_t in H4. rewrite <- IHG in H4. rewrite <- IHL in H4. rewrite <- eval_compB in H4.
           rewrite Comp_subB in H4. unfold Bapply_t. apply negb_true_iff. assumption.
        ** assumption.
      * simpl. assumption.
      * simpl. assumption.
      + (* while true *)
      destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'0}> t0 t) as [t0' [t' [comp [pc_true [IHG IHL]]]]];
        try reflexivity; try assumption.
      exists t0'. exists (t' :: cond b). splits.
      * eapply Relation_Operators.rtn1_trans. apply SWhileTrue_step. apply comp.
      * simpl. apply andb_true_iff. split.
        ** unfold Beval_t in H4. rewrite <- IHG in H4. rewrite <- IHL in H4. rewrite <- eval_compB in H4.
           rewrite Comp_subB in H4. unfold Bapply_t. assumption.
        ** assumption.
      * simpl. assumption.
      * simpl. assumption.
      + (* while false *)
      destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'}> t0 t) as [t0' [t' [comp [pc_true [IHG IHL]]]]];
        try reflexivity; try assumption.
      exists t0'. exists (t' :: cond (BNot b)). splits.
      * eapply Relation_Operators.rtn1_trans. apply SWhileFalse_step. apply comp.
      * simpl. apply andb_true_iff. split.
        ** unfold Beval_t in H4. rewrite <- IHG in H4. rewrite <- IHL in H4. rewrite <- eval_compB in H4.
           rewrite Comp_subB in H4. unfold Bapply_t. apply negb_true_iff. assumption.
        ** assumption.
      * simpl. assumption.
      * simpl. assumption.
Qed.

(** Attempts to merge some states *)
(** Plan: *)
(** 1. define an equivalence on Straces that lead to the same state *)
(** 2. show that we can contine computation from an equivalent state (?)
 *)

Definition GSub_equiv (G G':GSub) := forall x, G x = G' x.
Definition LSub_equiv (G G':GSub) := forall x, G x = G' x.
Definition PC_equiv (t t': STrace) := forall G0 L0, Beval G0 L0 (pc t) = true <-> Beval G0 L0 (pc t') = true.

Definition STrace_equiv (t t':STrace) := GSub_equiv (acc_GSubst_id t) (acc_GSubst_id t')
                                         /\ LSub_equiv (acc_LSubst_id t) (acc_LSubst_id t')
                                         /\ PC_equiv t t'.

Notation "t ~ t'" := (STrace_equiv t t') (at level 40) : trace_scope.

Lemma STrace_equiv_refl : forall t, t ~ t.
Proof. intro. unfold STrace_equiv. splits;
         intro; assumption.
Qed.

Lemma STrace_equiv_sym : forall t t', t ~ t' -> t' ~ t.
Proof. intros. unfold STrace_equiv in *. destruct H. destruct H0. splits.
       - intro. symmetry. apply H.
       - intro. symmetry. apply H0.
       - apply H1. - apply H1.
Qed.

Lemma STrace_equiv_trans : forall t t' t'', t ~ t' -> t' ~ t'' -> t ~ t''.
Proof. intros. unfold STrace_equiv in *. destruct H, H0, H1, H2. splits; intro.
         - rewrite H, H0. reflexivity.
         - rewrite H1, H2. reflexivity.
         - apply H3 in H5. apply H4 in H5. apply H5.
         - apply H4 in H5. apply H3 in H5. apply H5.
Qed.

(** The necessary condition on trace-prefixes for correctness*)
Definition correctness_prefix_condition t G0 L0 :=
  (exists t', acc_GVal G0 L0 t' = GComp G0 L0 (acc_GSubst_id t)
         /\ acc_LVal G0 L0 t' = LComp G0 L0 (acc_LSubst_id t)).

(**Idea: if two straces are equivalent, and one satisfies ^, then the other also does*)
Lemma STrace_correct_equiv_cong : forall t t' G0 L0,
    t ~ t' ->
    correctness_prefix_condition t G0 L0 ->
    correctness_prefix_condition t' G0 L0 .
Proof.
  intros. destruct H0 as [ct [HG HL]].
  exists ct. destruct H. splits.
  - rewrite HG. extensionality x.
    unfold GComp. rewrite <- H. reflexivity.
  - rewrite HL. extensionality x.
    unfold LComp. rewrite <- (proj1 H0). reflexivity.
Qed.

Lemma STrace_pc_equiv_cong : forall t t' G0 L0,
    t ~ t' ->
    Beval G0 L0 (pc t) = true ->
    Beval G0 L0 (pc t') = true.
Proof.
  intros t t' G0 L0 H. destruct H as [_ [_ PCEquiv]].
  apply PCEquiv.
Qed.

(* use these lemmas for something like "for t ~ t', if a concretization of t exists then a concretization of t' does too"
 and then maybe "(s, t) -> (s, t') is a sound reduction if t ~ t'" and do some state merging?*)
(* Note: still indexing on initial valuations, not sure what to do about that *)
  (* (t1 :: asgnG x e) ~ (t' :: asgnG x e) *)

Lemma G_cond_idempotent : forall t b,
    acc_GSubst_id t = acc_GSubst_id (t :: inl (inl b)).
Proof. intros. unfold acc_GSubst_id. unfold acc_GSubst. reflexivity. Qed.

Lemma L_cond_idempotent : forall t b,
    acc_LSubst_id t = acc_LSubst_id (t :: inl (inl b)).
Proof. intros. unfold acc_LSubst_id. unfold acc_LSubst. reflexivity. Qed.

Lemma STrace_Bapply_t_equiv_cong : forall t t' b,
    t ~ t' ->
    Bapply_t t b = Bapply_t t' b.
Proof.
  intros. unfold Bapply_t. destruct H, H0.
  unfold GSub_equiv in H. unfold LSub_equiv in H0.
  extensionality in H. extensionality in H0.
  rewrite H, H0. reflexivity.
Qed.

Lemma STrace_equiv_extend : forall t t' x,
    t ~ t' ->
    (t :: x) ~ (t' :: x).
Proof.
  intros. destruct x. destruct s.
  - unfold STrace_equiv in *. destruct H as [GEquiv [LEquiv PCEquiv]]. splits.
    + repeat (rewrite <- G_cond_idempotent in *). assumption.
    + repeat (rewrite <- L_cond_idempotent in *). assumption.
    + simpl. rewrite andb_true_iff. intro. destruct H.
      rewrite andb_true_iff. split.
      * unfold Bapply_t in *.
        unfold GSub_equiv in GEquiv. extensionality in GEquiv. rewrite <- GEquiv.
        unfold LSub_equiv in LEquiv. extensionality in LEquiv. rewrite <- LEquiv.
        apply H.
      * apply PCEquiv. assumption.
    + simpl. rewrite andb_true_iff. intro. destruct H.
      rewrite andb_true_iff. split.
      * unfold Bapply_t in *.
        unfold GSub_equiv in GEquiv. extensionality in GEquiv. rewrite GEquiv.
        unfold LSub_equiv in LEquiv. extensionality in LEquiv. rewrite LEquiv.
        apply H.
      * apply PCEquiv. assumption.
  - destruct p. unfold STrace_equiv in *.
    unfold acc_GSubst_id in *. unfold acc_LSubst_id in *.
    unfold GSub_equiv in *. unfold LSub_equiv in *.
    destruct H, H0. splits; intro.
    + extensionality in H. extensionality in H0. simpl. rewrite H, H0. reflexivity.
    + simpl. apply H0.
    + simpl in *. apply H1. apply H2.
    + simpl in *. apply H1. apply H2.
  - destruct p. unfold STrace_equiv in *.
    unfold acc_GSubst_id in *. unfold acc_LSubst_id in *.
    unfold GSub_equiv in *. unfold LSub_equiv in *.
    destruct H, H0. splits; intro.
    + simpl. apply H.
    + extensionality in H. extensionality  in H0. simpl. rewrite H, H0. reflexivity.
    + simpl in *. apply H1. apply H2.
    + simpl in *. apply H1. apply H2.
Qed.

Lemma STrace_equiv_continue : forall s s' t0 t0' t G0 L0,
    t0 ~ t0' ->
    (s, t0) ->* (s', t) ->
    Beval G0 L0 (pc t) = true ->
      exists t', t ~ t'
            /\ Beval G0 L0 (pc t') = true
            /\ (s, t0') ->* (s', t').
Proof.
  intros. dependent induction H0.
  - exists t0'. split.
    + assumption.
    + split.
      * apply STrace_pc_equiv_cong with (t := t); assumption.
      * apply rtn1_refl.
  - inversion H1; subst.
    + (* global assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=G e ; s'}> t0 t1) as [t' [IHEquiv [IHpc IHComp]]];
        try reflexivity; try assumption.
      exists (t' :: asgnG x e). split.
      * apply STrace_equiv_extend. assumption.
      * split.
        ** simpl. apply IHpc.
        ** eapply Relation_Operators.rtn1_trans. apply SGAsgn_step. apply IHComp.
    + (* local assignment *)
      destruct (IHclos_refl_trans_n1 s <{ x :=L e ; s'}> t0 t1) as [t' [IHEquiv [IHpc IHComp]]];
        try reflexivity; try assumption.
      exists (t' :: asgnL x e). split.
      * apply STrace_equiv_extend. assumption.
      * split.
        ** simpl. apply IHpc.
        ** eapply Relation_Operators.rtn1_trans. apply SLAsgn_step. apply IHComp.
    + (* proc *)
      destruct (IHclos_refl_trans_n1 s <{ proc(u){body}(e) ; s0}> t0 t2) as [t' [IHEquiv [IHpc IHComp]]];
        try reflexivity; try assumption.
      exists (t' :: asgnL y0 e). split.
      * apply STrace_equiv_extend. assumption.
      * split.
        ** simpl. apply IHpc.
        ** eapply Relation_Operators.rtn1_trans. apply SProc_step. exact []. apply IHComp.
    + (* return *)
      destruct (IHclos_refl_trans_n1 s <{ return ; s'}> t0 t) as [t' [IHEquiv [IHpc IHComp]]];
        try reflexivity; try assumption.
      exists t'. split.
      * assumption.
      * split.
        ** assumption.
        ** eapply Relation_Operators.rtn1_trans. apply SReturn_step. apply IHComp.
    + (* if true *)
      simpl in H2. apply andb_true_iff in H2. destruct H2.
      destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0}> t0 t1) as [t' [IHEquiv [IHpc IHComp]]];
        try reflexivity; try assumption.
      exists (t' :: cond b). split.
      * apply STrace_equiv_extend. assumption.
      * split.
        ** simpl. apply andb_true_iff. split;
             [rewrite STrace_Bapply_t_equiv_cong with (t' := t1);
              [assumption | apply STrace_equiv_sym; assumption]
             | assumption ].
        ** eapply Relation_Operators.rtn1_trans. apply SIfTrue_step. apply IHComp.
    + (* if false *)
      simpl in H2. apply andb_true_iff in H2. destruct H2.
      destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0}> t0 t1) as [t' [IHEquiv [IHpc IHComp]]];
        try reflexivity; try assumption.
      exists (t' :: cond <{~ b}>). split.
      * apply STrace_equiv_extend. assumption.
      * split.
        ** simpl. apply andb_true_iff. rewrite negb_true_iff in *. split.
           *** destruct IHEquiv, H5. unfold GSub_equiv in *. unfold LSub_equiv in *.
               extensionality in H4. extensionality in H5.
               rewrite <- H4, <- H5. assumption.
           *** assumption.
      ** eapply Relation_Operators.rtn1_trans. apply SIfFalse_step. apply IHComp.
    + (* while true *)
      simpl in H2. apply andb_true_iff in H2. destruct H2.
      destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'0}> t0 t1) as [t' [IHEquiv [IHpc IHComp]]];
        try reflexivity; try assumption.
      exists (t' :: cond b). split.
      * apply STrace_equiv_extend. assumption.
      * split.
        ** simpl. apply andb_true_iff. split;
             [rewrite STrace_Bapply_t_equiv_cong with (t' := t1);
              [assumption | apply STrace_equiv_sym; assumption]
             | assumption ].
      ** eapply Relation_Operators.rtn1_trans. apply SWhileTrue_step. apply IHComp.
    + (* while false *)
      simpl in H2. apply andb_true_iff in H2. destruct H2.
      destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'}> t0 t1) as [t' [IHEquiv [IHpc IHComp]]];
        try reflexivity; try assumption.
      exists (t' :: cond <{~b}>). split.
      * apply STrace_equiv_extend. assumption.
      * split.
        ** simpl. apply andb_true_iff. rewrite negb_true_iff in *. split.
           *** destruct IHEquiv, H5. unfold GSub_equiv in *. unfold LSub_equiv in *.
               extensionality in H4. extensionality in H5.
               rewrite <- H4, <- H5. assumption.
           *** assumption.
      ** eapply Relation_Operators.rtn1_trans. apply SWhileFalse_step. apply IHComp.
Qed.

Theorem correctness_reduced : forall s s' t0 t t0' G0 L0,
    (s, t0) ->* (s', t) ->
    Beval G0 L0 (pc t) = true ->
    correctness_prefix_condition t0 G0 L0 ->
    t0 ~ t0' ->
    exists t0' t', @multi_Cstep G0 L0 (s, t0') (s', t')
          /\ acc_GVal G0 L0 t' = GComp G0 L0 (acc_GSubst_id t)
          /\ acc_LVal G0 L0 t' = LComp G0 L0 (acc_LSubst_id t).
Proof.
  intros.
  destruct (STrace_equiv_continue s s' t0 t0' t G0 L0 H2 H H0)
  as [t' [HEquiv [Hpc HComp]]].
  apply STrace_correct_equiv_cong with (t' := t0') in H1;
    try assumption.
  destruct (correctness s s' t0' t' G0 L0 HComp Hpc H1) as [ct0 [ct [HCComp [HG HL]]]].
  destruct HEquiv as [GEquiv [LEquiv _]].
  unfold GSub_equiv in GEquiv. extensionality in GEquiv.
  unfold LSub_equiv in LEquiv. extensionality in LEquiv.
  exists ct0. exists ct. splits;
    [ apply HCComp
    | rewrite GEquiv; assumption
    | rewrite LEquiv; assumption].
Qed.

(** On extensions and computations *)
(* not sure if or when this will ever be useful *)
Definition S_is_extension (t0 t:STrace) := exists t', t = t0 ++ t'.
Definition C_is_extension (t0 t:CTrace) := exists t', t = t0 ++ t'.

Lemma STrace_extends : forall s s' t0 t,
    (s, t0) ->* (s', t) ->
    S_is_extension t0 t.
Proof.
  intros. dependent induction H.
  - exists []. reflexivity.
  - inversion H; subst.
    + destruct (IHclos_refl_trans_n1 s <{ x :=G e ; s' }> t0 t1);
        try reflexivity.
      exists (x0 :: asgnG x e). rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ x :=L e ; s' }> t0 t1);
        try reflexivity.
      exists (x0 :: asgnL x e). rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ proc(u){body}(e) ; s0 }> t0 t2);
        try reflexivity.
      exists (x :: asgnL y0 e). rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ return ; s' }> t0 t);
        try reflexivity.
      exists x. rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0 }> t0 t1);
        try reflexivity.
      exists (x :: cond b). rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0 }> t0 t1);
        try reflexivity.
      exists (x :: cond <{~ b}>). rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'0 }> t0 t1);
        try reflexivity.
      exists (x :: cond b). rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s' }> t0 t1);
        try reflexivity.
      exists (x :: cond <{~ b}>). rewrite H1. reflexivity.
Qed.

Lemma CTrace_extends : forall s s' t0 t G0 L0,
    @multi_Cstep G0 L0 (s, t0) (s', t) ->
    C_is_extension t0 t.
Proof.
  intros. dependent induction H.
  - exists []. reflexivity.
  - inversion H; subst.
    + destruct (IHclos_refl_trans_n1 s <{ x :=G e ; s' }> t0 t1);
        try reflexivity.
      exists (x0 :: inl (x, Aeval_t G0 L0 t1 e)).
      rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ x :=L e ; s' }> t0 t1);
        try reflexivity.
      exists (x0 :: inr (x, Aeval_t G0 L0 t1 e)).
      rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ proc(u){body}(e) ; s'0 }> t0 t1);
        try reflexivity.
      exists (x :: inr (y0, Aeval_t G0 L0 t1 e)). rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ return ; s' }> t0 t);
        try reflexivity.
      exists x. rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0 }> t0 t);
        try reflexivity.
      exists x. rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ if b {s1}{s2} ; s0 }> t0 t);
        try reflexivity.
      exists x. rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s'0 }> t0 t);
        try reflexivity.
      exists x. rewrite H1. reflexivity.
    + destruct (IHclos_refl_trans_n1 s <{ while b {s0} ; s' }> t0 t);
        try reflexivity.
      exists x. rewrite H1. reflexivity.
Qed.
