From Coq Require Import String Bool Datatypes Relations Program.Equality Classes.RelationClasses.
From SymEx Require Import Expr Maps.
Import BasicExpr BasicMaps.

Inductive trace (A : Type) : Type :=
| Tnil : trace A
| Tcons : trace A -> A -> trace A.

Arguments Tnil {A}.
Arguments Tcons {A} a l.

Declare Scope trace_scope.
Infix "::" := Tcons (at level 60, right associativity) : trace_scope.
Notation "[ ]" := Tnil (format "[ ]") : trace_scope.
Notation "[ x ]" := (Tcons Tnil x) : trace_scope.
Notation "[ x ; .. ; y ; z ]" := (Tcons (Tcons .. (Tcons Tnil x) .. y) z)
  (format "[ '[' x ; '/' .. ; '/' y ; '/' z ']' ]") : trace_scope.

Open Scope trace_scope.

Lemma cons_eq {A:Type} (x y:trace A) : forall a b, x::a = y::b -> x = y /\ a = b.
Proof. intros. induction x; inversion H; subst; split; reflexivity. Qed.

Fixpoint app {A:Type} (xs ys:trace A) : trace A :=
  match ys with
  | [] => xs
  | ys :: y => (app xs ys) :: y
  end.

Notation "x '++' y" := (app x y) : trace_scope.

Theorem app_nil_l {A:Type} (x:trace A) : [] ++ x = x.
Proof. induction x. reflexivity. simpl. rewrite IHx. reflexivity. Qed.

Theorem app_nil_r {A:Type} (x:trace A) : x ++ [] = x.
Proof. reflexivity. Qed.

Theorem app_comm_cons {A:Type} (a:A) (x y:trace A) : (x ++ y) :: a = x ++ (y :: a).
Proof. reflexivity. Qed.

Theorem app_assoc {A:Type} (x y z:trace A) : x ++ y ++ z = (x ++ y) ++ z.
Proof.
  induction z.
  - reflexivity.
  - simpl. rewrite IHz. reflexivity.
Qed.

Lemma cons_not_empty {A:Type} (a:A) (t:trace A) : t :: a <> [].
Proof.
  intros. induction t.
  - discriminate.
  - discriminate.
Qed.

Lemma not_empty_cons {A:Type} (t:trace A) : t <> [] -> exists a t', t = t'::a.
Proof.
  intros. destruct t.
  - exfalso. apply H. reflexivity.
  - exists a. exists t. reflexivity.
Qed.

Theorem app_eq_nil {A:Type} (x y:trace A) : x ++ y = [] -> x = [] /\ y = [].
Proof.
  induction y; induction x; intro; split;
    try (rewrite app_nil_r in H);
    try (rewrite app_nil_l in H);
    try reflexivity;
    try assumption;
    discriminate.
Qed.

Theorem cons_neq {A:Type} (x:trace A) (y:A) : x::y <> x.
Proof. induction x.
       - apply cons_not_empty.
       - intro. inversion H; subst. exact (IHx H1).
Qed.

Theorem cons_neq' {A:Type} (x:trace A) (y:A) : x <> x::y.
Proof. intro. symmetry in H. exact (cons_neq _ _  H). Qed.

Lemma peel_off' {A:Type} (t:trace A) (a:A) : exists x t', t::a = [x] ++ t'.
Proof.
  intros. induction t.
  - exists a. exists []. reflexivity.
  - destruct IHt as [x [t' IH]]. destruct t'; inversion IH; subst.
    + exists a0. exists [x]. reflexivity.
    + exists x. exists ((t' :: a0 ):: a1). reflexivity.
Qed.

Theorem peel_off {A:Type} (t:trace A) : t <> [] -> exists x t', t = [x] ++ t'.
Proof.
  intros. destruct (not_empty_cons _ H) as [x [t' H']].
  rewrite H'. apply peel_off'.
Qed.

(* generic equivalence stuff *)
Inductive permute_events {X: Type} (IF: relation X): relation (trace X) :=
  | pe_refl: forall t, permute_events IF t t
  | pe_sym: forall t t', permute_events IF t t' -> permute_events IF t' t
  | pe_trans: forall t1 t2 t3,
      permute_events IF t1 t2 -> permute_events IF t2 t3 -> permute_events IF t1 t3
  | pe_interference_free: forall t t' e1 e2,
      IF e1 e2 ->
      permute_events IF ((((t :: e1) :: e2)) ++ t') ((((t :: e2) :: e1)) ++ t')
.

Global Instance trace_eq_refl {X: Type} {r: relation X}: Reflexive (permute_events r).
Proof. intro. apply pe_refl. Qed.

Global Instance trace_eq_sym {X: Type} {r: relation X}: Symmetric (permute_events r).
Proof. intro. apply pe_sym. Qed.

Global Instance trace_eq_trans {X: Type} {r: relation X}: Transitive (permute_events r).
Proof. intro. apply pe_trans. Qed.

Lemma path_equiv_extend {X:Type}: forall r t t' (x: X),
    permute_events r t t' -> permute_events r (t :: x) (t' :: x).
Proof.
  intros. induction H.
  - reflexivity.
  - symmetry. assumption.
  - transitivity (t2::x); assumption.
  - rewrite 2 app_comm_cons. apply pe_interference_free. assumption.
Qed.

Module TraceSemantics.
  (** Symbolic *)
  Definition Var: Type := string.

  Inductive trace_step__S : Type :=
  | Asgn__S (x:Var) (e:Aexpr)
  | Cond (b:Bexpr).

  Definition trace__S := trace trace_step__S.

  Fixpoint acc_subst (s0:sub) (t:trace__S) : sub :=
    match t with
    | [] => s0
    | t :: Asgn__S x e => let s := acc_subst s0 t in
                      (x !-> Aapply s e ; s)
    | t :: _ => acc_subst s0 t
    end.

  Definition Aapply_t (t:trace__S) (e:Aexpr) : Aexpr :=
    Aapply (acc_subst id_sub t) e.

  Definition Bapply_t (t:trace__S) (e:Bexpr) : Bexpr :=
    Bapply (acc_subst id_sub t) e.

  Fixpoint pc (t:trace__S) : Bexpr :=
    match t with
    | [] => BTrue
    | t :: Cond b => BAnd (Bapply_t t b) (pc t)
    | t :: _ => pc t
    end.

  (** Concrete *)
  Definition trace__C := trace (Var * Aexpr).

  Fixpoint acc_val (V0:Valuation) (t:trace__C) : Valuation :=
    match t with
    | [] => V0
    | t :: (x, e) => let V := acc_val V0 t in
                   (x !-> Aeval V e ; V)
    end.

  Definition Aeval_t (V0:Valuation) (t:trace__C) (e:Aexpr) : nat :=
    Aeval (acc_val V0 t) e.

  Definition Beval_t (V0:Valuation) (t:trace__C) (e:Bexpr) : bool :=
    Beval (acc_val V0 t) e.

  Definition is_abstraction (V0:Valuation) (t:trace__C) (t':trace__S) : Prop :=
    Beval V0 (pc t') = true /\ Comp V0 (acc_subst id_sub t') = acc_val V0 t.

  Fixpoint Apply_t (s: sub) (t: trace__S) : trace__S :=
    match t with
    | [] => []
    | xs :: Asgn__S x e => Apply_t s xs :: Asgn__S x (Aapply s e)
    | xs :: Cond e => Apply_t s xs :: Cond (Bapply s e)
    end.

  (* Path Equivalence Conditions *)
  Definition sim_subst (r: relation trace_step__S) :=
    forall s x x' e e',
        r (Asgn__S x e) (Asgn__S x' e') ->
        (x' !-> Aapply (x !-> Aapply s e; s) e'; x !-> Aapply s e; s)
      = (x !-> Aapply (x' !-> Aapply s e'; s) e; x' !-> Aapply s e'; s).

  Definition subst_bapply (r: relation trace_step__S) :=
    forall x e b s, r (Asgn__S x e) (Cond b) ->
      Bapply (x !-> Aapply s e; s) b = Bapply s b.

  (* if r allows simultaneous substitution, then equiv_acc_subst *)
  Theorem equiv_acc_subst_generic (r: relation trace_step__S) (sim_subst: sim_subst r):
    forall s t t',
      permute_events r t t' -> acc_subst s t = acc_subst s t'.
  Proof.
    intros s t t' equiv. induction equiv;
      try auto.
    - rewrite IHequiv1. apply IHequiv2.
    - induction t'.
      + destruct e1, e2;
          try reflexivity.
        apply sim_subst. apply H.
      + destruct a; simpl;
          rewrite IHt'; auto.
  Qed.

  (* if r additionally respects subst_bapply we get equiv_pc*)
  Theorem equiv_pc_generic (r: relation trace_step__S) (sym: Symmetric r) (sim_subst: sim_subst r) (subst_bapply: subst_bapply r):
    forall V t t', permute_events r t t' -> Beval V (pc t) = true <-> Beval V (pc t') = true.
  Proof.
    intros.
    induction H.
    - reflexivity.
    - symmetry. apply IHpermute_events.
    - rewrite IHpermute_events1. apply IHpermute_events2.
    - induction t'.
      + destruct e1, e2.
        * reflexivity.
        * simpl. unfold Bapply_t. simpl.
          rewrite (subst_bapply _ _ _ _ H). reflexivity.
        * simpl. unfold Bapply_t. simpl. symmetry in H.
          rewrite (subst_bapply _ _ _ _ H). reflexivity.
        * simpl. unfold Bapply_t. simpl.
          rewrite 2 andb_assoc.
          rewrite (andb_comm (Beval V (Bapply (acc_subst id_sub t) b0))).
          reflexivity.
      + destruct a; simpl.
        * apply IHt'.
        * unfold Bapply_t.
          assert (IHequiv: permute_events r (((t :: e1) :: e2) ++ t') (((t :: e2) :: e1) ++ t'))
            by (apply pe_interference_free; assumption).
          rewrite (equiv_acc_subst_generic r sim_subst _ _ _ IHequiv).
          rewrite 2 andb_true_iff. rewrite IHt'. reflexivity.
  Qed.

  Definition sim_subst__C (r: relation (Var * Aexpr)) :=
    forall V x x' e e',
        r (x, e) (x', e') ->
        (x' !-> Aeval (x !-> Aeval V e ; V) e'; x !-> Aeval V e; V)
      = (x !-> Aeval (x' !-> Aeval V e'; V) e; x' !-> Aeval V e'; V).

  Theorem equiv_acc_val_generic (r: relation (Var * Aexpr)) (sim_subst: sim_subst__C r):
    forall V t t', permute_events r t t' -> acc_val V t = acc_val V t'.
  Proof.
    intros. induction H;
      try auto.
    - rewrite IHpermute_events1. apply IHpermute_events2.
    - induction t'.
      + destruct e1, e2; simpl.
        apply sim_subst. apply H.
      + destruct a; simpl. rewrite IHt'. reflexivity.
  Qed.

End TraceSemantics.
