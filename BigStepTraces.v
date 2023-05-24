(** Trying to reimplement the concrete big-step semantics of Nakata & Uustalu *)

From Coq Require Import
                 Strings.String
                 Bool.Bool
                 Init.Datatypes
                 Lists.Streams
                 Classes.RelationClasses
.

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import While.
Open Scope com_scope.

CoInductive trace {X:Type}: Type :=
| TSingl: X -> @trace X
| TCons: X -> @trace X -> @trace X.

CoInductive infinite {X:Type}: @trace X -> Prop :=
  | inf_intro: forall t x, infinite t -> infinite (TCons x t).

CoInductive trace_bisim {X: Type}: @trace X -> @trace X -> Prop :=
| bisim_singl: forall x x': X, trace_bisim (TSingl x) (TSingl x)
| bisim_step: forall t t' x, trace_bisim t t' -> trace_bisim (TCons x t) (TCons x t').

Global Instance trace_bisim_refl {X: Type}: Reflexive (@trace_bisim X).
Proof. cofix CH; intros x; destruct x.
       - constructor. exact x.
       - constructor. apply CH.
Qed.

Global Instance trace_eq_sym {X: Type}: Symmetric (@trace_bisim X).
Proof.
  cofix CH; intros x y H. destruct x, y;
    try (inversion H; subst; assumption).
  inversion H; subst. constructor. apply (CH _ _ H1).
Qed.

Global Instance trace_eq_trans {X: Type}: Transitive (@trace_bisim X).
Proof.
  cofix CH; intros x y z H0 H1. destruct x, y, z;
    try (inversion H0; inversion H1; subst; assumption).
  inversion H1; subst; inversion H0; subst. constructor.
  apply (CH x0 y z H3 H2).
Qed.

Notation " t '~' t'" := (trace_bisim t t')
                          (at level 40).

Lemma unfold_trace {X: Type}:
  forall t:@trace X, t = match t with
                    | TSingl x => TSingl x
                    | TCons x t => TCons x t
                    end.
Proof. intros. destruct t; reflexivity. Qed.

Inductive last_state {X:Type}: @trace X -> X -> Prop :=
| Last: forall x, last_state (TSingl x) x
| NotLast:  forall t x x', last_state t x -> last_state (TCons x' t) x.

Definition trace__S := @trace sub.
Definition trace__C := @trace Valuation.

(* Big-Step Functional Semantics *)
CoFixpoint sequence (k: Valuation -> trace__C) (t: trace__C): trace__C :=
  match t with
  | TSingl V => k V
  | TCons V t' => TCons V (sequence k t')
  end.

CoFixpoint loop (k: Valuation -> trace__C) (p: Valuation -> bool) (V: Valuation): trace__C :=
  if p V then
    match k V with
    | TSingl V' => TCons V' (loop k p V')
    | TCons V' t => TCons V' (loopseq k p t)
    end
  else TSingl V
with loopseq (k: Valuation -> trace__C) (p: Valuation -> bool) (t: trace__C): trace__C :=
       match t with
       | TSingl V => TCons V (loop k p V)
       | TCons V t' => TCons V (loopseq k p t')
       end.

Fixpoint eval (p:Stmt) (V:Valuation) {struct p}: trace__C :=
  match p with
  | <{skip}> => TSingl V
  | <{x := e}> => TCons V (TSingl (x !-> Aeval V e ; V))
  | <{p ; q}> => sequence (eval p) (eval q V)
  | <{if e {p} {q}}> => TCons V (if Beval V e then eval p V else eval q V)
  | <{while e {p}}> => TCons V (loop (eval p) (fun V => Beval V e) V)
  end.

(* Big-Step Relational Semantics *)
Reserved Notation " s , V '==>' t " (at level 40).
Reserved Notation " s , t '==>*' t' " (at level 40).

CoInductive denot__C: Stmt -> Valuation -> trace__C -> Prop :=
| denot_asgn__C: forall x e V,
    <{x := e}> , V ==> TCons V (TSingl (x !-> Aeval V e ; V))
| denot_skip__C: forall V,
    <{skip}>, V ==> TSingl V
| denot_seq__C: forall p q V t t',
    p, V ==> t -> q, t ==>* t' ->
    <{p ; q}>, V ==> t'
| denot_ift__C: forall V e p q t,
    Beval V e = true ->
    p, (TCons V (TSingl V)) ==>* t ->
    <{if e {p} {q}}>, V ==> t
| denot_iff__C: forall V e p q t,
    Beval V e = false ->
    q, (TCons V (TSingl V)) ==>* t ->
    <{if e {p} {q}}>, V ==> t
| denot_whilet__C: forall V e p t t',
    Beval V e = true ->
    p, (TCons V (TSingl V)) ==>* t ->
    <{while e {p}}>, t ==>* t' ->
    <{while e {p}}>, V ==> t'
| denot_whilef__C: forall V e p,
    Beval V e = false ->
    <{while e {p}}>, V ==> TCons V (TSingl V)
where " s , V '==>' t " := (denot__C s V t)
with denot_star__C: Stmt -> trace__C -> trace__C -> Prop :=
| denotNil: forall V p t,
    p, V ==> t -> p, (TSingl V) ==>* t
| denotCons: forall V p t t',
    p, t ==>* t' -> p, (TCons V t) ==>* TCons V t'
where " s , t '==>*' t' " := (denot_star__C s t t') .

Lemma denot_nil__C: forall p V V', denot__C p V (TSingl V') -> V = V'.
Proof.
  induction p; intros V V' H; inversion H; subst; auto.
  (* seq case *)
  - inversion H5; subst.
    rewrite (IHp1 _ _ H2). rewrite (IHp2 _ _ H0).
    reflexivity.
  (* if cases *)
  - inversion H6.
  - inversion H6.
  (* loop case *)
  - inversion H3; subst. inversion H6.
Qed.

Lemma denot_star_deterministic__C: forall p,
    (forall V t t', p, V ==> t -> p, V ==> t' -> t ~ t') ->
    forall t1 t2 t3 t4,
      t1 ~ t2 -> p, t1 ==>* t3 -> p, t2 ==>* t4 -> t3 ~ t4.
Proof.
  intros p H. cofix CH.
  intros ? ? ? ? H1 H2 H3.
  inversion H2; subst.
  - inversion H3; subst;
      inversion H1; subst; apply (H _ _ _ H0 H4).
  - inversion H3; subst;
      inversion H1; subst.
    constructor. apply (CH _ _ _ _ H6 H0 H4).
Qed.

Lemma denot_seq_deterministic__C: forall p q,
    (forall V t t', p, V ==> t -> p, V ==> t' -> t ~ t') ->
    (forall V t t', q, V ==> t -> q, V ==> t' -> t ~ t') ->
    forall V t t',
      <{p;q}>, V ==> t ->
      <{p;q}>, V ==> t' ->
      t ~ t'.
Proof.
  intros. inversion H1; subst; inversion H2; subst.
  specialize (H _ _ _ H5 H6).
  apply (denot_star_deterministic__C _ H0 _ _ _ _ H H8 H10).
Qed.


Lemma denot_loop_star_deterministic__C: forall e p,
  forall t1 t2 t3 t4,
    t1 ~ t2 ->
    <{while e {p}}>, t1 ==>* t3 ->
    <{while e {p}}>, t2 ==>* t4 ->
    t3 ~ t4.
Proof.
  intros e p. cofix CH.
  intros t1 t2 t3 t4 H1 H2 H3.
  inversion H2; subst.
  - inversion H3; subst.
    + inversion H1; subst. inversion H0; subst.
      * inversion H; subst.
Admitted.

Lemma denot_loop_deterministic__C: forall e p,
    (forall V t t', p, V ==> t -> p, V ==> t' -> t ~ t') ->
    forall V t t',
      <{while e {p}}>, V ==> t ->
      <{while e {p}}>, V ==> t' ->
      t ~ t'.
Proof.
  intros e p Hloop. cofix CH.
  assert (CH2: forall t1 t2 t3 t4,
    t1 ~ t2 ->
    <{while e {p}}>, t1 ==>* t3 ->
    <{while e {p}}>, t2 ==>* t4 ->
    t3 ~ t4).
  { cofix CH2. intros t1 t2 t3 t4 h1 h2 h3. inversion h2; subst.
    - inversion h3; subst.
      + inversion h1; subst. inversion H; subst.
        * inversion H0; subst.
          --
        * inversion H; subst.
          --
  }
  intros. inversion H0; subst.
  - inversion H1; subst.
    + eapply (denot_loop_star_deterministic__C e p _ _ _ _ _ H8 H11).
    + admit.
  - inversion H1; subst.
    + inversion H0; subst.
      * eapply (denot_loop_star_deterministic__C e p _ _ _ _ _ H12 H9).
      *
    + admit.
      +

(* Lemma 1: relational evaluation is deterministic up to bisimilarity *)
Theorem denot_deterministic__C: forall V p t t', trace_bisim t t' -> p, V ==> t -> p, V ==> t'.
Proof.
  intros. cofix CH.
  inversion H0; subst.
  -
Qed.
