(** * Context Reduction Basics *)

(** Reformulation of de Boer and Bonsangue's basic setup in the context-reduction setting *)

From Coq Require Import String Bool Datatypes Relations Program.Equality.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import Parallel.

From SymEx Require Import BasicContextReduction.

Definition merge_sub (b: Bexpr) (s1 s2: sub): sub :=
  fun x => AIte b (s1 x) (s2 x).

Lemma merge_sub_true: forall V b s s',
    Beval V b = true -> Comp V (merge_sub b s s') = Comp V s.
Proof.
  intros.
  unfold Comp, merge_sub.
  cbn; rewrite H.
  reflexivity.
Qed.

Lemma merge_sub_false: forall V b s s',
    Beval V b = false -> Comp V (merge_sub b s s') = Comp V s'.
Proof.
  intros.
  unfold Comp, merge_sub.
  cbn; rewrite H.
  reflexivity.
Qed.

Definition separates (p1 p2 b: Bexpr): Prop := forall V,
    (Beval V p1 = true -> Beval V b = true)
    /\ (Beval V p2 = true -> Beval V b = false).

Inductive ite_merge: relation (sub * Bexpr * Stmt) :=
| ite_merge_rt: forall sig0 sig phi0 phi s0 s,
    (sig0, phi0, s0) ->* (sig, phi, s) ->
    ite_merge (sig0, phi0, s0) (sig, phi, s)
| ite_merge_merge: forall sig0 sig sig' phi0 phi phi' s0 s b,
    ite_merge (sig0, phi0, s0) (sig, phi, s) ->
    ite_merge (sig0, phi0, s0) (sig', phi', s) ->
    separates phi phi' b ->
    ite_merge (sig0, phi0, s0) (merge_sub b sig sig', <{phi | phi'}>, s).

Notation " c '->ite' c'" := (ite_merge c c') (at level 40).

Definition pc_equiv (b1 b2: Bexpr): Prop := forall V, Beval V b1 = Beval V b2.

Theorem correctness : forall s s' sig phi V,
    (id_sub, BTrue, s) ->ite (sig, phi, s') ->
    exists V' phi',
      V' = (Comp V sig)
      /\ pc_equiv phi phi'
      /\ (Beval V phi' = true ->
         (V, s) =>* (V', s')).
Proof.
  intros. dependent induction H.
  - specialize (BasicContextReduction.correctness _ _ _ _ V H);
      intro basic_correct.
    exists (Comp V sig), phi. splits. apply basic_correct.
  - destruct (IHite_merge1 _ _ _ _ JMeq_refl eq_refl) as (V1' & phi1' & AbsV1' & pc_equiv1' & Comp1').
    destruct (IHite_merge2 _ _ _ _ JMeq_refl eq_refl) as (V' & phi'' & Abs' & pc_equiv' & Comp').
    exists (Comp V (merge_sub b sig1 sig')).
    exists <{phi1 | phi' }>. splits.
    simpl. intro Hpc. apply orb_true_iff in Hpc.
    destruct Hpc as [phi1_true | phi'_true].
    + (* b separates so this is the b=true case *)
      destruct (H1 V) as (b_true & _).
      rewrite merge_sub_true with (1 := (b_true phi1_true)).
      (* and we have the computation from IH! *)
      rewrite <- AbsV1'.
      rewrite pc_equiv1' in phi1_true.
      apply (Comp1' phi1_true).
    + destruct (H1 V) as (_ & b_false).
      rewrite merge_sub_false with (1 := (b_false phi'_true)).
      rewrite <- Abs'.
      rewrite pc_equiv' in phi'_true.
      apply (Comp' phi'_true).
Qed.

(* generalizing this last argument: *)
(*   goal: if the merged pc holds, then there is a concrete computation reaching the merged state *)

(* in the if-then-else case: split on b since it separates, *)
(*   then use the characterization of merge_sub and induction hypotheses *)

(* in general: pair of states satisfy a merge condition and we have IH(s)
  ==> resulting state is correct *)

Theorem completeness : forall s s' V0 V,
    (V0, s) =>* (V, s') ->
    exists sig phi, (id_sub, BTrue, s) ->ite (sig, phi, s') /\ Beval V0 phi = true /\ V = Comp V0 sig.
Proof.
  intros.
  destruct BasicContextReduction.completeness with (1:=H) as
    (sig & phi & Hrt & ? & ?).
  exists sig, phi. splits;
    try assumption.
  apply ite_merge_rt with (1:=Hrt).
Qed.
(* one potential problem of this approach: *)
(* since we are extending a complete semantics, we cannot define incomplete merge strats *)

(** an example (from Dominique) *)

Fact x_not_y: X <> Y.
Proof. apply String.eqb_neq. trivial. Qed.

Example merge_sub_ex: merge_sub (BLeq Y 1) (Y !-> 2 ; X !-> 1 ; id_sub) (X !-> 4 ; id_sub)
                      = (X !-> AIte (BLeq Y 1) 1 4 ; Y !-> AIte (BLeq Y 1) 2 Y ; merge_sub (BLeq Y 1) id_sub id_sub).
Proof.
  extensionality x. unfold merge_sub, update.
  destruct (String.eqb_spec X x), (String.eqb_spec Y x).
    - rewrite <- e0 in e. apply x_not_y in e. contradiction.
    - reflexivity.
    - rewrite e. reflexivity.
    - reflexivity.
Qed.

Example s0 : Stmt :=<{ if Y <= 1 {X := 1; Y := 2}{X := 4}; Z := 3 }>.
Example if_merge_example:
  (id_sub, BTrue, s0) ->ite (Y !-> 2; X !-> 1; id_sub, <{ Y <= 1 }>, <{ Z := 3 }>)
  -> (id_sub, BTrue, s0) ->ite (X !-> 4; id_sub, <{ ~ Y <= 1 }>, <{ Z := 3 }>) ->
  (id_sub, BTrue, s0) ->ite
    ((X !-> AIte (BLeq Y 1) 1 4 ; Y !-> AIte (BLeq Y 1) 2 Y ; merge_sub (BLeq Y 1) id_sub id_sub),
      <{Y <= 1 | ~ (Y <= 1)}>,
      <{Z := 3}>).
Proof.
  intros. rewrite <- merge_sub_ex.
  eapply ite_merge_merge.
  - assumption.
  - assumption.
  - split; intro.
    + easy.
    + apply negb_true_iff in H1. apply H1.
Qed.

(* huh, this worked surprisingly smoothly, what's next? *)

(* traces? *)
(* seems a lot like allowing equivalent t, but updating pc somehow *)
(* uh-oh what happens to calculated path condition and its monotonicity? *)

(* generalizations *)
(* I don't want a new induction scheme for every merge strategy *)
(* this seems orthogonal to the traces, and I don't love the idea of doing both at the same time *)
