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

Section AbstractMerge.
  Parameter concStar: relation (Valuation * Stmt).
  Parameter symbStar: relation (sub * Bexpr * Stmt).

  Parameter symbStar_correct: forall s s' sig phi V,
      symbStar (id_sub, BTrue, s) (sig, phi, s') ->
      Beval V phi = true ->
      concStar (V, s) (Comp V sig, s').

  Parameter symbStar_complete: forall s s' V0 V,
      concStar (V0, s) (V, s') ->
      exists sig phi, symbStar (id_sub, BTrue, s) (sig, phi, s')
                 /\ Beval V0 phi = true
                 /\ V = Comp V0 sig.

  (* for if-then-else we actually need more stuff here *)
  (* specifically b *)
  Parameter merge: (sub * Bexpr) -> (sub * Bexpr) -> (sub * Bexpr).
  Parameter mergeAllowed: (sub * Bexpr) -> (sub * Bexpr) -> bool.

  Definition pc_weaker (b1 b2: Bexpr): Prop := forall V, Beval V b1 = true -> Beval V b2 = true.
  Definition abstracts (V0: Valuation) (sig: sub) (V:Valuation): Prop := V = Comp V0 sig.

  Definition mergeSound: ((sub * Bexpr) -> (sub * Bexpr) -> (sub * Bexpr)) ->
                         ((sub * Bexpr) -> (sub * Bexpr) -> bool)
                         -> Prop :=
    fun merge allowed => forall V0 V V' sig phi sig' phi',
        allowed (sig, phi) (sig', phi') = true ->
        abstracts V0 sig V ->
        abstracts V0 sig' V' ->
        let (sig_merged, phi_merged) := merge (sig, phi) (sig', phi') in
        pc_weaker phi_merged phi /\ pc_weaker phi_merged phi' /\
          abstracts V0 sig_merged V /\ abstracts V0 sig_merged V'.

  (*
    we could make a very strict and obvious choice:
    if mergeAllowed, then the result is correct
    but that seems lazy – and also might require knowledge of previous computations

    we could try to do an order-theoretic thing:
    define a semilattice on symbolic states and require that a merge is the join?
    define a partial order and require that the merge is greater than both inputs?
    this might not be precise

    on that note, maybe there should be a mergeSound and a mergeComplete which imply correctness and completeness separately
    – it seems like KeY folks are interested in this style

    actually, if the refl/trans closure is complete then so is the merged version
    since we only describe *permissible* merges, we cannot make it incomplete

maybe this is an avenue for Arthur-style bug-search
   *)

  Inductive symb_merge: relation (sub * Bexpr * Stmt) :=
  | symb_merge_rt: forall sig0 sig phi0 phi s0 s,
      symbStar (sig0, phi0, s0) (sig, phi, s) ->
      symb_merge (sig0, phi0, s0) (sig, phi, s)
  | symb_merge_merge: forall sig0 sig sig' phi0 phi phi' s0 s,
      symb_merge (sig0, phi0, s0) (sig, phi, s) ->
      symb_merge (sig0, phi0, s0) (sig', phi', s) ->
      mergeAllowed (sig, phi) (sig', phi') = true ->
      symb_merge (sig0, phi0, s0) (merge (sig, phi) (sig', phi'), s).

  Notation " c '->m' c'" := (symb_merge c c') (at level 40).
  Notation " c '=>*' c'" := (concStar c c') (at level 40).

  Theorem correctness (mSound: mergeSound merge mergeAllowed) :
    forall s s' sig phi V,
      (id_sub, BTrue, s) ->m (sig, phi, s') ->
      Beval V phi = true ->
      (V, s) =>* (Comp V sig, s').
  Proof.
    intros. dependent induction H.
    - apply (symbStar_correct s s' sig phi V H H0).
    (* the interesting merge case *)
    - specialize (IHsymb_merge1 _ _ _ _ JMeq_refl eq_refl).
      (* specialize (IHsymb_merge2 _ _ _ _ JMeq_refl eq_refl). *)
      assert (abstracts V sig1 (Comp V sig1)) by easy.
      assert (abstracts V sig' (Comp V sig')) by easy.
      specialize (mSound V (Comp V sig1) (Comp V sig') sig1 phi1 sig' phi' H1 H3 H4).
      rewrite x in mSound. destruct mSound as (? & ? & ? & ?).
      rewrite <- H7. apply IHsymb_merge1.
      apply H5. assumption.
  Qed.
  (* mergeSound is a bit ad-hoc, and I don't like the assymmetry of considering only one branch *)
End AbstractMerge.

From SymEx Require Import IfThenElseMerge.
(* ite as an instance of this abstract merge? *)
