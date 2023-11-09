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

From SymEx Require Import ContextReduction.

Section AbstractMerge.
  Variable concStep: relation (Valuation * Stmt).
  Variable symbStep: relation (sub * Bexpr * Stmt).

  (* for if-then-else we actually need more stuff here *)
  (* specifically b *)
  Variable mergeStates: sub -> sub -> sub.
  Variable mergePCs: Bexpr -> Bexpr -> Bexpr.

  Variable mergeAllowed: (sub * Bexpr) -> (sub * Bexpr) -> Prop.

  Definition mergeSound: (sub -> sub -> sub) ->
                         (Bexpr -> Bexpr -> Bexpr) ->
                         ((sub * Bexpr) -> (sub * Bexpr) -> Prop)
                         -> Prop.
  Admitted. (* figure out what this has to be *)
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

  Variable mergeIsSound: mergeSound mergeStates mergePCs mergeAllowed.

  Definition concStar := clos_refl_trans_n1 _ concStep.

  Notation " c '->s' c'" := (symbStep c c') (at level 40).
  Notation " c '=>c' c'" := (concStep c c') (at level 40).
  Notation " c '=>*' c'" := (concStar c c') (at level 40).

  Inductive symbStar: relation (sub * Bexpr * Stmt) :=
  | multi_refl: forall sig phi s, symbStar (sig, phi, s) (sig, phi, s)
  | multi_step: forall sig0 sig sig' phi0 phi phi' s0 s s',
      symbStar (sig0, phi0, s0) (sig, phi, s) ->
      symbStep (sig, phi, s) (sig', phi', s') ->
      symbStar (sig0, phi0, s0) (sig', phi', s')
  | multi_merge: forall sig0 sig sig' phi0 phi phi' s0 s,
      symbStar (sig0, phi0, s0) (sig, phi, s) ->
      symbStar (sig0, phi0, s0) (sig', phi', s) ->
      mergeAllowed (sig, phi) (sig', phi') ->
      symbStar (sig0, phi0, s0) (mergeStates sig sig', mergePCs phi phi', s).

  (* this is an abuse of notation, since it's more than the refl/trans closure *)
  (* maybe use \ast or the name of the merge strat. *)
  Notation " c '->*' c'" := (symbStar c c') (at level 40).

  Theorem correctness : forall s s' sig phi V,
      (id_sub, BTrue, s) ->* (sig, phi, s') ->
      exists V' phi',
        V' = (Comp V sig)
        /\ (forall V, Beval V phi = Beval V phi')
        /\ (Beval V phi' = true -> (V, s) =>* (V', s')).
  Proof.
    intros. dependent induction H.
    (* assume this holds for refl/trans closure *)
    - admit.
    - admit.
    (* the interesting merge case *)
    - destruct (IHsymbStar1 mergeIsSound _ _ _ _ JMeq_refl eq_refl) as (V1' & phi1' & ? & ? & ?).
      destruct (IHsymbStar2 mergeIsSound _ _ _ _ JMeq_refl eq_refl) as (V' & phi'' & ? & ? & ?).
