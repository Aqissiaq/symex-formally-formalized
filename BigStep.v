From Coq Require Import
                 Strings.String
                 Bool.Bool
                 Init.Datatypes
                 Lists.List
                 Psatz
                 ZArith
                 Ensembles
                 Classes.RelationClasses.

From SymEx Require Import Expr.
Import BasicExpr.

From SymEx Require Import Maps.
Import BasicMaps.

From SymEx Require Import While.
Open Scope com_scope.

(** Trying the Nakata & Uustalu approach (functional big-step concrete/symbolic semantics)*)

CoInductive trace {X:Type}: Type :=
| TNil: X -> @trace X
| TCons: X -> @trace X -> @trace X.

CoInductive infinite {X:Type}: @trace X -> Prop :=
  | inf_intro: forall t x, infinite t -> infinite (TCons x t).

CoInductive trace_bisim {X: Type}: @trace X -> @trace X -> Prop :=
| bisim_singl: forall x x': X, trace_bisim (TNil x) (TNil x)
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

Definition unfold_trace {X} (t: @trace X): @trace X :=
         match t with
        | TNil x => TNil x
        | TCons x t => TCons x t
         end.

Lemma unfold_id {X}: forall (t: @trace X), t = unfold_trace t.
Proof. destruct t; reflexivity. Qed.

Inductive last_state {X:Type}: @trace X -> X -> Prop :=
| Last: forall x, last_state (TNil x) x
| Not_last:  forall t x x', last_state t x -> last_state (TCons x' t) x.

Lemma last_state_inf {X: Type}: forall t, (~ exists (x: X), last_state t x) -> infinite t.
Proof.
    cofix CH. intros.
    destruct t.
    + exfalso.
      apply H.
      exists x. constructor.
    + constructor.
      apply CH. intro contra.
      apply H. destruct contra as [x0 Hlast].
      exists x0. constructor. apply Hlast.
Qed.

CoFixpoint append {X: Type} (t1 t2: @trace X): @trace X :=
         match t1 with
        | TNil x => TCons x t2
        | TCons x t => TCons x (append t t2)
         end.
Notation " t '+++' t'" := (append t t')
                        (at level 40).

Lemma append_nil {X: Type}: forall (x: X) t, TNil x +++ t = TCons x t.
Proof. intros. rewrite (unfold_id (TNil x +++ t)). reflexivity. Qed.

Lemma append_cons {X: Type}: forall (x: X) t t', TCons x t +++ t' = TCons x (t +++ t').
Proof. intros. rewrite (unfold_id (TCons x t +++ t')). reflexivity. Qed.

CoFixpoint repeat_trace {X:Type} (x: X): @trace X := TCons x (repeat_trace x).

(* Concrete Big-Step Functional Semantics *)
Definition trace__C := @trace Valuation.

CoFixpoint sequence (k: Valuation -> trace__C) (t: trace__C): trace__C :=
  match t with
  (* This makes it so eval <{p ; q}> ~ eval p +++ eval q*)
  | TNil V => TCons V (k V)
  | TCons V t' => TCons V (sequence k t')
  end.

Lemma eval_seq_nil: forall k V, sequence k (TNil V) = TCons V (k V).
Proof. intros. rewrite (unfold_id (sequence k (TNil V))), (unfold_id (TCons V (k V))). reflexivity. Qed.

Lemma eval_seq_cons: forall k V t, sequence k (TCons V t) = TCons V (sequence k t).
Proof. intros. rewrite unfold_id with (t := sequence k (TCons V t)). reflexivity. Qed.

CoFixpoint loop (k: Valuation -> trace__C) (p: Valuation -> bool) (V: Valuation): trace__C :=
  if p V then
    match k V with
    | TNil V' => TCons V' (loop k p V')
    | TCons V' t => TCons V' (loopseq k p t)
    end
  else TNil V
with loopseq (k: Valuation -> trace__C) (p: Valuation -> bool) (t: trace__C): trace__C :=
       match t with
       | TNil V => TCons V (loop k p V)
       | TCons V t' => TCons V (loopseq k p t')
       end.

Lemma loopseq_nil: forall k p V, loopseq k p (TNil V) = TCons V (loop k p V).
Proof. intros. rewrite unfold_id with (t := loopseq k p (TNil V)). reflexivity. Qed.

Lemma loopseq_cons: forall k p V t, loopseq k p (TCons V t) = TCons V (loopseq k p t).
Proof. intros. rewrite unfold_id with (t := loopseq k p (TCons V t)). reflexivity. Qed.

Lemma loopseq_append: forall k p t V, last_state t V -> (loopseq k p t) ~ (t +++ loop k p V).
Proof.
    cofix CH. intros.
    rewrite unfold_id with (t := loopseq k p t).
    rewrite unfold_id with (t := t +++ loop k p V).
    destruct t.
    - inversion H; subst. reflexivity.
    - simpl. constructor.
      apply CH. inversion H; assumption.
Qed.

Fixpoint eval (p:Stmt) (V:Valuation): trace__C :=
  match p with
  | <{skip}> => TNil V
  | <{x := e}> => TNil (x !-> Aeval V e ; V)
  | <{p ; q}> => sequence (eval q) (eval p V)
  | <{if e {p} {q}}> => if Beval V e then eval p V else eval q V
  | <{while e {p}}> => (loop (eval p) (fun V => Beval V e) V)
  end.

(* Ideally I'd have
eval__C (p: Stmt): Valuation -> Valuation := fun V => last_state (eval p V)
but that assumes decidability
 *)

Example ex1: eval <{X := 4}> (_ !-> 0) = TNil (X !-> 4 ; _ !-> 0) := eq_refl.
Example ex2: eval <{X := 4 ; Y := 2}> (_ !-> 0) = TCons (X !-> 4 ; _ !-> 0) (TNil (Y !-> 2 ; X !-> 4 ; _ !-> 0)).
Proof.
    simpl.
    rewrite unfold_id with (t := sequence (fun V : Valuation => TNil (Y !-> 2; V)) (TNil (X !-> 4; _ !-> 0))).
    rewrite unfold_id with (t := (TNil (Y !-> 2; X !-> 4; _ !-> 0))).
    reflexivity.
Qed.
Example ex3: eval <{if X <= 1 {Y := 4} {Y := 2}}> (_ !-> 0) = (TNil (Y !-> 4 ; _ !-> 0)) :=
         eq_refl.
Example ex4: eval <{if X <= 1 {Y := 4} {Y := 2}}> (_ !-> 2) = (TNil (Y !-> 2 ; _ !-> 2)) :=
         eq_refl.
Example ex5: eval <{while X <= 1 {X := X + 1}}> (_ !-> 0)
             = (TCons (X !-> 1 ; _ !-> 0) (TCons (X !-> 2 ; X !-> 1 ; _ !-> 0) (TNil (X !-> 2 ; X !-> 1 ; _ !-> 0)))).
Proof.
    simpl.
    rewrite unfold_id with (t := (loop (fun V => TNil (X !-> V X + 1; V)) (fun V => V X <=? 1) (_ !-> 0))).
    simpl.
    rewrite unfold_id with (t := (loop (fun V => TNil (X !-> V X + 1; V)) (fun V => V X <=? 1) (X !-> 1; _ !-> 0))).
    simpl.
    rewrite unfold_id with (t := (loop (fun V => TNil (X !-> V X + 1; V)) (fun V => V X <=? 1) (X !-> 2; X !-> 1; _ !-> 0))).
    reflexivity.
Qed.

(* note that this is not an equality *)
Example ex6: eval <{while X <= 1 { skip }}> (_ !-> 0) ~ repeat_trace (_ !-> 0).
Proof.
    cofix CH.
    simpl in *.
    rewrite unfold_id with (t := repeat_trace (_ !-> 0)).
    rewrite unfold_id with (t := (loop (fun V => TNil V) (fun V => V X <=? 1) (_ !-> 0))).
    simpl. constructor.
    apply CH.
Qed.

Lemma seq_append': forall t k V,
    last_state t V ->
    sequence k t ~ (t +++ k V).
Proof.
    cofix CH. intros.
    rewrite unfold_id with (t := sequence k t).
    rewrite unfold_id with (t := t +++ k V).
    destruct t.
    - simpl. inversion H; subst.
      reflexivity.
    - simpl. constructor. apply CH.
      inversion H; subst. apply H3.
Qed.

Lemma seq_append: forall p1 p2 V V',
    last_state (eval p1 V) V' ->
    (sequence (eval p2) (eval p1 V)) ~ ((eval p1 V) +++ (eval p2 V')).
Proof. intros.
       apply seq_append'.
       apply H.
Qed.

Lemma seq_append_eval: forall p1 p2 V V',
    last_state (eval p1 V) V' ->
    (eval <{p1 ; p2}> V) ~ ((eval p1 V) +++ (eval p2 V')).
Proof. intros. simpl. apply seq_append. assumption. Qed.

Example loop_sanity_ex: eval <{while X <= 1 {X := X + 1}}> (_ !-> 0)
                     = eval <{if X <= 1 {X := X + 1} {skip} ; while X <= 1 {X := X + 1}}> (_ !-> 0).
Proof.
    simpl.
    rewrite unfold_id with (t := loop (fun V : Valuation => TNil (X !-> V X + 1; V)) (fun V : Valuation => V X <=? 1) (_ !-> 0)).
    rewrite unfold_id with (t := sequence (fun V : Valuation => loop (fun V0 : Valuation => TNil (X !-> V0 X + 1; V0)) (fun V0 : Valuation => V0 X <=? 1) V) (TNil (X !-> 1; _ !-> 0))).
    simpl.
    reflexivity.
Qed.

(* this is not actually true since sequencing adds a stutter step when case is false *)
(* Lemma loop_sanity: forall p e V, *)
(*     eval <{while e {p}}> V ~ eval <{if e {p} {skip} ; while e {p}}> V. *)

(*The same approach will not work for symbolic execution because non-determinism
  in "Coinductive Big-Step Semantics for Concurrency" they handle non-determinism with resumptions,
  let's do something similar?
 *)
(* this is very C-trees, actually*)
CoInductive tree__S: Type :=
  | ret (_:sub): tree__S
  | delay (_:sub) (_:tree__S): tree__S
  | choice (_: Bexpr) (_ _: tree__S): tree__S.

Lemma unfold_tree: forall t,
    t = match t with
       | ret s => ret s
       | delay s t' => delay s t'
       | choice b t1 t2 => choice b t1 t2
        end.
Proof. intros. destruct t; reflexivity. Qed.

CoInductive tree_bisim: tree__S -> tree__S -> Prop :=
  | ret_bisim: forall s, tree_bisim (ret s) (ret s)
  | delay_bisim: forall s t t', tree_bisim t t' -> tree_bisim (delay s t) (delay s t')
  | choice_bisim: forall b t1 t1' t2 t2',
      tree_bisim t1 t1' ->
      tree_bisim t2 t2' ->
      tree_bisim (choice b t1 t2) (choice b t1' t2')
.

Notation " t '~~' t'" := (tree_bisim t t')
                        (at level 40).

CoInductive in_tree__S: tree__S -> sub -> Bexpr -> Prop :=
  | In_leaf: forall s,
      in_tree__S (ret s) s BTrue
  | In_delay: forall s s' b t,
      in_tree__S t s b -> in_tree__S (delay s' t) s b
  | In_left: forall s b b' t1 t2,
      in_tree__S t1 s b -> in_tree__S (choice b' t1 t2) s <{b' && b}>
  | In_right: forall s b b' t1 t2,
      in_tree__S t2 s b -> in_tree__S (choice b' t1 t2) s <{~ b' && b}>
.

CoFixpoint sequence__S (k: sub -> tree__S) (t: tree__S): tree__S :=
         match t with
        | ret s => k s
        | delay s t' => delay s (sequence__S k t')
        | choice b t1 t2 => choice b (sequence__S k t1) (sequence__S k t2)
         end.

CoFixpoint evalbranch__S (p: Stmt) (t: tree__S): tree__S :=
         match t with
        | ret s => ret s
        | delay s t' => delay s (evalbranch__S p t')
        | choice b t1 t2 => choice b (evalbranch__S p t1) (evalbranch__S p t2)
         end.

CoFixpoint loop__S (k: sub -> tree__S) (b: Bexpr) (s: sub): tree__S :=
         choice b
         (match k s with
         | ret s' => delay s' (loop__S k b s')
         | delay s t => delay s (loopseq__S k b t)
         | choice b' t1 t2 => choice b' (loopseq__S k b t1) (loopseq__S k b t2)
          end)
         (ret s)
with loopseq__S (k: sub -> tree__S) (b: Bexpr) (t: tree__S): tree__S :=
       match t with
      | ret s => delay s (loop__S k b s)
      | delay s t' => delay s (loopseq__S k b t')
      | choice b' t1 t2 => choice b' (loopseq__S k b t1) (loopseq__S k b t2)
       end.

Fixpoint eval__S (p:Stmt) (s: sub): tree__S :=
  match p with
  | <{skip}> => ret s
  | <{x := e}> => ret (x !-> Aapply s e ; s)
  | <{p ; q}> => sequence__S (eval__S q) (eval__S p s)
  | <{if e {p} {q}}> => choice e (evalbranch__S q (eval__S p s)) (evalbranch__S p (eval__S q s))
  | <{while e {p}}> => choice e (evalbranch__S SSkip (loop__S (eval__S p) e s)) (ret s)
  end.

Example ex1__S: eval__S <{X := 4}> id_sub = ret (X !-> 4 ; id_sub).
Proof. reflexivity. Qed.

Example ex2__S: eval__S <{X := 4 ; Y := 2}> id_sub = ret (Y !-> 2 ; X !-> 4 ; id_sub).
Proof.
    simpl.
    rewrite unfold_tree with (t := sequence__S (fun s : sub => ret (Y !-> 2; s)) (ret (X !-> 4; id_sub))).
    reflexivity.
Qed.

Example ex3__S: eval__S <{if X <= 1 {Y := 4} {Y := 2}}> id_sub = choice <{X <= 1}> (ret (Y !-> 4 ; id_sub)) (ret (Y !-> 2 ; id_sub)).
Proof.
    simpl.
    rewrite unfold_tree with (t := (evalbranch__S <{ Y := 2 }> (ret (Y !-> 4; id_sub)))).
    rewrite unfold_tree with (t := (evalbranch__S <{ Y := 4 }> (ret (Y !-> 2; id_sub)))).
    reflexivity.
Qed.

Example ex4__S: eval__S <{if X <= 1 {Y := 4 ; Z := 4} {Y := 2} ; X := Y + 1}> id_sub
              = choice <{X <= 1}> (ret (X !-> <{4 + 1}>; Z !-> 4; Y !-> 4 ; id_sub)) (ret (X !-> <{2 + 1}> ; Y !-> 2; id_sub)).
Proof.
    simpl.
    rewrite unfold_tree with (t := sequence__S (fun s : sub => ret (X !-> APlus (s Y) 1; s))
    (choice <{ X <= 1 }> (evalbranch__S <{ Y := 2 }> (sequence__S (fun s : sub => ret (Z !-> 4; s)) (ret (Y !-> 4; id_sub))))
                        (evalbranch__S <{ Y := 4; Z := 4 }> (ret (Y !-> 2; id_sub))))).
    simpl.
    rewrite unfold_tree with (t := (sequence__S (fun s : sub => ret (X !-> APlus (s Y) 1; s))
                                    (evalbranch__S <{ Y := 2 }> (sequence__S (fun s : sub => ret (Z !-> 4; s)) (ret (Y !-> 4; id_sub)))))).
    simpl.
    rewrite unfold_tree with (t := (sequence__S (fun s : sub => ret (X !-> APlus (s Y) 1; s))
                                    (evalbranch__S <{ Y := 4; Z := 4 }> (ret (Y !-> 2; id_sub))))).
    simpl.
    replace ((Z !-> 4 ; Y !-> 4 ; id_sub) Y) with (AConst 4).
    replace ((Y !-> 2; id_sub) Y) with (AConst 2).
    all: reflexivity.
Qed.

(**
CoFixpoint loop_tree (k: sub -> tree__S) (b: Bexpr) (s: sub): tree__S :=
         choice b (loop_tree k b s) (ret s).
(* should update s somehow *)

Example ex5__S: eval__S <{while X <= 1 {X := X + 1}}> id_sub ~~ loop_tree (eval__S <{X := X + 1}>) <{X <= 1}> id_sub.
Proof.
    simpl.
    cofix CH.
    rewrite unfold_tree with (t := (evalbranch__S <{ skip }> (loop__S (fun s : sub => ret (X !-> APlus (s X) 1; s)) <{ X <= 1 }> id_sub))).
    rewrite unfold_tree with (t := (loop__S (fun s : sub => ret (X !-> APlus (s X) 1; s)) <{ X <= 1 }> id_sub)) in *.
    simpl in *.
    rewrite unfold_tree with (t := (evalbranch__S <{ skip }> (ret id_sub))).
    rewrite unfold_tree with (t := loop_tree (fun s => ret (X !-> APlus (s X) 1; s)) <{ X <= 1 }> id_sub).
    simpl. constructor.
    - inversion CH; subst.
      constructor.
    - constructor.
Qed.
*)

Lemma correctness: forall p V F B,
    in_tree__S (eval__S p id_sub) F B ->
    Beval V B = true ->
    last_state (eval p V) (Comp V F).
Proof.
    induction p; intros; simpl.
    - inversion H; subst. rewrite comp_id. apply Last.
    - inversion H; subst.
      rewrite asgn_sound, comp_id. apply Last.
    - admit.
    - inversion H; subst;
        simpl in H0; apply andb_true_iff in H0; destruct H0;
        destruct (Beval V b);
        try discriminate.
      + eapply IHp1.
        apply (IHp1 _ _ _ H6 H1).
      + apply Not_last. apply (IHp2 _ _ _ H6 H1).
    - inversion H; subst.
      + admit. (* bad form of loop *)
      + admit.
      + admit.

Lemma completeness: forall p V V',
    last_state (eval p V) V' ->
    exists F B, in_tree__S (eval__S p id_sub) F B
           /\ V' = Comp V F
           /\ Beval V B = true.
Proof.
    induction p; simpl; intros.
    - exists id_sub. exists BTrue. repeat split.
      + constructor.
      + inversion H; subst. apply comp_id.
    - exists (x !-> Aapply id_sub e; id_sub) . exists BTrue. repeat split.
      + constructor.
      + inversion H; subst.
        rewrite asgn_sound. rewrite comp_id.
        reflexivity.
    - inversion H; subst.
      + rewrite unfold_id with (t := sequence (eval p2) (eval p1 V)) in H1.
        simpl in H1.
