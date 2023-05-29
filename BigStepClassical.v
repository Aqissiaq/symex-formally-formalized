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

(* blæh *)
From Coq Require Import Classical Description.

(* Trick from Leroy *)
Inductive lessdef {A: Type}: option A -> option A -> Prop :=
  | lessdef_none: forall oa, lessdef None oa
  | lessdef_some: forall a, lessdef (Some a) (Some a).

Notation "x <<= y" := (lessdef x y) (at level 70, no associativity).

Lemma lessdef_refl {X:Type}: forall (x:option X), x <<= x.
Proof. destruct x; constructor. Qed.

#[export]
Hint Constructors lessdef : lessdef.

Section LIMIT.

Context {A: Type} (f: nat -> option A).

Hypothesis f_mono: forall i j, i <= j -> f i <<= f j.

Lemma limit_exists:
  { lim : option A | exists i, forall j, i <= j -> f j = lim }.
Proof.
    apply constructive_definite_description.
    destruct (classic (forall i, f i = None)) as [DIV|TERM].
    - exists None; split.
      + exists O; auto.
      + intros lim (i & LIM). rewrite <- (DIV i). apply LIM; lia.
    - apply not_all_ex_not in TERM. destruct TERM as (i & TERM).
      exists (f i); split.
      + exists i; intros. destruct (f_mono i j H). congruence. auto.
      + intros lim (i2 & LIM2). set (j := Nat.max i i2).
        rewrite <- (LIM2 j) by lia.
        destruct (f_mono i j). lia. congruence. auto.
Qed.

Definition limit : option A := proj1_sig limit_exists.

Lemma limit_charact: exists i, forall j, i <= j -> f j = limit.
Proof. unfold limit. apply proj2_sig. Qed.

End LIMIT.

Definition option_bind {X Y: Type} (m : option X) (f: X -> option Y): option Y :=
         match m with None => None | Some x => f x end.

Definition option_lift {X Y: Type} (f: X -> Y): X -> option Y := fun x => Some (f x).

Lemma option_bind_mono: forall (X Y: Type) (x x': option X) (f f': X -> option Y),
    x <<= x' -> (forall x, f x <<= f' x) -> option_bind x f <<= option_bind x' f'.
Proof. intros. destruct H; cbn; auto with lessdef. Qed.

Lemma option_inversion {X Y: Type} {x: option X} {f: X -> option Y} {y: Y}:
    option_bind x f = Some y ->
    exists x', x = Some x' /\ f x' = Some y.
Proof.
    destruct x; simpl; intros.
    - exists x. split; auto.
    - inversion H.
Qed.

Fixpoint loop_fuel__C (fuel: nat) (f: Valuation -> option Valuation) (b: Bexpr) (V: Valuation): option Valuation :=
         match fuel with
        | 0 => None
        | S n => if Beval V b
                then option_bind (f V) (loop_fuel__C n f b)
                else Some V
        end.

Fixpoint loop_count_fuel (fuel count: nat) (f: Valuation -> option Valuation) (b: Bexpr) (V: Valuation): option (Valuation * nat) :=
         match fuel with
        | 0 => None
        | S n => if Beval V b
                then option_bind (f V) (loop_count_fuel n (S count) f b)
                else Some (V, count)
        end.

Lemma loop_mono: forall i j f b V,
    i <= j -> loop_fuel__C i f b V <<= loop_fuel__C j f b V.
Proof.
    induction i; intros; simpl.
    - constructor.
    - destruct j.
      + inversion H.
      + simpl; destruct (Beval V b).
        * apply option_bind_mono.
          -- apply lessdef_refl.
          -- intro. apply IHi. lia.
        * constructor.
Qed.

Lemma loop_count_mono: forall i j n f b V,
    i <= j -> loop_count_fuel i n f b V <<= loop_count_fuel j n f b V.
Proof.
    induction i; intros; simpl.
    - constructor.
    - destruct j.
      + inversion H.
      + simpl; destruct (Beval V b).
        * apply option_bind_mono.
          -- apply lessdef_refl.
          -- intro. apply IHi. lia.
        * constructor.
Qed.

(** Concrete semantics *)
Definition loop__C (f: Valuation -> option Valuation) (b: Bexpr) (V: Valuation) : option Valuation :=
         limit (fun n => loop_fuel__C n f b V) (fun i j => loop_mono i j f b V).

Definition loop_count (f: Valuation -> option Valuation) (b: Bexpr) (V: Valuation) : option (Valuation * nat) :=
         limit (fun n => loop_count_fuel n 0 f b V) (fun i j => loop_count_mono i j 0 f b V).

(*not actually used atm*)
Inductive denot__C: Stmt -> (Valuation -> option Valuation) -> Prop :=
  | denot_skip__C: denot__C <{skip}> (fun V => Some V)
  | denot_asgn__C: forall x e,
      denot__C <{x := e}> (fun V => Some (x !-> Aeval V e; V))
  | denot_seq__C: forall p1 p2 f1 f2,
      denot__C p1 f1 ->
      denot__C p2 f2 ->
      denot__C <{p1 ; p2}> (fun V => option_bind (f1 V) f2)
  | denot_if__C: forall b p1 p2 f1 f2,
      denot__C p1 f1 ->
      denot__C p2 f2 ->
      denot__C <{if b {p1} {p2}}> (fun V => if Beval V b then f1 V else f2 V)
  | denot_loop__C: forall b p f,
      denot__C p f ->
      denot__C <{while b {p}}> (loop__C f b)
.

Fixpoint denot_fun (p: Stmt) (V: Valuation): option Valuation :=
         match p with
        | <{skip}> => Some V
        | <{x := e}> => Some (x !-> Aeval V e ; V)
        | <{p1 ; p2}> => option_bind (denot_fun p1 V) (denot_fun p2)
        | <{if b {p1} {p2}}> => if Beval V b then (denot_fun p1 V) else (denot_fun p2 V)
        | <{while b {p}}> => loop__C (denot_fun p) b V
         end.

(* Characterizing the concrete denotation *)
Lemma loop_charact__C: forall f b V, exists i, forall j, i <= j -> loop_fuel__C j f b V = loop__C f b V.
Proof. intros. apply limit_charact. Qed.

Lemma loop_count_charact: forall f b V, exists i, forall j, i <= j -> loop_count_fuel j 0 f b V = loop_count f b V.
Proof. intros. apply limit_charact. Qed.

Lemma loop_count_none: forall i n f b V,
    loop_fuel__C i f b V = None -> loop_count_fuel i n f b V = None.
Proof.
    induction i; intros; simpl in *.
    - reflexivity.
    - destruct (Beval V b), (f V).
      + simpl in *. apply IHi. apply H.
      + simpl. reflexivity.
      + inversion H.
      + inversion H.
Qed.

Lemma loop_count_increment: forall i n m f b V V',
    loop_count_fuel i n f b V = Some (V', m) <-> loop_count_fuel i (S n) f b V = Some (V', S m).
Proof.
    induction i; split; intros;
      try (simpl in H; inversion H).
    - simpl in *. destruct (Beval V b).
      + destruct (option_inversion H) as [? [? ?]].
        rewrite H0. simpl. rewrite <- IHi. apply H2.
      + inversion H. reflexivity.
    - simpl in *. destruct (Beval V b).
      + destruct (option_inversion H) as [? [? ?]].
        rewrite H0. simpl. rewrite IHi. apply H2.
      + inversion H. reflexivity.
Qed.

Lemma loop_count_correct: forall i f b V V',
    loop_fuel__C i f b V = Some V' -> exists n, loop_count_fuel i 0 f b V = Some (V', n).
Proof.
    induction i; intros.
    - simpl in H. inversion H.
    - simpl in *. destruct (Beval V b), (f V); cbn in *.
      + destruct (IHi _ _ _ _ H) as [n ?].
        exists (S n). rewrite <- loop_count_increment. apply H0.
      + inversion H.
      + inversion H. exists 0. reflexivity.
      + inversion H. exists 0. reflexivity.
Qed.

Lemma loop_unique__C: forall f b V i lim,
    (forall j, i <= j -> loop_fuel__C j f b V = lim) ->
    loop__C f b V = lim.
Proof.
    intros. destruct (loop_charact__C f b V) as [i' LIM].
    set (j := Nat.max i i').
    rewrite <- (H j). rewrite (LIM j). reflexivity.
    all: lia.
Qed.

Lemma loop_count_unique: forall f b V i lim,
    (forall j, i <= j -> loop_count_fuel j 0 f b V = lim) ->
    loop_count f b V = lim.
Proof.
    intros. destruct (loop_count_charact f b V) as [i' LIM].
    set (j := Nat.max i i').
    rewrite <- (H j). rewrite (LIM j). reflexivity.
    all: lia.
Qed.

Lemma denot_seq: forall p1 p2 V,
    denot_fun <{p1 ; p2}> V = option_bind (denot_fun p1 V) (denot_fun p2).
Proof. reflexivity. Qed.

Lemma denot_loop: forall f b V,
    loop__C f b V = if Beval V b then option_bind (f V) (loop__C f b) else Some V.
Proof.
    intros.
    destruct (f V) eqn:H.
    - destruct (loop_charact__C f b v) as [i LIM].
      apply loop_unique__C with (i := (S i)). intros.
      destruct j; [lia|].
      simpl. destruct (Beval V b);
        try reflexivity.
      rewrite H; cbn. apply LIM. lia.
    - destruct (loop_charact__C f b V) as [i LIM].
      apply loop_unique__C with (i := (S i)). intros.
      destruct j; [lia|].
      simpl. destruct (Beval V b);
        [rewrite H|]; reflexivity.
Qed.

Lemma denot_loop_seq: forall p b V,
    denot_fun <{while b {p}}> V = denot_fun <{if b {p ; while b {p}} {skip}}> V.
Proof.
    intros. simpl. rewrite denot_loop.
    destruct (Beval V b); reflexivity.
Qed.

Lemma loop_false: forall f b V, Beval V b = false -> loop__C f b V = Some V.
Proof. intros. rewrite denot_loop. rewrite H. reflexivity. Qed.

Definition option_apply {A B: Type}: option (A -> B) -> A -> option B :=
  fun f a => match f with
          | None => None
          | Some f => Some (f a)
          end.

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
(* this result is annoying, but meh *)

Example branch_example: Stmt := <{
    if X <= 0
           {if 1 <= 0 {X := 42} {X := 0}}
           {if 1 <= 0 {X := 42} {X := 1}}
    }>.

(** Symbolic Semantics *)

Definition Branch: Type := (Valuation -> Valuation) * (Ensemble Valuation).

Definition inverse_image {X: Type} (F: X -> X) (B: Ensemble X): Ensemble X := fun x => B (F x).
Definition denot__B (b: Bexpr): Ensemble Valuation := fun V => Beval V b = true.

Lemma denotB_true: forall V b, In _ (denot__B b) V <-> Beval V b = true.
Proof. split; intros; apply H. Qed.

Search (forall b, b <> true -> b = false).

Lemma denotB_false: forall V b, In _ (Complement _ (denot__B b)) V <-> Beval V b = false.
Proof.
    split; intros.
    - apply (not_true_is_false _ H).
    - unfold Complement, In, denot__B. intro. rewrite H in H0. discriminate.
Qed.

Fixpoint n_fold {X: Type} (n: nat) (f: X -> X): X -> X :=
         match n with
        | 0 => fun x => x
        | S n => fun x => f (n_fold n f x)
         end.

Lemma n_fold_inversion {X:Type}: forall n f (x: X), f (n_fold n f x) = n_fold (S n) f x.
Proof. reflexivity. Qed.

Lemma n_fold_step {X:Type}: forall n f (x y: X), n_fold (S n) f x = y -> exists z, n_fold n f x = z /\ f z = y.
Proof.
    induction n; intros; simpl in *.
    - exists x. split; [reflexivity | apply H].
    - exists (f (n_fold n f x)). split; [reflexivity | apply H].
Qed.

Lemma n_fold_construct {X:Type}: forall n f (x y z: X),
    n_fold n f x = y -> f y = z -> n_fold (S n) f x = z.
Proof.
    induction n; intros; simpl in *.
    - rewrite H. apply H0.
    - rewrite (IHn f x (n_fold n f x) y).
      + assumption.
      + reflexivity.
      + assumption.
Qed.

Definition loop_helper (body: Ensemble Branch) (b: Bexpr) (p: Stmt): Ensemble Branch -> Ensemble Branch :=
       fun big_F => fun X => exists F B Fp Bp,
           In _ big_F (F, B)
           /\ In _ body (Fp, Bp)
           /\ fst X = (fun V => F (Fp V))
           /\ snd X = Intersection _ (denot__B b) (Intersection _ Bp (inverse_image Fp B)).

Lemma loop_helper_step: forall n body b p F B X0,
    In _ (n_fold (S n) (loop_helper body b p) X0) (F, B) ->
    exists F' B', In _ (n_fold n (loop_helper body b p) X0) (F', B')
             /\ loop_helper body b p (Singleton _ (F', B')) (F, B)
.
Proof.
    intros.
    destruct (n_fold_step n (loop_helper body b p) X0 (n_fold (S n) (loop_helper body b p) X0))
      as [Y [H0 H1]]; [reflexivity|].
    destruct H as [F' [B' [Fp [Bp [Hbody [Hloop [tmp0 tmp1]]]]]]].
    simpl in tmp0, tmp1; subst.
    exists F'. exists B'. repeat split.
    - apply Hbody.
    - exists F'. exists B'. exists Fp. exists Bp.
      repeat split. apply Hloop.
Qed.

Inductive Big_Union {X} (Xs: Ensemble (Ensemble X)) : Ensemble X :=
  | Big_U_intro: forall X x, In _ Xs X -> In _ X x -> In _ (Big_Union Xs) x.

Inductive Union_Fam {X I} (Fs: I -> Ensemble X): Ensemble X :=
  | Fam_intro: forall {i x}, In _ (Fs i) x -> In _ (Union_Fam Fs) x.

Fixpoint denot__S (p: Stmt): Ensemble Branch := match p with
        | <{skip}> => Singleton _ (fun V => V, Full_set _)
        | <{x := e}> => Singleton _ (fun V => (x !-> Aeval V e ; V), Full_set _)
        | <{p ; q}> =>
            fun X => exists Fp Fq Bp Bq,
                In _ (denot__S p) (Fp, Bp)
                /\ In _ (denot__S q) (Fq, Bq)
                /\ (fst X = fun V => Fq (Fp V))
                /\ snd X = Intersection _ Bp (inverse_image Fp Bq)
        | <{if b {p} {q}}> =>
            fun X =>
              (exists F B,
                  In _ (denot__S p) (F, B)
                  /\ fst X = F
                  /\ snd X = Intersection _ B (denot__B b))
              \/
                (exists F B,
                    In _ (denot__S q) (F, B)
                    /\ fst X = F
                    /\ snd X = Intersection _ B (Complement _ (denot__B b)))
        | <{while b {p}}> =>
            Union_Fam (fun m => n_fold m (loop_helper (denot__S p) b p) (Singleton _ (fun V => V, Complement _ (denot__B b))))
         end.

Lemma denot_seq__S: forall p1 p2 F1 F2 B1 B2,
    In _ (denot__S p1) (F1, B1) ->
    In _ (denot__S p2) (F2, B2) ->
    In _ (denot__S <{p1 ; p2}>) (fun V => F2 (F1 V), Intersection _ B1 (inverse_image F1 B2)).
Proof.
    intros.
    exists F1. exists F2. exists B1. exists B2.
    repeat split; assumption.
Qed.

Lemma denot_if__S: forall b p1 p2 F1 F2 B1 B2,
    In _ (denot__S p1) (F1, B1) ->
    In _ (denot__S p2) (F2, B2) ->
    In _ (denot__S <{if b {p1} {p2}}>) (F1, Intersection _ B1 (denot__B b))
    /\ In _ (denot__S <{if b {p1} {p2}}>) (F2, Intersection _ B2 (Complement _ (denot__B b))).
Proof.
    intros. split.
    - left. exists F1. exists B1. repeat split. assumption.
    - right. exists F2. exists B2. repeat split. assumption.
Qed.

Lemma denot_while__S': forall b p F B,
    In _ (denot__S p) (F, B) ->
    In _ (denot__S <{while b {p}}>) (fun V => V, Complement _ (denot__B b))
    /\ In _ (denot__S <{while b {p}}>) (F,
       Intersection _ (denot__B b) (Intersection _ B (inverse_image F (Complement _ (denot__B b))))).
Proof.
    intros. split.
    - apply Fam_intro with (i := 0).
      constructor.
    - apply Fam_intro with (i := 1).
      simpl.
      exists (fun V => V). exists (Complement _ (denot__B b)).
      exists F. exists B. repeat split.
      + apply H.
Qed.

Lemma denot_while__S: forall b p F B Floop Bloop,
    In _ (denot__S p) (F, B) ->
    In _ (denot__S <{while b {p}}>) (Floop, Bloop) ->
    In _ (denot__S <{while b {p}}>)
   (fun V => Floop (F V), Intersection _ (denot__B b) (Intersection _ B (inverse_image F Bloop))).
Proof.
    intros. inversion H0; subst.
    apply Fam_intro with (i := S i).
    exists Floop. exists Bloop. exists F. exists B.
    repeat split;
      try assumption.
Qed.

Lemma loop_correct (p: Stmt)
  (IHp : forall (F : Valuation -> Valuation) (B : Ensemble Valuation) (V : Valuation),
      In Branch (denot__S p) (F, B) -> In Valuation B V -> exists V' : Valuation, F V = V' /\ denot_fun p V = Some V'):
  forall n F B b,
    In _ (n_fold n (loop_helper (denot__S p) b p)
         (Singleton _ (fun V => V, Complement _ (denot__B b))))
   (F, B) ->
    forall V,
      In _ B V ->
      loop_fuel__C (S n) (denot_fun p) b V = option_lift F V.
Proof.
    induction n; intros.
    - simpl in *. inversion H; subst.
      rewrite denotB_false in H0. rewrite H0.
      reflexivity.
    - destruct (loop_helper_step _ _ _ _ _ _ _ H) as [? [? [Hsofar Hstep]]].
      destruct Hstep as [F' [B' [Fbody [Bbody [? [? [? ?]]]]]]].
      simpl in H3, H4; subst.
      inversion H1; subst.
      inversion H0; subst.
      rewrite denotB_true in H3.
      specialize (IHn _ _ _ Hsofar (Fbody V)).
      replace (loop_fuel__C (S (S n)) (denot_fun p) b V) with
        (option_bind (denot_fun p V) (loop_fuel__C (S n) (denot_fun p) b)).
      unfold option_lift in *. rewrite <- IHn. cbn.
      replace (denot_fun p V) with (Some (Fbody V)).
      reflexivity.
      + destruct (IHp _ _ V H2) as [V' [? ?]];
          [inversion H4; subst; assumption |].
        rewrite H5, H6. reflexivity.
      + destruct H4. apply H5.
      + simpl. rewrite H3. reflexivity.
Qed.

Lemma intersect_subset {X: Type}: forall (A B: Ensemble X),
    Included _ A B -> A = Intersection _ A B.
Proof.
    intros. apply Extensionality_Ensembles. split.
    - intros x inA. split.
      + apply inA.
      + apply (H x inA).
    - intros x inIntersection.
      destruct inIntersection.
      apply H0.
Qed.

Lemma loop_count_monotone: forall i f b V V' n m,
    loop_count_fuel i n f b V = Some (V', m) ->
    n <= m.
Proof.
    induction i; intros.
    - simpl in H. inversion H.
    - simpl in H. destruct (Beval V b).
      + destruct (option_inversion H) as [? [? ?]].
        specialize (IHi _ _ _ _ _ _ H1). lia.
      + inversion H. auto.
Qed.

Lemma loop_count_zero: forall f b V V',
    loop_count f b V = Some (V', 0) ->
    Beval V b = false /\ V = V'.
Proof.
    intros. destruct (loop_count_charact f b V) as [i LIM].
    rewrite <- LIM with (j := S i) in H; [|lia].
    simpl in H. destruct (Beval V b) eqn:Hb, (f V).
    + simpl in H.
      apply loop_count_monotone in H. lia.
    + inversion H.
    + inversion H. split; reflexivity.
    + inversion H. split; reflexivity.
Qed.

Lemma loop_complete: forall i p b V V',
    loop_fuel__C (S i) (denot_fun p) b V = Some V' ->
    (forall Vbody Vbody',
        denot_fun p Vbody = Some Vbody' ->
      exists F B,
        In _ (denot__S p) (F, B)
        /\ F Vbody = Vbody'
        /\ In _ B Vbody) ->
    exists F B,
      In _ (Union_Fam (fun m => n_fold m (loop_helper (denot__S p) b p) (Singleton _ (fun V => V, Complement _ (denot__B b))))) (F, B)
      /\ F V = V'
      /\ In _ B V
.
Proof.
    induction i; intros.
    - simpl in H. destruct (Beval V b) eqn:Hbeval, (denot_fun p V); cbn in H;
        inversion H.
      + exists (fun V => V). exists (Complement _ (denot__B b)). repeat split.
        * apply Fam_intro with (i := 0). simpl.
          constructor.
        * rewrite denotB_false. rewrite <- H2. apply Hbeval.
      + exists (fun V => V). exists (Complement _ (denot__B b)). repeat split.
        * apply Fam_intro with (i := 0). simpl.
          constructor.
        * rewrite denotB_false. rewrite <- H2. apply Hbeval.
    - simpl in H. destruct (Beval V b) eqn:Hbeval; destruct (denot_fun p V) eqn:Hbody; cbn in *.
      + destruct (IHi _ _ _ _ H H0) as [F [B [Hin [HF HB]]]].
        inversion Hin as [i' [? ?]]; subst.
        destruct (H0 V v Hbody) as [F' [B' [Hin' [HF' HB']]]].
        exists (fun V => F (F' V)). eexists.
        repeat split.
        * apply Fam_intro with (i := S i').
          exists F. exists B. exists F'. exists B'.
          repeat split.
          -- apply H1.
          -- apply Hin'.
        * rewrite HF'. reflexivity.
        * repeat split.
          -- rewrite denotB_true. apply Hbeval.
          -- apply HB'.
          -- unfold inverse_image, In.
             rewrite HF'.
             apply HB.
      + inversion H.
      + inversion H; subst.
        specialize (IHi p b V' V').
        rewrite Hbeval in IHi.
        destruct (IHi H H0) as [F [B [Hin [HF HB]]]].
        inversion Hin as [i' [? ?]]; subst.
        exists F. exists B. repeat split.
        * apply Hin.
        * apply HF.
        * apply HB.
      + inversion H; subst.
        specialize (IHi p b V' V').
        rewrite Hbeval in IHi.
        destruct (IHi H H0) as [F [B [Hin [HF HB]]]].
        inversion Hin as [i' [? ?]]; subst.
        exists F. exists B. repeat split.
        * apply Hin.
        * apply HF.
        * apply HB.
Qed.

Lemma complete: forall p V V',
    denot_fun p V = Some V' ->
    exists F B,
      In _ (denot__S p) (F, B)
      /\ F V = V'
      /\ In _ B V.
Proof.
    induction p; intros.
    (* skip *)
    - exists (fun V => V).
      exists (Full_set _).
      simpl in *. repeat split;
        inversion H; reflexivity.
    (* assign *)
    - exists (fun V => (x !-> Aeval V e ; V)).
      exists (Full_set _).
      simpl in *. repeat split;
        inversion H; reflexivity.
    (* sequence *)
    - inversion H; subst.
      destruct (option_inversion H1) as [V1 [? ?]].
      destruct (IHp1 _ _ H0) as [F1 [B1 [Hbranch1 [Hresult1 Hpart1]]]].
      destruct (IHp2 _ _ H2) as [F2 [B2 [Hbranch2 [Hresult2 Hpart2]]]].
      exists (fun V => F2 (F1 V)).
      exists (Intersection _ B1 (inverse_image F1 B2)).
      simpl in *. split; try split.
      + exists F1. exists F2. exists B1. exists B2. repeat split;
          assumption.
      + rewrite Hresult1. apply Hresult2.
      + split.
        * apply Hpart1.
        * unfold inverse_image, In.
          rewrite Hresult1. apply Hpart2.
    (* if... *)
    - inversion H; subst. destruct (Beval V b) eqn:Hbeval.
      (*... true*)
      + destruct (IHp1 _ _ H1) as [F1 [B1 [Hbranch [Hresult Hpart]]]].
        exists F1. exists (Intersection _ B1 (denot__B b)). split; try split.
        * left. exists F1. exists B1. repeat split.
          apply Hbranch.
        * apply Hresult.
        * split.
          -- apply Hpart.
          -- rewrite denotB_true. apply Hbeval.
      (*... false*)
      + destruct (IHp2 _ _ H1) as [F2 [B2 [Hbranch [Hresult Hpart]]]].
        exists F2. exists (Intersection _ B2 (Complement _ (denot__B b))). split; try split.
        * right. exists F2. exists B2. repeat split.
          apply Hbranch.
        * apply Hresult.
        * split.
          -- apply Hpart.
          -- rewrite denotB_false. apply Hbeval.
    (* while *)
    - inversion H; subst; destruct (Beval V b) eqn:Hbeval.
      (* looping *)
      + rewrite denot_loop in H1. rewrite Hbeval in H1.
        destruct (option_inversion H1) as [? [? ?]].
        destruct (IHp _ _ H0) as [F [B [Hbody [HF HB]]]].
        destruct (loop_charact__C (denot_fun p) b x) as [i LIM].
        rewrite <- LIM with (j := S i) in H2; [|lia].
        destruct (loop_complete _ _ _ _ _ H2 IHp) as [F' [B' [Hhelp [HF' HB']]]].
        exists (fun V => F' (F V)). exists (Intersection _ (denot__B b) (Intersection _ B (inverse_image F B'))).
        split; try split.
        * apply denot_while__S.
          -- apply Hbody.
          -- simpl. apply Hhelp.
        * rewrite HF. apply HF'.
        * split.
          -- rewrite denotB_true. apply Hbeval.
          -- split.
             ++ apply HB.
             ++ unfold inverse_image, In. rewrite HF. apply HB'.
      (* end of loop *)
      + rewrite denot_loop in H1.
        rewrite Hbeval in H1.
        exists (fun V => V). exists (Complement _ (denot__B b)). repeat split.
        * apply Fam_intro with (i := 0).
          simpl. constructor.
        * inversion H1. reflexivity.
        * rewrite denotB_false. apply Hbeval.
Qed.


Lemma correct: forall p F B V,
    In _ (denot__S p) (F, B) ->
    In _ B V ->
    exists V', F V = V' /\ denot_fun p V = Some V'.
Proof.
    induction p; intros.
    - inversion H; subst.
      exists V. split; reflexivity.
    - inversion H; subst.
      exists (x !-> Aeval V e; V). split; reflexivity.
    - destruct H as [F1 [F2 [B1 [B2 [H1 [H2 [HF HB]]]]]]].
      exists (F2 (F1 V)). split.
      + simpl in HF. rewrite HF. reflexivity.
      + simpl in *.
        rewrite HB in H0. inversion H0; subst.
        destruct (IHp1 F1 B1 V H1 H) as [V1 [? HV1]]. rewrite HV1.
        destruct (IHp2 F2 B2 (F1 V) H2 H3) as [V2 [? HV2]].
        simpl.
        rewrite <- H4. rewrite HV2. rewrite H5.
        reflexivity.
    - simpl. destruct H; destruct (Beval V b) eqn:Hcond.
      (* condition true, left branch*)
      + destruct H as [F1 [B1 [H1 [HF HB]]]].
        simpl in HB. rewrite HB in H0. inversion H0; subst.
        destruct (IHp1 F B1 V H1 H) as [V1 [HF1 HV1]].
        exists V1. split; assumption.
      (* condition false, left branch => contradiction *)
      + destruct H as [F1 [B1 [H1 [HF HB]]]].
        simpl in HB. rewrite HB in H0. inversion H0; subst.
        unfold denot__B, In in H2. rewrite H2 in Hcond.
        discriminate.
      (* condition true, right branch => contradiction*)
      + destruct H as [F2 [B2 [H2 [HF HB]]]].
        simpl in HB. rewrite HB in H0. inversion H0; subst.
        unfold denot__B, In, Complement in H1.
        exfalso. apply H1. apply Hcond.
      (* condition false, right branch *)
      + destruct H as [F2 [B2 [H2 [HF HB]]]].
        simpl in HB. rewrite HB in H0. inversion H0; subst.
        destruct (IHp2 F B2 V H2 H) as [V2 [HF2 HV2]].
        exists V2. split; assumption.
    - inversion H; subst; cbn.
      destruct (loop_charact__C (denot_fun p) b V) as [i' LIM].
      rewrite <- LIM with (j := S i'); [| lia].
      destruct H1. destruct x; cbn in *.
      + rewrite <- H1 in H2. inversion H2; subst.
        exists V. split.
        * reflexivity.
        * rewrite denotB_false in H0. rewrite H0. reflexivity.
      + exists (F V). split.
        * reflexivity.
        * rewrite n_fold_inversion in H1.
          rewrite <- H1 in H2.
          destruct (loop_helper_step _ _ _ _ _ _ _ H2) as [? [? [Hsofar Hstep]]].
          destruct Hstep as [F' [B' [Fbody [Bbody [? [? [? ?]]]]]]].
          simpl in H5, H6; subst.
          inversion H3; subst.
          inversion H0; subst. inversion H5; subst.
          specialize (loop_correct p IHp _ _ _ _ Hsofar (Fbody V) H7). intro.
          rewrite denotB_true in H1. rewrite H1.
          destruct (IHp _ _ _ H4 H6) as [V' [? ?]].
          rewrite H10; simpl. rewrite <- H9.
          replace i' with (S x).
          (* the symbolic and concrete execution take same number of steps *)
          (* which is not strictly true, but should be admissible? *)
          unfold option_lift in H8. apply H8.
Admitted.

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
Proof. cbn. unfold Union_Fam. eapply Big_U_intro with (X := Singleton _ (fun V => V, fun V => V X > 10)).
       - exists 0.
       assert (Complement _ (denot__B <{ X <= 10 }>) = fun V => V X > 10).
         { apply Extensionality_Ensembles. repeat split; intros V H.
           - unfold Complement, In, denot__B in H. simpl in H. apply leb_correct_neg in H.
             apply not_le in H. apply H.
           - intro H'. unfold In, denot__B in *. simpl in *. apply leb_complete in H'. lia.
         }
         cbn. rewrite H. reflexivity.
       - reflexivity.
Qed.
