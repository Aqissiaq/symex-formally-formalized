(** * An aside to define (binary) relations nicely *)

Definition Relation (A : Type) := A -> A -> Prop.

Inductive Trans_Ref_Closure {A : Type} (R: Relation A) : Relation A :=
| Rrefl : forall x, Trans_Ref_Closure R x x
| Rstep : forall x y z,
    Trans_Ref_Closure R x y -> R y z -> Trans_Ref_Closure R x z.

Theorem closure_refl {A:Type} {R:Relation A} : forall x,
    Trans_Ref_Closure R x x.
Proof. apply Rrefl. Qed.

Theorem closure_trans {A:Type} {R:Relation A} : forall x y z,
    Trans_Ref_Closure R x y -> Trans_Ref_Closure R y z -> Trans_Ref_Closure R x z.
Proof. intros. induction H0.
       - assumption.
       - eapply Rstep. apply IHTrans_Ref_Closure. assumption. assumption.
Qed.

Inductive Trans_Ref_Closure' {A : Type} (R: Relation A) : Relation A :=
| Rrefl' : forall x, Trans_Ref_Closure' R x x
| Rstep' : forall x y z,
    R x y -> Trans_Ref_Closure' R y z -> Trans_Ref_Closure' R x z.

Theorem closure_refl' {A:Type} {R:Relation A} : forall x,
    Trans_Ref_Closure' R x x.
Proof. apply Rrefl'. Qed.

Theorem closure_trans' {A:Type} {R:Relation A} : forall x y z,
    Trans_Ref_Closure' R x y -> Trans_Ref_Closure' R y z -> Trans_Ref_Closure' R x z.
Proof. intros. induction H.
       - assumption.
       - eapply Rstep'. apply H. apply IHTrans_Ref_Closure'. assumption.
Qed.
