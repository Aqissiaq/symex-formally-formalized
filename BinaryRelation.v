(** * An aside to define (binary) relations nicely *)

Definition Relation (A : Type) := A -> A -> Prop.

Inductive Trans_Ref_Closure {A : Type} (R: Relation A) : Relation A :=
| Rrefl : forall x, Trans_Ref_Closure R x x
| Rtrans : forall x y z,
    Trans_Ref_Closure R x y -> R y z -> Trans_Ref_Closure R x z.

Inductive Trans_Ref_Closure' {A : Type} (R: Relation A) : Relation A :=
| Rrefl : forall x, Trans_Ref_Closure R x x
| Rtrans : forall x y z,
    R x y -> Trans_Ref_Closure R y z -> Trans_Ref_Closure R x z.
