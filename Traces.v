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
