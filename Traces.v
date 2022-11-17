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
  (format "[ '[' x ; '/' .. ; '/' y ; '/' z ']' ]") : list_scope.
