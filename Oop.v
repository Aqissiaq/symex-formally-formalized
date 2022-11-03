(** * 4. Object Orientation *)

(** We next extend the language of the previous section with object-oriented features. We first introduce a distinction
between variables x , y, . . . , e.g., the formal parameters of methods, including the keyword this, and fields f , f ′, . . .
(of the classes of a program)

 I am less interested in OOP and more in trace semantics*)

From Coq Require Import Strings.String.
Open Scope string_scope.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Program.   (* for `dependent induction` *)
From Coq Require Import Relations.

Inductive Oexpr : Type :=
| PNil
| PThis
| PVar (h:Heap)
| PCond (b:Bexpr) (e1 e2:Oexpr)
with Heap :=
| HVar (x:string)
| HExpr (e:Oexpr) (f:string)
with  Bexpr  :=
| BTrue
| BFalse
| BNot (b:Bexpr)
| BAnd (b1 b2:Bexpr)
| BEq (e1 e2:Oexpr).

Coercion PVar : Heap >-> Oexpr.

Definition r : Heap := HVar "r".

Inductive Stmt : Type :=
| SAsgn (h:Heap) (e:Oexpr)
| SNew (h:Heap) (C:Class)
| SMethod (h:Heap) (m:Class) (e0:Oexpr)
| SReturn (e:Oexpr)
| SSeq (s1 s2:Stmt)
| SIf (b:Bexpr) (s1 s2:Stmt)
| SLoop (b:Bexpr) (s:Stmt)
  with Class : Type :=
  (*just one method with no parameters per class for now*)
  | CDec (body:Stmt).

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "x '==' y" := (BEq x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "'if' b 'then' e1 'else' e2 'fi'" := (PCond b e1 e2)
           (in custom com at level 89, b at level 99,
            e1 at level 99, e2 at level 99) : com_scope.
Notation "e '->' f" := (HExpr e f) : com_scope.
Notation "'nil'" := PNil : com_scope.
Notation "'this'" := PThis : com_scope.
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).

Notation "x := y"  :=
         (SAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "h ':=' 'new' C" := (SNew h C)
            (in custom com at level 0, h constr at level 0,
             C at level 85, no associativity) : com_scope.
Notation "h '<-' m '(' e ')'" := (SMethod h m e)
            (in custom com at level 0, h constr at level 0,
             m at level 80, no associativity) : com_scope.
Notation "'return' e" := (SReturn e) (in custom com at level 85) : com_scope.
Notation "x ; y" :=
         (SSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x '{' y '}' '{' z '}'" :=
         (SIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x '{' y '}'" :=
         (SLoop x y)
           (in custom com at level 89, x at level 99,
               y at level 99) : com_scope.
Notation "'class' '{' b '}'"  :=
         (CDec b)
            (in custom com at level 0,
                b at level 85, no associativity) : com_scope.

Open Scope com_scope.

Fixpoint Oexpr_subst (e e0:Oexpr) : Oexpr :=
  match e with
  | PNil => PNil
  | PThis => e0
  | PVar (HExpr e' f) => Oexpr_subst e' e0
  | PVar x => PVar x
  | PCond b e1 e2 => PCond (Bexpr_subst b e0) (Oexpr_subst e1 e0) (Oexpr_subst e2 e0)
  end
  with Bexpr_subst (b:Bexpr) (e0:Oexpr) : Bexpr :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b => BNot (Bexpr_subst b e0)
  | BAnd b1 b2 => BAnd (Bexpr_subst b1 e0) (Bexpr_subst b2 e0)
  | BEq e1 e2 => BEq (Oexpr_subst e1 e0) (Oexpr_subst e2 e0)
  end.

Definition Heap_subst (h:Heap) (e0:Oexpr) : Heap :=
  match h with
  | HVar x => HVar x
  | HExpr e f => HExpr (Oexpr_subst e e0) f
  end.

Fixpoint method_subst (body:Stmt) (e0:Oexpr) : Stmt :=
  match body with
  | SAsgn h e => SAsgn (Heap_subst h e0) (Oexpr_subst e e0)
  | SNew h C => SNew (Heap_subst h e0) C
  | SMethod h m e'0 => SMethod (Heap_subst h e0) m (Oexpr_subst e'0 e0)
  | SReturn e => SReturn (Oexpr_subst e e0)
  | SSeq s1 s2 => SSeq (method_subst s1 e0) (method_subst s2 e0)
  | SIf b s1 s2 => SIf (Bexpr_subst b e0) (method_subst s1 e0) (method_subst s2 e0)
  | SLoop b s => SLoop (Bexpr_subst b e0) (method_subst s e0)
  end.

Definition TraceStep : Type := (Bexpr + (Heap * Class) + (Heap * Oexpr)).

Definition pc : Bexpr -> TraceStep :=
  fun b => inl (inl b).
Definition new : (Heap * Class) -> TraceStep :=
*  fun x => inl (inr x).
Definition asgn : (Heap * Oexpr) -> TraceStep := inr.

Open Scope list_scope.
Definition Trace : Type := list TraceStep.

Definition SState : Type := Stmt * Trace.

Reserved Notation " c '->s' c' " (at level 40).

Inductive Sstep : relation SState :=
| SAsgn_step : forall h e s p,
    (<{ h := e ; s }>, p) ->s (s, p ++ [asgn (h, e)])
| SNew_step : forall h C s p x,
    (*maybe an "x fresh" condition here*)
    (<{ h := new C ; s }>, p) ->s (s, p ++ [ asgn (h, PVar x) ; new (x, C)])
| SMethod_step : forall h e0 s s' p,
    (<{ h <- class { s } (e0) ; s'}>, p)
    ->s (SSeq (method_subst s e0) <{ h := r ; s'}>, p ++ [pc (BNot (BEq e0 PNil))])
| SReturn_step : forall e s p,
    (<{ return e ; s }>, p) ->s (s, p ++ [asgn (r, e)])
| SIfTrue_step : forall b s1 s2 s p,
    (<{ if b {s1}{s2} ; s}>, p) ->s (<{ s1 ; s }>, p ++ [pc b])
| SIfFalse_step : forall b s1 s2 s p,
    (<{ if b {s1}{s2} ; s}>, p) ->s (<{ s2 ; s }>, p ++ [pc (BNot b)])
| SWhileTrue_step : forall b s s' p,
    (<{ while b {s} ; s' }>, p) ->s (<{ s ; while b {s} ; s' }>, p ++ [pc b])
| SWhileFalse_step : forall b s s' p,
    (<{ while b {s} ; s' }>, p) ->s (s', p ++ [pc (BNot b)])
  where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40).

Fixpoint subst_expr (e': Oexpr) (x:string) (e:Oexpr) : Oexpr :=
  match e' with
  | PVar (HExpr e0 f) => PVar (HExpr (subst_expr e0 x e) f)
  | HVar y => if (x =? y)%string then e else HVar y
  | PCond b e1 e2 => PCond (subst_bexpr b x e) (subst_expr e1 x e) (subst_expr e2 x e)
  | e' => e'
  end
with subst_bexpr (b:Bexpr) (x:string) (e:Oexpr) : Bexpr :=
       match b with
       | BNot b => BNot (subst_bexpr b x e)
       | BAnd b1 b2 => BAnd (subst_bexpr b1 x e) (subst_bexpr b2 x e)
       | BEq e1 e2 => BEq (subst_expr e1 x e) (subst_expr e2 x e)
       | b => b
       end.

Fixpoint subst_heap (e': Oexpr) (h:Oexpr) (f:string) (e:Oexpr) : Oexpr :=
  match e' with
  | PVar (HExpr e0 f') => if (f =? f')%string
                         then PCond (BEq (subst_heap e0 h f e) h) e (subst_heap e0 h f e)
                         else PVar (HExpr (subst_heap e0 h f e) f')
  | PCond b e1 e2 => PCond (subst_bexpr_heap b h f e) (subst_heap e1 h f e) (subst_heap e2 h f e)
  | e' => e'
  end
with subst_bexpr_heap (b:Bexpr) (h:Oexpr) (f:string) (e:Oexpr) : Bexpr :=
       match b with
       | BNot b => BNot (subst_bexpr_heap b h f e)
       | BAnd b1 b2 => BAnd (subst_bexpr_heap b1 h f e) (subst_bexpr_heap b2 h f e)
       | BEq e1 e2 => BEq (subst_heap e1 h f e) (subst_heap e2 h f e)
       | b => b
       end.

(* the article includes a class here, but then never use it? *)
Fixpoint subst_newB (b:Bexpr) (x:string) : Bexpr :=
  match b with
  | BNot b => BNot (subst_newB b x)
  | BAnd b1 b2 => BAnd (subst_newB b1 x) (subst_newB b2 x)
  | BEq (HVar y) (HVar z) => if (y =? x)%string && (z =? x)%string then BTrue else BFalse
  | BEq _ _ => BFalse
  | b => b
  end.

Fixpoint subst_newHB (b:Bexpr) (h:Oexpr) (f:string) : Bexpr :=
  match b with
  | BNot b => BNot (subst_newHB b h f)
  | BAnd b1 b2 => BAnd (subst_newHB b1 h f) (subst_newHB b2 h f)
  | BEq _ _ => BFalse
  | b => b
  end.

Fixpoint subst_new (e: Oexpr) (x:string) : Oexpr :=
  match e with
  | PNil => PNil
  | PThis => PThis
  | HVar y => HVar y
  | HExpr (HVar y) f => if (x =? y)%string then PNil else HExpr (HVar y) f
  | HExpr e f => HExpr (subst_new e x) f
  | PCond b e1 e2 => PCond (subst_newB b x) (subst_new e1 x) (subst_new e2 x)
  end.

Fixpoint nil_error_absence (e:Oexpr) : Bexpr :=
  match e with
  | PVar (HExpr e f) =>  BAnd <{ ~ (e == nil) }> (nil_error_absence e)
  | PCond b e1 e2 => BAnd (nil_error_absenceB b) (BAnd (nil_error_absence e1) (nil_error_absence e2))
  | _ => BTrue
  end
with nil_error_absenceB (b:Bexpr) : Bexpr :=
       match b with
       | BNot b => nil_error_absenceB b
       | BAnd b1 b2 => BAnd (nil_error_absenceB b1) (nil_error_absenceB b2)
       | BEq e1 e2 => BAnd (nil_error_absence e1) (nil_error_absence e2)
       | _ => BTrue
       end.

Fixpoint path_condition (t:Trace) : Bexpr :=
  match t with
  | [] => BTrue
  | inl (inl b) :: p => BAnd (path_condition p) b
  | inl (inr (HVar x, C)) :: p => subst_newB (path_condition p) x
  | inl (inr (HExpr h f, C)) :: p => subst_newHB (path_condition p) h f
  | inr (HVar x, e) :: p => BAnd (subst_bexpr (path_condition p) x e) (nil_error_absence e)
  | inr (HExpr h f, e) :: p => BAnd (subst_bexpr_heap (path_condition p) h f e)
                               (BAnd (nil_error_absence h) (nil_error_absence e))
  end.

(** Concrete Semantics *)

(* we "cheat" by just evaluating to symbols represented by strings *)
Definition Obs : Type := string.
Definition Val : Type := string.

Definition GVal : Type := string -> Obs.
Definition HVal : Type := Obs -> string -> Val.

Fixpoint eval (G:GVal) (H:HVal) (e:Oexpr) : option Val :=
  match e with
  | PNil => Some "nil"
  | PThis => Some "this"
  | HVar x => Some (G x)
  | PVar (HExpr e f) => match eval G H e with
                       | None => None
                       | Some o => if f =? "nil" then None else
                           if o =? "nil" then None else Some (H o f)
                       end
  | PCond b e1 e2 => match evalB G H b with
                      | None => None
                    | Some true => eval G H e1
                    | Some false => eval G H e2
                    end
                      end
  with evalB (G:GVal) (H:HVal) (b:Bexpr) : option bool:=
         match b with
         | BTrue => Some true
         | BFalse => Some false
         | BNot b => option_map negb (evalB G H b)
         | BAnd b1 b2 => match evalB G H b1 with
                        | None => None
                        | Some b1 => option_map (andb b1) (evalB G H b2)
                        end
         | BEq e1 e2 => match eval G H e1 with
                       | None => None
                       | Some o1 => match eval G H e2 with
                                   | None => None
                                   | Some o2 => Some (o1 =? o2)
                                   end
                       end
         end.

Definition update {E:Type} (s: string -> E) (x:string) (e:E) : string -> E :=
  fun y => if String.eqb x y then e else s x.

Definition CConfig : Type := GVal * HVal * Trace.

Reserved Notation " c '=>c' c' " (at level 40).

Definition Hupdate (H:HVal) (o:Obs) (f:string) (v:Val) : HVal :=
  fun (o':Obs) (f':string) => if (o =? o') && (f =? f') then v else H o' f'.

Inductive Cstep : relation CConfig :=
| CHAsgn_step : forall G H h h' f e e' p,
    eval G H h = Some h' ->
    eval G H e = Some e' ->
    (G, H, asgn (HExpr h f,e) :: p) =>c (G , Hupdate H h' f e', p)
| CGAsgn_step : forall G H x e e' p,
    eval G H e = Some e' ->
    (G, H, asgn (HVar x, e) :: p) =>c (update G x e', H, p)
| CGNew_step : forall G H x f C p o,
    (* o fresh? *)
    (G, H, new (HVar x, C) :: p) =>c (update G x o, Hupdate H o f "nil", p)
(* this means new objects cannot be assigned to fields, which is maybe non intentional *)
| CTest_step : forall G H b p,
    evalB G H b = Some true ->
    (G, H, pc b :: p) =>c (G, H, p)
  where " c '=>c' c' " := (Cstep c c').

Definition multi_Cstep := clos_refl_trans_1n _ Cstep.
Notation " c '=>*' c' " := (multi_Cstep c c') (at level 40).

Definition computes (G:GVal) (H:HVal) (p:Trace) : Prop := exists G' H', (G, H, p) =>* (G', H', []).

Lemma some_not_none {T:Type} (x:T) : Some x <> None.
Proof. intro. inversion H. Qed.

Lemma none_not_some {T:Type} (x:T) : None <> Some x.
Proof. intro. inversion H. Qed.

Lemma some_injective {T:Type} (x y:T) : Some x = Some y -> x = y.
Proof. intros. inversion H. reflexivity. Qed.

Theorem sound_and_complete : forall G H p,
    computes G H p <-> evalB G H (path_condition p) = Some true.
Proof.
  intros. induction p.
  - split; intro.
    + reflexivity.
    + exists G. exists H. constructor.
  - destruct a as [[b | (h, C)] | x].
    (* boolean test *)
    + split; intro.
      * destruct H0 as [G' [H' comp]]. destruct IHp as [IHright IHleft].
        inversion comp; subst.
        inversion H0; subst.
        simpl. rewrite IHright. rewrite H8. reflexivity.
        exists G'. exists H'. apply H1.
      * destruct IHp as [IHright IHleft].
        inversion H0; subst. destruct (evalB G H (path_condition p)). destruct b0.
        ** destruct (IHleft eq_refl) as [G' [H' c]].
        exists G'. exists H'. econstructor.
           *** apply CTest_step. destruct (evalB G H b).
               inversion H2. reflexivity.
               simpl in H2. apply none_not_some in H2. contradiction.
           *** assumption.
        ** destruct (evalB G H b); try destruct b0;
             simpl in H2; try (apply some_injective in H2); discriminate.
        ** discriminate.
    (* new *)
    + admit. (* needs a C-aware substB, which I haven't figured out *)
      + split; intro.
        ++ destruct H0 as [G' [H' comp]]. destruct IHp as [IHright IHleft].
           inversion comp; subst.
           inversion H0; subst.
           * simpl.
