(** * Trace Semantics *)

(** Anticipating the need for trace semantics for reduction in a concurrent setting,
    we develop them for the language extended with procedures from Recursion.v
 *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Init.Datatypes.
From Coq Require Import Program.   (* for `dependent induction` *)
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)
From Coq Require Import Relations.
From Coq Require Import Lists.List.
Import ListNotations.

From SymEx Require Import Expr.
Import ProcedureExpr.

From SymEx Require Import Maps.
Import ProcedureMaps.

From SymEx Require Import Recursion.
Open Scope com_scope.
Open Scope string_scope.

(** Symbolic semantics *)

(** How should a /trace/ keep track of the current stack frame? *)

(* keep the substitutions around? feels cheat-y *)
(* record "procedure call" in the trace? *)
(* inline the procedure body like in OOP.v? <-- easier implementation? *)
(* continuations like in LAGC? <-- probably better suited to parallelism *)

(** last two both seem reasonable, but lets try the easiest *)

Fixpoint Stmt_sub (s:Stmt) (u y:LVar) : Stmt :=
  let t : LSub := (u !-> (ALVar y) ; Lid_sub) in
  match s with
  | SGAsgn x e => SGAsgn x (Aapply Gid_sub t e)
  | SLAsgn x e => SLAsgn (if u =? x then y else x) (Aapply Gid_sub t e)
  | SProc P e => SProc P (Aapply Gid_sub t e)
  | SSeq s1 s2 => SSeq (Stmt_sub s1 u y) (Stmt_sub s1 u y)
  | SIf b s1 s2 => SIf (Bapply Gid_sub t b) (Stmt_sub s1 u y) (Stmt_sub s1 u y)
  | SWhile b s => SWhile (Bapply Gid_sub t b) (Stmt_sub s u y)
  | SReturn => SReturn
  end.

Open Scope list_scope.

Definition STrace_step : Type := (Bexpr + (GVar * Aexpr) + (LVar * Aexpr)).

Definition pc : Bexpr -> STrace_step := fun x => inl (inl x).
Definition asgnG : GVar -> Aexpr -> STrace_step := fun x e => inl (inr (x, e)).
Definition asgnL : LVar -> Aexpr -> STrace_step := fun x e => inr (x, e).

Definition STrace := list STrace_step.

Definition SConfig : Type := Stmt * STrace.

Reserved Notation " c '->s' c' " (at level 40).
Inductive Sstep : relation SConfig  :=
| SGAsgn_step : forall x e s t,
    (<{ x :=G e ; s }>, t) ->s (s, t ++ [asgnG x e])
| SLAsgn_step : forall x e s t,
    (<{ x :=L e ; s }>, t) ->s (s, t ++ [asgnL x e])
| SProc_step : forall (t:STrace) u y body e s t,
    (* "y fresh", somehow *)
    (<{ proc(u){body}(e) ; s }>, t) ->s (SSeq (Stmt_sub body u y) s, t ++ [asgnL u e])
| SReturn_step : forall s t,
    (<{ return ; s }>, t) ->s (s, t)
| SIfTrue_step : forall b s1 s2 s t,
    (<{ if b {s1}{s2} ; s}>, t) ->s (<{ s1 ; s }>, t ++ [pc b])
| SIfFalse_step : forall b s1 s2 s t,
    (<{ if b {s1}{s2} ; s}>, t) ->s (<{ s2 ; s }>, t ++ [pc (BNot b)])
| SWhileTrue_step : forall b s s' t,
    (<{ while b {s} ; s' }>, t) ->s (<{ s ; while b {s} ; s' }>, t ++ [pc b])
| SWhileFalse_step : forall b s s' t,
    (<{ while b {s} ; s' }>, t) ->s (s', t ++ [pc (BNot b)])
  where " c '->s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40).

(** Concrete semantics *)

Definition Val : Type := nat.
Definition CTrace_step : Type := (GVar * Val) + (LVar * Val).

Definition CTrace := list CTrace_step.

Definition accG (x:GVar) : option nat -> CTrace_step -> option nat :=
  fun acc t => match t with
            | inr _ => acc
            | inl (y, v) => if x =? y then Some v else acc
            end.

Definition accL (x:LVar) : option nat -> CTrace_step -> option nat :=
  fun acc t => match t with
            | inl _ => acc
            | inr (y, v) => if x =? y then Some v else acc
            end.

Definition acc_GVal' (t:CTrace) (x:GVar) : option nat :=
  fold_left (accG x) t None.

Definition acc_LVal' (t:CTrace) (x:LVar) : option nat :=
  fold_left (accG x) t None.

(* for now, let's just "cheat" in totality *)
Definition acc_GVal (t:CTrace) : GVal :=
  fun x => match acc_GVal' t x with
        | None => 0
        | Some n => n
        end.

Definition acc_LVal (t:CTrace) : LVal :=
  fun x => match acc_GVal' t x with
        | None => 0
        | Some n => n
        end.

Definition Aeval_t (t:CTrace) (e:Aexpr) : nat :=
  Aeval (acc_GVal t) (acc_LVal t) e.

Definition Beval_t (t:CTrace) (b:Bexpr) : bool :=
  Beval (acc_GVal t) (acc_LVal t) b.

Definition CConfig : Type := Stmt * CTrace.

Reserved Notation " c '=>c' c' " (at level 40).

Inductive Cstep : relation CConfig :=
| CGASgn_step : forall x e s t,
    (<{ x :=G e ; s }>, t) =>c (s, t ++ [inl (x, Aeval_t t e)])
| CLASgn_step : forall x e s t,
    (<{ x :=L e ; s }>, t) =>c (s, t ++ [inr (x, Aeval_t t e)])
| CProc_step : forall u body e s t y,
    (<{ proc(u){body}(e) ; s }>, t) =>c (SSeq (Stmt_sub body u y) s, t ++ [inr (y, Aeval_t t e)])
| CReturn_step : forall s t,
    (<{ return ; s }>, t) =>c (s, t)
| CIfTrue_step : forall b s1 s2 s t,
    Beval_t t b = true ->
    (<{ if b {s1}{s2} ; s }>, t) =>c (<{s1 ; s}>, t)
| CIfFalse_step : forall b s1 s2 s t,
    Beval_t t b = false ->
    (<{ if b {s1}{s2} ; s }>, t) =>c (<{s2 ; s}>, t)
| CWhileTrue_step : forall b s s' t,
    Beval_t t b = true ->
    (<{ while b {s} ; s' }>, t) =>c (<{s ; while b {s} ; s'}>, t)
| CWhileFalse_step : forall b s s' t,
    Beval_t t b = false ->
    (<{ while b {s} ; s' }>, t) =>c (s', t)
  where " c '=>c' c' " := (Cstep c c').

Definition multi_Cstep := clos_refl_trans_n1 _ Cstep.
Notation " c '=>*' c' " := (multi_Cstep c c') (at level 40).
