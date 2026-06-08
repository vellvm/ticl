From Stdlib Require Import Nat Strings.String.
From ExtLib Require Import Data.Map.FMapAList Data.String Structures.Maps.
From TICL Require Import
  ICTree.Core
  Events.StateE
  Lang.Maps
  Lang.Yield.Events
  Lang.Yield.Syntax.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

Definition Ctx := alist string nat.
Definition Mem := stateE Ctx.

(** Raw Yield denotations can yield, fork, and access memory. *)
Definition YEff := yieldE + (forkE + Mem).

Definition ytrigger (e : YEff) : ictree YEff (encode e) :=
  @ICtree.trigger YEff YEff _ _ ReSum_refl ReSumRet_refl e.
Definition yget : ictree YEff Ctx := ytrigger (inr (inr Get)).
Definition yput (m : Ctx) : ictree YEff unit :=
  ytrigger (inr (inr (Put m))).
Definition yyield : ictree YEff unit := ytrigger (inl Yield).
Definition yfork : ictree YEff bool := ytrigger (inr (inl Fork)).

(** Denotation of expressions.  Successful variable reads yield once before
    returning the value; missing variables remain stuck. *)
Fixpoint denote_exp (e : YExp) : ictree YEff nat :=
  match e with
  | YVar name =>
      ctx <- yget;;
      match lookup name ctx with
      | Some value => yyield;; Ret value
      | None => stuck
      end
  | YLit n => Ret n
  | YPlus a b =>
      x <- denote_exp a;;
      y <- denote_exp b;;
      Ret (x + y)%nat
  | YMinus a b =>
      x <- denote_exp a;;
      y <- denote_exp b;;
      Ret (x - y)%nat
  | YMult a b =>
      x <- denote_exp a;;
      y <- denote_exp b;;
      Ret (x * y)%nat
  end.

(** Internal result used to prevent child threads from inheriting source
    continuations outside their fork body.

    [Fallthrough] means the current thread should continue with the enclosing
    source continuation.  [HaltThread] means a spawned child has finished its
    declared body and must not inherit enclosing continuations. *)
Inductive YStmtFlow : Type :=
| Fallthrough
| HaltThread.

(** Flow-sensitive denotation of statements. *)
Fixpoint denote_stmt_flow (s : YStmt) : ictree YEff YStmtFlow :=
  match s with
  | YAssign name expr =>
      value <- denote_exp expr;;
      ctx <- yget;;
      yput (add name value ctx);;
      Ret Fallthrough
  | YSeq a b =>
      flow <- denote_stmt_flow a;;
      match flow with
      | Fallthrough => denote_stmt_flow b
      | HaltThread => Ret HaltThread
      end
  | YIf test then_branch else_branch =>
      condition_value <- denote_exp test;;
      if is_true condition_value then
        denote_stmt_flow then_branch
      else
        denote_stmt_flow else_branch
  | YWhile test body =>
      ICtree.iter
        (fun _ =>
           condition_value <- denote_exp test;;
           if is_true condition_value then
             flow <- denote_stmt_flow body;;
             match flow with
             | Fallthrough => Ret (inl tt)
             | HaltThread => Ret (inr HaltThread)
             end
           else
             Ret (inr Fallthrough)) tt
  | YFork body =>
      in_child <- yfork;;
      if in_child then
        _ <- denote_stmt_flow body;;
        Ret HaltThread
      else
        Ret Fallthrough
  | YSkip => Ret Fallthrough
  | YYield =>
      yyield;;
      Ret Fallthrough
  end.

(** Public denotation of statements to unscheduled Yield threads. *)
Definition denote_stmt (s : YStmt) : ictree YEff unit :=
  _ <- denote_stmt_flow s;;
  Ret tt.
