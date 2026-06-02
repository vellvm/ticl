From Stdlib Require Import Nat Strings.String.
From ExtLib Require Import Data.Map.FMapAList Data.String Structures.Maps.
From TICL Require Import ICTree.Core Events.StateE Lang.Maps Lang.Yield.Events Lang.Yield.Syntax.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

Definition Ctx := alist string nat.
Definition Mem := stateE Ctx.

(** Raw Yield denotations can yield, fork, and access memory. *)
Definition YEff := yieldE + (forkE + Mem).

Definition ytrigger (e : YEff) : ictree YEff (encode e) :=
  @ICtree.trigger YEff YEff _ _ ReSum_refl ReSumRet_refl e.
Definition yget : ictree YEff Ctx := ytrigger (inr (inr Get)).
Definition yput (m : Ctx) : ictree YEff unit := ytrigger (inr (inr (Put m))).
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

(** Denotation of statements to unscheduled Yield threads. *)
Fixpoint denote_stmt (s : YStmt) : ictree YEff unit :=
  match s with
  | YAssign name expr =>
      value <- denote_exp expr;;
      ctx <- yget;;
      yput (add name value ctx)
  | YSeq a b =>
      denote_stmt a;;
      denote_stmt b
  | YIf test then_branch else_branch =>
      condition_value <- denote_exp test;;
      if is_true condition_value then
        denote_stmt then_branch
      else
        denote_stmt else_branch
  | YWhile test body =>
      ICtree.iter
        (fun _ =>
           condition_value <- denote_exp test;;
           if is_true condition_value then
             denote_stmt body;; Ret (inl tt)
           else
             Ret (inr tt)) tt
  | YFork inactive active =>
      in_child <- yfork;;
      if in_child then
        denote_stmt inactive
      else
        denote_stmt active
  | YSkip => Ret tt
  | YYield => yyield
  end.
