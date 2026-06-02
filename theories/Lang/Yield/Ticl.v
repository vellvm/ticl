(** TICL-facing Yield surface.

    Public tiers exported by this façade:

    - [Lang.Yield.Events], [Lang.Yield.Syntax], and [Lang.Yield.Denote] expose
      raw source-level threads with [Yield], [Fork], and memory effects.
    - [Lang.Yield.Scheduler] exposes the scheduler, and [scheduled_visible]
      exposes scheduled programs with scheduler [Spawn], cooperative [Yield],
      and memory effects visible.
    - [interp_scheduled_erased], [instr_exp_erased], and [instr_stmt_erased]
      expose the state-only TICL view where scheduler/yield observations are
      intentionally erased.
    - [interp_scheduled], [instr_exp], and [instr_stmt] are compatibility
      aliases for the erased tier.

    This file also carries a small regression surface: constructor unfold facts,
    one-step scheduler facts, finite-pool slot regressions, concrete visible
    YYield/YFork examples, and alias facts documenting that the compatibility
    APIs are erased. *)
From Stdlib Require Import
  Fin
  Nat
  Strings.String.

From ExtLib Require Import
  Data.Map.FMapAList
  Data.String
  Structures.Maps.

From TICL Require Export
  Lang.Yield.Events
  Lang.Yield.Syntax
  Lang.Yield.Denote
  Lang.Yield.Vec
  Lang.Yield.Scheduler
  Lang.Yield.Interp.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.Interp.Core.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

(** Expression denotation constructor unfold facts. *)
Lemma denote_exp_yvar name :
  denote_exp (YVar name) =
    (ctx <- yget;;
     match lookup name ctx with
     | Some value => yyield;; Ret value
     | None => stuck
     end).
Proof. reflexivity. Qed.

Lemma denote_exp_ylit n : denote_exp (YLit n) = Ret n.
Proof. reflexivity. Qed.

Lemma denote_exp_yplus a b :
  denote_exp (YPlus a b) =
    (x <- denote_exp a;; y <- denote_exp b;; Ret (x + y)%nat).
Proof. reflexivity. Qed.

Lemma denote_exp_yminus a b :
  denote_exp (YMinus a b) =
    (x <- denote_exp a;; y <- denote_exp b;; Ret (x - y)%nat).
Proof. reflexivity. Qed.

Lemma denote_exp_ymult a b :
  denote_exp (YMult a b) =
    (x <- denote_exp a;; y <- denote_exp b;; Ret (x * y)%nat).
Proof. reflexivity. Qed.

(** Statement denotation constructor unfold facts. *)
Lemma denote_stmt_yassign name expr :
  denote_stmt (YAssign name expr) =
    (value <- denote_exp expr;; ctx <- yget;; yput (add name value ctx)).
Proof. reflexivity. Qed.

Lemma denote_stmt_yseq a b :
  denote_stmt (YSeq a b) = (denote_stmt a;; denote_stmt b).
Proof. reflexivity. Qed.

Lemma denote_stmt_yif test then_branch else_branch :
  denote_stmt (YIf test then_branch else_branch) =
    (condition_value <- denote_exp test;;
     if YieldSyntax.is_true condition_value then
       denote_stmt then_branch
     else
       denote_stmt else_branch).
Proof. reflexivity. Qed.

Lemma denote_stmt_ywhile test body :
  denote_stmt (YWhile test body) =
    ICtree.iter
      (fun _ =>
         condition_value <- denote_exp test;;
         if YieldSyntax.is_true condition_value then
           denote_stmt body;; Ret (inl tt)
         else
           Ret (inr tt)) tt.
Proof. reflexivity. Qed.

Lemma denote_stmt_yfork inactive active :
  denote_stmt (YFork inactive active) =
    (in_child <- yfork;;
     if in_child then
       denote_stmt inactive
     else
       denote_stmt active).
Proof. reflexivity. Qed.

Lemma denote_stmt_yskip : denote_stmt YSkip = Ret tt.
Proof. reflexivity. Qed.

Lemma denote_stmt_yyield : denote_stmt YYield = yyield.
Proof. reflexivity. Qed.

(** Scheduler one-step/case regression facts. *)
Section SchedulerFacts.
  Context {E : Type} `{Encode E}.

  Local Ltac solve_focused_schedule H :=
    lazy [schedule observe _observe];
    match type of H with
    | observe (?v ?i) = _ =>
        change (@_observe _ _ unit (v i)) with (observe (v i));
        rewrite H;
        reflexivity
    end.

  Lemma schedule_empty_none (v : pool E 0) :
    observe (schedule 0 v None) = RetF tt.
  Proof. reflexivity. Qed.

  Lemma schedule_no_focus_nonempty n (v : pool E (S n)) :
    observe (schedule (S n) v None) =
      VisF (inl Yield) (fun _ => Br n (fun i => schedule (S n) v (Some i))).
  Proof. reflexivity. Qed.

  Lemma schedule_focused_ret n (v : pool E (S n)) (i : Fin.t (S n)) :
    observe (v i) = RetF tt ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule n (remove_pool v i) None).
  Proof.
    intro Hret.
    solve_focused_schedule Hret.
  Qed.

  Lemma schedule_focused_br n (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v i) = BrF b k ->
    observe (schedule (S n) v (Some i)) =
      BrF b (fun j => schedule (S n) (replace_pool v i (k j)) (Some i)).
  Proof.
    intro Hbr.
    solve_focused_schedule Hbr.
  Qed.

  Lemma schedule_focused_guard n (v : pool E (S n)) (i : Fin.t (S n)) t :
    observe (v i) = GuardF t ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S n) (replace_pool v i t) (Some i)).
  Proof.
    intro Hg.
    solve_focused_schedule Hg.
  Qed.

  Lemma schedule_focused_yield n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inl Yield) k ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S n) (replace_pool v i (k tt)) None).
  Proof.
    intro Hy.
    solve_focused_schedule Hy.
  Qed.

  Lemma schedule_focused_fork n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inr (inl Fork)) k ->
    observe (schedule (S n) v (Some i)) =
      VisF ((inr (inl Spawn)) : yieldE + (spawnE + E))
        (fun _ => schedule (S (S n))
                    (cons_pool (k true) (replace_pool v i (k false)))
                    (Some (Fin.FS i))).
  Proof.
    intro Hf.
    solve_focused_schedule Hf.
  Qed.

  Lemma schedule_focused_user_event n (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v i) = VisF (inr (inr e)) k ->
    observe (schedule (S n) v (Some i)) =
      VisF ((inr (inr e)) : yieldE + (spawnE + E))
        (fun x => schedule (S n) (replace_pool v i (k x)) (Some i)).
  Proof.
    intro Hu.
    solve_focused_schedule Hu.
  Qed.
End SchedulerFacts.

(** Non-degenerate finite-pool scheduler regressions. *)
Section SchedulerPoolRegressions.
  Context {E : Type} `{Encode E}.

  Lemma schedule_yield_two_threads_one_step (next other : thread E) :
    observe
      (schedule 2
         (cons_pool
            (Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next))
            (fun _ : Fin.t 1 => other))
         (Some Fin.F1)) =
      GuardF
        (schedule 2
           (replace_pool
              (cons_pool
                 (Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next))
                 (fun _ : Fin.t 1 => other))
              Fin.F1 next)
           None).
  Proof. reflexivity. Qed.

  Lemma schedule_yield_two_threads_focused_slot (next other : thread E) :
    replace_pool
      (cons_pool
         (Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next))
         (fun _ : Fin.t 1 => other))
      Fin.F1 next Fin.F1 = next.
  Proof. apply replace_pool_hit. Qed.

  Lemma schedule_yield_two_threads_other_slot (next other : thread E) :
    replace_pool
      (cons_pool
         (Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next))
         (fun _ : Fin.t 1 => other))
      Fin.F1 next (Fin.FS Fin.F1) = other.
  Proof.
    rewrite replace_pool_miss by discriminate.
    apply cons_pool_tail.
  Qed.

  Lemma schedule_fork_two_threads_one_step
      (child parent other : thread E) :
    observe
      (schedule 2
         (cons_pool
            (Vis ((inr (inl Fork)) : yieldE + (forkE + E))
               (fun in_child : bool => if in_child then child else parent))
            (fun _ : Fin.t 1 => other))
         (Some Fin.F1)) =
      VisF ((inr (inl Spawn)) : yieldE + (spawnE + E))
        (fun _ =>
           schedule 3
             (cons_pool child
                (replace_pool
                   (cons_pool
                      (Vis ((inr (inl Fork)) : yieldE + (forkE + E))
                         (fun in_child : bool => if in_child then child else parent))
                      (fun _ : Fin.t 1 => other))
                   Fin.F1 parent))
             (Some (Fin.FS Fin.F1))).
  Proof. reflexivity. Qed.

  Lemma schedule_fork_two_threads_child_slot
      (child parent other : thread E) :
    cons_pool child
      (replace_pool
         (cons_pool
            (Vis ((inr (inl Fork)) : yieldE + (forkE + E))
               (fun in_child : bool => if in_child then child else parent))
            (fun _ : Fin.t 1 => other))
         Fin.F1 parent)
      Fin.F1 = child.
  Proof. apply cons_pool_head. Qed.

  Lemma schedule_fork_two_threads_parent_slot
      (child parent other : thread E) :
    cons_pool child
      (replace_pool
         (cons_pool
            (Vis ((inr (inl Fork)) : yieldE + (forkE + E))
               (fun in_child : bool => if in_child then child else parent))
            (fun _ : Fin.t 1 => other))
         Fin.F1 parent)
      (Fin.FS Fin.F1) = parent.
  Proof.
    rewrite cons_pool_tail.
    apply replace_pool_hit.
  Qed.

  Lemma schedule_fork_two_threads_other_slot
      (child parent other : thread E) :
    cons_pool child
      (replace_pool
         (cons_pool
            (Vis ((inr (inl Fork)) : yieldE + (forkE + E))
               (fun in_child : bool => if in_child then child else parent))
            (fun _ : Fin.t 1 => other))
         Fin.F1 parent)
      (Fin.FS (Fin.FS Fin.F1)) = other.
  Proof.
    rewrite cons_pool_tail.
    rewrite replace_pool_miss by discriminate.
    apply cons_pool_tail.
  Qed.
End SchedulerPoolRegressions.

(** Concrete scheduler-visible examples. *)
Lemma scheduled_visible_yyield_one_step :
  observe (scheduled_visible YYield) =
    GuardF
      (schedule 1
         (replace_pool (fun _ : Fin.t 1 => denote_stmt YYield) Fin.F1 (Ret tt))
         None).
Proof. reflexivity. Qed.

Lemma scheduled_visible_yfork_skip_skip_one_step :
  observe (scheduled_visible (YFork YSkip YSkip)) =
    let fork_continuation :=
      fun in_child : bool =>
        ICtree.subst'
          (fun in_child : bool => if in_child then Ret tt else Ret tt)
          (RetF in_child) in
    VisF ((inr (inl Spawn)) : yieldE + (spawnE + Mem))
      (fun _ =>
         schedule 2
           (cons_pool (fork_continuation true)
              (replace_pool
                 (fun _ : Fin.t 1 => denote_stmt (YFork YSkip YSkip))
                 Fin.F1 (fork_continuation false)))
           (Some (Fin.FS Fin.F1))).
Proof.
  unfold scheduled_visible.
  apply (@schedule_focused_fork Mem _ 0
           (fun _ : Fin.t 1 => denote_stmt (YFork YSkip YSkip))
           Fin.F1
           (fun in_child : bool =>
              ICtree.subst'
                (fun in_child : bool => if in_child then Ret tt else Ret tt)
                (RetF in_child))).
  cbn.
  unfold resum, ReSum_refl, resum_ret, ReSumRet_refl.
  reflexivity.
Qed.

(** Erasure handlers intentionally hide scheduler/thread observations. *)
Lemma handle_spawn_spawn_erased : handle_spawn (inr (inl Spawn)) = Ret tt.
Proof. reflexivity. Qed.

Lemma handle_yield_yield_erased : handle_yield (inl Yield) = Ret tt.
Proof. reflexivity. Qed.

Lemma interp_scheduled_erased_unfold s :
  interp_scheduled_erased s = interp_yield (interp_spawn (scheduled_visible s)).
Proof. reflexivity. Qed.

(** Compatibility aliases are erased APIs. *)
Lemma scheduled_alias s : scheduled s = scheduled_visible s.
Proof. reflexivity. Qed.

Lemma interp_scheduled_alias_erased s : interp_scheduled s = interp_scheduled_erased s.
Proof. reflexivity. Qed.

Lemma instr_exp_alias_erased e ctx : instr_exp e ctx = instr_exp_erased e ctx.
Proof. reflexivity. Qed.

Lemma instr_stmt_alias_erased s ctx : instr_stmt s ctx = instr_stmt_erased s ctx.
Proof. reflexivity. Qed.
