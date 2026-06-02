From Stdlib Require Import Fin.
From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad
  Structures.MonadState
  Data.Map.FMapAList
  Data.String.
From TICL Require Import
  ICTree.Core
  ICTree.Interp.Core
  ICTree.Interp.State
  ICTree.Events.State
  ICTree.Events.Writer
  Events.Core
  Events.StateE
  Lang.Maps
  Lang.Yield.Events
  Lang.Yield.Syntax
  Lang.Yield.Denote
  Lang.Yield.Scheduler.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

(** Start a source statement as a singleton pool focused on its only thread.
    This is the scheduler-visible view: source [Fork] events have been
    scheduled into scheduler [Spawn] observations, and cooperative [Yield]
    observations remain visible alongside memory effects. *)
Definition scheduled_visible (s : YStmt) : completed Mem :=
  schedule 1 (fun _ => denote_stmt s) (Some Fin.F1).

(** Backward-compatible name for the scheduler-visible scheduled computation. *)
Definition scheduled : YStmt -> completed Mem := scheduled_visible.

(** Erase scheduler spawn observations while preserving yield and memory events. *)
Definition handle_spawn : (yieldE + (spawnE + Mem)) ~> ictree (yieldE + Mem) :=
  fun event =>
    match event with
    | inl y => ICtree.trigger y
    | inr (inl Spawn) => Ret tt
    | inr (inr m) => ICtree.trigger m
    end.
Definition interp_spawn {X} (t : ictree (yieldE + (spawnE + Mem)) X) : ictree (yieldE + Mem) X :=
  interp handle_spawn t.

(** Erase cooperative yield observations, leaving only memory effects. *)
Definition handle_yield : (yieldE + Mem) ~> ictree Mem :=
  fun event =>
    match event with
    | inl Yield => Ret tt
    | inr m => ICtree.trigger m
    end.
Definition interp_yield {X} (t : ictree (yieldE + Mem) X) : ictree Mem X :=
  interp handle_yield t.

(** Erased scheduled interpretation: both scheduler [Spawn] and cooperative
    [Yield] observations are intentionally erased, leaving only memory effects. *)
Definition interp_scheduled_erased (s : YStmt) : ictree Mem unit :=
  interp_yield (interp_spawn (scheduled_visible s)).

(** Backward-compatible erased scheduled interpretation.  New concurrency-facing
    code should choose explicitly between [scheduled_visible] and
    [interp_scheduled_erased]. *)
Definition interp_scheduled : YStmt -> ictree Mem unit := interp_scheduled_erased.

(** Interpret a raw thread without scheduling by resolving [Fork] to [false],
    i.e. taking the active branch. *)
Definition handle_thread : YEff ~> ictree (yieldE + Mem) :=
  fun event =>
    match event with
    | inl y => ICtree.trigger y
    | inr (inl Fork) => Ret false
    | inr (inr m) => ICtree.trigger m
    end.
Definition interp_thread {X} (t : ictree YEff X) : ictree Mem X :=
  interp_yield (interp handle_thread t).

(** Erased expression instrumentation: raw thread-level [Yield] observations
    are erased before state instrumentation. *)
Definition instr_exp_erased (e : YExp) (ctx : Ctx) : ictreeW Ctx (nat * Ctx) :=
  instr_stateE (interp_thread (denote_exp e)) ctx.

(** Erased statement instrumentation: scheduler [Spawn] and cooperative [Yield]
    observations are erased before state instrumentation. *)
Definition instr_stmt_erased (s : YStmt) (ctx : Ctx) : ictreeW Ctx (unit * Ctx) :=
  instr_stateE (interp_scheduled_erased s) ctx.

(** Backward-compatible erased instrumentation aliases.  These names preserve the
    iteration-1 API, where instrumentation observed only memory/state effects. *)
Definition instr_exp : YExp -> Ctx -> ictreeW Ctx (nat * Ctx) := instr_exp_erased.
Definition instr_stmt : YStmt -> Ctx -> ictreeW Ctx (unit * Ctx) := instr_stmt_erased.
