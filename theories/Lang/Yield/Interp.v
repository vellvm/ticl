From Stdlib Require Import Fin Vector.
From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad
  Structures.MonadState
  Data.Map.FMapAList
  Data.String.
From TICL Require Import
  ICTree.Core
  ICTree.Interp.Core
  ICTree.Interp.State.Mod
  ICTree.Interp.Yield.Mod
  ICTree.Events.Yield
  ICTree.Events.State
  ICTree.Events.Writer
  Events.Core
  Events.StateE
  Lang.Maps
  Lang.Yield.Syntax
  Lang.Yield.Denote
  Utils.Vectors.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.

(** * Source-level startup and instrumentation wrappers *)
(** Every definition below is a direct instantiation of the raw interpreter
    layer in [ICTree.Interp.Yield.Mod] at the Yield source denotations. *)

(** Start a source statement as a singleton pool focused on its only thread.
    This is the scheduler-visible view: source [Fork] events have been
    scheduled into scheduler [Spawn] observations, and cooperative [Yield]
    observations remain visible alongside memory effects. *)
Definition scheduled_visible (s : YStmt) : completed Mem :=
  schedule 1 [denote_stmt s]%vector (Some Fin.F1).

(** Backward-compatible name for the scheduler-visible scheduled computation. *)
Definition scheduled : YStmt -> completed Mem := scheduled_visible.

(** Erased scheduled interpretation: both scheduler [Spawn] and cooperative
    [Yield] observations are intentionally erased, leaving only memory effects. *)
Definition interp_scheduled_erased (s : YStmt) : ictree Mem unit :=
  interp_yield (interp_spawn (scheduled_visible s)).

(** Backward-compatible erased scheduled interpretation.  New concurrency-facing
    code should choose explicitly between [scheduled_visible] and
    [interp_scheduled_erased]. *)
Definition interp_scheduled : YStmt -> ictree Mem unit := interp_scheduled_erased.

(** Erased expression instrumentation: raw thread-level [Yield] observations
    are erased before state instrumentation. *)
Definition instr_exp_erased (e : YExp) (ctx : Ctx) : ictreeW Ctx (nat * Ctx) :=
  instr_thread (denote_exp e) ctx.

(** Flow-preserving erased statement instrumentation for structural facts whose
    contracts must expose [Fallthrough] versus [HaltThread].  The public
    [instr_stmt_erased] remains the scheduled unit-returning view. *)
Definition instr_stmt_flow_erased
    (s : YStmt) (ctx : Ctx) : ictreeW Ctx (YStmtFlow * Ctx) :=
  instr_thread (denote_stmt_flow s) ctx.

(** Erased statement instrumentation: scheduler [Spawn] and cooperative [Yield]
    observations are erased before state instrumentation. *)
Definition instr_stmt_erased (s : YStmt) (ctx : Ctx) : ictreeW Ctx (unit * Ctx) :=
  instr_schedule 1 [denote_stmt s]%vector (Some Fin.F1) ctx.

(** Backward-compatible erased instrumentation aliases.  These names preserve the
    iteration-1 API, where instrumentation observed only memory/state effects. *)
Definition instr_exp : YExp -> Ctx -> ictreeW Ctx (nat * Ctx) := instr_exp_erased.
Definition instr_stmt : YStmt -> Ctx -> ictreeW Ctx (unit * Ctx) := instr_stmt_erased.
