From Stdlib Require Import
  Fin
  Vector
  Program.Equality.

From TICL Require Import
  ICTree.Interp.Yield.Observed
  ICTree.Logic.SchedulerFairness.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Events.Yield
  ICTree.Interp.Yield.Mod
  Logic.Core
  Logic.Kripke
  Lang.Yield.Syntax
  Lang.Yield.Denote
  Lang.Yield.Interp
  Utils.Vectors.

Import ICtree ICTreeNotations TiclNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.

(** * Source-level observed scheduler *)
(** The observation tier is entirely generic; a source program only supplies
    the start-up pool.  Nothing below discharges [SchedulerProgress]: the
    fairness result stays conditional on scheduler progress, and it speaks
    about scheduling-point offers, not about fair thread selection. *)

Definition scheduled_observed (s : YStmt) : observed_completed Mem :=
  schedule_with_offers 1 [denote_stmt s]%vector (Some Fin.F1).

Theorem forget_scheduled_observed_is_scheduled_visible (s : YStmt) :
  forget_scheduler_offers (scheduled_observed s) ~ scheduled_visible s.
Proof.
  unfold scheduled_observed, scheduled_visible.
  apply forget_scheduler_offers_preserves_schedule.
Qed.

Theorem scheduled_observed_every_live_slot_eventually_offered (s : YStmt) :
  SchedulerProgress (scheduled_observed s) Pure ->
  agc scheduling_point_offer_obligation (scheduled_observed s) Pure.
Proof.
  unfold scheduled_observed.
  apply every_live_slot_is_eventually_offered_at_scheduling_points.
Qed.
