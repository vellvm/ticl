From TICL Require Import
  CTree.Core
  Utils.Vectors.

From TICL Require Export
  Events.YieldE.

Generalizable All Variables.

(** * Cooperative concurrency triggers, threads and pools *)

(** Create a [Yield] event node, with subevents if needed *)
Definition yield {E B} `{yieldE -< E} : ctree E B unit :=
  CTree.trigger (subevent _ Yield).

(** Create a [Fork] event node, with subevents if needed *)
Definition fork {E B} `{forkE -< E} : ctree E B bool :=
  CTree.trigger (subevent _ Fork).


(** A runnable source thread may yield, fork, or perform user effects. *)
Definition thread (E B : Type -> Type) := ctree (yieldE +' (forkE +' E)) B unit.

(** A scheduled computation exposes user effects and selected pool slots. *)
Definition completed (E B : Type -> Type) := ctree (E +' schedE) B unit.

(** A policy-scheduled pool exposes scheduling decisions and user events;
    yields and forks are interpreted. *)
Definition scheduled (E B : Type -> Type) := ctree (schedE +' E) B unit.

(** Finite thread pools are represented as vectors of threads. *)
Definition pool (E B : Type -> Type) (n : nat) := vec n (thread E B).
