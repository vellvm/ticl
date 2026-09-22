From TICL Require Import
  ICTree.Core
  Utils.Vectors.

From TICL Require Export
  Events.Core
  Events.YieldE.

Generalizable All Variables.

(** * Cooperative concurrency triggers, threads and pools *)

(** Create a [Yield] event node, with subevents if needed *)
Definition yield {E} `{HE : Encode E} `{RS : ReSum yieldE E}
           `{RR : @ReSumRet yieldE E Encode_yieldE HE RS} : ictree E unit :=
  @ICtree.trigger yieldE E Encode_yieldE HE RS RR Yield.

(** Create a [Fork] event node, with subevents if needed *)
Definition fork {E} `{HE : Encode E} `{RS : ReSum forkE E}
           `{RR : @ReSumRet forkE E Encode_forkE HE RS} : ictree E bool :=
  @ICtree.trigger forkE E Encode_forkE HE RS RR Fork.

(** Create a [Spawn] event node, with subevents if needed *)
Definition spawn {E} `{HE : Encode E} `{RS : ReSum spawnE E}
           `{RR : @ReSumRet spawnE E Encode_spawnE HE RS} : ictree E unit :=
  @ICtree.trigger spawnE E Encode_spawnE HE RS RR Spawn.

(** A runnable source thread may yield, fork, or perform user effects. *)
Definition thread (E : Type) `{Encode E} := ictree (yieldE + (forkE + E)) unit.

(** A scheduled computation exposes yields and spawns, but no raw forks. *)
Definition completed (E : Type) `{Encode E} := ictree (yieldE + (spawnE + E)) unit.

(** Finite thread pools are represented as vectors of threads. *)
Definition pool (E : Type) `{Encode E} (n : nat) := vec n (thread E).
