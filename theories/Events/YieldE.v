From TICL Require Import Events.Core.

Generalizable All Variables.

(** * Cooperative concurrency events *)
(** These are plain event datatypes with their encodings.  They are independent
    of any source language and of the [ictree] structure itself. *)

(** Cooperative scheduling point emitted by source-level [yield]. *)
Variant yieldE : Type := Yield.

(** Thread-local fork choice.  The scheduler interprets the resulting [bool]
    to run both continuations. *)
Variant forkE : Type := Fork.

(** Scheduler-level observation that a fork spawned another runnable thread. *)
Variant spawnE : Type := Spawn.

#[global] Instance Encode_yieldE : Encode yieldE :=
  fun e => match e with Yield => unit end.
#[global] Instance Encode_forkE : Encode forkE :=
  fun e => match e with Fork => bool end.
#[global] Instance Encode_spawnE : Encode spawnE :=
  fun e => match e with Spawn => unit end.
