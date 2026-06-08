From Stdlib Require Import Fin.
From TICL Require Import ICTree.Core Events.Core.

Generalizable All Variables.

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

Definition yield {E} `{HE : Encode E} `{RS : ReSum yieldE E}
           `{RR : @ReSumRet yieldE E Encode_yieldE HE RS} : ictree E unit :=
  @ICtree.trigger yieldE E Encode_yieldE HE RS RR Yield.
Definition fork {E} `{HE : Encode E} `{RS : ReSum forkE E}
           `{RR : @ReSumRet forkE E Encode_forkE HE RS} : ictree E bool :=
  @ICtree.trigger forkE E Encode_forkE HE RS RR Fork.
Definition spawn {E} `{HE : Encode E} `{RS : ReSum spawnE E}
           `{RR : @ReSumRet spawnE E Encode_spawnE HE RS} : ictree E unit :=
  @ICtree.trigger spawnE E Encode_spawnE HE RS RR Spawn.

(** A runnable source thread may yield, fork, or perform user effects. *)
Definition thread (E : Type) `{Encode E} := ictree (yieldE + (forkE + E)) unit.

(** A scheduled computation exposes yields and spawns, but no raw forks. *)
Definition completed (E : Type) `{Encode E} := ictree (yieldE + (spawnE + E)) unit.

(** Finite thread pools are represented as functions from finite indices. *)
Definition pool (E : Type) `{Encode E} (n : nat) := Fin.t n -> thread E.
