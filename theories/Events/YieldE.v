Generalizable All Variables.

(** * Cooperative concurrency events *)
(** These are plain indexed event datatypes.  They are independent
    of any source language and of the [ctree] structure itself. *)

(** Cooperative scheduling point emitted by source-level [yield]. *)
Variant yieldE : Type -> Type := Yield : yieldE unit.

(** Thread-local fork choice.  The scheduler interprets the resulting [bool]
    to run both continuations. *)
Variant forkE : Type -> Type := Fork : forkE bool.


(** The zero-based slot selected at a scheduling boundary. *)
Variant schedE : Type -> Type :=
| Scheduled : nat -> schedE unit.
