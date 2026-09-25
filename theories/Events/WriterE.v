From TICL Require Import
  Events.Core.

Set Implicit Arguments.
Generalizable All Variables.

(** * Writer events over ghost state [S] *)
Section Writer.
  (** Events in Ticl get interpreted into a writer monad [writerE S]. Base formulas
  later reference those [log] events in specifications. *)
  Variable (S: Type).

  (** The writer event type is [writerE] *)
  Variant writerE : Type :=
    | Log : S -> writerE.
  
  (** Writer events are deterministic, always return [unit] *)
  #[global] Instance encode_writerE: Encode writerE :=
    fun e => unit.

End Writer.

Arguments Log {S}.

(** * Indexed observations.

    Instrumentation that wants to distinguish *occurrences* of the same
    payload logs the payload together with the count of observations that
    preceded it.  The payload is arbitrary, so the same representation serves
    a queue's popped value and a tagged allocator event. *)
Record indexed (A : Type) := stamp {
  indexed_value : A;
  indexed_index : nat
}.

Arguments stamp {A} _ _.
Arguments indexed_value {A} _.
Arguments indexed_index {A} _.

(** [P] holds of the payload AND the occurrence is not older than [lower].
    A retained world therefore cannot satisfy a strictly later bound. *)
Definition indexed_after {A} (P : A -> Prop) (lower : nat)
  (o : indexed A) : Prop :=
  P (indexed_value o) /\ lower <= indexed_index o.

