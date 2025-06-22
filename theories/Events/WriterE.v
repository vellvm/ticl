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

