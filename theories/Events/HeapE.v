From TICL Require Import Events.Core.

Variant heapE : Type :=
| HRead (a : nat)
| HWrite (a v : nat)
| HAlloc (size : nat)
| HFree (a : nat)
| HCAS (a expected desired : nat).

#[global] Instance Encode_heapE : Encode heapE :=
  fun e => match e with
           | HRead _ | HAlloc _ => nat
           | HWrite _ _ | HFree _ => unit
           | HCAS _ _ _ => bool
           end.
