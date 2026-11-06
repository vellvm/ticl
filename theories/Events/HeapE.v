Variant heapE : Type -> Type :=
| HRead (a : nat) : heapE nat
| HWrite (a v : nat) : heapE unit
| HAlloc (size : nat) : heapE nat
| HFree (a : nat) : heapE unit
| HCAS (a expected desired : nat) : heapE bool.
