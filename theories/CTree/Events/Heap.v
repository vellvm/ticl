From TICL Require Import CTree.Core.
From TICL Require Export Events.HeapE.

Definition heap_read {E B} `{heapE -< E} (a : nat) : ctree E B nat :=
  CTree.trigger (subevent _ (HRead a)).

Definition heap_write {E B} `{heapE -< E} (a v : nat) : ctree E B unit :=
  CTree.trigger (subevent _ (HWrite a v)).

Definition heap_alloc {E B} `{heapE -< E} (size : nat) : ctree E B nat :=
  CTree.trigger (subevent _ (HAlloc size)).

Definition heap_free {E B} `{heapE -< E} (a : nat) : ctree E B unit :=
  CTree.trigger (subevent _ (HFree a)).

Definition heap_cas {E B} `{heapE -< E} (a expected desired : nat) : ctree E B bool :=
  CTree.trigger (subevent _ (HCAS a expected desired)).
