From TICL Require Import ICTree.Core.
From TICL Require Export Events.Core Events.HeapE.

Definition heap_read {E : Type} `{HE : Encode E} `{RS : ReSum heapE E}
  `{RR : @ReSumRet heapE E Encode_heapE HE RS}
  (a : nat) : ictree E nat :=
  @ICtree.trigger heapE E Encode_heapE HE RS RR (HRead a).

Definition heap_write {E : Type} `{HE : Encode E} `{RS : ReSum heapE E}
  `{RR : @ReSumRet heapE E Encode_heapE HE RS}
  (a v : nat) : ictree E unit :=
  @ICtree.trigger heapE E Encode_heapE HE RS RR (HWrite a v).

Definition heap_alloc {E : Type} `{HE : Encode E} `{RS : ReSum heapE E}
  `{RR : @ReSumRet heapE E Encode_heapE HE RS}
  (size : nat) : ictree E nat :=
  @ICtree.trigger heapE E Encode_heapE HE RS RR (HAlloc size).

Definition heap_free {E : Type} `{HE : Encode E} `{RS : ReSum heapE E}
  `{RR : @ReSumRet heapE E Encode_heapE HE RS}
  (a : nat) : ictree E unit :=
  @ICtree.trigger heapE E Encode_heapE HE RS RR (HFree a).

Definition heap_cas {E : Type} `{HE : Encode E} `{RS : ReSum heapE E}
  `{RR : @ReSumRet heapE E Encode_heapE HE RS}
  (a expected desired : nat) : ictree E bool :=
  @ICtree.trigger heapE E Encode_heapE HE RS RR (HCAS a expected desired).
