From Stdlib Require Import List Arith.PeanoNat.
From TICL Require Import
  Lang.CSL.Queue.Representation ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Heap ICTree.Events.Writer ICTree.Interp.State.Mod.

Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Typeclasses Opaque equ sbisim.

(** The memory operations of one rotation are independent of its observation alphabet. *)
Definition queue_turn {E : Type} `{HE : Encode E} `{RS : ReSum heapE E}
  `{RR : @ReSumRet heapE E Encode_heapE HE RS} {X}
  (emit_value : nat -> ictree E unit) (hdr : nat) (tail : ictree E X) : ictree E X :=
  a <- heap_read (S hdr);;
  value <- heap_read a;;
  emit_value value;;
  next <- heap_read (S a);;
  heap_write (S hdr) next;;
  last <- heap_read hdr;;
  heap_write (S (if Nat.eqb next 0 then hdr else last)) a;;
  heap_write (S a) 0;;
  heap_write hdr a;;
  tail.

Lemma queue_turn_equ {E : Type} `{HE : Encode E} `{RS : ReSum heapE E}
  `{RR : @ReSumRet heapE E Encode_heapE HE RS} {X}
  (emit_value : nat -> ictree E unit) hdr (t u : ictree E X) :
  t ≅ u -> queue_turn emit_value hdr t ≅ queue_turn emit_value hdr u.
Proof.
  intro Htu; unfold queue_turn.
  do 9 (apply equ_clo_bind_eq; intro).
  exact Htu.
Qed.

Lemma queue_turn_bind {E : Type} `{HE : Encode E} `{RS : ReSum heapE E}
  `{RR : @ReSumRet heapE E Encode_heapE HE RS} {X Y}
  (emit_value : nat -> ictree E unit) hdr (tail : ictree E X) (k : X -> ictree E Y) :
  (queue_turn emit_value hdr tail >>= k) ≅ queue_turn emit_value hdr (tail >>= k).
Proof.
  unfold queue_turn.
  do 9 (etransitivity; [apply bind_bind|]; apply equ_clo_bind_eq; intro).
  reflexivity.
Qed.

Lemma queue_turn_spec {E W : Type} {HE : Encode E} {X}
  (other : E ~> stateT SSig (ictreeW W))
  (emit_value : nat -> ictree (heapE + E) unit) (observe_value : nat -> nat -> W) :
  (forall value h c (tail : ictree (heapE + E) X),
    interp_state (h_sum heap_handler other) (emit_value value;; tail) (h,c) ~
      (log (observe_value value c);;
       interp_state (h_sum heap_handler other) tail (h,S c))) ->
  forall hdr a ns value values h c (tail : ictree (heapE + E) X),
    qrep hdr (a :: ns) (value :: values) h ->
    interp_state (h_sum heap_handler other) (queue_turn emit_value hdr tail) (h,c) ~
      (log (observe_value value c);;
       interp_state (h_sum heap_handler other) tail
         (rot_heap hdr a (hdf ns 0) (zof hdr ns) h,S c)).
Proof.
  intros Emit hdr a ns value values h c tail Hq.
  pose proof Hq as (Hwf & Hhd & Htl & Hch & Hdom).
  cbn in Hhd, Htl.
  destruct Hch as (Ha & Hsa & Hch).
  pose proof (qwf_neqs _ _ _ Hwf) as (Hha & Hsha & Hhsa & Hshsa & Hhshdr).
  pose proof (qrep_zof_dom _ _ _ _ _ _ Hq) as Hzdom.
  assert (Hhdrdom : h hdr <> None) by (rewrite Htl; discriminate).
  assert (Hsadom : h (S a) <> None) by (rewrite Hsa; discriminate).
  assert (Hshdrdom : h (S hdr) <> None) by (rewrite Hhd; discriminate).
  assert (Hread_hdr : upd h (S hdr) (hdf ns 0) hdr = Some (last (a :: ns) 0))
    by (rewrite upd_neq by congruence; exact Htl).
  unfold queue_turn.
  etransitivity; [apply (interp_heap_rd other (S hdr) h c a _ Hhd)|].
  etransitivity; [apply (interp_heap_rd other a h c value _ Ha)|].
  etransitivity; [apply Emit|].
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  etransitivity; [apply (interp_heap_rd other (S a) h (S c) (hdf ns 0) _ Hsa)|].
  etransitivity;
    [apply (interp_heap_wr_present other (S hdr) h (S c) (hdf ns 0) _ Hshdrdom)|].
  etransitivity; [apply (interp_heap_rd other hdr (upd h (S hdr) (hdf ns 0)) (S c)
    (last (a :: ns) 0) _ Hread_hdr)|].
  cbn beta iota.
  rewrite (zof_compute hdr a ns Hwf).
  etransitivity; [apply (interp_heap_wr_present other (S (zof hdr ns)) _ (S c) a _
    (upd_mono _ _ _ _ Hzdom))|].
  etransitivity; [apply (interp_heap_wr_present other (S a) _ (S c) 0 _
    (upd_mono _ _ _ _ (upd_mono _ _ _ _ Hsadom)))|].
  etransitivity; [apply (interp_heap_wr_present other hdr _ (S c) a _
    (upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _ Hhdrdom))))|].
  reflexivity.
Qed.
