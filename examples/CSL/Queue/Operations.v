From Stdlib Require Import List Arith.PeanoNat.
From examples Require Import CSL.Queue.Representation.
From TICL Require Import
  CTree.Core
  CTree.Events.Heap
  CTree.Events.Writer
  CTree.Interp.State.Mod.

Import CTree CTreeNotations ListNotations.
Local Open Scope ctree_scope.

(** The memory operations of one rotation are independent of its observation alphabet. *)
Definition queue_turn {E B : Type -> Type} `{heapE -< E} {X}
  (emit_value : nat -> ctree E B unit) (hdr : nat) (tail : ctree E B X) : ctree E B X :=
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

Lemma queue_turn_equ {E B : Type -> Type} `{heapE -< E} {X}
  (emit_value : nat -> ctree E B unit) hdr (t u : ctree E B X) :
  t ≅ u -> queue_turn emit_value hdr t ≅ queue_turn emit_value hdr u.
Proof.
  intro Htu; unfold queue_turn.
  do 9 (apply equ_clo_bind_eq; intro).
  exact Htu.
Qed.

Lemma queue_turn_bind {E B : Type -> Type} `{heapE -< E} {X Y}
  (emit_value : nat -> ctree E B unit) hdr (tail : ctree E B X) (k : X -> ctree E B Y) :
  (queue_turn emit_value hdr tail >>= k) ≅ queue_turn emit_value hdr (tail >>= k).
Proof.
  unfold queue_turn.
  do 9 (etransitivity; [apply bind_bind|]; apply equ_clo_bind_eq; intro).
  reflexivity.
Qed.

(** A logged prefix as a single [Vis] node.  [log o;; t] is a bind whose two
    trees may live at different [ctree] universes, which blocks the bind
    congruences on [interp_state] results; the [Vis] form has one universe,
    so [sb_vis] applies. *)
Lemma log_vis {W B X} (o : W) (t : ctreeW W B X) :
  (log o;; t) ≅ Vis (Log o) (fun _ => t).
Proof.
  unfold log; rewrite bind_trigger; step; constructor; intros []; reflexivity.
Qed.

(** Stated directly at the CSL handler [sh]: a handler-generic statement over
    [ctreeW W B] pins the writer universe below ITree's monomorphic [stateT]
    universes and cannot be instantiated at [sh]. *)
Lemma queue_turn_spec {A : Type} {X}
  (emit_value : nat -> ctree (heapE +' (stateE Ctx.Ctx +' writerE A)) Bn unit)
  (observe_value : nat -> nat -> CSLObs A) :
  (forall value h allocs ctx c (tail : ctree (heapE +' (stateE Ctx.Ctx +' writerE A)) Bn X),
    interp_state sh (emit_value value;; tail) ((h,allocs),(ctx,c)) ~
      (log (observe_value value c);;
       interp_state sh tail ((h,allocs),(ctx,S c)))) ->
  forall hdr a ns value values h allocs ctx c
    (tail : ctree (heapE +' (stateE Ctx.Ctx +' writerE A)) Bn X),
    qrep hdr (a :: ns) (value :: values) h ->
    interp_state sh (queue_turn emit_value hdr tail) ((h,allocs),(ctx,c)) ~
      (log (observe_value value c);;
       interp_state sh tail
         ((rot_heap hdr a (List.hd 0 ns) (zof hdr ns) h,allocs),(ctx,S c))).
Proof.
  intros Emit hdr a ns value values h allocs ctx c tail Hq.
  set (other := h_sum csl_context_handler (csl_emit_handler (A:=A))).
  change (sh (A:=A)) with (h_sum heap_handler other) in *.
  pose proof Hq as (Hwf & Hhd & Htl & Hch & Hdom).
  cbn in Hhd, Htl.
  apply chain_cons in Hch as (Ha & Hsa & Hch).
  pose proof (qwf_neqs _ _ _ Hwf) as (Hha & Hsha & Hhsa & Hshsa & Hhshdr).
  pose proof (qrep_zof_dom _ _ _ _ _ _ Hq) as Hzdom.
  assert (Hhdrdom : h hdr <> None) by (rewrite Htl; discriminate).
  assert (Hsadom : h (S a) <> None) by (rewrite Hsa; discriminate).
  assert (Hshdrdom : h (S hdr) <> None) by (rewrite Hhd; discriminate).
  assert (Hread_hdr : upd h (S hdr) (List.hd 0 ns) hdr = Some (last (a :: ns) 0))
    by (rewrite upd_neq by congruence; exact Htl).
  unfold queue_turn.
  etransitivity; [apply (interp_heap_rd other (S hdr) h allocs (ctx,c) a _ Hhd)|].
  etransitivity; [apply (interp_heap_rd other a h allocs (ctx,c) value _ Ha)|].
  etransitivity; [apply Emit|].
  rewrite !log_vis; apply sb_vis; intros _.
  etransitivity; [apply (interp_heap_rd other (S a) h allocs (ctx,S c) (List.hd 0 ns) _ Hsa)|].
  etransitivity;
    [apply (interp_heap_wr_present other (S hdr) h allocs (ctx,S c) (List.hd 0 ns) _ Hshdrdom)|].
  etransitivity; [apply (interp_heap_rd other hdr (upd h (S hdr) (List.hd 0 ns)) allocs (ctx,S c)
    (last (a :: ns) 0) _ Hread_hdr)|].
  cbn beta iota.
  rewrite (zof_compute hdr a ns Hwf).
  etransitivity; [apply (interp_heap_wr_present other (S (zof hdr ns)) _ allocs (ctx,S c) a _
    (upd_mono _ _ _ _ Hzdom))|].
  etransitivity; [apply (interp_heap_wr_present other (S a) _ allocs (ctx,S c) 0 _
    (upd_mono _ _ _ _ (upd_mono _ _ _ _ Hsadom)))|].
  etransitivity; [apply (interp_heap_wr_present other hdr _ allocs (ctx,S c) a _
    (upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _ Hhdrdom))))|].
  reflexivity.
Qed.
