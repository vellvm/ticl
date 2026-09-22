From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector.
From Stdlib Require Import Classes.Morphisms.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Interp.State.Mod
  ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin Utils.Vectors.
From TICL Require Import Lang.CSL.Queue.Representation.
From examples Require Import CSL.Allocator.Layout
  CSL.Allocator.Program CSL.Allocator.Model.

Import ICtree ICTreeNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope list_scope.


Definition client_next base client : option (option unit) -> thread sE :=
  until_tail (client_round base client) (fun _ => Ret tt).
Definition remote_after_free base client (flow : option unit) : thread sE :=
  match flow with
  | None => client_next base client None
  | Some _ =>
      denote_flow (CBind CYield (fun _ => CRet (Some tt : option unit))) >>=
        client_next base client
  end.
Definition remote_cas_tail base block old : CProg (option unit) :=
  CBind (CCAS (remote_head base) old block) (fun success =>
    if success then
      CBind (CEmit tag_retire block) (fun _ => CRet (None : option unit))
    else
      CBind (CEmit tag_retry block) (fun _ =>
      CBind CYield (fun _ => CRet (Some tt : option unit)))).
Definition remote_link_tail base block old : CProg (option unit) :=
  CBind (CWrite block old) (fun _ =>
  CBind CYield (fun _ => remote_cas_tail base block old)).

Definition remote_residual (base : nat) (client : bool) (pc : remote_pc) : thread sE :=
  match pc with
  | RPoll => denote (remote_client base client)
  | RRead block => denote_flow (remote_free base block) >>= remote_after_free base client
  | RLink block old => denote_flow (remote_link_tail base block old) >>=
      until_tail (remote_attempt base block) (remote_after_free base client)
  | RCAS block old => denote_flow (remote_cas_tail base block old) >>=
      until_tail (remote_attempt base block) (remote_after_free base client)
  end.

Definition owner_next base : option (option unit) -> thread sE :=
  until_tail (owner_round base) (fun _ => Ret tt).
Definition owner_offer_tail base (client : bool) : CProg (option unit) :=
  if client then
    CBind (offer_block base true) (fun _ => CRet (Some tt : option unit))
  else
    CBind (offer_block base false) (fun _ =>
    CBind (offer_block base true) (fun _ => CRet (Some tt : option unit))).
Definition owner_after_collect base (flow : option unit) : thread sE :=
  match flow with
  | None => owner_next base None
  | Some _ => denote_flow (owner_offer_tail base false) >>= owner_next base
  end.
Definition owner_after_detach base (flow : option unit) : thread sE :=
  match flow with
  | None => owner_after_collect base None
  | Some _ => denote_flow (CUntilNone (reclaim_step base)) >>= owner_after_collect base
  end.
Definition detach_cas_tail base old : CProg (option unit) :=
  CBind (CCAS (remote_head base) old 0) (fun success =>
    if success then
      CBind (CWrite (drain_head base) old) (fun _ =>
      CBind CYield (fun _ => CRet (None : option unit)))
    else CBind CYield (fun _ => CRet (Some tt : option unit))).

Definition owner_residual (base : nat) (pc : owner_pc) : thread sE :=
  match pc with
  | ORead => denote (CUntilNone (owner_round base))
  | OCAS old => denote_flow (detach_cas_tail base old) >>=
      until_tail (detach_attempt base) (owner_after_detach base)
  | ODrain => denote_flow (CUntilNone (reclaim_step base)) >>= owner_after_collect base
  | OOffer client => denote_flow (owner_offer_tail base client) >>= owner_next base
  end.
Definition allocator_pool (base : nat) (s : AState) : pool sE 3 :=
  [remote_residual base true (remote1_state s);
   remote_residual base false (remote0_state s);
   owner_residual base (owner_state s)]%vector.
Definition source_pool0 base : pool sE 3 :=
  [denote (remote_client base true); denote (remote_client base false);
   denote (CUntilNone (owner_round base))]%vector.
Definition state_agrees (sigma : SSig) (s : AState) : Prop :=
  heq (fst sigma) (aheap s) /\ snd sigma = acount s.

Lemma allocator_inv_state_equiv base capacity s t :
  state_equiv s t -> allocator_inv base capacity s -> allocator_inv base capacity t.
Proof.
  destruct s as [h c op r0 r1], t as [k d oq q0 q1].
  intros [Hh [Hc [Ho [H0 H1]]]]; cbn in Hh, Hc, Ho, H0, H1.
  subst d oq q0 q1.
  intros (Hbase & Hback & L & R & D & m0 & m1 & Hr & Hl & Hd & CL & CR & CD &
    Hm0 & Hm1 & Hp & Hop & Ho & Hc0 & Hc1).
  cbn [aheap owner_state remote0_state remote1_state] in *.
  unfold allocator_inv; cbn [aheap owner_state remote0_state remote1_state].
  split; [exact Hbase|]; split.
  - intro x; rewrite <- Hh; apply Hback.
  - exists L, R, D, m0, m1.
    repeat split; try assumption;
      try solve [rewrite <- Hh; assumption];
      try solve [eapply ai_free_chain_frame;
        [eassumption|intros; symmetry; apply Hh]];
      try solve [eapply ai_cached_remote_frame;
        [eassumption|intros; symmetry; apply Hh]].
Qed.

Definition source_reheap (sigma : SSig) (s : AState) : AState :=
  {| aheap := fst sigma; acount := snd sigma;
     owner_state := owner_state s;
     remote0_state := remote0_state s; remote1_state := remote1_state s |}.

Lemma state_agrees_reheap sigma s :
  state_agrees sigma s -> state_equiv s (source_reheap sigma s).
Proof.
  intros [Hh Hc]; unfold state_equiv, source_reheap; cbn.
  split; [now apply heq_sym|]; repeat split; congruence.
Qed.

Lemma source_pool0_initial capacity c :
  pool_equ (source_pool0 1) (allocator_pool 1 (initial_state capacity c)).
Proof. apply pool_equ_refl. Qed.



Lemma interp_rr_init_links n (ts : pool sE (S n)) (i : Fin.t (S n))
  first count (K : option unit -> thread sE) m h c :
  (forall offset, Nat.lt offset (2 * count) ->
    h (first + offset)%nat <> None) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (init_links first count) >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
    (Some i) m (init_links_heap first count h,c).
Proof.
  revert first h; induction count as [|count IH]; intros first h Allocated.
  - cbn [init_links init_links_heap]; rewrite interp_rr_ret; reflexivity.
  - cbn [init_links init_links_heap]; rewrite interp_rr_bind.
    etransitivity.
    + apply interp_rr_write_present.
      specialize (Allocated 0 ltac:(cbn; lia)).
      now rewrite Nat.add_0_r in Allocated.
    + apply IH; intros offset O; apply upd_mono.
      replace (first + 2 + offset)%nat with (first + (2 + offset))%nat by lia.
      apply Allocated; cbn; lia.
Qed.

Lemma interp_nd_init_links n (ts : pool sE (S n)) (i : Fin.t (S n))
  first count (K : option unit -> thread sE) h c :
  (forall offset, Nat.lt offset (2 * count) ->
    h (first + offset)%nat <> None) ->
  interp_nd (S n)
    (ts @ i := (denote_flow (init_links first count) >>= K)) (Some i) (h,c) ~
  interp_nd (S n) (ts @ i := K (Some tt))
    (Some i) (init_links_heap first count h,c).
Proof.
  revert first h; induction count as [|count IH]; intros first h Allocated.
  - cbn [init_links init_links_heap]; rewrite interp_nd_source_ret; reflexivity.
  - cbn [init_links init_links_heap]; rewrite interp_nd_source_bind.
    etransitivity.
    + apply interp_nd_source_write_present.
      specialize (Allocated 0 ltac:(cbn; lia)).
      now rewrite Nat.add_0_r in Allocated.
    + apply IH; intros offset O; apply upd_mono.
      replace (first + 2 + offset)%nat with (first + (2 + offset))%nat by lia.
      apply Allocated; cbn; lia.
Qed.

(** The starting heap is the actual allocation overlay.  In particular the
    five metadata writes and every link write are checked against allocated
    cells, and the untouched payloads retain the allocation's zeroes. *)
Lemma interp_rr_init_page n (ts : pool sE (S n)) (i : Fin.t (S n))
  base capacity (K : option unit -> thread sE) m h c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (init_page base capacity) >>= K))
    (Some i) m (hunion (hblock base (page_size capacity)) h,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
    (Some i) m (page_heap base capacity h,c).
Proof.
  unfold init_page, page_heap.
  do 5 (rewrite interp_rr_bind; etransitivity;
    [apply interp_rr_write_present;
      repeat apply upd_mono;
      rewrite page_backing_in by
        (unfold remote_head, drain_head, mailbox, local_head, page_size; lia);
      discriminate |]).
  apply interp_rr_init_links; intros offset O.
  repeat apply upd_mono.
  rewrite page_backing_in by (unfold page_size; lia); discriminate.
Qed.

Lemma interp_nd_init_page n (ts : pool sE (S n)) (i : Fin.t (S n))
  base capacity (K : option unit -> thread sE) h c :
  interp_nd (S n)
    (ts @ i := (denote_flow (init_page base capacity) >>= K))
    (Some i) (hunion (hblock base (page_size capacity)) h,c) ~
  interp_nd (S n) (ts @ i := K (Some tt))
    (Some i) (page_heap base capacity h,c).
Proof.
  unfold init_page, page_heap.
  do 5 (rewrite interp_nd_source_bind; etransitivity;
    [apply interp_nd_source_write_present;
      repeat apply upd_mono;
      rewrite page_backing_in by
        (unfold remote_head, drain_head, mailbox, local_head, page_size; lia);
      discriminate |]).
  apply interp_nd_init_links; intros offset O.
  repeat apply upd_mono.
  rewrite page_backing_in by (unfold page_size; lia); discriminate.
Qed.

(** A first-fit equation is separated from the finite-heap existence proof,
    so concrete initialized source programs can use a known fresh base. *)
Lemma interp_rr_new_page_first n (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity base (K : option nat -> thread sE) m h c :
  Nat.lt 0 base -> block_free h base (page_size capacity) ->
  (forall j, Nat.lt 0 j -> Nat.lt j base ->
    ~ block_free h j (page_size capacity)) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (new_page capacity) >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some base))
    (Some i) m (page_heap base capacity h,c).
Proof.
  intros Positive Free First.
  unfold new_page; rewrite interp_rr_bind.
  rewrite interp_rr_alloc_first with (base:=base) by
    (try apply page_size_positive; assumption).
  rewrite interp_rr_bind; etransitivity.
  - apply interp_rr_init_page.
  - rewrite interp_rr_ret; reflexivity.
Qed.

Lemma interp_nd_new_page_first n (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity base (K : option nat -> thread sE) h c :
  Nat.lt 0 base -> block_free h base (page_size capacity) ->
  (forall j, Nat.lt 0 j -> Nat.lt j base ->
    ~ block_free h j (page_size capacity)) ->
  interp_nd (S n)
    (ts @ i := (denote_flow (new_page capacity) >>= K)) (Some i) (h,c) ~
  interp_nd (S n) (ts @ i := K (Some base))
    (Some i) (page_heap base capacity h,c).
Proof.
  intros Positive Free First.
  unfold new_page; rewrite interp_nd_source_bind.
  rewrite interp_nd_source_alloc_first with (base:=base) by
    (try apply page_size_positive; assumption).
  rewrite interp_nd_source_bind; etransitivity.
  - apply interp_nd_init_page.
  - rewrite interp_nd_source_ret; reflexivity.
Qed.

Lemma interp_rr_new_page n (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity (K : option nat -> thread sE) m h c :
  heap_finite h ->
  exists base,
    Nat.lt 0 base /\ block_free h base (page_size capacity) /\
    (forall j, Nat.lt 0 j -> Nat.lt j base ->
      ~ block_free h j (page_size capacity)) /\
    heap_finite (page_heap base capacity h) /\
    (forall x, h x <> None -> page_heap base capacity h x = h x) /\
    interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow (new_page capacity) >>= K)) (Some i) m (h,c) ~
    interp_schedule_rr sh (S n) (ts @ i := K (Some base))
      (Some i) m (page_heap base capacity h,c).
Proof.
  intro Finite.
  destruct (sh_alloc_finite h (page_size capacity) c Finite
    (page_size_positive capacity)) as (base & Positive & Free & First & Alloc).
  exists base; split; [exact Positive |]; split; [exact Free |].
  split; [exact First |]; split; [now apply page_heap_finite |].
  split; [now apply page_heap_old_frame |].
  apply interp_rr_new_page_first; assumption.
Qed.

Lemma interp_nd_new_page n (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity (K : option nat -> thread sE) h c :
  heap_finite h ->
  exists base,
    Nat.lt 0 base /\ block_free h base (page_size capacity) /\
    (forall j, Nat.lt 0 j -> Nat.lt j base ->
      ~ block_free h j (page_size capacity)) /\
    heap_finite (page_heap base capacity h) /\
    (forall x, h x <> None -> page_heap base capacity h x = h x) /\
    interp_nd (S n)
      (ts @ i := (denote_flow (new_page capacity) >>= K)) (Some i) (h,c) ~
    interp_nd (S n) (ts @ i := K (Some base))
      (Some i) (page_heap base capacity h,c).
Proof.
  intro Finite.
  destruct (sh_alloc_finite h (page_size capacity) c Finite
    (page_size_positive capacity)) as (base & Positive & Free & First & Alloc).
  exists base; split; [exact Positive |]; split; [exact Free |].
  split; [exact First |]; split; [now apply page_heap_finite |].
  split; [now apply page_heap_old_frame |].
  apply interp_nd_new_page_first; assumption.
Qed.

(** Empty heaps accept the very first candidate, even when capacity is zero:
    the allocation request is always for at least the five metadata cells. *)
Lemma sh_alloc_page_hemp capacity c :
  runStateT (sh (inl (HAlloc (page_size capacity)))) (hemp,c) ~
    Ret (1,(hunion (hblock 1 (page_size capacity)) hemp,c)).
Proof.
  apply sh_alloc_first.
  - apply page_size_positive.
  - lia.
  - intros offset O; reflexivity.
  - intros j Positive Before; lia.
Qed.

Lemma interp_rr_new_page_hemp n (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity (K : option nat -> thread sE) m c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (new_page capacity) >>= K)) (Some i) m (hemp,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some 1))
    (Some i) m (page_heap 1 capacity hemp,c).
Proof.
  apply interp_rr_new_page_first.
  - lia.
  - intros offset O; reflexivity.
  - intros j Positive Before; lia.
Qed.

Lemma interp_nd_new_page_hemp n (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity (K : option nat -> thread sE) c :
  interp_nd (S n)
    (ts @ i := (denote_flow (new_page capacity) >>= K)) (Some i) (hemp,c) ~
  interp_nd (S n) (ts @ i := K (Some 1))
    (Some i) (page_heap 1 capacity hemp,c).
Proof.
  apply interp_nd_new_page_first.
  - lia.
  - intros offset O; reflexivity.
  - intros j Positive Before; lia.
Qed.

(** Source read probes after dynamic initialization.  Instantiating [address]
    with metadata, link, or payload addresses combines these equations with
    the corresponding [page_heap_*] lookup laws, without assuming a fixture. *)

Lemma interp_rr_new_page_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity (address : nat -> nat) value (K : option nat -> thread sE) m c :
  page_heap 1 capacity hemp (address 1) = Some value ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind (new_page capacity)
      (fun base => CRead (address base))) >>= K)) (Some i) m (hemp,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some value))
    (Some i) m (page_heap 1 capacity hemp,c).
Proof.
  intro Lookup; rewrite interp_rr_bind, interp_rr_new_page_hemp.
  apply interp_rr_read_value; exact Lookup.
Qed.

Lemma interp_nd_new_page_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity (address : nat -> nat) value (K : option nat -> thread sE) c :
  page_heap 1 capacity hemp (address 1) = Some value ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CBind (new_page capacity)
      (fun base => CRead (address base))) >>= K)) (Some i) (hemp,c) ~
  interp_nd (S n) (ts @ i := K (Some value))
    (Some i) (page_heap 1 capacity hemp,c).
Proof.
  intro Lookup; rewrite interp_nd_source_bind, interp_nd_new_page_hemp.
  apply interp_nd_source_read_value; exact Lookup.
Qed.

Lemma interp_rr_new_page_read_missing n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity (address : nat -> nat) (K : option nat -> thread sE) m c :
  page_heap 1 capacity hemp (address 1) = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind (new_page capacity)
      (fun base => CRead (address base))) >>= K)) (Some i) m (hemp,c) ~
    (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intro Missing; rewrite interp_rr_bind, interp_rr_new_page_hemp.
  apply interp_rr_read_missing; exact Missing.
Qed.

Lemma interp_nd_new_page_read_missing n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity (address : nat -> nat) (K : option nat -> thread sE) c :
  page_heap 1 capacity hemp (address 1) = None ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CBind (new_page capacity)
      (fun base => CRead (address base))) >>= K)) (Some i) (hemp,c) ~
    (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intro Missing; rewrite interp_nd_source_bind, interp_nd_new_page_hemp.
  apply interp_nd_source_read_missing; exact Missing.
Qed.

(** The children are the actual scoped-fork children: their [None] branch
    terminates rather than running the parent's remaining initialization.
    Parent focus advances twice, but its cursor is unchanged until selection. *)
Theorem run_rr_allocator_initialized capacity c :
  run_rr (allocator_program capacity) hemp c ~
    interp_schedule_rr sh 3 (source_pool0 1) None 0
      (page_heap 1 capacity hemp,c).
Proof.
  unfold run_rr.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (allocator_program capacity) >>= fun _ => Ret tt))
    (Some Fin.F1) 0 (hemp,c) ~
    interp_schedule_rr sh 3 (source_pool0 1) None 0
      (page_heap 1 capacity hemp,c)).
  unfold allocator_program; rewrite interp_rr_bind, interp_rr_new_page_hemp.
  rewrite interp_rr_bind, interp_rr_fork.
  change (interp_schedule_rr sh 2
    ([denote (remote_client 1 false); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CFork (remote_client 1 true)) (fun _ => owner 1))
        >>= fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) 0 (page_heap 1 capacity hemp,c) ~
    interp_schedule_rr sh 3 (source_pool0 1) None 0
      (page_heap 1 capacity hemp,c)).
  rewrite interp_rr_bind, interp_rr_fork.
  change (interp_schedule_rr sh 3
    ([denote (remote_client 1 true); denote (remote_client 1 false); Ret tt]%vector
      @ Fin.FS (Fin.FS Fin.F1) :=
        (denote_flow (owner 1) >>= fun _ => Ret tt))
    (Some (Fin.FS (Fin.FS Fin.F1))) 0 (page_heap 1 capacity hemp,c) ~
    interp_schedule_rr sh 3 (source_pool0 1) None 0
      (page_heap 1 capacity hemp,c)).
  unfold owner; rewrite interp_rr_bind, interp_rr_yield; reflexivity.
Qed.

Theorem run_nd_allocator_initialized capacity c :
  run_nd (allocator_program capacity) hemp c ~
    interp_nd 3 (source_pool0 1) None (page_heap 1 capacity hemp,c).
Proof.
  unfold run_nd.
  change (interp_nd 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (allocator_program capacity) >>= fun _ => Ret tt))
    (Some Fin.F1) (hemp,c) ~
    interp_nd 3 (source_pool0 1) None (page_heap 1 capacity hemp,c)).
  unfold allocator_program; rewrite interp_nd_source_bind, interp_nd_new_page_hemp.
  rewrite interp_nd_source_bind, interp_nd_source_fork.
  change (interp_nd 2
    ([denote (remote_client 1 false); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CFork (remote_client 1 true)) (fun _ => owner 1))
        >>= fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) (page_heap 1 capacity hemp,c) ~
    interp_nd 3 (source_pool0 1) None (page_heap 1 capacity hemp,c)).
  rewrite interp_nd_source_bind, interp_nd_source_fork.
  change (interp_nd 3
    ([denote (remote_client 1 true); denote (remote_client 1 false); Ret tt]%vector
      @ Fin.FS (Fin.FS Fin.F1) :=
        (denote_flow (owner 1) >>= fun _ => Ret tt))
    (Some (Fin.FS (Fin.FS Fin.F1))) (page_heap 1 capacity hemp,c) ~
    interp_nd 3 (source_pool0 1) None (page_heap 1 capacity hemp,c)).
  unfold owner; rewrite interp_nd_source_bind, interp_nd_source_yield; reflexivity.
Qed.

From Stdlib Require Import List Program.Equality Classes.RelationClasses.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Trans ICTree.Events.Writer ICTree.Events.Yield
  ICTree.Interp.State.Mod ICTree.Interp.Yield.Mod
  ICTree.Interp.Yield.SBisim ICTree.Interp.Yield.RoundRobin
  ICTree.Interp.Refine Utils.Vectors.

Unset Implicit Arguments.

Import ICtree ICTreeNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope list_scope.

Lemma source_owner_read base :
  owner_residual base ORead ≅
  (denote_flow (detach_remote base) >>= owner_after_detach base).
Proof.
  unfold owner_residual, denote.
  rewrite source_raw_until.
  change ((denote_flow (owner_round base) >>= owner_next base) ≅
    (denote_flow (detach_remote base) >>= owner_after_detach base)).
  unfold owner_round; rewrite source_raw_bind.
  transitivity (denote_flow (collect_remote base) >>= owner_after_collect base).
  - apply equ_clo_bind_eq; intros [[]|]; reflexivity.
  - unfold collect_remote; rewrite source_raw_bind.
    apply equ_clo_bind_eq; intros [[]|]; reflexivity.
Qed.





Ltac allocator_residual_raw :=
  unfold remote_residual, owner_residual, remote_free, remote_client,
    detach_remote, remote_link_tail, remote_cas_tail, detach_cas_tail,
    owner_offer_tail, denote, client_next, remote_after_free,
    owner_next, owner_after_collect, owner_after_detach;
  csl_raw_equ.

Ltac allocator_residual_alignment :=
  cbn beta iota zeta;
  first [solve [apply guard_equ_equ; reflexivity] |
    lazymatch goal with
    | |- guard_equ (denote_flow (CRet _) >>= _) _ =>
        eapply guard_equ_trans; [apply guard_equ_equ; apply source_raw_ret|];
        allocator_residual_alignment
    | |- guard_equ (denote_flow (CBind _ _) >>= _) _ =>
        eapply guard_equ_trans; [apply guard_equ_equ; apply source_raw_bind|];
        allocator_residual_alignment
    | |- guard_equ (Ret _ >>= _) _ =>
        eapply guard_equ_trans; [apply guard_equ_equ; apply bind_ret_l|];
        allocator_residual_alignment
    | |- guard_equ (Guard _) _ => apply guard_equ_left; allocator_residual_alignment
    end |
    solve [apply guard_equ_equ; allocator_residual_raw] |
    rewrite source_owner_read; apply guard_equ_equ; allocator_residual_raw].

Ltac allocator_present :=
  first [congruence | apply upd_mono; allocator_present].

Ltac allocator_segment_steps :=
  repeat first
    [ progress (cbn beta iota zeta)
    | match goal with
      | H : Nat.eqb ?x ?y = ?b |- context [Nat.eqb ?x ?y] => rewrite H
      end
    | progress (rewrite Nat.eqb_refl)
    | lazymatch goal with
      | |- exact_source_segment_to (denote_flow (CBind _ _) >>= _) _ _ _ _ =>
          apply exact_source_bind
      | |- exact_source_segment_to (denote_flow (CRet _) >>= _) _ _ _ _ =>
          apply exact_source_ret
      | |- exact_source_segment_to (denote_flow (CUntilNone _) >>= _) _ _ _ _ =>
          apply exact_source_until
      | |- exact_source_segment_to (denote_flow (CRead _) >>= _) _ _ _ _ =>
          eapply exact_source_read; [eassumption|]
      | |- exact_source_segment_to (denote_flow (CWrite _ _) >>= _) _ _ _ _ =>
          eapply exact_source_write; [allocator_present|]
      | |- exact_source_segment_to (denote_flow (CEmit _ _) >>= _) _ _ _ _ =>
          apply exact_source_emit
      | |- exact_source_segment_to (denote_flow (CCAS _ _ _) >>= _) _ _ _ _ =>
          first [eapply exact_source_cas_success; [congruence|] |
            eapply exact_source_cas_failure;
              [eassumption|apply Nat.eqb_neq; eassumption|]]
      end
    | progress (
        lazymatch goal with
        | |- exact_source_segment_to ?src ?sigma ?logs ?target ?sigma' =>
          let src' := eval cbv beta iota zeta delta
            [remote_residual owner_residual denote remote_client remote_free
             remote_attempt remote_link_tail remote_cas_tail client_round
             owner_round collect_remote detach_remote detach_attempt
             detach_cas_tail reclaim_step owner_offer_tail offer_block
             until_tail client_next remote_after_free owner_next
             owner_after_collect owner_after_detach] in src in
          change (exact_source_segment_to src' sigma logs target sigma')
        end) ];
  apply exact_source_yield; allocator_residual_alignment.

(** The checked model branches provide precisely the successful heap reads.
    Repeated checked writes remain allocated even if addresses coincide; no
    heap extensionality, freshness assumption, or unchecked CAS is used here. *)
Local Opaque denote_flow ICtree.iter ICtree.bind.

Lemma turn_source_exact_segment base who s t event :
  turn base who s = Some (t,event) ->
  exists residual,
    ExactThreadSegment ((allocator_pool base s) $ slot_of_actor who)
      (aheap s,acount s) (event_obs event) residual (aheap t,acount t) /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  destruct s as [h c op r0 r1]; destruct who;
    [destruct op|destruct r0|destruct r1]; intro Hturn;
    cbn [turn aheap acount owner_state remote0_state remote1_state] in Hturn.
  all: repeat match type of Hturn with
    | context [match ?v with Some _ => _ | None => _ end] =>
        let Hv := fresh "Hcell" in destruct v eqn:Hv; try discriminate
    | context [if ?b then _ else _] =>
        let Hb := fresh "Htest" in destruct b eqn:Hb; try discriminate
    end.
  all: inversion Hturn; subst t event; clear Hturn.
  all: repeat match goal with
    | H : Nat.eqb ?x ?y = true |- _ =>
        apply Nat.eqb_eq in H; subst
    end.
  all: cbn [allocator_pool slot_of_actor Vector.nth aheap acount
    owner_state remote0_state remote1_state event_obs].
  all: lazymatch goal with
  | |- exists residual, ExactThreadSegment ?src ?sigma ?logs residual ?sigma' /\
      guard_equ residual ?target =>
      change (exact_source_segment_to src sigma logs target sigma')
  end.
  all: allocator_segment_steps.
Qed.

Local Transparent denote_flow ICtree.iter ICtree.bind.

Lemma turn_source_segment base who s t event :
  turn base who s = Some (t,event) ->
  exists residual,
    ThreadSegment ((allocator_pool base s) $ slot_of_actor who)
      (aheap s,acount s) (event_obs event) residual (aheap t,acount t) /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  intro Hturn; destruct (turn_source_exact_segment base who s t event Hturn)
    as (residual & Hseg & Htail).
  exists residual; split; [now apply ExactThreadSegment_segment|exact Htail].
Qed.


Lemma turn_other_slots base who s t event :
  turn base who s = Some (t,event) ->
  forall j, j <> slot_of_actor who ->
    ((allocator_pool base s) $ j) ≅ ((allocator_pool base t) $ j).
Proof.
  intro Hturn; intro j.
  rewrite <- (slot_of_actor_of_slot j).
  destruct (actor_of_slot j) eqn:Hactor.
  all: destruct s as [h c op r0 r1]; destruct who;
    cbn [turn aheap acount owner_state remote0_state remote1_state] in Hturn;
    intro Hne; try contradiction.
  all: repeat match type of Hturn with
    | context [match ?v with Some _ => _ | None => _ end] =>
        let Hv := fresh "Hcell" in destruct v eqn:Hv; try discriminate
    | context [match ?v with
        ORead => _ | OCAS _ => _ | ODrain => _ | OOffer _ => _ end] => destruct v
    | context [match ?v with
        RPoll => _ | RRead _ => _ | RLink _ _ => _ | RCAS _ _ => _ end] => destruct v
    | context [if ?b then _ else _] => destruct b
    end.
  all: inversion Hturn; subst t event; reflexivity.
Qed.

Lemma allocator_pool_state_equiv base s t :
  state_equiv s t -> pool_equ (allocator_pool base s) (allocator_pool base t).
Proof.
  intros [_ [_ [Ho [H0 H1]]]].
  unfold allocator_pool; rewrite Ho, H0, H1; apply pool_equ_refl.
Qed.

(** The concrete segment is first built with the actual heap function.  Only
    the model transition and ownership invariant are transported pointwise. *)
Theorem selected_turn_source_segment base capacity (ts : pool sE 3)
  sigma s who t event :
  pool_guard_equ ts (allocator_pool base s) ->
  state_agrees sigma s -> allocator_inv base capacity s ->
  turn base who s = Some (t,event) ->
  exists residual sigma',
    ThreadSegment (ts $ slot_of_actor who) sigma
      (event_obs event) residual sigma' /\
    state_agrees sigma' t /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  intros Hpool Hagree Hinv Hturn.
  pose proof (state_agrees_reheap sigma s Hagree) as Hreheap.
  destruct (turn_respects_heq_some base who s (source_reheap sigma s)
    t event Hreheap Hturn) as (actual & Hactual & Hnext).
  destruct (turn_source_segment base who
    (source_reheap sigma s) actual event Hactual)
    as (canonical & Hseg & Htail).
  change (ThreadSegment ((allocator_pool base s) $ slot_of_actor who)
    (fst sigma,snd sigma) (event_obs event) canonical
    (aheap actual,acount actual)) in Hseg.
  destruct sigma as [h c]; cbn [fst snd] in Hseg.
  destruct (guard_equ_segment
    ((allocator_pool base s) $ slot_of_actor who)
    (ts $ slot_of_actor who) (h,c) (event_obs event)
    canonical (aheap actual,acount actual)
    (guard_equ_sym _ _ (Hpool (slot_of_actor who))) Hseg)
    as (residual & Hraw & Hrawtail).
  exists residual, (aheap actual,acount actual); split; [exact Hraw|]; split.
  - destruct Hnext as [Hheap [Hcount _]].
    split; cbn; [now apply heq_sym|symmetry; exact Hcount].
  - eapply guard_equ_trans; [apply guard_equ_sym; exact Hrawtail|].
    eapply guard_equ_trans; [exact Htail|].
    apply guard_equ_equ; symmetry.
    apply (allocator_pool_state_equiv base t actual Hnext).
Qed.

Theorem selected_source_segment_exact base capacity (ts : pool sE 3)
  sigma s who t event logs residual sigma' :
  pool_guard_equ ts (allocator_pool base s) ->
  state_agrees sigma s -> allocator_inv base capacity s ->
  turn base who s = Some (t,event) ->
  ThreadSegment (ts $ slot_of_actor who) sigma logs residual sigma' ->
  logs = event_obs event /\ state_agrees sigma' t /\
  guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  intros Hpool Hagree Hinv Hturn Hseg.
  destruct (selected_turn_source_segment base capacity ts sigma s who t event
    Hpool Hagree Hinv Hturn) as (other & sigma2 & Hother & Hstate & Htail).
  destruct (ThreadSegment_deterministic (ts $ slot_of_actor who) sigma
    logs residual sigma' (event_obs event) other sigma2 Hseg Hother)
    as [Hlogs [Hsigma Hresidual]].
  subst sigma2; split; [exact Hlogs|]; split; [exact Hstate|].
  eapply guard_equ_trans; [apply guard_equ_equ; exact Hresidual|exact Htail].
Qed.

Theorem selected_source_segment_turn base capacity (ts : pool sE 3)
  sigma s who logs residual sigma' :
  pool_guard_equ ts (allocator_pool base s) ->
  state_agrees sigma s -> allocator_inv base capacity s ->
  ThreadSegment (ts $ slot_of_actor who) sigma logs residual sigma' ->
  exists t event,
    turn base who s = Some (t,event) /\
    logs = event_obs event /\ state_agrees sigma' t /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  intros Hpool Hagree Hinv Hseg.
  destruct (turn_total base capacity who s Hinv) as (t & event & Hturn).
  exists t, event; split; [exact Hturn|].
  eapply selected_source_segment_exact; eauto.
Qed.

Lemma selected_source_pool_update base (ts : pool sE 3) s who t event residual :
  pool_guard_equ ts (allocator_pool base s) ->
  turn base who s = Some (t,event) ->
  guard_equ residual ((allocator_pool base t) $ slot_of_actor who) ->
  pool_guard_equ (ts @ slot_of_actor who := residual) (allocator_pool base t).
Proof.
  intros Hpool Hturn Htail j.
  destruct (Fin.eq_dec j (slot_of_actor who)) as [->|Hne].
  - rewrite Vector.nth_replace_eq; exact Htail.
  - rewrite Vector.nth_replace_neq by congruence.
    eapply guard_equ_trans; [apply Hpool|].
    apply guard_equ_equ; exact (turn_other_slots base who s t event Hturn j Hne).
Qed.

(** This is a finite first-yield certificate, not a progress premise about
    model runs.  Its constructors cannot pass a yield or terminate in a
    return, fork, branch, missing-cell fault, or divergent prefix. *)
Theorem initialized_worker_next_yield base capacity (ts : pool sE 3)
  sigma s who :
  pool_guard_equ ts (allocator_pool base s) ->
  state_agrees sigma s -> allocator_inv base capacity s ->
  exists logs residual sigma',
    ThreadSegment (ts $ slot_of_actor who) sigma logs residual sigma'.
Proof.
  intros Hpool Hagree Hinv.
  destruct (turn_total base capacity who s Hinv) as (t & event & Hturn).
  destruct (selected_turn_source_segment base capacity ts sigma s who t event
    Hpool Hagree Hinv Hturn) as (residual & sigma' & Hseg & _).
  exists (event_obs event), residual, sigma'; exact Hseg.
Qed.

Theorem initialized_worker_no_terminal_prefix base capacity (ts : pool sE 3)
  sigma s who :
  pool_guard_equ ts (allocator_pool base s) ->
  state_agrees sigma s -> allocator_inv base capacity s ->
  not (guard_equ (ts $ slot_of_actor who) (Ret tt)) /\
  (forall k : bool -> thread sE,
    ~ guard_equ (ts $ slot_of_actor who) (Vis (inr (inl Fork)) k)) /\
  (forall n (k : Fin.t (S n) -> thread sE),
    ~ guard_equ (ts $ slot_of_actor who) (Br n k)) /\
  not (guard_equ (ts $ slot_of_actor who) (stuck : thread sE)).
Proof.
  intros Hpool Hagree Hinv.
  destruct (initialized_worker_next_yield base capacity ts sigma s who
    Hpool Hagree Hinv) as (logs & residual & sigma' & Hseg).
  repeat split.
  - intro Hbad.
    destruct (guard_equ_segment _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
    exact (ThreadSegment_ret_absurd sigma logs u sigma' Hfalse).
  - intros k Hbad.
    destruct (guard_equ_segment _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
    exact (ThreadSegment_fork_absurd k sigma logs u sigma' Hfalse).
  - intros n k Hbad.
    destruct (guard_equ_segment _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
    exact (ThreadSegment_br_absurd n k sigma logs u sigma' Hfalse).
  - intro Hbad.
    destruct (guard_equ_segment _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
    exact (ThreadSegment_stuck_absurd sigma logs u sigma' Hfalse).
Qed.

Theorem initialized_worker_no_fault_or_divergence base capacity (ts : pool sE 3)
  sigma s who :
  pool_guard_equ ts (allocator_pool base s) ->
  state_agrees sigma s -> allocator_inv base capacity s ->
  not (is_stuck (ts $ slot_of_actor who)) /\
  not (guard_equ (ts $ slot_of_actor who) (spin : thread sE)) /\
  (forall (e : sE) (k : encode e -> thread sE),
    guard_equ (ts $ slot_of_actor who) ((@go CEff _ unit (VisF (inr (inr e) : CEff) k))) ->
    ~ (runStateT (sh e) sigma ~ (stuck : ictreeW SObs (encode e * SSig)))).
Proof.
  intros Hpool Hagree Hinv.
  destruct (initialized_worker_next_yield base capacity ts sigma s who
    Hpool Hagree Hinv) as (logs & residual & sigma' & Hseg).
  split.
  - intro Hstuck; apply Hstuck; eapply ThreadSegment_can_step; exact Hseg.
  - split.
    + intro Hbad.
      destruct (guard_equ_segment _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
      exact (ThreadSegment_spin_absurd sigma logs u sigma' Hfalse).
    + intros e k Hhead Hfault.
      destruct (guard_equ_segment _ _ _ _ _ _ Hhead Hseg) as (u & Hfalse & _).
      exact (ThreadSegment_fault_absurd e k sigma logs u sigma' Hfault Hfalse).
Qed.


Local Lemma source_replace_turn base who s t event residual :
  turn base who s = Some (t,event) ->
  pool_equ (allocator_pool base s @ slot_of_actor who := residual)
    (allocator_pool base t @ slot_of_actor who := residual).
Proof.
  intros Hturn j; destruct (Fin.eq_dec j (slot_of_actor who)) as [->|Hne].
  - rewrite !Vector.nth_replace_eq; reflexivity.
  - rewrite !Vector.nth_replace_neq by congruence.
    exact (turn_other_slots base who s t event Hturn j Hne).
Qed.


(** Each equation encompasses every branch of the phase table.  The result
    retains the actual residual at None focus: guard_equ is not silently
    promoted to an unfocused-pool congruence. *)
Theorem turn_interp_nd base capacity who s t event :
  allocator_inv base capacity s -> turn base who s = Some (t,event) ->
  exists residual,
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who) /\
    interp_nd 3 (allocator_pool base s) (Some (slot_of_actor who))
      (aheap s,acount s) ~
    emit_list (event_obs event)
      (interp_nd 3 (allocator_pool base t @ slot_of_actor who := residual)
        None (aheap t,acount t)).
Proof.
  intros Hinv Hturn.
  destruct (turn_source_segment base who s t event Hturn)
    as (residual & Hseg & Htail).
  exists residual; split; [exact Htail|].
  etransitivity.
  - symmetry; apply equ_sbisim, interp_nd_equ, source_replace_current.
  - etransitivity.
    + exact (segment_interp_nd 2 (allocator_pool base s) (slot_of_actor who)
        ((allocator_pool base s) $ slot_of_actor who) (aheap s,acount s)
        (event_obs event) residual (aheap t,acount t) Hseg).
    + apply emit_list_sbisim, equ_sbisim, interp_nd_equ.
      exact (source_replace_turn base who s t event residual Hturn).
Qed.

Theorem turn_interp_rr base capacity who s t event cursor :
  allocator_inv base capacity s -> turn base who s = Some (t,event) ->
  exists residual,
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who) /\
    interp_schedule_rr sh 3 (allocator_pool base s) (Some (slot_of_actor who))
      cursor (aheap s,acount s) ~
    emit_list (event_obs event)
      (interp_schedule_rr sh 3
        (allocator_pool base t @ slot_of_actor who := residual)
        None cursor (aheap t,acount t)).
Proof.
  intros Hinv Hturn.
  destruct (turn_source_segment base who s t event Hturn)
    as (residual & Hseg & Htail).
  exists residual; split; [exact Htail|].
  etransitivity.
  - symmetry; apply equ_sbisim, interp_schedule_rr_equ,
      source_replace_current.
  - etransitivity.
    + exact (segment_interp_rr 2 (allocator_pool base s) (slot_of_actor who)
        ((allocator_pool base s) $ slot_of_actor who) cursor (aheap s,acount s)
        (event_obs event) residual (aheap t,acount t) Hseg).
    + apply emit_list_sbisim, equ_sbisim, interp_schedule_rr_equ.
      exact (source_replace_turn base who s t event residual Hturn).
Qed.

Theorem selected_turn_interp_nd base capacity (ts : pool sE 3)
  sigma s who t event :
  pool_guard_equ ts (allocator_pool base s) ->
  state_agrees sigma s -> allocator_inv base capacity s ->
  turn base who s = Some (t,event) ->
  exists residual sigma',
    state_agrees sigma' t /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who) /\
    interp_nd 3 ts (Some (slot_of_actor who)) sigma ~
    emit_list (event_obs event)
      (interp_nd 3 (ts @ slot_of_actor who := residual) None sigma').
Proof.
  intros Hpool Hagree Hinv Hturn.
  destruct (selected_turn_source_segment base capacity ts sigma s who t event
    Hpool Hagree Hinv Hturn) as (residual & sigma' & Hseg & Hstate & Htail).
  exists residual, sigma'; split; [exact Hstate|]; split; [exact Htail|].
  etransitivity.
  - symmetry; apply equ_sbisim, interp_nd_equ, source_replace_current.
  - exact (segment_interp_nd 2 ts (slot_of_actor who)
      (ts $ slot_of_actor who) sigma (event_obs event) residual sigma' Hseg).
Qed.

Theorem selected_turn_interp_rr base capacity (ts : pool sE 3)
  sigma s who t event cursor :
  pool_guard_equ ts (allocator_pool base s) ->
  state_agrees sigma s -> allocator_inv base capacity s ->
  turn base who s = Some (t,event) ->
  exists residual sigma',
    state_agrees sigma' t /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who) /\
    interp_schedule_rr sh 3 ts (Some (slot_of_actor who)) cursor sigma ~
    emit_list (event_obs event)
      (interp_schedule_rr sh 3 (ts @ slot_of_actor who := residual) None cursor sigma').
Proof.
  intros Hpool Hagree Hinv Hturn.
  destruct (selected_turn_source_segment base capacity ts sigma s who t event
    Hpool Hagree Hinv Hturn) as (residual & sigma' & Hseg & Hstate & Htail).
  exists residual, sigma'; split; [exact Hstate|]; split; [exact Htail|].
  etransitivity.
  - symmetry; apply equ_sbisim, interp_schedule_rr_equ,
      source_replace_current.
  - exact (segment_interp_rr 2 ts (slot_of_actor who)
      (ts $ slot_of_actor who) cursor sigma (event_obs event) residual sigma' Hseg).
Qed.

From Coinduction Require Import coinduction rel tactics.
Local Open Scope nat_scope.

Lemma selected_turn_exact_segment base (ts : pool sE 3) s who t event :
  pool_guard_equ ts (allocator_pool base s) -> turn base who s = Some (t,event) ->
  exists residual,
    ExactThreadSegment (ts $ slot_of_actor who) (aheap s,acount s)
      (event_obs event) residual (aheap t,acount t) /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  intros Hpool Hturn.
  destruct (turn_source_exact_segment base who s t event Hturn) as (residual & Hseg & Htail).
  exists residual; split; [|exact Htail].
  apply (proj2 (guard_equ_exact_segment_iff
    (ts $ slot_of_actor who) ((allocator_pool base s) $ slot_of_actor who)
    (Hpool (slot_of_actor who)) (aheap s,acount s) (event_obs event)
    residual (aheap t,acount t))); exact Hseg.
Qed.

Lemma selected_turn_rr_prefix base (ts : pool sE 3) s who t event cursor :
  pool_guard_equ ts (allocator_pool base s) -> turn base who s = Some (t,event) ->
  exists residual word,
    rr_prefix_events word = event_obs event /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who) /\
    interp_schedule_rr sh 3 ts (Some (slot_of_actor who)) cursor (aheap s,acount s) ≅
      rr_prefix word (Guard (interp_schedule_rr sh 3
        (ts @ slot_of_actor who := residual) None cursor (aheap t,acount t))).
Proof.
  intros Hpool Hturn.
  destruct (selected_turn_exact_segment base ts s who t event Hpool Hturn)
    as (residual & Hseg & Htail).
  destruct (exact_segment_rr_prefix 2 ts (slot_of_actor who)
    (ts $ slot_of_actor who) cursor (aheap s,acount s) (event_obs event)
    residual (aheap t,acount t) Hseg) as (word & Ew & Et).
  exists residual, word; split; [exact Ew|]; split; [exact Htail|].
  etransitivity; [|exact Et].
  symmetry; apply interp_schedule_rr_equ, source_replace_current.
Qed.

Lemma allocator_pool_rr_aligned base capacity : forall s ts cursor,
  allocator_inv base capacity s -> pool_guard_equ ts (allocator_pool base s) ->
  rr_aligned
    (interp_schedule_rr sh 3 ts None cursor (aheap s,acount s))
    (model_rr base s cursor).
Proof.
  cofix IH; intros s ts cursor Hinv Hpool.
  set (who := actor_of_slot (rr_pick 2 cursor)).
  assert (Eslot : slot_of_actor who = rr_pick 2 cursor).
  { unfold who; apply slot_of_actor_of_slot. }
  destruct (turn_total base capacity who s Hinv) as (next & event & Hturn).
  destruct (selected_turn_rr_prefix base ts s who next event (S cursor) Hpool Hturn)
    as (residual & word & Ew & Htail & Eprefix).
  set (next_tree := interp_schedule_rr sh 3
    (ts @ slot_of_actor who := residual) None (S cursor) (aheap next,acount next)).
  set (next_model := model_rr base next (S cursor)).
  assert (Hsource : interp_schedule_rr sh 3 ts None cursor (aheap s,acount s) ≅
    rr_guards 3 (rr_prefix word (Guard next_tree))).
  {
    etransitivity; [exact (segment_rr_select_exact 2 ts cursor (aheap s,acount s))|].
    apply (rr_guards_equ 3); rewrite <- Eslot; exact Eprefix.
  }
  assert (Hnextinv : allocator_inv base capacity next).
  { eapply turn_preserves_inv; eauto. }
  assert (Hnextpool : pool_guard_equ (ts @ slot_of_actor who := residual)
    (allocator_pool base next)).
  { eapply selected_source_pool_update; eauto. }
  destruct event as [o|]; cbn [event_obs] in Ew.
  - destruct (rr_prefix_one_event word o (Guard next_tree) Ew) as (n & m & Eword).
    eapply rr_align_log with (n := 3 + n) (m := 0) (o := o)
      (t' := rr_guards m (Guard next_tree)) (u' := Guard next_model).
    + etransitivity; [exact Hsource|].
      rewrite (rr_guards_add 3 n
        (Vis (Log o) (fun _ => rr_guards m (Guard next_tree)))).
      apply rr_guards_equ; exact Eword.
    + rewrite (unfold_model_rr base s cursor); fold who; rewrite Hturn; reflexivity.
    + eapply rr_align_guard with (n := m) (m := 0)
        (t' := next_tree) (u' := next_model).
      * rewrite rr_guards_guard; reflexivity.
      * reflexivity.
      * apply IH; assumption.
  - eapply rr_align_guard with (n := 3 + List.length word) (m := 0)
      (t' := next_tree) (u' := next_model).
    + etransitivity; [exact Hsource|].
      rewrite (rr_prefix_no_events word (Guard next_tree) Ew).
      rewrite <- (rr_guards_add 3 (List.length word) (Guard next_tree)).
      rewrite rr_guards_guard; reflexivity.
    + rewrite (unfold_model_rr base s cursor); fold who; rewrite Hturn; reflexivity.
    + apply IH; assumption.
Qed.

Lemma allocator_pool_rr_bisim base capacity s ts cursor :
  allocator_inv base capacity s -> pool_guard_equ ts (allocator_pool base s) ->
  interp_schedule_rr sh 3 ts None cursor (aheap s,acount s) ~ model_rr base s cursor.
Proof.
  intros Hinv Hpool; apply rr_aligned_sbisim.
  exact (allocator_pool_rr_aligned base capacity s ts cursor Hinv Hpool).
Qed.

Theorem run_rr_allocator_bisim capacity c :
  run_rr (allocator_program capacity) hemp c ~ model_rr 1 (initial_state capacity c) 0.
Proof.
  rewrite run_rr_allocator_initialized.
  apply (allocator_pool_rr_bisim 1 capacity (initial_state capacity c)).
  - apply initial_state_inv.
  - apply execution_pool_guard_equ, source_pool0_initial.
Qed.

From Coinduction Require Import coinduction rel tactics.
Local Notation st L := (coinduction.t (sb L)).


Lemma allocator_pool_nd_bisim base capacity : forall s ts,
  allocator_inv base capacity s -> pool_guard_equ ts (allocator_pool base s) ->
  interp_nd 3 ts None (aheap s,acount s) ~ model_nd base s.
Proof.
  unfold sbisim; apply_coinduction; fold_sbisim.
  intros R IH s ts Hinv Hpool.
  etransitivity; [apply (coinduction.gfp_bt (sb eq) R), interp_nd_select|].
  eapply equ_sbt_closed_goal; [reflexivity|apply unfold_model_nd|].
  apply step_sb_br_id; [reflexivity|intro i].
  destruct (turn_total base capacity (actor_of_slot i) s Hinv)
    as (next & event & Hturn).
  rewrite Hturn.
  destruct (selected_turn_exact_segment base ts s (actor_of_slot i) next event
    Hpool Hturn) as (residual & Hseg & Htail).
  pose proof (selected_source_pool_update base ts s (actor_of_slot i)
    next event residual Hpool Hturn Htail) as Hnextpool.
  apply ExactThreadSegment_segment in Hseg.
  pose proof (segment_interp_nd 2 ts (slot_of_actor (actor_of_slot i))
    (ts $ slot_of_actor (actor_of_slot i)) (aheap s,acount s)
    (event_obs event) residual (aheap next,acount next) Hseg) as Esegment.
  rewrite slot_of_actor_of_slot in Esegment, Hnextpool.
  assert (Efocus : interp_nd 3 ts (Some i) (aheap s,acount s) ~
    emit_list (event_obs event)
      (interp_nd 3 (ts @ i := residual) None (aheap next,acount next))).
  {
    etransitivity; [|exact Esegment].
    symmetry; apply equ_sbisim, interp_nd_equ,
      source_replace_current.
  }
  assert (Hnextinv : allocator_inv base capacity next).
  { eapply turn_preserves_inv; eauto. }
  etransitivity; [apply (coinduction.gfp_t (sb eq) R); exact Efocus|].
  assert (Hcontinue : st eq R
    (interp_nd 3 (ts @ i := residual) None (aheap next,acount next))
    (Guard (model_nd base next))).
  {
    etransitivity; [exact (IH next (ts @ i := residual) Hnextinv Hnextpool)|].
    apply (coinduction.gfp_t (sb eq) R); symmetry; exact (sb_guard (model_nd base next)).
  }
  destruct event as [o|]; cbn [event_obs].
  - eapply equ_clos_st_goal;
      [reflexivity|symmetry; exact (emit_list_cons o [] (Guard (model_nd base next)))|].
    apply (emit_list_st R [o]); exact Hcontinue.
  - exact Hcontinue.
Qed.

Theorem run_nd_allocator_bisim capacity c :
  run_nd (allocator_program capacity) hemp c ~ model_nd 1 (initial_state capacity c).
Proof.
  rewrite run_nd_allocator_initialized.
  apply (allocator_pool_nd_bisim 1 capacity (initial_state capacity c)).
  - apply initial_state_inv.
  - apply execution_pool_guard_equ, source_pool0_initial.
Qed.
