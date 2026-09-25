From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector.
From TICL Require Import ICTree.Interp.Yield.Execution.
From TICL Require Import Utils.Execution.
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
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (init_links first count) >>= K)) (Some i) (h,c) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
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
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (init_page base capacity) >>= K))
    (Some i) (hunion (hblock base (page_size capacity)) h,c) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
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
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (new_page capacity) >>= K)) (Some i) (h,c) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some base))
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
  destruct (heap_handler_alloc_finite h (page_size capacity) c Finite
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
    interp_schedule_nd sh (S n)
      (ts @ i := (denote_flow (new_page capacity) >>= K)) (Some i) (h,c) ~
    interp_schedule_nd sh (S n) (ts @ i := K (Some base))
      (Some i) (page_heap base capacity h,c).
Proof.
  intro Finite.
  destruct (heap_handler_alloc_finite h (page_size capacity) c Finite
    (page_size_positive capacity)) as (base & Positive & Free & First & Alloc).
  exists base; split; [exact Positive |]; split; [exact Free |].
  split; [exact First |]; split; [now apply page_heap_finite |].
  split; [now apply page_heap_old_frame |].
  apply interp_nd_new_page_first; assumption.
Qed.

(** Empty heaps accept the very first candidate, even when capacity is zero:
    the allocation request is always for at least the five metadata cells. *)

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
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (new_page capacity) >>= K)) (Some i) (hemp,c) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some 1))
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
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind (new_page capacity)
      (fun base => CRead (address base))) >>= K)) (Some i) (hemp,c) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some value))
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
    (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Missing; rewrite interp_rr_bind, interp_rr_new_page_hemp.
  apply interp_rr_read_missing; exact Missing.
Qed.

Lemma interp_nd_new_page_read_missing n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  capacity (address : nat -> nat) (K : option nat -> thread sE) c :
  page_heap 1 capacity hemp (address 1) = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind (new_page capacity)
      (fun base => CRead (address base))) >>= K)) (Some i) (hemp,c) ~
    (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
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
    interp_schedule_nd sh 3 (source_pool0 1) None (page_heap 1 capacity hemp,c).
Proof.
  unfold run_nd.
  change (interp_schedule_nd sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (allocator_program capacity) >>= fun _ => Ret tt))
    (Some Fin.F1) (hemp,c) ~
    interp_schedule_nd sh 3 (source_pool0 1) None (page_heap 1 capacity hemp,c)).
  unfold allocator_program; rewrite interp_nd_source_bind, interp_nd_new_page_hemp.
  rewrite interp_nd_source_bind, interp_nd_source_fork.
  change (interp_schedule_nd sh 2
    ([denote (remote_client 1 false); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CFork (remote_client 1 true)) (fun _ => owner 1))
        >>= fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) (page_heap 1 capacity hemp,c) ~
    interp_schedule_nd sh 3 (source_pool0 1) None (page_heap 1 capacity hemp,c)).
  rewrite interp_nd_source_bind, interp_nd_source_fork.
  change (interp_schedule_nd sh 3
    ([denote (remote_client 1 true); denote (remote_client 1 false); Ret tt]%vector
      @ Fin.FS (Fin.FS Fin.F1) :=
        (denote_flow (owner 1) >>= fun _ => Ret tt))
    (Some (Fin.FS (Fin.FS Fin.F1))) (page_heap 1 capacity hemp,c) ~
    interp_schedule_nd sh 3 (source_pool0 1) None (page_heap 1 capacity hemp,c)).
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
      | |- (segment_to sh csl_equ) (denote_flow (CBind _ _) >>= _) _ _ _ _ =>
          apply exact_source_bind
      | |- (segment_to sh csl_equ) (denote_flow (CRet _) >>= _) _ _ _ _ =>
          apply exact_source_ret
      | |- (segment_to sh csl_equ) (denote_flow (CUntilNone _) >>= _) _ _ _ _ =>
          apply exact_source_until
      | |- (segment_to sh csl_equ) (denote_flow (CRead _) >>= _) _ _ _ _ =>
          eapply exact_source_read; [eassumption|]
      | |- (segment_to sh csl_equ) (denote_flow (CWrite _ _) >>= _) _ _ _ _ =>
          eapply exact_source_write; [allocator_present|]
      | |- (segment_to sh csl_equ) (denote_flow (CEmit _ _) >>= _) _ _ _ _ =>
          apply exact_source_emit
      | |- (segment_to sh csl_equ) (denote_flow (CCAS _ _ _) >>= _) _ _ _ _ =>
          first [eapply exact_source_cas_success; [congruence|] |
            eapply exact_source_cas_failure;
              [eassumption|apply Nat.eqb_neq; eassumption|]]
      end
    | progress (
        lazymatch goal with
        | |- (segment_to sh csl_equ) ?src ?sigma ?logs ?target ?sigma' =>
          let src' := eval cbv beta iota zeta delta
            [remote_residual owner_residual denote remote_client remote_free
             remote_attempt remote_link_tail remote_cas_tail client_round
             owner_round collect_remote detach_remote detach_attempt
             detach_cas_tail reclaim_step owner_offer_tail offer_block
             until_tail client_next remote_after_free owner_next
             owner_after_collect owner_after_detach] in src in
          change ((segment_to sh csl_equ) src' sigma logs target sigma')
        end) ];
  apply exact_source_yield; allocator_residual_alignment.

(** The checked model branches provide precisely the successful heap reads.
    Repeated checked writes remain allocated even if addresses coincide; no
    heap extensionality, freshness assumption, or unchecked CAS is used here. *)
Local Opaque denote_flow ICtree.iter ICtree.bind.

Lemma turn_source_exact_segment base who s t event :
  turn base who s = Some (t,event) ->
  exists residual,
    (ThreadSegment sh csl_equ) ((allocator_pool base s) $ slot_of_actor who)
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
  | |- exists residual, (ThreadSegment sh csl_equ) ?src ?sigma ?logs residual ?sigma' /\
      guard_equ residual ?target =>
      change ((segment_to sh csl_equ) src sigma logs target sigma')
  end.
  all: allocator_segment_steps.
Qed.

Local Transparent denote_flow ICtree.iter ICtree.bind.

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

(** ** The allocator's pool-simulation certificate.

    One instantiation of [ICTree.Interp.Yield.Execution.PoolSimulation]; the
    scheduling-equivalence theorems it unlocks are the library's, so no
    allocator copy of the ND coinduction or the RR guard-alignment proof
    remains.  The exact segment is built at the ACTUAL heap through
    [source_reheap] and the generic step-result congruence, so no heap
    function is extracted or equated. *)
Theorem allocator_simulation base capacity :
  PoolSimulation 2 sh slot_of_actor (turn base) (allocator_pool base)
    state_agrees (allocator_inv base capacity).
Proof.
  split.
  - intros who s Hinv.
    destruct (turn_total base capacity who s Hinv) as (t & event & Hturn).
    exists t, event; split; [exact Hturn | eapply turn_preserves_inv; eauto].
  - intros who s s' event sigma Hinv Hagree Hturn.
    pose proof (state_agrees_reheap sigma s Hagree) as Hreheap.
    destruct (step_some_compatible (turn base) state_equiv (turn_proper base)
      who s (source_reheap sigma s) s' event Hreheap Hturn) as (actual & Hactual & Hnext).
    destruct (turn_source_exact_segment base who
      (source_reheap sigma s) actual event Hactual)
      as (residual & Hseg & Htail).
    destruct sigma as [h c].
    cbn [source_reheap aheap acount owner_state remote0_state remote1_state
      allocator_pool fst snd] in Hseg, Htail |- *.
    exists residual, (aheap actual,acount actual).
    split; [exact Hseg |].
    split.
    + destruct Hnext as [Hheap [Hcount _]].
      split; cbn; [now apply heq_sym | symmetry; exact Hcount].
    + split.
      * eapply guard_equ_trans; [exact Htail |].
        apply guard_equ_equ; symmetry.
        exact (allocator_pool_state_equiv base s' actual Hnext
                 (slot_of_actor who)).
      * intros j Hj.
        etransitivity;
          [exact (turn_other_slots base who (source_reheap (h,c) s) actual event
                    Hactual j Hj) |].
        symmetry; exact (allocator_pool_state_equiv base s' actual Hnext j).
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
    promoted to an unfocused-pool congruence.  At the canonical state the
    handler state after the turn is EXACTLY the model's heap and counter. *)
Theorem turn_interp_nd base capacity who s t event :
  allocator_inv base capacity s -> turn base who s = Some (t,event) ->
  exists residual,
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who) /\
    interp_schedule_nd sh 3 (allocator_pool base s) (Some (slot_of_actor who))
      (aheap s,acount s) ~
    emit_list (event_obs event)
      (interp_schedule_nd sh 3 (allocator_pool base t @ slot_of_actor who := residual)
        None (aheap t,acount t)).
Proof.
  intros Hinv Hturn.
  destruct (turn_source_exact_segment base who s t event Hturn)
    as (residual & Hseg & Htail).
  exists residual; split; [exact Htail|].
  etransitivity.
  - exact (segment_interp_nd sh csl_equ (fun X t u => equ_sbisim t u)
      2 (allocator_pool base s) (slot_of_actor who) (aheap s,acount s)
      (event_obs event) residual (aheap t,acount t) Hseg).
  - apply emit_list_sbisim, equ_sbisim, (interp_schedule_nd_equ sh).
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
  destruct (turn_source_exact_segment base who s t event Hturn)
    as (residual & Hseg & Htail).
  exists residual; split; [exact Htail|].
  etransitivity.
  - exact (segment_interp_rr sh csl_equ (fun X t u => equ_sbisim t u)
      2 (allocator_pool base s) (slot_of_actor who) cursor (aheap s,acount s)
      (event_obs event) residual (aheap t,acount t) Hseg).
  - apply emit_list_sbisim, equ_sbisim, interp_schedule_rr_equ.
    exact (source_replace_turn base who s t event residual Hturn).
Qed.

(** At an arbitrary aligned pool and store the final handler state is only
    relationally determined, by the library segment of [allocator_simulation]. *)
Theorem selected_turn_interp_nd base capacity (ts : pool sE 3)
  sigma s who t event :
  pool_guard_equ ts (allocator_pool base s) ->
  state_agrees sigma s -> allocator_inv base capacity s ->
  turn base who s = Some (t,event) ->
  exists residual sigma',
    state_agrees sigma' t /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who) /\
    interp_schedule_nd sh 3 ts (Some (slot_of_actor who)) sigma ~
    emit_list (event_obs event)
      (interp_schedule_nd sh 3 (ts @ slot_of_actor who := residual) None sigma').
Proof.
  intros Hpool Hagree Hinv Hturn.
  destruct (pool_simulation_turn_nd (allocator_simulation base capacity)
    ts s who t event sigma Hinv Hagree Hpool Hturn)
    as (residual & sigma' & Hstate & Hnext & Hinterp).
  exists residual, sigma'; split; [exact Hstate|]; split.
  - pose proof (Hnext (slot_of_actor who)) as Htail.
    rewrite Vector.nth_replace_eq in Htail; exact Htail.
  - exact Hinterp.
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
  destruct (selected_turn_segment (allocator_simulation base capacity)
    ts s who t event sigma Hinv Hagree Hpool Hturn)
    as (residual & sigma' & Hseg & Hstate & Hnext).
  exists residual, sigma'; split; [exact Hstate|]; split.
  - pose proof (Hnext (slot_of_actor who)) as Htail.
    rewrite Vector.nth_replace_eq in Htail; exact Htail.
  - exact (segment_interp_rr sh csl_equ (fun X t u => equ_sbisim t u)
      2 ts (slot_of_actor who) cursor sigma
      (event_obs event) residual sigma' Hseg).
Qed.

From Coinduction Require Import coinduction rel tactics.
Local Open Scope nat_scope.

Lemma selected_turn_exact_segment base (ts : pool sE 3) s who t event :
  pool_guard_equ ts (allocator_pool base s) -> turn base who s = Some (t,event) ->
  exists residual,
    (ThreadSegment sh csl_equ) (ts $ slot_of_actor who) (aheap s,acount s)
      (event_obs event) residual (aheap t,acount t) /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  intros Hpool Hturn.
  destruct (turn_source_exact_segment base who s t event Hturn) as (residual & Hseg & Htail).
  exists residual; split; [|exact Htail].
  apply (proj2 ((guard_equ_segment_iff sh csl_equ)
    (ts $ slot_of_actor who) ((allocator_pool base s) $ slot_of_actor who)
    (Hpool (slot_of_actor who)) (aheap s,acount s) (event_obs event)
    residual (aheap t,acount t))); exact Hseg.
Qed.

Theorem run_rr_allocator_bisim capacity c :
  run_rr (allocator_program capacity) hemp c ~
    (model_rr 2 actor_of_slot (turn 1) (initial_state capacity c) 0
       : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  rewrite run_rr_allocator_initialized.
  exact (pool_simulation_rr_bisim actor_of_slot slot_of_actor_of_slot
    (allocator_simulation 1 capacity)
    (initial_state capacity c) (source_pool0 1) (page_heap 1 capacity hemp,c) 0
    (initial_state_inv capacity c) (conj (heq_refl _) eq_refl)
    (pool_equ_guard _ _ (source_pool0_initial capacity c))).
Qed.

Theorem run_nd_allocator_bisim capacity c :
  run_nd (allocator_program capacity) hemp c ~
    (model_nd 2 actor_of_slot (turn 1) (initial_state capacity c)
       : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  rewrite run_nd_allocator_initialized.
  exact (pool_simulation_nd_bisim actor_of_slot slot_of_actor_of_slot
    (allocator_simulation 1 capacity)
    (initial_state capacity c) (source_pool0 1) (page_heap 1 capacity hemp,c)
    (initial_state_inv capacity c) (conj (heq_refl _) eq_refl)
    (pool_equ_guard _ _ (source_pool0_initial capacity c))).
Qed.

(** The one program-specific validity entry point for raw source executions:
    the library's pool validity at the allocator handler, slot map, initial
    source pool, and initialized page. *)
Definition allocator_source_valid (capacity c : nat)
  (se : Execution (pool sE 3 * SSig) Actor (list (indexed (nat * nat)))) : Prop :=
  pool_execution_valid 2 sh slot_of_actor
    (source_pool0 1) (page_heap 1 capacity hemp,c) se.
