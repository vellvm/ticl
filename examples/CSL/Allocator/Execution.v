From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector.
From Stdlib Require Import Classes.Morphisms.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Interp.State.Mod
  ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin Utils.Vectors.
From examples Require Import CSL.HeapQ CSL.Allocator.Layout
  CSL.Allocator.Program CSL.Allocator.Model.

Import ICtree ICTreeNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope list_scope.

Definition emit_list {X} (xs : list SObs) (t : ictreeW SObs X) : ictreeW SObs X :=
  List.fold_right (fun o k => log o;; k) t xs.
Definition turn_observations (event : option SObs) : list SObs :=
  match event with None => [] | Some o => [o] end.

(** A finite derivation stops at the first source yield.  The handler premise
    is its actual effect semantics, not an allocator transition assumption. *)
Inductive ThreadSegment : thread sE -> SSig -> list SObs -> thread sE -> SSig -> Prop :=
| segment_yield (k : unit -> thread sE) sigma :
    ThreadSegment (Vis (inl Yield) k) sigma [] (k tt) sigma
| segment_guard t sigma logs t' sigma' :
    ThreadSegment t sigma logs t' sigma' ->
    ThreadSegment (Guard t) sigma logs t' sigma'
| segment_user (e : sE) (k : encode e -> thread sE) sigma result sigma1
    before after t' sigma' :
    runStateT (sh e) sigma ~ emit_list before (Ret (result,sigma1)) ->
    ThreadSegment (k result) sigma1 after t' sigma' ->
    ThreadSegment (@go CEff _ unit (VisF (inr (inr e) : CEff) k))
      sigma (before ++ after) t' sigma'
| segment_equ t u sigma logs u' t' sigma' :
    t ≅ u -> ThreadSegment u sigma logs u' sigma' -> u' ≅ t' ->
    ThreadSegment t sigma logs t' sigma'.

(** Only finite leading guards and raw tree equivalence are forgotten.
    A real [Br] node is never included in this closure. *)
Inductive guard_equ : thread sE -> thread sE -> Prop :=
| guard_equ_equ t u : t ≅ u -> guard_equ t u
| guard_equ_left t u : guard_equ t u -> guard_equ (Guard t) u
| guard_equ_right t u : guard_equ t u -> guard_equ t (Guard u)
| guard_equ_sym t u : guard_equ t u -> guard_equ u t
| guard_equ_trans t u v : guard_equ t u -> guard_equ u v -> guard_equ t v.

(** These are the actual [CUntilNone] continuations, including halt flow. *)
Definition until_tail {A} (body : CProg (option A))
  (K : option unit -> thread sE) (flow : option (option A)) : thread sE :=
  match flow with
  | None => K None
  | Some None => K (Some tt)
  | Some (Some _) => Guard (denote_flow (CUntilNone body) >>= K)
  end.

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
Definition pool_guard_equ {n} (ts us : pool sE n) : Prop :=
  forall i, guard_equ (ts $ i) (us $ i).
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

Lemma execution_pool_guard_equ {n} (ts us : pool sE n) :
  pool_equ ts us -> pool_guard_equ ts us.
Proof. intros H i; apply guard_equ_equ, H. Qed.

Lemma execution_pool_guard_replace {n} (ts us : pool sE n)
  (i : Fin.t n) t u :
  pool_guard_equ ts us -> guard_equ t u ->
  pool_guard_equ (ts @ i := t) (us @ i := u).
Proof.
  intros Hpool Htu j; destruct (Fin.eq_dec j i) as [->|Hneq].
  - rewrite !Vector.nth_replace_eq; exact Htu.
  - rewrite !Vector.nth_replace_neq by congruence; apply Hpool.
Qed.

(** Silent checked writes, with the continuation held fixed while the state
    handler is simplified.  No congruence on a pool of bisimilar threads is
    used here. *)
Local Lemma allocator_interp_rr_write_present n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h c :
  h a <> None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
    (Some i) m (upd h a v,c).
Proof.
  intro Present.
  pose proof (sinterp_wr' a h c v
    (fun x : unit => (Ret x : ictree sE unit)) Present) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_rr_write.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.

Local Lemma allocator_interp_nd_write_present n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h c :
  h a <> None ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) (h,c) ~
  interp_nd (S n) (ts @ i := K (Some tt))
    (Some i) (upd h a v,c).
Proof.
  intro Present.
  pose proof (sinterp_wr' a h c v
    (fun x : unit => (Ret x : ictree sE unit)) Present) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_nd_source_write.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.

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
    + apply allocator_interp_rr_write_present.
      specialize (Allocated 0 ltac:(cbn; lia)).
      now rewrite Nat.add_0_r in Allocated.
    + apply IH; intros offset O; apply upd_preserves_present.
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
    + apply allocator_interp_nd_write_present.
      specialize (Allocated 0 ltac:(cbn; lia)).
      now rewrite Nat.add_0_r in Allocated.
    + apply IH; intros offset O; apply upd_preserves_present.
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
    [apply allocator_interp_rr_write_present;
      repeat apply upd_preserves_present;
      rewrite page_backing_in by
        (unfold remote_head, drain_head, mailbox, local_head, page_size; lia);
      discriminate |]).
  apply interp_rr_init_links; intros offset O.
  repeat apply upd_preserves_present.
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
    [apply allocator_interp_nd_write_present;
      repeat apply upd_preserves_present;
      rewrite page_backing_in by
        (unfold remote_head, drain_head, mailbox, local_head, page_size; lia);
      discriminate |]).
  apply interp_nd_init_links; intros offset O.
  repeat apply upd_preserves_present.
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
  pose proof (sinterp_alloc_first h (page_size capacity) base c
    (fun a : nat => (Ret a : ictree sE nat))
    (page_size_positive capacity) Positive Free First) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  unfold new_page; rewrite interp_rr_bind, interp_rr_alloc.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  eapply equ_clos_sbisim_goal; [apply bind_ret_l | reflexivity |].
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
  pose proof (sinterp_alloc_first h (page_size capacity) base c
    (fun a : nat => (Ret a : ictree sE nat))
    (page_size_positive capacity) Positive Free First) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  unfold new_page; rewrite interp_nd_source_bind, interp_nd_source_alloc.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  eapply equ_clos_sbisim_goal; [apply bind_ret_l | reflexivity |].
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
  runStateT (sh (SAlloc (page_size capacity))) (hemp,c) ~
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
Local Lemma allocator_interp_rr_read_value n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h c :
  h a = Some value ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some value)) (Some i) m (h,c).
Proof.
  intro Lookup.
  pose proof (sinterp_rd a h c value
    (fun x : nat => (Ret x : ictree sE nat)) Lookup) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_rr_read.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.

Local Lemma allocator_interp_nd_read_value n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h c :
  h a = Some value ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) (h,c) ~
  interp_nd (S n) (ts @ i := K (Some value)) (Some i) (h,c).
Proof.
  intro Lookup.
  pose proof (sinterp_rd a h c value
    (fun x : nat => (Ret x : ictree sE nat)) Lookup) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_nd_source_read.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.

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
  apply allocator_interp_rr_read_value; exact Lookup.
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
  apply allocator_interp_nd_read_value; exact Lookup.
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
  intro Missing; rewrite interp_rr_bind, interp_rr_new_page_hemp, interp_rr_read.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [eapply equ_clos_sbisim_goal;
        [exact (sinterp_srd_stuck (address 1) (page_heap 1 capacity hemp) c Missing)
        |reflexivity|reflexivity]
      |intro result; reflexivity]
    |eapply equ_clos_sbisim_goal; [apply bind_stuck_equ|reflexivity|reflexivity]]
  end.
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
  intro Missing.
  rewrite interp_nd_source_bind, interp_nd_new_page_hemp, interp_nd_source_read.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [eapply equ_clos_sbisim_goal;
        [exact (sinterp_srd_stuck (address 1) (page_heap 1 capacity hemp) c Missing)
        |reflexivity|reflexivity]
      |intro result; reflexivity]
    |eapply equ_clos_sbisim_goal; [apply bind_stuck_equ|reflexivity|reflexivity]]
  end.
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

Lemma emit_list_nil {X} (t : ictreeW SObs X) : emit_list [] t = t.
Proof. reflexivity. Qed.

Lemma emit_list_cons {X} o xs (t : ictreeW SObs X) :
  emit_list (o :: xs) t ≅ Vis (Log o) (fun _ => emit_list xs t).
Proof.
  change ((log o ;; emit_list xs t) ≅ Vis (Log o) (fun _ => emit_list xs t)).
  unfold log, ICtree.trigger; rewrite bind_vis.
  step; constructor; intros []; rewrite bind_ret_l; reflexivity.
Qed.

Lemma emit_list_app {X} xs ys (t : ictreeW SObs X) :
  emit_list (xs ++ ys) t = emit_list xs (emit_list ys t).
Proof. unfold emit_list; rewrite List.fold_right_app; reflexivity. Qed.

Lemma emit_list_equ {X} xs (t u : ictreeW SObs X) :
  t ≅ u -> emit_list xs t ≅ emit_list xs u.
Proof.
  intro E; induction xs as [|o xs IH]; [exact E|].
  rewrite !emit_list_cons; step; constructor; intro x; exact IH.
Qed.

Lemma emit_list_sbisim {X} xs (t u : ictreeW SObs X) :
  t ~ u -> emit_list xs t ~ emit_list xs u.
Proof.
  intro E; induction xs as [|o xs IH]; [exact E|].
  rewrite !emit_list_cons; apply sb_vis; intro x; exact IH.
Qed.

Lemma emit_list_bind {X Y} xs (t : ictreeW SObs X)
  (k : X -> ictreeW SObs Y) :
  emit_list xs t >>= k ≅ emit_list xs (t >>= k).
Proof.
  induction xs as [|o xs IH]; [reflexivity|].
  change (((log o ;; emit_list xs t) >>= k) ≅
    (log o ;; emit_list xs (t >>= k))).
  etransitivity; [apply bind_bind|].
  apply equ_clo_bind_eq; intros []; exact IH.
Qed.

Lemma emit_list_ret_bind {X Y} xs (x : X) (k : X -> ictreeW SObs Y) :
  emit_list xs (Ret x) >>= k ≅ emit_list xs (k x).
Proof.
  etransitivity; [apply emit_list_bind|].
  apply emit_list_equ, bind_ret_l.
Qed.

(** Return values are observable labels, including when they contain heaps.
    This proves equality of actual responses; it never identifies merely
    pointwise-equal heap functions. *)
Lemma emit_list_ret_injective {X} xs ys (x y : X) :
  emit_list xs (Ret x) ~ emit_list ys (Ret y) -> xs = ys /\ x = y.
Proof.
  revert ys; induction xs as [|o xs IH]; intros [|p ys] E.
  - split; [reflexivity|]. exact (@sbisim_ret_inv (writerE SObs) _ X x y E).
  - rewrite emit_list_cons in E.
    exfalso; exact (@sbisim_ret_vis_inv (writerE SObs) _ X x (Log p)
      (fun _ => emit_list ys (Ret y)) E).
  - rewrite emit_list_cons in E.
    exfalso; eapply (@sbisim_ret_vis_inv (writerE SObs) _ X y (Log o)
      (fun _ => emit_list xs (Ret x))); symmetry; exact E.
  - rewrite !emit_list_cons in E.
    pose proof (@sbisim_vis_invT (writerE SObs) _ X
      (Log o) (Log p) (fun _ => emit_list xs (Ret x))
      (fun _ => emit_list ys (Ret y)) tt E) as [_ Eo].
    injection Eo as Eo; subst p.
    pose proof (@sbisim_vis_invE (writerE SObs) _ X (Log o)
      (fun _ => emit_list xs (Ret x)) (fun _ => emit_list ys (Ret y))
      tt E tt) as Etail.
    destruct (IH ys Etail) as [-> ->]; auto.
Qed.

Lemma handler_response_unique (e : sE) (sigma : SSig)
  (result : encode e) (sigma1 : SSig) (before : list SObs)
  (result' : encode e) (sigma2 : SSig) (before' : list SObs) :
  runStateT (sh e) sigma ~ emit_list before (Ret (result,sigma1)) ->
  runStateT (sh e) sigma ~ emit_list before' (Ret (result',sigma2)) ->
  before = before' /\ result = result' /\ sigma1 = sigma2.
Proof.
  intros E1 E2.
  assert (E : emit_list before (Ret (result,sigma1)) ~
              emit_list before' (Ret (result',sigma2))).
  { transitivity (runStateT (sh e) sigma); [symmetry; exact E1|exact E2]. }
  destruct (emit_list_ret_injective _ _ _ _ E) as [Ex Er].
  inversion Er; subst; auto.
Qed.

Lemma sbisim_stuck_is_stuck {E} {HE : Encode E} {X} (t : ictree E X) :
  t ~ (stuck : ictree E X) -> is_stuck t.
Proof.
  intros Ets [l [u Hstep]].
  destruct (sbisim_trans t stuck u l eq Ets Hstep)
    as [l' [u' [Hbad _]]].
  eapply trans_stuck; exact Hbad.
Qed.

Lemma emit_list_ret_not_stuck {X} xs (x : X) :
  ~ (emit_list xs (Ret x) ~ (stuck : ictreeW SObs X)).
Proof.
  intro E; apply sbisim_stuck_is_stuck in E.
  destruct xs as [|o xs].
  - apply E; exists (val x), stuck; apply trans_ret.
  - apply E; exists (obs (Log o) tt), (emit_list xs (Ret x)).
    rewrite emit_list_cons.
    exact (@trans_vis (writerE SObs) _ X (Log o) tt (fun _ => emit_list xs (Ret x))).
Qed.

(** Raw congruence is allowed on both ends, but no source-side [sbisim]
    congruence is used. *)
Lemma ThreadSegment_equ_input t u sigma xs residual sigma' :
  t ≅ u -> ThreadSegment t sigma xs residual sigma' ->
  ThreadSegment u sigma xs residual sigma'.
Proof.
  intros E H; eapply segment_equ; [symmetry; exact E|exact H|reflexivity].
Qed.

Lemma ThreadSegment_equ_output t sigma xs residual residual' sigma' :
  ThreadSegment t sigma xs residual sigma' -> residual ≅ residual' ->
  ThreadSegment t sigma xs residual' sigma'.
Proof. intros H E; eapply segment_equ; [reflexivity|exact H|exact E]. Qed.

Lemma ThreadSegment_yield_inv_equ t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  forall k : unit -> thread sE,
    t ≅ Vis (inl Yield) k ->
    xs = [] /\ sigma' = sigma /\ k tt ≅ residual.
Proof.
  intro H; induction H as
    [k0 sigma
    |t sigma xs residual sigma' H IH
    |e k0 sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout].
  - intros k E; split; [reflexivity|]; split; [reflexivity|].
    symmetry; exact (equ_vis_invE E tt).
  - intros k E; step in E; cbn in E; inversion E.
  - intros k E; pose proof (equ_vis_invT E) as [_ Ebad]; discriminate.
  - intros k E.
    assert (Eu : u ≅ Vis (inl Yield) k).
    { transitivity t; [symmetry; exact Etu|exact E]. }
    destruct (IH k Eu) as [Ex [Es Ek]].
    split; [exact Ex|]; split; [exact Es|].
    transitivity u'; assumption.
Qed.

Lemma ThreadSegment_yield_inv k sigma xs residual sigma' :
  ThreadSegment (Vis (inl Yield) k) sigma xs residual sigma' ->
  xs = [] /\ sigma' = sigma /\ k tt ≅ residual.
Proof. intro H; eapply ThreadSegment_yield_inv_equ; [exact H|reflexivity]. Qed.

Lemma ThreadSegment_guard_inv_equ t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  forall u, t ≅ Guard u -> ThreadSegment u sigma xs residual sigma'.
Proof.
  intro H; induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t v sigma xs v' residual sigma' Etv H IH Eout].
  - intros u E; step in E; cbn in E; inversion E.
  - intros u E; apply equ_guard_invE in E.
    eapply ThreadSegment_equ_input; [exact E|exact H].
  - intros u E; step in E; cbn in E; inversion E.
  - intros u E.
    eapply ThreadSegment_equ_output; [|exact Eout].
    apply IH; transitivity t; [symmetry; exact Etv|exact E].
Qed.

Lemma ThreadSegment_guard_inv t sigma xs residual sigma' :
  ThreadSegment (Guard t) sigma xs residual sigma' ->
  ThreadSegment t sigma xs residual sigma'.
Proof. intro H; eapply ThreadSegment_guard_inv_equ; [exact H|reflexivity]. Qed.

Lemma ThreadSegment_guard_iff t sigma xs residual sigma' :
  ThreadSegment (Guard t) sigma xs residual sigma' <->
  ThreadSegment t sigma xs residual sigma'.
Proof. split; [apply ThreadSegment_guard_inv|apply segment_guard]. Qed.

Lemma ThreadSegment_user_inv_equ t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  forall (e : sE) (k : encode e -> thread sE),
    t ≅ (@go CEff _ unit (VisF (inr (inr e) : CEff) k)) ->
    exists result sigma1 before after,
      xs = before ++ after /\
      runStateT (sh e) sigma ~ emit_list before (Ret (result,sigma1)) /\
      ThreadSegment (k result) sigma1 after residual sigma'.
Proof.
  intro H; induction H as
    [k0 sigma
    |t sigma xs residual sigma' H IH
    |e0 k0 sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout].
  - intros e k E; pose proof (equ_vis_invT E) as [_ Ebad]; discriminate.
  - intros e k E; step in E; cbn in E; inversion E.
  - intros e k E.
    pose proof (equ_vis_invT E) as [_ Ee].
    assert (Eevent : e0 = e) by congruence; subst e.
    exists result, sigma1, before, after.
    split; [reflexivity|]; split; [exact Eh|].
    eapply ThreadSegment_equ_input; [exact (equ_vis_invE E result)|exact H].
  - intros e k E.
    assert (Eu : u ≅ (@go CEff _ unit (VisF (inr (inr e) : CEff) k))).
    { transitivity t; [symmetry; exact Etu|exact E]. }
    destruct (IH e k Eu) as [r [sigma1 [before [after [Ex [Eh Htail]]]]]].
    exists r, sigma1, before, after; split; [exact Ex|]; split; [exact Eh|].
    eapply ThreadSegment_equ_output; eassumption.
Qed.

Lemma ThreadSegment_user_inv (e : sE) (k : encode e -> thread sE)
  sigma xs residual sigma' :
  ThreadSegment ((@go CEff _ unit (VisF (inr (inr e) : CEff) k))) sigma xs residual sigma' ->
  exists result sigma1 before after,
    xs = before ++ after /\
    runStateT (sh e) sigma ~ emit_list before (Ret (result,sigma1)) /\
    ThreadSegment (k result) sigma1 after residual sigma'.
Proof. intro H; eapply ThreadSegment_user_inv_equ; [exact H|reflexivity]. Qed.

Lemma ThreadSegment_ret_absurd_equ t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' -> ~ (t ≅ Ret tt).
Proof.
  intro H; induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intro E.
  - step in E; cbn in E; inversion E.
  - step in E; cbn in E; inversion E.
  - step in E; cbn in E; inversion E.
  - apply IH; transitivity t; [symmetry; exact Etu|exact E].
Qed.

Lemma ThreadSegment_ret_absurd sigma xs residual sigma' :
  ~ ThreadSegment (Ret tt) sigma xs residual sigma'.
Proof. intro H; eapply ThreadSegment_ret_absurd_equ; [exact H|reflexivity]. Qed.

Lemma ThreadSegment_fork_absurd_equ t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  forall k : bool -> thread sE, ~ (t ≅ Vis (inr (inl Fork)) k).
Proof.
  intro H; induction H as
    [k0 sigma
    |t sigma xs residual sigma' H IH
    |e k0 sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intros k E.
  - pose proof (equ_vis_invT E) as [_ Ebad]; discriminate.
  - step in E; cbn in E; inversion E.
  - pose proof (equ_vis_invT E) as [_ Ebad]; discriminate.
  - apply (IH k); transitivity t; [symmetry; exact Etu|exact E].
Qed.

Lemma ThreadSegment_fork_absurd k sigma xs residual sigma' :
  ~ ThreadSegment (Vis (inr (inl Fork)) k) sigma xs residual sigma'.
Proof. intro H; eapply ThreadSegment_fork_absurd_equ; [exact H|reflexivity]. Qed.

Lemma ThreadSegment_br_absurd_equ t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  forall n (k : Fin.t (S n) -> thread sE), ~ (t ≅ Br n k).
Proof.
  intro H; induction H as
    [k0 sigma
    |t sigma xs residual sigma' H IH
    |e k0 sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intros n k E.
  - step in E; cbn in E; inversion E.
  - step in E; cbn in E; inversion E.
  - step in E; cbn in E; inversion E.
  - apply (IH n k); transitivity t; [symmetry; exact Etu|exact E].
Qed.

Lemma ThreadSegment_br_absurd n k sigma xs residual sigma' :
  ~ ThreadSegment (Br n k) sigma xs residual sigma'.
Proof. intro H; eapply ThreadSegment_br_absurd_equ; [exact H|reflexivity]. Qed.

(** A finite first-yield derivation cannot be manufactured by repeatedly
    unfolding a divergent guard.  A user case provides its actual response as
    the witness needed for the first visible raw transition. *)
Lemma ThreadSegment_can_step t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' -> exists l u, trans l t u.
Proof.
  intro H; induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout].
  - exists (obs (inl Yield) tt), (k tt); apply trans_vis.
  - destruct IH as [l [u Hstep]]; exists l, u; now apply trans_guard.
  - exists (obs (inr (inr e) : CEff) result), (k result); apply trans_vis.
  - destruct IH as [l [v Hstep]]; exists l, v; rewrite Etu; exact Hstep.
Qed.

Lemma ThreadSegment_divergent_absurd t sigma xs residual sigma' :
  is_stuck t -> ~ ThreadSegment t sigma xs residual sigma'.
Proof. intros Hdiv Hseg; apply Hdiv; eapply ThreadSegment_can_step; exact Hseg. Qed.

Lemma ThreadSegment_stuck_absurd sigma xs residual sigma' :
  ~ ThreadSegment (stuck : thread sE) sigma xs residual sigma'.
Proof. apply ThreadSegment_divergent_absurd, stuck_is_stuck. Qed.

Lemma ThreadSegment_spin_absurd sigma xs residual sigma' :
  ~ ThreadSegment (spin : thread sE) sigma xs residual sigma'.
Proof.
  intro H; eapply ThreadSegment_br_absurd_equ; [exact H|].
  apply unfold_spin.
Qed.

Lemma ThreadSegment_fault_absurd (e : sE) (k : encode e -> thread sE)
  sigma xs residual sigma' :
  runStateT (sh e) sigma ~ (stuck : ictreeW SObs (encode e * SSig)) ->
  ~ ThreadSegment ((@go CEff _ unit (VisF (inr (inr e) : CEff) k))) sigma xs residual sigma'.
Proof.
  intros Ef Hseg.
  destruct (ThreadSegment_user_inv e k sigma xs residual sigma' Hseg)
    as [result [sigma1 [before [after [_ [Eh _]]]]]].
  apply (emit_list_ret_not_stuck before (result,sigma1)).
  transitivity (runStateT (sh e) sigma); [symmetry; exact Eh|exact Ef].
Qed.

Lemma ThreadSegment_deterministic t sigma xs u sigma1 ys v sigma2 :
  ThreadSegment t sigma xs u sigma1 ->
  ThreadSegment t sigma ys v sigma2 ->
  xs = ys /\ sigma1 = sigma2 /\ u ≅ v.
Proof.
  intros H1; revert ys v sigma2.
  induction H1 as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intros ys v sigma2 H2.
  - destruct (ThreadSegment_yield_inv k sigma ys v sigma2 H2)
      as [Ex [Es Ek]].
    split; [symmetry; exact Ex|]; split; [symmetry; exact Es|exact Ek].
  - apply IH; now apply ThreadSegment_guard_inv in H2.
  - destruct (ThreadSegment_user_inv e k sigma ys v sigma2 H2)
      as [r [sigma0 [before0 [after0 [Ey [Eh0 Htail]]]]]].
    destruct (handler_response_unique e sigma result sigma1 before
      r sigma0 before0 Eh Eh0) as [Eb [Er Es]].
    subst before0; subst r; subst sigma0.
    destruct (IH after0 v sigma2 Htail) as [Ea [Es Er]].
    split; [subst ys; now rewrite Ea|]; split; assumption.
  - assert (H2u : ThreadSegment u sigma ys v sigma2).
    { eapply ThreadSegment_equ_input; [exact Etu|exact H2]. }
    destruct (IH ys v sigma2 H2u) as [Ex [Es Er]].
    split; [exact Ex|]; split; [exact Es|].
    transitivity u'; [symmetry; exact Eout|exact Er].
Qed.

#[global] Instance guard_equ_Equivalence : Equivalence guard_equ.
Proof.
  split.
  - intro t; apply guard_equ_equ; reflexivity.
  - intros t u; apply guard_equ_sym.
  - intros t u v; apply guard_equ_trans.
Qed.

Lemma guard_equ_sbisim t u : guard_equ t u -> t ~ u.
Proof.
  intro H; induction H as [t u E|t u H IH|t u H IH|t u H IH|t u v H1 IH1 H2 IH2].
  - rewrite E; reflexivity.
  - rewrite sb_guard; exact IH.
  - rewrite sb_guard; exact IH.
  - symmetry; exact IH.
  - transitivity u; assumption.
Qed.

(** This stronger same-residual transport follows from the output-equ rule.
    Symmetry in the finite guard closure is handled by proving both directions
    together, rather than assuming a reverse simulation. *)
Lemma guard_equ_segment_iff t u : guard_equ t u ->
  forall sigma xs residual sigma',
    ThreadSegment t sigma xs residual sigma' <->
    ThreadSegment u sigma xs residual sigma'.
Proof.
  intro H; induction H as [t u E|t u H IH|t u H IH|t u H IH|t u v H1 IH1 H2 IH2];
    intros sigma xs residual sigma'.
  - split; intro Hseg.
    + eapply ThreadSegment_equ_input; [exact E|exact Hseg].
    + eapply ThreadSegment_equ_input; [symmetry; exact E|exact Hseg].
  - rewrite ThreadSegment_guard_iff; apply IH.
  - rewrite ThreadSegment_guard_iff; apply IH.
  - symmetry; apply IH.
  - transitivity (ThreadSegment u sigma xs residual sigma'); [apply IH1|apply IH2].
Qed.

Lemma guard_equ_segment t u sigma xs t' sigma' :
  guard_equ t u -> ThreadSegment t sigma xs t' sigma' ->
  exists u', ThreadSegment u sigma xs u' sigma' /\ guard_equ t' u'.
Proof.
  intros E Hseg; exists t'; split.
  - apply (proj1 (guard_equ_segment_iff t u E sigma xs t' sigma')); exact Hseg.
  - apply guard_equ_equ; reflexivity.
Qed.

Lemma guard_equ_br_yield_absurd n (k : Fin.t (S n) -> thread sE)
  (ky : unit -> thread sE) : ~ guard_equ (Br n k) (Vis (inl Yield) ky).
Proof.
  intro E; apply guard_equ_sbisim in E.
  eapply (@sbisim_vis_br_inv CEff _ unit n (inl Yield) ky k); symmetry; exact E.
Qed.

(** Equivalence of pools is used only for genuine raw [equ].  Guard removal
    below is deliberately restricted to the focused slot. *)
Lemma segment_nd_replace_equ n (ts : pool sE (S n)) (i : Fin.t (S n))
  t u focus sigma :
  t ≅ u ->
  interp_nd (S n) (ts @ i := t) focus sigma ~
  interp_nd (S n) (ts @ i := u) focus sigma.
Proof.
  intro E.
  pose proof (interp_nd_equ (S n) (ts @ i := t) (ts @ i := u)
    focus sigma (replace_pool_equ ts ts i t u (pool_equ_refl ts) E)) as Ep.
  rewrite Ep; reflexivity.
Qed.

Lemma segment_rr_replace_equ n (ts : pool sE (S n)) (i : Fin.t (S n))
  t u focus m sigma :
  t ≅ u ->
  interp_schedule_rr sh (S n) (ts @ i := t) focus m sigma ~
  interp_schedule_rr sh (S n) (ts @ i := u) focus m sigma.
Proof.
  intro E.
  pose proof (interp_schedule_rr_equ sh (S n) (ts @ i := t) (ts @ i := u)
    focus m sigma (replace_pool_equ ts ts i t u (pool_equ_refl ts) E)) as Ep.
  rewrite Ep; reflexivity.
Qed.

Lemma segment_nd_focused_guard n (ts : pool sE (S n)) (i : Fin.t (S n)) t sigma :
  interp_nd (S n) (ts @ i := Guard t) (Some i) sigma ~
  interp_nd (S n) (ts @ i := t) (Some i) sigma.
Proof.
  erewrite interp_nd_guard by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma segment_rr_focused_guard n (ts : pool sE (S n)) (i : Fin.t (S n)) t m sigma :
  interp_schedule_rr sh (S n) (ts @ i := Guard t) (Some i) m sigma ~
  interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma.
Proof.
  erewrite interp_schedule_rr_guard by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma guard_equ_focused_nd n (ts : pool sE (S n)) (i : Fin.t (S n)) t u sigma :
  guard_equ t u ->
  interp_nd (S n) (ts @ i := t) (Some i) sigma ~
  interp_nd (S n) (ts @ i := u) (Some i) sigma.
Proof.
  intro H; induction H as [t u E|t u H IH|t u H IH|t u H IH|t u v H1 IH1 H2 IH2].
  - apply segment_nd_replace_equ; exact E.
  - etransitivity; [apply segment_nd_focused_guard|exact IH].
  - etransitivity; [exact IH|symmetry; apply segment_nd_focused_guard].
  - symmetry; exact IH.
  - etransitivity; [exact IH1|exact IH2].
Qed.

Lemma guard_equ_focused_rr n (ts : pool sE (S n)) (i : Fin.t (S n)) t u m sigma :
  guard_equ t u ->
  interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma ~
  interp_schedule_rr sh (S n) (ts @ i := u) (Some i) m sigma.
Proof.
  intro H; induction H as [t u E|t u H IH|t u H IH|t u H IH|t u v H1 IH1 H2 IH2].
  - apply segment_rr_replace_equ; exact E.
  - etransitivity; [apply segment_rr_focused_guard|exact IH].
  - etransitivity; [exact IH|symmetry; apply segment_rr_focused_guard].
  - symmetry; exact IH.
  - etransitivity; [exact IH1|exact IH2].
Qed.

Lemma segment_nd_focused_user n (ts : pool sE (S n)) (i : Fin.t (S n))
  (e : sE) (k : encode e -> thread sE) sigma :
  interp_nd (S n) (ts @ i := (@go CEff _ unit (VisF (inr (inr e) : CEff) k))) (Some i) sigma ~
  (runStateT (sh e) sigma >>= fun '(x,sigma') =>
    interp_nd (S n) (ts @ i := k x) (Some i) sigma').
Proof.
  erewrite interp_nd_user by (rewrite Vector.nth_replace_eq; reflexivity).
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [x sigma']; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma segment_rr_focused_user n (ts : pool sE (S n)) (i : Fin.t (S n))
  (e : sE) (k : encode e -> thread sE) m sigma :
  interp_schedule_rr sh (S n) (ts @ i := (@go CEff _ unit (VisF (inr (inr e) : CEff) k))) (Some i) m sigma ~
  (runStateT (sh e) sigma >>= fun '(x,sigma') =>
    interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma').
Proof.
  erewrite interp_schedule_rr_user by (rewrite Vector.nth_replace_eq; reflexivity).
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [x sigma']; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma segment_interp_nd n (ts : pool sE (S n)) (i : Fin.t (S n))
  t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  interp_nd (S n) (ts @ i := t) (Some i) sigma ~
  emit_list xs (interp_nd (S n) (ts @ i := residual) None sigma').
Proof.
  intro H; revert n ts i.
  induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intros n ts i.
  - cbn [emit_list].
    erewrite interp_nd_yield by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq; reflexivity.
  - etransitivity; [apply segment_nd_focused_guard|apply IH].
  - etransitivity; [apply segment_nd_focused_user|].
    transitivity (emit_list before (Ret (result,sigma1)) >>=
      fun '(x,sigma0) => interp_nd (S n) (ts @ i := k x) (Some i) sigma0).
    + apply sbisim_clo_bind_eq; [exact Eh|intro r; reflexivity].
    + rewrite emit_list_ret_bind, emit_list_app.
      apply emit_list_sbisim; apply IH.
  - etransitivity; [apply segment_nd_replace_equ; exact Etu|].
    etransitivity; [apply IH|].
    apply emit_list_sbisim, segment_nd_replace_equ; exact Eout.
Qed.

Lemma segment_interp_rr n (ts : pool sE (S n)) (i : Fin.t (S n))
  t m sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma ~
  emit_list xs (interp_schedule_rr sh (S n) (ts @ i := residual) None m sigma').
Proof.
  intro H; revert n ts i m.
  induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intros n ts i m.
  - cbn [emit_list].
    erewrite interp_schedule_rr_yield by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq; reflexivity.
  - etransitivity; [apply segment_rr_focused_guard|apply IH].
  - etransitivity; [apply segment_rr_focused_user|].
    transitivity (emit_list before (Ret (result,sigma1)) >>=
      fun '(x,sigma0) => interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma0).
    + apply sbisim_clo_bind_eq; [exact Eh|intro r; reflexivity].
    + rewrite emit_list_ret_bind, emit_list_app.
      apply emit_list_sbisim; apply IH.
  - etransitivity; [apply segment_rr_replace_equ; exact Etu|].
    etransitivity; [apply IH|].
    apply emit_list_sbisim, segment_rr_replace_equ; exact Eout.
Qed.

(** Exact equations retain the finite administrative guard path.  In particular
    RR selection is not a visible branch after refinement: its three guards
    must not be used as a guarded [sbisim] coinduction hypothesis.  These laws
    expose them for induction on an actual [trans_] derivation instead. *)
Lemma segment_rr_guard_exact n (ts : pool sE (S n)) (i : Fin.t (S n))
  t m sigma :
  observe (ts $ i) = GuardF t ->
  interp_schedule_rr sh (S n) ts (Some i) m sigma ≅
  Guard (interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma).
Proof.
  intro Hobs; unfold interp_schedule_rr at 1.
  rewrite unfold_run_round_robin, (schedule_focused_guard n ts i t Hobs).
  rewrite interp_erase_guard, interp_state_tau; reflexivity.
Qed.

Lemma segment_rr_yield_exact n (ts : pool sE (S n)) (i : Fin.t (S n))
  k m sigma :
  observe (ts $ i) = VisF (inl Yield) k ->
  interp_schedule_rr sh (S n) ts (Some i) m sigma ≅
  Guard (interp_schedule_rr sh (S n) (ts @ i := k tt) None m sigma).
Proof.
  intro Hobs; unfold interp_schedule_rr at 1.
  rewrite unfold_run_round_robin, (schedule_focused_yield n ts i k Hobs).
  rewrite interp_erase_guard, interp_state_tau; reflexivity.
Qed.

Lemma segment_rr_user_exact n (ts : pool sE (S n)) (i : Fin.t (S n))
  (e : sE) (k : encode e -> thread sE) m sigma :
  observe (ts $ i) = VisF (inr (inr e)) k ->
  interp_schedule_rr sh (S n) ts (Some i) m sigma ≅
  (runStateT (sh e) sigma >>= fun '(x,sigma') =>
    Guard (Guard (Guard
      (interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma')))).
Proof.
  intro Hobs; unfold interp_schedule_rr at 1.
  rewrite unfold_run_round_robin, (schedule_focused_user_event n ts i e k Hobs).
  rewrite interp_erase_user, interp_state_vis.
  apply equ_clo_bind with (S := eq); [reflexivity|].
  intros [x sigma'] r <-; apply guard_equ_node.
  etransitivity; [apply interp_state_tau|].
  apply guard_equ_node, interp_state_tau.
Qed.

Lemma segment_rr_select_exact n (ts : pool sE (S n)) m sigma :
  interp_schedule_rr sh (S n) ts None m sigma ≅
  Guard (Guard (Guard
    (interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) sigma))).
Proof.
  unfold interp_schedule_rr at 1.
  rewrite unfold_run_round_robin, schedule_no_focus_nonempty.
  rewrite interp_erase_yield.
  etransitivity; [apply interp_state_tau|].
  apply guard_equ_node.
  etransitivity; [apply interp_state_tau|].
  apply guard_equ_node.
  rewrite (unfold_run_round_robin
    (Br n (fun i => schedule (S n) ts (Some i))) m).
  change (interp_state sh
    (interp_yield (interp_spawn
      (Guard (run_round_robin (schedule (S n) ts (Some (rr_pick n m))) (S m))))) sigma ≅
    Guard (interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) sigma)).
  rewrite interp_erase_guard, interp_state_tau; reflexivity.
Qed.

(** A stronger certificate for the initialized workers: primitive handlers
    return by raw equivalence.  This retains finite administrative guards for
    round-robin divergence matching; source validity still uses ThreadSegment. *)
Inductive ExactThreadSegment : thread sE -> SSig -> list SObs -> thread sE -> SSig -> Prop :=
| exact_segment_yield (k : unit -> thread sE) sigma :
    ExactThreadSegment (Vis (inl Yield) k) sigma [] (k tt) sigma
| exact_segment_guard t sigma logs t' sigma' :
    ExactThreadSegment t sigma logs t' sigma' ->
    ExactThreadSegment (Guard t) sigma logs t' sigma'
| exact_segment_user (e : sE) (k : encode e -> thread sE) sigma result sigma1
    before after t' sigma' :
    runStateT (sh e) sigma ≅ emit_list before (Ret (result,sigma1)) ->
    ExactThreadSegment (k result) sigma1 after t' sigma' ->
    ExactThreadSegment (@go CEff _ unit (VisF (inr (inr e) : CEff) k))
      sigma (before ++ after) t' sigma'
| exact_segment_equ t u sigma logs u' t' sigma' :
    t ≅ u -> ExactThreadSegment u sigma logs u' sigma' -> u' ≅ t' ->
    ExactThreadSegment t sigma logs t' sigma'.

Lemma ExactThreadSegment_segment t sigma xs residual sigma' :
  ExactThreadSegment t sigma xs residual sigma' ->
  ThreadSegment t sigma xs residual sigma'.
Proof.
  intro H; induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout].
  - apply segment_yield.
  - apply segment_guard; exact IH.
  - eapply segment_user; [|exact IH].
    eapply equ_clos_sbisim_goal; [exact Eh|reflexivity|reflexivity].
  - eapply segment_equ; eassumption.
Qed.

Lemma ExactThreadSegment_equ_input t u sigma xs residual sigma' :
  t ≅ u -> ExactThreadSegment t sigma xs residual sigma' ->
  ExactThreadSegment u sigma xs residual sigma'.
Proof.
  intros E H; eapply exact_segment_equ; [symmetry; exact E|exact H|reflexivity].
Qed.

Lemma ExactThreadSegment_equ_output t sigma xs residual residual' sigma' :
  ExactThreadSegment t sigma xs residual sigma' -> residual ≅ residual' ->
  ExactThreadSegment t sigma xs residual' sigma'.
Proof. intros H E; eapply exact_segment_equ; [reflexivity|exact H|exact E]. Qed.

Lemma ExactThreadSegment_guard_inv_equ t sigma xs residual sigma' :
  ExactThreadSegment t sigma xs residual sigma' ->
  forall u, t ≅ Guard u -> ExactThreadSegment u sigma xs residual sigma'.
Proof.
  intro H; induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t v sigma xs v' residual sigma' Etv H IH Eout].
  - intros u E; step in E; cbn in E; inversion E.
  - intros u E; apply equ_guard_invE in E.
    eapply ExactThreadSegment_equ_input; [exact E|exact H].
  - intros u E; step in E; cbn in E; inversion E.
  - intros u E.
    eapply ExactThreadSegment_equ_output; [|exact Eout].
    apply IH; transitivity t; [symmetry; exact Etv|exact E].
Qed.

Lemma ExactThreadSegment_guard_inv t sigma xs residual sigma' :
  ExactThreadSegment (Guard t) sigma xs residual sigma' ->
  ExactThreadSegment t sigma xs residual sigma'.
Proof. intro H; eapply ExactThreadSegment_guard_inv_equ; [exact H|reflexivity]. Qed.

Lemma ExactThreadSegment_guard_iff t sigma xs residual sigma' :
  ExactThreadSegment (Guard t) sigma xs residual sigma' <->
  ExactThreadSegment t sigma xs residual sigma'.
Proof. split; [apply ExactThreadSegment_guard_inv|apply exact_segment_guard]. Qed.

Lemma guard_equ_exact_segment_iff t u : guard_equ t u ->
  forall sigma xs residual sigma',
    ExactThreadSegment t sigma xs residual sigma' <->
    ExactThreadSegment u sigma xs residual sigma'.
Proof.
  intro H; induction H as [t u E|t u H IH|t u H IH|t u H IH|t u v H1 IH1 H2 IH2];
    intros sigma xs residual sigma'.
  - split; intro Hseg.
    + eapply ExactThreadSegment_equ_input; [exact E|exact Hseg].
    + eapply ExactThreadSegment_equ_input; [symmetry; exact E|exact Hseg].
  - rewrite ExactThreadSegment_guard_iff; apply IH.
  - rewrite ExactThreadSegment_guard_iff; apply IH.
  - symmetry; apply IH.
  - transitivity (ExactThreadSegment u sigma xs residual sigma'); [apply IH1|apply IH2].
Qed.

(** Raw source equations retain the outer option; in particular a successful
    remote publication must return through its caller before reaching Yield. *)
Lemma source_raw_bind {A B} (p : CProg A) (next : A -> CProg B)
  (K : option B -> thread sE) :
  (denote_flow (CBind p next) >>= K) ≅
  (denote_flow p >>= fun flow =>
    match flow with None => K None | Some x => denote_flow (next x) >>= K end).
Proof.
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intros [x|]; [reflexivity|apply bind_ret_l].
Qed.

Lemma source_raw_ret {A} (x : A) (K : option A -> thread sE) :
  (denote_flow (CRet x) >>= K) ≅ K (Some x).
Proof. cbn [denote_flow]; apply bind_ret_l. Qed.

Lemma source_raw_until {A} (body : CProg (option A))
  (K : option unit -> thread sE) :
  (denote_flow (CUntilNone body) >>= K) ≅
  (denote_flow body >>= until_tail body K).
Proof.
  set (loop_body := fun _ : unit =>
    flow <- denote_flow body;;
    match flow with
    | None => Ret (inr (None : option unit))
    | Some None => Ret (inr (Some tt))
    | Some (Some _) => Ret (inl tt)
    end).
  change ((ICtree.iter loop_body tt >>= K) ≅
    (denote_flow body >>= fun flow =>
      match flow with
      | None => K None
      | Some None => K (Some tt)
      | Some (Some _) => Guard (ICtree.iter loop_body tt >>= K)
      end)).
  transitivity ((loop_body tt >>= fun lr =>
    match lr with
    | inl j => Guard (ICtree.iter loop_body j)
    | inr result => Ret result
    end) >>= K).
  - apply equ_clo_bind with (S := eq).
    + apply unfold_iter.
    + intros r r' <-; reflexivity.
  - etransitivity; [apply bind_bind|].
    unfold loop_body at 1.
    etransitivity; [apply bind_bind|].
    apply equ_clo_bind_eq; intros [[x|]|]; cbn.
    + etransitivity; [apply bind_ret_l|]. apply bind_guard.
    + etransitivity; [apply bind_ret_l|]. apply bind_ret_l.
    + etransitivity; [apply bind_ret_l|]. apply bind_ret_l.
Qed.

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

Local Definition source_segment_to (t : thread sE) (sigma : SSig)
  (logs : list SObs) (target : thread sE) (sigma' : SSig) : Prop :=
  exists residual, ExactThreadSegment t sigma logs residual sigma' /\
    guard_equ residual target.

Local Lemma source_to_equ t u sigma logs target sigma' :
  t ≅ u -> source_segment_to u sigma logs target sigma' ->
  source_segment_to t sigma logs target sigma'.
Proof.
  intros Htu (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply exact_segment_equ; [exact Htu|exact Hseg|reflexivity].
Qed.

Local Lemma source_to_bind {A B} (p : CProg A) (next : A -> CProg B)
  (K : option B -> thread sE) sigma logs target sigma' :
  source_segment_to (denote_flow p >>= fun flow =>
    match flow with None => K None | Some x => denote_flow (next x) >>= K end)
    sigma logs target sigma' ->
  source_segment_to (denote_flow (CBind p next) >>= K) sigma logs target sigma'.
Proof.
  intro H; eapply source_to_equ; [apply source_raw_bind|exact H].
Qed.

Local Lemma source_to_ret {A} (x : A) (K : option A -> thread sE)
  sigma logs target sigma' :
  source_segment_to (K (Some x)) sigma logs target sigma' ->
  source_segment_to (denote_flow (CRet x) >>= K) sigma logs target sigma'.
Proof.
  intro H; eapply source_to_equ; [apply source_raw_ret|exact H].
Qed.

Local Lemma source_to_until {A} (body : CProg (option A))
  (K : option unit -> thread sE) sigma logs target sigma' :
  source_segment_to (denote_flow body >>= until_tail body K)
    sigma logs target sigma' ->
  source_segment_to (denote_flow (CUntilNone body) >>= K)
    sigma logs target sigma'.
Proof.
  intro H; eapply source_to_equ; [apply source_raw_until|exact H].
Qed.

Local Lemma source_to_read a v (K : option nat -> thread sE)
  h c logs target sigma' :
  h a = Some v ->
  source_segment_to (K (Some v)) (h,c) logs target sigma' ->
  source_segment_to (denote_flow (CRead a) >>= K) (h,c) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply exact_segment_equ with (u' := residual)
    (u := Vis (inr (inr (SRd a))) (fun v => K (Some v))).
  - cbn [denote_flow]; unfold heap_event; rewrite !bind_bind, bind_vis.
    step; constructor; intro x; rewrite !bind_ret_l; reflexivity.
  - change (ExactThreadSegment (Vis (inr (inr (SRd a))) (fun v => K (Some v)))
      (h,c) ([] ++ logs) residual sigma').
    eapply exact_segment_user; [|exact Hseg].
    cbn [emit_list]; rewrite (sh_rd_some a h c v Hr); reflexivity.
  - reflexivity.
Qed.

Local Lemma source_upd_present h a v x : h x <> None -> upd h a v x <> None.
Proof.
  intro H; unfold upd; destruct (Nat.eqb x a); [discriminate|exact H].
Qed.

Local Lemma source_to_write a v (K : option unit -> thread sE)
  h c logs target sigma' :
  h a <> None ->
  source_segment_to (K (Some tt)) (upd h a v,c) logs target sigma' ->
  source_segment_to (denote_flow (CWrite a v) >>= K) (h,c) logs target sigma'.
Proof.
  intros Hp (residual & Hseg & Htail).
  destruct (h a) as [w|] eqn:Hw; [|contradiction].
  exists residual; split; [|exact Htail].
  eapply exact_segment_equ with (u' := residual)
    (u := Vis (inr (inr (SWr a v))) (fun _ => K (Some tt))).
  - cbn [denote_flow]; unfold heap_event; rewrite !bind_bind, bind_vis.
    step; constructor; intros [].
    change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
      K (Some tt)).
    rewrite !bind_ret_l; reflexivity.
  - change (ExactThreadSegment (Vis (inr (inr (SWr a v))) (fun _ => K (Some tt)))
      (h,c) ([] ++ logs) residual sigma').
    eapply exact_segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite (sh_wr_some a h c v w Hw); reflexivity.
  - reflexivity.
Qed.

Local Lemma source_to_emit tag block (K : option unit -> thread sE)
  h c logs target sigma' :
  source_segment_to (K (Some tt)) (h,S c) logs target sigma' ->
  source_segment_to (denote_flow (CEmit tag block) >>= K) (h,c)
    (SPop tag block c :: logs) target sigma'.
Proof.
  intros (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply exact_segment_equ with (u' := residual)
    (u := Vis (inr (inr (SEmit tag block))) (fun _ => K (Some tt))).
  - cbn [denote_flow]; unfold heap_event; rewrite !bind_bind, bind_vis.
    step; constructor; intros [].
    change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
      K (Some tt)).
    rewrite !bind_ret_l; reflexivity.
  - change (ExactThreadSegment
      (Vis (inr (inr (SEmit tag block))) (fun _ => K (Some tt)))
      (h,c) ([SPop tag block c] ++ logs) residual sigma').
    eapply exact_segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite sh_emit; reflexivity.
  - reflexivity.
Qed.

Local Lemma source_to_cas_success a expected desired
  (K : option bool -> thread sE) h c logs target sigma' :
  h a = Some expected ->
  source_segment_to (K (Some true)) (upd h a desired,c) logs target sigma' ->
  source_segment_to (denote_flow (CCAS a expected desired) >>= K)
    (h,c) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply exact_segment_equ with (u' := residual)
    (u := Vis (inr (inr (SCAS a expected desired))) (fun b => K (Some b))).
  - cbn [denote_flow]; unfold heap_event; rewrite !bind_bind, bind_vis.
    step; constructor; intro b; rewrite !bind_ret_l; reflexivity.
  - change (ExactThreadSegment
      (Vis (inr (inr (SCAS a expected desired))) (fun b => K (Some b)))
      (h,c) ([] ++ logs) residual sigma').
    eapply exact_segment_user; [|exact Hseg].
    cbn [emit_list]; rewrite (sh_cas_success a expected desired h c Hr); reflexivity.
  - reflexivity.
Qed.

Local Lemma source_to_cas_failure a expected desired current
  (K : option bool -> thread sE) h c logs target sigma' :
  h a = Some current -> current <> expected ->
  source_segment_to (K (Some false)) (h,c) logs target sigma' ->
  source_segment_to (denote_flow (CCAS a expected desired) >>= K)
    (h,c) logs target sigma'.
Proof.
  intros Hr Hne (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply exact_segment_equ with (u' := residual)
    (u := Vis (inr (inr (SCAS a expected desired))) (fun b => K (Some b))).
  - cbn [denote_flow]; unfold heap_event; rewrite !bind_bind, bind_vis.
    step; constructor; intro b; rewrite !bind_ret_l; reflexivity.
  - change (ExactThreadSegment
      (Vis (inr (inr (SCAS a expected desired))) (fun b => K (Some b)))
      (h,c) ([] ++ logs) residual sigma').
    eapply exact_segment_user; [|exact Hseg].
    cbn [emit_list]; rewrite (sh_cas_failure a expected desired current h c Hr Hne);
      reflexivity.
  - reflexivity.
Qed.

Local Lemma source_to_yield (K : option unit -> thread sE) sigma target :
  guard_equ (K (Some tt)) target ->
  source_segment_to (denote_flow CYield >>= K) sigma [] target sigma.
Proof.
  intro Htail; exists (K (Some tt)); split; [|exact Htail].
  eapply exact_segment_equ with (u := Vis (inl Yield) (fun _ => K (Some tt))).
  - cbn [denote_flow]; unfold source_yield; rewrite !bind_bind, bind_vis.
    step; constructor; intros [].
    change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
      K (Some tt)).
    rewrite !bind_ret_l; reflexivity.
  - apply exact_segment_yield.
  - reflexivity.
Qed.

(** Finite syntax normalization is used only for raw equ and leading guards.
    It never changes a scheduler focus or invokes pool sbisim congruence. *)
Ltac allocator_raw_equ :=
  cbn beta iota zeta;
  first [reflexivity |
    lazymatch goal with
    | |- (denote_flow (CBind _ _) >>= _) ≅ _ =>
        etransitivity; [apply source_raw_bind|]; allocator_raw_equ
    | |- (denote_flow (CRet _) >>= _) ≅ _ =>
        etransitivity; [apply source_raw_ret|]; allocator_raw_equ
    | |- ((?t >>= ?k) >>= ?j) ≅ _ =>
        etransitivity; [apply bind_bind|]; allocator_raw_equ
    | |- (Ret _ >>= _) ≅ _ =>
        etransitivity; [apply bind_ret_l|]; allocator_raw_equ
    | |- _ ≅ (denote_flow (CBind _ _) >>= _) => symmetry; allocator_raw_equ
    | |- _ ≅ (denote_flow (CRet _) >>= _) => symmetry; allocator_raw_equ
    | |- _ ≅ ((_ >>= _) >>= _) => symmetry; allocator_raw_equ
    | |- _ ≅ (Ret _ >>= _) => symmetry; allocator_raw_equ
    | |- Guard _ ≅ Guard _ => apply guard_equ_node; allocator_raw_equ
    end].

#[local] Instance source_guard_equ_proper :
  Proper (equ eq ==> equ eq ==> iff) guard_equ.
Proof.
  intros t t' Ht u u' Hu; split; intro H.
  - eapply guard_equ_trans; [apply guard_equ_equ; symmetry; exact Ht|].
    eapply guard_equ_trans; [exact H|apply guard_equ_equ; exact Hu].
  - eapply guard_equ_trans; [apply guard_equ_equ; exact Ht|].
    eapply guard_equ_trans; [exact H|apply guard_equ_equ; symmetry; exact Hu].
Qed.

Ltac allocator_residual_raw :=
  unfold remote_residual, owner_residual, remote_free, remote_client,
    detach_remote, remote_link_tail, remote_cas_tail, detach_cas_tail,
    owner_offer_tail, denote, client_next, remote_after_free,
    owner_next, owner_after_collect, owner_after_detach;
  allocator_raw_equ.

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
  first [congruence | apply source_upd_present; allocator_present].

Ltac allocator_segment_steps :=
  repeat first
    [ progress (cbn beta iota zeta)
    | match goal with
      | H : Nat.eqb ?x ?y = ?b |- context [Nat.eqb ?x ?y] => rewrite H
      end
    | progress (rewrite Nat.eqb_refl)
    | lazymatch goal with
      | |- source_segment_to (denote_flow (CBind _ _) >>= _) _ _ _ _ =>
          apply source_to_bind
      | |- source_segment_to (denote_flow (CRet _) >>= _) _ _ _ _ =>
          apply source_to_ret
      | |- source_segment_to (denote_flow (CUntilNone _) >>= _) _ _ _ _ =>
          apply source_to_until
      | |- source_segment_to (denote_flow (CRead _) >>= _) _ _ _ _ =>
          eapply source_to_read; [eassumption|]
      | |- source_segment_to (denote_flow (CWrite _ _) >>= _) _ _ _ _ =>
          eapply source_to_write; [allocator_present|]
      | |- source_segment_to (denote_flow (CEmit _ _) >>= _) _ _ _ _ =>
          apply source_to_emit
      | |- source_segment_to (denote_flow (CCAS _ _ _) >>= _) _ _ _ _ =>
          first [eapply source_to_cas_success; [congruence|] |
            eapply source_to_cas_failure;
              [eassumption|apply Nat.eqb_neq; eassumption|]]
      end
    | progress (
        lazymatch goal with
        | |- source_segment_to ?src ?sigma ?logs ?target ?sigma' =>
          let src' := eval cbv beta iota zeta delta
            [remote_residual owner_residual denote remote_client remote_free
             remote_attempt remote_link_tail remote_cas_tail client_round
             owner_round collect_remote detach_remote detach_attempt
             detach_cas_tail reclaim_step owner_offer_tail offer_block
             until_tail client_next remote_after_free owner_next
             owner_after_collect owner_after_detach] in src in
          change (source_segment_to src' sigma logs target sigma')
        end) ];
  apply source_to_yield; allocator_residual_alignment.

(** The checked model branches provide precisely the successful heap reads.
    Repeated checked writes remain allocated even if addresses coincide; no
    heap extensionality, freshness assumption, or unchecked CAS is used here. *)
Local Opaque denote_flow ICtree.iter ICtree.bind.

Lemma turn_source_exact_segment base who s t event :
  turn base who s = Some (t,event) ->
  exists residual,
    ExactThreadSegment ((allocator_pool base s) $ slot_of_actor who)
      (aheap s,acount s) (turn_observations event) residual (aheap t,acount t) /\
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
    owner_state remote0_state remote1_state turn_observations].
  all: lazymatch goal with
  | |- exists residual, ExactThreadSegment ?src ?sigma ?logs residual ?sigma' /\
      guard_equ residual ?target =>
      change (source_segment_to src sigma logs target sigma')
  end.
  all: allocator_segment_steps.
Qed.

Local Transparent denote_flow ICtree.iter ICtree.bind.

Lemma turn_source_segment_checked base who s t event :
  turn base who s = Some (t,event) ->
  exists residual,
    ThreadSegment ((allocator_pool base s) $ slot_of_actor who)
      (aheap s,acount s) (turn_observations event) residual (aheap t,acount t) /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  intro Hturn; destruct (turn_source_exact_segment base who s t event Hturn)
    as (residual & Hseg & Htail).
  exists residual; split; [now apply ExactThreadSegment_segment|exact Htail].
Qed.

Lemma turn_source_segment base capacity who s t event :
  allocator_inv base capacity s -> turn base who s = Some (t,event) ->
  exists residual,
    ThreadSegment ((allocator_pool base s) $ slot_of_actor who)
      (aheap s,acount s) (turn_observations event) residual (aheap t,acount t) /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof. intros _; apply turn_source_segment_checked. Qed.

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
      (turn_observations event) residual sigma' /\
    state_agrees sigma' t /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  intros Hpool Hagree Hinv Hturn.
  pose proof (state_agrees_reheap sigma s Hagree) as Hreheap.
  pose proof (allocator_inv_state_equiv base capacity s
    (source_reheap sigma s) Hreheap Hinv) as Hactualinv.
  destruct (turn_respects_heq_some base who s (source_reheap sigma s)
    t event Hreheap Hturn) as (actual & Hactual & Hnext).
  destruct (turn_source_segment base capacity who
    (source_reheap sigma s) actual event Hactualinv Hactual)
    as (canonical & Hseg & Htail).
  change (ThreadSegment ((allocator_pool base s) $ slot_of_actor who)
    (fst sigma,snd sigma) (turn_observations event) canonical
    (aheap actual,acount actual)) in Hseg.
  destruct sigma as [h c]; cbn [fst snd] in Hseg.
  destruct (guard_equ_segment
    ((allocator_pool base s) $ slot_of_actor who)
    (ts $ slot_of_actor who) (h,c) (turn_observations event)
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
  logs = turn_observations event /\ state_agrees sigma' t /\
  guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  intros Hpool Hagree Hinv Hturn Hseg.
  destruct (selected_turn_source_segment base capacity ts sigma s who t event
    Hpool Hagree Hinv Hturn) as (other & sigma2 & Hother & Hstate & Htail).
  destruct (ThreadSegment_deterministic (ts $ slot_of_actor who) sigma
    logs residual sigma' (turn_observations event) other sigma2 Hseg Hother)
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
    logs = turn_observations event /\ state_agrees sigma' t /\
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
  exists (turn_observations event), residual, sigma'; exact Hseg.
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

Local Lemma source_replace_current n (ts : pool sE n) (i : Fin.t n) :
  pool_equ (ts @ i := (ts $ i)) ts.
Proof.
  intro j; destruct (Fin.eq_dec j i) as [->|Hne].
  - rewrite Vector.nth_replace_eq; reflexivity.
  - rewrite Vector.nth_replace_neq by congruence; reflexivity.
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

Local Lemma source_equ_sbisim {X} (t u : ictreeW SObs X) : t ≅ u -> t ~ u.
Proof. intro E; rewrite E; reflexivity. Qed.

(** Each equation encompasses every branch of the phase table.  The result
    retains the actual residual at None focus: guard_equ is not silently
    promoted to an unfocused-pool congruence. *)
Theorem turn_interp_nd base capacity who s t event :
  allocator_inv base capacity s -> turn base who s = Some (t,event) ->
  exists residual,
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who) /\
    interp_nd 3 (allocator_pool base s) (Some (slot_of_actor who))
      (aheap s,acount s) ~
    emit_list (turn_observations event)
      (interp_nd 3 (allocator_pool base t @ slot_of_actor who := residual)
        None (aheap t,acount t)).
Proof.
  intros Hinv Hturn.
  destruct (turn_source_segment base capacity who s t event Hinv Hturn)
    as (residual & Hseg & Htail).
  exists residual; split; [exact Htail|].
  etransitivity.
  - symmetry; apply source_equ_sbisim, interp_nd_equ, source_replace_current.
  - etransitivity.
    + exact (segment_interp_nd 2 (allocator_pool base s) (slot_of_actor who)
        ((allocator_pool base s) $ slot_of_actor who) (aheap s,acount s)
        (turn_observations event) residual (aheap t,acount t) Hseg).
    + apply emit_list_sbisim, source_equ_sbisim, interp_nd_equ.
      exact (source_replace_turn base who s t event residual Hturn).
Qed.

Theorem turn_interp_rr base capacity who s t event cursor :
  allocator_inv base capacity s -> turn base who s = Some (t,event) ->
  exists residual,
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who) /\
    interp_schedule_rr sh 3 (allocator_pool base s) (Some (slot_of_actor who))
      cursor (aheap s,acount s) ~
    emit_list (turn_observations event)
      (interp_schedule_rr sh 3
        (allocator_pool base t @ slot_of_actor who := residual)
        None cursor (aheap t,acount t)).
Proof.
  intros Hinv Hturn.
  destruct (turn_source_segment base capacity who s t event Hinv Hturn)
    as (residual & Hseg & Htail).
  exists residual; split; [exact Htail|].
  etransitivity.
  - symmetry; apply source_equ_sbisim, interp_schedule_rr_equ,
      source_replace_current.
  - etransitivity.
    + exact (segment_interp_rr 2 (allocator_pool base s) (slot_of_actor who)
        ((allocator_pool base s) $ slot_of_actor who) cursor (aheap s,acount s)
        (turn_observations event) residual (aheap t,acount t) Hseg).
    + apply emit_list_sbisim, source_equ_sbisim, interp_schedule_rr_equ.
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
    emit_list (turn_observations event)
      (interp_nd 3 (ts @ slot_of_actor who := residual) None sigma').
Proof.
  intros Hpool Hagree Hinv Hturn.
  destruct (selected_turn_source_segment base capacity ts sigma s who t event
    Hpool Hagree Hinv Hturn) as (residual & sigma' & Hseg & Hstate & Htail).
  exists residual, sigma'; split; [exact Hstate|]; split; [exact Htail|].
  etransitivity.
  - symmetry; apply source_equ_sbisim, interp_nd_equ, source_replace_current.
  - exact (segment_interp_nd 2 ts (slot_of_actor who)
      (ts $ slot_of_actor who) sigma (turn_observations event) residual sigma' Hseg).
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
    emit_list (turn_observations event)
      (interp_schedule_rr sh 3 (ts @ slot_of_actor who := residual) None cursor sigma').
Proof.
  intros Hpool Hagree Hinv Hturn.
  destruct (selected_turn_source_segment base capacity ts sigma s who t event
    Hpool Hagree Hinv Hturn) as (residual & sigma' & Hseg & Hstate & Htail).
  exists residual, sigma'; split; [exact Hstate|]; split; [exact Htail|].
  etransitivity.
  - symmetry; apply source_equ_sbisim, interp_schedule_rr_equ,
      source_replace_current.
  - exact (segment_interp_rr 2 ts (slot_of_actor who)
      (ts $ slot_of_actor who) cursor sigma (turn_observations event) residual sigma' Hseg).
Qed.

From Coinduction Require Import coinduction rel tactics.
Local Open Scope nat_scope.

Fixpoint rr_guards {X} (n : nat) (t : ictreeW SObs X) : ictreeW SObs X :=
  match n with 0 => t | S n => Guard (rr_guards n t) end.

Lemma rr_guards_trans {X} n l (t u : ictreeW SObs X) :
  trans l t u -> trans l (rr_guards n t) u.
Proof. intro H; induction n; cbn [rr_guards]; [exact H|now apply trans_guard]. Qed.

(** This proof relation consumes a guard on BOTH sides in a silent round.
    Its finite prefixes cannot turn silent divergence into a visible event. *)
CoInductive rr_aligned {X} : ictreeW SObs X -> ictreeW SObs X -> Prop :=
| rr_align_guard t u n m t' u' :
    t ≅ rr_guards (S n) t' -> u ≅ rr_guards (S m) u' ->
    rr_aligned t' u' -> rr_aligned t u
| rr_align_log t u n m o t' u' :
    t ≅ rr_guards n (Vis (Log o) (fun _ => t')) ->
    u ≅ rr_guards m (Vis (Log o) (fun _ => u')) ->
    rr_aligned t' u' -> rr_aligned t u.

Lemma rr_aligned_equ {X} (t u a b : ictreeW SObs X) :
  t ≅ a -> u ≅ b -> rr_aligned t u -> rr_aligned a b.
Proof.
  intros Et Eu H; destruct H as [t u n m t' u' El Er H|t u n m o t' u' El Er H].
  - eapply rr_align_guard; [| |exact H].
    + transitivity t; [symmetry; exact Et|exact El].
    + transitivity u; [symmetry; exact Eu|exact Er].
  - eapply rr_align_log; [| |exact H].
    + transitivity t; [symmetry; exact Et|exact El].
    + transitivity u; [symmetry; exact Eu|exact Er].
Qed.

Lemma rr_aligned_sym {X} : forall t u : ictreeW SObs X,
  rr_aligned t u -> rr_aligned u t.
Proof.
  cofix IH; intros t u H;
    destruct H as [t u n m t' u' El Er H|t u n m o t' u' El Er H].
  - eapply rr_align_guard; [exact Er|exact El|apply IH; exact H].
  - eapply rr_align_log; [exact Er|exact El|apply IH; exact H].
Qed.

Lemma rr_aligned_match {X} l T U :
  @trans_ (writerE SObs) _ X l T U ->
  forall u, rr_aligned (go T) u ->
  exists u', trans l u u' /\ rr_aligned (go U) u'.
Proof.
  intro TR; induction TR as
    [l inner target TR IH
    |n pick k result Eresult
    |e k answer result Eresult
    |result value Eresult]; intros u A.
  - inversion A as [left right n m tl tr El Er Hnext|left right n m o tl tr El Er Hnext];
      subst; clear A; rename Hnext into A.
    + apply equ_guard_invE in El; destruct n as [|n].
      * cbn [rr_guards] in El.
        assert (Ai : rr_aligned (go (observe inner)) tr).
        { eapply rr_aligned_equ; [|reflexivity|exact A].
          transitivity inner; [symmetry; exact El|apply ictree_eta]. }
        destruct (IH tr Ai) as (next & Tnext & Anext).
        exists next; split; [rewrite Er; now apply rr_guards_trans|exact Anext].
      * apply IH; eapply rr_aligned_equ; [apply ictree_eta|reflexivity|].
        eapply rr_align_guard; eassumption.
    + destruct n as [|n].
      * cbn [rr_guards] in El; step in El; cbn in El; inversion El.
      * apply equ_guard_invE in El.
        apply IH; eapply rr_aligned_equ; [apply ictree_eta|reflexivity|].
        eapply rr_align_log; eassumption.
  - inversion A as [left right p q tl tr El Er Hnext|left right p q o tl tr El Er Hnext];
      subst; clear A; rename Hnext into A.
    + step in El; cbn [rr_guards] in El; inversion El.
    + destruct p; step in El; cbn [rr_guards] in El; inversion El.
  - destruct e as [o]; destruct answer.
    inversion A as [left right n m tl tr El Er Hnext|left right n m p tl tr El Er Hnext];
      subst; clear A; rename Hnext into A.
    + step in El; cbn [rr_guards] in El; inversion El.
    + destruct n as [|n].
      * cbn [rr_guards] in El.
        pose proof (equ_vis_invT El) as [_ Ep]; injection Ep as Ep; subst p.
        pose proof (equ_vis_invE El tt) as Ek.
        exists tr; split.
        -- rewrite Er; apply rr_guards_trans.
           exact (@trans_vis (writerE SObs) _ X (Log o) tt (fun _ => tr)).
        -- eapply rr_aligned_equ; [|reflexivity|exact A].
           transitivity (k tt); [symmetry; exact Ek|].
           transitivity result; [exact Eresult|apply ictree_eta].
      * step in El; cbn [rr_guards] in El; inversion El.
  - inversion A as [left right n m tl tr El Er Hnext|left right n m o tl tr El Er Hnext];
      subst; clear A; rename Hnext into A.
    + step in El; cbn [rr_guards] in El; inversion El.
    + destruct n; step in El; cbn [rr_guards] in El; inversion El.
Qed.

Lemma rr_aligned_trans {X} (t u next : ictreeW SObs X) l :
  rr_aligned t u -> trans l t next ->
  exists other, trans l u other /\ rr_aligned next other.
Proof.
  intros A TR.
  assert (Ae : rr_aligned (go (observe t)) u).
  { eapply rr_aligned_equ; [apply ictree_eta|reflexivity|exact A]. }
  destruct (rr_aligned_match l (observe t) (observe next) TR u Ae)
    as (other & To & Ao).
  exists other; split; [exact To|].
  eapply rr_aligned_equ; [symmetry; apply ictree_eta|reflexivity|exact Ao].
Qed.

Lemma rr_aligned_sbisim {X} : forall t u : ictreeW SObs X,
  rr_aligned t u -> t ~ u.
Proof.
  unfold sbisim; apply_coinduction; fold_sbisim.
  intros R IH t u A; split; intros l next TR.
  - destruct (rr_aligned_trans t u next l A TR) as (other & To & Ao).
    exists l, other; split; [exact To|]; split; [now apply IH|reflexivity].
  - destruct (rr_aligned_trans u t next l (rr_aligned_sym t u A) TR)
      as (other & To & Ao).
    exists l, other; split; [exact To|]; split.
    + apply IH, rr_aligned_sym; exact Ao.
    + reflexivity.
Qed.

Lemma rr_guards_equ {X} n (t u : ictreeW SObs X) :
  t ≅ u -> rr_guards n t ≅ rr_guards n u.
Proof.
  intro E; induction n; cbn [rr_guards]; [exact E|now apply guard_equ_node].
Qed.
Lemma rr_guards_add {X} n m (t : ictreeW SObs X) :
  rr_guards (n + m) t = rr_guards n (rr_guards m t).
Proof. induction n; cbn [rr_guards Nat.add]; [reflexivity|now rewrite IHn]. Qed.
Lemma rr_guards_guard {X} n (t : ictreeW SObs X) :
  rr_guards n (Guard t) = rr_guards (S n) t.
Proof. induction n; cbn [rr_guards]; [reflexivity|now rewrite IHn]. Qed.

(** A finite proof prefix, not an additional evaluator or scheduler. *)
Inductive rr_token := RRGuard | RRLog (o : SObs).
Fixpoint rr_prefix {X} (word : list rr_token) (t : ictreeW SObs X) : ictreeW SObs X :=
  match word with
  | [] => t
  | RRGuard :: rest => Guard (rr_prefix rest t)
  | RRLog o :: rest => Vis (Log o) (fun _ => rr_prefix rest t)
  end.
Fixpoint rr_prefix_events (word : list rr_token) : list SObs :=
  match word with
  | [] => []
  | RRGuard :: rest => rr_prefix_events rest
  | RRLog o :: rest => o :: rr_prefix_events rest
  end.
Lemma rr_prefix_app {X} left right (t : ictreeW SObs X) :
  rr_prefix (left ++ right) t = rr_prefix left (rr_prefix right t).
Proof.
  induction left as [|[|o] rest IH]; cbn [List.app rr_prefix];
    [reflexivity|now rewrite IH|now rewrite IH].
Qed.
Lemma rr_prefix_equ {X} word (t u : ictreeW SObs X) :
  t ≅ u -> rr_prefix word t ≅ rr_prefix word u.
Proof.
  intro E; induction word as [|[|o] rest IH]; cbn [rr_prefix].
  - exact E.
  - now apply guard_equ_node.
  - apply vis_equ_node; intros []; exact IH.
Qed.
Lemma rr_prefix_events_app left right :
  rr_prefix_events (left ++ right) = rr_prefix_events left ++ rr_prefix_events right.
Proof.
  induction left as [|[|o] rest IH]; cbn [List.app rr_prefix_events];
    [reflexivity|exact IH|now rewrite IH].
Qed.
Lemma rr_prefix_events_logs logs : rr_prefix_events (List.map RRLog logs) = logs.
Proof. induction logs; cbn [List.map rr_prefix_events]; [reflexivity|now rewrite IHlogs]. Qed.
Lemma rr_prefix_emit {X} logs (t : ictreeW SObs X) :
  rr_prefix (List.map RRLog logs) t ≅ emit_list logs t.
Proof.
  induction logs as [|o rest IH]; [reflexivity|].
  cbn [List.map rr_prefix]; rewrite emit_list_cons.
  apply vis_equ_node; intros []; exact IH.
Qed.
Lemma rr_prefix_no_events {X} word (t : ictreeW SObs X) :
  rr_prefix_events word = [] -> rr_prefix word t = rr_guards (List.length word) t.
Proof.
  induction word as [|[|o] rest IH]; cbn [rr_prefix_events rr_prefix List.length rr_guards];
    intro E; [reflexivity|now rewrite IH|discriminate].
Qed.
Lemma rr_prefix_one_event {X} word o (t : ictreeW SObs X) :
  rr_prefix_events word = [o] -> exists n m,
  rr_prefix word t ≅ rr_guards n (Vis (Log o) (fun _ => rr_guards m t)).
Proof.
  induction word as [|[|p] rest IH]; cbn [rr_prefix_events]; intro E; [discriminate| |].
  - destruct (IH E) as (n & m & H).
    exists (S n), m; cbn [rr_prefix rr_guards]; now apply guard_equ_node.
  - injection E as Ep Er; subst p.
    exists 0, (List.length rest); cbn [rr_prefix rr_guards].
    apply vis_equ_node; intros []; rewrite (rr_prefix_no_events rest t Er); reflexivity.
Qed.

Local Lemma exact_rr_user_replaced n (ts : pool sE (S n)) (i : Fin.t (S n))
  (e : sE) (k : encode e -> thread sE) m sigma :
  interp_schedule_rr sh (S n)
    (ts @ i := (@go CEff _ unit (VisF (inr (inr e) : CEff) k))) (Some i) m sigma ≅
  (runStateT (sh e) sigma >>= fun '(x,sigma') =>
    rr_guards 3 (interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma')).
Proof.
  etransitivity.
  - eapply segment_rr_user_exact; rewrite Vector.nth_replace_eq; reflexivity.
  - apply equ_clo_bind with (S := eq); [reflexivity|].
    intros [x sigma'] y <-; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma exact_segment_rr_prefix n (ts : pool sE (S n)) (i : Fin.t (S n))
  t m sigma logs residual sigma' :
  ExactThreadSegment t sigma logs residual sigma' ->
  exists word, rr_prefix_events word = logs /\
  interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma ≅
    rr_prefix word (Guard
      (interp_schedule_rr sh (S n) (ts @ i := residual) None m sigma')).
Proof.
  intro H; revert n ts i m.
  induction H as
    [k sigma
    |t sigma logs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma logs u' residual sigma' Etu H IH Eout]; intros n ts i m.
  - exists []; split; [reflexivity|]; cbn [rr_prefix].
    etransitivity.
    + eapply segment_rr_yield_exact; rewrite Vector.nth_replace_eq; reflexivity.
    + rewrite Vector.replace_replace_eq; reflexivity.
  - destruct (IH n ts i m) as (word & Ew & Et).
    exists (RRGuard :: word); split; [exact Ew|]; cbn [rr_prefix].
    etransitivity.
    + eapply segment_rr_guard_exact; rewrite Vector.nth_replace_eq; reflexivity.
    + apply guard_equ_node; rewrite Vector.replace_replace_eq; exact Et.
  - destruct (IH n ts i m) as (word & Ew & Et).
    exists (List.map RRLog before ++ RRGuard :: RRGuard :: RRGuard :: word); split.
    + rewrite rr_prefix_events_app, rr_prefix_events_logs; cbn [rr_prefix_events].
      now rewrite Ew.
    + etransitivity; [apply exact_rr_user_replaced|].
      set (resume := fun response : (encode e * SSig)%type =>
        let '(x,sigma0) := response in
        rr_guards 3 (interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma0)).
      transitivity (emit_list before (Ret (result,sigma1)) >>= resume).
      * apply equ_clo_bind with (S := eq); [exact Eh|intros x y <-; reflexivity].
      * etransitivity; [apply emit_list_ret_bind|]; unfold resume.
        transitivity (emit_list before
          (rr_guards 3 (rr_prefix word (Guard
            (interp_schedule_rr sh (S n) (ts @ i := residual) None m sigma'))))).
        -- apply emit_list_equ, rr_guards_equ; exact Et.
        -- rewrite rr_prefix_app; cbn [rr_prefix rr_guards].
           symmetry; apply rr_prefix_emit.
  - destruct (IH n ts i m) as (word & Ew & Et).
    exists word; split; [exact Ew|].
    etransitivity.
    + apply interp_schedule_rr_equ, replace_pool_equ; [apply pool_equ_refl|exact Etu].
    + etransitivity; [exact Et|].
      apply rr_prefix_equ, guard_equ_node, interp_schedule_rr_equ, replace_pool_equ;
        [apply pool_equ_refl|exact Eout].
Qed.

Lemma selected_turn_exact_segment base (ts : pool sE 3) s who t event :
  pool_guard_equ ts (allocator_pool base s) -> turn base who s = Some (t,event) ->
  exists residual,
    ExactThreadSegment (ts $ slot_of_actor who) (aheap s,acount s)
      (turn_observations event) residual (aheap t,acount t) /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who).
Proof.
  intros Hpool Hturn.
  destruct (turn_source_exact_segment base who s t event Hturn) as (residual & Hseg & Htail).
  exists residual; split; [|exact Htail].
  apply (proj2 (guard_equ_exact_segment_iff
    (ts $ slot_of_actor who) ((allocator_pool base s) $ slot_of_actor who)
    (Hpool (slot_of_actor who)) (aheap s,acount s) (turn_observations event)
    residual (aheap t,acount t))); exact Hseg.
Qed.

Lemma selected_turn_rr_prefix base (ts : pool sE 3) s who t event cursor :
  pool_guard_equ ts (allocator_pool base s) -> turn base who s = Some (t,event) ->
  exists residual word,
    rr_prefix_events word = turn_observations event /\
    guard_equ residual ((allocator_pool base t) $ slot_of_actor who) /\
    interp_schedule_rr sh 3 ts (Some (slot_of_actor who)) cursor (aheap s,acount s) ≅
      rr_prefix word (Guard (interp_schedule_rr sh 3
        (ts @ slot_of_actor who := residual) None cursor (aheap t,acount t))).
Proof.
  intros Hpool Hturn.
  destruct (selected_turn_exact_segment base ts s who t event Hpool Hturn)
    as (residual & Hseg & Htail).
  destruct (exact_segment_rr_prefix 2 ts (slot_of_actor who)
    (ts $ slot_of_actor who) cursor (aheap s,acount s) (turn_observations event)
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
  destruct event as [o|]; cbn [turn_observations] in Ew.
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

Lemma nd_st_emit_list {X} (R : ictreeW SObs X -> ictreeW SObs X -> Prop)
  logs t u :
  st eq R t u -> st eq R (emit_list logs t) (emit_list logs u).
Proof.
  intro H; induction logs as [|o rest IH]; [exact H|].
  change (st eq R (log o ;; emit_list rest t) (log o ;; emit_list rest u)).
  apply st_clo_bind_eq; [reflexivity|intros []; exact IH].
Qed.

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
    (turn_observations event) residual (aheap next,acount next) Hseg) as Esegment.
  rewrite slot_of_actor_of_slot in Esegment, Hnextpool.
  assert (Efocus : interp_nd 3 ts (Some i) (aheap s,acount s) ~
    emit_list (turn_observations event)
      (interp_nd 3 (ts @ i := residual) None (aheap next,acount next))).
  {
    etransitivity; [|exact Esegment].
    symmetry; apply source_equ_sbisim, interp_nd_equ,
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
  destruct event as [o|]; cbn [turn_observations].
  - eapply equ_clos_st_goal;
      [reflexivity|symmetry; exact (emit_list_cons o [] (Guard (model_nd base next)))|].
    apply (nd_st_emit_list R [o]); exact Hcontinue.
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
