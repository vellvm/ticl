(** * A finite link-first allocator page.

    The five metadata cells precede stride-two blocks.  A block's first cell
    is its free-list link; its successor cell is mutable client payload.
    The stride-two geometry ([cells], [node_addrs], [init_links_heap]) is
    owned by [Events.HeapModel]; this module only fixes the page layout. *)

From Stdlib Require Import List Lia Arith.PeanoNat.
From TICL Require Import Events.HeapModel Utils.Pcm Utils.Lists.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Definition page_size (capacity : nat) : nat := 5 + 2 * capacity.
Definition remote_head (base : nat) : nat := base.
Definition local_head (base : nat) : nat := base + 1.
Definition drain_head (base : nat) : nat := base + 2.
Definition mailbox (base : nat) (client : bool) : nat :=
  base + 3 + (if client then 1 else 0).
Definition page_blocks (base capacity : nat) : list nat :=
  node_addrs (base + 5) capacity.
Definition tag_alloc : nat := 0.
Definition tag_retire : nat := 1.
Definition tag_reclaim : nat := 2.
Definition tag_retry : nat := 3.

Definition page_metadata (base : nat) : list nat :=
  [remote_head base; local_head base; drain_head base;
   mailbox base false; mailbox base true].
Definition page_cells (base capacity : nat) : list nat :=
  page_metadata base ++ cells (page_blocks base capacity).

Lemma page_size_positive capacity : Nat.lt 0 (page_size capacity).
Proof. unfold page_size; lia. Qed.

Lemma page_blocks_in base capacity b :
  In b (page_blocks base capacity) <->
    exists j, Nat.lt j capacity /\ b = base + 5 + 2 * j.
Proof. apply node_addrs_in. Qed.

Lemma page_blocks_length base capacity :
  length (page_blocks base capacity) = capacity.
Proof. apply node_addrs_length. Qed.

Lemma page_blocks_nodup base capacity :
  NoDup (page_blocks base capacity).
Proof. apply node_addrs_nodup. Qed.

Lemma page_blocks_bounds base capacity b :
  In b (page_blocks base capacity) ->
    Nat.le (base + 5) b /\ Nat.lt (S b) (base + page_size capacity).
Proof.
  intros Hin; apply page_blocks_in in Hin as (j & Hj & Hb).
  unfold page_size; lia.
Qed.

Lemma page_blocks_link_payload_disjoint base capacity a b :
  In a (page_blocks base capacity) -> In b (page_blocks base capacity) ->
  a <> S b.
Proof. apply node_addrs_link_payload_disjoint. Qed.

Lemma page_metadata_range base x :
  In x (page_metadata base) <-> Nat.le base x /\ Nat.lt x (base + 5).
Proof.
  unfold page_metadata, remote_head, local_head, drain_head, mailbox.
  cbn [In]; lia.
Qed.

Lemma page_metadata_nodup base : NoDup (page_metadata base).
Proof.
  unfold page_metadata, remote_head, local_head, drain_head, mailbox.
  repeat constructor; cbn [In]; intuition lia.
Qed.


Lemma mailbox_injective base client client' :
  mailbox base client = mailbox base client' -> client = client'.
Proof. destruct client, client'; unfold mailbox; intros H; try reflexivity; lia. Qed.

Lemma page_metadata_blocks_disjoint base capacity x b :
  In x (page_metadata base) -> In b (page_blocks base capacity) ->
  x <> b /\ x <> S b.
Proof.
  intros Hx Hb; apply page_metadata_range in Hx.
  apply page_blocks_bounds in Hb; lia.
Qed.

Lemma page_block_cells_range base capacity x :
  In x (cells (page_blocks base capacity)) <->
    Nat.le (base + 5) x /\ Nat.lt x (base + page_size capacity).
Proof.
  unfold page_blocks; rewrite node_cells_range; unfold page_size; lia.
Qed.

Lemma page_cells_range base capacity x :
  In x (page_cells base capacity) <->
    Nat.le base x /\ Nat.lt x (base + page_size capacity).
Proof.
  unfold page_cells; rewrite in_app_iff, page_metadata_range, page_block_cells_range.
  unfold page_size; lia.
Qed.

(** This is the addresswise coverage useful for splitting metadata, links,
    and payloads in the ownership invariant. *)
Lemma page_interval_coverage base capacity x :
  (Nat.le base x /\ Nat.lt x (base + page_size capacity)) <->
    In x (page_metadata base) \/
    exists b, In b (page_blocks base capacity) /\ (x = b \/ x = S b).
Proof.
  rewrite <- page_cells_range; unfold page_cells.
  rewrite in_app_iff, in_cells; reflexivity.
Qed.

Lemma page_cells_nodup base capacity : NoDup (page_cells base capacity).
Proof.
  unfold page_cells; apply NoDup_app.
  - apply page_metadata_nodup.
  - apply node_addrs_cells_nodup.
  - intros x Hmeta Hblock.
    apply page_metadata_range in Hmeta.
    apply page_block_cells_range in Hblock; lia.
Qed.


(** ** Pure counterparts of the checked initialization writes

    The order here is the source order: remote, drain, mailbox 0, mailbox 1,
    local; then links from low to high.  The allocation overlay installs the
    zero payloads.  Initialization never writes a payload cell. *)

Definition page_heap (base capacity : nat) (h : Heap) : Heap :=
  init_links_heap (base + 5) capacity
    (upd
      (upd
        (upd
          (upd
            (upd (hunion (hblock base (page_size capacity)) h)
              (remote_head base) 0)
            (drain_head base) 0)
          (mailbox base false) 0)
        (mailbox base true) 0)
      (local_head base) (match capacity with 0 => 0 | S _ => base + 5 end)).

(** ** Backing storage, checked cells, and the old frame *)

Lemma page_backing_in base capacity h x :
  (Nat.le base x /\ Nat.lt x (base + page_size capacity)) ->
  hunion (hblock base (page_size capacity)) h x = Some 0.
Proof.
  intros [Hlo Hhi]; apply hunion_some.
  replace x with (base + (x - base)) by lia; apply hblock_in; lia.
Qed.

Lemma page_heap_frame base capacity h x :
  (Nat.lt x base \/ Nat.le (base + page_size capacity) x) ->
  page_heap base capacity h x = h x.
Proof.
  intro Hout; unfold page_heap.
  rewrite init_links_heap_out by (unfold page_size in Hout; lia).
  unfold remote_head, local_head, drain_head, mailbox.
  repeat rewrite upd_neq by (unfold page_size in Hout; lia).
  apply hunion_none, hblock_out; exact Hout.
Qed.

Lemma page_heap_in base capacity h x :
  (Nat.le base x /\ Nat.lt x (base + page_size capacity)) ->
  page_heap base capacity h x <> None.
Proof.
  intro Hin; unfold page_heap; apply init_links_heap_dom; right.
  repeat apply upd_mono.
  rewrite page_backing_in by exact Hin; discriminate.
Qed.

Lemma page_heap_dom base capacity h x :
  page_heap base capacity h x <> None <->
    (Nat.le base x /\ Nat.lt x (base + page_size capacity)) \/ h x <> None.
Proof.
  destruct (Nat.lt_ge_cases x base) as [Hlo | Hlo].
  - rewrite page_heap_frame by (now left); intuition lia.
  - destruct (Nat.lt_ge_cases x (base + page_size capacity)) as [Hhi | Hhi].
    + split.
      * intro H; left; split; assumption.
      * intro H; apply page_heap_in; split; assumption.
    + rewrite page_heap_frame by (now right); intuition lia.
Qed.

Lemma page_heap_closed_dom base capacity x :
  page_heap base capacity hemp x <> None <->
    Nat.le base x /\ Nat.lt x (base + page_size capacity).
Proof.
  rewrite page_heap_dom; unfold hemp; split.
  - intros [H | H]; [exact H | exfalso; apply H; reflexivity].
  - intro H; now left.
Qed.

Lemma page_heap_closed_none base capacity x :
  page_heap base capacity hemp x = None <->
    Nat.lt x base \/ Nat.le (base + page_size capacity) x.
Proof.
  split.
  - intro Hnone; destruct (Nat.lt_ge_cases x base) as [Hlo | Hlo].
    + now left.
    + destruct (Nat.lt_ge_cases x (base + page_size capacity)) as [Hhi | Hhi].
      * exfalso; apply (page_heap_in base capacity hemp x (conj Hlo Hhi)); exact Hnone.
      * now right.
  - intro Hout; rewrite page_heap_frame by exact Hout; reflexivity.
Qed.


Lemma page_heap_old_frame base capacity h :
  block_free h base (page_size capacity) ->
  forall x, h x <> None -> page_heap base capacity h x = h x.
Proof.
  intros Hfree x Hx; destruct (Nat.lt_ge_cases x base) as [Hlo | Hlo].
  - apply page_heap_frame; now left.
  - destruct (Nat.lt_ge_cases x (base + page_size capacity)) as [Hhi | Hhi].
    + exfalso; apply Hx.
      replace x with (base + (x - base)) by lia; apply Hfree; lia.
    + apply page_heap_frame; now right.
Qed.

Lemma page_heap_on_page base capacity h f x :
  (Nat.le base x /\ Nat.lt x (base + page_size capacity)) ->
  page_heap base capacity h x = page_heap base capacity f x.
Proof.
  intro Hin; unfold page_heap; apply init_links_heap_lookup_agree.
  repeat apply upd_lookup_agree.
  rewrite (page_backing_in base capacity h x Hin).
  rewrite (page_backing_in base capacity f x Hin); reflexivity.
Qed.


Lemma page_heap_split base capacity h :
  heq (page_heap base capacity h) (hunion (page_heap base capacity hemp) h).
Proof.
  intro x; destruct (Nat.lt_ge_cases x base) as [Hlo | Hlo].
  - rewrite hunion_none.
    + apply page_heap_frame; now left.
    + rewrite page_heap_frame by (now left); reflexivity.
  - destruct (Nat.lt_ge_cases x (base + page_size capacity)) as [Hhi | Hhi].
    + rewrite hunion_eq by (apply page_heap_in; split; assumption).
      apply page_heap_on_page; split; assumption.
    + rewrite hunion_none.
      * apply page_heap_frame; now right.
      * rewrite page_heap_frame by (now right); reflexivity.
Qed.

Lemma page_heap_disjoint base capacity h :
  block_free h base (page_size capacity) ->
  hdisj (page_heap base capacity hemp) h.
Proof.
  intros Hfree x; destruct (page_heap base capacity hemp x) eqn:E.
  - right.
    assert (Hin : Nat.le base x /\ Nat.lt x (base + page_size capacity)).
    { apply page_heap_closed_dom; rewrite E; discriminate. }
    replace x with (base + (x - base)) by lia; apply Hfree; lia.
  - now left.
Qed.

Lemma page_heap_finite base capacity h :
  heap_finite h -> heap_finite (page_heap base capacity h).
Proof.
  intro Hh; unfold page_heap; apply init_links_heap_finite.
  repeat apply heap_finite_upd.
  apply heap_finite_hunion; [apply heap_finite_hblock | exact Hh].
Qed.

(** ** Initialized contents *)

Lemma page_heap_remote base capacity h :
  page_heap base capacity h (remote_head base) = Some 0.
Proof.
  unfold page_heap, remote_head, local_head, drain_head, mailbox.
  rewrite init_links_heap_out by (left; lia).
  repeat rewrite upd_neq by lia; apply upd_eq.
Qed.

Lemma page_heap_drain base capacity h :
  page_heap base capacity h (drain_head base) = Some 0.
Proof.
  unfold page_heap, remote_head, local_head, drain_head, mailbox.
  rewrite init_links_heap_out by (left; lia).
  repeat rewrite upd_neq by lia; apply upd_eq.
Qed.

Lemma page_heap_mailbox base capacity h client :
  page_heap base capacity h (mailbox base client) = Some 0.
Proof.
  destruct client; unfold page_heap, remote_head, local_head, drain_head, mailbox;
    rewrite init_links_heap_out by (left; lia);
    repeat rewrite upd_neq by lia; apply upd_eq.
Qed.

Lemma page_heap_local base capacity h :
  page_heap base capacity h (local_head base) =
    Some (match capacity with 0 => 0 | S _ => base + 5 end).
Proof.
  unfold page_heap, local_head.
  rewrite init_links_heap_out by (left; lia); apply upd_eq.
Qed.

Lemma page_heap_local_blocks base capacity h :
  page_heap base capacity h (local_head base) = Some (hd 0 (page_blocks base capacity)).
Proof. rewrite page_heap_local; destruct capacity; reflexivity. Qed.

Lemma page_heap_payload base capacity h b :
  In b (page_blocks base capacity) -> page_heap base capacity h (S b) = Some 0.
Proof.
  intro Hb; pose proof (page_blocks_bounds base capacity b Hb) as Hbounds.
  unfold page_heap; rewrite init_links_heap_payload by exact Hb.
  unfold remote_head, local_head, drain_head, mailbox.
  repeat rewrite upd_neq by lia.
  apply page_backing_in; lia.
Qed.

Lemma page_heap_link base capacity h prefix b rest :
  page_blocks base capacity = prefix ++ b :: rest ->
  page_heap base capacity h b = Some (hd 0 rest).
Proof. intro H; unfold page_heap; apply init_links_heap_link with (prefix := prefix); exact H. Qed.

Lemma page_heap_link_index base capacity h j :
  Nat.lt j capacity ->
  page_heap base capacity h (base + 5 + 2 * j) =
    Some (if Nat.ltb (S j) capacity then base + 5 + 2 * S j else 0).
Proof. intro H; unfold page_heap; apply init_links_heap_link_index, H. Qed.
