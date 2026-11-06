From Stdlib Require Import List Lia Arith.PeanoNat.
From TICL Require Import Events.HeapModel.
From examples Require Import CSL.Queue.Representation.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(** ** A generic queue heap *)

Definition nodeval (ns vs : list nat) : Heap :=
  apply_writes (rev (node_writes ns vs)) hemp.

Definition qheap (hdr: nat) (ns vs: list nat) : Heap :=
  fun x => if Nat.eqb x hdr then Some (last ns 0)
        else if Nat.eqb x (S hdr) then Some (List.hd 0 ns)
        else nodeval ns vs x.

Lemma nodeval_dom: forall ns vs x,
    nodeval ns vs x <> None -> In x (cells ns).
Proof.
  intros ns vs x H; unfold nodeval in H.
  apply apply_writes_dom_exact in H as [H | H]; [| exfalso; apply H; reflexivity].
  rewrite map_rev in H; apply in_rev in H.
  now apply node_writes_keys_subset in H.
Qed.

Lemma nodeval_in: forall ns vs x,
    length ns = length vs -> In x (cells ns) -> nodeval ns vs x <> None.
Proof.
  intros ns vs x Hlen Hx; unfold nodeval.
  exact (proj2 (node_writes_dom ns vs x Hlen) Hx).
Qed.


Lemma nodeval_chain: forall hdr ns vs,
    qwf hdr ns -> length ns = length vs -> chain (nodeval ns vs) ns vs 0.
Proof.
  intros hdr ns vs Hwf Hlen; destruct ns as [|a ns].
  - destruct vs; cbn in Hlen; [apply chain_nil | discriminate].
  - assert (Hnd : NoDup (cells (a :: ns))).
    { apply cells_nodup.
      - pose proof (proj1 Hwf) as Hnames.
        apply NoDup_cons_iff in Hnames; tauto.
      - intros b d Hb Hd; apply (proj2 (proj2 Hwf)); now right. }
    assert (Hnext : length vs = length (tl (a :: ns) ++ [0])).
    { rewrite app_length; cbn; cbn in Hlen; lia. }
    pose proof (node_writes_contents (a :: ns) vs Hlen Hnd) as Hcontents.
    assert (Hpayload : Forall2 (fun b v => nodeval (a :: ns) vs b = Some v)
      (a :: ns) (map fst (combine vs (tl (a :: ns) ++ [0])))).
    { apply Forall2_map_right.
      eapply Forall2_impl'; [exact Hcontents |].
      intros b [v next] Hb Hpair [Hp Hl]; exact Hp. }
    assert (Hlinks : Forall2 (fun b next => nodeval (a :: ns) vs (S b) = Some next)
      (a :: ns) (map snd (combine vs (tl (a :: ns) ++ [0])))).
    { apply Forall2_map_right.
      eapply Forall2_impl'; [exact Hcontents |].
      intros b [v next] Hb Hpair [Hp Hl]; exact Hl. }
    rewrite map_fst_combine in Hpayload by exact Hnext.
    rewrite map_snd_combine in Hlinks by exact Hnext.
    split; [now apply linked_of_Forall2 | exact Hpayload].
Qed.

Theorem qheap_qrep: forall hdr ns vs,
    qwf hdr ns -> length ns = length vs -> ns <> [] ->
    qrep hdr ns vs (qheap hdr ns vs).
Proof.
  intros hdr ns vs Hwf Hlen Hne.
  pose proof (qwf_hdr_cells _ _ Hwf) as Hhnc.
  pose proof (qwf_shdr_cells _ _ Hwf) as Hshnc.
  assert (Hhdr: qheap hdr ns vs hdr = Some (last ns 0))
    by (unfold qheap; now rewrite Nat.eqb_refl).
  assert (Hshdr: qheap hdr ns vs (S hdr) = Some (List.hd 0 ns)).
  { unfold qheap; destruct (Nat.eqb_spec (S hdr) hdr) as [C | _]; [lia |].
    now rewrite Nat.eqb_refl. }
  assert (Hcell: forall x, In x (cells ns) -> qheap hdr ns vs x = nodeval ns vs x).
  { intros x Hx; unfold qheap.
    destruct (Nat.eqb_spec x hdr) as [Ex | Hnh]; [rewrite Ex in Hx; contradiction |].
    destruct (Nat.eqb_spec x (S hdr)) as [Ex | Hnsh];
      [rewrite Ex in Hx; contradiction | reflexivity]. }
  split; [exact Hwf | split; [exact Hshdr | split; [| split]]].
  - unfold tailok; destruct ns as [| a ns]; [contradiction | exact Hhdr].
  - eapply chain_mono; [apply (nodeval_chain hdr ns vs Hwf Hlen) |].
    intros x Hx; now apply Hcell.
  - split.
    + unfold qheap.
      destruct (Nat.eqb_spec 0 hdr) as [C | _];
        [exfalso; apply (qwf_zero _ _ Hwf); rewrite C; apply in_eq |].
      destruct (Nat.eqb_spec 0 (S hdr)) as [C | _]; [lia |].
      destruct (nodeval ns vs 0) eqn:E; [| reflexivity].
      exfalso; apply (qwf_zero _ _ Hwf), in_cons, in_cons.
      apply (nodeval_dom ns vs 0); congruence.
    + intros x Hx; unfold qcells in Hx.
      destruct Hx as [Ex | [Ex | Hx]].
      * rewrite <- Ex, Hhdr; discriminate.
      * rewrite <- Ex, Hshdr; discriminate.
      * rewrite (Hcell x Hx); revert Hx; now apply nodeval_in.
Qed.

Theorem qheap_qex: forall hdr ns vs, qex hdr ns (qheap hdr ns vs).
Proof.
  intros hdr ns vs x Hx; unfold qheap in Hx.
  destruct (Nat.eqb_spec x hdr) as [Ex | Hnh]; [rewrite Ex; apply in_eq |].
  destruct (Nat.eqb_spec x (S hdr)) as [Ex | Hnsh];
    [rewrite Ex; apply in_cons, in_eq |].
  apply in_cons, in_cons, (nodeval_dom ns vs x), Hx.
Qed.

(** ** Runtime-base contiguous queue layout

    The stride-two node geometry ([node_addrs], [node_cells_range]) is owned
    by [Events.HeapModel]. *)

Definition queue_nodes (hdr count : nat) : list nat :=
  node_addrs (hdr + 2) count.

Definition fill_nodes_heap (first : nat) (values : list nat) (h : Heap) : Heap :=
  apply_writes (node_writes (node_addrs first (length values)) values) h.

Definition init_queue_heap (hdr : nat) (values : list nat) (h : Heap) : Heap :=
  let ns := queue_nodes hdr (length values) in
  fill_nodes_heap (hdr + 2) values
    (upd (upd h hdr (last ns 0)) (S hdr) (List.hd 0 ns)).

Definition new_queue_heap (hdr : nat) (values : list nat) (h : Heap) : Heap :=
  init_queue_heap hdr values
    (hunion (hblock hdr (2 * S (length values))) h).

Lemma queue_nodes_length hdr count : length (queue_nodes hdr count) = count.
Proof. apply node_addrs_length. Qed.

Lemma queue_nodes_qwf hdr count : Nat.lt 0 hdr -> qwf hdr (queue_nodes hdr count).
Proof.
  intro Hhdr; unfold qwf, queue_nodes.
  change (NoDup (node_addrs hdr (S count)) /\
    ~ In 0 (node_addrs hdr (S count)) /\
    (forall a b, In a (node_addrs hdr (S count)) ->
      In b (node_addrs hdr (S count)) -> a <> S b)).
  split; [apply node_addrs_nodup | split].
  - intro Hin; apply node_addrs_in in Hin as (j & Hj & Hx); lia.
  - intros a b Ha Hb.
    apply node_addrs_in in Ha as (j & Hj & Ha).
    apply node_addrs_in in Hb as (k & Hk & Hb).
    lia.
Qed.

Lemma queue_cells_range hdr count x :
  In x (qcells hdr (queue_nodes hdr count)) <->
    Nat.le hdr x /\ Nat.lt x (hdr + 2 * S count).
Proof.
  change (In x (cells (node_addrs hdr (S count))) <->
    Nat.le hdr x /\ Nat.lt x (hdr + 2 * S count)).
  apply node_cells_range.
Qed.

Lemma qheap_queue_nodes_rep hdr values :
  Nat.lt 0 hdr ->
  qrep hdr (queue_nodes hdr (length values)) values
    (qheap hdr (queue_nodes hdr (length values)) values).
Proof.
  intro Hhdr; destruct values as [| value values].
  - change (qrep hdr [] [] (qheap hdr [] [])).
    assert (Htail : qheap hdr [] [] hdr = Some 0).
    { unfold qheap; now rewrite Nat.eqb_refl. }
    assert (Hhead : qheap hdr [] [] (S hdr) = Some 0).
    { unfold qheap; destruct (Nat.eqb_spec (S hdr) hdr) as [Hbad | Hne]; [lia |].
      now rewrite Nat.eqb_refl. }
    split; [exact (queue_nodes_qwf hdr 0 Hhdr) |].
    split; [exact Hhead |].
    split; [change (qheap hdr [] [] hdr <> None); rewrite Htail; discriminate |].
    split; [apply chain_nil | split].
    + unfold qheap; destruct (Nat.eqb_spec 0 hdr) as [Hbad | Hne]; [lia |].
      reflexivity.
    + intros x [Hx | [Hx | []]]; subst x;
        [rewrite Htail | rewrite Hhead]; discriminate.
  - apply qheap_qrep.
    + now apply queue_nodes_qwf.
    + apply queue_nodes_length.
    + discriminate.
Qed.

Lemma nodeval_node_addrs_out first values x :
  (Nat.lt x first \/ Nat.le (first + 2 * length values) x) ->
  nodeval (node_addrs first (length values)) values x = None.
Proof.
  intro Hout; destruct (nodeval (node_addrs first (length values)) values x) eqn:E;
    [| reflexivity].
  exfalso.
  assert (Hin : In x (cells (node_addrs first (length values)))).
  { apply (nodeval_dom (node_addrs first (length values)) values x); rewrite E; discriminate. }
  apply node_cells_range in Hin; lia.
Qed.

(** Filling a strided list changes exactly its node cells. *)
Lemma fill_nodes_heap_lookup first values h x :
  fill_nodes_heap first values h x =
    match nodeval (node_addrs first (length values)) values x with
    | Some value => Some value
    | None => h x
    end.
Proof.
  unfold fill_nodes_heap, nodeval.
  rewrite apply_writes_rev by
    (apply node_writes_nodup; [apply node_addrs_length | apply node_addrs_cells_nodup]).
  rewrite !apply_writes_lookup.
  destruct (find (fun av => Nat.eqb x (fst av))
    (rev (node_writes (node_addrs first (length values)) values)))
    as [[a value] |]; reflexivity.
Qed.

Lemma init_queue_heap_agrees hdr values h :
  heq (init_queue_heap hdr values h)
    (hunion (qheap hdr (queue_nodes hdr (length values)) values) h).
Proof.
  intro x; unfold init_queue_heap; rewrite fill_nodes_heap_lookup.
  unfold hunion, qheap, queue_nodes.
  destruct (Nat.eqb_spec x hdr) as [Hx | Hhdr].
  - subst x; rewrite nodeval_node_addrs_out by (left; lia).
    rewrite upd_neq by lia; apply upd_eq.
  - destruct (Nat.eqb_spec x (S hdr)) as [Hx | Hshdr].
    + subst x; rewrite nodeval_node_addrs_out by (left; lia); apply upd_eq.
    + rewrite upd_neq by exact Hshdr.
      rewrite upd_neq by exact Hhdr; reflexivity.
Qed.

Lemma new_queue_heap_agrees hdr values h :
  Nat.lt 0 hdr -> block_free h hdr (2 * S (length values)) ->
  heq (new_queue_heap hdr values h)
    (hunion (qheap hdr (queue_nodes hdr (length values)) values) h).
Proof.
  intros Hhdr Hfree x; unfold new_queue_heap.
  rewrite (init_queue_heap_agrees hdr values _ x); unfold hunion.
  destruct (qheap hdr (queue_nodes hdr (length values)) values x) eqn:E;
    [reflexivity |].
  assert (Hout : hblock hdr (2 * S (length values)) x = None).
  { apply hblock_out.
    destruct (Nat.lt_ge_cases x hdr) as [Hlo | Hlo]; [now left | right].
    destruct (Nat.lt_ge_cases x (hdr + 2 * S (length values))) as [Hhi | Hhi];
      [| exact Hhi].
    exfalso.
    pose proof (qheap_queue_nodes_rep hdr values Hhdr) as Hq.
    apply (qrep_fp _ _ _ _ Hq x).
    - apply queue_cells_range; split; assumption.
    - exact E. }
  now rewrite Hout.
Qed.

Lemma new_queue_heap_disjoint hdr values h :
  block_free h hdr (2 * S (length values)) ->
  hdisj (qheap hdr (queue_nodes hdr (length values)) values) h.
Proof.
  intros Hfree x.
  destruct (qheap hdr (queue_nodes hdr (length values)) values x) eqn:E;
    [right | now left].
  assert (Hin : In x (qcells hdr (queue_nodes hdr (length values)))).
  { apply (qheap_qex hdr (queue_nodes hdr (length values)) values x); rewrite E; discriminate. }
  apply queue_cells_range in Hin as [Hlo Hhi].
  replace x with (hdr + (x - hdr)) by lia.
  apply Hfree; lia.
Qed.

Lemma fill_nodes_heap_finite first values h :
  heap_finite h -> heap_finite (fill_nodes_heap first values h).
Proof.
  apply apply_writes_finite.
Qed.

Lemma new_queue_heap_finite hdr values h :
  heap_finite h -> heap_finite (new_queue_heap hdr values h).
Proof.
  intro Hh; unfold new_queue_heap, init_queue_heap.
  apply fill_nodes_heap_finite, heap_finite_upd, heap_finite_upd.
  apply heap_finite_hunion; [apply heap_finite_hblock | exact Hh].
Qed.
