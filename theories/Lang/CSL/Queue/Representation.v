(** * Heap-backed queue representation and pure resource theory.

    This file contains NO temporal reasoning.  It fixes

    - the resource model: a partial map [Heap = nat -> option nat], with
      disjointness, union and a domain predicate;
    - the representation predicate [qrep hdr ns vs h]: the heap [h] holds a
      null-terminated singly linked list of two-cell nodes at the DISTINCT
      addresses [ns] carrying the payloads [vs], anchored at a two-cell header
      [hdr] (tail pointer) / [S hdr] (head pointer);
    - the pure list theory the temporal proof consumes: [chain] append/split
      and the footprint permutation, using the generic [Utils.Lists] theory.

    Design notes, and why they are not free choices:

    - Payloads may REPEAT.  [vs] is an arbitrary [list nat]; nothing below
      assumes the payloads are distinct.  Node ADDRESSES must be distinct and
      non-overlapping, which is [qwf].

    - [qwf] states non-overlap directly ([a <> S b] for any two node names)
      rather than through an allocation policy.  [qwf_aligned] shows that
      two-word alignment is a sufficient concrete policy. The representation
      predicate is independent of the allocator used to obtain those cells.

    - The tail pointer is constrained only when the queue is non-empty.  That
      is what makes the intermediate ownership split of [Rotate.v] uniform: at
      the instant the head node is detached, the remaining queue is a genuine
      [qrep] even when it has become empty and the tail pointer is stale.  *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat
  Sorting.Permutation.

Import ListNotations.

(* Implicit arguments are deliberately OFF: every lemma below is applied
   positionally in the rotation proof. *)

(** ** The resource model *)

From TICL Require Export Lang.CSL.Heap Utils.Lists.

(** ** Footprints and well-formedness

    The stride-two node geometry ([cells], [in_cells]) is owned by
    [TICL.Events.HeapModel]; the queue adds only its header pair. *)

(** The footprint of a queue: the header's two cells plus every node's two
    cells. *)
Definition qcells (hdr: nat) (ns: list nat) : list nat := hdr :: S hdr :: cells ns.


(** Well-formedness of the node NAMES: distinct, non-null, and non-overlapping
    (no node's payload cell is another node's link cell).  Payloads are
    unconstrained. *)
Definition qwf (hdr: nat) (ns: list nat) : Prop :=
  NoDup (hdr :: ns)
  /\ ~ In 0 (hdr :: ns)
  /\ (forall a b, In a (hdr :: ns) -> In b (hdr :: ns) -> a <> S b).

(** Two-word alignment is a sufficient concrete policy for the non-overlap
    condition.  It is offered as evidence that [qwf] is satisfiable by a
    standard layout, not used anywhere below. *)
Lemma qwf_aligned: forall hdr ns,
    NoDup (hdr :: ns) -> ~ In 0 (hdr :: ns) ->
    Forall Nat.Even (hdr :: ns) ->
    qwf hdr ns.
Proof.
  intros hdr ns Hnd H0 Hev; split; [assumption | split; [assumption |]].
  intros a b Ha Hb ->.
  rewrite Forall_forall in Hev.
  destruct (Hev _ Ha) as (m & Hm); destruct (Hev _ Hb) as (k & Hk); lia.
Qed.

Lemma qwf_perm: forall hdr ns ns', Permutation ns ns' -> qwf hdr ns -> qwf hdr ns'.
Proof.
  intros hdr ns ns' Hp (Hnd & H0 & Hov).
  assert (Hp': Permutation (hdr :: ns) (hdr :: ns')) by now constructor.
  split; [| split].
  - eapply Permutation_NoDup; eauto.
  - intro Hin; apply H0; eapply Permutation_in; [apply Permutation_sym|]; eauto.
  - intros a b Ha Hb; apply Hov;
      eapply Permutation_in; [apply Permutation_sym; exact Hp' | exact Ha
                             | apply Permutation_sym; exact Hp' | exact Hb].
Qed.

(** The inequality shapes the rotation proof needs, extracted once. *)
Lemma qwf_hdr_cells: forall hdr ns, qwf hdr ns -> ~ In hdr (cells ns).
Proof.
  intros hdr ns (Hnd & H0 & Hov) Hin.
  apply NoDup_cons_iff in Hnd as (Hni & _).
  apply in_cells in Hin as (a & Ha & [Heq | Heq]).
  - subst; contradiction.
  - eapply Hov with (a := hdr) (b := a); cbn; auto.
Qed.

Lemma qwf_shdr_cells: forall hdr ns, qwf hdr ns -> ~ In (S hdr) (cells ns).
Proof.
  intros hdr ns (Hnd & H0 & Hov) Hin.
  apply NoDup_cons_iff in Hnd as (Hni & _).
  apply in_cells in Hin as (a & Ha & [Heq | Heq]).
  - eapply Hov with (a := a) (b := hdr); cbn; auto.
  - assert (a = hdr) by lia; subst; contradiction.
Qed.

Lemma qwf_node_cells: forall hdr ns a,
    qwf hdr (a :: ns) -> ~ In a (cells ns) /\ ~ In (S a) (cells ns).
Proof.
  intros hdr ns a (Hnd & H0 & Hov).
  apply NoDup_cons_iff in Hnd as (_ & Hnd).
  apply NoDup_cons_iff in Hnd as (Hni & _).
  split; intro Hin; apply in_cells in Hin as (b & Hb & [Heq | Heq]).
  - subst; contradiction.
  - eapply Hov with (a := a) (b := b); cbn; auto.
  - eapply Hov with (a := b) (b := a); cbn; auto.
  - assert (a = b) by lia; subst; contradiction.
Qed.

Lemma qwf_zero: forall hdr ns, qwf hdr ns -> ~ In 0 (qcells hdr ns).
Proof.
  intros hdr ns (Hnd & H0 & Hov) [Hc | [Hc | Hc]].
  - apply H0; cbn; auto.
  - lia.
  - apply in_cells in Hc as (a & Ha & [Heq | Heq]); [| lia].
    apply H0; cbn; subst; auto.
Qed.

(** ** The chain of nodes *)

(** [chain h ns vs fin]: the addresses [ns] carry the payloads [vs] and are
    linked in order, the last link holding [fin].  The terminator is a
    PARAMETER: that is what lets the rotation retarget the last link by
    [chain_split] + [chain_app] instead of a bespoke surgery lemma.

    The link structure is the generic [Utils.Lists.linked] predicate at the
    successor cell [S a]; payload agreement is an ordinary [Forall2].  The
    allocator's free list, whose links live at [a], reuses the same theory
    through a different edge relation. *)
Definition chain (h: Heap) (ns vs: list nat) (fin: nat) : Prop :=
  linked (fun a next => h (S a) = Some next) ns fin
  /\ List.Forall2 (fun a v => h a = Some v) ns vs.

Lemma chain_nil: forall h fin, chain h [] [] fin.
Proof. intros h fin; split; [exact I | constructor]. Qed.

Lemma chain_cons: forall h a ns v vs fin,
    chain h (a :: ns) (v :: vs) fin <->
      h a = Some v /\ h (S a) = Some (List.hd fin ns) /\ chain h ns vs fin.
Proof.
  intros h a ns v vs fin; unfold chain; cbn [linked].
  rewrite Forall2_cons_iff; tauto.
Qed.

Lemma chain_len: forall h ns vs f, chain h ns vs f -> length ns = length vs.
Proof. intros h ns vs f (_ & Hf); eapply Forall2_length; exact Hf. Qed.

Lemma Forall2_cells_mono: forall (h h': Heap) (ns vs: list nat),
    Forall2 (fun a v => h a = Some v) ns vs ->
    (forall x, In x (cells ns) -> h' x = h x) ->
    Forall2 (fun a v => h' a = Some v) ns vs.
Proof.
  intros h h' ns vs Hf; induction Hf as [| a v ns vs Hav Hf IH]; intro Hag;
    [constructor |].
  constructor.
  - rewrite Hag; [exact Hav |].
    apply in_cells; exists a; split; now left.
  - apply IH; intros x Hx; apply Hag.
    apply in_cells in Hx as (b & Hb & Hxb).
    apply in_cells; exists b; split; [now right | exact Hxb].
Qed.

Lemma chain_mono: forall h h' ns vs fin,
    chain h ns vs fin ->
    (forall x, In x (cells ns) -> h' x = h x) ->
    chain h' ns vs fin.
Proof.
  intros h h' ns vs fin (Hl & Hf) Hag; split.
  - eapply linked_mono; [| exact Hl].
    intros a b Ha Hab; rewrite Hag; [exact Hab |].
    apply in_cells; exists a; split; [exact Ha | now right].
  - eapply Forall2_cells_mono; [exact Hf | exact Hag].
Qed.

Lemma chain_dom: forall h ns vs f x, chain h ns vs f -> In x (cells ns) -> h x <> None.
Proof.
  intros h ns; induction ns as [| a ns IH]; intros vs f x Hc Hin.
  - cbn in Hin; contradiction.
  - destruct vs as [| v vs]; [destruct Hc as (_ & Hf); inversion Hf |].
    apply chain_cons in Hc as (Ha & Hsa & Hc).
    change (In x ([a; S a] ++ cells ns)) in Hin.
    rewrite in_app_iff in Hin; destruct Hin as [Hin | Hin].
    + cbn in Hin; destruct Hin as [Hx | [Hx | []]]; subst x;
        [now rewrite Ha | now rewrite Hsa].
    + eapply IH; eauto.
Qed.

Definition agree_out (m: list nat) (h h': Heap) : Prop :=
  forall x, ~ In x m -> h' x = h x.

Lemma chain_frame: forall h h' m ns vs f,
    chain h ns vs f ->
    agree_out m h h' ->
    (forall x, In x m -> ~ In x (cells ns)) ->
    chain h' ns vs f.
Proof.
  intros h h' m ns vs f Hc Hag Hm; eapply chain_mono; [exact Hc |].
  intros x Hx; apply Hag; intro Hin; exact (Hm x Hin Hx).
Qed.

Lemma chain_app: forall h ns1 vs1 ns2 vs2 f,
    chain h ns1 vs1 (List.hd f ns2) ->
    chain h ns2 vs2 f ->
    chain h (ns1 ++ ns2) (vs1 ++ vs2) f.
Proof.
  intros h ns1 vs1 ns2 vs2 f (H1l & H1f) (H2l & H2f); split.
  - apply linked_app; assumption.
  - apply Forall2_app; assumption.
Qed.

Lemma chain_split: forall h ns1 vs1 ns2 vs2 f,
    length ns1 = length vs1 ->
    chain h (ns1 ++ ns2) (vs1 ++ vs2) f ->
    chain h ns1 vs1 (List.hd f ns2) /\ chain h ns2 vs2 f.
Proof.
  intros h ns1 vs1 ns2 vs2 f Hl (Hlk & Hf).
  apply linked_split in Hlk as (H1l & H2l).
  destruct (Forall2_app_inv_len _ _ _ _ _ Hl Hf) as (H1f & H2f).
  split; split; assumption.
Qed.

(** ** The representation predicate *)

Definition tailok (hdr: nat) (ns: list nat) (h: Heap) : Prop :=
  match ns with
  | nil => h hdr <> None
  | _ => h hdr = Some (last ns 0)
  end.

(** *** MODIFIED FOR THE FRAME EXPERIMENT (one-time resource-layer cost).

    The recurrence experiment's clause 5 was the EXACT domain condition

      [forall x, h x <> None <-> In x (qcells hdr ns)]

    which is a PRECISE assertion: it pins the heap down to the queue's own
    footprint and is therefore false of any heap that also holds an unrelated
    frame.  Under it the recurrence theorem cannot even be STATED about a
    framed heap, let alone transported to one.

    Clause 5 is weakened here to the two things the development actually
    uses -- null is unallocated, and the footprint is allocated -- so that
    [qrep] becomes the INTUITIONISTIC ("heap contains this queue") reading.
    The exact reading is retained under the name [qrepX] in [Frame.v], and
    [Frame.qrepX_frame] proves [qrepX hdr ns vs h -> hdisj h f -> f 0 = None
     -> qrep hdr ns vs (hunion h f)], so nothing proved in the recurrence
    experiment is weakened: every old hypothesis still implies the new one
    ([Frame.qrepX_qrep]).

    The grouped conjunction supports the common destructuring pattern
    [(Hwf & Hhd & Htl & Hch & Hdom)] used by the queue operation proofs. *)
Definition qrep (hdr: nat) (ns vs: list nat) (h: Heap) : Prop :=
  qwf hdr ns
  /\ h (S hdr) = Some (List.hd 0 ns)
  /\ tailok hdr ns h
  /\ chain h ns vs 0
  /\ (h 0 = None /\ forall x, In x (qcells hdr ns) -> h x <> None).

Lemma qrep_len: forall hdr ns vs h, qrep hdr ns vs h -> length ns = length vs.
Proof. intros ? ? ? ? (_ & _ & _ & Hc & _); eapply chain_len; eauto. Qed.

(** The null address is never allocated: this is what makes an out-of-footprint
    dereference of the null head pointer STUCK under the safe handler.  It is
    now an explicit clause rather than a consequence of exactness, because a
    frame must be allowed to allocate cells the queue does not own -- but NOT
    the null cell.  That is the first of the two compatibility conditions the
    transport theorem needs. *)
Lemma qrep_null: forall hdr ns vs h, qrep hdr ns vs h -> h 0 = None.
Proof. intros hdr ns vs h (_ & _ & _ & _ & Hd); exact (proj1 Hd). Qed.

Lemma qrep_fp: forall hdr ns vs h,
    qrep hdr ns vs h -> forall x, In x (qcells hdr ns) -> h x <> None.
Proof. intros hdr ns vs h (_ & _ & _ & _ & Hd); exact (proj2 Hd). Qed.

(** *** ADDED FOR THE FRAME EXPERIMENT.

    [qex hdr ns h] is the EXACTNESS side condition that clause 5 used to carry
    inside [qrep].  Keeping it separate is what makes framing expressible:
    [qrep] says "this heap CONTAINS the queue", [qrep /\ qex] says "this heap
    IS the queue".  In separation-logic terms [qrep = qrepX * True] and
    [qrepX] is the precise assertion; [Frame.v] proves both directions. *)
Definition qex (hdr: nat) (ns: list nat) (h: Heap) : Prop :=
  forall x, h x <> None -> In x (qcells hdr ns).

Lemma qrep_head_null_iff: forall hdr ns vs h,
    qrep hdr ns vs h -> (List.hd 0 ns = 0 <-> ns = []).
Proof.
  intros hdr ns vs h (Hwf & _ & _ & _ & _); destruct Hwf as (_ & H0 & _).
  destruct ns as [| a ns]; cbn; split; intro Hx; auto.
  - exfalso; apply H0; cbn; tauto.
  - discriminate.
Qed.

(** ** Rotation on the abstract lists *)


Lemma qcells_rot: forall hdr a ns x,
    In x (qcells hdr (ns ++ [a])) <-> In x (qcells hdr (a :: ns)).
Proof.
  intros hdr a ns x; unfold qcells.
  assert (Hc: forall y, In y (cells (ns ++ [a])) <-> In y (cells (a :: ns))).
  { intro y; unfold cells; rewrite flat_map_app.
    cbn; rewrite in_app_iff; cbn; tauto. }
  split; intros [H | [H | H]].
  - now left.
  - now right; left.
  - right; right; now apply Hc.
  - now left.
  - now right; left.
  - right; right; now apply Hc.
Qed.


(** ** The rotation, as heap surgery.

    [rot_heap hdr a n z h] is the heap after the four writes the rotation
    performs, in program order:

      1. [S hdr := n]   detach: the head pointer skips the old head node [a];
      2. [S z   := a]   append: the old last node (or the header, when the
                        queue has become empty) links to [a];
      3. [S a   := 0]   [a] is now the last node;
      4. [hdr   := a]   the tail pointer is [a].

    No cell outside the queue's footprint is touched, and no cell is created:
    [rot_heap_dom] states exactly that. *)

Definition rot_heap (hdr a n z: nat) (h: Heap) : Heap :=
  upd (upd (upd (upd h (S hdr) n) (S z) a) (S a) 0) hdr a.

(** The node the append phase links to: the old last node, or the header
    itself when detaching emptied the queue. *)
Definition zof (hdr: nat) (ns: list nat) : nat :=
  match ns with nil => hdr | _ => last ns 0 end.

Lemma zof_snoc: forall hdr l a, zof hdr (l ++ [a]) = a.
Proof.
  intros hdr l a; unfold zof; destruct (l ++ [a]) eqn:E.
  - exfalso; apply app_eq_nil in E as (_ & C); discriminate.
  - rewrite <- E; apply last_last.
Qed.

Lemma rot_heap_hdr: forall hdr a n z h, rot_heap hdr a n z h hdr = Some a.
Proof. intros; unfold rot_heap; apply upd_eq. Qed.

Lemma rot_heap_sa: forall hdr a n z h,
    S a <> hdr -> rot_heap hdr a n z h (S a) = Some 0.
Proof. intros; unfold rot_heap; rewrite upd_neq by assumption; apply upd_eq. Qed.

Lemma rot_heap_sz: forall hdr a n z h,
    S z <> hdr -> z <> a -> rot_heap hdr a n z h (S z) = Some a.
Proof.
  intros; unfold rot_heap.
  rewrite upd_neq by assumption.
  rewrite upd_neq by (intro C; apply H0; now injection C).
  apply upd_eq.
Qed.

Lemma rot_heap_shdr: forall hdr a n z h,
    hdr <> a -> hdr <> z -> rot_heap hdr a n z h (S hdr) = Some n.
Proof.
  intros; unfold rot_heap.
  rewrite upd_neq by (intro C; lia).
  rewrite upd_neq by (intro C; apply H; now injection C).
  rewrite upd_neq by (intro C; apply H0; now injection C).
  apply upd_eq.
Qed.

Lemma rot_heap_other: forall hdr a n z h x,
    x <> hdr -> x <> S a -> x <> S z -> x <> S hdr ->
    rot_heap hdr a n z h x = h x.
Proof.
  intros; unfold rot_heap.
  rewrite upd_neq by assumption.
  rewrite upd_neq by assumption.
  rewrite upd_neq by assumption.
  rewrite upd_neq by assumption.
  reflexivity.
Qed.

Lemma rot_heap_dom: forall hdr a n z h,
    h (S hdr) <> None -> h (S z) <> None -> h (S a) <> None -> h hdr <> None ->
    forall x, rot_heap hdr a n z h x <> None <-> h x <> None.
Proof.
  intros hdr a n z h H1 H2 H3 H4 x; unfold rot_heap.
  assert (E1: forall y, upd h (S hdr) n y <> None <-> h y <> None)
    by (intro; now apply upd_dom).
  assert (E2: forall y, upd (upd h (S hdr) n) (S z) a y <> None <-> h y <> None).
  { intro y; rewrite upd_dom; [now apply E1 | now apply E1]. }
  assert (E3: forall y, upd (upd (upd h (S hdr) n) (S z) a) (S a) 0 y <> None
                   <-> h y <> None).
  { intro y; rewrite upd_dom; [now apply E2 | now apply E2]. }
  rewrite upd_dom; [now apply E3 | now apply E3].
Qed.

(** *** The intermediate ownership split.

    Between the detach (write 1) and the append (write 2) the heap splits into
    two DISJOINT parts: a well-formed queue holding the remaining nodes [ns],
    and the two cells of the detached node [a], which the program still owns.
    This is the separating conjunction the rotation transfers across, and it is
    uniform: when [ns] is empty the remaining queue is still a [qrep], with an
    unconstrained (stale) tail pointer. *)

Definition nodeat (a v nx: nat) (h: Heap) : Prop :=
  h a = Some v /\ h (S a) = Some nx /\ (forall x, h x <> None <-> (x = a \/ x = S a)).

(** The address inequalities the rotation needs, derived once from [qwf]. *)
Definition nodeb (a x: nat) : bool := orb (Nat.eqb x a) (Nat.eqb x (S a)).

Lemma nodeb_true: forall a x, nodeb a x = true <-> (x = a \/ x = S a).
Proof.
  intros a x; unfold nodeb; rewrite Bool.orb_true_iff, !Nat.eqb_eq; reflexivity.
Qed.

Lemma nodeb_false: forall a x, nodeb a x = false <-> (x <> a /\ x <> S a).
Proof.
  intros a x; unfold nodeb; rewrite Bool.orb_false_iff, !Nat.eqb_neq; reflexivity.
Qed.

Lemma qwf_neqs: forall hdr a ns,
    qwf hdr (a :: ns) ->
    hdr <> a /\ S hdr <> a /\ hdr <> S a /\ S hdr <> S a /\ hdr <> S hdr.
Proof.
  intros hdr a ns (Hnd & H0 & Hov).
  apply NoDup_cons_iff in Hnd as (Hni & Hnd').
  assert (Hha: hdr <> a) by (intro C; apply Hni; subst; apply in_eq).
  split; [exact Hha |].
  split; [intro C; apply (Hov a hdr);
          [apply in_cons, in_eq | apply in_eq | congruence] |].
  split; [apply (Hov hdr a); [apply in_eq | apply in_cons, in_eq] |].
  split; [intro C; apply Hha; now injection C |].
  apply (Hov hdr hdr); apply in_eq.
Qed.

Lemma qwf_neqs_mem: forall hdr a ns z,
    qwf hdr (a :: ns) -> In z ns ->
    z <> hdr /\ z <> a /\ z <> S hdr /\ z <> S a
    /\ S z <> hdr /\ S z <> a /\ S z <> S hdr /\ S z <> S a.
Proof.
  intros hdr a ns z (Hnd & H0 & Hov) Hz.
  assert (HzL: In z (hdr :: a :: ns)) by (apply in_cons, in_cons; assumption).
  apply NoDup_cons_iff in Hnd as (Hni & Hnd').
  apply NoDup_cons_iff in Hnd' as (Hnia & Hnd'').
  assert (Hzh: z <> hdr) by (intro C; apply Hni; subst; apply in_cons; assumption).
  assert (Hza: z <> a) by (intro C; apply Hnia; subst; assumption).
  split; [exact Hzh |].
  split; [exact Hza |].
  split; [apply (Hov z hdr); [assumption | apply in_eq] |].
  split; [apply (Hov z a); [assumption | apply in_cons, in_eq] |].
  split; [intro C; apply (Hov hdr z); [apply in_eq | assumption | congruence] |].
  split; [intro C; apply (Hov a z);
          [apply in_cons, in_eq | assumption | congruence] |].
  split; [intro C; apply Hzh; now injection C |].
  intro C; apply Hza; now injection C.
Qed.

Lemma qwf_tail: forall hdr a ns, qwf hdr (a :: ns) -> qwf hdr ns.
Proof.
  intros hdr a ns (Hnd & H0 & Hov); split; [| split].
  - apply NoDup_cons_iff in Hnd as (Hni & Hnd').
    apply NoDup_cons_iff in Hnd' as (_ & Hnd').
    constructor; [intro C; apply Hni; now apply in_cons | assumption].
  - intro C; apply H0; cbn in C |- *; tauto.
  - intros x y Hx Hy; apply Hov; cbn in Hx, Hy |- *; tauto.
Qed.

(** The two halves of the intermediate split, as explicit heaps: the queue
    that remains after the head node is detached, and the detached node
    itself.  They are given as functions rather than existential witnesses so
    that the append phase can be stated as consuming exactly [qnode]. *)
Definition qres (hdr a n: nat) (h: Heap) : Heap :=
  fun x => if nodeb a x then None else upd h (S hdr) n x.

Definition qnode (a: nat) (h: Heap) : Heap :=
  fun x => if nodeb a x then h x else None.

(** The intermediate ownership split needs the EXACT reading: [qnode] is
    claimed to own exactly two cells, which is only true if [h] owned exactly
    the queue to begin with.  The extra [qex] hypothesis and conclusion are
    what clause 5 used to supply implicitly. *)
Theorem rot_detach_split: forall hdr a ns v vs h,
    qrep hdr (a :: ns) (v :: vs) h ->
    qex hdr (a :: ns) h ->
    hdisj (qres hdr a (List.hd 0 ns) h) (qnode a h)
    /\ heq (upd h (S hdr) (List.hd 0 ns)) (hunion (qres hdr a (List.hd 0 ns) h) (qnode a h))
    /\ (qrep hdr ns vs (qres hdr a (List.hd 0 ns) h)
        /\ qex hdr ns (qres hdr a (List.hd 0 ns) h))
    /\ nodeat a v (List.hd 0 ns) (qnode a h).
Proof.
  intros hdr a ns v vs h Hq Hex.
  pose proof Hq as (Hwf & Hhd & Htl & Hch & Hdom0).
  assert (Hdom: forall x, h x <> None <-> In x (qcells hdr (a :: ns)))
    by (intro x; split; [apply Hex | apply (proj2 Hdom0)]).
  apply chain_cons in Hch as (Ha & Hsa & Hch).
  pose proof (qwf_neqs _ _ _ Hwf) as (Hha & Hsha & Hhsa & Hshsa & Hhshdr).
  pose proof (qwf_node_cells _ _ _ Hwf) as (Hanc & Hsanc).
  pose proof (qwf_tail _ _ _ Hwf) as Hwfns.
  pose proof (qwf_shdr_cells _ _ Hwfns) as Hshdrnc.
  assert (Hhdrdom: h hdr <> None) by (apply Hdom; apply in_eq).
  assert (Ea: nodeb a a = true) by (apply nodeb_true; now left).
  assert (Esa: nodeb a (S a) = true) by (apply nodeb_true; now right).
  assert (Ehdr: nodeb a hdr = false) by (apply nodeb_false; split; congruence).
  assert (Eshdr: nodeb a (S hdr) = false) by (apply nodeb_false; split; congruence).
  assert (Hqshdr: qres hdr a (List.hd 0 ns) h (S hdr) = Some (List.hd 0 ns))
    by (unfold qres; rewrite Eshdr; apply upd_eq).
  assert (Hqhdr: qres hdr a (List.hd 0 ns) h hdr = h hdr)
    by (unfold qres; rewrite Ehdr; rewrite upd_neq by congruence; reflexivity).
  split; [| split; [| split]].
  - intro x; unfold qres, qnode; destruct (nodeb a x); [now left | now right].
  - intro x; unfold qres, qnode, hunion; destruct (nodeb a x) eqn:E.
    + apply nodeb_true in E as [-> | ->]; rewrite upd_neq by congruence; reflexivity.
    + destruct (upd h (S hdr) (List.hd 0 ns) x); reflexivity.
  - (* the remaining queue is a genuine representation; when the detach has
       emptied it, the tail pointer is stale and [tailok] does not constrain it *)
    assert (Hres: forall x, qres hdr a (List.hd 0 ns) h x <> None
                       <-> In x (qcells hdr ns)).
    { intro x; unfold qres; split.
      - destruct (nodeb a x) eqn:E; [congruence |].
        apply nodeb_false in E as (Exa & Exsa); intro Hx.
        destruct (Nat.eqb_spec x (S hdr)) as [-> | Hne]; [apply in_cons, in_eq |].
        rewrite upd_neq in Hx by assumption.
        apply Hdom in Hx; unfold qcells in Hx |- *.
        destruct Hx as [C | [C | Hx]];
          [subst; apply in_eq | subst; apply in_cons, in_eq |].
        apply in_cons, in_cons.
        cbn in Hx; destruct Hx as [C | [C | Hx]]; [congruence | congruence | exact Hx].
      - intro Hx.
        assert (Hnb: nodeb a x = false).
        { apply nodeb_false; unfold qcells in Hx.
          destruct Hx as [C | [C | Hx]].
          - subst; split; congruence.
          - subst; split; congruence.
          - split; intro C; subst; contradiction. }
        rewrite Hnb.
        destruct (Nat.eqb_spec x (S hdr)) as [-> | Hne]; [rewrite upd_eq; congruence |].
        rewrite upd_neq by assumption; apply Hdom.
        unfold qcells in Hx |- *.
        destruct Hx as [C | [C | Hx]];
          [subst; apply in_eq | subst; apply in_cons, in_eq
          | apply in_cons, in_cons; cbn; tauto]. }
    assert (Hresnull: qres hdr a (List.hd 0 ns) h 0 = None).
    { destruct (qres hdr a (List.hd 0 ns) h 0) eqn:E0; [| reflexivity].
      exfalso; apply (qwf_zero hdr ns Hwfns), Hres; congruence. }
    split; [| intros x Hx; apply Hres; exact Hx].
    split; [exact Hwfns | split; [exact Hqshdr | split; [| split]]].
    + unfold tailok; destruct ns as [| b ns'];
        [rewrite Hqhdr; exact Hhdrdom | rewrite Hqhdr; cbn in Htl |- *; exact Htl].
    + eapply chain_frame with (m := [a; S a; S hdr]) (h := h); [exact Hch | |].
      * intros x Hx; unfold qres.
        assert (Hnb: nodeb a x = false).
        { apply nodeb_false; split.
          - intro C; subst; apply Hx; apply in_eq.
          - intro C; subst; apply Hx; apply in_cons, in_eq. }
        rewrite Hnb.
        rewrite upd_neq by (intro C; subst; apply Hx; apply in_cons, in_cons, in_eq).
        reflexivity.
      * intros x Hx; cbn in Hx.
        destruct Hx as [C | [C | [C | []]]]; subst; assumption.
    + split; [exact Hresnull | intros x Hx; apply Hres; exact Hx].
  - (* the detached node, still owned *)
    unfold nodeat, qnode; split; [| split].
    + rewrite Ea; exact Ha.
    + rewrite Esa; exact Hsa.
    + intro x; destruct (nodeb a x) eqn:E.
      * apply nodeb_true in E as Ex; split; [intros _; exact Ex |].
        intros _; destruct Ex as [-> | ->]; [now rewrite Ha | now rewrite Hsa].
      * apply nodeb_false in E as (Exa & Exsa).
        split; [congruence | intros [C | C]; congruence].
Qed.

(** The separating-conjunction reading of the same fact. *)
Corollary rot_detach_sep: forall hdr a ns v vs h,
    qrep hdr (a :: ns) (v :: vs) h ->
    qex hdr (a :: ns) h ->
    exists hq hn,
      hdisj hq hn
      /\ heq (upd h (S hdr) (List.hd 0 ns)) (hunion hq hn)
      /\ qrep hdr ns vs hq
      /\ nodeat a v (List.hd 0 ns) hn.
Proof.
  intros hdr a ns v vs h H Hex.
  apply (rot_detach_split hdr a ns v vs h H) in Hex as (H1 & H2 & (H3 & _) & H4).
  eauto 6.
Qed.


Lemma cells_mono_app: forall x l1 l2, In x (cells l1) -> In x (cells (l1 ++ l2)).
Proof. intros x l1 l2 H; unfold cells in *; rewrite flat_map_app, in_app_iff; now left. Qed.

Lemma cells_mono_cons: forall x b l, In x (cells l) -> In x (cells (b :: l)).
Proof. intros x b l H; cbn; auto. Qed.

(** ** The rotation theorem.

    One completed rotation turns the represented queue [a :: ns] / [v :: vs]
    into [ns ++ [a]] / [vs ++ [v]] -- exactly the abstract pop-and-push -- and
    touches no cell outside the queue's own footprint. *)
Theorem rot_heap_spec: forall hdr a ns v vs h,
    qrep hdr (a :: ns) (v :: vs) h ->
    qrep hdr (ns ++ [a]) (vs ++ [v]) (rot_heap hdr a (List.hd 0 ns) (zof hdr ns) h)
    /\ (forall x, rot_heap hdr a (List.hd 0 ns) (zof hdr ns) h x <> None <-> h x <> None).
Proof.
  intros hdr a ns v vs h Hq.
  pose proof Hq as (Hwf & Hhd & Htl & Hch & Hdom).
  apply chain_cons in Hch as (Ha & Hsa & Hch).
  pose proof (qwf_neqs _ _ _ Hwf) as (Hha & Hsha & Hhsa & Hshsa & Hhshdr).
  pose proof (qwf_node_cells _ _ _ Hwf) as (Hanc & Hsanc).
  pose proof (qwf_hdr_cells _ _ Hwf) as Hhnc.
  pose proof (qwf_shdr_cells _ _ Hwf) as Hshnc.
  assert (Hhdrdom: h hdr <> None) by (apply (proj2 Hdom); apply in_eq).
  assert (Hshdrdom: h (S hdr) <> None) by (rewrite Hhd; discriminate).
  assert (Hsadom: h (S a) <> None) by (rewrite Hsa; discriminate).
  destruct (list_eq_dec Nat.eq_dec ns []) as [Hnil | Hne].
  - (* the queue had one element: detaching empties it, the append re-links
       the header itself, and the structure comes back to where it started *)
    subst ns.
    destruct vs as [| v1 vs1]; [| destruct Hch as (_ & Hf); inversion Hf].
    cbn in Hsa |- *.
    assert (Hdom': forall x, rot_heap hdr a 0 hdr h x <> None <-> h x <> None)
      by (apply rot_heap_dom; assumption).
    split; [| exact Hdom'].
    split; [exact Hwf | split; [| split; [| split]]].
    + rewrite (rot_heap_sz hdr a 0 hdr h); [reflexivity | congruence | congruence].
    + cbn; apply rot_heap_hdr.
    + cbn [app]; apply (proj2 (chain_cons _ _ _ _ _ _)); split; [| split].
      * rewrite rot_heap_other by (first [congruence | lia]); exact Ha.
      * apply rot_heap_sa; congruence.
      * apply chain_nil.
    + split.
      * destruct (rot_heap hdr a 0 hdr h 0) eqn:E0; [| reflexivity].
        exfalso; assert (Hc: h 0 <> None) by (apply Hdom'; congruence).
        apply Hc; exact (proj1 Hdom).
      * intro x; rewrite Hdom'; apply (proj2 Hdom).
  - (* the general case: the append re-links the old last node *)
    destruct (exists_last Hne) as (ns0 & zz & Hns).
    assert (Hzz: In zz ns) by (rewrite Hns, in_app_iff; right; apply in_eq).
    pose proof (qwf_neqs_mem _ _ _ _ Hwf Hzz)
      as (Hzh & Hza & Hzsh & Hzsa & Hszh & Hsza & Hszsh & Hszsa).
    assert (Hz: zof hdr ns = zz) by (rewrite Hns; apply zof_snoc).
    assert (Hvne: vs <> []).
    { intro C; rewrite C in Hch; apply chain_len in Hch;
      rewrite Hns, app_length in Hch; cbn in Hch; lia. }
    destruct (exists_last Hvne) as (vs0 & vz & Hvs).
    assert (Hlen: length ns0 = length vs0).
    { apply chain_len in Hch; rewrite Hns, Hvs, !app_length in Hch; cbn in Hch; lia. }
    rewrite Hns, Hvs in Hch.
    apply chain_split in Hch as (Hch0 & Hchz); [| exact Hlen].
    cbn [List.hd] in Hch0; apply chain_cons in Hchz as (Hzv & Hszv & _).
    assert (Hszdom: h (S zz) <> None) by (rewrite Hszv; discriminate).
    assert (Hdom': forall x, rot_heap hdr a (List.hd 0 ns) zz h x <> None <-> h x <> None)
      by (apply rot_heap_dom; assumption).
    rewrite Hz.
    split; [| exact Hdom'].
    split; [| split; [| split; [| split]]].
    + eapply qwf_perm; [| exact Hwf].
      change (Permutation (a :: ns) (ns ++ [a])); apply (rotl_perm (a :: ns)).
    + rewrite rot_heap_shdr by congruence.
      rewrite hd_app; cbn; f_equal; symmetry; now apply hd_default.
    + unfold tailok; destruct (ns ++ [a]) eqn:E.
      * exfalso; apply app_eq_nil in E as (_ & C); discriminate.
      * rewrite <- E, last_last; apply rot_heap_hdr.
    + apply chain_app.
      * (* the remaining nodes, with the last link retargeted to [a] *)
        cbn; rewrite Hns, Hvs; apply chain_app.
        -- cbn; eapply chain_frame with (m := [hdr; S hdr; S a; S zz]) (h := h);
             [exact Hch0 | |].
           ++ intros x Hx; apply rot_heap_other;
                intro C; subst x; apply Hx;
                [apply in_eq | apply in_cons, in_cons, in_eq
                | apply in_cons, in_cons, in_cons, in_eq | apply in_cons, in_eq].
           ++ intros x Hx Hin; cbn in Hx.
              assert (Hin': In x (cells (a :: ns)))
                by (apply cells_mono_cons; rewrite Hns; now apply cells_mono_app).
              destruct Hx as [C | [C | [C | [C | []]]]]; subst x.
              ** now apply Hhnc.
              ** now apply Hshnc.
              ** apply Hsanc; rewrite Hns; now apply cells_mono_app.
              ** (* [S zz] is the link the append rewrites; it is not a cell of
                    the nodes that stay in place *)
                 apply in_cells in Hin as (c & Hc & [C | C]).
                 --- assert (Hc': In c ns) by (rewrite Hns, in_app_iff; now left).
                     destruct Hwf as (_ & _ & Hov).
                     apply (Hov c zz);
                       [apply in_cons, in_cons; exact Hc'
                       | apply in_cons, in_cons; exact Hzz
                       | congruence].
                 --- assert (Hcz: c = zz) by lia.
                     destruct Hwf as (Hnd & _ & _).
                     apply NoDup_cons_iff in Hnd as (_ & Hnd).
                     apply NoDup_cons_iff in Hnd as (_ & Hnd).
                     rewrite Hns in Hnd; apply NoDup_remove_2 in Hnd.
                     apply Hnd; rewrite app_nil_r; rewrite <- Hcz; exact Hc.
        -- cbn [app List.hd]; apply (proj2 (chain_cons _ _ _ _ _ _)); split; [| split].
           ++ rewrite rot_heap_other by (first [congruence | lia]); exact Hzv.
           ++ cbn [List.hd]; apply rot_heap_sz; congruence.
           ++ apply chain_nil.
      * cbn [app List.hd]; apply (proj2 (chain_cons _ _ _ _ _ _)); split; [| split].
        -- rewrite rot_heap_other by (first [congruence | lia]); exact Ha.
        -- cbn [List.hd]; apply rot_heap_sa; congruence.
        -- apply chain_nil.
    + split.
      * destruct (rot_heap hdr a (List.hd 0 ns) zz h 0) eqn:E0; [| reflexivity].
        exfalso; assert (Hc: h 0 <> None) by (apply Hdom'; congruence).
        apply Hc; exact (proj1 Hdom).
      * intro x; rewrite Hdom'; intro Hx; apply (proj2 Hdom).
        apply qcells_rot; exact Hx.
Qed.

(** ** Two facts the language layer needs about the rotation's footprint. *)


(** The cell the append phase writes is always already allocated: it is the
    header's link cell when the detach empties the queue, and the last node's
    link cell otherwise. *)
Lemma qrep_zof_dom: forall hdr a ns v vs h,
    qrep hdr (a :: ns) (v :: vs) h -> h (S (zof hdr ns)) <> None.
Proof.
  intros hdr a ns v vs h Hq.
  pose proof Hq as (Hwf & Hhd & Htl & Hch & Hdom).
  destruct ns as [| b ns1].
  - cbn [zof]; rewrite Hhd; discriminate.
  - apply (proj2 Hdom); unfold qcells; apply in_cons, in_cons.
    apply in_cells; exists (last (b :: ns1) 0); split.
    + apply in_cons, last_in; discriminate.
    + right; reflexivity.
Qed.

(** The address the program computes for the append is exactly [zof]. *)
Lemma zof_compute: forall hdr a ns,
    qwf hdr (a :: ns) ->
    (if Nat.eqb (List.hd 0 ns) 0 then hdr else last (a :: ns) 0) = zof hdr ns.
Proof.
  intros hdr a ns (Hnd & H0 & Hov); destruct ns as [| b ns1]; [reflexivity |].
  cbn [List.hd].
  destruct (Nat.eqb_spec b 0) as [-> | Hb]; [exfalso; apply H0; cbn; tauto |].
  reflexivity.
Qed.

