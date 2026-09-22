(** * HeapQ: a heap-backed rotating queue -- resource model and pure theory.

    This file contains NO temporal reasoning.  It fixes

    - the resource model: a partial map [Heap = nat -> option nat], with
      disjointness, union and a domain predicate;
    - the representation predicate [qrep hdr ns vs h]: the heap [h] holds a
      null-terminated singly linked list of two-cell nodes at the DISTINCT
      addresses [ns] carrying the payloads [vs], anchored at a two-cell header
      [hdr] (tail pointer) / [S hdr] (head pointer);
    - the pure list theory the temporal proof consumes: [chain] append/split,
      the footprint permutation, and the [find] lemmas restated at [nat].

    Design notes, and why they are not free choices:

    - Payloads may REPEAT.  [vs] is an arbitrary [list nat]; nothing below
      assumes the payloads are distinct.  Node ADDRESSES must be distinct and
      non-overlapping, which is [qwf].

    - [qwf] states non-overlap directly ([a <> S b] for any two node names)
      rather than through an allocation policy.  [qwf_aligned] shows that
      two-word alignment is a sufficient concrete policy.  No allocation
      happens anywhere in this development; [qwf] is a precondition on a
      PREALLOCATED structure.

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

From TICL Require Export Lang.CSL.Heap.

Lemma upd_eq: forall h a v, upd h a v a = Some v.
Proof. intros; unfold upd; now rewrite Nat.eqb_refl. Qed.

Lemma upd_neq: forall h a v x, x <> a -> upd h a v x = h x.
Proof. intros; unfold upd; now apply Nat.eqb_neq in H as ->. Qed.

Lemma upd_dom: forall h a v x, h a <> None -> (upd h a v x <> None <-> h x <> None).
Proof.
  intros h a v x Ha; unfold upd; destruct (Nat.eqb_spec x a) as [-> | Hne].
  - split; [intros _; exact Ha | intros _; discriminate].
  - reflexivity.
Qed.
(** ** Cells, footprints and well-formedness *)

(** The two cells of a node named [a]: the payload cell [a] and the link cell
    [S a]. *)
Definition cells (l: list nat) : list nat := flat_map (fun a => [a; S a]) l.

(** The footprint of a queue: the header's two cells plus every node's two
    cells. *)
Definition qcells (hdr: nat) (ns: list nat) : list nat := hdr :: S hdr :: cells ns.

Lemma in_cells: forall x l, In x (cells l) <-> exists a, In a l /\ (x = a \/ x = S a).
Proof.
  intros x l; unfold cells; rewrite in_flat_map; split.
  - intros (a & Ha & Hx); exists a; split; [assumption |].
    cbn in Hx; destruct Hx as [Heq | [Heq | []]]; [left | right]; congruence.
  - intros (a & Ha & Hx); exists a; split; [assumption |].
    cbn; destruct Hx as [-> | ->]; auto.
Qed.

Lemma cells_app: forall l1 l2, cells (l1 ++ l2) = cells l1 ++ cells l2.
Proof. intros; apply flat_map_app. Qed.

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

Definition hdf (l: list nat) (f: nat) : nat := match l with nil => f | a :: _ => a end.

Lemma hdf_app: forall l1 l2 f, hdf (l1 ++ l2) f = hdf l1 (hdf l2 f).
Proof. now intros [| a l1] l2 f. Qed.

(** [chain h ns vs fin]: the addresses [ns] carry the payloads [vs] and are
    linked in order, the last link holding [fin].  The terminator is a
    PARAMETER: that is what lets the rotation retarget the last link by
    [chain_split] + [chain_app] instead of a bespoke surgery lemma. *)
Fixpoint chain (h: Heap) (ns vs: list nat) (fin: nat) : Prop :=
  match ns, vs with
  | nil, nil => True
  | a :: ns', v :: vs' =>
      h a = Some v /\ h (S a) = Some (hdf ns' fin) /\ chain h ns' vs' fin
  | _, _ => False
  end.

Lemma chain_len: forall h ns vs f, chain h ns vs f -> length ns = length vs.
Proof.
  induction ns as [| a ns IH]; intros [| v vs] f Hc; cbn in *; try contradiction; auto.
  destruct Hc as (_ & _ & Hc); f_equal; eauto.
Qed.

Lemma chain_dom: forall h ns vs f x, chain h ns vs f -> In x (cells ns) -> h x <> None.
Proof.
  induction ns as [| a ns IH]; intros [| v vs] f x Hc Hin; cbn in *;
    try contradiction; try tauto.
  destruct Hc as (Ha & Hsa & Hc).
  destruct Hin as [Heq | [Heq | Hin]]; [subst; now rewrite Ha | subst; now rewrite Hsa |].
  eapply IH; eauto.
Qed.

Definition agree_out (m: list nat) (h h': Heap) : Prop :=
  forall x, ~ In x m -> h' x = h x.

Lemma chain_frame: forall h h' m ns vs f,
    chain h ns vs f ->
    agree_out m h h' ->
    (forall x, In x m -> ~ In x (cells ns)) ->
    chain h' ns vs f.
Proof.
  intros h h' m; induction ns as [| a ns IH]; intros [| v vs] f Hc Hag Hm;
    cbn in *; try contradiction; auto.
  destruct Hc as (Ha & Hsa & Hc).
  split; [| split].
  - rewrite Hag; auto. intro Hin; eapply Hm; eauto; cbn; auto.
  - rewrite Hag; auto. intro Hin; eapply Hm; eauto; cbn; auto.
  - eapply IH; eauto. intros x Hx Hin; eapply Hm; eauto; cbn; auto.
Qed.

Lemma chain_app: forall h ns1 vs1 ns2 vs2 f,
    chain h ns1 vs1 (hdf ns2 f) ->
    chain h ns2 vs2 f ->
    chain h (ns1 ++ ns2) (vs1 ++ vs2) f.
Proof.
  intros h; induction ns1 as [| a ns1 IH]; intros [| v vs1] ns2 vs2 f H1 H2;
    cbn in *; try contradiction; auto.
  destruct H1 as (Ha & Hsa & Hc).
  split; [assumption | split; [rewrite Hsa; now rewrite hdf_app | now apply IH]].
Qed.

Lemma chain_split: forall h ns1 vs1 ns2 vs2 f,
    length ns1 = length vs1 ->
    chain h (ns1 ++ ns2) (vs1 ++ vs2) f ->
    chain h ns1 vs1 (hdf ns2 f) /\ chain h ns2 vs2 f.
Proof.
  intros h; induction ns1 as [| a ns1 IH]; intros [| v vs1] ns2 vs2 f Hl Hc;
    cbn in *; try discriminate; auto.
  destruct Hc as (Ha & Hsa & Hc).
  apply IH in Hc as (H1 & H2); [| lia].
  split; [| assumption].
  split; [assumption | split; [rewrite Hsa; now rewrite hdf_app | assumption]].
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

    The arity of the conjunction is unchanged, so every destructuring pattern
    [(Hwf & Hhd & Htl & Hch & Hdom)] downstream still typechecks.  [QLang.v]
    and [Recurrence.v] are byte-identical to the recurrence experiment. *)
Definition qrep (hdr: nat) (ns vs: list nat) (h: Heap) : Prop :=
  qwf hdr ns
  /\ h (S hdr) = Some (hdf ns 0)
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
    qrep hdr ns vs h -> (hdf ns 0 = 0 <-> ns = []).
Proof.
  intros hdr ns vs h (Hwf & _ & _ & _ & _); destruct Hwf as (_ & H0 & _).
  destruct ns as [| a ns]; cbn; split; intro Hx; auto.
  - exfalso; apply H0; cbn; tauto.
  - discriminate.
Qed.

(** ** Rotation on the abstract lists *)

Definition rotl {A} (l: list A) : list A :=
  match l with nil => nil | x :: xs => xs ++ [x] end.

Lemma rotl_perm: forall {A} (l: list A), Permutation l (rotl l).
Proof.
  intros A [| x xs]; cbn; [constructor |].
  apply Permutation_cons_app; rewrite app_nil_r; apply Permutation_refl.
Qed.

Lemma qcells_rot: forall hdr a ns x,
    In x (qcells hdr (ns ++ [a])) <-> In x (qcells hdr (a :: ns)).
Proof.
  intros hdr a ns x; unfold qcells.
  assert (Hc: forall y, In y (cells (ns ++ [a])) <-> In y (cells (a :: ns))).
  { intro y; rewrite cells_app.
    replace (cells (a :: ns)) with (cells [a] ++ cells ns) by reflexivity.
    rewrite !in_app_iff; tauto. }
  split; intros [H | [H | H]].
  - now left.
  - now right; left.
  - right; right; now apply Hc.
  - now left.
  - now right; left.
  - right; right; now apply Hc.
Qed.

(** ** [find], restated at [nat].

    The reference proof [examples/Queue.v] states these over the abstract
    payload type [T] of the module [MeQ.ME] with a [RelDec] instance.  That
    module's [T] is an opaque parameter, so the lemmas cannot be instantiated;
    the statements and proof structure are reproduced here at [nat] with
    [Nat.eqb].  This is a REPRESENTATION-SPECIFIC ADAPTATION, recorded as such
    in the reuse report. *)

Fixpoint find (t: nat) (l: list nat) : option nat :=
  match l with
  | nil => None
  | h :: ts => if Nat.eqb h t then Some 0 else option_map S (find t ts)
  end.

Lemma unfold_find_hd: forall t h ts,
    find t (h :: ts) = (if Nat.eqb h t then Some 0 else option_map S (find t ts)).
Proof. reflexivity. Qed.

Lemma find_last_ex: forall nl ts, exists i0 : nat, find nl (ts ++ [nl]) = Some i0.
Proof.
  induction ts as [| a ts IH]; cbn.
  - exists 0; now rewrite Nat.eqb_refl.
  - destruct IH as (x & Hx); destruct (Nat.eqb_spec a nl) as [-> |].
    + now exists 0.
    + exists (S x); now rewrite Hx.
Qed.

Lemma find_app_l: forall nl ts n l, find nl ts = Some n -> find nl (ts ++ l) = Some n.
Proof.
  induction ts as [| a ts IH]; intros n l H; cbn in *; [discriminate |].
  destruct (Nat.eqb a nl); auto.
  destruct (find nl ts) eqn:Hf; cbn in *; [| discriminate].
  erewrite IH; eauto.
Qed.

Lemma find_in: forall nl l n, find nl l = Some n -> In nl l.
Proof.
  induction l as [| a l IH]; intros n H; cbn in *; [discriminate |].
  destruct (Nat.eqb_spec a nl) as [-> |]; auto.
  destruct (find nl l) eqn:Hf; cbn in *; [| discriminate]; eauto.
Qed.

Lemma find_nonnil: forall nl l n, find nl l = Some n -> l <> [].
Proof. intros nl [| a l] n H; cbn in *; [discriminate | congruence]. Qed.

(** The position of [nl] after one rotation: this is the natural rank of the
    reference proof, restated here so that the temporal file never re-derives
    it.  If [nl] is at position [S d] it moves to [d]; if it is at position [0]
    it is popped now. *)
Lemma find_rotl: forall nl v vs d,
    find nl (v :: vs) = Some (S d) -> find nl (rotl (v :: vs)) = Some d.
Proof.
  intros nl v vs d H; cbn in *.
  destruct (Nat.eqb_spec v nl) as [-> | Hne]; [discriminate |].
  destruct (find nl vs) as [m |] eqn:Hf; cbn in *; [| discriminate].
  assert (m = d) by congruence; subst.
  now apply find_app_l.
Qed.

Lemma find_rotl_pres: forall nl v vs d,
    find nl (v :: vs) = Some d -> exists d', find nl (rotl (v :: vs)) = Some d'.
Proof.
  intros nl v vs [| d] H.
  - cbn in H; destruct (Nat.eqb_spec v nl) as [-> |]; [| destruct (find nl vs); cbn in H; congruence].
    cbn; apply find_last_ex.
  - eexists; eapply find_rotl; eauto.
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
    hdisj (qres hdr a (hdf ns 0) h) (qnode a h)
    /\ heq (upd h (S hdr) (hdf ns 0)) (hunion (qres hdr a (hdf ns 0) h) (qnode a h))
    /\ (qrep hdr ns vs (qres hdr a (hdf ns 0) h)
        /\ qex hdr ns (qres hdr a (hdf ns 0) h))
    /\ nodeat a v (hdf ns 0) (qnode a h).
Proof.
  intros hdr a ns v vs h Hq Hex.
  pose proof Hq as (Hwf & Hhd & Htl & Hch & Hdom0).
  assert (Hdom: forall x, h x <> None <-> In x (qcells hdr (a :: ns)))
    by (intro x; split; [apply Hex | apply (proj2 Hdom0)]).
  destruct Hch as (Ha & Hsa & Hch).
  pose proof (qwf_neqs _ _ _ Hwf) as (Hha & Hsha & Hhsa & Hshsa & Hhshdr).
  pose proof (qwf_node_cells _ _ _ Hwf) as (Hanc & Hsanc).
  pose proof (qwf_tail _ _ _ Hwf) as Hwfns.
  pose proof (qwf_shdr_cells _ _ Hwfns) as Hshdrnc.
  assert (Hhdrdom: h hdr <> None) by (apply Hdom; apply in_eq).
  assert (Ea: nodeb a a = true) by (apply nodeb_true; now left).
  assert (Esa: nodeb a (S a) = true) by (apply nodeb_true; now right).
  assert (Ehdr: nodeb a hdr = false) by (apply nodeb_false; split; congruence).
  assert (Eshdr: nodeb a (S hdr) = false) by (apply nodeb_false; split; congruence).
  assert (Hqshdr: qres hdr a (hdf ns 0) h (S hdr) = Some (hdf ns 0))
    by (unfold qres; rewrite Eshdr; apply upd_eq).
  assert (Hqhdr: qres hdr a (hdf ns 0) h hdr = h hdr)
    by (unfold qres; rewrite Ehdr; rewrite upd_neq by congruence; reflexivity).
  split; [| split; [| split]].
  - intro x; unfold qres, qnode; destruct (nodeb a x); [now left | now right].
  - intro x; unfold qres, qnode, hunion; destruct (nodeb a x) eqn:E.
    + apply nodeb_true in E as [-> | ->]; rewrite upd_neq by congruence; reflexivity.
    + destruct (upd h (S hdr) (hdf ns 0) x); reflexivity.
  - (* the remaining queue is a genuine representation; when the detach has
       emptied it, the tail pointer is stale and [tailok] does not constrain it *)
    assert (Hres: forall x, qres hdr a (hdf ns 0) h x <> None
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
    assert (Hresnull: qres hdr a (hdf ns 0) h 0 = None).
    { destruct (qres hdr a (hdf ns 0) h 0) eqn:E0; [| reflexivity].
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
      /\ heq (upd h (S hdr) (hdf ns 0)) (hunion hq hn)
      /\ qrep hdr ns vs hq
      /\ nodeat a v (hdf ns 0) hn.
Proof.
  intros hdr a ns v vs h H Hex.
  apply (rot_detach_split hdr a ns v vs h H) in Hex as (H1 & H2 & (H3 & _) & H4).
  eauto 6.
Qed.

Lemma hdf_ne: forall l f g, l <> [] -> hdf l f = hdf l g.
Proof. now intros [| a l] f g H. Qed.

Lemma cells_mono_app: forall x l1 l2, In x (cells l1) -> In x (cells (l1 ++ l2)).
Proof. intros x l1 l2 H; rewrite cells_app, in_app_iff; now left. Qed.

Lemma cells_mono_cons: forall x b l, In x (cells l) -> In x (cells (b :: l)).
Proof. intros x b l H; cbn; auto. Qed.

(** ** The rotation theorem.

    One completed rotation turns the represented queue [a :: ns] / [v :: vs]
    into [ns ++ [a]] / [vs ++ [v]] -- exactly the abstract pop-and-push -- and
    touches no cell outside the queue's own footprint. *)
Theorem rot_heap_spec: forall hdr a ns v vs h,
    qrep hdr (a :: ns) (v :: vs) h ->
    qrep hdr (ns ++ [a]) (vs ++ [v]) (rot_heap hdr a (hdf ns 0) (zof hdr ns) h)
    /\ (forall x, rot_heap hdr a (hdf ns 0) (zof hdr ns) h x <> None <-> h x <> None).
Proof.
  intros hdr a ns v vs h Hq.
  pose proof Hq as (Hwf & Hhd & Htl & Hch & Hdom).
  destruct Hch as (Ha & Hsa & Hch).
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
    destruct vs as [| v1 vs1]; [| cbn in Hch; contradiction].
    cbn in Hsa |- *.
    assert (Hdom': forall x, rot_heap hdr a 0 hdr h x <> None <-> h x <> None)
      by (apply rot_heap_dom; assumption).
    split; [| exact Hdom'].
    split; [exact Hwf | split; [| split; [| split]]].
    + rewrite (rot_heap_sz hdr a 0 hdr h); [reflexivity | congruence | congruence].
    + cbn; apply rot_heap_hdr.
    + cbn; split; [| split; [| exact I]].
      * rewrite rot_heap_other by (first [congruence | lia]); exact Ha.
      * apply rot_heap_sa; congruence.
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
    cbn in Hch0, Hchz; destruct Hchz as (Hzv & Hszv & _).
    assert (Hszdom: h (S zz) <> None) by (rewrite Hszv; discriminate).
    assert (Hdom': forall x, rot_heap hdr a (hdf ns 0) zz h x <> None <-> h x <> None)
      by (apply rot_heap_dom; assumption).
    rewrite Hz.
    split; [| exact Hdom'].
    split; [| split; [| split; [| split]]].
    + eapply qwf_perm; [| exact Hwf].
      change (Permutation (a :: ns) (ns ++ [a])); apply (rotl_perm (a :: ns)).
    + rewrite rot_heap_shdr by congruence.
      rewrite hdf_app; cbn; f_equal; symmetry; now apply hdf_ne.
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
        -- cbn; split; [| split; [| exact I]].
           ++ rewrite rot_heap_other by (first [congruence | lia]); exact Hzv.
           ++ apply rot_heap_sz; congruence.
      * cbn; split; [| split; [| exact I]].
        -- rewrite rot_heap_other by (first [congruence | lia]); exact Ha.
        -- apply rot_heap_sa; congruence.
    + split.
      * destruct (rot_heap hdr a (hdf ns 0) zz h 0) eqn:E0; [| reflexivity].
        exfalso; assert (Hc: h 0 <> None) by (apply Hdom'; congruence).
        apply Hc; exact (proj1 Hdom).
      * intro x; rewrite Hdom'; intro Hx; apply (proj2 Hdom).
        apply qcells_rot; exact Hx.
Qed.

(** ** Two facts the language layer needs about the rotation's footprint. *)

Lemma upd_mono: forall h a v x, h x <> None -> upd h a v x <> None.
Proof. intros h a v x H; unfold upd; destruct (Nat.eqb x a); [discriminate | exact H]. Qed.

Lemma last_in: forall (l: list nat) d, l <> [] -> In (last l d) l.
Proof.
  intros l d H; destruct (exists_last H) as (l' & x & ->).
  rewrite last_last, in_app_iff; right; apply in_eq.
Qed.

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
    (if Nat.eqb (hdf ns 0) 0 then hdr else last (a :: ns) 0) = zof hdr ns.
Proof.
  intros hdr a ns (Hnd & H0 & Hov); destruct ns as [| b ns1]; [reflexivity |].
  cbn [hdf].
  destruct (Nat.eqb_spec b 0) as [-> | Hb]; [exfalso; apply H0; cbn; tauto |].
  reflexivity.
Qed.

Lemma find_head: forall nl v vs, find nl (v :: vs) = Some 0 -> v = nl.
Proof.
  intros nl v vs H; cbn in H.
  destruct (Nat.eqb_spec v nl) as [-> | Hne]; [reflexivity |].
  destruct (find nl vs); cbn in H; discriminate.
Qed.

Lemma rotl_cons: forall (v: nat) vs, rotl (v :: vs) = vs ++ [v].
Proof. reflexivity. Qed.
