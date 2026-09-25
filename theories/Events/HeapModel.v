(** * The concrete heap model.

    Representation: [nat -> option nat].  Equivalence: pointwise equality.
    Composition: union, defined exactly on disjoint pairs.  This is the
    "justified map representation / equivalence" the PCM interface asks for; it
    is not an association list under list equality, for which commutativity is
    false.

    This module owns the *pure* heap: its PCM instance, its points-to and
    framing laws, the single update primitive [upd], the finite-block algebra
    used by allocation, and the stride-two node geometry shared by the queue
    and the allocator.  It is deliberately distinct from [ICTree.Events.Heap],
    which only builds [heapE] triggers.

    Heap equality stays POINTWISE ([heq]).  Nothing here converts it to
    function equality or assumes extensionality. *)

From Stdlib Require Import
  Basics
  Arith.PeanoNat
  Lia
  List
  Relations
  Sorting.Permutation.

From TICL Require Export Utils.Pcm.

Import ListNotations.
Local Open Scope pcm_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(** ** Carrier and primitive operations *)
Definition Heap := nat -> option nat.

Definition hemp : Heap := fun _ => None.
Definition heq (h1 h2: Heap) : Prop := forall a, h1 a = h2 a.
Definition hdisj (h1 h2: Heap) : Prop := forall a, h1 a = None \/ h2 a = None.
Definition hunion (h1 h2: Heap) : Heap :=
  fun a => match h1 a with Some v => Some v | None => h2 a end.

Definition hsingle (a v: nat) : Heap :=
  fun b => if Nat.eq_dec a b then Some v else None.
Definition hfree (a: nat) (h: Heap) : Heap :=
  fun b => if Nat.eq_dec a b then None else h b.

(** The single update primitive.  Its decision procedure is [Nat.eqb] on the
    LOOKED-UP address, which is the computational convention every allocator
    and queue computation already uses. *)
Definition upd (h : Heap) (a v : nat) : Heap :=
  fun x => if Nat.eqb x a then Some v else h x.

(** The empty heap has no allocated cell. *)
Lemma hemp_dom: forall x, hemp x <> None -> False.
Proof. intros x H; apply H; reflexivity. Qed.

(** Pointwise contents of a finite collection of heap cells. *)
Definition cellsat (W: list (nat * nat)) (h: Heap) : Prop :=
  Forall (fun p => h (fst p) = Some (snd p)) W.

Lemma cellsat_heq: forall W h1 h2, heq h1 h2 -> cellsat W h1 -> cellsat W h2.
Proof.
  intros W k1 k2 Heq H; unfold cellsat in *.
  rewrite Forall_forall in *; intros p Hp; rewrite <- Heq; now apply H.
Qed.

Lemma cellsat_agree: forall W h h',
    (forall p, In p W -> h' (fst p) = h (fst p)) -> cellsat W h -> cellsat W h'.
Proof.
  intros W h h' Hag H; unfold cellsat in *.
  rewrite Forall_forall in *; intros p Hp; rewrite Hag by exact Hp; now apply H.
Qed.

Ltac hcase a := unfold hunion, hfree, hsingle, hemp in *;
                intros; repeat (destruct (Nat.eq_dec _ _)); subst; auto.

Lemma hdisj_none: forall h1 h2 a v, hdisj h1 h2 -> h1 a = Some v -> h2 a = None.
Proof. intros h1 h2 a v Hd Hs; destruct (Hd a) as [Hn | Hn]; congruence. Qed.

(** ** The algebra of [upd].

    Elementary lookup facts about the primitive defined above.  Stated with
    explicit binders: they are applied positionally. *)

Lemma upd_unfold: forall h a v x, upd h a v x = if Nat.eqb x a then Some v else h x.
Proof. reflexivity. Qed.

Lemma upd_eq: forall h a v, upd h a v a = Some v.
Proof. intros; unfold upd; now rewrite Nat.eqb_refl. Qed.

Lemma upd_neq: forall h a v x, x <> a -> upd h a v x = h x.
Proof. intros; unfold upd; now apply Nat.eqb_neq in H as ->. Qed.

Lemma upd_mono: forall h a v x, h x <> None -> upd h a v x <> None.
Proof. intros h a v x H; unfold upd; destruct (Nat.eqb x a); [discriminate | exact H]. Qed.

Lemma upd_dom: forall h a v x, h a <> None -> (upd h a v x <> None <-> h x <> None).
Proof.
  intros h a v x Ha; unfold upd; destruct (Nat.eqb_spec x a) as [-> | Hne].
  - split; [intros _; exact Ha | intros _; discriminate].
  - reflexivity.
Qed.

Lemma upd_lookup_agree: forall h f a v x, h x = f x -> upd h a v x = upd f a v x.
Proof.
  intros h f a v x H; destruct (Nat.eq_dec x a) as [-> | Hne].
  - now rewrite !upd_eq.
  - now rewrite !upd_neq by exact Hne.
Qed.

Lemma upd_heq: forall h k a v, heq h k -> heq (upd h a v) (upd k a v).
Proof.
  intros h k a v H x; unfold upd; destruct (Nat.eqb x a); [reflexivity | apply H].
Qed.

(** Elementary lookup consequences of [hunion]/[hdisj].  These read a single
    address out of a union; the monoid laws below are stated pointwise on top
    of them. *)

Lemma hunion_some: forall h f x v, h x = Some v -> hunion h f x = Some v.
Proof. intros h f x v H; unfold hunion; now rewrite H. Qed.

Lemma hunion_eq: forall h f x, h x <> None -> hunion h f x = h x.
Proof.
  intros h f x H; destruct (h x) as [v |] eqn:E; [| congruence].
  now apply hunion_some.
Qed.

Lemma hunion_none: forall h f x, h x = None -> hunion h f x = f x.
Proof. intros h f x H; unfold hunion; now rewrite H. Qed.

Lemma hunion_dom: forall h f x, h x <> None -> hunion h f x <> None.
Proof. intros h f x H; now rewrite hunion_eq. Qed.

Lemma hunion_null: forall h f, h 0 = None -> f 0 = None -> hunion h f 0 = None.
Proof. intros h f Hh Hf; unfold hunion; now rewrite Hh. Qed.

Lemma hdisj_union: forall h1 h2 f,
    hdisj h1 h2 -> hdisj h1 f -> hdisj h1 (hunion h2 f).
Proof.
  intros h1 h2 f H12 H1f x.
  destruct (h1 x) eqn:E1; [| now left].
  right; unfold hunion.
  destruct (H12 x) as [C | E2]; [congruence |]; rewrite E2.
  destruct (H1f x) as [C | Ef]; [congruence | exact Ef].
Qed.

(** Every law is proved as a standalone lemma first, so that the instance is a
    list of [exact]s and its field order cannot silently drift. *)
Lemma heq_refl: forall a, heq a a.
Proof. intros a x; reflexivity. Qed.

Lemma heq_sym: forall a b, heq a b -> heq b a.
Proof. intros a b Hab x; now rewrite Hab. Qed.

Lemma heq_trans: forall a b c, heq a b -> heq b c -> heq a c.
Proof. intros a b c Hab Hbc x; now rewrite Hab, Hbc. Qed.

Lemma hdisj_resp: forall a a' b b', heq a a' -> heq b b' -> hdisj a b -> hdisj a' b'.
Proof. intros a a' b b' Ha Hb Hd x; rewrite <- Ha, <- Hb; apply Hd. Qed.

Lemma hunion_resp: forall a a' b b', heq a a' -> heq b b' -> heq (hunion a b) (hunion a' b').
Proof. intros a a' b b' Ha Hb x; unfold hunion; rewrite Ha, Hb; reflexivity. Qed.

Lemma hdisj_sym: forall a b, hdisj a b -> hdisj b a.
Proof. intros a b Hd x; destruct (Hd x); auto. Qed.

Lemma hunion_comm: forall a b, hdisj a b -> heq (hunion a b) (hunion b a).
Proof.
  intros a b Hd x; unfold hunion; destruct (Hd x) as [Hx | Hx]; rewrite Hx.
  - destruct (b x); reflexivity.
  - destruct (a x); reflexivity.
Qed.

Lemma hdisj_hemp: forall a, hdisj hemp a.
Proof. intros a x; left; reflexivity. Qed.

Lemma hunion_hemp: forall a, heq (hunion hemp a) a.
Proof. intros a x; reflexivity. Qed.

Lemma hdisj_assocL: forall a b c, hdisj b c -> hdisj a (hunion b c) -> hdisj a b.
Proof.
  intros a b c Hbc Ha x; specialize (Ha x); unfold hunion in Ha.
  destruct (b x) eqn:Hb; auto.
Qed.

Lemma hdisj_assocR: forall a b c, hdisj b c -> hdisj a (hunion b c) -> hdisj (hunion a b) c.
Proof.
  intros a b c Hbc Ha x; specialize (Ha x); specialize (Hbc x); unfold hunion in *.
  destruct (a x) eqn:Ha'; destruct (b x) eqn:Hb'; destruct (c x) eqn:Hc';
    intuition (try discriminate); auto.
Qed.

Lemma hdisj_assocI: forall a b c,
    hdisj b c -> hdisj a b -> hdisj (hunion a b) c -> hdisj a (hunion b c).
Proof.
  intros a b c Hbc Hab Habc x.
  specialize (Hbc x); specialize (Hab x); specialize (Habc x); unfold hunion in *.
  destruct (a x) eqn:Ha'; destruct (b x) eqn:Hb'; destruct (c x) eqn:Hc';
    intuition (try discriminate); auto.
Qed.

Lemma hunion_assoc: forall a b c,
    hdisj b c -> hdisj a (hunion b c) -> heq (hunion a (hunion b c)) (hunion (hunion a b) c).
Proof. intros a b c _ _ x; unfold hunion; destruct (a x); reflexivity. Qed.

#[global] Instance HeapPCM : PCM Heap.
Proof.
  refine {| peq := heq; pdef := hdisj; pop := hunion; pemp := hemp |}.
  - exact heq_refl.
  - exact heq_sym.
  - exact heq_trans.
  - exact hdisj_resp.
  - exact hunion_resp.
  - exact hdisj_sym.
  - exact hunion_comm.
  - exact hdisj_hemp.
  - exact hunion_hemp.
  - exact hdisj_assocL.
  - exact hdisj_assocR.
  - exact hdisj_assocI.
  - exact hunion_assoc.
Defined.

(** Heaps are cancellative -- recorded to show the class is not weakened by
    leaving cancellativity out. *)
Lemma HeapCancellative: Cancellative Heap.
Proof.
  intros a b c Hab Hac Heq x; cbn in *.
  unfold heq, hunion, hdisj in *.
  specialize (Heq x); specialize (Hab x); specialize (Hac x).
  destruct (a x) eqn:Ha; auto.
  destruct Hab as [? | Hb]; [congruence |].
  destruct Hac as [? | Hc]; [congruence |].
  congruence.
Qed.

(** ** Points-to, and the separation it buys.

    [pto a v] is an assertion about the *owned* resource.  [CNow] is
    tree-blind, so this can never be a TICL base predicate on its own: it is a
    predicate on the resource, lifted into the temporal layer only through an
    owned projection. *)
Definition pto (a v: nat) : assn Heap := fun h => heq h (hsingle a v).

Lemma pto_proper: forall a v, AProper (pto a v).
Proof. intros a v h1 h2 Heq Hp x; rewrite <- Heq; apply Hp. Qed.

Lemma pto_lookup: forall a v h, pto a v h -> h a = Some v.
Proof. intros a v h Hp; rewrite Hp; hcase a; congruence. Qed.

(** Two points-to on the same address cannot be separated: the hallmark
    consequence of a disjointness-based PCM. *)
Theorem pto_sep_same_false: forall a v v' h, ~ (pto a v ⋆ pto a v')%pcm h.
Proof.
  intros a v v' h (h1 & h2 & Hd & Heq & H1 & H2).
  apply pto_lookup in H1; apply pto_lookup in H2.
  destruct (Hd a); congruence.
Qed.

(** Distinct addresses do separate. *)
Theorem pto_sep_distinct: forall a b v v',
    a <> b -> (pto a v ⋆ pto b v')%pcm (hunion (hsingle a v) (hsingle b v')).
Proof.
  intros a b v v' Hab.
  exists (hsingle a v), (hsingle b v').
  split; [| split; [| split]].
  - intro x; unfold hsingle; destruct (Nat.eq_dec a x); destruct (Nat.eq_dec b x);
      subst; auto.
    exfalso; auto.
  - intro x; reflexivity.
  - intro x; reflexivity.
  - intro x; reflexivity.
Qed.

(** ** Safe-access locality on the concrete heap.

    Each of the three laws is stated with the footprint hypothesis it needs. *)

(** A read inside the owned footprint returns the owned value, under every
    compatible frame. *)
Theorem read_local: forall h f a v,
    hdisj h f -> h a = Some v -> hunion h f a = Some v.
Proof. intros h f a v Hd Ha; unfold hunion; now rewrite Ha. Qed.

(** A write inside the owned footprint keeps the frame disjoint ... *)
Theorem write_local_disj: forall h f a v v0,
    hdisj h f -> h a = Some v0 -> hdisj (upd h a v) f.
Proof.
  intros h f a v v0 Hd Ha x; destruct (Nat.eq_dec x a) as [-> | Hne].
  - right; eapply hdisj_none; eauto.
  - rewrite upd_neq by exact Hne; apply Hd.
Qed.

(** ... and commutes with framing. *)
Theorem write_local_frame: forall h f a v,
    heq (upd (hunion h f) a v) (hunion (upd h a v) f).
Proof.
  intros h f a v x; destruct (Nat.eq_dec x a) as [-> | Hne].
  - rewrite !upd_eq; unfold hunion; now rewrite upd_eq.
  - rewrite !upd_neq by exact Hne; unfold hunion; now rewrite upd_neq by exact Hne.
Qed.

(** A free inside the owned footprint keeps the frame disjoint ... *)
Theorem free_local_disj: forall h f a,
    hdisj h f -> hdisj (hfree a h) f.
Proof. intros h f a Hd x; unfold hfree; destruct (Nat.eq_dec a x); auto. Qed.

(** ... and commutes with framing, provided the address is owned. *)
Theorem free_local_frame: forall h f a v0,
    hdisj h f -> h a = Some v0 ->
    heq (hfree a (hunion h f)) (hunion (hfree a h) f).
Proof.
  intros h f a v0 Hd Ha x; unfold hfree, hunion; destruct (Nat.eq_dec a x); auto.
  subst; erewrite hdisj_none; eauto.
Qed.

(** Freeing an absent address leaves the heap pointwise unchanged. *)
Lemma hfree_absent_noop (h : Heap) a :
  h a = None -> heq (hfree a h) h.
Proof.
  intros Ha x; unfold hfree; destruct (Nat.eq_dec a x) as [<- | _]; auto.
Qed.

(** ** Finite blocks over the unrestricted function heap.
    Bounds are proof witnesses only; allocation searches in its handler.
    Fresh ownership preserves the old resource, not literal frame-stable bases. *)

Definition heap_bounded (bound : nat) (h : Heap) : Prop :=
  forall x, Nat.le bound x -> h x = None.
Definition heap_finite (h : Heap) : Prop :=
  exists bound, heap_bounded bound h.
Definition hblock (base size : nat) : Heap :=
  fun x => if andb (Nat.leb base x) (Nat.ltb x (base + size))
           then Some 0 else None.
Definition block_free (h : Heap) (base size : nat) : Prop :=
  forall offset, Nat.lt offset size -> h (base + offset) = None.
Definition block_pto (base size : nat) : Heap -> Prop :=
  fun h => heq h (hblock base size).

Lemma hblock_in base size offset :
  Nat.lt offset size -> hblock base size (base + offset) = Some 0.
Proof.
  intro H; unfold hblock.
  assert (L : Nat.leb base (base + offset) = true)
    by (apply Nat.leb_le; lia).
  assert (R : Nat.ltb (base + offset) (base + size) = true)
    by (apply Nat.ltb_lt; lia).
  now rewrite L, R.
Qed.

Lemma hblock_out base size x :
  (Nat.lt x base \/ Nat.le (base + size) x) ->
  hblock base size x = None.
Proof.
  intro H; unfold hblock.
  destruct (Nat.leb_spec0 base x); destruct (Nat.ltb_spec0 x (base + size));
    cbn; try reflexivity; lia.
Qed.

Lemma block_free_disjoint h base size :
  block_free h base size <-> hdisj (hblock base size) h.
Proof.
  split.
  - intros H x.
    destruct (Nat.le_gt_cases base x) as [L | L];
      [destruct (Nat.lt_ge_cases x (base + size)) as [R | R] |].
    + right; replace x with (base + (x - base)) by lia; apply H; lia.
    + left; apply hblock_out; auto.
    + left; apply hblock_out; auto.
  - intros H offset O; specialize (H (base + offset)).
    rewrite (hblock_in base size offset O) in H; destruct H; congruence.
Qed.

Lemma heap_finite_hemp : heap_finite hemp.
Proof. exists 0; intros x H; reflexivity. Qed.

Lemma heap_finite_hblock base size : heap_finite (hblock base size).
Proof.
  exists (base + size); intros x H; apply hblock_out; auto.
Qed.

Lemma heap_finite_hunion h f :
  heap_finite h -> heap_finite f -> heap_finite (hunion h f).
Proof.
  intros [B HB] [C HC]; exists (Nat.max B C); intros x H.
  unfold hunion; rewrite HB, HC; try reflexivity; lia.
Qed.

Lemma heap_finite_upd h a v : heap_finite h -> heap_finite (upd h a v).
Proof.
  intros [B Bound]; exists (Nat.max B (S a)); intros x X.
  unfold upd; destruct (Nat.eqb_spec x a); [lia | apply Bound; lia].
Qed.

Lemma heap_bounded_block_free bound h base size :
  heap_bounded bound h -> Nat.le bound base -> block_free h base size.
Proof. intros H B offset O; apply H; lia. Qed.

Lemma allocated_block_sep base size h (P : Heap -> Prop) :
  block_free h base size -> P h ->
  asep (block_pto base size) P (hunion (hblock base size) h).
Proof.
  intros F H; exists (hblock base size), h.
  split; [apply block_free_disjoint; exact F |].
  split; [apply heq_refl |].
  split; [apply heq_refl | exact H].
Qed.

(** An owned block cannot be separated from a points-to on one of its cells. *)
Lemma block_pto_overlap_false base size a v h :
  base <= a < base + size ->
  ~ asep (block_pto base size) (pto a v) h.
Proof.
  intros Ha (b & p & D & _ & B & P).
  assert (Hb : b a = Some 0).
  { rewrite (B a); replace a with (base + (a - base)) by lia; apply hblock_in; lia. }
  apply pto_lookup in P; destruct (D a); congruence.
Qed.

(** The immutable snapshot is searched without fuel or heap instrumentation. *)
Fixpoint block_freeb (h : Heap) (base size : nat) : bool :=
  match size with
  | 0 => true
  | S rest =>
      match h base with
      | None => block_freeb h (S base) rest
      | Some _ => false
      end
  end.

Lemma block_freeb_spec h base size :
  block_freeb h base size = true <-> block_free h base size.
Proof.
  revert base; induction size as [|size IH]; intro base.
  - split; [intros _ offset O; lia | reflexivity].
  - cbn [block_freeb]; destruct (h base) as [v|] eqn:E.
    + split; [discriminate | intro F].
      specialize (F 0 ltac:(lia)); rewrite Nat.add_0_r, E in F; discriminate.
    + rewrite IH; split.
      * intros F [|offset] O.
        -- now rewrite Nat.add_0_r.
        -- replace (base + S offset)%nat with (S base + offset)%nat by lia; apply F; lia.
      * intros F offset O.
        replace (S base + offset)%nat with (base + S offset)%nat by lia; apply F; lia.
Qed.

(** ** Stride-two node geometry.

    A node named [a] owns exactly two cells: [a] and [S a].  Stride two, null
    terminator zero, and low-to-high initialization order are fixed; this is a
    concrete layout, not a configurable memory-layout framework.  Both the
    queue representation and the allocator page share it. *)

(** The two cells of a node named [a]: the payload cell [a] and the link cell
    [S a]. *)
Definition cells (l: list nat) : list nat := flat_map (fun a => [a; S a]) l.

Lemma in_cells: forall x l, In x (cells l) <-> exists a, In a l /\ (x = a \/ x = S a).
Proof.
  intros x l; unfold cells; rewrite in_flat_map; split.
  - intros (a & Ha & Hx); exists a; split; [assumption |].
    cbn in Hx; destruct Hx as [Heq | [Heq | []]]; [left | right]; congruence.
  - intros (a & Ha & Hx); exists a; split; [assumption |].
    cbn; destruct Hx as [-> | ->]; auto.
Qed.

Fixpoint node_addrs (first count : nat) : list nat :=
  match count with
  | 0 => []
  | S rest => first :: node_addrs (first + 2) rest
  end.

Lemma node_addrs_in first count x :
  In x (node_addrs first count) <->
    exists j, Nat.lt j count /\ x = first + 2*j.
Proof.
  revert first x; induction count as [| count IH]; intros first x.
  - cbn [node_addrs]; split; [contradiction | intros (j & Hj & _); lia].
  - cbn [node_addrs In]; rewrite IH; split.
    + intros [Hx | (j & Hj & Hx)].
      * exists 0; split; lia.
      * exists (S j); split; lia.
    + intros (j & Hj & Hx); destruct j as [| j].
      * left; lia.
      * right; exists j; split; lia.
Qed.

Lemma node_addrs_length first count : length (node_addrs first count) = count.
Proof.
  revert first; induction count as [| count IH]; intro first;
    cbn [node_addrs length]; [reflexivity | now rewrite IH].
Qed.

Lemma node_addrs_nodup first count : NoDup (node_addrs first count).
Proof.
  revert first; induction count as [| count IH]; intro first; cbn [node_addrs].
  - constructor.
  - constructor; [| apply IH].
    intro Hin; apply node_addrs_in in Hin as (j & Hj & Hx); lia.
Qed.

Lemma node_cells_range first count x :
  In x (cells (node_addrs first count)) <->
    Nat.le first x /\ Nat.lt x (first + 2 * count).
Proof.
  revert first x; induction count as [| count IH]; intros first x.
  - cbn [node_addrs cells]; split; [contradiction | lia].
  - change ((first = x \/ S first = x \/
      In x (cells (node_addrs (first + 2) count))) <->
      Nat.le first x /\ Nat.lt x (first + 2 * S count)).
    rewrite IH; split.
    + intros [Hx | [Hx | Hx]]; lia.
    + intros [Hlo Hhi].
      destruct (Nat.eq_dec first x) as [Hx | Hx]; [now left |].
      destruct (Nat.eq_dec (S first) x) as [Hsx | Hsx]; [now right; left |].
      right; right; split; lia.
Qed.

Lemma node_addrs_link_payload_disjoint first count a b :
  In a (node_addrs first count) -> In b (node_addrs first count) ->
  a <> S b.
Proof.
  intros Ha Hb.
  apply node_addrs_in in Ha as (i & Hi & Ha).
  apply node_addrs_in in Hb as (j & Hj & Hb).
  lia.
Qed.

Lemma node_addrs_cells_nodup first count :
  NoDup (cells (node_addrs first count)).
Proof.
  revert first; induction count as [| count IH]; intro first.
  - constructor.
  - change (NoDup (first :: S first :: cells (node_addrs (first + 2) count))).
    constructor.
    + intros [H | H]; [lia | apply node_cells_range in H; lia].
    + constructor.
      * intro H; apply node_cells_range in H; lia.
      * apply IH.
Qed.

(** ** Pure link initialization over a stride-two node list.

    Links run low to high; the last node's link is the null terminator zero.
    [count = 0] leaves the heap unchanged.  Without a checked-write premise the
    pure initializer may EXTEND a domain; the exact domain law below makes that
    explicit.  Checked source writes still require allocated cells. *)

Fixpoint init_links_heap (first count : nat) (h : Heap) : Heap :=
  match count with
  | 0 => h
  | S rest =>
      init_links_heap (first + 2) rest
        (upd h first (match rest with 0 => 0 | S _ => first + 2 end))
  end.

Lemma init_links_heap_lookup_agree first count h f x :
  h x = f x -> init_links_heap first count h x = init_links_heap first count f x.
Proof.
  revert first h f; induction count as [| count IH]; intros first h f H.
  - exact H.
  - cbn [init_links_heap]; apply IH, upd_lookup_agree, H.
Qed.

Lemma init_links_heap_frame first count h x :
  ~ In x (node_addrs first count) -> init_links_heap first count h x = h x.
Proof.
  revert first h; induction count as [| count IH]; intros first h Hout.
  - reflexivity.
  - cbn [init_links_heap]; rewrite IH.
    + apply upd_neq; intro H; apply Hout; cbn [node_addrs]; now left.
    + intro Hin; apply Hout; cbn [node_addrs]; now right.
Qed.

Lemma init_links_heap_out first count h x :
  (Nat.lt x first \/ Nat.le (first + 2 * count) x) ->
  init_links_heap first count h x = h x.
Proof.
  intro Hout; apply init_links_heap_frame.
  intro Hin; apply node_addrs_in in Hin as (j & Hj & Hx); lia.
Qed.

Lemma init_links_heap_payload first count h b :
  In b (node_addrs first count) -> init_links_heap first count h (S b) = h (S b).
Proof.
  intro Hb; apply init_links_heap_frame; intro Hin.
  exact (node_addrs_link_payload_disjoint first count (S b) b Hin Hb eq_refl).
Qed.

Lemma init_links_heap_dom first count h x :
  init_links_heap first count h x <> None <->
    In x (node_addrs first count) \/ h x <> None.
Proof.
  revert first h x; induction count as [| count IH]; intros first h x.
  - cbn [init_links_heap node_addrs In]; tauto.
  - cbn [init_links_heap node_addrs In]; rewrite IH; unfold upd.
    destruct (Nat.eqb_spec x first) as [Hx | Hne].
    + subst x; split; intro H.
      * left; now left.
      * right; discriminate.
    + intuition congruence.
Qed.

(** A list-suffix lookup is independent of the incoming heap.  In particular
    it supplies exactly the head/tail equations a free-list ownership proof
    needs, without defining that ownership predicate here. *)
Lemma init_links_heap_link first count h prefix b rest :
  node_addrs first count = prefix ++ b :: rest ->
  init_links_heap first count h b = Some (hd 0 rest).
Proof.
  revert first h prefix b rest; induction count as [| count IH];
    intros first h prefix b rest Hnodes.
  - destruct prefix; discriminate.
  - destruct prefix as [| a prefix].
    + cbn [node_addrs app] in Hnodes.
      injection Hnodes as Hb Hrest; subst b; subst rest.
      cbn [init_links_heap].
      rewrite init_links_heap_out by (left; lia).
      rewrite upd_eq; destruct count; reflexivity.
    + cbn [node_addrs app] in Hnodes.
      injection Hnodes as Ha Htail.
      cbn [init_links_heap]; eapply IH; exact Htail.
Qed.

Lemma init_links_heap_link_index first count h j :
  Nat.lt j count ->
  init_links_heap first count h (first + 2 * j) =
    Some (if Nat.ltb (S j) count then first + 2 * S j else 0).
Proof.
  revert first h j; induction count as [| count IH]; intros first h j Hj.
  - lia.
  - destruct j as [| j].
    + replace (first + 2 * 0) with first by lia.
      cbn [init_links_heap].
      rewrite init_links_heap_out by (left; lia).
      rewrite upd_eq; destruct count; reflexivity.
    + cbn [init_links_heap].
      replace (first + 2 * S j) with (first + 2 + 2 * j) by lia.
      rewrite IH by lia.
      change (Some (if Nat.ltb (S j) count then first + 2 + 2 * S j else 0) =
        Some (if Nat.ltb (S j) count then first + 2 * S (S j) else 0)).
      destruct (Nat.ltb (S j) count); f_equal; lia.
Qed.

Lemma init_links_heap_finite first count h :
  heap_finite h -> heap_finite (init_links_heap first count h).
Proof.
  revert first h; induction count as [| count IH]; intros first h Hh.
  - exact Hh.
  - cbn [init_links_heap]; apply IH, heap_finite_upd, Hh.
Qed.
