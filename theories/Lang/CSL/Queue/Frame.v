(** * Separation and framing of heap-backed queue recurrence.

    This module separates resource reasoning from temporal recurrence:

    - the PRECISE representation predicate [qrepX = qrep /\ qex] and the
      transport theorem [qrepX_frame]: a heap that IS the queue, disjointly
      extended by any null-avoiding frame, is a heap that CONTAINS the queue;

    - the converse [qrep_decompose]: every heap containing the queue splits,
      UNIQUELY ([qrep_decompose_unique]), as (queue * frame).  Together these
      say [qrep = qrepX * True] with [qrepX] precise, so "the frame" is a
      function of the state rather than a re-chosen existential;

    - transport corollaries reuse [Recurrence.v] without reopening its temporal
      invariant, rank, induction, or coinduction;

    - frame PRESERVATION: the run's heap after any number of rotations agrees
      with the initial heap outside the queue's footprint ([qstepN_agree]), so
      any assertion holding of the frame holds forever
      ([frame_assertion_preserved]).  [Trace.run_stepN] is what makes "after
      n rotations" the same thing as "n observations into the run".

    All frame heaps are parameters; concrete fixtures remain in examples. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Interp.State.Mod
  ICTree.Events.State
  ICTree.Events.Writer
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.State
  Logic.Core.

From TICL Require Import
  Lang.CSL.Queue.Representation Lang.CSL.Queue.Sequential Lang.CSL.Queue.Recurrence
  Lang.CSL.Queue.Trace Lang.CSL.Queue.Layout.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.

(** ** The precise representation predicate *)

Definition qrepX (hdr: nat) (ns vs: list nat) (h: Heap) : Prop :=
  qrep hdr ns vs h /\ qex hdr ns h.

Lemma qrepX_qrep: forall hdr ns vs h, qrepX hdr ns vs h -> qrep hdr ns vs h.
Proof. intros ? ? ? ? (H & _); exact H. Qed.

(** *** The transport theorem on the PRECONDITION.

    [f] is an arbitrary heap.  The two compatibility conditions are exactly
    [hdisj h f] -- the frame owns no cell of the queue -- and [f 0 = None] --
    the frame does not allocate the null address, which the language treats as
    the end-of-list terminator.  Both are refuted by counterexample in
    [Overlap.v]. *)
Theorem qrepX_frame: forall hdr ns vs h f,
    qrepX hdr ns vs h ->
    hdisj h f ->
    f 0 = None ->
    qrep hdr ns vs (hunion h f).
Proof.
  intros hdr ns vs h f ((Hwf & Hhd & Htl & Hch & Hnull & Hfp) & Hex) Hdisj Hf0.
  split; [exact Hwf | split; [| split; [| split]]].
  - now apply hunion_some.
  - unfold tailok in Htl |- *; destruct ns as [| a ns].
    + now apply hunion_dom.
    + now apply hunion_some.
  - eapply chain_mono; [exact Hch |].
    intros x Hx; apply hunion_eq; eapply chain_dom; eauto.
  - split.
    + rewrite hunion_none; assumption.
    + intros x Hx; apply hunion_dom, Hfp, Hx.
Qed.

(** A precise queue owns nothing outside its footprint. *)
Lemma qex_out: forall hdr ns h x,
    qex hdr ns h -> ~ In x (qcells hdr ns) -> h x = None.
Proof.
  intros hdr ns h x Hex Hout; destruct (h x) eqn:E;
    [exfalso; apply Hout, Hex; congruence | reflexivity].
Qed.

(** [qrep] only looks at the footprint and at the null cell, so it survives any
    change that leaves both alone.  This is what turns [qstepN_agree] (the
    rotating queue touches nothing outside ITS footprint) into "the unused
    second queue is still there, at every reachable state". *)
Lemma qrep_agree_fp: forall hdr ns vs h h',
    qrep hdr ns vs h ->
    (forall x, In x (qcells hdr ns) -> h' x = h x) ->
    h' 0 = None ->
    qrep hdr ns vs h'.
Proof.
  intros hdr ns vs h h' (Hwf & Hhd & Htl & Hch & Hnull & Hfp) Hag H0.
  assert (Hcells: forall x, In x (cells ns) -> h' x = h x)
    by (intros x Hx; apply Hag, in_cons, in_cons, Hx).
  split; [exact Hwf | split; [| split; [| split]]].
  - rewrite Hag; [exact Hhd | apply in_cons, in_eq].
  - unfold tailok in Htl |- *; destruct ns as [| a ns];
      rewrite Hag by apply in_eq; exact Htl.
  - eapply chain_mono; [exact Hch | exact Hcells].
  - split; [exact H0 | intros x Hx; rewrite Hag by exact Hx; now apply Hfp].
Qed.

(** ** The canonical decomposition, and its uniqueness *)

Definition inqb (hdr: nat) (ns: list nat) (x: nat) : bool :=
  if in_dec Nat.eq_dec x (qcells hdr ns) then true else false.

Lemma inqb_true: forall hdr ns x, inqb hdr ns x = true <-> In x (qcells hdr ns).
Proof.
  intros hdr ns x; unfold inqb; destruct (in_dec Nat.eq_dec x (qcells hdr ns));
    split; intro H; auto; discriminate.
Qed.

Lemma inqb_false: forall hdr ns x, inqb hdr ns x = false <-> ~ In x (qcells hdr ns).
Proof.
  intros hdr ns x; unfold inqb; destruct (in_dec Nat.eq_dec x (qcells hdr ns));
    split; intro H; auto; [discriminate | contradiction].
Qed.

Definition qloc (hdr: nat) (ns: list nat) (H: Heap) : Heap :=
  fun x => if inqb hdr ns x then H x else None.

Definition qfrm (hdr: nat) (ns: list nat) (H: Heap) : Heap :=
  fun x => if inqb hdr ns x then None else H x.

Lemma qloc_in: forall hdr ns H x, In x (qcells hdr ns) -> qloc hdr ns H x = H x.
Proof. intros; unfold qloc; now rewrite (proj2 (inqb_true hdr ns x)). Qed.

Lemma qloc_out: forall hdr ns H x, ~ In x (qcells hdr ns) -> qloc hdr ns H x = None.
Proof. intros; unfold qloc; now rewrite (proj2 (inqb_false hdr ns x)). Qed.

Lemma qfrm_in: forall hdr ns H x, In x (qcells hdr ns) -> qfrm hdr ns H x = None.
Proof. intros; unfold qfrm; now rewrite (proj2 (inqb_true hdr ns x)). Qed.

Lemma qfrm_out: forall hdr ns H x, ~ In x (qcells hdr ns) -> qfrm hdr ns H x = H x.
Proof. intros; unfold qfrm; now rewrite (proj2 (inqb_false hdr ns x)). Qed.

Theorem qrep_decompose: forall hdr ns vs H,
    qrep hdr ns vs H ->
    qrepX hdr ns vs (qloc hdr ns H)
    /\ hdisj (qloc hdr ns H) (qfrm hdr ns H)
    /\ heq H (hunion (qloc hdr ns H) (qfrm hdr ns H))
    /\ qfrm hdr ns H 0 = None.
Proof.
  intros hdr ns vs H Hq.
  pose proof Hq as (Hwf & Hhd & Htl & Hch & Hnull & Hfp).
  assert (Hhdr: In hdr (qcells hdr ns)) by apply in_eq.
  assert (Hshdr: In (S hdr) (qcells hdr ns)) by (apply in_cons, in_eq).
  assert (Hcells: forall x, In x (cells ns) -> In x (qcells hdr ns))
    by (intros x Hx; apply in_cons, in_cons, Hx).
  split; [split; [split; [exact Hwf | split; [| split; [| split]]] |] | split; [| split]].
  - rewrite qloc_in; assumption.
  - unfold tailok in Htl |- *; destruct ns as [| a ns]; rewrite qloc_in; assumption.
  - eapply chain_mono; [exact Hch |]; intros x Hx; apply qloc_in, Hcells, Hx.
  - split.
    + destruct (in_dec Nat.eq_dec 0 (qcells hdr ns)) as [Hin | Hout];
        [now rewrite qloc_in | now rewrite qloc_out].
    + intros x Hx; rewrite qloc_in by exact Hx; now apply Hfp.
  - intros x Hx; unfold qloc in Hx; destruct (inqb hdr ns x) eqn:E;
      [now apply inqb_true | congruence].
  - intro x; unfold qloc, qfrm; destruct (inqb hdr ns x); [now right | now left].
  - intro x; unfold hunion, qloc, qfrm; destruct (inqb hdr ns x);
      [destruct (H x); reflexivity | reflexivity].
  - destruct (in_dec Nat.eq_dec 0 (qcells hdr ns)) as [Hin | Hout];
      [now rewrite qfrm_in | now rewrite qfrm_out].
Qed.

(** Precision: the split is UNIQUE.  This is what makes "the frame" a function
    of the state, so that "the same [f] throughout execution" is a statement
    about one resource rather than a fresh existential at every step. *)
Theorem qrep_decompose_unique: forall hdr ns vs H h f,
    qrepX hdr ns vs h ->
    hdisj h f ->
    heq H (hunion h f) ->
    heq h (qloc hdr ns H) /\ heq f (qfrm hdr ns H).
Proof.
  intros hdr ns vs H h f (Hq & Hex) Hdisj Heqh.
  pose proof (qrep_fp _ _ _ _ Hq) as Hfp.
  split; intro x; destruct (in_dec Nat.eq_dec x (qcells hdr ns)) as [Hin | Hout].
  - rewrite qloc_in by exact Hin; rewrite Heqh, hunion_eq by now apply Hfp.
    reflexivity.
  - rewrite qloc_out by exact Hout.
    destruct (h x) eqn:E; [exfalso; apply Hout, Hex; congruence | reflexivity].
  - rewrite qfrm_in by exact Hin.
    destruct (Hdisj x) as [Hh | Hf]; [| exact Hf].
    exfalso; apply (Hfp x Hin); exact Hh.
  - rewrite qfrm_out by exact Hout; rewrite Heqh, hunion_none;
      [reflexivity |].
    destruct (h x) eqn:E; [exfalso; apply Hout, Hex; congruence | reflexivity].
Qed.

(** ** The transport corollaries.

    Apply [Recurrence.v] with framed representation premises. The shared
    [aul_state_iter_ghost] rule and queue invariants are reused unchanged. *)

Theorem rotate_agaf_pop_framed: forall hdr nlv ns vs d h f c,
    qrepX hdr ns vs h ->
    hdisj h f ->
    f 0 = None ->
    find nlv vs = Some d ->
    <( {run hdr (hunion h f) c}, Pure |= AG (AF visW {popped nlv}) )>.
Proof.
  intros hdr nlv ns vs d h f c Hx Hd Hf Hfind.
  eapply rotate_agaf_pop_heap; [eapply qrepX_frame; eassumption | exact Hfind].
Qed.

Theorem rotate_agaf_pop_fresh_framed: forall hdr nlv ns vs d h f c k,
    qrepX hdr ns vs h ->
    hdisj h f ->
    f 0 = None ->
    find nlv vs = Some d ->
    <( {run hdr (hunion h f) c}, Pure |= AG (AF visW {popped_after nlv k}) )>.
Proof.
  intros hdr nlv ns vs d h f c k Hx Hd Hf Hfind.
  eapply rotate_agaf_pop_fresh; [eapply qrepX_frame; eassumption | exact Hfind].
Qed.

(** The control that separates "the payload is somewhere in the global heap"
    from "the payload is popped": an element absent from the OWNED queue is
    never observed, no matter what the frame stores. *)
Theorem absent_never_observed_framed: forall hdr ns vs nlv h f c,
    qrepX hdr ns vs h ->
    hdisj h f ->
    f 0 = None ->
    ns <> [] ->
    ~ In nlv vs ->
    <( {run hdr (hunion h f) c}, Pure |= AG (now {obs_sat (fun x => x <> nlv)}) )>.
Proof.
  intros hdr ns vs nlv h f c Hx Hd Hf Hne Hnin.
  eapply absent_never_observed;
    [eapply qrepX_frame; eassumption | exact Hne | exact Hnin].
Qed.

(** The stuck control transports too: an empty owned queue is stuck even when
    the frame is a large populated heap. *)
Theorem empty_queue_no_ag_framed: forall hdr vs h f c w phi,
    qrepX hdr [] vs h ->
    hdisj h f ->
    f 0 = None ->
    ~ <( {run hdr (hunion h f) c}, w |= AG phi )>.
Proof.
  intros hdr vs h f c w phi Hx Hd Hf.
  eapply empty_queue_no_ag; eapply qrepX_frame; eassumption.
Qed.

(** ** Frame preservation *)

Lemma qcells_writes: forall hdr a ns,
    In hdr (qcells hdr (a :: ns))
    /\ In (S hdr) (qcells hdr (a :: ns))
    /\ In (S a) (qcells hdr (a :: ns))
    /\ In (S (zof hdr ns)) (qcells hdr (a :: ns)).
Proof.
  intros hdr a ns.
  split; [apply in_eq |].
  split; [apply in_cons, in_eq |].
  split; [apply in_cons, in_cons, in_cells; exists a; split; [apply in_eq | now right] |].
  destruct ns as [| b ns'].
  - cbn [zof]; apply in_cons, in_eq.
  - apply in_cons, in_cons, in_cells; exists (zof hdr (b :: ns')); split; [| now right].
    cbn [zof]; apply in_cons, last_in; discriminate.
Qed.

Lemma qstep_agree: forall hdr ns vs h,
    qrep hdr ns vs h -> ns <> [] ->
    agree_out (qcells hdr ns) h (qstep hdr ns h).
Proof.
  intros hdr ns vs h Hq Hne.
  destruct ns as [| a ns']; [contradiction |].
  destruct (qcells_writes hdr a ns') as (H1 & H2 & H3 & H4).
  intros x Hx; cbn [qstep]; apply rot_heap_other;
    intro C; subst x; contradiction.
Qed.

Lemma qcells_rotl: forall hdr ns x,
    ns <> [] -> (In x (qcells hdr (rotl ns)) <-> In x (qcells hdr ns)).
Proof.
  intros hdr [| a ns'] x Hne; [contradiction |]; cbn [rotl]; apply qcells_rot.
Qed.

Theorem qstepN_agree: forall n hdr ns vs h,
    qrep hdr ns vs h -> ns <> [] ->
    agree_out (qcells hdr ns) h (qstepN hdr n ns h).
Proof.
  induction n as [| n IH]; intros hdr ns vs h Hq Hne.
  - intros x Hx; reflexivity.
  - intros x Hx; cbn [qstepN].
    rewrite (IH hdr (rotl ns) (rotl vs) (qstep hdr ns h)
               (qstep_qrep _ _ _ _ Hq Hne) (rotl_nonnil _ Hne) x).
    + now apply (qstep_agree hdr ns vs h Hq Hne).
    + intro C; apply Hx, (qcells_rotl hdr ns x Hne), C.
Qed.

(** The frame sub-heap is preserved POINTWISE, for every number of rotations. *)
Theorem frame_preserved: forall n hdr ns vs h,
    qrep hdr ns vs h -> ns <> [] ->
    heq (qfrm hdr ns h) (qfrm hdr ns (qstepN hdr n ns h)).
Proof.
  intros n hdr ns vs h Hq Hne x.
  destruct (in_dec Nat.eq_dec x (qcells hdr ns)) as [Hin | Hout].
  - now rewrite !qfrm_in.
  - rewrite !qfrm_out by exact Hout.
    symmetry; now apply (qstepN_agree n hdr ns vs h Hq Hne).
Qed.

Corollary frame_assertion_preserved: forall (A: Heap -> Prop) n hdr ns vs h,
    (forall h1 h2, heq h1 h2 -> A h1 -> A h2) ->
    qrep hdr ns vs h -> ns <> [] ->
    A (qfrm hdr ns h) ->
    A (qfrm hdr ns (qstepN hdr n ns h)).
Proof.
  intros A n hdr ns vs h HA Hq Hne HAf.
  eapply HA; [eapply frame_preserved; eassumption | exact HAf].
Qed.

(** The version stated on the ORIGINAL frame [f] of a [*]-decomposition, which
    is what the transport corollaries hand the client. *)
Corollary frame_assertion_preserved_sep: forall (A: Heap -> Prop) n hdr ns vs h f,
    (forall h1 h2, heq h1 h2 -> A h1 -> A h2) ->
    qrepX hdr ns vs h -> hdisj h f -> f 0 = None -> ns <> [] ->
    A f ->
    A (qfrm hdr ns (qstepN hdr n ns (hunion h f))).
Proof.
  intros A n hdr ns vs h f HA Hx Hd Hf Hne HAf.
  pose proof (qrepX_frame _ _ _ _ _ Hx Hd Hf) as HqH.
  destruct (qrep_decompose_unique hdr ns vs (hunion h f) h f Hx Hd
              (fun x => eq_refl)) as (_ & Hfeq).
  eapply frame_assertion_preserved; [exact HA | exact HqH | exact Hne |].
  eapply HA; [exact Hfeq | exact HAf].
Qed.


(** A newly initialized queue owns its block beside the unchanged old heap. *)
Lemma new_queue_heap_owned hdr values h :
  Nat.lt 0 hdr -> block_free h hdr (2 * S (length values)) ->
  asep (qrepX hdr (queue_nodes hdr (length values)) values)
       (fun frame => heq frame h)
       (new_queue_heap hdr values h).
Proof.
  intros Hhdr Hfree.
  exists (qheap hdr (queue_nodes hdr (length values)) values), h.
  split; [now apply new_queue_heap_disjoint |].
  split; [now apply new_queue_heap_agrees |].
  split.
  - split; [now apply qheap_queue_nodes_rep | apply qheap_qex].
  - intro x; reflexivity.
Qed.
