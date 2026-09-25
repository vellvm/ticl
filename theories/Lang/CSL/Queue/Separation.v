(** * Sep2: the separation layer for TWO ACTIVE queues.

    NEW in this experiment.  The dependency experiment
    ("measure reuse under an unused second queue") proved a TRANSPORT theorem:
    a queue's [AG AF] specification survives disjoint extension of the heap by
    an arbitrary FIXED frame [f].  Nothing in that development says what
    happens when the other region is itself running.

    This file is the resource-level content of that difference.  It contains
    three kinds of statement:

    1. [foreign_pres] -- a step of ONE queue preserves the OTHER queue's
       representation.  This is NOT an instance of the frame rule: the frame
       rule says an untouched region stays untouched, whereas here the region
       that stays intact is one that will itself take steps later, and the
       region taking the step is one that the other's specification must also
       be stated about.  The proof is nevertheless CHEAP, and that is the
       measurable finding: it is two applications of frozen lemmas
       ([Frame.qstep_agree] and [Frame.qrep_agree_fp]).

    2. [compose3] -- the three-way composition (queue 1 * queue 2 * outer
       frame) that instantiates the disjointness premises from precise
       ownership.  Here the frame rule IS reused, unchanged
       ([Frame.qrepX_frame]).

    3. [owned_queues_sound] -- precise separating ownership of two queues
       yields the two representations and their footprint disjointness.

    Everything in this file is a statement about heaps.  No temporal formula
    and no ICTree appears. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.

From TICL Require Import Lang.CSL.Queue.Representation Lang.CSL.Queue.Trace
  Lang.CSL.Queue.Layout Lang.CSL.Queue.Frame.

Import ListNotations.
Local Open Scope list_scope.

(** ** Footprint disjointness of two queues *)

Definition Disj (u: nat) (n1: list nat) (v: nat) (n2: list nat) : Prop :=
  forall x, In x (qcells u n1) -> ~ In x (qcells v n2).

Lemma Disj_sym: forall u n1 v n2, Disj u n1 v n2 -> Disj v n2 u n1.
Proof. intros u n1 v n2 H x Hx Hy; exact (H x Hy Hx). Qed.

(** The footprint is stable as a SET under rotation ([Frame.qcells_rotl]), so
    disjointness needs no re-establishing: it is transported, not re-proved.
    This is one of the reused locality facts. *)
Lemma Disj_rotl_l: forall u n1 v n2,
    n1 <> [] -> Disj u n1 v n2 -> Disj u (rotl n1) v n2.
Proof.
  intros u n1 v n2 Hne H x Hx; apply H, (qcells_rotl u n1 x Hne), Hx.
Qed.

Lemma Disj_rotl_r: forall u n1 v n2,
    n2 <> [] -> Disj u n1 v n2 -> Disj u n1 v (rotl n2).
Proof.
  intros u n1 v n2 Hne H x Hx Hy.
  apply (H x Hx), (qcells_rotl v n2 x Hne), Hy.
Qed.

(** ** The foreign step preserves the other queue

    This is the core new obligation of active composition.  Read it as: the
    OTHER component's representation predicate, at the SAME abstract queue
    [n2]/[vs2], survives an arbitrary step of THIS component. *)

Lemma qstep_null: forall u n1 vs1 h,
    qrep u n1 vs1 h -> n1 <> [] -> qstep u n1 h 0 = None.
Proof.
  intros u n1 vs1 h Hq Hne.
  pose proof Hq as (Hwf & _ & _ & _ & Hnull & _).
  rewrite (qstep_agree u n1 vs1 h Hq Hne 0) by (apply qwf_zero, Hwf).
  exact Hnull.
Qed.

Theorem foreign_pres: forall u n1 vs1 v n2 vs2 h,
    qrep u n1 vs1 h -> n1 <> [] ->
    qrep v n2 vs2 h ->
    Disj u n1 v n2 ->
    qrep v n2 vs2 (qstep u n1 h).
Proof.
  intros u n1 vs1 v n2 vs2 h Hq1 Hne1 Hq2 Hd.
  eapply qrep_agree_fp; [exact Hq2 | | ].
  - intros x Hx.
    apply (qstep_agree u n1 vs1 h Hq1 Hne1).
    intro C; exact (Hd x C Hx).
  - eapply qstep_null; eassumption.
Qed.

(** The same statement in the [rot_heap] form the language layer produces.
    [qstep u (a :: n1) h] is [rot_heap u a (List.hd 0 n1) (zof u n1) h] by
    definition, so this is a restatement, not a second proof. *)
Corollary foreign_pres_rot: forall u a n1 vs1 v n2 vs2 h,
    qrep u (a :: n1) vs1 h ->
    qrep v n2 vs2 h ->
    Disj u (a :: n1) v n2 ->
    qrep v n2 vs2 (rot_heap u a (List.hd 0 n1) (zof u n1) h).
Proof.
  intros u a n1 vs1 v n2 vs2 h Hq1 Hq2 Hd.
  exact (foreign_pres u (a :: n1) vs1 v n2 vs2 h Hq1 ltac:(discriminate) Hq2 Hd).
Qed.

(** ** Three-way composition: queue 1 * queue 2 * outer frame

    The two queues are given as PRECISE resources ([qrepX], "this heap IS the
    queue"), the outer frame [f] as an arbitrary null-avoiding heap.  The
    conclusion supplies the composed run's three preconditions. *)

Theorem compose3: forall u n1 vs1 h1 v n2 vs2 h2 f,
    qrepX u n1 vs1 h1 ->
    qrepX v n2 vs2 h2 ->
    hdisj h1 h2 -> hdisj h1 f -> hdisj h2 f ->
    f 0 = None ->
    qrep u n1 vs1 (hunion h1 (hunion h2 f))
    /\ qrep v n2 vs2 (hunion h1 (hunion h2 f))
    /\ Disj u n1 v n2.
Proof.
  intros u n1 vs1 h1 v n2 vs2 h2 f Hx1 Hx2 H12 H1f H2f Hf0.
  pose proof (qrepX_qrep _ _ _ _ Hx1) as Hq1.
  pose proof (qrepX_qrep _ _ _ _ Hx2) as Hq2.
  pose proof (qrep_null _ _ _ _ Hq2) as Hn2.
  assert (Hun0: hunion h2 f 0 = None) by (apply hunion_null; assumption).
  split; [| split].
  - (* the frame rule, REUSED unchanged *)
    apply (qrepX_frame u n1 vs1 h1 (hunion h2 f) Hx1
             (hdisj_union h1 h2 f H12 H1f) Hun0).
  - (* queue 2 sits under an allocated region on its left: agreement, not framing *)
    eapply qrep_agree_fp; [exact Hq2 | |].
    + intros x Hx.
      assert (Hd2: h2 x <> None) by (eapply qrep_fp; eassumption).
      assert (H1n: h1 x = None)
        by (destruct (H12 x) as [E | C]; [exact E | contradiction]).
      unfold hunion; rewrite H1n.
      destruct (h2 x) eqn:E2; [reflexivity | contradiction].
    + unfold hunion; rewrite (qrep_null _ _ _ _ Hq1); exact Hun0.
  - (* disjoint ownership gives disjoint footprints *)
    intros x Hx1' Hx2'.
    assert (Hd1: h1 x <> None) by (eapply qrep_fp; eassumption).
    assert (Hd2: h2 x <> None) by (eapply qrep_fp; eassumption).
    destruct (H12 x); contradiction.
Qed.

(** ** Precise ownership of two queues

    [owned_queues] is the separating conjunction of the two precise queue
    resources.  Soundness goes through [compose3] with an empty outer frame and
    pointwise footprint agreement; heap functions are never equated. *)

Definition owned_queues u ns1 vs1 v ns2 vs2 : Heap -> Prop :=
  asep (qrepX u ns1 vs1) (qrepX v ns2 vs2).

Lemma owned_queues_sound u ns1 vs1 v ns2 vs2 h :
  owned_queues u ns1 vs1 v ns2 vs2 h ->
  qrep u ns1 vs1 h /\ qrep v ns2 vs2 h /\ Disj u ns1 v ns2.
Proof.
  intros (h1 & h2 & Hd & Heq & H1 & H2).
  change (hdisj h1 h2) in Hd.
  change (heq h (hunion h1 h2)) in Heq.
  assert (H1e : hdisj h1 hemp) by (intro x; right; reflexivity).
  assert (H2e : hdisj h2 hemp) by (intro x; right; reflexivity).
  destruct (compose3 u ns1 vs1 h1 v ns2 vs2 h2 hemp
    H1 H2 Hd H1e H2e eq_refl) as (Q1 & Q2 & Hdisj).
  assert (Hagree : forall x, hunion h1 (hunion h2 hemp) x = h x).
  { intro x; rewrite Heq; unfold hunion, hemp.
    destruct (h1 x); [reflexivity | destruct (h2 x); reflexivity]. }
  split; [| split].
  - eapply qrep_agree_fp; [exact Q1 | |].
    + intros x _; symmetry; apply Hagree.
    + rewrite <- Hagree; exact (qrep_null _ _ _ _ Q1).
  - eapply qrep_agree_fp; [exact Q2 | |].
    + intros x _; symmetry; apply Hagree.
    + rewrite <- Hagree; exact (qrep_null _ _ _ _ Q2).
  - exact Hdisj.
Qed.
