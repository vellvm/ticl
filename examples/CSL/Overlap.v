(** * Overlap: the compatibility preconditions are load-bearing.

    [Frame.qrepX_frame] asks for two things of a frame [f]:

      (C1) [hdisj h f] -- the frame owns no cell of the queue;
      (C2) [f 0 = None] -- the frame does not allocate the null address.

    A precondition can fail to apply for two very different reasons: because
    it is merely sufficient, or because dropping it makes the conclusion
    false.  These are the second kind.  Each condition is refuted twice: once
    showing that the compatibility check rejects the candidate frame, and once
    showing that the conclusion the frame rule would license is actually
    false.

    This file is frame-variant independent. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.

From examples Require Import CSL.HeapQ CSL.Trace CSL.Layout CSL.Frame.

Import ListNotations.
Local Open Scope list_scope.

(** ** C1: overlap *)

(** The candidate frame claims address 3, which is the queue's HEAD POINTER
    cell -- squarely inside [qcells hdr1 ns1]. *)
Definition fbad : Heap := Layout.hsingle 3 42.

Lemma three_in_footprint: In 3 (qcells hdr1 ns1).
Proof. unfold hdr1, ns1, qcells; cbn; tauto. Qed.

(** (a) The compatibility check rejects it. *)
Theorem overlap_rejected: ~ hdisj h1 fbad.
Proof.
  intro Hd; destruct (Hd 3) as [H | H].
  - apply (qrep_fp hdr1 ns1 vs1 h1 qrep1 3 three_in_footprint); exact H.
  - unfold fbad, Layout.hsingle in H; cbn in H; discriminate.
Qed.

(** (b) ...and the conclusion it would license is FALSE.  The cell the
    candidate frame claims really does change value after one rotation, so no
    assertion about it can be carried across the queue's execution.  This is
    what makes [hdisj] a genuine hypothesis rather than a convenience: the
    failure is semantic, not a stuck proof. *)
Lemma rot_changes_head_pointer: qstep hdr1 ns1 h1 3 = Some 6 /\ h1 3 = Some 4.
Proof. split; reflexivity. Qed.

Theorem overlap_frame_not_preserved:
    cellsat [(3, 4)] h1 /\ ~ cellsat [(3, 4)] (qstep hdr1 ns1 h1).
Proof.
  split.
  - unfold cellsat; repeat constructor.
  - intro H; unfold cellsat in H; rewrite Forall_forall in H.
    specialize (H (3, 4) (in_eq _ _)); cbn in H; discriminate.
Qed.

(** For contrast, the SAME shape of assertion about a cell outside the
    footprint is preserved -- so the refutation above is about overlap and not
    about [cellsat] being unpreservable in general. *)
Theorem disjoint_cell_is_preserved: forall n a v,
    high a ->
    cellsat [(a, v)] h1 -> cellsat [(a, v)] (qstepN hdr1 n ns1 h1).
Proof.
  intros n a v Ha H; eapply cellsat_agree; [| exact H].
  intros p Hp; cbn in Hp; destruct Hp as [E | []]; rewrite <- E; cbn.
  apply (qstepN_agree n hdr1 ns1 vs1 h1 qrep1 ns1_nonnil).
  intro C; apply (high_not_low a); [exact Ha | now apply qcells1_low].
Qed.

(** ** C2: the null address *)

(** The candidate frame allocates address 0, which the language's
    representation uses as the end-of-list terminator. *)
Definition fnull : Heap := Layout.hsingle 0 1.

(** (a) The compatibility check rejects it. *)
Theorem null_frame_rejected: fnull 0 <> None.
Proof. unfold fnull, Layout.hsingle; cbn; discriminate. Qed.

(** (b) ...and the conclusion it would license is FALSE: the extended heap is
    not a representation of the queue at all, so the frozen recurrence theorem
    does not even apply to it.  [hdisj h1 fnull] DOES hold, so this is a
    condition that disjointness alone does not supply. *)
Theorem null_frame_disjoint_but_bad:
    hdisj h1 fnull /\ ~ qrep hdr1 ns1 vs1 (hunion h1 fnull).
Proof.
  split.
  - intro x; destruct (h1 x) eqn:E; [| now left].
    right; unfold fnull, Layout.hsingle.
    destruct (Nat.eqb_spec x 0) as [Ex | Hne]; [| reflexivity].
    exfalso; rewrite Ex in E.
    pose proof (qrep_null hdr1 ns1 vs1 h1 qrep1) as H0; congruence.
  - intro Hq; pose proof (qrep_null _ _ _ _ Hq) as H0.
    unfold hunion, fnull, Layout.hsingle in H0; cbn in H0; discriminate.
Qed.

(** ** The two conditions are independent

    [fbad] satisfies C2 and fails C1; [fnull] satisfies C1 and fails C2.  So
    neither condition subsumes the other, and the transport theorem's
    precondition is not redundant. *)
Theorem conditions_independent:
    (fbad 0 = None /\ ~ hdisj h1 fbad)
    /\ (hdisj h1 fnull /\ fnull 0 <> None).
Proof.
  split.
  - split; [reflexivity | apply overlap_rejected].
  - split; [apply (proj1 null_frame_disjoint_but_bad) | apply null_frame_rejected].
Qed.
