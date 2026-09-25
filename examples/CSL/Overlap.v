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

    The witness queue (header 2, nodes [4;6], payloads [7;9]) and the two
    candidate frames are section [Let]s, discharged into the statements.
    This file is frame-variant independent. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.

From TICL Require Import Lang.CSL.Queue.Representation Lang.CSL.Queue.Trace
  Lang.CSL.Queue.Frame Lang.CSL.Queue.Layout.

Import ListNotations.
Local Open Scope list_scope.

Section Overlap.

Let h1 : Heap := qheap 2 [4;6] [7;9].
(** The candidate frame claims address 3, which is the queue's HEAD POINTER
    cell -- squarely inside [qcells 2 [4;6]]. *)
Let fbad : Heap := hsingle 3 42.
(** The candidate frame allocates address 0, which the language's
    representation uses as the end-of-list terminator. *)
Let fnull : Heap := hsingle 0 1.

Local Lemma qwf1 : qwf 2 [4;6].
Proof.
  split; [| split].
  - repeat (apply NoDup_cons; [cbn; intuition congruence |]); apply NoDup_nil.
  - cbn; intuition congruence.
  - cbn; intros x y Hx Hy; intuition lia.
Qed.

Local Lemma qrep1 : qrep 2 [4;6] [7;9] h1.
Proof. apply qheap_qrep; [apply qwf1 | reflexivity | discriminate]. Qed.

(** ** C1: overlap *)

(** (a) The compatibility check rejects it. *)
Theorem overlap_rejected: ~ hdisj h1 fbad.
Proof.
  intro Hd; destruct (Hd 3) as [H | H].
  - assert (Hin : In 3 (qcells 2 [4;6])) by (unfold qcells; cbn; tauto).
    apply (qrep_fp 2 [4;6] [7;9] h1 qrep1 3 Hin); exact H.
  - unfold fbad, hsingle in H; cbn in H; discriminate.
Qed.

(** (b) ...and the conclusion it would license is FALSE.  The cell the
    candidate frame claims really does change value after one rotation, so no
    assertion about it can be carried across the queue's execution.  This is
    what makes [hdisj] a genuine hypothesis rather than a convenience: the
    failure is semantic, not a stuck proof. *)
Local Lemma rot_changes_head_pointer : qstep 2 [4;6] h1 3 = Some 6 /\ h1 3 = Some 4.
Proof. split; reflexivity. Qed.

Theorem overlap_frame_not_preserved:
    cellsat [(3, 4)] h1 /\ ~ cellsat [(3, 4)] (qstep 2 [4;6] h1).
Proof.
  split.
  - unfold cellsat; repeat constructor.
  - intro H; unfold cellsat in H; rewrite Forall_forall in H.
    specialize (H (3, 4) (in_eq _ _)); cbn [fst snd] in H.
    rewrite (proj1 rot_changes_head_pointer) in H; discriminate.
Qed.

(** ** C2: the null address *)

(** (a) The compatibility check rejects it. *)
Theorem null_frame_rejected: fnull 0 <> None.
Proof. unfold fnull, hsingle; cbn; discriminate. Qed.

(** (b) ...and the conclusion it would license is FALSE: the extended heap is
    not a representation of the queue at all, so the frozen recurrence theorem
    does not even apply to it.  [hdisj h1 fnull] DOES hold, so this is a
    condition that disjointness alone does not supply. *)
Theorem null_frame_disjoint_but_bad:
    hdisj h1 fnull /\ ~ qrep 2 [4;6] [7;9] (hunion h1 fnull).
Proof.
  split.
  - intro x; destruct (h1 x) eqn:E; [| now left].
    right; unfold fnull, hsingle.
    destruct (Nat.eq_dec 0 x) as [Ex | Hne]; [| reflexivity].
    exfalso; rewrite <- Ex in E.
    pose proof (qrep_null 2 [4;6] [7;9] h1 qrep1) as H0; congruence.
  - intro Hq; pose proof (qrep_null _ _ _ _ Hq) as H0.
    unfold hunion, fnull, hsingle in H0; cbn in H0; discriminate.
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

End Overlap.
