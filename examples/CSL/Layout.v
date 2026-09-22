(** Concrete queue layout and address-bound frame fixtures. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.

From TICL Require Import
  Lang.CSL.Queue.Representation Lang.CSL.Queue.Layout Lang.CSL.Queue.Frame.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.



(** ** The concrete rotating queue, frozen across every frame variant.

    Addresses are even and below 8; every frame variant below allocates only
    addresses at least 8.  That single numeric separation is what both proof
    families use, and it is stated once, here. *)

Definition hdr1 : nat := 2.
Definition ns1 : list nat := [4; 6].
Definition vs1 : list nat := [7; 9].
Definition nl : nat := 7.

Definition h1 : Heap := qheap hdr1 ns1 vs1.

Lemma qwf1: qwf hdr1 ns1.
Proof.
  unfold hdr1, ns1; split; [| split].
  - repeat (apply NoDup_cons; [cbn; intuition congruence |]); apply NoDup_nil.
  - cbn; intuition congruence.
  - cbn; intros x y Hx Hy; intuition lia.
Qed.

Lemma qrep1: qrep hdr1 ns1 vs1 h1.
Proof. apply qheap_qrep; [apply qwf1 | reflexivity | discriminate]. Qed.

Lemma qex1: qex hdr1 ns1 h1.
Proof. apply qheap_qex. Qed.

Lemma ns1_nonnil: ns1 <> [].
Proof. discriminate. Qed.

Lemma find_nl_vs1: find nl vs1 = Some 0.
Proof. reflexivity. Qed.

(** The queue's footprint is exactly the addresses below 8. *)
Lemma qcells1_low: forall x, In x (qcells hdr1 ns1) -> x < 8.
Proof. unfold hdr1, ns1, qcells; cbn; intros x H; intuition lia. Qed.

Lemma h1_low: forall x, h1 x <> None -> x < 8.
Proof. intros x H; apply qcells1_low, qex1, H. Qed.

(** [high] and [HighHeap] are the SHARED vocabulary in which every frame
    variant describes itself: "I allocate only addresses at or above 8".
    They are defined here, in a file that does not import the [Coinduction]
    library, because inside TICL's scopes [<=] resolves to a lattice order
    rather than to [Nat.le]. *)
Definition high (x: nat) : Prop := 8 <= x.

Definition HighHeap (f: Heap) : Prop := forall x, f x <> None -> high x.

Lemma high_not_low: forall x, high x -> x < 8 -> False.
Proof. unfold high; intros x H1 H2; lia. Qed.

Lemma high_nonzero: forall x, high x -> x <> 0.
Proof. unfold high; intros x H; lia. Qed.


(** The two compatibility conditions, derived once from the address bound.
    Every frame variant states only [HighHeap fv]; both proof families read
    the conditions off from here. *)

Lemma disj_of_high: forall f, HighHeap f -> hdisj h1 f.
Proof.
  intros f Hhigh x; destruct (h1 x) eqn:E; [| now left].
  right; destruct (f x) eqn:F; [| reflexivity].
  exfalso; apply (high_not_low x); [apply Hhigh; congruence |].
  apply h1_low; congruence.
Qed.

Lemma null_of_high: forall f, HighHeap f -> f 0 = None.
Proof.
  intros f Hhigh; destruct (f 0) eqn:E; [| reflexivity].
  exfalso; apply (high_nonzero 0); [apply Hhigh; congruence | reflexivity].
Qed.

(** Rotation permutes the node list, so every node reachable from the initial
    layout still lies below 8.  Both families need this to know that the four
    addresses a rotation writes are inside the queue. *)
Lemma ns1_low: forall x, In x ns1 -> x < 7.
Proof. unfold ns1; cbn; intros x H; intuition lia. Qed.

(** ** Instantiating the compatibility conditions from an address bound.

    Every frame variant is described by "I allocate only addresses at least
    8"; the owned queue lives below 8 ([Layout.h1_low]).  These two lemmas turn
    that numeric statement into the two compatibility conditions, once. *)

Lemma qrepX1: qrepX hdr1 ns1 vs1 h1.
Proof. split; [apply qrep1 | apply qex1]. Qed.

