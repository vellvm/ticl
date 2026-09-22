From Stdlib Require Import Lia Arith.PeanoNat.
From TICL Require Import Lang.CSL.Pcm.

Lemma same_cell_cannot_separate a v w h :
  ~ asep (pto a v) (pto a w) h.
Proof. apply Pcm.pto_sep_same_false. Qed.

Lemma distinct_cells_separate :
  asep (pto 2 7) (pto 4 9)
    (hunion (Pcm.hsingle 2 7) (Pcm.hsingle 4 9)).
Proof. apply Pcm.pto_sep_distinct; discriminate. Qed.

Lemma block_overlap_rejected :
  forall h, ~ asep (block_pto 1 2) (pto 2 9) h.
Proof.
  intros h (b & p & D & E & B & P).
  pose proof (B 2) as B2; change (b 2 = Some 0) in B2.
  pose proof (pto_lookup 2 9 p P) as P2.
  destruct (D 2); congruence.
Qed.

Lemma allocated_block_frame :
  asep (block_pto 3 2) (pto 2 9)
    (hunion (hblock 3 2) (Pcm.hsingle 2 9)).
Proof.
  apply allocated_block_sep.
  - intros offset O; unfold Pcm.hsingle; destruct (Nat.eq_dec 2 (3 + offset));
      [lia | reflexivity].
  - apply heq_refl.
Qed.
