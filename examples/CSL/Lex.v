(** * Lex: the lexicographic variant used by the SCHEDULED composition.

    NEW in this experiment.  The frozen [Recurrence.v] rank is [lexnat], a
    lexicographic order on [nat * nat]: (occurrence bound still to outrun,
    position of the observed element).  A composed run needs a THIRD
    component, and it is a genuinely new obligation rather than a bigger
    number:

    - the first component (occurrence bound) falls on EVERY scheduler turn,
      because every turn of either queue emits exactly one observation;
    - the second component (position of the element in the FOCUSED queue) falls
      only on the focused queue's own turns and is UNCHANGED by the foreign
      queue's turns;
    - the third component is the SCHEDULER PHASE, and it is what makes a
      foreign turn count as progress at all: a turn of the other queue leaves
      the focused queue's position alone, so without a phase component the
      variant would not decrease and the composition proof would not close.

    So the third component is exactly the "scheduler-phase progress argument"
    the composition needs on top of the reused position argument.  Nothing
    here is ordinal: the whole rank is [nat * (nat * nat)]. *)

From Stdlib Require Import
  Relations
  Arith.Wf_nat
  Arith.PeanoNat
  Lia.

(** One lexicographic layer over [nat]. *)
Definition lexn {A} (R: relation A) : relation (nat * A) :=
  fun p q => fst p < fst q \/ (fst p = fst q /\ R (snd p) (snd q)).

Lemma lexn_wf {A} (R: relation A): well_founded R -> well_founded (lexn R).
Proof.
  intros HR [a b]; revert b.
  induction a as [a IHa] using (well_founded_induction lt_wf).
  intro b.
  induction b as [b IHb] using (well_founded_induction HR).
  constructor; intros [c d] [Hlt | (Heq & Hlt)]; cbn in *.
  - now apply IHa.
  - subst c; now apply IHb.
Qed.

(** The rank of the composed proof. *)
Definition rank3 : relation (nat * (nat * nat)) := lexn (lexn lt).

Lemma rank3_wf: well_founded rank3.
Proof. apply lexn_wf, lexn_wf, lt_wf. Qed.

(** The three ways the rank falls, stated as the composition proof uses them.
    [rank3_bound] is the reused occurrence argument, [rank3_pos] the reused
    position argument, [rank3_phase] the NEW scheduler-phase argument. *)

Lemma rank3_bound: forall b b' p p' q q',
    b' < b -> rank3 (b', (p', q')) (b, (p, q)).
Proof. intros; left; cbn; assumption. Qed.

Lemma rank3_pos: forall b p p' q q',
    p' < p -> rank3 (b, (p', q')) (b, (p, q)).
Proof. intros; right; cbn; split; [reflexivity | left; cbn; assumption]. Qed.

Lemma rank3_phase: forall b p q q',
    q' < q -> rank3 (b, (p, q')) (b, (p, q)).
Proof.
  intros; right; cbn; split; [reflexivity |].
  right; cbn; split; [reflexivity | assumption].
Qed.
