From Stdlib Require Import Relations Arith.Wf_nat Arith.PeanoNat List Lia.

(** One natural-number lexicographic layer over an arbitrary relation. *)
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

(** Natural pair and triple ranks share the same lexicographic construction. *)
Definition lexnat : relation (nat * nat) := lexn lt.

Lemma lexnat_wf: well_founded lexnat.
Proof. apply lexn_wf, lt_wf. Qed.

Definition rank3 : relation (nat * (nat * nat)) := lexn (lexn lt).

Lemma rank3_wf: well_founded rank3.
Proof. apply lexn_wf, lexn_wf, lt_wf. Qed.

(** Decrease in the first, second, or third component of a triple. *)
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

(** Occurrences arbitrarily far along a sequence, and counts in finite
    half-open intervals. *)
Definition infinitely (P : nat -> Prop) : Prop :=
  forall n, exists k, n <= k /\ P k.

Definition count_if (p : nat -> bool) (lo len : nat) : nat :=
  List.length (List.filter p (List.seq lo len)).

Lemma count_if_zero p lo : count_if p lo 0 = 0.
Proof. reflexivity. Qed.

Lemma count_if_succ p lo len :
  count_if p lo (S len) = (if p lo then 1 else 0) + count_if p (S lo) len.
Proof.
  unfold count_if; cbn [List.seq List.filter]; destruct (p lo); reflexivity.
Qed.

Lemma count_if_add p lo left right :
  count_if p lo (left + right) = count_if p lo left + count_if p (lo + left) right.
Proof.
  unfold count_if; rewrite List.seq_app, List.filter_app, List.length_app; reflexivity.
Qed.

Lemma infinitely_count_if (p : nat -> bool) :
  infinitely (fun k => p k = true) ->
  forall wanted lo, exists len, wanted <= count_if p lo len.
Proof.
  intros Hinf wanted; induction wanted as [|wanted IH]; intro lo.
  - exists 0; rewrite count_if_zero; lia.
  - destruct (Hinf lo) as [k [Hlo Hk]].
    destruct (IH (S k)) as [len Hlen].
    exists ((k - lo) + S len).
    rewrite count_if_add.
    replace (lo + (k - lo)) with k by lia.
    rewrite count_if_succ, Hk; cbn; lia.
Qed.

(** Constructively find the first satisfying index in a finite interval,
    or establish that the whole interval has no satisfying index. *)
Lemma finite_first (P : nat -> Prop)
  (dec : forall j, sumbool (P j) (not (P j))) lo len :
  (forall j, lo <= j < lo + len -> ~ P j) \/
  exists j, lo <= j < lo + len /\ P j /\ forall i, lo <= i < j -> ~ P i.
Proof.
  revert lo; induction len as [|len IH]; intro lo.
  - left; intros; lia.
  - destruct (dec lo) as [Hyes|Hno].
    + right; exists lo; split; [lia|]; split; [exact Hyes|].
      intros i Hi; lia.
    + destruct (IH (S lo)) as [Hnone|(j & Hj & HP & Hfirst)].
      * left; intros i Hi; destruct (Nat.eq_dec i lo) as [->|Hne];
          [exact Hno|apply Hnone; lia].
      * right; exists j; split; [lia|]; split; [exact HP|].
        intros i Hi; destruct (Nat.eq_dec i lo) as [->|Hne];
          [exact Hno|apply Hfirst; lia].
Qed.

(** Boolean existence search is a projection of the same first-index search. *)
Lemma finite_bool_search (p : nat -> bool) lo len :
  (exists k, lo <= k < lo + len /\ p k = true) \/
  (forall k, lo <= k < lo + len -> p k = false).
Proof.
  assert (dec : forall k, sumbool (p k = true) (p k <> true)).
  { intro k; destruct (p k); [left; reflexivity|right; discriminate]. }
  destruct (finite_first (fun k => p k = true) dec lo len)
    as [Hnone|(k & Hk & Hp & _) ].
  - right; intros k Hk.
    destruct (p k) eqn:Hp; [exfalso; exact (Hnone k Hk Hp)|reflexivity].
  - left; exists k; split; assumption.
Qed.
