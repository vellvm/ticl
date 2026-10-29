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

(** * Bounded-credit progress.

    A [Credit] RELATION (not a computable rank extractor) that descends by at
    least the charge of every uncharged-goal step bounds how many charged
    indices can pass before the goal is met.  Keeping the witnesses in [Prop]
    is what lets the same theorem serve a concrete potential and a
    heap-related ghost list.

    Charging counts selected USEFUL indices, not elapsed time, so arbitrarily
    many idle indices are allowed.  The zero-length interval is supported and
    cannot fabricate a hit. *)

Lemma credit_interval
  (Credit : nat -> nat -> Prop) (charged : nat -> bool) (goal : nat -> Prop)
  (step : forall k credit, Credit k credit -> ~ goal k ->
    exists credit', Credit (S k) credit' /\
      (if charged k then 1 else 0) + credit' <= credit) :
  forall lo len credit,
    Credit lo credit ->
    (forall k, lo <= k < lo + len -> ~ goal k) ->
    exists credit', Credit (lo + len) credit' /\
      count_if charged lo len + credit' <= credit.
Proof.
  intros lo len; revert lo; induction len as [|len IH]; intros lo credit Hc Hno.
  - exists credit; rewrite Nat.add_0_r, count_if_zero; split; [exact Hc | lia].
  - destruct (step lo credit Hc (Hno lo ltac:(lia))) as (mid & Hmid & Hdrop).
    destruct (IH (S lo) mid Hmid ltac:(intros k Hk; apply Hno; lia))
      as (credit' & Hcredit' & Hcount).
    exists credit'; split.
    + now replace (lo + S len) with (S lo + len) by lia.
    + rewrite count_if_succ; destruct (charged lo); lia.
Qed.

(** The first goal index inside an interval whose charge reaches a bound that
    no goal-free prefix can reach. *)
Lemma count_if_first
  (charged : nat -> bool) (goal : nat -> Prop)
  (dec : forall k, sumbool (goal k) (not (goal k))) lo len bound :
  (forall n, (forall k, lo <= k < lo + n -> ~ goal k) ->
    count_if charged lo n < bound) ->
  bound <= count_if charged lo len ->
  exists k, lo <= k < lo + len /\ goal k /\
    count_if charged lo (S k - lo) <= bound.
Proof.
  intros Hprefix Hreach.
  destruct (finite_first goal dec lo len) as [Hnone | (k & Hk & Hgoal & Hfirst)].
  - exfalso; specialize (Hprefix len Hnone); lia.
  - exists k; split; [exact Hk |]; split; [exact Hgoal |].
    (** The charge up to and including [k] is the goal-free prefix plus at
        most one, and the goal-free prefix is strictly below [bound]. *)
    assert (Hpre : count_if charged lo (k - lo) < bound)
      by (apply Hprefix; intros i Hi; apply Hfirst; lia).
    replace (S k - lo) with ((k - lo) + 1) by lia.
    rewrite count_if_add.
    replace (lo + (k - lo)) with k by lia.
    rewrite count_if_succ, count_if_zero.
    destruct (charged k); lia.
Qed.

(** If every goal-free interval has bounded charge and charging happens
    infinitely often, the goal is met infinitely often. *)
Lemma infinitely_progress
  (charged : nat -> bool) (goal : nat -> Prop)
  (dec : forall k, sumbool (goal k) (not (goal k))) :
  (forall lo, exists bound, forall len,
    (forall k, lo <= k < lo + len -> ~ goal k) ->
    count_if charged lo len < bound) ->
  infinitely (fun k => charged k = true) -> infinitely goal.
Proof.
  intros Hbound Hinf n.
  destruct (Hbound n) as (bound & Hprefix).
  destruct (infinitely_count_if charged Hinf bound n) as (len & Hlen).
  destruct (count_if_first charged goal dec n len bound Hprefix Hlen)
    as (k & Hk & Hgoal & _).
  exists k; split; [lia | exact Hgoal].
Qed.
