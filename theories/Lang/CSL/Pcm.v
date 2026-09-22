(** * A partial commutative monoid with explicit definedness, and a concrete
      disjoint-heap model.

    Design notes, all of them forced by the evidence collected earlier in this
    project:

    - The composition is *partial*.  We present it, as separation algebras
      usually are, by a total operation [pop] together with a definedness
      predicate [pdef].  This keeps every law a first-order statement and
      avoids reasoning about [option] equalities inside a setoid.

    - The carrier comes with its own equivalence [peq].  This is deliberate:
      the intended heap model is a *map*, and list concatenation is not
      commutative under list equality.  We therefore fix a justified map
      representation (total functions [nat -> option nat]) and a justified map
      equivalence (pointwise equality), and prove commutativity for that
      equivalence rather than assuming it for a representation that does not
      have it.

    - Cancellativity is NOT a field of the class.  It is defined separately,
      below, so that a theorem can be checked to be independent of it simply by
      being provable in a section that only assumes [PCM].  [BoolPCM] below is
      a PCM in which cancellativity provably fails; the transport theorems of
      [Transport.v] instantiate at it. *)

From Stdlib Require Import
  Basics
  Arith.PeanoNat
  Lia
  List
  Relations.

Generalizable All Variables.

(** ** The interface *)
Class PCM (A: Type) := {
  (** the justified equivalence on the carrier *)
  peq : A -> A -> Prop;
  (** definedness / compatibility of a composition *)
  pdef : A -> A -> Prop;
  (** the composition, meaningful exactly when [pdef] holds *)
  pop : A -> A -> A;
  (** the unit *)
  pemp : A;

  peq_refl : forall a, peq a a;
  peq_sym : forall a b, peq a b -> peq b a;
  peq_trans : forall a b c, peq a b -> peq b c -> peq a c;

  (** both [pdef] and [pop] respect the equivalence *)
  pdef_resp : forall a a' b b', peq a a' -> peq b b' -> pdef a b -> pdef a' b';
  pop_resp : forall a a' b b', peq a a' -> peq b b' -> peq (pop a b) (pop a' b');

  (** commutativity, in both components *)
  pdef_comm : forall a b, pdef a b -> pdef b a;
  pop_comm : forall a b, pdef a b -> peq (pop a b) (pop b a);

  (** unit laws *)
  pdef_emp : forall a, pdef pemp a;
  pop_emp : forall a, peq (pop pemp a) a;

  (** associativity, with the definedness bookkeeping made explicit *)
  pdef_assocL : forall a b c, pdef b c -> pdef a (pop b c) -> pdef a b;
  pdef_assocR : forall a b c, pdef b c -> pdef a (pop b c) -> pdef (pop a b) c;
  pdef_assocI : forall a b c, pdef b c -> pdef a b -> pdef (pop a b) c -> pdef a (pop b c);
  pop_assoc : forall a b c,
      pdef b c -> pdef a (pop b c) -> peq (pop a (pop b c)) (pop (pop a b) c)
}.

Declare Scope pcm_scope.
Delimit Scope pcm_scope with pcm.
Notation "a ⊎ b" := (pop a b) (at level 50, left associativity): pcm_scope.
Notation "a # b" := (pdef a b) (at level 70, no associativity): pcm_scope.
Notation "a ≈ b" := (peq a b) (at level 70, no associativity): pcm_scope.
Local Open Scope pcm_scope.

(** Cancellativity is a *separate* property.  Everything proved in a section
    that assumes only [PCM] is, by construction, independent of it. *)
Definition Cancellative (A: Type) `{PCM A} : Prop :=
  forall a b c, a # b -> a # c -> a ⊎ b ≈ a ⊎ c -> b ≈ c.

Section PcmFacts.
  Context {A: Type} `{PCM A}.

  Lemma pop_emp_r: forall a, a # pemp -> a ⊎ pemp ≈ a.
  Proof.
    intros a Hd.
    eapply peq_trans; [apply pop_comm; auto | apply pop_emp].
  Qed.

  Lemma pdef_emp_r: forall a, a # pemp.
  Proof. intro a; apply pdef_comm, pdef_emp. Qed.

  (** The "other" associativity direction, derived. *)
  Lemma pop_assoc': forall a b c,
      b # c -> a # (b ⊎ c) -> (a ⊎ b) ⊎ c ≈ a ⊎ (b ⊎ c).
  Proof. intros; apply peq_sym, pop_assoc; auto. Qed.
End PcmFacts.

(** ** Spatial assertions over an arbitrary PCM *)
Definition assn (A: Type) := A -> Prop.

Section Assertions.
  Context {A: Type} `{PCM A}.

  (** An assertion is *well formed* when it does not distinguish equivalent
      resources.  Every assertion built below is well formed. *)
  Definition AProper (P: assn A) : Prop := forall a b, a ≈ b -> P a -> P b.

  Definition aemp : assn A := fun a => a ≈ pemp.

  Definition asep (P Q: assn A) : assn A :=
    fun a => exists a1 a2, a1 # a2 /\ a ≈ a1 ⊎ a2 /\ P a1 /\ Q a2.

  Definition awand (P Q: assn A) : assn A :=
    fun a => forall b, a # b -> P b -> Q (a ⊎ b).

  Definition atrue : assn A := fun _ => True.

  Lemma aemp_proper: AProper aemp.
  Proof. intros a b Hab Ha; unfold aemp in *; eauto using peq_sym, peq_trans. Qed.

  Lemma asep_proper: forall P Q, AProper (asep P Q).
  Proof.
    intros P Q a b Hab (a1 & a2 & Hd & Heq & HP & HQ).
    exists a1, a2; repeat split; auto.
    eauto using peq_sym, peq_trans.
  Qed.

  (** [⋆] is commutative. *)
  Lemma asep_comm: forall P Q a, asep P Q a -> asep Q P a.
  Proof.
    intros P Q a (a1 & a2 & Hd & Heq & HP & HQ).
    exists a2, a1; repeat split; auto using pdef_comm.
    eapply peq_trans; [exact Heq | apply pop_comm; auto].
  Qed.

  (** [emp] is a left unit, in both directions. *)
  Lemma asep_emp_l: forall P a, AProper P -> P a -> asep aemp P a.
  Proof.
    intros P a HP Ha.
    exists pemp, a; repeat split; auto using pdef_emp, peq_refl.
    - apply peq_sym, pop_emp.
    - unfold aemp; apply peq_refl.
  Qed.

  Lemma asep_emp_l_inv: forall P a, AProper P -> asep aemp P a -> P a.
  Proof.
    intros P a HP (a1 & a2 & Hd & Heq & Hemp & HQ).
    eapply HP; [| exact HQ].
    apply peq_sym.
    eapply peq_trans; [exact Heq |].
    eapply peq_trans; [| apply pop_emp].
    apply pop_resp; auto using peq_refl.
  Qed.

  (** [⋆] is associative, one direction shown (the other is symmetric). *)
  Lemma asep_assoc: forall P Q R a,
      asep P (asep Q R) a -> asep (asep P Q) R a.
  Proof.
    intros P Q R a (a1 & a23 & Hd1 & Heq1 & HP & (a2 & a3 & Hd2 & Heq2 & HQ & HR)).
    assert (Hd1': a1 # (a2 ⊎ a3)) by (eapply pdef_resp; [apply peq_refl | exact Heq2 | exact Hd1]).
    exists (a1 ⊎ a2), a3; repeat split.
    - eapply pdef_assocR; eauto.
    - eapply peq_trans; [exact Heq1 |].
      eapply peq_trans; [| eapply pop_assoc; eauto].
      apply pop_resp; auto using peq_refl.
    - exists a1, a2; repeat split; auto using peq_refl.
      eapply pdef_assocL; eauto.
    - assumption.
  Qed.

  (** Monotonicity: the frame rule of the *spatial* layer. *)
  Lemma asep_mono: forall (P P' Q Q': assn A) a,
      (forall x, P x -> P' x) -> (forall x, Q x -> Q' x) ->
      asep P Q a -> asep P' Q' a.
  Proof.
    intros * HP HQ (a1 & a2 & Hd & Heq & H1 & H2).
    exists a1, a2; auto.
  Qed.

  (** The adjunction, both directions.  [awand] is recorded because the brief
      lists it as optional; nothing downstream depends on it. *)
  Lemma awand_intro: forall (P Q R: assn A),
      (forall a, asep P Q a -> R a) ->
      forall a, P a -> awand Q R a.
  Proof.
    intros P Q R Hpq a Ha b Hd HQ.
    apply Hpq; exists a, b; repeat split; auto using peq_refl.
  Qed.

  Lemma awand_elim: forall (P Q: assn A) a,
      asep (awand P Q) P a -> AProper Q -> Q a.
  Proof.
    intros P Q a (a1 & a2 & Hd & Heq & Hw & HP) HQ.
    eapply HQ; [apply peq_sym; exact Heq |].
    now apply Hw.
  Qed.
End Assertions.

Arguments AProper {A _} P.
Arguments aemp {A _}.
Arguments asep {A _} P Q.
Arguments awand {A _} P Q.
Arguments atrue {A _}.

Notation "P ⋆ Q" := (asep P Q) (at level 55, right associativity): pcm_scope.
Notation "P -⋆ Q" := (awand P Q) (at level 60, right associativity): pcm_scope.

(** ** The concrete model: partial maps as total functions.

    Representation: [nat -> option nat].  Equivalence: pointwise equality.
    Composition: union, defined exactly on disjoint pairs.  This is the
    "justified map representation / equivalence" the brief asks for; it is not
    an association list under list equality, for which commutativity is false. *)
Definition Heap := nat -> option nat.

Definition hemp : Heap := fun _ => None.
Definition heq (h1 h2: Heap) : Prop := forall a, h1 a = h2 a.
Definition hdisj (h1 h2: Heap) : Prop := forall a, h1 a = None \/ h2 a = None.
Definition hunion (h1 h2: Heap) : Heap :=
  fun a => match h1 a with Some v => Some v | None => h2 a end.

Definition hsingle (a v: nat) : Heap :=
  fun b => if Nat.eq_dec a b then Some v else None.
Definition hupd (a v: nat) (h: Heap) : Heap :=
  fun b => if Nat.eq_dec a b then Some v else h b.
Definition hfree (a: nat) (h: Heap) : Heap :=
  fun b => if Nat.eq_dec a b then None else h b.

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

Ltac hcase a := unfold hunion, hupd, hfree, hsingle, hemp in *;
                intros; repeat (destruct (Nat.eq_dec _ _)); subst; auto.

Lemma hdisj_none: forall h1 h2 a v, hdisj h1 h2 -> h1 a = Some v -> h2 a = None.
Proof. intros h1 h2 a v Hd Hs; destruct (Hd a) as [Hn | Hn]; congruence. Qed.

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
    leaving cancellativity out; nothing in [Transport.v] uses this. *)
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

(** ** A PCM in which cancellativity fails.

    Carrier [bool], composition [orb], always defined, unit [false].  Every PCM
    law holds; cancellativity does not.  [Transport.v] instantiates its six
    transport theorems at this PCM, which is the evidence that generic
    transport does not need cancellativity. *)
#[global] Instance BoolPCM : PCM bool.
Proof.
  refine {| peq := @eq bool; pdef := fun _ _ => True; pop := orb; pemp := false |}.
  - reflexivity.
  - intros a b; auto.
  - intros a b c; apply eq_trans.
  - intros a a' b b' Ha Hb _; exact I.
  - intros a a' b b' Ha Hb; now subst.
  - intros a b _; exact I.
  - intros a b _; apply Bool.orb_comm.
  - intros a; exact I.
  - intros a; reflexivity.
  - intros a b c _ _; exact I.
  - intros a b c _ _; exact I.
  - intros a b c _ _ _; exact I.
  - intros a b c _ _; now rewrite Bool.orb_assoc.
Defined.

Theorem bool_pcm_not_cancellative: ~ Cancellative bool.
Proof.
  intro Hc.
  assert (Hd: (true # true)%pcm) by exact I.
  assert (Hd': (true # false)%pcm) by exact I.
  assert (Heq: (true ⊎ true ≈ true ⊎ false)%pcm) by reflexivity.
  specialize (Hc true true false Hd Hd' Heq).
  cbn in Hc; discriminate.
Qed.

(** ** Points-to, and the separation it buys.

    [pto a v] is an assertion about the *owned* resource.  Note the evidence
    from the companion experiment: [CNow] is tree-blind, so this can never be a
    TICL base predicate on its own.  It is a predicate on the resource, lifted
    into the temporal layer only through the owned projection in
    [Transport.v]. *)
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

    Each of the three laws is stated with the footprint hypothesis it needs,
    and [HeapLocal.v] refutes each of them once that hypothesis is dropped. *)

(** A read inside the owned footprint returns the owned value, under every
    compatible frame. *)
Theorem read_local: forall h f a v,
    hdisj h f -> h a = Some v -> hunion h f a = Some v.
Proof. intros h f a v Hd Ha; unfold hunion; now rewrite Ha. Qed.

(** A write inside the owned footprint keeps the frame disjoint ... *)
Theorem write_local_disj: forall h f a v v0,
    hdisj h f -> h a = Some v0 -> hdisj (hupd a v h) f.
Proof.
  intros h f a v v0 Hd Ha x; unfold hupd; destruct (Nat.eq_dec a x).
  - subst; right; eapply hdisj_none; eauto.
  - apply Hd.
Qed.

(** ... and commutes with framing. *)
Theorem write_local_frame: forall h f a v,
    heq (hupd a v (hunion h f)) (hunion (hupd a v h) f).
Proof. intros h f a v x; unfold hupd, hunion; destruct (Nat.eq_dec a x); auto. Qed.

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
