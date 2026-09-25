(** * A partial commutative monoid with explicit definedness.

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
      have it.  That concrete model lives in [Events.HeapModel].

    - Cancellativity is NOT a field of the class.  It is defined separately,
      below, so that a theorem can be checked to be independent of it simply by
      being provable in a section that only assumes [PCM].  [BoolPCM] below is
      a PCM in which cancellativity provably fails.

    ExtLib's [MonoidLaws] is a total, equality-based monoid; it is not a
    replacement for partial composition with pointwise equivalence. *)

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

(** ** A PCM in which cancellativity fails.

    Carrier [bool], composition [orb], always defined, unit [false].  Every PCM
    law holds; cancellativity does not.  This is the evidence that generic
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
