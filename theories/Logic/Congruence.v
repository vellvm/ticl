(*| Congruences [equiv_ticl] of TICL logic |*)
From Stdlib Require Import
  Basics
  Classes.SetoidClass
  Classes.Morphisms.

From Coinduction Require Import all.

From TICL Require Import
  Utils.Utils
  Logic.Semantics
  Logic.Kripke
  Logic.Setoid.

Import TiclNotations.
Local Open Scope ticl_scope.

Generalizable All Variables.

(** Semantic implication and equivalence at a model-compatible formula index. *)
Definition impl_ticl {M E B} {K : Kripke M E B} (X : Type) (b : bool)
    : relation (ticl_at E X b) :=
  fun p q => forall (t : M E B X) w, entails X b p t w -> entails X b q t w.
Definition equiv_ticl {M E B} {K : Kripke M E B} (X : Type) (b : bool)
    : relation (ticl_at E X b) :=
  fun p q => impl_ticl X b p q /\ impl_ticl X b q p.

Section EquivTiclEquivalences.
  Context `{K : Kripke M E B} {X : Type} {b : bool}.
  Global Instance Reflexive_impl_ticl : Reflexive (impl_ticl X b).
  Proof. repeat red; auto. Qed.
  Global Instance Transitive_impl_ticl : Transitive (impl_ticl X b).
  Proof. repeat red; auto. Qed.
  Global Instance Equivalence_equiv_ticl : Equivalence (equiv_ticl X b).
  Proof.
    constructor.
    - split; auto.
    - split; now destruct H.
    - split; destruct H, H0; transitivity y; auto.
  Qed.
  Global Add Parametric Morphism : (impl_ticl X b) with signature
      equiv_ticl X b ==> equiv_ticl X b ==> iff as equiv_ticl_impl.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; intros pp'.
    - transitivity p; auto. transitivity p'; auto.
    - transitivity q'; auto. transitivity q; auto.
  Qed.
  Global Add Parametric Morphism : (equiv_ticl X b) with signature
      equiv_ticl X b ==> equiv_ticl X b ==> iff as equiv_ticl_equiv.
  Proof.
    intros p q pq p' q' pq'; split; intros pp'.
    - now rewrite <- pq, <- pq'.
    - now rewrite pq, pq'.
  Qed.
End EquivTiclEquivalences.

Section EquivTiclFormulas.
  Context `{KMS : Kripke M E B} {X : Type} {b : bool}.
  Arguments impl /.
  Global Add Parametric Morphism : (entails X b) with signature
      impl_ticl X b ==> eq ==> eq ==> impl as impl_ticl_entails.
  Proof. intros p q H t w; exact (H t w). Qed.
  Global Add Parametric Morphism : (entails X b) with signature
      equiv_ticl X b ==> eq ==> eq ==> iff as equiv_ticl_entails.
  Proof. intros p q [pq qp] t w; split; auto. Qed.

  Global Add Parametric Morphism : (@CAnd E (if b then Some X else None))
      with signature impl_ticl X b ==> impl_ticl X b ==> impl_ticl X b
      as impl_ticl_and.
  Proof.
    intros p q pq p' q' pq' t w H; apply ticl_and in H; apply ticl_and.
    destruct H; split; auto.
  Qed.
  Global Add Parametric Morphism : (@CAnd E (if b then Some X else None))
      with signature equiv_ticl X b ==> equiv_ticl X b ==> equiv_ticl X b
      as equiv_ticl_and.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split;
      eapply impl_ticl_and; eassumption.
  Qed.
  Global Add Parametric Morphism : (@COr E (if b then Some X else None))
      with signature impl_ticl X b ==> impl_ticl X b ==> impl_ticl X b
      as impl_ticl_or.
  Proof.
    intros p q pq p' q' pq' t w H; apply ticl_or in H; apply ticl_or.
    destruct H; [left | right]; auto.
  Qed.
  Global Add Parametric Morphism : (@COr E (if b then Some X else None))
      with signature equiv_ticl X b ==> equiv_ticl X b ==> equiv_ticl X b
      as equiv_ticl_or.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split;
      eapply impl_ticl_or; eassumption.
  Qed.
  Global Add Parametric Morphism : (@Cx E (if b then Some X else None))
      with signature eq ==> impl_ticl X false ==> impl_ticl X b ==> impl_ticl X b
      as impl_ticl_next.
  Proof.
    intros [] p q pq p' q' pq' t w H.
    - apply ticl_an in H as (Hp & Hs & Hn); apply ticl_an.
      split2; auto.
    - apply ticl_en in H as (Hp & t' & w' & TR & Hr); apply ticl_en.
      split; [auto | exists t', w'; auto].
  Qed.
  Global Add Parametric Morphism : (@Cx E (if b then Some X else None))
      with signature eq ==> equiv_ticl X false ==> equiv_ticl X b ==> equiv_ticl X b
      as equiv_ticl_next.
  Proof.
    intros c p q [pq qp] p' q' [pq' qp']; split;
      (eapply impl_ticl_next; [reflexivity | eassumption | eassumption]).
  Qed.
  Global Add Parametric Morphism : (@Cu E (if b then Some X else None))
      with signature eq ==> impl_ticl X false ==> impl_ticl X b ==> impl_ticl X b
      as impl_ticl_until.
  Proof.
    intros [] p q pq p' q' pq' t w H.
    - apply ticl_au in H; apply ticl_au; induction H.
      + apply MatchA; auto.
      + apply StepA. destruct H as (Hp & Hs & Hnext).
        destruct H0 as (_ & _ & IH); split2; auto.
    - apply ticl_eu in H; apply ticl_eu; induction H.
      + apply MatchE; auto.
      + apply StepE. destruct H as (Hp & t' & w' & TR & Hr & IH).
        split; [auto | exists t', w'; auto].
  Qed.
  Global Add Parametric Morphism : (@Cu E (if b then Some X else None))
      with signature eq ==> equiv_ticl X false ==> equiv_ticl X b ==> equiv_ticl X b
      as equiv_ticl_until.
  Proof.
    intros c p q [pq qp] p' q' [pq' qp']; split;
      (eapply impl_ticl_until; [reflexivity | eassumption | eassumption]).
  Qed.
End EquivTiclFormulas.

(* Specialize the mode before unifying the formula domain: the conditional
   index cannot itself determine an unknown mode during setoid search. *)
#[global] Hint Extern 1 (Proper _ (entails ?X ?b)) =>
  eapply (@equiv_ticl_entails_Proper _ _ _ _ X b) : typeclass_instances.
#[global] Hint Extern 1 (Proper _ (entails ?X ?b)) =>
  eapply (@impl_ticl_entails_Proper _ _ _ _ X b) : typeclass_instances.
#[global] Hint Extern 1 (Proper _ (entailsL ?X)) =>
  eapply (@equiv_ticl_entails_Proper _ _ _ _ X false)
  : typeclass_instances.
#[global] Hint Extern 1 (Proper _ (entailsL ?X)) =>
  eapply (@impl_ticl_entails_Proper _ _ _ _ X false)
  : typeclass_instances.
#[global] Hint Extern 1 (Proper _ (@entailsR _ _ _ _ ?X)) =>
  eapply (@equiv_ticl_entails_Proper _ _ _ _ X true)
  : typeclass_instances.
#[global] Hint Extern 1 (Proper _ (@entailsR _ _ _ _ ?X)) =>
  eapply (@impl_ticl_entails_Proper _ _ _ _ X true)
  : typeclass_instances.

Section EquivTiclGlobal.
  Context `{KMS : Kripke M E B} {X : Type}.
  Global Add Parametric Morphism : (@Cg E) with signature
      eq ==> impl_ticl X false ==> impl_ticl X false as impl_ticl_global.
  Proof.
    intros [] p q Heq t w; rewrite 2 unfold_entails; cbn [entails_step].
    - assert (H : agcF (entails X false p) <= agcF (entails X false q)).
      { intros R t' w' (Hy & Hs & Htr); split2; auto. }
      pose proof (@gfp_leq _ _ _ _ H) as G; cbn in G; apply G.
    - assert (H : egcF (entails X false p) <= egcF (entails X false q)).
      { intros R t' w' (Hy & t_ & w_ & TR & Hr); split; auto.
        exists t_, w_; auto. }
      pose proof (@gfp_leq _ _ _ _ H) as G; cbn in G; apply G.
  Qed.
  Global Add Parametric Morphism : (@Cg E) with signature
      eq ==> equiv_ticl X false ==> equiv_ticl X false as equiv_ticl_global.
  Proof.
    intros c p q [pq qp]; split; eapply impl_ticl_global;
      [reflexivity | exact pq | reflexivity | exact qp].
  Qed.
  Lemma ret_impl_ticl (P Q : X -> World E -> Prop) :
    (forall x w, P x w -> Q x w) -> impl_ticl X true (CRet P) (CRet Q).
  Proof.
    intros HPQ t w H; apply ticl_ret in H as (x & HR & Hd).
    apply ticl_ret; exists x; split; auto.
  Qed.
  Lemma aur_ret_mono (t : M E B X) w (phi : ticll E) (P Q : X -> World E -> Prop) :
    (forall x w, P x w -> Q x w) ->
    <( t, w |=R phi AU ret P )> -> <( t, w |=R phi AU ret Q )>.
  Proof.
    intros HPQ H; apply ticl_au in H; apply ticl_au; induction H.
    - apply MatchA; eapply ret_impl_ticl; eassumption.
    - apply StepA; exact H0.
  Qed.
  Lemma aur_done_mono (t : M E B X) w (phi : ticll E) (P Q : X -> World E -> Prop) :
    (forall x w, P x w -> Q x w) ->
    auc (entails X false phi) (fun _ wd => done_with P wd) t w ->
    auc (entails X false phi) (fun _ wd => done_with Q wd) t w.
  Proof.
    intros HPQ H; eapply auc_mono_r; [|exact H].
    intros t' wd Hd; exact (done_with_mono P Q HPQ wd Hd).
  Qed.
End EquivTiclGlobal.

(** * Equations of TICL suffix formulas [ticlr] *)
Section TiclEquations.
  Context `{KMS: Kripke M E B} {X: Type} {b : bool}.
  Abbreviation MS := (M E B X).
  Abbreviation MP := (MS -> World E -> Prop).
  Infix "⋖" := (@impl_ticl M E B KMS X b) (at level 58, left associativity).
  Infix "⩸" := (@equiv_ticl M E B KMS X b) (at level 58, left associativity).

  (** Left injection of [p] into [p \/ q] *)
  Lemma impl_or_injL: forall (p q: ticl_at E X b),
      impl_ticl X b p (COr p q).
  Proof.
    intros p q t w R.
    apply ticl_or.
    now left.
  Qed.

  (** Right injection of [q] into [p \/ q] *)
  Lemma impl_or_injR: forall (p q: ticl_at E X b),
      impl_ticl X b q (COr p q).
  Proof.
    intros p q t w R.
    apply ticl_or.
    now right.
  Qed.
  
  (** Or and implication *)
  Lemma impl_or_impl_or: forall (p q R : ticl_at E X b),      
      impl_ticl X b (COr p q) R -> impl_ticl X b p R \/ impl_ticl X b q R.
  Proof.
    unfold impl_ticl.
    intros.
    left; intros.
    apply H.
    apply ticl_or.
    now left.
  Qed.

  (** And and implication *)
  Lemma impl_or_impl_and: forall (p q R : ticl_at E X b),
      impl_ticl X b p R /\ impl_ticl X b q R ->
      impl_ticl X b (COr p q) R.
  Proof.
    unfold impl_ticl.
    intros.
    destruct H.
    apply ticl_or in H0.
    destruct H0.
    - now apply H.
    - now apply H1.
  Qed.

  (** If [p] holds now and either [q] or [r] next, then this implies [p AN (q \/ r)].
      Intuitively, we can have a trace where [p] holds now and either [q] or [r] holds next.
      But if we chose [q] to hold next, we lose the information that [r] holds next.
  *)
  Lemma impl_an_or: forall (p : ticll E) (q r : ticl_at E X b),
      impl_ticl X b (COr (Cx Q_A p q) (Cx Q_A p r)) (Cx Q_A p (COr q r)).
  Proof.
    unfold impl_ticl.
    intros p q r t' w' Hn.
    apply ticl_or in Hn as [Hn | Hn].
    - apply ticl_an; 
        apply ticl_an in Hn as (Hp & Hs & H); split2; auto with ticl.
      intros t_ w_ TR_.
      apply ticl_or; left; auto with ticl.
    - apply ticl_an; 
        apply ticl_an in Hn as (Hp & Hs & H); split2; auto with ticl.
      intros t_ w_ TR_.
      apply ticl_or; right; auto with ticl.
  Qed.
  
  (** [p AU q] is equivalent to [q] or [p] holds now and [p AU q] holds next. *)
  Lemma equiv_au_an (p : ticll E) (q : ticl_at E X b) :
      equiv_ticl X b (Cu Q_A p q) (COr q (Cx Q_A p (Cu Q_A p q))).
  Proof.
    split; intros t w H.
    - apply ticl_au in H; apply ticl_or; destruct H as [t w Hq | t w Hs].
      + now left.
      + right; apply ticl_an; destruct Hs as (Hp & Hs & Hn).
        split2; auto. intros; apply ticl_au; auto.
    - apply ticl_or in H as [Hq | Hn]; apply ticl_au.
      + now apply MatchA.
      + apply ticl_an in Hn as (Hp & Hs & Hn); apply StepA; split2; auto.
        intros; apply ticl_au; auto.
  Qed.

  (** [p EU q] is equivalent to [q] or [p] holds now and [p EU q] holds next. *)
  Lemma equiv_eu_en (p : ticll E) (q : ticl_at E X b) :
      equiv_ticl X b (Cu Q_E p q) (COr q (Cx Q_E p (Cu Q_E p q))).
  Proof.
    split; intros t w H.
    - apply ticl_eu in H; apply ticl_or; destruct H as [t w Hq | t w Hs].
      + now left.
      + right; apply ticl_en; destruct Hs as (Hp & t' & w' & TR & Hr).
        split; [exact Hp | exists t', w'; split; [exact TR | now apply ticl_eu]].
    - apply ticl_or in H as [Hq | Hn]; apply ticl_eu.
      + now apply MatchE.
      + apply ticl_en in Hn as (Hp & t' & w' & TR & Hr).
        apply StepE; split; [exact Hp | exists t', w'; split; [exact TR | now apply ticl_eu]].
  Qed.

  (** [p AU (p AN q)] implies [p AN (p AU q)].
      Intuitively, we move the [AN] from the end to the beginning. *)
  Lemma impl_auan_anau: forall (p: ticll E) (q: ticl_at E X b),
      impl_ticl X b (Cu Q_A p (Cx Q_A p q)) (Cx Q_A p (Cu Q_A p q)).
  Proof.
    intros p q t w H.
    cinduction H.
    - apply ticl_an in Hp as (? & ? & ?).
      apply ticl_an.
      split2; auto.
      intros t' w' TR.
      apply equiv_au_an.
      rewrite ticl_or.
      left.
      now apply H1.
    - rewrite ticl_an.
      split2; auto.
      intros t' w' TR.
      apply equiv_au_an; apply ticl_or.
      right; auto.
  Qed.

  (** [p EU (p EN q)] implies [p EN (p EU q)].
      Intuitively, we move the [EN] from the end to the beginning. *)
  Lemma impl_euen_eneu: forall (p: ticll E) (q: ticl_at E X b),
      impl_ticl X b (Cu Q_E p (Cx Q_E p q)) (Cx Q_E p (Cu Q_E p q)).
  Proof.
    intros p q t w H.
    cinduction H.
    - apply ticl_en in Hp as (? & t' & w' & TR & ?).
      apply ticl_en.
      split; auto with ticl.
      exists t', w'.
      split; auto with ticl.
      rewrite equiv_eu_en, ticl_or.
      now left.
    - rewrite ticl_en.
      split; auto with ticl.
      exists t0, w0.
      split; auto with ticl.
      rewrite equiv_eu_en, ticl_or.
      right; auto with ticl.
  Qed.

  (** [p AU q] is idempotent. *)
  Lemma equiv_au_idem: forall (p: ticll E) (q: ticl_at E X b),
      equiv_ticl X b (Cu Q_A p q) (Cu Q_A p (Cu Q_A p q)).
  Proof.
    split; intros * t w H; cinduction H.
    - apply equiv_au_an, ticl_or.
      left.
      apply equiv_au_an, ticl_or.
      now left.
    - apply equiv_au_an, ticl_or.
      right.
      apply ticl_an; split; auto.
    - apply Hp.
    - apply equiv_au_an, ticl_or; right; apply ticl_an; split; auto.
  Qed.

  (** [p EU q] is idempotent. *)
  Lemma equiv_eu_idem: forall (p: ticll E) (q: ticl_at E X b),
      equiv_ticl X b (Cu Q_E p q) (Cu Q_E p (Cu Q_E p q)).
  Proof.
    split; unfold impl_ticl; intros; cinduction H.
    - apply equiv_eu_en, ticl_or; left.
      apply equiv_eu_en, ticl_or.
      now left.
    - apply equiv_eu_en, ticl_or; right.
      apply ticl_en; split; eauto.
    - apply Hp.
    - apply equiv_eu_en, ticl_or; right.
      apply ticl_en; split; eauto.
  Qed.

End TiclEquations.


(** * Equations of TICL prefix formulas [ticll] *)
Section TicllEquations.
  Context `{KMS: Kripke M E B} {X: Type}.
  Abbreviation MS := (M E B X).
  Abbreviation MP := (MS -> World E -> Prop).
  Infix "⋖" := (impl_ticl X false (K:=KMS)) (at level 58, left associativity).
  Infix "⩸" := (equiv_ticl X false (K:=KMS)) (at level 58, left associativity).

  (** Unfold a [vis] formula into a [now] formula *)
  Lemma equivl_vis_now: forall φ,
      <( vis φ )> ⩸ <( now {fun w => exists Y (e: E Y) (v: Y), w = Obs e v /\ φ Y e v} )>.
  Proof.
    intros; split; unfold impl_ticl; rewrite ?unfold_entails; cbn [entails_step].
    - intros * [[] Hd]; ddestruction Hd.
      split; [|constructor].
      exists Y, e, v; auto.
    - intros * [(Y & e & v & -> & Hφ) Hd]; split; auto with ticl.
  Qed.

  (** [AU] either [q] holds or [p] holds and [p AU q] holds next *)

  (** [EU] either [q] holds or [p] holds and [p EU q] holds next *)

  (** [⊤ /\ p] is the identity of [/\] *)
  Lemma equivl_and_idL: forall (p: ticll E),
      <( ⊤ /\ p )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - split; auto.
      now apply ticl_not_done in Hp.
  Qed.

  (** [p /\ ⊤] is the identity of [/\] *)
  Lemma equivl_and_idR: forall (p: ticll E),
      <( p /\ ⊤ )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - split; auto.
      now apply ticl_not_done in Hp.
  Qed.

  (** [⊥ \/ p] is the identity of [\/] *)
  Lemma equivl_or_idL: forall (p: ticll E),
      <( ⊥ \/ p )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - apply ticl_or in Hp as [HF | Hp]; [exfalso; eapply ticll_sound; exact HF | exact Hp].
    - apply ticl_or; now right.
  Qed.

  (** [p \/ ⊥] is the identity of [\/] *)
  Lemma equivl_or_idR: forall (p: ticll E),
      <( p \/ ⊥ )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - apply ticl_or in Hp as [Hp | HF]; [exact Hp | exfalso; eapply ticll_sound; exact HF].
    - apply ticl_or; now left.
  Qed.

  (** [AG p] is equivalent to [p] holds, and next [p AN (AG p)] holds. *)
  Lemma equivl_ag_an: forall (p: ticll E),
      <( AG p )> ⩸ <( p AN (AG p) )>.
  Proof.
    split; intros t w Hp.
    - step in Hp; inv Hp; split; auto.
    - destruct Hp.
      destruct H0; step; now constructor.
  Qed.

  (** [EG p] is equivalent to [p] holds, and next [p EN (EG p)] holds. *)
  Lemma equivl_eg_en: forall (p: ticll E),
      <( EG p )> ⩸ <( p EN (EG p) )>.
  Proof.
    split; intros t w Hp.
    - split; step in Hp; inv Hp; auto.
    - destruct Hp.
      step; now constructor.
  Qed.

  (** [p AU (p AN q)] implies [p AN (p AU q)].
       Intuitively, we move the [AN] from the end to the beginning. *)

  (** If [AG p] holds always then [p] holds now. *)
  Lemma impll_ag_refl: forall (p: ticll E),
      <( AG p )> ⋖ p.
  Proof.
    unfold impl_ticl; intros.
    rewrite equivl_ag_an, ticl_an in H.
    now destruct H.
  Qed.

  (** If [EG p] holds always then [p] holds now. *)
  Lemma impll_eg_refl: forall (p: ticll E),
      <( EG p )> ⋖ p.
  Proof.
    unfold impl_ticl; intros.
    rewrite equivl_eg_en, ticl_en in H.
    now destruct H.
  Qed.

  (** [p AU q] is idempotent. *)

  (** [p EU q] is idempotent. *)

  (** [AG p] is idempotent. *)
  Lemma equivl_ag_idem: forall (p: ticll E),
      <( AG p )> ⩸ <( AG (AG p) )>.
  Proof.
    split.
    - unfold impl_ticl; intros;
        revert H; revert t w; coinduction R CIH; intros t' w' Hag.
      constructor; auto.
      apply equivl_ag_an in Hag; rewrite ticl_an in Hag; destruct Hag, H0.
      split; auto.
    - apply impll_ag_refl.
  Qed.

  (** [EG p] is idempotent. *)
  Lemma equivl_eg_idem: forall (p: ticll E),
      <( EG p )> ⩸ <( EG (EG p) )>.
  Proof.
    split.
    - unfold impl_ticl; intros;
        revert H; revert t w; coinduction R CIH; intros t' w' Heg.
      constructor; auto.
      apply equivl_eg_en in Heg; rewrite ticl_en in Heg; destruct Heg, H0 as (t_ & w_  & TR & H0).
      exists t_, w_; intuition.
    - apply impll_eg_refl.
  Qed.

  (** [AG (p /\ q)] is equivalent to [AG p /\ AG q]. *)
  Lemma equivl_and_ag: forall p q,
      <( AG (p /\ q) )> ⩸ <( AG p /\ AG q )>.
  Proof.
    intros p q; split.
    - intros t w H; apply ticl_and; split.
      + eapply impl_ticl_global; [reflexivity | | exact H].
        intros t' w' Hpq; apply ticl_and in Hpq; exact (proj1 Hpq).
      + eapply impl_ticl_global; [reflexivity | | exact H].
        intros t' w' Hpq; apply ticl_and in Hpq; exact (proj2 Hpq).
    - unfold impl_ticl; intros; revert H; revert t w.
      coinduction R CIH; intros.
      apply ticl_and in H as (Hp & Hq).
      apply equivl_ag_an, ticl_an in Hp as (Hp & Hs & Hgp).
      apply equivl_ag_an, ticl_an in Hq as (Hq & _ & Hgq).
      split; [apply ticl_and; auto | split; [exact Hs |]].
      intros t' w' TR; apply CIH; apply ticl_and; split; auto.
  Qed.

  (** [EG (p /\ q)] implies [EG p /\ EG q] but is not equivalent like [AG].
      This is because for [EG (p /\ q)] we can have a trace where both [p] and [q] hold now and next,
      but for [EG p /\ EG q] we must chose either [p] or [q] to hold always.
  *)
  Lemma impll_and_eg: forall p q,
      <( EG (p /\ q) )> ⋖ <( EG p /\ EG q )>.
  Proof.
    intros p q t w H; apply ticl_and; split.
    - eapply impl_ticl_global; [reflexivity | | exact H].
      intros t' w' Hpq; apply ticl_and in Hpq; exact (proj1 Hpq).
    - eapply impl_ticl_global; [reflexivity | | exact H].
      intros t' w' Hpq; apply ticl_and in Hpq; exact (proj2 Hpq).
  Qed.

  (** [AG (p \/ q)] implies [AG p \/ AG q].
      Intuitively, we can have a trace where [p] holds always or [q] holds always.
      But if we chose [p] to hold always, we lose the information that [q] holds always.
  *)
  Lemma impll_or_ag: forall p q,
      <( AG p \/ AG q )> ⋖ <( AG (p \/ q) )>.
  Proof.
    intros p q t w H; apply ticl_or in H as [H | H].
    - eapply impl_ticl_global; [reflexivity | | exact H].
      intros t' w' Hp; apply ticl_or; left; exact Hp.
    - eapply impl_ticl_global; [reflexivity | | exact H].
      intros t' w' Hp; apply ticl_or; right; exact Hp.
  Qed.

  (** [EG (p \/ q)] implies [EG p \/ EG q].
      Intuitively, we can have a trace where [p] holds always or [q] holds always.
      But if we chose [p] to hold always, we lose the information that [q] holds always.
  *)
  Lemma impll_or_eg: forall p q,
      <( EG p \/ EG q )> ⋖ <( EG (p \/ q) )>.
  Proof.
    intros p q t w H; apply ticl_or in H as [H | H].
    - eapply impl_ticl_global; [reflexivity | | exact H].
      intros t' w' Hp; apply ticl_or; left; exact Hp.
    - eapply impl_ticl_global; [reflexivity | | exact H].
      intros t' w' Hp; apply ticl_or; right; exact Hp.
  Qed.

End TicllEquations.


Infix "⋖L" := (impl_ticl _ false) (in custom ticl at level 79, left associativity) : ticl_scope.
Infix "⩸L" := (equiv_ticl _ false) (in custom ticl at level 79, left associativity) : ticl_scope.
Infix "⋖R" := (impl_ticl _ true) (in custom ticl at level 79, left associativity) : ticl_scope.
Infix "⩸R" := (equiv_ticl _ true) (in custom ticl at level 79, left associativity) : ticl_scope.
