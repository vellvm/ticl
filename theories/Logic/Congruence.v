(*| Congruences [equiv_ticl] of TICL logic |*)
From Coq Require Import
  Basics
  Classes.SetoidClass
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice tactics.

From TICL Require Import
  Utils.Utils
  Events.Core
  Logic.Semantics
  Logic.Kripke
  Logic.Setoid.

Import TiclNotations.
Local Open Scope ticl_scope.

Generalizable All Variables.

(*| Semantic implication of ticll formulas [p ⪟ q] |*)
Definition impl_ticll {M} `{HE: Encode E} {K: Kripke M E} (X: Type): relation (ticll E) :=
  fun p q => forall (t: M E HE X) (w: World E), entailsL X p t w -> entailsL X q t w.

(*| Semantic implication of ticlr formulas [p ⪟ q] |*)
Definition impl_ticlr {M} `{HE: Encode E} {K: Kripke M E} (X: Type): relation (ticlr E X) :=
  fun p q => forall (t: M E HE X) (w: World E), entailsR p t w -> entailsR q t w.

(*| Semantic equivalence of ticll formulas [p ≃ q] |*)
Definition equiv_ticll {M} `{HE: Encode E} {K: Kripke M E} (X: Type): relation (ticll E) :=
  fun p q => impl_ticll X p q /\ impl_ticll X q p.

(*| Semantic equivalence of ticlr formulas [p ≃ q] |*)
Definition equiv_ticlr {M} `{HE: Encode E} {K: Kripke M E} (X: Type): relation (ticlr E X) :=
  fun p q => impl_ticlr X p q /\ impl_ticlr X q p.

Section EquivTiclEquivalences.
  Context `{K: Kripke M E} {X: Type}.
  Notation impl_ticll := (@impl_ticll M E HE K X).
  Notation impl_ticlr := (@impl_ticlr M E HE K X).
  Notation equiv_ticll := (@equiv_ticll M E HE K X).
  Notation equiv_ticlr := (@equiv_ticlr M E HE K X).

  Global Instance Reflexive_impl_ticll:
    Reflexive impl_ticll.
  Proof. repeat red; auto. Qed.

  Global Instance Transitive_impl_ticll:
    Transitive impl_ticll.
  Proof. repeat red; auto. Qed.

  Global Instance Reflexive_impl_ticlr:
    Reflexive impl_ticlr.
  Proof. repeat red; auto. Qed.

  Global Instance Transitive_impl_ticlr:
    Transitive impl_ticlr.
  Proof. repeat red; auto. Qed.

  Global Instance Equivalence_equiv_ticll:
    Equivalence equiv_ticll.
  Proof.
    constructor.
    - split; auto.
    - split; now destruct H.
    - split; destruct H, H0;
        transitivity y; auto.
  Qed.

  Global Instance Equivalence_equiv_ticlr:
    Equivalence equiv_ticlr.
  Proof.
    constructor.
    - split; auto.
    - split; now destruct H.
    - split; destruct H, H0;
        transitivity y; auto.
  Qed.

  (*| [impl_ticll] proper under [equiv_ticll] |*)
  Global Add Parametric Morphism : impl_ticll with signature
         equiv_ticll ==> equiv_ticll ==> iff as equiv_ticll_impl.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split;
      intros pp'.
    - transitivity p; auto.
      transitivity p'; auto.
    - transitivity q'; auto.
      transitivity q; auto.
  Qed.

  (*| [impl_ticll] proper under [equiv_ticll] |*)
  Global Add Parametric Morphism : equiv_ticll with signature
         equiv_ticll ==> equiv_ticll ==> iff as equiv_ticll_equiv.
  Proof.
    intros p q pq p' q' pq'; split;
      intros pp'.
    - now rewrite <- pq, <- pq'.
    - now rewrite pq, pq'.
  Qed.

  (*| [impl_ticlr] proper under [equiv_ticlr] |*)
  Global Add Parametric Morphism : impl_ticlr with signature
         equiv_ticlr ==> equiv_ticlr ==> iff as equiv_ticlr_impl.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split;
      intros pp'.
    - transitivity p; auto.
      transitivity p'; auto.
    - transitivity q'; auto.
      transitivity q; auto.
  Qed.

  (*| [impl_ticll] proper under [equiv_ticll] |*)
  Global Add Parametric Morphism : equiv_ticlr with signature
         equiv_ticlr ==> equiv_ticlr ==> iff as equiv_ticlr_equiv.
  Proof.
    intros p q pq p' q' pq'; split;
      intros pp'.
    - now rewrite <- pq, <- pq'.
    - now rewrite pq, pq'.
  Qed.
End EquivTiclEquivalences.

(*| Equations of TICL (left) |*)
Section EquivTicllFormulas.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Notation impl_ticll := (@impl_ticll M E HE KMS X).
  Notation equiv_ticll := (@equiv_ticll M E HE KMS X).

  Arguments impl /.
  (*| Rewriting [equiv_ticl] over [entailsF] |*)
  Global Add Parametric Morphism: (entailsL X)
         with signature (impl_ticll ==> eq ==> eq ==> impl)
           as impl_ticll_entailsL.
  Proof. intro x; induction x; intros y φy; cbn; intros; auto. Qed.

  Global Add Parametric Morphism: (entailsL X)
         with signature (equiv_ticll ==> eq ==> eq ==> iff)
           as equiv_ticll_entailsL.
  Proof. intros x y [Hxy Hyx]; split; intro H; auto. Qed.

  (*| Congruences over equiv_ticl |*)
  Global Add Parametric Morphism: CAndL
         with signature impl_ticll ==> impl_ticll ==> impl_ticll
           as impl_ticll_equiv_and.
  Proof.
    intros p q EQpq p' q' EQpq'; unfold impl_ticll; intros.
    rewrite unfold_entailsL in *; destruct H; split; auto.
  Qed.

  Global Add Parametric Morphism: CAndL
         with signature equiv_ticll ==> equiv_ticll ==> equiv_ticll
           as equiv_ticll_equiv_and.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; [rewrite pq', pq | rewrite qp, qp']; reflexivity.
  Qed.

  Global Add Parametric Morphism: COrL
         with signature impl_ticll ==> impl_ticll ==> impl_ticll
           as impl_ticll_equiv_or.
  Proof.
    intros p q EQpq p' q' EQpq'; unfold impl_ticll; intros.
    rewrite unfold_entailsL in *; destruct H; auto.
  Qed.

  Global Add Parametric Morphism: COrL
         with signature equiv_ticll ==> equiv_ticll ==> equiv_ticll
           as equiv_ticll_equiv_or.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split.
    - rewrite pq', pq; reflexivity.
    - rewrite qp, qp'; reflexivity.
  Qed.

  Global Add Parametric Morphism: CxL
         with signature eq ==> impl_ticll ==> impl_ticll ==> impl_ticll as impl_ticll_next.
  Proof.
    intros [] p q pq; unfold impl_ticll; intros.
    - rewrite unfold_entailsL in H |- *; destruct H as (Hp & Hs & H).
      split2; auto.
    - rewrite unfold_entailsL in H |- *; destruct H as (Hp & t' & w' & TR & ?).
      split; [auto| exists t', w'; intuition].
  Qed.

  Global Add Parametric Morphism: CxL
      with signature eq ==> equiv_ticll ==> equiv_ticll ==> equiv_ticll as equiv_ticll_next.
  Proof.
    intros [] p q [pq qp] p' q' [pq' qp']; split; try (rewrite pq, pq' || rewrite qp, qp'); reflexivity.
  Qed.

  Global Add Parametric Morphism: CuL
         with signature eq ==> impl_ticll ==> impl_ticll ==> impl_ticll
           as impl_ticll_until.
  Proof.
    intros [] p q Hpq p' q' Hpq'; unfold impl_ticll; intros * Hu.
    - cinduction Hu; rewrite unfold_entailsL.
      + left; auto.
      + right; auto.
        split2; auto.
    - cinduction Hu; rewrite unfold_entailsL.
      + left; auto.
      + right; split; auto.
        exists t0, w0; auto.
  Qed.

  Global Add Parametric Morphism: CuL
      with signature eq ==> equiv_ticll ==> equiv_ticll ==> equiv_ticll as equiv_ticll_until.
  Proof.
    intros [] p q [pq qp] p' q' [pq' qp']; split; try (rewrite pq, pq' || rewrite qp, qp'); reflexivity.
  Qed.

  Global Add Parametric Morphism: Cg
         with signature (eq ==> impl_ticll ==> impl_ticll)
           as impl_ticll_global.
  Proof.
    intros [] p q Heq; unfold impl_ticll;
      coinduction R CIH; intros; step in H.
    - destruct H as (Hy & Hs & Htr); constructor.
      + now rewrite Heq in Hy.
      + rewrite Heq in Hy.
        split; auto.
        intros t' w' TR.
        apply CIH.
        rewrite unfold_entailsL; auto.
    - destruct H as (Hy & t' & w' & TR & ?); constructor.
      + now rewrite Heq in Hy.
      + exists t', w'; split; auto.
  Qed.

  Global Add Parametric Morphism: Cg
         with signature (eq ==> equiv_ticll ==> equiv_ticll)
           as equiv_ticll_global.
  Proof.
    intros c p q [pq qp]; split; try (rewrite pq || rewrite qp); reflexivity.
  Qed.

End EquivTicllFormulas.

Section EquivTiclrFormulas.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Notation impl_ticlr := (@impl_ticlr M E HE KMS X).
  Notation equiv_ticlr := (@equiv_ticlr M E HE KMS X).

  (*| Rewriting [impl_ticl], [equiv_ticl] over [entailsR] |*)
  Arguments impl /.
  Global Add Parametric Morphism: entailsR
         with signature (impl_ticlr ==> eq ==> eq ==> impl)
           as impl_ticlr_entailsR.
  Proof. intro x; induction x; intros y φy; cbn; intros; auto. Qed.

  Global Add Parametric Morphism: entailsR
         with signature (equiv_ticlr ==> eq ==> eq ==> iff)
           as equiv_ticll_entailsR.
  Proof. intros x y [Hxy Hyx]; split; intro H; auto. Qed.

  (*| Congruences over equiv_ticlr |*)
  Global Add Parametric Morphism: CAndR
         with signature impl_ticlr ==> impl_ticlr ==> impl_ticlr
           as impl_ticlr_equiv_andr.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ticll, impl_ticlr in *; intros.
    rewrite unfold_entailsR in *; destruct H; split; auto.
  Qed.

  Global Add Parametric Morphism: CAndR
         with signature equiv_ticlr ==> equiv_ticlr ==> equiv_ticlr
           as equiv_ticlr_equiv_andr.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; [rewrite pq', pq | rewrite qp, qp']; reflexivity.
  Qed.

  Global Add Parametric Morphism: COrR
         with signature impl_ticlr ==> impl_ticlr ==> impl_ticlr
           as impl_ticlr_equiv_orr.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ticlr in *; intros.
    rewrite unfold_entailsR in *; destruct H.
    - left; now apply pq.
    - right; now apply pq'.
  Qed.

  Global Add Parametric Morphism: COrR
         with signature equiv_ticlr  ==> equiv_ticlr ==> equiv_ticlr
           as equiv_ticlr_equiv_orr.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; [rewrite pq', pq | rewrite qp, qp']; reflexivity.
  Qed.

  Global Add Parametric Morphism: CImplR
         with signature flip (impl_ticll X) ==> impl_ticlr ==> impl_ticlr
           as impl_ticlr_equiv_implL.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ticlr in *; intros.
    rewrite unfold_entailsR in *; intro Ha; now apply pq', H, pq.
  Qed.

  Global Add Parametric Morphism: CImplR
         with signature impl_ticll X ==> flip impl_ticlr ==> flip impl_ticlr
           as impl_ticlr_equiv_implR.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ticlr in *; intros.
    rewrite unfold_entailsR in *; intro Ha; now apply pq', H, pq.
  Qed.

  Global Add Parametric Morphism: CImplR
         with signature equiv_ticll X ==> equiv_ticlr ==> equiv_ticlr
           as equiv_ticlr_equiv_implR.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; unfold equiv_ticlr; split.
    - rewrite <- qp, pq'; reflexivity.
    - rewrite <- pq, qp'; reflexivity.
  Qed.

  Global Add Parametric Morphism: CxR
         with signature eq ==> impl_ticll X ==> impl_ticlr ==> impl_ticlr as impl_ticlr_next.
  Proof.
    intros [] p q pq p' q' pq'; unfold impl_ticlr; intros.
    - destruct H as (Hp & Hs & H).
      split2; auto; intros * TR; intuition.
    - destruct H as (Hp & t' & w' & TR & ?).
      split; auto.
      exists t', w'; intuition.
  Qed.

  Global Add Parametric Morphism: CxR
      with signature eq ==> equiv_ticll X ==> equiv_ticlr ==> equiv_ticlr as equiv_ticlr_next.
  Proof.
    intros [] p q [pq qp] p' q' [pq' qp']; split; try (rewrite pq, pq' || rewrite qp, qp'); reflexivity.
  Qed.

  Global Add Parametric Morphism: CuR
         with signature eq ==> impl_ticll X ==> impl_ticlr ==> impl_ticlr as impl_ticlr_until.
  Proof.
    intros [] p q Hpq p' q' Hpq'; unfold impl_ticlr; intros * Hu.
    - cinduction Hu; rewrite unfold_entailsR; [left; auto | right; split2]; auto.
    - cinduction Hu; rewrite unfold_entailsR; [left; auto | right; split]; eauto.
  Qed.

  Global Add Parametric Morphism: CuR
      with signature eq ==> equiv_ticll X ==> equiv_ticlr ==> equiv_ticlr as equiv_ticlr_until.
  Proof.
    intros [] p q [pq qp] p' q' [pq' qp']; split; try (rewrite pq, pq' || rewrite qp, qp'); reflexivity.
  Qed.


        
End EquivTiclrFormulas.

(*| Equations of TICL (left) |*)
Section TicllEquations.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Infix "⋖" := (impl_ticll X (K:=KMS)) (at level 58, left associativity).
  Infix "⩸" := (equiv_ticll X (K:=KMS)) (at level 58, left associativity).

  Lemma ticll_vis_now: forall φ,
      <( vis φ )> ⩸ <( now {fun w => exists (e: E) (v: encode e), w = Obs e v /\ φ e v} )>.
  Proof.
    intros; split; unfold impl_ticll; rewrite ?unfold_entailsF.
    - intros * [[] Hd]; ddestruction Hd.
      split; [|constructor].
      exists e, v; auto.
    - intros * [(e & v & -> & Hφ) Hd]; split; auto with ticl.
  Qed.

  Lemma ticll_au_an: forall (p q: ticll E),
      <( p AU q )> ⩸ <( q \/ (p AN (p AU q)) )>.
  Proof.
    intros p q; split; intros t w Hind.
    - cinduction Hind.
      + now left.
      + right; split; auto.
    - apply ticll_or in Hind as [Hind | Hind].
      + now left.
      + rewrite unfold_entailsL.
        now right.
  Qed.

  Lemma ticll_eu_en: forall (p q: ticll E),
      <( p EU q )> ⩸ <( q \/ (p EN (p EU q)) )>.
  Proof.
    intros p q; split; intros t w Hind.
    - cinduction Hind.
      + now left.
      + rewrite ticll_or; right.
        rewrite ticll_en; split; auto.
        exists t0, w0; split; auto.
    - rewrite unfold_entailsL in Hind; destruct Hind.
      + now left.
      + destruct H.
        now right.
  Qed.

  Lemma ticll_and_idL: forall (p: ticll E),
      <( ⊤ /\ p )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - split; auto.
      now apply ticll_not_done in Hp.
  Qed.

  Lemma ticll_and_idR: forall (p: ticll E),
      <( p /\ ⊤ )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - split; auto.
      now apply ticll_not_done in Hp.
  Qed.

  Lemma ticll_or_idL: forall (p: ticll E),
      <( ⊥ \/ p )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - now right.
  Qed.

  Lemma ticll_or_idR: forall (p: ticll E),
      <( p \/ ⊥ )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - now left.
  Qed.

  Lemma ticll_ag_an: forall (p: ticll E),
      <( AG p )> ⩸ <( p AN (AG p) )>.
  Proof.
    split; intros t w Hp.
    - step in Hp; inv Hp; split; auto.
    - destruct Hp.
      destruct H0; step; now constructor.
  Qed.

  Lemma ticll_eg_en: forall (p: ticll E),
      <( EG p )> ⩸ <( p EN (EG p) )>.
  Proof.
    split; intros t w Hp.
    - split; step in Hp; inv Hp; auto.
    - destruct Hp.
      step; now constructor.
  Qed.

  Lemma ticll_auan_anau: forall (p q: ticll E),
      <( p AU (p AN q) )> ⋖ <( p AN (p AU q) )>.
  Proof.
    intros * t w H.
    cinduction H.
    + apply ticll_an in Hp as (? & ? & ?).
      rewrite unfold_entailsL.
      split2; auto.
      intros t' w' TR.
      apply ticll_au_an.
      rewrite ticll_or.
      left.
      now apply H1.
    + rewrite ticll_an.
      split2; auto.
      intros t' w' TR.
      apply ticll_au_an; apply ticll_or.
      right; auto.
  Qed.
  
  Lemma ticll_ag_refl: forall (p: ticll E),
      <( AG p )> ⋖ p.
  Proof.
    unfold impl_ticll; intros.
    rewrite ticll_ag_an, ticll_an in H.
    now destruct H.
  Qed.

  Lemma ticll_eg_refl: forall (p: ticll E),
      <( EG p )> ⋖ p.
  Proof.
    unfold impl_ticll; intros.
    rewrite ticll_eg_en, ticll_en in H.
    now destruct H.
  Qed.

  Lemma ticll_au_idem: forall (p q: ticll E),
      <( p AU q )> ⩸ <( p AU (p AU q) )>.
  Proof.
    split; unfold impl_ticll; intros; cinduction H.
    - apply ticll_au_an, ticll_or.
      left.
      apply ticll_au_an, ticll_or.
      now left.
    - apply ticll_au_an, ticll_or.
      right.
      apply ticll_an; split; auto.
    - apply Hp.
    - apply ticll_au_an; right; split; auto.
  Qed.

  Lemma ticll_eu_idem: forall (p q: ticll E),
      <( p EU q )> ⩸ <( p EU (p EU q) )>.
  Proof.
    split; unfold impl_ticll; intros; cinduction H.
    - apply ticll_eu_en, ticll_or; left.
      apply ticll_eu_en, ticll_or.
      now left.
    - apply ticll_eu_en, ticll_or; right.
      apply ticll_en; split; eauto.
    - apply Hp.
    - apply ticll_eu_en, ticll_or; right.
      apply ticll_en; split; eauto.
  Qed.

  Lemma ticll_ag_idem: forall (p: ticll E),
      <( AG p )> ⩸ <( AG (AG p) )>.
  Proof.
    split.
    - unfold impl_ticll; intros;
        revert H; revert t w; coinduction R CIH; intros t' w' Hag.
      constructor; auto.
      apply ticll_ag_an in Hag; rewrite unfold_entailsL in Hag; destruct Hag, H0.
      split; auto.
    - apply ticll_ag_refl.
  Qed.

  Lemma ticll_eg_idem: forall (p: ticll E),
      <( EG p )> ⩸ <( EG (EG p) )>.
  Proof.
    split.
    - unfold impl_ticll; intros;
        revert H; revert t w; coinduction R CIH; intros t' w' Heg.
      constructor; auto.
      apply ticll_eg_en in Heg; rewrite unfold_entailsL in Heg; destruct Heg, H0 as (t_ & w_  & TR & H0).
      exists t_, w_; intuition.
    - apply ticll_eg_refl.
  Qed.

  Lemma ticll_and_ag: forall p q,
      <( AG (p /\ q) )> ⩸ <( AG p /\ AG q )>.
  Proof with eauto.
    split.
    - unfold impl_ticll; intros; apply ticll_and; split.
      + generalize dependent t.
        generalize dependent w.
        coinduction R CIH; intros.
        apply ticll_ag_an, ticll_an in H as (Hp & Hs & Hg).
        split2...
        now apply ticll_and in Hp as (Hp & Hq).
      + generalize dependent t.
        generalize dependent w.
        coinduction R CIH; intros.
        apply ticll_ag_an, ticll_an in H as (Hp & Hs & Hg).
        split2...
        now apply ticll_and in Hp as (Hp & Hq).
    - unfold impl_ticll; intros; revert H; revert t w.
      coinduction R CIH; intros.
      destruct H as (Hp & Hq).
      apply ticll_ag_an, ticll_an in Hp as (Hp & Hs & Hgp).
      apply ticll_ag_an, ticll_an in Hq as (Hq & _ & Hgq).
      split2...
      apply ticll_and...
  Qed.

  (* Other direction does not hold *)
  Lemma ticll_and_eg: forall p q,
      <( EG (p /\ q) )> ⋖ <( EG p /\ EG q )>.
  Proof with eauto.
    unfold impl_ticll; intros; apply ticll_and; split.
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ticll_eg_en, ticll_en in H as (Hp & t' & w' & TR & Hg).
      split...
      now apply ticll_and in Hp as (Hp & Hq).
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ticll_eg_en, ticll_en in H as (Hp & t' & w' & TR & Hg).
      split...
      now apply ticll_and in Hp as (Hp & Hq).
  Qed.

  Lemma ticll_or_ag: forall p q,
      <( AG p \/ AG q )> ⋖ <( AG (p \/ q) )>.
  Proof with eauto.
    unfold impl_ticll; intros; apply ticll_or in H as [H|H]. 
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ticll_ag_an, ticll_an in H as (Hp & Hs & Hg).
      split2...
      apply ticll_or; now left. 
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ticll_ag_an, ticll_an in H as (Hp & Hs & Hg).
      split2...
      apply ticll_or; now right.
  Qed.

  Lemma ticll_or_eg: forall p q,
      <( EG p \/ EG q )> ⋖ <( EG (p \/ q) )>.
  Proof with eauto.
    unfold impl_ticll; intros; apply ticll_or in H as [H|H]. 
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ticll_eg_en, ticll_en in H as (Hp & t' & w' & TR & Hg).
      split...
      apply ticll_or; now left.
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ticll_eg_en, ticll_en in H as (Hp & t' & w' & TR & Hg).
      split...
      apply ticll_or; now right.
  Qed.

End TicllEquations.

Section TiclrEquations.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Infix "⋖" := (@impl_ticlr M E HE KMS X) (at level 58, left associativity).
  Infix "⩸" := (@equiv_ticlr M E HE KMS X) (at level 58, left associativity).

  Lemma ticlr_finish_done: forall (φ: X -> forall e, encode e -> Prop),
      <[ finish φ ]> ⩸ <[ done {fun x w =>
                                  exists (e: E) (v: encode e), w = Obs e v /\ φ x e v} ]>.
  Proof with eauto with ticl.
    intros; split; intros t w Hinv.
    - apply ticlr_done.
      apply ticlr_finish in Hinv; inv Hinv; constructor;
        destruct H as (e' & v' & Hinv & ?); ddestruction Hinv...
    - apply ticlr_finish.
      apply ticlr_finish in Hinv; inv Hinv; constructor;
        destruct H as (e' & v' & Hinv & ?); ddestruction Hinv...
  Qed.

  Lemma ticlr_or_injL: forall (p q: ticlr E X),
      <[ p ]> ⋖ <[ p \/ q ]>.
  Proof.
    intros p q t w R.
    apply ticlr_or.
    now left.
  Qed.

  Lemma ticlr_or_injR: forall (p q: ticlr E X),
      <[ q ]> ⋖ <[ p \/ q ]>.
  Proof.
    intros p q t w R.
    apply ticlr_or.
    now right.
  Qed.
  
  Lemma ticlr_or_impl_or: forall p q R,      
      <[ p \/ q ]> ⋖ R -> <[ p ]> ⋖ R \/ <[ q ]> ⋖ R.
  Proof.
    unfold impl_ticlr.
    intros.
    left; intros.
    apply H.
    apply ticlr_or.
    now left.
  Qed.

  Lemma ticlr_or_impl_and: forall p q R,
      <[ p ]> ⋖ R /\ <[ q ]> ⋖ R ->
      <[ p \/ q ]> ⋖ R.
  Proof.
    unfold impl_ticlr.
    intros.
    destruct H.
    apply ticlr_or in H0.
    destruct H0.
    - now apply H.
    - now apply H1.
  Qed.
      
  Lemma ticlr_au_an: forall (p: ticll E) (q: ticlr E X),
      <[ p AU q ]> ⩸ <[ q \/ (p AN (p AU q)) ]>.
  Proof with auto with ticl.
    intros p q; split; intros t w Hind.
    - cinduction Hind.
      + now left.
      + right; split...
    - apply ticlr_or in Hind as [Hind | Hind].
      + now left.
      + rewrite unfold_entailsR.
        now right.
  Qed.

  Lemma ticlr_eu_en: forall (p: ticll E) (q: ticlr E X),
      <[ p EU q ]> ⩸ <[ q \/ (p EN (p EU q)) ]>.
  Proof.
    intros p q; split; intros t w Hind.
    - cinduction Hind.
      + now left.
      + rewrite ticlr_or; right.
        rewrite ticlr_en; split; auto.
        exists t0, w0; split; auto.
    - rewrite unfold_entailsR in Hind; destruct Hind.
      + now left.
      + destruct H.
        now right.
  Qed.

  Lemma ticlr_auan_anau: forall (p: ticll E) (q: ticlr E X),
      <[ p AU (p AN q) ]> ⋖ <[ p AN (p AU q) ]>.
  Proof with auto with ticl.
    intros p q t w H.
    cinduction H.
    - apply ticlr_an in Hp as (? & ? & ?).
      rewrite unfold_entailsR.
      split2; auto.
      intros t' w' TR.
      apply ticlr_au_an.
      rewrite ticlr_or.
      left.
      now apply H1.
    - rewrite ticlr_an.
      split2; auto.
      intros t' w' TR.
      apply ticlr_au_an; apply ticlr_or.
      right; auto.
  Qed.

  Lemma ticlr_euen_eneu: forall (p: ticll E) (q: ticlr E X),
      <[ p EU (p EN q) ]> ⋖ <[ p EN (p EU q) ]>.
  Proof with auto with ticl.
    intros p q t w H.
    cinduction H.
    - apply ticlr_en in Hp as (? & t' & w' & TR & ?).
      rewrite unfold_entailsR.
      split...
      exists t', w'.
      split...
      rewrite ticlr_eu_en, ticlr_or.
      now left.
    - rewrite ticlr_en.
      split...
      exists t0, w0.
      split...
      rewrite ticlr_eu_en, ticlr_or.
      right...
  Qed.

  Lemma ticlr_au_idem: forall (p: ticll E) (q: ticlr E X),
      <[ p AU q ]> ⩸ <[ p AU (p AU q) ]>.
  Proof.
    split; intros * t w H; cinduction H.
    - apply ticlr_au_an, ticlr_or.
      left.
      apply ticlr_au_an, ticlr_or.
      now left.
    - apply ticlr_au_an, ticlr_or.
      right.
      apply ticlr_an; split; auto.
    - apply Hp.
    - apply ticlr_au_an; right; split; auto.
  Qed.

  Lemma ticlr_eu_idem: forall (p: ticll E) (q: ticlr E X),
      <[ p EU q ]> ⩸ <[ p EU (p EU q) ]>.
  Proof.
    split; unfold impl_ticlr; intros; cinduction H.
    - apply ticlr_eu_en, ticlr_or; left.
      apply ticlr_eu_en, ticlr_or.
      now left.
    - apply ticlr_eu_en, ticlr_or; right.
      apply ticlr_en; split; eauto.
    - apply Hp.
    - apply ticlr_eu_en, ticlr_or; right.
      apply ticlr_en; split; eauto.
  Qed.

  Lemma ticlr_modus: forall q q' (t: M E HE X) w,
      <[ {t}, {w} |= q -> q' ]> ->
      <( {t}, {w} |= q )> ->
      <[ {t}, {w} |= q' ]>.
  Proof.
    eauto.
  Qed.

End TiclrEquations.

Infix "⋖L" := (impl_ticll _) (in custom ticll at level 79, left associativity): ticl_scope.
Infix "⩸L" := (equiv_ticll _ ) (in custom ticll at level 79, left associativity): ticl_scope.
Infix "⋖R" := (impl_ticlr _) (in custom ticlr at level 79, left associativity): ticl_scope.
Infix "⩸R" := (equiv_ticlr _ ) (in custom ticlr at level 79, left associativity): ticl_scope.
