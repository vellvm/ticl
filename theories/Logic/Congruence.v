(*| Congruences [equiv_ctl] of CTL logic |*)
From Coq Require Import
  Basics
  Classes.SetoidClass
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice tactics.

From CTree Require Import
  Utils.Utils
  Events.Core
  Logic.Semantics
  Logic.Kripke
  Logic.Setoid.

Import CtlNotations.
Local Open Scope ctl_scope.

Generalizable All Variables.

(*| Semantic implication of ctll formulas [p ⪟ q] |*)
Definition impl_ctll {M} `{HE: Encode E} {K: Kripke M E} (X: Type): relation (ctll E) :=
  fun p q => forall (t: M E HE X) (w: World E), entailsL X p t w -> entailsL X q t w.

(*| Semantic implication of ctlr formulas [p ⪟ q] |*)
Definition impl_ctlr {M} `{HE: Encode E} {K: Kripke M E} (X: Type): relation (ctlr E X) :=
  fun p q => forall (t: M E HE X) (w: World E), entailsR p t w -> entailsR q t w.

(*| Semantic equivalence of ctll formulas [p ≃ q] |*)
Definition equiv_ctll {M} `{HE: Encode E} {K: Kripke M E} (X: Type): relation (ctll E) :=
  fun p q => impl_ctll X p q /\ impl_ctll X q p.

(*| Semantic equivalence of ctlr formulas [p ≃ q] |*)
Definition equiv_ctlr {M} `{HE: Encode E} {K: Kripke M E} (X: Type): relation (ctlr E X) :=
  fun p q => impl_ctlr X p q /\ impl_ctlr X q p.

Section EquivCtlEquivalences.
  Context `{K: Kripke M E} {X: Type}.
  Notation impl_ctll := (@impl_ctll M E HE K X).
  Notation impl_ctlr := (@impl_ctlr M E HE K X).
  Notation equiv_ctll := (@equiv_ctll M E HE K X).
  Notation equiv_ctlr := (@equiv_ctlr M E HE K X).

  Global Instance Reflexive_impl_ctll:
    Reflexive impl_ctll.
  Proof. repeat red; auto. Qed.

  Global Instance Transitive_impl_ctll:
    Transitive impl_ctll.
  Proof. repeat red; auto. Qed.

  Global Instance Reflexive_impl_ctlr:
    Reflexive impl_ctlr.
  Proof. repeat red; auto. Qed.

  Global Instance Transitive_impl_ctlr:
    Transitive impl_ctlr.
  Proof. repeat red; auto. Qed.

  Global Instance Equivalence_equiv_ctll:
    Equivalence equiv_ctll.
  Proof.
    constructor.
    - split; auto.
    - split; now destruct H.
    - split; destruct H, H0;
        transitivity y; auto.
  Qed.

  Global Instance Equivalence_equiv_ctlr:
    Equivalence equiv_ctlr.
  Proof.
    constructor.
    - split; auto.
    - split; now destruct H.
    - split; destruct H, H0;
        transitivity y; auto.
  Qed.

  (*| [impl_ctll] proper under [equiv_ctll] |*)
  Global Add Parametric Morphism : impl_ctll with signature
         equiv_ctll ==> equiv_ctll ==> iff as equiv_ctll_impl.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split;
      intros pp'.
    - transitivity p; auto.
      transitivity p'; auto.
    - transitivity q'; auto.
      transitivity q; auto.
  Qed.

  (*| [impl_ctll] proper under [equiv_ctll] |*)
  Global Add Parametric Morphism : equiv_ctll with signature
         equiv_ctll ==> equiv_ctll ==> iff as equiv_ctll_equiv.
  Proof.
    intros p q pq p' q' pq'; split;
      intros pp'.
    - now rewrite <- pq, <- pq'.
    - now rewrite pq, pq'.
  Qed.

  (*| [impl_ctlr] proper under [equiv_ctlr] |*)
  Global Add Parametric Morphism : impl_ctlr with signature
         equiv_ctlr ==> equiv_ctlr ==> iff as equiv_ctlr_impl.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split;
      intros pp'.
    - transitivity p; auto.
      transitivity p'; auto.
    - transitivity q'; auto.
      transitivity q; auto.
  Qed.

  (*| [impl_ctll] proper under [equiv_ctll] |*)
  Global Add Parametric Morphism : equiv_ctlr with signature
         equiv_ctlr ==> equiv_ctlr ==> iff as equiv_ctlr_equiv.
  Proof.
    intros p q pq p' q' pq'; split;
      intros pp'.
    - now rewrite <- pq, <- pq'.
    - now rewrite pq, pq'.
  Qed.
End EquivCtlEquivalences.

(*| Equations of CTL (left) |*)
Section EquivCtllFormulas.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Notation impl_ctll := (@impl_ctll M E HE KMS X).
  Notation equiv_ctll := (@equiv_ctll M E HE KMS X).

  Arguments impl /.
  (*| Rewriting [equiv_ctl] over [entailsF] |*)
  Global Add Parametric Morphism: (entailsL X)
         with signature (impl_ctll ==> eq ==> eq ==> impl)
           as impl_ctll_entailsL.
  Proof. intro x; induction x; intros y φy; cbn; intros; auto. Qed.

  Global Add Parametric Morphism: (entailsL X)
         with signature (equiv_ctll ==> eq ==> eq ==> iff)
           as equiv_ctll_entailsL.
  Proof. intros x y [Hxy Hyx]; split; intro H; auto. Qed.

  (*| Congruences over equiv_ctl |*)
  Global Add Parametric Morphism: CAndL
         with signature impl_ctll ==> impl_ctll ==> impl_ctll
           as impl_ctll_equiv_and.
  Proof.
    intros p q EQpq p' q' EQpq'; unfold impl_ctll; intros.
    rewrite unfold_entailsL in *; destruct H; split; auto.
  Qed.

  Global Add Parametric Morphism: CAndL
         with signature equiv_ctll ==> equiv_ctll ==> equiv_ctll
           as equiv_ctll_equiv_and.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; [rewrite pq', pq | rewrite qp, qp']; reflexivity.
  Qed.

  Global Add Parametric Morphism: COrL
         with signature impl_ctll ==> impl_ctll ==> impl_ctll
           as impl_ctll_equiv_or.
  Proof.
    intros p q EQpq p' q' EQpq'; unfold impl_ctll; intros.
    rewrite unfold_entailsL in *; destruct H; auto.
  Qed.

  Global Add Parametric Morphism: COrL
         with signature equiv_ctll ==> equiv_ctll ==> equiv_ctll
           as equiv_ctll_equiv_or.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split.
    - rewrite pq', pq; reflexivity.
    - rewrite qp, qp'; reflexivity.
  Qed.

  Global Add Parametric Morphism: CxL
         with signature eq ==> impl_ctll ==> impl_ctll ==> impl_ctll as impl_ctll_next.
  Proof.
    intros [] p q pq; unfold impl_ctll; intros.
    - rewrite unfold_entailsL in H |- *; destruct H as (Hp & Hs & H).
      split2; auto.
    - rewrite unfold_entailsL in H |- *; destruct H as (Hp & t' & w' & TR & ?).
      split; [auto| exists t', w'; intuition].
  Qed.

  Global Add Parametric Morphism: CxL
      with signature eq ==> equiv_ctll ==> equiv_ctll ==> equiv_ctll as equiv_ctll_next.
  Proof.
    intros [] p q [pq qp] p' q' [pq' qp']; split; try (rewrite pq, pq' || rewrite qp, qp'); reflexivity.
  Qed.

  Global Add Parametric Morphism: CuL
         with signature eq ==> impl_ctll ==> impl_ctll ==> impl_ctll
           as impl_ctll_until.
  Proof.
    intros [] p q Hpq p' q' Hpq'; unfold impl_ctll; intros * Hu.
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
      with signature eq ==> equiv_ctll ==> equiv_ctll ==> equiv_ctll as equiv_ctll_until.
  Proof.
    intros [] p q [pq qp] p' q' [pq' qp']; split; try (rewrite pq, pq' || rewrite qp, qp'); reflexivity.
  Qed.

  Global Add Parametric Morphism: Cg
         with signature (eq ==> impl_ctll ==> impl_ctll)
           as impl_ctll_global.
  Proof.
    intros [] p q Heq; unfold impl_ctll;
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
         with signature (eq ==> equiv_ctll ==> equiv_ctll)
           as equiv_ctll_global.
  Proof.
    intros c p q [pq qp]; split; try (rewrite pq || rewrite qp); reflexivity.
  Qed.

End EquivCtllFormulas.

Section EquivCtlrFormulas.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Notation impl_ctlr := (@impl_ctlr M E HE KMS X).
  Notation equiv_ctlr := (@equiv_ctlr M E HE KMS X).

  (*| Rewriting [impl_ctl], [equiv_ctl] over [entailsR] |*)
  Arguments impl /.
  Global Add Parametric Morphism: entailsR
         with signature (impl_ctlr ==> eq ==> eq ==> impl)
           as impl_ctlr_entailsR.
  Proof. intro x; induction x; intros y φy; cbn; intros; auto. Qed.

  Global Add Parametric Morphism: entailsR
         with signature (equiv_ctlr ==> eq ==> eq ==> iff)
           as equiv_ctll_entailsR.
  Proof. intros x y [Hxy Hyx]; split; intro H; auto. Qed.

  (*| Congruences over equiv_ctlr |*)
  Global Add Parametric Morphism: CAndR
         with signature impl_ctlr ==> impl_ctlr ==> impl_ctlr
           as impl_ctlr_equiv_andr.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ctll, impl_ctlr in *; intros.
    rewrite unfold_entailsR in *; destruct H; split; auto.
  Qed.

  Global Add Parametric Morphism: CAndR
         with signature equiv_ctlr ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_andr.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; [rewrite pq', pq | rewrite qp, qp']; reflexivity.
  Qed.

  Global Add Parametric Morphism: COrR
         with signature impl_ctlr ==> impl_ctlr ==> impl_ctlr
           as impl_ctlr_equiv_orr.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ctlr in *; intros.
    rewrite unfold_entailsR in *; destruct H.
    - left; now apply pq.
    - right; now apply pq'.
  Qed.

  Global Add Parametric Morphism: COrR
         with signature equiv_ctlr  ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_orr.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; [rewrite pq', pq | rewrite qp, qp']; reflexivity.
  Qed.

  Global Add Parametric Morphism: CImplR
         with signature flip (impl_ctll X) ==> impl_ctlr ==> impl_ctlr
           as impl_ctlr_equiv_implL.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ctlr in *; intros.
    rewrite unfold_entailsR in *; intro Ha; now apply pq', H, pq.
  Qed.

  Global Add Parametric Morphism: CImplR
         with signature impl_ctll X ==> flip impl_ctlr ==> flip impl_ctlr
           as impl_ctlr_equiv_implR.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ctlr in *; intros.
    rewrite unfold_entailsR in *; intro Ha; now apply pq', H, pq.
  Qed.

  Global Add Parametric Morphism: CImplR
         with signature equiv_ctll X ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_implR.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; unfold equiv_ctlr; split.
    - rewrite <- qp, pq'; reflexivity.
    - rewrite <- pq, qp'; reflexivity.
  Qed.

  Global Add Parametric Morphism: CxR
         with signature eq ==> impl_ctll X ==> impl_ctlr ==> impl_ctlr as impl_ctlr_next.
  Proof.
    intros [] p q pq p' q' pq'; unfold impl_ctlr; intros.
    - destruct H as (Hp & Hs & H).
      split2; auto; intros * TR; intuition.
    - destruct H as (Hp & t' & w' & TR & ?).
      split; auto.
      exists t', w'; intuition.
  Qed.

  Global Add Parametric Morphism: CxR
      with signature eq ==> equiv_ctll X ==> equiv_ctlr ==> equiv_ctlr as equiv_ctlr_next.
  Proof.
    intros [] p q [pq qp] p' q' [pq' qp']; split; try (rewrite pq, pq' || rewrite qp, qp'); reflexivity.
  Qed.

  Global Add Parametric Morphism: CuR
         with signature eq ==> impl_ctll X ==> impl_ctlr ==> impl_ctlr as impl_ctlr_until.
  Proof.
    intros [] p q Hpq p' q' Hpq'; unfold impl_ctlr; intros * Hu.
    - cinduction Hu; rewrite unfold_entailsR; [left; auto | right; split2]; auto.
    - cinduction Hu; rewrite unfold_entailsR; [left; auto | right; split]; eauto.
  Qed.

  Global Add Parametric Morphism: CuR
      with signature eq ==> equiv_ctll X ==> equiv_ctlr ==> equiv_ctlr as equiv_ctlr_until.
  Proof.
    intros [] p q [pq qp] p' q' [pq' qp']; split; try (rewrite pq, pq' || rewrite qp, qp'); reflexivity.
  Qed.


        
End EquivCtlrFormulas.

(*| Equations of CTL (left) |*)
Section CtllEquations.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Infix "⋖" := (impl_ctll X (K:=KMS)) (at level 58, left associativity).
  Infix "⩸" := (equiv_ctll X (K:=KMS)) (at level 58, left associativity).

  Lemma ctll_vis_now: forall φ,
      <( vis φ )> ⩸ <( now {fun w => exists (e: E) (v: encode e), w = Obs e v /\ φ e v} )>.
  Proof.
    intros; split; unfold impl_ctll; rewrite ?unfold_entailsF.
    - intros * [[] Hd]; ddestruction Hd.
      split; [|constructor].
      exists e, v; auto.
    - intros * [(e & v & -> & Hφ) Hd]; split; auto with ctl.
  Qed.

  Lemma ctll_au_ax: forall (p q: ctll E),
      <( p AU q )> ⩸ <( q \/ (p AN (p AU q)) )>.
  Proof.
    intros p q; split; intros t w Hind.
    - cinduction Hind.
      + now left.
      + right; split; auto.
    - apply ctll_or in Hind as [Hind | Hind].
      + now left.
      + rewrite unfold_entailsL.
        now right.
  Qed.

  Lemma ctll_eu_ex: forall (p q: ctll E),
      <( p EU q )> ⩸ <( q \/ (p EN (p EU q)) )>.
  Proof.
    intros p q; split; intros t w Hind.
    - cinduction Hind.
      + now left.
      + rewrite ctll_or; right.
        rewrite ctll_ex; split; auto.
        exists t0, w0; split; auto.
    - rewrite unfold_entailsL in Hind; destruct Hind.
      + now left.
      + destruct H.
        now right.
  Qed.

  Lemma ctll_and_idL: forall (p: ctll E),
      <( ⊤ /\ p )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - split; auto.
      now apply ctll_not_done in Hp.
  Qed.

  Lemma ctll_and_idR: forall (p: ctll E),
      <( p /\ ⊤ )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - split; auto.
      now apply ctll_not_done in Hp.
  Qed.

  Lemma ctll_or_idL: forall (p: ctll E),
      <( ⊥ \/ p )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - now right.
  Qed.

  Lemma ctll_or_idR: forall (p: ctll E),
      <( p \/ ⊥ )> ⩸ <( p )>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - now left.
  Qed.

  Lemma ctll_ag_ax: forall (p: ctll E),
      <( AG p )> ⩸ <( p AN (AG p) )>.
  Proof.
    split; intros t w Hp.
    - step in Hp; inv Hp; split; auto.
    - destruct Hp.
      destruct H0; step; now constructor.
  Qed.

  Lemma ctll_eg_ex: forall (p: ctll E),
      <( EG p )> ⩸ <( p EN (EG p) )>.
  Proof.
    split; intros t w Hp.
    - split; step in Hp; inv Hp; auto.
    - destruct Hp.
      step; now constructor.
  Qed.

  Lemma ctll_auax_axau: forall (p q: ctll E),
      <( p AU (p AN q) )> ⋖ <( p AN (p AU q) )>.
  Proof.
    intros * t w H.
    cinduction H.
    + apply ctll_ax in Hp as (? & ? & ?).
      rewrite unfold_entailsL.
      split2; auto.
      intros t' w' TR.
      apply ctll_au_ax.
      rewrite ctll_or.
      left.
      now apply H1.
    + rewrite ctll_ax.
      split2; auto.
      intros t' w' TR.
      apply ctll_au_ax; apply ctll_or.
      right; auto.
  Qed.
  
  Lemma ctll_ag_refl: forall (p: ctll E),
      <( AG p )> ⋖ p.
  Proof.
    unfold impl_ctll; intros.
    rewrite ctll_ag_ax, ctll_ax in H.
    now destruct H.
  Qed.

  Lemma ctll_eg_refl: forall (p: ctll E),
      <( EG p )> ⋖ p.
  Proof.
    unfold impl_ctll; intros.
    rewrite ctll_eg_ex, ctll_ex in H.
    now destruct H.
  Qed.

  Lemma ctll_au_idem: forall (p q: ctll E),
      <( p AU q )> ⩸ <( p AU (p AU q) )>.
  Proof.
    split; unfold impl_ctll; intros; cinduction H.
    - apply ctll_au_ax, ctll_or.
      left.
      apply ctll_au_ax, ctll_or.
      now left.
    - apply ctll_au_ax, ctll_or.
      right.
      apply ctll_ax; split; auto.
    - apply Hp.
    - apply ctll_au_ax; right; split; auto.
  Qed.

  Lemma ctll_eu_idem: forall (p q: ctll E),
      <( p EU q )> ⩸ <( p EU (p EU q) )>.
  Proof.
    split; unfold impl_ctll; intros; cinduction H.
    - apply ctll_eu_ex, ctll_or; left.
      apply ctll_eu_ex, ctll_or.
      now left.
    - apply ctll_eu_ex, ctll_or; right.
      apply ctll_ex; split; eauto.
    - apply Hp.
    - apply ctll_eu_ex, ctll_or; right.
      apply ctll_ex; split; eauto.
  Qed.

  Lemma ctll_ag_idem: forall (p: ctll E),
      <( AG p )> ⩸ <( AG (AG p) )>.
  Proof.
    split.
    - unfold impl_ctll; intros;
        revert H; revert t w; coinduction R CIH; intros t' w' Hag.
      constructor; auto.
      apply ctll_ag_ax in Hag; rewrite unfold_entailsL in Hag; destruct Hag, H0.
      split; auto.
    - apply ctll_ag_refl.
  Qed.

  Lemma ctll_eg_idem: forall (p: ctll E),
      <( EG p )> ⩸ <( EG (EG p) )>.
  Proof.
    split.
    - unfold impl_ctll; intros;
        revert H; revert t w; coinduction R CIH; intros t' w' Heg.
      constructor; auto.
      apply ctll_eg_ex in Heg; rewrite unfold_entailsL in Heg; destruct Heg, H0 as (t_ & w_  & TR & H0).
      exists t_, w_; intuition.
    - apply ctll_eg_refl.
  Qed.

  Lemma ctll_and_ag: forall p q,
      <( AG (p /\ q) )> ⩸ <( AG p /\ AG q )>.
  Proof with eauto.
    split.
    - unfold impl_ctll; intros; apply ctll_and; split.
      + generalize dependent t.
        generalize dependent w.
        coinduction R CIH; intros.
        apply ctll_ag_ax, ctll_ax in H as (Hp & Hs & Hg).
        split2...
        now apply ctll_and in Hp as (Hp & Hq).
      + generalize dependent t.
        generalize dependent w.
        coinduction R CIH; intros.
        apply ctll_ag_ax, ctll_ax in H as (Hp & Hs & Hg).
        split2...
        now apply ctll_and in Hp as (Hp & Hq).
    - unfold impl_ctll; intros; revert H; revert t w.
      coinduction R CIH; intros.
      destruct H as (Hp & Hq).
      apply ctll_ag_ax, ctll_ax in Hp as (Hp & Hs & Hgp).
      apply ctll_ag_ax, ctll_ax in Hq as (Hq & _ & Hgq).
      split2...
      apply ctll_and...
  Qed.

  (* Other direction does not hold *)
  Lemma ctll_and_eg: forall p q,
      <( EG (p /\ q) )> ⋖ <( EG p /\ EG q )>.
  Proof with eauto.
    unfold impl_ctll; intros; apply ctll_and; split.
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ctll_eg_ex, ctll_ex in H as (Hp & t' & w' & TR & Hg).
      split...
      now apply ctll_and in Hp as (Hp & Hq).
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ctll_eg_ex, ctll_ex in H as (Hp & t' & w' & TR & Hg).
      split...
      now apply ctll_and in Hp as (Hp & Hq).
  Qed.

  Lemma ctll_or_ag: forall p q,
      <( AG p \/ AG q )> ⋖ <( AG (p \/ q) )>.
  Proof with eauto.
    unfold impl_ctll; intros; apply ctll_or in H as [H|H]. 
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ctll_ag_ax, ctll_ax in H as (Hp & Hs & Hg).
      split2...
      apply ctll_or; now left. 
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ctll_ag_ax, ctll_ax in H as (Hp & Hs & Hg).
      split2...
      apply ctll_or; now right.
  Qed.

  Lemma ctll_or_eg: forall p q,
      <( EG p \/ EG q )> ⋖ <( EG (p \/ q) )>.
  Proof with eauto.
    unfold impl_ctll; intros; apply ctll_or in H as [H|H]. 
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ctll_eg_ex, ctll_ex in H as (Hp & t' & w' & TR & Hg).
      split...
      apply ctll_or; now left.
    + generalize dependent t.
      generalize dependent w.
      coinduction R CIH; intros.
      apply ctll_eg_ex, ctll_ex in H as (Hp & t' & w' & TR & Hg).
      split...
      apply ctll_or; now right.
  Qed.

End CtllEquations.

Section CtlrEquations.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Infix "⋖" := (@impl_ctlr M E HE KMS X) (at level 58, left associativity).
  Infix "⩸" := (@equiv_ctlr M E HE KMS X) (at level 58, left associativity).

  Lemma ctlr_finish_done: forall (φ: X -> forall e, encode e -> Prop),
      <[ finish φ ]> ⩸ <[ done {fun x w =>
                                  exists (e: E) (v: encode e), w = Obs e v /\ φ x e v} ]>.
  Proof with eauto with ctl.
    intros; split; intros t w Hinv.
    - apply ctlr_done.
      apply ctlr_finish in Hinv; inv Hinv; constructor;
        destruct H as (e' & v' & Hinv & ?); ddestruction Hinv...
    - apply ctlr_finish.
      apply ctlr_finish in Hinv; inv Hinv; constructor;
        destruct H as (e' & v' & Hinv & ?); ddestruction Hinv...
  Qed.

  Lemma ctlr_or_injL: forall (p q: ctlr E X),
      <[ p ]> ⋖ <[ p \/ q ]>.
  Proof.
    intros p q t w R.
    apply ctlr_or.
    now left.
  Qed.

  Lemma ctlr_or_injR: forall (p q: ctlr E X),
      <[ q ]> ⋖ <[ p \/ q ]>.
  Proof.
    intros p q t w R.
    apply ctlr_or.
    now right.
  Qed.
  
  Lemma ctlr_or_impl_or: forall p q R,      
      <[ p \/ q ]> ⋖ R -> <[ p ]> ⋖ R \/ <[ q ]> ⋖ R.
  Proof.
    unfold impl_ctlr.
    intros.
    left; intros.
    apply H.
    apply ctlr_or.
    now left.
  Qed.

  Lemma ctlr_or_impl_and: forall p q R,
      <[ p ]> ⋖ R /\ <[ q ]> ⋖ R ->
      <[ p \/ q ]> ⋖ R.
  Proof.
    unfold impl_ctlr.
    intros.
    destruct H.
    apply ctlr_or in H0.
    destruct H0.
    - now apply H.
    - now apply H1.
  Qed.
      
  Lemma ctlr_au_ax: forall (p: ctll E) (q: ctlr E X),
      <[ p AU q ]> ⩸ <[ q \/ (p AN (p AU q)) ]>.
  Proof with auto with ctl.
    intros p q; split; intros t w Hind.
    - cinduction Hind.
      + now left.
      + right; split...
    - apply ctlr_or in Hind as [Hind | Hind].
      + now left.
      + rewrite unfold_entailsR.
        now right.
  Qed.

  Lemma ctlr_eu_ex: forall (p: ctll E) (q: ctlr E X),
      <[ p EU q ]> ⩸ <[ q \/ (p EN (p EU q)) ]>.
  Proof.
    intros p q; split; intros t w Hind.
    - cinduction Hind.
      + now left.
      + rewrite ctlr_or; right.
        rewrite ctlr_ex; split; auto.
        exists t0, w0; split; auto.
    - rewrite unfold_entailsR in Hind; destruct Hind.
      + now left.
      + destruct H.
        now right.
  Qed.

  Lemma ctlr_auax_axau: forall (p: ctll E) (q: ctlr E X),
      <[ p AU (p AN q) ]> ⋖ <[ p AN (p AU q) ]>.
  Proof with auto with ctl.
    intros p q t w H.
    cinduction H.
    - apply ctlr_ax in Hp as (? & ? & ?).
      rewrite unfold_entailsR.
      split2; auto.
      intros t' w' TR.
      apply ctlr_au_ax.
      rewrite ctlr_or.
      left.
      now apply H1.
    - rewrite ctlr_ax.
      split2; auto.
      intros t' w' TR.
      apply ctlr_au_ax; apply ctlr_or.
      right; auto.
  Qed.

  Lemma ctlr_euex_exeu: forall (p: ctll E) (q: ctlr E X),
      <[ p EU (p EN q) ]> ⋖ <[ p EN (p EU q) ]>.
  Proof with auto with ctl.
    intros p q t w H.
    cinduction H.
    - apply ctlr_ex in Hp as (? & t' & w' & TR & ?).
      rewrite unfold_entailsR.
      split...
      exists t', w'.
      split...
      rewrite ctlr_eu_ex, ctlr_or.
      now left.
    - rewrite ctlr_ex.
      split...
      exists t0, w0.
      split...
      rewrite ctlr_eu_ex, ctlr_or.
      right...
  Qed.

  Lemma ctlr_au_idem: forall (p: ctll E) (q: ctlr E X),
      <[ p AU q ]> ⩸ <[ p AU (p AU q) ]>.
  Proof.
    split; intros * t w H; cinduction H.
    - apply ctlr_au_ax, ctlr_or.
      left.
      apply ctlr_au_ax, ctlr_or.
      now left.
    - apply ctlr_au_ax, ctlr_or.
      right.
      apply ctlr_ax; split; auto.
    - apply Hp.
    - apply ctlr_au_ax; right; split; auto.
  Qed.

  Lemma ctlr_eu_idem: forall (p: ctll E) (q: ctlr E X),
      <[ p EU q ]> ⩸ <[ p EU (p EU q) ]>.
  Proof.
    split; unfold impl_ctlr; intros; cinduction H.
    - apply ctlr_eu_ex, ctlr_or; left.
      apply ctlr_eu_ex, ctlr_or.
      now left.
    - apply ctlr_eu_ex, ctlr_or; right.
      apply ctlr_ex; split; eauto.
    - apply Hp.
    - apply ctlr_eu_ex, ctlr_or; right.
      apply ctlr_ex; split; eauto.
  Qed.

  Lemma ctlr_modus: forall q q' (t: M E HE X) w,
      <[ {t}, {w} |= q -> q' ]> ->
      <( {t}, {w} |= q )> ->
      <[ {t}, {w} |= q' ]>.
  Proof.
    eauto.
  Qed.


End CtlrEquations.

Infix "⋖L" := (impl_ctll _) (in custom ctll at level 79, left associativity): ctl_scope.
Infix "⩸L" := (equiv_ctll _ ) (in custom ctll at level 79, left associativity): ctl_scope.
Infix "⋖R" := (impl_ctlr _) (in custom ctlr at level 79, left associativity): ctl_scope.
Infix "⩸R" := (equiv_ctlr _ ) (in custom ctlr at level 79, left associativity): ctl_scope.
