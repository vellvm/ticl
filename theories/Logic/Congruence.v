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
         with signature eq ==> impl_ctll ==> impl_ctll as impl_ctll_next.
  Proof.
    intros [] p q pq; unfold impl_ctll; intros.
    - destruct H.
      split; auto; intros * TR; intuition.
    - destruct H as (t' & w' & TR & ?).
      exists t', w'; intuition.
  Qed.
  
  Global Add Parametric Morphism: CxL
      with signature eq ==> equiv_ctll ==> equiv_ctll as equiv_ctll_next.
  Proof.
    intros [] p q [pq qp]; split; try (rewrite pq || rewrite qp); reflexivity.
  Qed.

  Global Add Parametric Morphism: CuL
         with signature eq ==> impl_ctll ==> impl_ctll ==> impl_ctll
           as impl_ctll_until.
  Proof.
    intros [] p q Hpq p' q' Hpq'; unfold impl_ctll; intros * Hu.
    - cinduction Hu; rewrite unfold_entailsL; [left | right]; auto.
    - cinduction Hu; rewrite unfold_entailsL; [left | right]; auto.
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
  Global Add Parametric Morphism: CAndLR
         with signature impl_ctll X ==> impl_ctlr ==> impl_ctlr
           as impl_ctlr_equiv_and.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ctll, impl_ctlr in *; intros.
    rewrite unfold_entailsR in *; destruct H; split; auto.
  Qed.

  Global Add Parametric Morphism: CAndLR
         with signature equiv_ctll X ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_and.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; [rewrite pq', pq | rewrite qp, qp']; reflexivity.
  Qed.

  Global Add Parametric Morphism: CAndRR
         with signature impl_ctlr ==> impl_ctlr ==> impl_ctlr
           as impl_ctlr_equiv_andr.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ctll, impl_ctlr in *; intros.
    rewrite unfold_entailsR in *; destruct H; split; auto.
  Qed.

  Global Add Parametric Morphism: CAndRR
         with signature equiv_ctlr ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_andr.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; [rewrite pq', pq | rewrite qp, qp']; reflexivity.
  Qed.

  Global Add Parametric Morphism: COrLR
         with signature impl_ctll X ==> impl_ctlr ==> impl_ctlr
           as impl_ctlr_equiv_or.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ctlr in *; intros.
    rewrite unfold_entailsR in *; destruct H.
    - left; now apply pq.
    - right; now apply pq'.
  Qed.

  Global Add Parametric Morphism: COrLR
         with signature equiv_ctll X ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_or.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; [rewrite pq', pq | rewrite qp, qp']; reflexivity.
  Qed.

  Global Add Parametric Morphism: COrRR
         with signature impl_ctlr ==> impl_ctlr ==> impl_ctlr
           as impl_ctlr_equiv_orr.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ctlr in *; intros.
    rewrite unfold_entailsR in *; destruct H.
    - left; now apply pq.
    - right; now apply pq'.
  Qed.

  Global Add Parametric Morphism: COrRR
         with signature equiv_ctlr  ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_orr.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; split; [rewrite pq', pq | rewrite qp, qp']; reflexivity.
  Qed.

  Global Add Parametric Morphism: CImplLR
         with signature flip (impl_ctll X) ==> impl_ctlr ==> impl_ctlr
           as impl_ctlr_equiv_implL.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ctlr in *; intros.
    rewrite unfold_entailsR in *; intro Ha; now apply pq', H, pq. 
  Qed.

  Global Add Parametric Morphism: CImplLR
         with signature impl_ctll X ==> flip impl_ctlr ==> flip impl_ctlr
           as impl_ctlr_equiv_implR.
  Proof.
    intros p q pq p' q' pq'; unfold impl_ctlr in *; intros.
    rewrite unfold_entailsR in *; intro Ha; now apply pq', H, pq. 
  Qed.

  Global Add Parametric Morphism: CImplLR
         with signature equiv_ctll X ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_implR.
  Proof.
    intros p q [pq qp] p' q' [pq' qp']; unfold equiv_ctlr; split.
    - rewrite <- qp, pq'; reflexivity.
    - rewrite <- pq, qp'; reflexivity.
  Qed.

  Global Add Parametric Morphism: CxR
         with signature eq ==> impl_ctlr ==> impl_ctlr as impl_ctlr_next.
  Proof.
    intros [] p q pq; unfold impl_ctlr; intros.
    - destruct H.
      split; auto; intros * TR; intuition.
    - destruct H as (t' & w' & TR & ?).
      exists t', w'; intuition.
  Qed.
  
  Global Add Parametric Morphism: CxR
      with signature eq ==> equiv_ctlr ==> equiv_ctlr as equiv_ctlr_next.
  Proof.
    intros [] p q [pq qp]; split; try (rewrite pq || rewrite qp); reflexivity.
  Qed.

  Global Add Parametric Morphism: CuR
         with signature eq ==> impl_ctll X ==> impl_ctlr ==> impl_ctlr as impl_ctlr_until.
  Proof.
    intros [] p q Hpq p' q' Hpq'; unfold impl_ctlr; intros * Hu.
    - cinduction Hu; rewrite unfold_entailsR; [left | right]; auto.
    - cinduction Hu; rewrite unfold_entailsR; [left | right]; auto.
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
      <( p AU q )> ⩸ <( q \/ (p /\ AX (p AU q)) )>.
  Proof.
    intros p q; split; intros t w Hind.
    - cinduction Hind. 
      + now left.
      + destruct H1 as ([? ?] & ?).
        right; split; auto.
    - rewrite unfold_entailsL in Hind; destruct Hind.
      + now left. 
      + destruct H.
        destruct H0.
        rewrite unfold_entailsL.
        now right.
  Qed.

  Lemma ctll_eu_ex: forall (p q: ctll E),
      <( p EU q )> ⩸ <( q \/ (p /\ EX (p EU q)) )>.
  Proof.
    intros p q; split; intros t w Hind.
    - cinduction Hind. 
      + now left.
      + destruct H1 as (t' & w' & TR & ?).
        right; split; auto.
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

  Lemma ctll_af_ax: forall (p: ctll E),
      <( AF p )> ⩸ <( p \/ AX (AF p) )>.
  Proof.
    intros.
    etransitivity.
    apply ctll_au_ax.
    now rewrite ctll_and_idL.
  Qed.

  Lemma ctll_ef_ex: forall (p: ctll E),
      <( EF p )> ⩸ <( p \/ EX (EF p) )>.
  Proof.
    intros.
    etransitivity.
    apply ctll_eu_ex.
    now rewrite ctll_and_idL.
  Qed.

  Lemma ctll_ag_ax: forall (p: ctll E),
      <( AG p )> ⩸ <( p /\ AX (AG p) )>.
   Proof. 
     split; intros t w Hp.
     - step in Hp; inv Hp; split; auto.
     - destruct Hp.
       destruct H0; step; now constructor.
   Qed.

   Lemma ctll_eg_ex: forall (p: ctll E),
       <( EG p )> ⩸ <( p /\ EX (EG p) )>.
   Proof. 
     split; intros t w Hp.
     - split; step in Hp; inv Hp; auto.
     - destruct Hp.
       step; now constructor.
   Qed.

   Lemma ctll_afax_axaf: forall (p: ctll E) (t: MS) w,
       <( t, w |= AF AX p )> -> <( t, w |= AX AF p )>.
   Proof.
     intros * H.
     cinduction H.
     + destruct H.
       rewrite unfold_entailsL.
       split; auto.
       intros t' w' TR.
       cut <( t', w' |= AF p )>; auto.
       apply ctll_af_ax.
       rewrite unfold_entailsL.
       left.
       now apply H0.
     + destruct H0, H1; clear H H1.
       rewrite unfold_entailsL.
       split; auto.
       intros t' w' TR.       
       pose proof (H3 _ _ TR).
       rewrite unfold_entailsL in H; destruct H.
       cut <( t', w' |= AF p )>; auto.
       apply ctll_af_ax.
       rewrite unfold_entailsL.
       right; split; auto.
   Qed.

   Lemma ctll_af_involutive: forall (p: ctll E),
       <( AF p )> ⩸ <( AF (AF p) )>.
   Proof.
     split; unfold impl_ctll; intros; cinduction H.
     - apply ctll_af_ax.
       rewrite unfold_entailsL.
       left.
       now apply ctll_af_ax; left.
     - destruct H0, H1; clear H1.
       apply ctll_af_ax; right; split; auto.
     - apply H.
     - destruct H0, H1; clear H1 H.
       apply ctll_af_ax; right; split; auto.
   Qed.

   Lemma ctll_ef_involutive: forall (p: ctll E),
       <( EF p )> ⩸ <( EF (EF p) )>.
   Proof.
     split; unfold impl_ctll; intros; cinduction H.
     - apply ctll_ef_ex; rewrite unfold_entailsL; left.
       now apply ctll_ef_ex; left.
     - destruct H1 as (t1 & w1 & TR1 & H1). 
       apply ctll_ef_ex; right.
       exists t1, w1; auto.
     - apply H.
     - destruct H1 as (t1 & w1 & TR1 & H1). 
       apply ctll_ef_ex; right.
       exists t1, w1; auto.
   Qed.
   
   Lemma ctll_ag_involutive: forall (p: ctll E),
       <( AG p )> ⩸ <( AG (AG p) )>.
   Proof.
     split; unfold impl_ctll; intros;
       revert H; revert t w; coinduction R CIH; intros t' w' Hag.     
     - constructor; auto. 
       apply ctll_ag_ax in Hag; rewrite unfold_entailsL in Hag; destruct Hag.
       rewrite unfold_entailsL in H0; destruct H0.
       split; auto. 
     - rewrite ctll_ag_ax in Hag; rewrite unfold_entailsL in Hag; destruct Hag.
       rewrite unfold_entailsL in H0; destruct H0.
       rewrite ctll_ag_ax in H; rewrite unfold_entailsL in H.
       destruct H.
       constructor; auto.
       split; auto.
   Qed.

   Lemma ctll_eg_involutive: forall (p: ctll E),
       <( EG p )> ⩸ <( EG (EG p) )>.
   Proof.
     split;  unfold impl_ctll; intros;
       revert H; revert t w; coinduction R CIH; intros t' w' Heg.     
     - constructor; auto.
       apply ctll_eg_ex in Heg; rewrite unfold_entailsL in Heg; destruct Heg.
       rewrite unfold_entailsL in H0; destruct H0 as (t & w & TR & HH).
       exists t, w; intuition.
     - apply ctll_eg_ex in Heg; rewrite unfold_entailsL in Heg; destruct Heg.
       rewrite unfold_entailsL in H0; destruct H0 as (t & w & TR & HH).
       rewrite ctll_eg_ex in H.
       rewrite unfold_entailsL in H; destruct H.
       constructor; auto.
       exists t, w; intuition.
   Qed.
End CtllEquations.

Section CtlrEquations.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Infix "⋖" := (@impl_ctlr M E HE KMS X) (at level 58, left associativity).
  Infix "⩦" := (@equiv_ctlr M E HE KMS X) (at level 58, left associativity).
  
  Lemma ctlr_finish_done: forall (φ: X -> forall e, encode e -> Prop),
      <[ finish φ ]> ⩦ <[ done {fun x w => 
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
  
  Lemma ctlr_au_ax: forall (p: ctll E) (q: ctlr E X),
      <[ p AU q ]> ⩦ <[ q \/ (p ∩ AX (p AU q)) ]>.
  Proof.
    intros p q; split; intros t w Hind.
    - cinduction Hind. 
      + now left.
      + destruct H1 as ([? ?] & ?).
        right; split; auto.
    - rewrite unfold_entailsR in Hind; destruct Hind.
      + now left. 
      + destruct H, H0.
        rewrite unfold_entailsR.
        now right.
  Qed.

  Lemma ctlr_eu_ex: forall (p: ctll E) (q: ctlr E X),
      <[ p EU q ]> ⩦ <[ q \/ (p ∩ EX (p EU q)) ]>.
  Proof.
    intros p q; split; intros t w Hind.
    - cinduction Hind. 
      + now left.
      + destruct H1 as (t' & w' & TR & ?).
        right; split; auto.
    - rewrite unfold_entailsR in Hind; destruct Hind.
      + now left. 
      + destruct H.
        now right. 
  Qed.

  (* LEF: The other direction does not hold, counter p := done {fun _ => True} *)
  Lemma ctlr_and_idL: forall (p: ctlr E X),
      <[ ⊤ ∩ p ]> ⋖ <[ p ]>.
  Proof.
    intros p t w Hp.
    now destruct Hp.
  Qed.

  (* LEF: But this AX, EX variant does hold, we get the [not_done w] from X *)
  Lemma ctlr_and_ax_idL: forall (p: ctlr E X),
      <[ ⊤ ∩ AX p ]> ⩦ <[ AX p ]>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - apply ctlr_andl; split; auto.
      destruct Hp.
      apply ctll_now; intuition.
      now apply can_step_not_done with t.
  Qed.

  Lemma ctlr_and_ex_idL: forall (p: ctlr E X),
      <[ ⊤ ∩ EX p ]> ⩦ <[ EX p ]>.
  Proof.
    split; intros t w Hp.
    - now destruct Hp.
    - apply ctlr_andl; split; auto.
      destruct Hp as (t' & w' & TR & ?).
      apply ctll_now; intuition.
  Qed.
  
  Lemma ctlr_af_ax: forall (p: ctlr E X),
      <[ AF p ]> ⩦ <[ p \/ AX (AF p) ]>.
  Proof.
    intros.
    etransitivity.
    apply ctlr_au_ax.
    now rewrite ctlr_and_ax_idL.
  Qed.

  Lemma ctlr_ef_ex: forall (p: ctlr E X),
      <[ EF p ]> ⩦ <[ p \/ EX (EF p) ]>.
  Proof.
    intros.
    etransitivity.
    apply ctlr_eu_ex.
    now rewrite ctlr_and_ex_idL.
  Qed.
  
  Lemma ctlr_afax_axaf: forall (p: ctlr E X) (t: MS) w,
      <[ t, w |= AF AX p ]> -> <[ t, w |= AX AF p ]>.
  Proof.
    intros * H.
    cinduction H.
    + destruct H.
      rewrite unfold_entailsR.
      split; auto.
      intros t' w' TR.
      cut <[ t', w' |= AF p ]>; auto.
      apply ctlr_af_ax.
      rewrite unfold_entailsR.
      left.
      now apply H0.
    + destruct H0, H1; clear H H1.
      rewrite unfold_entailsR.
      split; auto.
      intros t' w' TR.       
      pose proof (H3 _ _ TR).
      rewrite unfold_entailsR in H; destruct H.
      cut <[ t', w' |= AF p ]>; auto.
      apply ctlr_af_ax.
      rewrite unfold_entailsR.
      right; split; auto.
   Qed.

   Lemma ctlr_af_involutive: forall (p: ctlr E X),
       <[ AF p ]> ⩦ <[ AF (AF p) ]>.
   Proof.
     split; unfold impl_ctlr; intros; cinduction H.
     - apply ctlr_af_ax; rewrite unfold_entailsR.
       left.
       now apply ctlr_af_ax; left.
     - destruct H0, H1; clear H1.
       apply ctlr_af_ax; right; split; auto.
     - apply H.
     - destruct H0, H1; clear H1 H.
       apply ctlr_af_ax; right; split; auto.
   Qed.

   Lemma ctlr_ef_involutive: forall (p: ctlr E X),
       <[ EF p ]> ⩦ <[ EF (EF p) ]>.
   Proof.
     split; unfold impl_ctlr; intros; cinduction H.
     - apply ctlr_ef_ex; rewrite unfold_entailsR; left.
       now apply ctlr_ef_ex; left.
     - destruct H1 as (t1 & w1 & TR1 & H1). 
       apply ctlr_ef_ex; right.
       exists t1, w1; auto.
     - apply H.
     - destruct H1 as (t1 & w1 & TR1 & H1). 
       apply ctlr_ef_ex; right.
       exists t1, w1; auto.
   Qed.
End CtlrEquations.
