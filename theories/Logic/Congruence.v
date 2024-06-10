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

From Equations Require Import Equations.

Import CtlNotations.
Local Open Scope ctl_scope.

Generalizable All Variables.

(*| Semantic equivalences of formulas |*)
Definition equiv_ctll {M} `{HE: Encode E} {K: Kripke M E} (X: Type): relation (ctll E) :=
  fun p q => forall (t: M E HE X) (w: World E), entailsL X p t w <-> entailsL X q t w.

Definition equiv_ctlr {M} `{HE: Encode E} {K: Kripke M E} (X: Type): relation (ctlr E X) :=
  fun p q => forall (t: M E HE X) (w: World E), entailsR p t w <-> entailsR q t w.

Section EquivCtlEquivalences.
  Context `{K: Kripke M E} {X: Type}.
  Notation equiv_ctll := (@equiv_ctll M E HE K X).
  Notation equiv_ctlr := (@equiv_ctlr M E HE K X).

  Global Instance Equivalence_equiv_ctll:
    Equivalence equiv_ctll.
  Proof.
    constructor.
    - intros P x; reflexivity.
    - intros P Q H' x; symmetry; auto.
    - intros P Q R H0' H1' x; etransitivity; auto.
  Qed.

  (*| [equiv_ctll] proper under [equiv_ctll] |*)
  Global Add Parametric Morphism : equiv_ctll with signature
         equiv_ctll ==> equiv_ctll ==> iff as equiv_ctll_equiv.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; intro BASE; cbn in *.
    - symmetry in EQpq'; apply EQpq'.
      symmetry in EQpp'; apply EQpp'.
      now apply EQpq.
    - symmetry in EQpq'; apply EQpq.
      apply EQpp'.
      now apply EQpq'.
    - apply EQpq'.
      symmetry in EQpp'; apply EQpp'.
      symmetry in EQpq; now apply EQpq.
    - apply EQpq.
      apply EQpp'.
      symmetry in EQpq'; now apply EQpq'.
  Qed.

  Global Instance Equivalence_equiv_ctlr:
    Equivalence equiv_ctlr.
  Proof.
    constructor.
    - intros P x; reflexivity.
    - intros P Q H' x; symmetry; auto.
    - intros P Q R H0' H1' x; etransitivity; auto.
  Qed.
  
  (*| [equiv_ctlr] proper under [equiv_ctlr] |*)
  Global Add Parametric Morphism : equiv_ctlr with signature
         equiv_ctlr ==> equiv_ctlr ==> iff as equiv_ctlr_equiv.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; intro BASE; cbn in *.
    - symmetry in EQpq'; apply EQpq'.
      symmetry in EQpp'; apply EQpp'.
      now apply EQpq.
    - symmetry in EQpq'; apply EQpq.
      apply EQpp'.
      now apply EQpq'.
    - apply EQpq'.
      symmetry in EQpp'; apply EQpp'.
      symmetry in EQpq; now apply EQpq.
    - apply EQpq.
      apply EQpp'.
      symmetry in EQpq'; now apply EQpq'.
  Qed.
  
End EquivCtlEquivalences.

(*| Equations of CTL (left) |*)
Section EquivCtllFormulas.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Notation equiv_ctll := (@equiv_ctll M E HE KMS X).

  (*| Rewriting [equiv_ctl] over [entailsF] |*)
  Global Add Parametric Morphism: (entailsL X)
         with signature (equiv_ctll ==> eq ==> eq ==> iff)
           as proper_equiv_ctl_entailsL.
  Proof. intro x; induction x; intros y EQφ; apply EQφ. Qed.

  (*| Congruences over equiv_ctl |*)
  Global Add Parametric Morphism: CAndL
         with signature equiv_ctll ==> equiv_ctll ==> equiv_ctll
           as equiv_ctll_equiv_and.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; destruct EQpp'.
    + now apply EQpq.
    + now apply EQpq'.
    + now apply EQpq in H.
    + now apply EQpq' in H0.
  Qed.

  Global Add Parametric Morphism: COrL
         with signature equiv_ctll ==> equiv_ctll ==> equiv_ctll
           as equiv_ctll_equiv_or.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; destruct EQpp'.
    + left; now apply EQpq.
    + right; now apply EQpq'.
    + left; now apply EQpq in H.
    + right; now apply EQpq' in H.
  Qed.

  Global Add Parametric Morphism: CImplL
         with signature equiv_ctll ==> equiv_ctll ==> equiv_ctll
           as equiv_ctll_equiv_impl.
  Proof.
    intros p q EQpq p' q' EQpq'; split; rewrite unfold_entailsL;
      intros EQpp'; rewrite unfold_entailsL; intro HH; apply EQpq'; apply EQpq in HH;
      now apply EQpp'.
  Qed.

  Global Add Parametric Morphism: CxL
      with signature eq ==> equiv_ctll ==> equiv_ctll as equiv_ctll_equiv_next.
  Proof.
    intros [] p q EQpq.
    - split; intros; rewrite ctll_ax in *;
        destruct H; split; auto; intros.
      + rewrite <- EQpq; auto.
      + rewrite EQpq; auto.
    - split; intros; rewrite ctll_ex in *;
        destruct H as (t' & w' & TR & Hdone); exists t', w'; split; auto.
      + rewrite <- EQpq; auto.
      + rewrite EQpq; auto.
  Qed.

  Global Add Parametric Morphism: CuL
         with signature eq ==> equiv_ctll ==> equiv_ctll ==> equiv_ctll
           as equiv_ctll_equiv_until.
  Proof.
    intros [] p q EQpq p' q' EQpq'.
    - split; intros Hau; cinduction Hau; rewrite unfold_entailsL.
      + left; now rewrite <- EQpq'.
      + right; auto; now rewrite <- EQpq.
      + left; now rewrite EQpq'.
      + right; auto; now rewrite EQpq.
    - split; intros Heu; cinduction Heu.
      + left; now rewrite <- EQpq'.
      + right; destruct H0 as (m' & TR & Heu).
        * now rewrite <- EQpq.
        * exact H1. 
      + left; now rewrite EQpq'.
      + right; destruct H0 as (m' & TR & Heu).
        * now rewrite EQpq.
        * exact H1.
  Qed.

  Ltac coinduction_gg R CIH :=
  let R' := fresh R in
  setoid_rewrite unfold_entailsL;
  coinduction R' CIH.
  
  Global Add Parametric Morphism: Cg
         with signature (eq ==> equiv_ctll ==> equiv_ctll)
           as proper_equivctl_global.
  Proof.
    intros [] p q Heq; unfold equiv_ctll.  
    - split; revert t w; coinduction R CIH; intros; step in H; destruct H as (Hy & H0). 
      + constructor. 
        * now rewrite Heq in Hy.
        * rewrite Heq in Hy.
          destruct H0 as (Hs & Htr).
          split; auto.
          intros t' w' TR.
          apply CIH.
          rewrite unfold_entailsL; auto.
      + constructor.      
        * now rewrite <- Heq in Hy.
        * rewrite <- Heq in Hy.
          destruct H0 as (Hs & Htr).
          split; auto.
          intros t' w' TR.
          apply CIH.
          rewrite unfold_entailsL; auto.
    - split; revert t w; coinduction R CIH; intros; step in H;
        destruct H as (Hy & (t' & w' & TR & H0)).
      + constructor.
        * now rewrite Heq in Hy.
        * exists t', w'; split; auto.
      + constructor.
        * now rewrite <- Heq in Hy.
        * exists t', w'; split; auto.
  Qed.
  
End EquivCtllFormulas.

Section EquivCtlrFormulas.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Notation equiv_ctlr := (@equiv_ctlr M E HE KMS X).

   (*| Rewriting [equiv_ctl] over [entailsF] |*)
  Global Add Parametric Morphism: entailsR
         with signature (equiv_ctlr ==> eq ==> eq ==> iff)
           as proper_equiv_ctl_entailsR.
  Proof. intro x; induction x; intros y EQφ; apply EQφ. Qed.

  (*| Congruences over equiv_ctlr |*)
  Global Add Parametric Morphism: CAndR
         with signature equiv_ctll X ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_and.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; destruct EQpp'.
    + now apply EQpq.
    + now apply EQpq'.
    + now apply EQpq in H.
    + now apply EQpq' in H0.
  Qed.

  Global Add Parametric Morphism: COrR
         with signature equiv_ctlr ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_or.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; destruct EQpp'.
    + left; now apply EQpq.
    + right; now apply EQpq'.
    + left; now apply EQpq in H.
    + right; now apply EQpq' in H.
  Qed.

  Global Add Parametric Morphism: CImplR
         with signature equiv_ctlr ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_impl.
  Proof.
    intros p q EQpq p' q' EQpq'; split; rewrite unfold_entailsR;
      intros EQpp'; rewrite unfold_entailsR; intro HH; apply EQpq'; apply EQpq in HH;
      now apply EQpp'.
  Qed.

  Global Add Parametric Morphism: CxR
      with signature eq ==> equiv_ctlr ==> equiv_ctlr as equiv_ctlr_equiv_next.
  Proof.
    intros [] p q EQpq.
    - split; intros; rewrite ctlr_ax in *;
        destruct H; split; auto; intros.
      + rewrite <- EQpq; auto.
      + rewrite EQpq; auto.
    - split; intros; rewrite ctlr_ex in *;
        destruct H as (t' & w' & TR & Hdone); exists t', w'; split; auto.
      + rewrite <- EQpq; auto.
      + rewrite EQpq; auto.
  Qed.

  Global Add Parametric Morphism: CuR
         with signature eq ==> equiv_ctll X ==> equiv_ctlr ==> equiv_ctlr
           as equiv_ctlr_equiv_until.
  Proof.
    intros [] p q EQpq p' q' EQpq'.
    - split; intros Hau; cinduction Hau; rewrite unfold_entailsR.
      + left; now rewrite <- EQpq'.
      + right; auto; now rewrite <- EQpq.
      + left; now rewrite EQpq'.
      + right; auto; now rewrite EQpq.
    - split; intros Heu; cinduction Heu.
      + left; now rewrite <- EQpq'.
      + right; destruct H0 as (m' & TR & Heu).
        * now rewrite <- EQpq.
        * exact H1. 
      + left; now rewrite EQpq'.
      + right; destruct H0 as (m' & TR & Heu).
        * now rewrite EQpq.
        * exact H1.
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
    intros; split; rewrite ?unfold_entailsF.
    - intros [[] Hd]; ddestruction Hd.
      split; [|constructor].
      exists e, v; auto.
    - intros [(e & v & -> & Hφ) Hd]; split; auto with ctl.
  Qed.

  Lemma ctll_au_ax: forall (p q: ctll E),
      <( p AU q )> ⩸ <( q \/ (p /\ AX (p AU q)) )>.
  Proof.
    intros p q; split; intro Hind.
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
    intros p q; split; intro Hind.
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
    split; intros * Hp.
    - now destruct Hp.
    - split; auto.
  Qed.

  Lemma ctll_and_idR: forall (p: ctll E),
      <( p /\ ⊤ )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - split; auto.
  Qed.

  Lemma ctll_or_idL: forall (p: ctll E),
      <( ⊥ \/ p )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - now right. 
  Qed.

  Lemma ctll_or_idR: forall (p: ctll E),
      <( p \/ ⊥ )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
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
     split; intros * Hp.
     - step in Hp; inv Hp; split; auto.
     - destruct Hp.
       destruct H0; step; now constructor.
   Qed.

   Lemma ctll_eg_ex: forall (p: ctll E),
       <( EG p )> ⩸ <( p /\ EX (EG p) )>.
   Proof. 
     split; intros * Hp.
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
     split; intros; cinduction H.
     - apply ctll_af_ax. rewrite unfold_entailsL.
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
     split; intros; cinduction H.
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
     split; intros;
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
       split; auto; intros.       
   Qed.

   Lemma ctll_eg_involutive: forall (p: ctll E),
       <( EG p )> ⩸ <( EG (EG p) )>.
   Proof.
     split; intros;
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
  Infix "⩸" := (@equiv_ctlr M E HE KMS X) (at level 58, left associativity).
  
  Lemma ctlr_finish_done: forall (φ: X -> forall e, encode e -> Prop),
      <[ finish φ ]> ⩸ <[ done {fun x w => 
                                  exists (e: E) (v: encode e), w = Obs e v /\ φ x e v} ]>.
  Proof with eauto with ctl.
    intros; split; intro Hinv. 
    - apply ctlr_done.
      apply ctlr_finish in Hinv; inv Hinv; constructor;
        destruct H as (e' & v' & Hinv & ?); ddestruction Hinv...
    - apply ctlr_finish.
      apply ctlr_finish in Hinv; inv Hinv; constructor;
        destruct H as (e' & v' & Hinv & ?); ddestruction Hinv...
  Qed.
  
  Lemma ctlr_au_ax: forall (p: ctll E) (q: ctlr E X),
      <[ p AU q ]> ⩸ <[ q \/ (p /\ AX (p AU q)) ]>.
  Proof.
    intros p q; split; intro Hind.
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
      <[ p EU q ]> ⩸ <[ q \/ (p /\ EX (p EU q)) ]>.
  Proof.
    intros p q; split; intro Hind.
    - cinduction Hind. 
      + now left.
      + destruct H1 as (t' & w' & TR & ?).
        right; split; auto.
    - rewrite unfold_entailsR in Hind; destruct Hind.
      + now left. 
      + destruct H.
        now right. 
  Qed.

  Lemma ctlr_and_idL: forall (p: ctlr E X),
      <[ ⊤ /\ p ]> ⩸ <[ p ]>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - split; auto.
  Qed.

  Lemma ctlr_af_ax: forall (p: ctlr E X),
      <[ AF p ]> ⩸ <[ p \/ AX (AF p) ]>.
  Proof.
    intros.
    etransitivity.
    apply ctlr_au_ax.
    now rewrite ctlr_and_idL.
  Qed.

  Lemma ctlr_ef_ex: forall (p: ctlr E X),
      <[ EF p ]> ⩸ <[ p \/ EX (EF p) ]>.
  Proof.
    intros.
    etransitivity.
    apply ctlr_eu_ex.
    now rewrite ctlr_and_idL.
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
       <[ AF p ]> ⩸ <[ AF (AF p) ]>.
   Proof.
     split; intros; cinduction H.
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
       <[ EF p ]> ⩸ <[ EF (EF p) ]>.
   Proof.
     split; intros; cinduction H.
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
