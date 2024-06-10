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
  Logic.Setoid
  Logic.Tactics.

Import CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope type_scope.

Generalizable All Variables.

(*| Equations of CTL |*)
Section EquivCtlFormulas.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Notation equiv_ctl := (@equiv_ctl M E HE KMS X).

  (*| Rewriting [equiv_ctl] over [entailsF] |*)
  Global Add Parametric Morphism: (entailsF (X:=X))
         with signature (equiv_ctl ==> eq ==> eq ==> iff)
           as proper_equiv_ctl_entailsF.
  Proof. intro x; induction x; intros y EQφ; apply EQφ. Qed.

  (*| Congruences over equiv_ctl |*)
  Global Add Parametric Morphism: CAnd
         with signature equiv_ctl ==> equiv_ctl ==> equiv_ctl
           as equiv_ctl_equiv_and.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; destruct EQpp'.
    + now apply EQpq.
    + now apply EQpq'.
    + now apply EQpq in H.
    + now apply EQpq' in H0.
  Qed.

  Global Add Parametric Morphism: COr
         with signature equiv_ctl ==> equiv_ctl ==> equiv_ctl
           as equiv_ctl_equiv_or.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; destruct EQpp'.
    + left; now apply EQpq.
    + right; now apply EQpq'.
    + left; now apply EQpq in H.
    + right; now apply EQpq' in H.
  Qed.

  Global Add Parametric Morphism: CImpl
         with signature equiv_ctl ==> equiv_ctl ==> equiv_ctl
           as equiv_ctl_equiv_impl.
  Proof.
    intros p q EQpq p' q' EQpq'; split; rewrite unfold_entailsF;
      intros EQpp'; rewrite unfold_entailsF; intro HH; apply EQpq'; apply EQpq in HH;
      now apply EQpp'.
  Qed.

  Global Add Parametric Morphism: Cx
      with signature eq ==> equiv_ctl ==> equiv_ctl as equiv_ctl_equiv_next.
  Proof.
    intros [] p q EQpq.
    - split; intros; rewrite ctl_ax in *;
        destruct H; split; auto; intros.
      + rewrite <- EQpq; auto.
      + rewrite EQpq; auto.
    - split; intros; rewrite ctl_ex in *;
        destruct H as (t' & w' & TR & Hdone); exists t', w'; split; auto.
      + now rewrite <- EQpq.
      + now rewrite EQpq. 
  Qed.

  Global Add Parametric Morphism: Cu
         with signature eq ==> equiv_ctl ==> equiv_ctl ==> equiv_ctl
           as equiv_ctl_equiv_until.
  Proof.
    intros [] p q EQpq p' q' EQpq'.
    - split; intros Hau; cinduction Hau.
      + cright; now rewrite <- EQpq'.
      + cleft; auto; now rewrite <- EQpq.
      + cright; now rewrite EQpq'.
      + cleft; auto; now rewrite EQpq.
    - split; intros Heu; cinduction Heu.
      + right; now rewrite <- EQpq'.
      + left; destruct H0 as (m' & TR & Heu).
        * now rewrite <- EQpq.
        * exact H1. 
      + right; now rewrite EQpq'.
      + left; destruct H0 as (m' & TR & Heu).
        * now rewrite EQpq.
        * exact H1.
  Qed.

  Global Add Parametric Morphism: Cg
         with signature (eq ==> equiv_ctl ==> equiv_ctl)
           as proper_equivctl_global.
  Proof.
    intros [] p q Heq; unfold equiv_ctl.  
    - split; revert t w; coinduction R CIH; intros; step in H; destruct H as (Hy & H0). 
      + constructor. 
        * now rewrite Heq in Hy.
        * rewrite Heq in Hy.
          destruct H0 as (Hs & Htr).
          split; auto.
          intros t' w' TR.
          apply CIH.
          rewrite unfold_entailsF.
          now apply Htr.
      + constructor.      
        * now rewrite <- Heq in Hy.
        * rewrite <- Heq in Hy.
          destruct H0 as (Hs & Htr).
          split; auto.
          intros t' w' TR.
          apply CIH.
          rewrite unfold_entailsF.
          now apply Htr.
    - split; revert t w; coinduction R CIH; intros; step in H;
        destruct H as (Hy & (t' & w' & TR & H0)).
      + constructor.
        * now rewrite Heq in Hy.
        * exists t', w'; split; auto.
      + constructor.
        * now rewrite <- Heq in Hy.
        * exists t', w'; split; auto.
  Qed.
  
End EquivCtlFormulas.

(*| Equations of CTL |*)
Section CtlEquations.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).  
  Infix "⩸" := (equiv_ctl X (K:=KMS)) (at level 58, left associativity).

  Lemma ctl_vis_now: forall φ,
      <( vis φ )> ⩸ <( now {fun w => exists (e: E) (v: encode e), w = Obs e v /\ φ e v} )>.
  Proof.
    intros; split; rewrite ?unfold_entailsF.
    - intros [[] Hd]; ddestruction Hd.
      split; [|constructor].
      exists e, v; auto.
    - intros [(e & v & -> & Hφ) Hd]; split; auto with ctl.
  Qed.

  Lemma ctl_finish_done: forall (φ: X -> forall e, encode e -> Prop),
      <( finish φ )> ⩸ <( done {fun x w => 
                                  exists (e: E) (v: encode e), w = Obs e v /\ φ x e v})>.
  Proof.
    intros; split; intro Hinv. 
    - apply ctl_done.
      apply ctl_finish in Hinv; inv Hinv; constructor;
        destruct H as (e' & v' & Hinv & ?); ddestruction Hinv; eauto with ctl.
    - apply ctl_finish.
      apply ctl_finish in Hinv; inv Hinv; constructor;
        destruct H as (e' & v' & Hinv & ?); ddestruction Hinv; eauto with ctl.
  Qed.

  Lemma ctl_au_ax: forall (p q: ctlf E),
      <( p AU q )> ⩸ <( q \/ (p /\ AX (p AU q)) )>.
  Proof.
    intros p q; split; intro Hind.
    - cinduction Hind. 
      + now cleft.
      + destruct H1 as ([? ?] & ?).
        cright; split; auto.
    - cdestruct Hind.
      + now cright. 
      + cdestruct H.
        cdestruct H0.
        cleft; auto.
        split; auto.
  Qed.

  Lemma ctl_eu_ex: forall (p q: ctlf E),
      <( p EU q )> ⩸ <( q \/ (p /\ EX (p EU q)) )>.
  Proof.
    intros p q; split; intro Hind.
    - cinduction Hind. 
      + now cleft.
      + destruct H1 as (t' & w' & TR & ?).
        cright; csplit; auto.
    - cdestruct Hind.
      + now cright. 
      + cdestruct H.
        now cleft.
  Qed.
  
  Lemma ctl_and_idL: forall (p: ctlf E),
      <( ⊤ /\ p )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - split; auto.
  Qed.

  Lemma ctl_and_idR: forall (p: ctlf E),
      <( p /\ ⊤ )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - split; auto.
  Qed.

  Lemma ctl_or_idL: forall (p: ctlf E),
      <( ⊥ \/ p )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - now right. 
  Qed.

  Lemma ctl_or_idR: forall (p: ctlf E),
      <( p \/ ⊥ )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - now left.
  Qed.

  Lemma ctl_af_ax: forall (p: ctlf E),
      <( AF p )> ⩸ <( p \/ AX (AF p) )>.
  Proof.
    intros.
    etransitivity.
    apply ctl_au_ax.
    now rewrite ctl_and_idL.
  Qed.

  Lemma ctl_ef_ex: forall (p: ctlf E),
      <( EF p )> ⩸ <( p \/ EX (EF p) )>.
  Proof.
    intros.
    etransitivity.
    apply ctl_eu_ex.
    now rewrite ctl_and_idL.
  Qed.

  Lemma ctl_ag_ax: forall (p: ctlf E),
      <( AG p )> ⩸ <( p /\ AX (AG p) )>.
   Proof. 
     split; intros * Hp.
     - step in Hp; inv Hp; csplit; auto.
     - cdestruct Hp.
       destruct H0; step; now constructor.
   Qed.

   Lemma ctl_eg_ex: forall (p: ctlf E),
       <( EG p )> ⩸ <( p /\ EX (EG p) )>.
   Proof. 
     split; intros * Hp.
     - split; step in Hp; inv Hp; auto.
     - cdestruct Hp.
       step; now constructor.
   Qed.

   (* LEF: The opposite direction does not seem provable at this level
      of abstraction. *)
   Lemma ctl_afax_axaf: forall (p: ctlf E) (t: MS) w,
       <( t, w |= AF AX p )> -> <( t, w |= AX AF p )>.
   Proof.
     intros * H.
     cinduction H.
     + cdestruct H.
       split; auto.
       intros t' w' TR.
       apply ctl_af_ax.
       left.
       now apply H.
     + destruct H0, H1; clear H H1.
       split; auto.
       intros t' w' TR.       
       pose proof (H3 _ _ TR).
       cdestruct H. 
       apply ctl_af_ax.
       right.
       now apply H3.
   Qed.

   Lemma ctl_af_involutive: forall (p: ctlf E),
       <( AF p )> ⩸ <( AF (AF p) )>.
   Proof.
     split; intros; induction H.
     - apply ctl_af_ax; left.
       now apply ctl_af_ax; left.
     - destruct H0, H1; clear H1.
       apply ctl_af_ax; right; split; auto.
     - apply H.
     - destruct H0, H1; clear H1 H.
       apply ctl_af_ax; right; split; auto.
   Qed.

   Lemma ctl_ef_involutive: forall (p: ctlf E),
       <( EF p )> ⩸ <( EF (EF p) )>.
   Proof.
     split; intros; cinduction H.
     - apply ctl_ef_ex; left.
       now apply ctl_ef_ex; left.
     - destruct H1 as (t1 & w1 & TR1 & H1). 
       apply ctl_ef_ex; right.
       exists t1, w1; auto.
     - apply H.
     - destruct H1 as (t1 & w1 & TR1 & H1). 
       apply ctl_ef_ex; right.
       exists t1, w1; auto.
   Qed.
   
   Lemma ctl_ag_involutive: forall (p: ctlf E),
       <( AG p )> ⩸ <( AG (AG p) )>.
   Proof.
     split; intros;
       revert H; revert t w; coinduction R CIH; intros t' w' Hag.     
     - constructor; auto. 
       apply ctl_ag_ax in Hag; cdestruct Hag.
       cdestruct H0.
       split; auto. 
     - rewrite ctl_ag_ax in Hag.      
       cdestruct Hag.
       cdestruct H0.
       rewrite ctl_ag_ax in H.
       cdestruct H.
       constructor; auto.
       split; auto; intros.       
   Qed.

   Lemma ctl_eg_involutive: forall (p: ctlf E),
       <( EG p )> ⩸ <( EG (EG p) )>.
   Proof.
     split; intros;
       revert H; revert t w; coinduction R CIH; intros t' w' Heg.     
     - constructor; auto.
       apply ctl_eg_ex in Heg; cdestruct Heg.
       cdestruct H0.
       exists t, w; intuition.
     - rewrite ctl_eg_ex in Heg.      
       cdestruct Heg.
       cdestruct H0.
       rewrite ctl_eg_ex in H.
       cdestruct H.
       constructor; auto.
       exists t, w; intuition.
   Qed.
End CtlEquations.

(*| Ltac Tactic [next], rewrite au, af, ag, ar, eu, ef, er, eg
    to a disjunction/conjucntion with ax, ex respectively |*)
#[global] Tactic Notation "next" :=
  lazymatch goal with
  | |- context[@entailsF ?M ?E ?HE ?KMS ?X ?φ ?t ?w] =>
      lazymatch φ with
      | Cx Q_A ?p => apply (@ctl_ax M E HE KMS X)
      | Cx Q_E ?p => apply (@ctl_ex M E HE KMS X)
      | Cg Q_A ?p => apply (@ctl_ag_ax M E HE KMS X)
      | Cg Q_E ?p => apply (@ctl_eg_ex M E HE KMS X)
      | Cu Q_A (CProp True) ?q =>
          apply (@ctl_af_ax M E HE KMS X)
      | Cu Q_A ?p ?q =>
          apply (@ctl_au_ax M E HE KMS X)
      | Cu Q_E (CProp True) ?q =>
          apply (@ctl_ef_ex M E HE KMS X)
      | Cu Q_A ?p ?q =>
          apply (@ctl_eu_ex M E HE KMS X)
      | ?ptrivial => fail "Cannot step formula " ptrivial
      end
  end.

#[global] Tactic Notation "next" "in" ident(H) :=
  lazymatch type of H with
  | context[@entailsF ?M ?E ?HE ?KMS ?X ?φ ?t ?w] =>
      lazymatch φ with
      | Cx Q_A ?p => rewrite (@ctl_ax M E HE KMS X) in H
      | Cx Q_E ?p => rewrite (@ctl_ex M E HE KMS X) in H
      | context[Cg Q_A ?p] => rewrite (@ctl_ag_ax M E HE KMS X p) in H
      | context[Cg Q_E ?p] => rewrite (@ctl_eg_ex M E HE KMS X p) in H
      | context[Cu Q_A (CProp True) ?q] =>
          rewrite (@ctl_af_ax M E HE KMS X q) in H
      | context[Cu Q_A ?p ?q] =>
          rewrite (@ctl_au_ax M E HE KMS X p q) in H
      | context[Cu Q_E (CProp True) ?q] =>
          rewrite (@ctl_ef_ex M E HE KMS X q) in H
      | context[Cu Q_E ?p ?q] =>
          rewrite (@ctl_eu_ex M E HE KMS X p q) in H
      | ?ptrivial => fail "Cannot step formula " ptrivial " in " H
      end
  end.
