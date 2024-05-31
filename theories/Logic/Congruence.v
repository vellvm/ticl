(*| Congruences [equiv_ctl] of CTL logic |*)
From Coq Require Import
  Basics
  Classes.SetoidClass
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice tactics.

From CTree Require Import
  Utils.Utils
  Logic.Semantics
  Logic.Setoid
  Logic.Tactics.

Import CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope type_scope.

Set Implicit Arguments.
Generalizable All Variables.

(*| Equations of CTL |*)
Section EquivCtlFormulas.
  Context `{K: Kripke M W} {X: Type}.  
  Notation MP := (M X -> World W -> Prop).
  Notation equiv_ctl b := (@equiv_ctl M W HE K X b).

  (*| Rewriting [equiv_ctl] over [entailsF] |*)
  Global Add Parametric Morphism{b}: (entailsF (X:=X))
         with signature (equiv_ctl b ==> eq ==> eq ==> iff)
           as proper_equiv_ctl_entailsF.
  Proof. intro x; induction x; intros y EQφ; apply EQφ. Qed.

  Arguments CAnd {W} {HW} {X} {a b}.
  (*| Congruences over equiv_ctl |*)
  Global Add Parametric Morphism{a b}: CAnd
         with signature equiv_ctl a ==> equiv_ctl b ==> equiv_ctl (a||b)
           as equiv_ctl_equiv_and.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; destruct EQpp'.
    + now apply EQpq.
    + now apply EQpq'.
    + now apply EQpq in H.
    + now apply EQpq' in H0.
  Qed.

  Arguments COr {W} {HW} {X} {a b}.
  Global Add Parametric Morphism{a b}: COr
         with signature equiv_ctl a  ==> equiv_ctl b ==> equiv_ctl (a||b)
           as equiv_ctl_equiv_or.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; destruct EQpp'.
    + left; now apply EQpq.
    + right; now apply EQpq'.
    + left; now apply EQpq in H.
    + right; now apply EQpq' in H.
  Qed.

  Arguments CImpl {W} {HW} {X} {a b}.
  Global Add Parametric Morphism{a b}: CImpl
         with signature equiv_ctl a ==> equiv_ctl b ==> equiv_ctl (a||b)
           as equiv_ctl_equiv_impl.
  Proof.
    intros p q EQpq p' q' EQpq'; split; rewrite unfold_entailsF;
      intros EQpp'; rewrite unfold_entailsF; intro HH; apply EQpq'; apply EQpq in HH;
      now apply EQpp'.
  Qed.

  Arguments CAX {W} {HW} {X} {b}.
  Global Add Parametric Morphism{b}: CAX
      with signature equiv_ctl b ==> equiv_ctl b as equiv_ctl_equiv_ax.
  Proof.
    intros p q EQpq; split; intros; rewrite unfold_ax in *;
      destruct H; split; auto; intros.
    - rewrite <- EQpq; auto.
    - rewrite EQpq; auto.
  Qed.

  Arguments CEX {W} {HW} {X} {b}.
  Global Add Parametric Morphism{b}: CEX
      with signature equiv_ctl b ==> equiv_ctl b as equiv_ctl_equiv_ex.
  Proof.
    intros p q EQpq; split; intros; rewrite unfold_ex in *;
      destruct H as (t' & w' & TR & Hdone); exists t', w'; split; auto.
    - now rewrite <- EQpq.
    - now rewrite EQpq. 
  Qed.

  Arguments CAU {W} {HW} {X} {b}.
  Global Add Parametric Morphism{b}: CAU
         with signature equiv_ctl false ==> equiv_ctl b ==> equiv_ctl b
           as equiv_ctl_equiv_au.
  Proof.
    intros p q EQpq p' q' EQpq'.
    split; intros Hau; cinduction Hau.
    - cright; now rewrite <- EQpq'.
    - cleft; auto; now rewrite <- EQpq.
    - cright; now rewrite EQpq'.
    - cleft; auto; now rewrite EQpq.
  Qed.

  Arguments CEU {W} {HW} {X} {b}.
  Global Add Parametric Morphism{b}: CEU
         with signature equiv_ctl false ==> equiv_ctl b ==> equiv_ctl b
           as equiv_ctl_equiv_eu.
  Proof.
    intros p q EQpq p' q' EQpq'.
    split; intros Heu; cinduction Heu.
    - cright; now rewrite <- EQpq'.
    - cleft; destruct H0 as (m' & TR & Heu).
      + now rewrite <- EQpq.
      + exact H1. 
    - cright; now rewrite EQpq'.
    - cleft; destruct H0 as (m' & TR & Heu).
      + now rewrite EQpq.
      + exact H1.
  Qed.

  Arguments CAR {W} {HW} {X} {b}.
  Global Add Parametric Morphism{b}: CAR with signature
         (equiv_ctl false ==> equiv_ctl b ==> equiv_ctl b)
           as proper_equivctl_ar.
  Proof.
    intros.
    unfold equiv_ctl.
    split; revert t w; coinduction R CIH; intros; step in H1; cbn in H1; inv H1.
    - apply RMatchA.
      + now rewrite <- H0.
      + now rewrite <- H.
    - apply RStepA.
      + now rewrite <- H.
      + destruct H3; split; auto.
        intros t' w' TR.
        apply CIH.
        rewrite unfold_entailsF.
        now apply H3.
    - apply RMatchA.
      + now rewrite H0.
      + now rewrite H.
    - apply RStepA.
      + now rewrite H.
      + destruct H3; split; auto.
        intros t' w' TR.
        apply CIH.
        rewrite unfold_entailsF.
        now apply H3.
  Qed.
  
  Arguments CER {W} {HW} {X} {b}.
  Global Add Parametric Morphism {b}: CER with signature
         (equiv_ctl false ==> equiv_ctl b ==> equiv_ctl b)
           as proper_equivctl_er.
  Proof.
    intros.
    unfold equiv_ctl.
    split; revert t w; coinduction R CIH; intros; step in H1; cbn in H1; inv H1.
    - apply RMatchE.
      + now rewrite <- H0.
      + now rewrite <- H.
    - apply RStepE.
      + now rewrite <- H.
      + destruct H3 as (t' & w' & TR & H').
        exists t', w'; intuition.
    - apply RMatchE.
      + now rewrite H0.
      + now rewrite H.
    - apply RStepE.
      + now rewrite H.
      + destruct H3 as (t' & w' & TR & H').
        exists t', w'; intuition.
  Qed.
  
End EquivCtlFormulas.

(*| Equations of CTL |*)
Section CtlEquations.
  Context `{KMS: Kripke M W} {X: Type} {b: bool}.
  Notation MP := (M X * World W -> Prop).  
  Infix "⩸" := (equiv_ctl (K:=KMS) (X:=X)) (at level 58, left associativity).
  
  Lemma ctl_au_ax: forall (p: ctlf W X false) (q: ctlf W X b),
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

  Lemma ctl_eu_ex: forall p q,
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
  
  Lemma ctl_and_idL: forall (p: ctlf W),
      <( ⊤ /\ p )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - split; auto.
  Qed.

  Lemma ctl_and_idR: forall (p: ctlf W),
      <( p /\ ⊤ )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - split; auto.
  Qed.

  Lemma ctl_or_idL: forall (p: ctlf W),
      <( ⊥ \/ p )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - now right. 
  Qed.

  Lemma ctl_or_idR: forall (p: ctlf W),
      <( p \/ ⊥ )> ⩸ <( p )>.
  Proof.
    split; intros * Hp.
    - now destruct Hp.
    - now left.
  Qed.

  Lemma ctl_af_ax: forall (p: ctlf W),
      <( AF p )> ⩸ <( p \/ AX (AF p) )>.
  Proof.
    intros.
    etransitivity.
    apply ctl_au_ax.
    now rewrite ctl_and_idL.
  Qed.

  Lemma ctl_ef_ex: forall (p: ctlf W),
      <( EF p )> ⩸ <( p \/ EX (EF p) )>.
  Proof.
    intros.
    etransitivity.
    apply ctl_eu_ex.
    now rewrite ctl_and_idL.
  Qed.

  Lemma ctl_ar_ax: forall (p q: ctlf W),
      <( p AR q )> ⩸ <( p /\ (q \/ AX (p AR q)) )>.
   Proof. 
     split; intros * Hp.
     - step in Hp; inv Hp; csplit.
       + assumption.
       + now cleft. 
       + assumption. 
       + now cright.
     - cdestruct Hp.
       destruct H0; step; now constructor.
   Qed.

   Lemma ctl_er_ex: forall (p q: ctlf W),
      <( p ER q )> ⩸ <( p /\ (q \/ EX (p ER q)) )>.
   Proof. 
     split; intros * Hp.
     - split; step in Hp; inv Hp.
       + assumption.
       + assumption.
       + now left.
       + now right.
     - destruct Hp.
       destruct H0; step; now constructor.
   Qed.

   Lemma ctl_ag_ax: forall (p: ctlf W),
       <( AG p )> ⩸ <( p /\ AX (AG p) )>.
   Proof.
     etransitivity.
     - apply ctl_ar_ax.
     - now rewrite ctl_or_idL.
   Qed.

   Lemma ctl_eg_ex: forall (p: ctlf W),
       <( EG p )> ⩸ <( p /\ EX (EG p) )>.
   Proof.
     etransitivity.
     - apply ctl_er_ex.
     - now rewrite ctl_or_idL.
   Qed.

   (* LEF: The opposite direction does not seem provable at this level
      of abstraction. *)
   Lemma ctl_afax_axaf: forall (p: ctlf W) (t: M X) w,
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
   
   Lemma ctl_af_involutive: forall (p: ctlf W),
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

   Lemma ctl_ef_involutive: forall (p: ctlf W),
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
   
   Lemma ctl_ag_involutive: forall (p: ctlf W),
       <( AG p )> ⩸ <( AG (AG p) )>.
   Proof.
     split; intros;
       revert H; revert t w; coinduction R CIH; intros t' w' Hag.     
     - apply RStepA; auto.
       apply ctl_ag_ax in Hag; cdestruct Hag.
       cdestruct H0.
       split; auto. 
     - rewrite ctl_ag_ax in Hag.      
       cdestruct Hag.
       cdestruct H0.
       rewrite ctl_ag_ax in H.
       cdestruct H.
       apply RStepA; auto.
       split; auto; intros.       
   Qed.

   Lemma ctl_eg_involutive: forall (p: ctlf W),
       <( EG p )> ⩸ <( EG (EG p) )>.
   Proof.
     split; intros;
       revert H; revert t w; coinduction R CIH; intros t' w' Heg.     
     - apply RStepE; auto.
       apply ctl_eg_ex in Heg; cdestruct Heg.
       cdestruct H0.
       exists t, w; intuition.
     - rewrite ctl_eg_ex in Heg.      
       cdestruct Heg.
       cdestruct H0.
       rewrite ctl_eg_ex in H.
       cdestruct H.
       apply RStepE; auto.
       exists t, w; intuition.
   Qed.
End CtlEquations.

(*| Ltac Tactic [next], rewrite au, af, ag, ar, eu, ef, er, eg
    to a disjunction/conjucntion with ax, ex respectively |*)
#[global] Tactic Notation "next" :=
  lazymatch goal with
  | |- context[@entailsF ?M ?W ?HE ?KMS ?X ?φ ?t ?w] =>
      lazymatch φ with
      | CAX ?p => apply (@unfold_ax M W HE KMS X)
      | CEX ?p => apply (@unfold_ex M W HE KMS X)
      | CAU ?p ?q => lazymatch eval cbv in p with
                    | CBase (fun _ => True) =>
                        apply (@ctl_af_ax M W HE KMS X)
                    | _ => apply (@ctl_au_ax M W HE KMS X)
                    end
      | CEU ?p ?q => lazymatch eval cbv in p with
                    | CBase (fun _ => True) =>
                        apply (@ctl_ef_ex M W HE KMS X)
                    | _ => apply (@ctl_eu_ex M W HE KMS X)
                    end
      | CAR ?p ?q => lazymatch eval cbv in q with
                    | CBase (fun _ => False) =>
                        apply (@ctl_ag_ax M W HE KMS X)
                    | _ => apply (@ctl_ar_ax M W HE KMS X)
                    end
      | CER ?p ?q => lazymatch eval cbv in q with
                    | CBase (fun _ => False) =>
                        apply (@ctl_eg_ex M W HE KMS X)
                    | _ => apply (@ctl_er_ex M W HE KMS X)
                    end
      | ?ptrivial => fail "Cannot step formula " ptrivial
      end
  end.

#[global] Tactic Notation "next" "in" ident(H) :=
  lazymatch type of H with
  | context[@entailsF ?M ?W ?HE ?KMS ?X ?φ ?t ?w] =>
      lazymatch φ with
      | CAX ?p => rewrite (@unfold_ax M W HE KMS X) in H
      | CEX ?p => rewrite (@unfold_ex M W HE KMS X) in H
      | context[CAU ?p ?q] =>
          lazymatch eval cbv in p with
          | CBase (fun _ => True) =>
              rewrite (@ctl_af_ax M W HE KMS X q) in H
          | _ => rewrite (@ctl_au_ax M W HE KMS X p q) in H
          end
      | context[CEU ?p ?q] =>
          lazymatch eval cbv in p with
          | CBase (fun _ => True) => rewrite (@ctl_ef_ex M W HE KMS X q) in H
          | _ => rewrite (@ctl_eu_ex M W HE KMS X p q) in H
          end
      | context[CAR ?p ?q] =>
          lazymatch eval cbv in q with
          | CBase (fun _ => False) => rewrite (@ctl_ag_ax M W HE KMS X p) in H
          | _ => rewrite (@ctl_ar_ax M W HE KMS X p q) in H
          end
      | context[CER ?p ?q] =>
          lazymatch eval cbv in q with
          | CBase (fun _ => False) => rewrite (@ctl_eg_ex M W HE KMS X p) in H
          | _ => rewrite (@ctl_er_ex M W HE KMS X p q) in H
          end
      | ?ptrivial => fail "Cannot step formula " ptrivial " in " H
      end
  end.
