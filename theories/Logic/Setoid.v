(*|
==============================================================
Congruence with respect a KripkeSetoid structure (simulation)
==============================================================
|*)
From Stdlib Require Import
  Basics
  Classes.SetoidClass
  Classes.Morphisms.

From Coinduction Require Import all.

From TICL Require Import
  Utils.Utils
  Logic.Kripke
  Logic.Semantics.

From Equations Require Import Equations.

Import TiclNotations CoindNotations.
Local Open Scope ticl_scope.
Local Open Scope type_scope.

Generalizable All Variables.

(** * Kripke setoids *)
(** Relation [meq] over [M X] is a Kripke setoid if
    the following square commutes

   [s, w]   ↦   [s', w']
     |             |
   meq s t     exists t', meq s' t'
     |             |
     v             v
   [t, w]   ↦   [t', w']
*)  
(** [KripkeSetoid] is a class that defines a Kripke setoid over a Kripke structure.
Meaning a kripke structure equipped with an equivalence relation. This is important
as we will show the equivalence relation preserves all Ticl specifications, a strong result.
This is akin to the result that strong bisimulation preserves all CTL specifications, but stronger
as Ticl extends CTL with post-conditions in suffix formulas. *)
Class KripkeSetoid (M: (Type -> Type) -> (Type -> Type) -> Type -> Type) (E B: Type -> Type)
  {K: Kripke M E B} X (meq: relation (M E B X)) {Eqm: Equivalence meq} :=
  ktrans_semiproper : forall (t s s': M E B X) w w',
    meq s t ->
    ktrans s w s' w' ->
    exists t', ktrans t w t' w' /\ meq s' t'.

Ltac ktrans_equ TR :=
    match type of TR with
      | @ktrans ?M ?E ?B ?KMS ?X ?y ?s ?z ?w =>
          match goal with
          | [HS: KripkeSetoid ?M ?E ?B ?X ?meq, 
                H: ?meq ?y ?x |- _] => 
              symmetry in H;
              let TR_ := fresh "TR" in
              let EQ_ := fresh "EQ" in
              let z_ := fresh "z" in
              destruct (ktrans_semiproper _ _ _ _ _
                          H TR) as (z_ & TR_ & EQ_)
          | [HS: KripkeSetoid ?M ?E ?B ?X ?meq,
                H: ?meq ?x ?y |- _] =>
              let TR_ := fresh "TR" in
              let EQ_ := fresh "EQ" in
              let z_ := fresh "z" in
              destruct (ktrans_semiproper _ _ _ _ _ H TR) as (z_ & TR_ & EQ_)
          end
    end.

(** * Models are setoids over TICL *)
Section EquivSetoid.
  Context `{K: Kripke M E B} {X} {meq: relation (M E B X)} {Eqm: Equivalence meq}
    {KS: KripkeSetoid M E B X meq}.

  Abbreviation MS := (M E B X).
  Abbreviation MP := (MS -> World E -> Prop).

  Global Add Parametric Morphism: can_step
    with signature meq ==> eq ==> iff as proper_can_step.
  Proof.
    intros t t' Heqt w;
      split; intros; subst; destruct H as (t_ & w_ & ?).
    - destruct (ktrans_semiproper t' t _ _ w_ Heqt H) as (y' & TR' & EQ').
      now (exists y', w_).
    - symmetry in Heqt.
      destruct (ktrans_semiproper _ _ _ _ w_ Heqt H) as (y' & TR' & EQ').
      now (exists y', w_).
  Qed.

  (** * [entailsF] is a congruence with regards to [meq] *)
  Global Add Parametric Morphism {φ: World E -> Prop}: (fun _ => φ)
      with signature meq ==> eq ==> iff as meq_proper_fun.
  Proof. intros; split; auto. Qed.
  
  Global Add Parametric Morphism p: (entailsR (CDone p))
        with signature meq ==> eq ==> iff as meq_proper_done.
  Proof. intros; rewrite unfold_entailsR; reflexivity. Qed.

  (** * Congruence with respect to binary modalities AN, EN, AU, EU *)
  Section Binary.
    Context {P Q: MP} {HP: Proper (meq ==> eq ==> iff) P} {HQ: Proper (meq ==> eq ==> iff) Q}.

    (** [anc] is a congruence with regards to [meq] *)
    Global Add Parametric Morphism: (anc P Q)
           with signature (meq ==> eq ==> iff) as proper_ax_equ.
    Proof.
      intros x y Heqt w; split; intros (Hp & Hs & HN). 
      - split; [now rewrite <- Heqt |split; [now rewrite <- Heqt|]].
        intros u z TR.
        ktrans_equ TR.
        apply HN in TR0.
        now rewrite EQ.
      - split; [now rewrite Heqt |split; [now rewrite Heqt|]].
        intros u z TR.
        ktrans_equ TR.
        apply HN in TR0.
        now rewrite EQ.
    Qed.      
    
    (** [enc] is a congruence with regards to [meq] *)
    Global Add Parametric Morphism: (enc P Q)
           with signature (meq ==> eq ==> iff) as proper_ex_equ.
    Proof.
      intros x y Heqt w; split; intros (Hp & x' & z & TR & HP');
        ktrans_equ TR.
      - split.
        + now rewrite <- Heqt.
        + exists z0, z; split; auto.
          now rewrite <- EQ.
      - split.
        + now rewrite <- Heqt.
        + exists z0, z; split; auto.
          now rewrite <- EQ.
    Qed.
    
    (** [auc] is a congruence with regards to [meq] *)
    Global Add Parametric Morphism: (auc P Q)
          with signature (meq ==> eq ==> iff) as proper_au_equ.
    Proof.
      intros x y EQ; split; intros * au.
      (* -> *)
      - generalize dependent y.
        induction au; intros y EQ.
        + rewrite EQ in H; now apply MatchA.
        + eapply StepA; try now rewrite <- EQ.
          destruct H as (Hp & Hs & ?), H0 as (_ & _ & ?).
          split2.
          * now rewrite <- EQ.
          * now rewrite <- EQ.
          * intros y' w' TR.
            ktrans_equ TR.
            eapply H0; [apply TR0|].
            now symmetry.
      (* <- *)
      - generalize dependent x.
        induction au; intros x EQ.
        + rewrite <- EQ in H; now apply MatchA.
        + eapply StepA; try now rewrite EQ.
          destruct H as (Hp & Hs & ?), H0 as (_ & _ & ?).
          split2.
          * now rewrite EQ.
          * now rewrite EQ.
          * intros y' w' TR.
            ktrans_equ TR.
            eapply H0; [apply TR0|].
            now symmetry.
    Qed.

    (** [euc] is a congruence with regards to [meq] *)
    Global Add Parametric Morphism: (euc P Q)
          with signature (meq ==> eq ==> iff) as proper_eu_equ.
    Proof.
      intros x y EQ; split; intro eu.
      (* -> *)
      - generalize dependent y.
        induction eu; intros.    
        + rewrite EQ in H; now apply MatchE.
        + destruct H as (Hp & t' & w' & TR' & Hind & Hy).
          eapply StepE; split.
          * now rewrite <- EQ.          
          * ktrans_equ TR'; exists z, w'; auto.
      - generalize dependent x.
        induction eu; intros.
        + rewrite <- EQ in H; now apply MatchE.
        + destruct H as (Hp & t' & w' & TR' & Hind & Hy). 
          eapply StepE; split.
          * now rewrite EQ.
          * ktrans_equ TR';
              exists z, w'; split; eauto.
            apply Hy.
            now symmetry.
    Qed.
  End Binary.

  (** * Congruence of the greatest fixpoints AG, EG *)
  (** Properness is inf-closed, so it propagates along the whole final chain
      of [agcF P]/[egcF P] (tower induction), hence to every chain element
      used in a proof by coinduction, and in particular to the [gfp]. *)
  Context {P: MP} {HP: Proper (meq ==> eq ==> iff) P}.

  Lemma inf_closed_proper_meq:
    inf_closed (fun R: MP => Proper (meq ==> eq ==> iff) R).
  Proof.
    intros T HT t t' Heqt w w' <-.
    split; intros H R HR; specialize (HT R HR).
    - apply (HT _ _ Heqt _ _ eq_refl), H, HR.
    - apply (HT _ _ Heqt _ _ eq_refl), H, HR.
  Qed.

  (** Every element of the final chain of [agcF P] is a congruence. *)
  Lemma agc_chain_proper: forall (R: Chain (agcF P)),
      Proper (meq ==> eq ==> iff) `R.
  Proof.
    apply tower.
    - apply inf_closed_proper_meq.
    - intros R HR; cbn.
      intros t t' Heqt w w' <-; apply (proper_ax_equ (Q:=`R)); auto.
  Qed.

  (** Every element of the final chain of [egcF P] is a congruence. *)
  Lemma egc_chain_proper: forall (R: Chain (egcF P)),
      Proper (meq ==> eq ==> iff) `R.
  Proof.
    apply tower.
    - apply inf_closed_proper_meq.
    - intros R HR; cbn.
      intros t t' Heqt w w' <-; apply (proper_ex_equ (Q:=`R)); auto.
  Qed.

  Global Add Parametric Morphism (R: Chain (agcF P)): (elem R)
         with signature (meq ==> eq ==> iff) as proper_agc_chain_equ.
  Proof. intros t t' Heqt w; apply (agc_chain_proper R); auto. Qed.

  Global Add Parametric Morphism (R: Chain (egcF P)): (elem R)
         with signature (meq ==> eq ==> iff) as proper_egc_chain_equ.
  Proof. intros t t' Heqt w; apply (egc_chain_proper R); auto. Qed.

  (** [agc] is a congruence with regards to [meq] *)
  Global Add Parametric Morphism: (agc P)
         with signature (meq ==> eq ==> iff) as proper_ag_equ.
  Proof. intros t t' Heqt w; apply (agc_chain_proper (chain_gfp _)); auto. Qed.

  (** [egc] is a congruence with regards to [meq] *)
  Global Add Parametric Morphism: (egc P)
         with signature (meq ==> eq ==> iff) as proper_er_equ.
  Proof. intros t t' Heqt w; apply (egc_chain_proper (chain_gfp _)); auto. Qed.

End EquivSetoid.

(** * Congruence with respect to TICL formulas *)
(** [entailsL] is a congruence with regards to [meq]. This is the main result of this file. *)
Global Add Parametric Morphism `{KS: KripkeSetoid M E B X meq} (φ: ticll E) :
  (entailsL X φ)
       with signature (meq ==> eq  ==> iff) as proper_entailsL_meq.
Proof.
  induction φ; intros * Heq w.
  - (* Now *) rewrite ?ticll_now; reflexivity. 
  - (* CuL *) destruct q; rewrite unfold_entailsL.
    + (* au *)
      refine (@proper_au_equ M E B K X meq Eqm KS (entailsL X φ1) (entailsL X φ2) _ _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
    + (* eu *)
      refine (@proper_eu_equ M E B K X meq Eqm KS (entailsL X φ1) (entailsL X φ2) _ _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* CxL *) destruct q; rewrite unfold_entailsL.
    + (* ax *)
      refine (@proper_ax_equ M E B K X meq Eqm KS (entailsL X φ1) (entailsL X φ2) _ _ _ _ Heq _ _ eq_refl);
        unfold Proper, respectful; intros; subst; auto.
    + (* ex *)
      refine (@proper_ex_equ M E B K X meq Eqm KS (entailsL X φ1) (entailsL X φ2) _ _ _ _ Heq _ _ eq_refl);
        unfold Proper, respectful; intros; subst; auto. 
  - (* Cg *) destruct q; rewrite unfold_entailsL.
    + (* ag *)
      refine (@proper_ag_equ M E B K X meq Eqm KS (entailsL X φ) _ _ _ Heq _ _ eq_refl);
        unfold Proper, respectful; intros; subst; auto.
    + (* er *)
      refine (@proper_er_equ M E B K X meq Eqm KS (entailsL X φ) _ _ _ Heq _ _ eq_refl);
        unfold Proper, respectful; intros; subst; auto.
  - (* /\ *) split; intros [Ha Hb]; split.
    + now rewrite <- (IHφ1 _ _ Heq).
    + now rewrite <- (IHφ2 _ _ Heq).
    + now rewrite (IHφ1 _ _ Heq).
    + now rewrite (IHφ2 _ _ Heq).
  - (* \/ *) split; intros; rewrite unfold_entailsL in *; destruct H.
    + left; now rewrite <- (IHφ1 _ _ Heq).
    + right; now rewrite <- (IHφ2 _ _ Heq).
    + left; now rewrite (IHφ1 _ _ Heq).
    + right; now rewrite (IHφ2 _ _ Heq).
Qed.

(** [entailsR] is a congruence with regards to [meq]. *)
Global Add Parametric Morphism `{KS: KripkeSetoid M E B X meq} (φ: ticlr E X) :
  (entailsR φ)
       with signature (meq ==> eq  ==> iff) as proper_entailsR_meq.
Proof.
  induction φ; intros * Heq w.
  - (* Done *) rewrite ?ticll_done; reflexivity. 
  - (* Ret *) rewrite ?ticlr_ret.
    split; intros (r & Hr & Han); exists r; split; auto.
    + refine (proj1 (@proper_ax_equ M E B K X meq Eqm KS (fun _ w => not_done w) (fun _ => done_of r w) _ _ _ _ Heq _ _ eq_refl) Han);
        unfold Proper, respectful; intros; subst; auto.
    + refine (proj2 (@proper_ax_equ M E B K X meq Eqm KS (fun _ w => not_done w) (fun _ => done_of r w) _ _ _ _ Heq _ _ eq_refl) Han);
        unfold Proper, respectful; intros; subst; auto.
  - (* CuR *) destruct q; rewrite unfold_entailsR.
    + (* au *)
      refine (@proper_au_equ M E B K X meq Eqm KS (entailsL X φ) (entailsR φ0) _ _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
    + (* eu *)
      refine (@proper_eu_equ M E B K X meq Eqm KS (entailsL X φ) (entailsR φ0) _ _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* CxR *) destruct q; rewrite unfold_entailsR. 
    + (* ax *)
      refine (@proper_ax_equ M E B K X meq Eqm KS (entailsL X φ) (entailsR φ0) _ _ _ _ Heq _ _ eq_refl);
        unfold Proper, respectful; intros; subst; auto.
    + (* ex *)
      refine (@proper_ex_equ M E B K X meq Eqm KS (entailsL X φ) (entailsR φ0) _ _ _ _ Heq _ _ eq_refl);
        unfold Proper, respectful; intros; subst; auto.
  - (* /\ *) split; rewrite unfold_entailsR; intros [Ha Hb]; rewrite unfold_entailsR; split.
    + now rewrite <- (IHφ1 _ _ Heq).
    + now rewrite <- (IHφ2 _ _ Heq).
    + now rewrite (IHφ1 _ _ Heq).
    + now rewrite (IHφ2 _ _ Heq).
  - (* /\ *) split; intros; rewrite ticlr_or in H |- *; destruct H.
    + left; now rewrite <- (IHφ1 _ _ Heq).
    + right; now rewrite <- (IHφ2 _ _ Heq).
    + left; now rewrite (IHφ1 _ _ Heq).
    + right; now rewrite (IHφ2 _ _ Heq).      
Qed.
