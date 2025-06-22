(*|
==============================================================
Congruence with respect a KripkeSetoid structure (simulation)
==============================================================
|*)
From Stdlib Require Import
  Basics
  Classes.SetoidClass
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice tactics.

From TICL Require Import
  Utils.Utils
  Events.Core
  Logic.Kripke
  Logic.Semantics.

From Equations Require Import Equations.

Import TiclNotations.
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
Class KripkeSetoid (M: forall E, Encode E -> Type -> Type) (E: Type) {HE: Encode E}
  {K: Kripke M E} X (meq: relation (M E HE X)) {Eqm: Equivalence meq} :=
  ktrans_semiproper : forall (t s s': M E HE X) w w',
    meq s t ->
    ktrans s w s' w' ->
    exists t', ktrans t w t' w' /\ meq s' t'.

Ltac ktrans_equ TR :=
    match type of TR with
      | @ktrans ?M ?E ?HE ?KMS ?X ?y ?s ?z ?w =>
          match goal with
          | [HS: KripkeSetoid ?M ?W ?X ?meq, 
                H: ?meq ?y ?x |- _] => 
              symmetry in H;
              let TR_ := fresh "TR" in
              let EQ_ := fresh "EQ" in
              let z_ := fresh "z" in
              destruct (ktrans_semiproper _ _ _ _ _
                          H TR) as (z_ & TR_ & EQ_)
          | [HS: KripkeSetoid ?M ?W ?X ?meq,
                H: ?meq ?x ?y |- _] =>
              let TR_ := fresh "TR" in
              let EQ_ := fresh "EQ" in
              let z_ := fresh "z" in
              destruct (ktrans_semiproper _ _ _ _ _ H TR) as (z_ & TR_ & EQ_)
          end
    end.

(** * Models are setoids over TICL *)
Section EquivSetoid.
  Context `{K: Kripke M E} {X} {meq: relation (M E HE X)} {Eqm: Equivalence meq}
    {KS: KripkeSetoid M E X meq}.

  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).

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

  (** Placeholder for properness, to be proved by induction and plugged in later. *)
  Context {P: MP} {HP: Proper (meq ==> eq ==> iff) P}.
  
  (** [meq] closure enchancing function. *)
  Variant mequ_clos_body(R : MP) : MP :=
    | mequ_clos_ctor : forall t0 w0 t1 w1
                         (Heqm : meq t0 t1)
                         (Heqw : w0 = w1)
                         (HR : R t1 w1),
        mequ_clos_body R t0 w0.
  Hint Constructors mequ_clos_body: core.

  Arguments impl /.
  Program Definition mequ_clos: mon MP :=
    {| body := mequ_clos_body |}.
  Next Obligation. repeat red; intros; destruct H0; subst; eauto. Qed.

  (** [meq] is under the coinductive companion [agct] *)
  Lemma mequ_clos_agc:
    mequ_clos <= agct P.
  Proof.
    apply Coinduction; cbn.
    intros R t0 w0 [t1 w1 t2 w2 Heq -> [Hp HR]]. 
    rewrite <- Heq in Hp.
    destruct HR as (Hs & HR').
    split; [auto | split].
    - now rewrite Heq.
    - intros t' w' TR.
      eapply (f_Tf (agcF P)). 
      ktrans_equ TR.
      eapply mequ_clos_ctor with (t1:=z); eauto. 
  Qed.

  (** [meq] is under the coinductive companion [egct] *)
  Lemma mequ_clos_egc:
    mequ_clos <= egct P.
  Proof.
    apply Coinduction; cbn.
    intros R t0 w0 [t1 w1 t2 w2 Heq -> [Hp HR]]. 
    rewrite <- Heq in Hp.
    destruct HR as (t' & w' & TR & HR). 
    split; [auto |].
    ktrans_equ TR.
    exists z, w'; split; auto.
    eapply (f_Tf (egcF P)). 
    eapply mequ_clos_ctor with (t1:=t') (w1:=w'); eauto.
    now symmetry.
  Qed.

  (** [agct] is a congruence with regards to [meq] *)
  Global Add Parametric Morphism RR: (agct P RR) with signature
         (meq ==> eq ==> iff) as proper_agt_equ.
  Proof.
    intros t t' Heqm w'; split; intro G; apply (ft_t mequ_clos_agc).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.

  (** [agcT] is a congruence with regards to [meq] *)
  Global Add Parametric Morphism RR f: (agcT P f RR)
         with signature (meq ==> eq ==> iff) as proper_agT_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (fT_T mequ_clos_agc).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  (** [agc] is a congruence with regards to [meq] *)
  Global Add Parametric Morphism: (agc P)
         with signature (meq ==> eq ==> iff) as proper_ag_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_agc).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.      

  (** [egct] is a congruence with regards to [meq] *)
  Global Add Parametric Morphism RR: (egct P RR)
         with signature (meq ==> eq ==> iff) as proper_egt_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_egc).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.

  (** [egcT] is a congruence with regards to [meq] *)
  Global Add Parametric Morphism RR f: (egcT P f RR)
         with signature (meq ==> eq ==> iff) as proper_egT_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (fT_T mequ_clos_egc).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.
  
  (** [egc] is a congruence with regards to [meq] *)
  Global Add Parametric Morphism: (egc P)
         with signature (meq ==> eq ==> iff) as proper_er_equ.
  Proof.
    intros t t' Heqt w'; split; intro G; apply (ft_t mequ_clos_egc).
    - eapply mequ_clos_ctor with (t1:=t); eauto.
      now symmetry.
    - eapply mequ_clos_ctor with (t1:=t'); eauto.
  Qed.

  (** * Congruence with respect to binary modalities AN, EN, AU, EU *)
  Context {Q: MP} {HQ: Proper (meq ==> eq ==> iff) Q}.

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

End EquivSetoid.

(** * Congruence with respect to TICL formulas *)
(** [entailsL] is a congruence with regards to [meq]. This is the main result of this file. *)
Global Add Parametric Morphism `{KS: KripkeSetoid M E X meq} (φ: ticll E) :
  (entailsL X φ)
       with signature (meq ==> eq  ==> iff) as proper_entailsL_meq.
Proof.
  induction φ; intros * Heq w.
  - (* Now *) rewrite ?ticll_now; reflexivity. 
  - (* CuL *) destruct q; rewrite unfold_entailsL.
    + (* au *)
      refine (@proper_au_equ M E HE K X meq Eqm KS (entailsL X φ1) _ (entailsL X φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
    + (* eu *)
      refine (@proper_eu_equ M E HE K X meq Eqm KS (entailsL X φ1) _ (entailsL X φ2) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* CxL *) destruct q; rewrite unfold_entailsL.
    + (* ax *)
      refine (@proper_ax_equ M E HE K X meq Eqm KS (entailsL X φ1) _ (entailsL X φ2) _ _ _ Heq _ _ eq_refl);
        unfold Proper, respectful; intros; subst; auto.
    + (* ex *)
      refine (@proper_ex_equ M E HE K X meq Eqm KS (entailsL X φ1) _ (entailsL X φ2) _ _ _ Heq _ _ eq_refl);
        unfold Proper, respectful; intros; subst; auto. 
  - (* Cg *) destruct q; rewrite unfold_entailsL.
    + (* ag *)
      refine (@proper_ag_equ M E HE K X meq Eqm KS (entailsL X φ) _ _ _ Heq _ _ eq_refl);
        unfold Proper, respectful; intros; subst; auto.
    + (* er *)
      refine (@proper_er_equ M E HE K X meq Eqm KS (entailsL X φ) _ _ _ Heq _ _ eq_refl);
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
Global Add Parametric Morphism `{KS: KripkeSetoid M E X meq} (φ: ticlr E X) :
  (entailsR φ)
       with signature (meq ==> eq  ==> iff) as proper_entailsR_meq.
Proof.
  induction φ; intros * Heq w.
  - (* Done *) rewrite ?ticll_done; reflexivity. 
  - (* CuR *) destruct q; rewrite unfold_entailsR.
    + (* au *)
      refine (@proper_au_equ M E HE K X meq Eqm KS (entailsL X φ) _ (entailsR φ0) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
    + (* eu *)
      refine (@proper_eu_equ M E HE K X meq Eqm KS (entailsL X φ) _ (entailsR φ0) _ _ _ Heq _ _ eq_refl);
      unfold Proper, respectful; intros; subst; auto.
  - (* CxR *) destruct q; rewrite unfold_entailsR. 
    + (* ax *)
      refine (@proper_ax_equ M E HE K X meq Eqm KS (entailsL X φ) _ (entailsR φ0) _ _ _ Heq _ _ eq_refl);
        unfold Proper, respectful; intros; subst; auto.
    + (* ex *)
      refine (@proper_ex_equ M E HE K X meq Eqm KS (entailsL X φ) _ (entailsR φ0) _ _ _ Heq _ _ eq_refl);
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
  - (* -> *)
    split; intros * H; rewrite unfold_entailsR in *; intro HI;
      apply (IHφ _ _ Heq), H.
    + now rewrite Heq.
    + now rewrite <- Heq.
Qed.