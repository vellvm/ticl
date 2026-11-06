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

    Global Instance proper_qnext_equ (q : ticlq) :
      Proper (meq ==> eq ==> iff) (qnext q P Q).
    Proof. destruct q; cbn [qnext]; typeclasses eauto. Qed.

    Global Instance proper_quntil_equ (q : ticlq) :
      Proper (meq ==> eq ==> iff) (quntil q P Q).
    Proof. destruct q; cbn [quntil]; typeclasses eauto. Qed.
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
(** [entails] preserves model equivalence at either formula mode. *)
Global Add Parametric Morphism `{KS: KripkeSetoid M E B X meq}
    (b : bool) (φ : ticl_at E X b) :
  (entails X b φ)
       with signature (meq ==> eq ==> iff) as proper_entails_meq.
Proof.
  assert (Hall : forall b (p : ticl_at E X b),
      Proper (meq ==> eq ==> iff) (entails X b p)).
  { apply (@ticl_at_ind E X
      (fun b p => Proper (meq ==> eq ==> iff) (entails X b p))).
    - intros p t t' Heq w w' <-; rewrite !ticl_now; reflexivity.
    - intros p t t' Heq w w' <-; rewrite !ticl_ret.
      split; intros (r & Hr & Han); exists r; split; auto.
      + refine (proj1 (@proper_ax_equ M E B K X meq Eqm KS
          (fun _ w => not_done w) (fun _ => done_of r w)
          _ _ _ _ Heq _ _ eq_refl) Han);
          unfold Proper, respectful; intros; subst; reflexivity.
      + refine (proj2 (@proper_ax_equ M E B K X meq Eqm KS
          (fun _ w => not_done w) (fun _ => done_of r w)
          _ _ _ _ Heq _ _ eq_refl) Han);
          unfold Proper, respectful; intros; subst; reflexivity.
    - intros b' q p IHp r IHr t t' Heq w w' <-; destruct q.
      + rewrite !ticl_au.
        exact (@proper_au_equ M E B K X meq Eqm KS
          (entails X false p) (entails X b' r) IHp IHr
          t t' Heq w w eq_refl).
      + rewrite !ticl_eu.
        exact (@proper_eu_equ M E B K X meq Eqm KS
          (entails X false p) (entails X b' r) IHp IHr
          t t' Heq w w eq_refl).
    - intros b' q p IHp r IHr t t' Heq w w' <-; destruct q.
      + rewrite !ticl_an.
        exact (@proper_ax_equ M E B K X meq Eqm KS
          (entails X false p) (entails X b' r) IHp IHr
          t t' Heq w w eq_refl).
      + rewrite !ticl_en.
        exact (@proper_ex_equ M E B K X meq Eqm KS
          (entails X false p) (entails X b' r) IHp IHr
          t t' Heq w w eq_refl).
    - intros q p IHp t t' Heq w w' <-; destruct q.
      + rewrite !unfold_entails_ag.
        exact (@proper_ag_equ M E B K X meq Eqm KS
          (entails X false p) IHp t t' Heq w w eq_refl).
      + rewrite !unfold_entails_eg.
        exact (@proper_er_equ M E B K X meq Eqm KS
          (entails X false p) IHp t t' Heq w w eq_refl).
    - intros b' p IHp r IHr t t' Heq w w' <-.
      rewrite !ticl_and.
      now rewrite (IHp t t' Heq w w eq_refl),
        (IHr t t' Heq w w eq_refl).
    - intros b' p IHp r IHr t t' Heq w w' <-.
      rewrite !ticl_or.
      now rewrite (IHp t t' Heq w w eq_refl),
        (IHr t t' Heq w w eq_refl). }
  intros t t' Heq w; exact (Hall b φ t t' Heq w w eq_refl).
Qed.
