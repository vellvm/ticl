From Stdlib Require Import Basics Classes.SetoidClass Classes.Morphisms.
From Coinduction Require Import all.
From TICL Require Import Utils.Utils Logic.Kripke Logic.Semantics.
From Equations Require Import Equations.

Import TiclNotations CoindNotations.
Local Open Scope ticl_scope.
Local Open Scope type_scope.
Generalizable All Variables.

Section KripkeSim.
  Context `{K: Kripke M E B} {X: Type}.
  Variable RV : X -> X -> Prop.
  Variable Fr : M E B X -> M E B X -> Prop.

  (** Worlds related by the simulation: equal except at returns, where values are [RV]-related. *)
  Variant simW : World E -> World E -> Prop :=
  | SimPure : simW Pure Pure
  | SimObs {Y} (e: E Y) (v: Y) : simW (Obs e v) (Obs e v)
  | SimDone (x x': X) : RV x x' -> simW (Done x) (Done x')
  | SimFinish {Y} (e: E Y) (v: Y) (x x': X) :
      RV x x' -> simW (Finish e v x) (Finish e v x').

  (** [Fr] transports every step forward, and steps backward only when the small
      side [can_step], as required by [AN] and [AU]. *)
  Hypothesis sim_l : forall t t' w t1 w1, Fr t t' -> |t, w| ↦ |t1, w1| ->
    exists t1' w1', |t', w| ↦ |t1', w1'| /\ Fr t1 t1' /\ simW w1 w1'.
  Hypothesis sim_r : forall t t' w t1' w1', Fr t t' -> can_step t w ->
    |t', w| ↦ |t1', w1'| ->
    exists t1 w1, |t, w| ↦ |t1, w1| /\ Fr t1 t1' /\ simW w1 w1'.

  (** Related nonterminal worlds are equal. *)
  Lemma simW_not_done w w' : simW w w' -> not_done w -> w' = w.
  Proof. intros H Hnd; destruct H; auto; inversion Hnd. Qed.

  (** Nonterminal worlds are related to themselves. *)
  Lemma simW_refl w : not_done w -> simW w w.
  Proof. destruct 1; constructor. Qed.

  (** Forward simulation preserves the ability to step at the same world. *)
  Lemma sim_can_step t t' w : Fr t t' -> can_step t w -> can_step t' w.
  Proof.
    intros HF (t1 & w1 & HT).
    destruct (sim_l _ _ _ _ _ HF HT) as (t1' & w1' & HT' & _).
    now exists t1', w1'.
  Qed.

  (** Equal-world transport extends to [simW] when the source property implies [not_done]. *)
  Lemma sim_world (P P' : M E B X -> World E -> Prop) :
    (forall t t' w, Fr t t' -> P t w -> P' t' w) ->
    (forall t w, P t w -> not_done w) ->
    forall t t' w w', Fr t t' -> simW w w' -> P t w -> P' t' w'.
  Proof. intros HP Hnd t t' w w' HF HW H; rewrite (simW_not_done _ _ HW (Hnd _ _ H)); eauto. Qed.

  Section Binary.
    Variables P P' Q Q' : M E B X -> World E -> Prop.
    Hypothesis HP : forall t t' w, Fr t t' -> P t w -> P' t' w.
    Hypothesis HQ : forall t t' w w', Fr t t' -> simW w w' -> Q t w -> Q' t' w'.

    (** Universal next transports forward at equal source worlds and related successor worlds. *)
    Lemma sim_anc t t' w : Fr t t' -> anc P Q t w -> anc P' Q' t' w.
    Proof.
      intros HF (Hp & Hs & HN); split; [eapply HP; eauto|].
      split; [eapply sim_can_step; eauto|].
      intros t1' w1' HT'.
      destruct (sim_r _ _ _ _ _ HF Hs HT') as (t1 & w1 & HT & HF1 & HW).
      eapply HQ; eauto.
    Qed.

    (** Existential next transports forward at equal source worlds and related successor worlds. *)
    Lemma sim_enc t t' w : Fr t t' -> enc P Q t w -> enc P' Q' t' w.
    Proof.
      intros HF (Hp & t1 & w1 & HT & Hq); split; [eapply HP; eauto|].
      destruct (sim_l _ _ _ _ _ HF HT) as (t1' & w1' & HT' & HF1 & HW).
      exists t1', w1'; split; [exact HT'|eapply HQ; eauto].
    Qed.

    (** Universal until transports forward across related worlds. *)
    Lemma sim_auc t t' w w' : Fr t t' -> simW w w' ->
      auc P Q t w -> auc P' Q' t' w'.
    Proof.
      intros HF HW H; revert t' w' HF HW.
      induction H as [t w Hq|t w Hs IH]; intros t' w' HF HW.
      - apply MatchA; eapply HQ; eauto.
      - destruct IH as (Hp & Hcan & HN).
        pose proof (simW_not_done _ _ HW (can_step_not_done _ _ Hcan)); subst w'.
        apply StepA; split; [eapply HP; eauto|].
        split; [eapply sim_can_step; eauto|].
        intros t1' w1' HT'.
        destruct (sim_r _ _ _ _ _ HF Hcan HT') as (t1 & w1 & HT & HF1 & HW1).
        eapply HN; eauto.
    Qed.

    (** Existential until transports forward across related worlds. *)
    Lemma sim_euc t t' w w' : Fr t t' -> simW w w' ->
      euc P Q t w -> euc P' Q' t' w'.
    Proof.
      intros HF HW H; revert t' w' HF HW.
      induction H as [t w Hq|t w [Hp [t1 [w1 [HT [Hq IH]]]]]]; intros t' w' HF HW.
      - apply MatchE; eapply HQ; eauto.
      - pose proof (simW_not_done _ _ HW (ktrans_not_done _ _ _ _ HT)); subst w'.
        apply StepE; split; [eapply HP; eauto|].
        destruct (sim_l _ _ _ _ _ HF HT) as (t1' & w1' & HT' & HF1 & HW1).
        exists t1', w1'; split; [exact HT'|eapply IH; eauto].
    Qed.
  End Binary.

  Section Always.
    Variables P P' : M E B X -> World E -> Prop.
    Hypothesis HP : forall t t' w, Fr t t' -> P t w -> P' t' w.

    (** Universal always transports forward at equal worlds into every chain stage. *)
    Lemma sim_agc_chain : forall R: Chain (agcF P'), forall t t' w,
      Fr t t' -> agc P t w -> `R t' w.
    Proof.
      apply (tower (b := agcF P') (P := fun R => forall t t' w,
        Fr t t' -> agc P t w -> R t' w)).
      - intros T HT t t' w HF H R HR; eapply HT; eauto.
      - intros R HR t t' w HF H; cbn.
        step in H.
        eapply sim_anc; [exact HP| |exact HF|exact H].
        eapply sim_world; [exact HR|].
        intros u z Hag; step in Hag; eapply anc_not_done; exact Hag.
    Qed.

    (** Universal always transports forward at equal worlds. *)
    Lemma sim_agc t t' w : Fr t t' -> agc P t w -> agc P' t' w.
    Proof. apply (sim_agc_chain (chain_gfp _)). Qed.

    (** Existential always transports forward at equal worlds into every chain stage. *)
    Lemma sim_egc_chain : forall R: Chain (egcF P'), forall t t' w,
      Fr t t' -> egc P t w -> `R t' w.
    Proof.
      apply (tower (b := egcF P') (P := fun R => forall t t' w,
        Fr t t' -> egc P t w -> R t' w)).
      - intros T HT t t' w HF H R HR; eapply HT; eauto.
      - intros R HR t t' w HF H; cbn.
        step in H.
        eapply sim_enc; [exact HP| |exact HF|exact H].
        eapply sim_world; [exact HR|].
        intros u z Heg; step in Heg; eapply enc_not_done; exact Heg.
    Qed.

    (** Existential always transports forward at equal worlds. *)
    Lemma sim_egc t t' w : Fr t t' -> egc P t w -> egc P' t' w.
    Proof. apply (sim_egc_chain (chain_gfp _)). Qed.
  End Always.

  (** Rewrite [done]/[ret] postconditions by [RV]; [ret R] becomes [AX done (R ⋆ RV)]
      because the target return value is only [RV]-related. *)
  Fixpoint framer (ψ: ticlr E X) : ticlr E X :=
    match ψ with
    | CDone p => CDone (fun x' w => exists x, RV x x' /\ p x w)
    | CRet p => CxR Q_A (CNow (fun _ => True))
        (CDone (fun x' w => exists x, RV x x' /\ p x w))
    | CuR q φ ψ => CuR q φ (framer ψ)
    | CxR q φ ψ => CxR q φ (framer ψ)
    | CAndR p q => CAndR (framer p) (framer q)
    | COrR p q => COrR (framer p) (framer q)
    end.

  (** Prefix formulas transport unchanged along the simulation at equal worlds. *)
  Theorem ticll_sim : forall (φ: ticll E) t t' w,
    Fr t t' -> <( t, w |= φ )> -> <( t', w |= φ )>.
  Proof.
    induction φ; intros t t' w HF H;
      pose proof (ticll_not_done _ _ _ _ H) as Hnd;
      rewrite unfold_entailsL in *.
    - exact H.
    - destruct q.
      + eapply sim_auc; [exact IHφ1| |exact HF|apply simW_refl; exact Hnd|exact H].
        eapply sim_world; [exact IHφ2|intros; eapply ticll_not_done; eauto].
      + eapply sim_euc; [exact IHφ1| |exact HF|apply simW_refl; exact Hnd|exact H].
        eapply sim_world; [exact IHφ2|intros; eapply ticll_not_done; eauto].
    - destruct q.
      + eapply sim_anc; [exact IHφ1| |exact HF|exact H].
        eapply sim_world; [exact IHφ2|intros; eapply ticll_not_done; eauto].
      + eapply sim_enc; [exact IHφ1| |exact HF|exact H].
        eapply sim_world; [exact IHφ2|intros; eapply ticll_not_done; eauto].
    - destruct q; [eapply sim_agc|eapply sim_egc]; eauto.
    - destruct H; split; [eapply IHφ1|eapply IHφ2]; eauto.
    - destruct H; [left; eapply IHφ1|right; eapply IHφ2]; eauto.
  Qed.

  (** Terminal postconditions transport forward across related worlds using [RV]. *)
  Lemma sim_done_with (p: X -> World E -> Prop) w w' : simW w w' ->
    done_with p w -> done_with (fun x' z => exists x, RV x x' /\ p x z) w'.
  Proof.
    intros HW HD; destruct HD; ddestruction HW; constructor; eauto.
  Qed.

  (** Suffix formulas transport forward across related worlds with [framer]. *)
  Theorem ticlr_sim : forall (ψ: ticlr E X) t t' w w',
    Fr t t' -> simW w w' ->
    <[ t, w |= ψ ]> -> <[ t', w' |= {framer ψ} ]>.
  Proof.
    induction ψ; cbn [framer]; intros t t' w w' HF HW H;
      rewrite unfold_entailsR in *.
    - eapply sim_done_with; eauto.
    - destruct H as (x & Hp & Hnd & Hcan & HN).
      pose proof (simW_not_done _ _ HW Hnd); subst w'.
      split; [split; auto|split; [eapply sim_can_step; eauto|]].
      intros u' z' HT'.
      destruct (sim_r _ _ _ _ _ HF Hcan HT') as (u & z & HT & HF1 & HW1).
      specialize (HN _ _ HT); apply done_of_eq in HN.
      pose proof (sim_done_with _ _ _ HW1 HN) as HD.
      destruct HD as [x' [y [HR [Heq Hz]]]|Y e v x' [y [HR [Heq Hz]]]];
        subst y; subst; constructor; exists x; auto.
    - destruct q.
      + eapply sim_auc; [exact (ticll_sim φ)| |exact HF|exact HW|exact H].
        intros; eapply IHψ; eauto.
      + eapply sim_euc; [exact (ticll_sim φ)| |exact HF|exact HW|exact H].
        intros; eapply IHψ; eauto.
    - destruct q.
      + pose proof (simW_not_done _ _ HW (anc_not_done _ _ _ _ _ H)); subst w'.
        eapply sim_anc; [exact (ticll_sim φ)| |exact HF|exact H].
        intros; eapply IHψ; eauto.
      + pose proof (simW_not_done _ _ HW (enc_not_done _ _ _ _ _ H)); subst w'.
        eapply sim_enc; [exact (ticll_sim φ)| |exact HF|exact H].
        intros; eapply IHψ; eauto.
    - destruct H; split; [eapply IHψ1|eapply IHψ2]; eauto.
    - destruct H; [left; eapply IHψ1|right; eapply IHψ2]; eauto.
  Qed.
End KripkeSim.
