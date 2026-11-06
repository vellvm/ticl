From Stdlib Require Import Basics Classes.SetoidClass Classes.Morphisms.
From Coinduction Require Import all.
From TICL Require Import Utils.Utils Logic.Kripke Logic.Semantics Logic.Congruence.
From Equations Require Import Equations.

Import TiclNotations CoindNotations.
Local Open Scope ticl_scope.
Local Open Scope type_scope.
Generalizable All Variables.

Definition event_rel (E : Type -> Type) := forall Y, E Y -> E Y -> Prop.
Definition event_eq {E} : event_rel E := fun _ => eq.
Definition event_right_unique {E} (ER : event_rel E) : Prop :=
  forall Y (e e1 e2 : E Y), ER Y e e1 -> ER Y e e2 -> e1 = e2.
Definition sim_unique {E X} (b : bool) (ER : event_rel E) (RV : X -> X -> Prop) :=
  if b then event_right_unique ER /\
    (forall x y1 y2, RV x y1 -> RV x y2 -> y1 = y2)
  else True.

Lemma event_eq_right_unique {E} : event_right_unique (@event_eq E).
Proof. intros Y e e1 e2 H1 H2; unfold event_eq in *; congruence. Qed.
Lemma event_eq_refl {E} Y (e : E Y) : event_eq Y e e.
Proof. reflexivity. Qed.

(** Related worlds retain constructor shape and event responses. *)
Variant simW {E X} (ER : event_rel E) (RV : X -> X -> Prop) : World E -> World E -> Prop :=
| SimPure : simW ER RV Pure Pure
| SimObs {Y} (e e' : E Y) (v : Y) :
    ER Y e e' -> simW ER RV (Obs e v) (Obs e' v)
| SimDone (x x' : X) : RV x x' -> simW ER RV (Done x) (Done x')
| SimFinish {Y} (e e' : E Y) (v : Y) (x x' : X) :
    ER Y e e' -> RV x x' -> simW ER RV (Finish e v x) (Finish e' v x').

Lemma simW_not_done_iff {E X} ER (RV : X -> X -> Prop) w w' :
  @simW E X ER RV w w' -> (not_done w <-> not_done w').
Proof. destruct 1; split; intro Hnd; try constructor; inversion Hnd. Qed.

Lemma simW_refl {E X} ER (RV : X -> X -> Prop) :
  (forall Y (e : E Y), ER Y e e) -> forall w, not_done w -> simW ER RV w w.
Proof. intros HR w Hnd; destruct Hnd; constructor; auto. Qed.

Lemma simW_not_done_right_unique {E X} ER (RV : X -> X -> Prop) :
  event_right_unique ER -> forall w w1 w2,
  not_done w -> @simW E X ER RV w w1 -> simW ER RV w w2 -> w1 = w2.
Proof.
  intros HU w w1 w2 Hnd H1 H2; destruct Hnd;
    ddestruction H1; ddestruction H2; [reflexivity|].
  f_equal; eapply HU; eauto.
Qed.

Lemma simW_event_eq_not_done {E X} (RV : X -> X -> Prop) w w' :
  @simW E X event_eq RV w w' -> not_done w -> w' = w.
Proof.
  intros HW Hnd; destruct Hnd; ddestruction HW; [reflexivity|].
  unfold event_eq in H; now subst.
Qed.

(** Every atom, including guards and predecessor worlds, is transported. *)
Definition framer {E : Type -> Type} (X : Type) (b : bool) (ER : event_rel E)
  (RV : X -> X -> Prop) (p : ticl E (if b then Some X else None))
  : ticl E (if b then Some X else None) :=
  map_atoms
    (fun P w' => exists w, simW ER RV w w' /\ P w)
    (fun P x' w' => exists x w, RV x x' /\ simW ER RV w w' /\ P x w) b p.

Lemma framer_now {E} X ER RV (P : World E -> Prop) :
  framer X false ER RV (CNow P) = CNow (fun w' => exists w, simW ER RV w w' /\ P w).
Proof. reflexivity. Qed.
Lemma framer_ret {E} X ER RV (P : X -> World E -> Prop) :
  framer X true ER RV (CRet P) =
    CRet (fun x' w' => exists x w, RV x x' /\ simW ER RV w w' /\ P x w).
Proof. reflexivity. Qed.
Lemma framer_u {E} X (b : bool) ER RV q (p : ticl E None) (r : ticl E (if b then Some X else None)) :
  framer X b ER RV (Cu q p r) =
    Cu q (framer X false ER RV p) (framer X b ER RV r).
Proof. destruct b; reflexivity. Qed.
Lemma framer_n {E} X (b : bool) ER RV q (p : ticl E None) (r : ticl E (if b then Some X else None)) :
  framer X b ER RV (Cx q p r) =
    Cx q (framer X false ER RV p) (framer X b ER RV r).
Proof. destruct b; reflexivity. Qed.
Lemma framer_g {E} X ER RV q (p : ticl E None) :
  framer X false ER RV (Cg q p) = Cg q (framer X false ER RV p).
Proof. reflexivity. Qed.
Lemma framer_and {E} X (b : bool) ER RV (p r : ticl E (if b then Some X else None)) :
  framer X b ER RV (CAnd p r) = CAnd (framer X b ER RV p) (framer X b ER RV r).
Proof. destruct b; reflexivity. Qed.
Lemma framer_or {E} X (b : bool) ER RV (p r : ticl E (if b then Some X else None)) :
  framer X b ER RV (COr p r) = COr (framer X b ER RV p) (framer X b ER RV r).
Proof. destruct b; reflexivity. Qed.

Equations prefix_stable {E X} (ER : event_rel E) (RV : X -> X -> Prop)
  (p : ticl E None) : Prop :=
prefix_stable ER RV (CNow P) :=
  forall w w', not_done w -> simW ER RV w w' -> P w -> P w';
prefix_stable ER RV (Cu _ p r) := prefix_stable ER RV p /\ prefix_stable ER RV r;
prefix_stable ER RV (Cx _ p r) := prefix_stable ER RV p /\ prefix_stable ER RV r;
prefix_stable ER RV (Cg _ p) := prefix_stable ER RV p;
prefix_stable ER RV (CAnd p r) := prefix_stable ER RV p /\ prefix_stable ER RV r;
prefix_stable ER RV (COr p r) := prefix_stable ER RV p /\ prefix_stable ER RV r.

Section ShallowKripkeSim.
  Context {M E B} {KS KT : Kripke M E B} {X : Type}.
  Variable ER : event_rel E.
  Variable RV : X -> X -> Prop.
  Variable Fr : M E B X -> M E B X -> Prop.

  Hypothesis sim_l : forall t t' w w' t1 w1,
    Fr t t' -> simW ER RV w w' -> @ktrans M E B KS X t w t1 w1 ->
    exists t1' w1', @ktrans M E B KT X t' w' t1' w1' /\
      Fr t1 t1' /\ simW ER RV w1 w1'.
  Hypothesis sim_r : forall t t' w w' t1' w1',
    Fr t t' -> simW ER RV w w' -> @can_step M E B KS X t w ->
    @ktrans M E B KT X t' w' t1' w1' ->
    exists t1 w1, @ktrans M E B KS X t w t1 w1 /\
      Fr t1 t1' /\ simW ER RV w1 w1'.

  Lemma sim_can_step t t' w w' :
    Fr t t' -> simW ER RV w w' ->
    @can_step M E B KS X t w -> @can_step M E B KT X t' w'.
  Proof.
    intros HF HW (t1 & w1 & HT).
    destruct (sim_l _ _ _ _ _ _ HF HW HT) as (t1' & w1' & HT' & _).
    now exists t1', w1'.
  Qed.

  Section Binary.
    Variables P P' Q Q' : M E B X -> World E -> Prop.
    Hypothesis HP : forall t t' w w', Fr t t' -> simW ER RV w w' -> P t w -> P' t' w'.
    Hypothesis HQ : forall t t' w w', Fr t t' -> simW ER RV w w' -> Q t w -> Q' t' w'.

    Lemma sim_anc t t' w w' : Fr t t' -> simW ER RV w w' ->
      @anc M E B KS X P Q t w -> @anc M E B KT X P' Q' t' w'.
    Proof.
      intros HF HW (Hp & Hs & HN); split; [eapply HP; eauto|].
      split; [eapply sim_can_step; eauto|].
      intros t1' w1' HT'.
      destruct (sim_r _ _ _ _ _ _ HF HW Hs HT') as (t1 & w1 & HT & HF1 & HW1).
      eapply HQ; eauto.
    Qed.

    Lemma sim_enc t t' w w' : Fr t t' -> simW ER RV w w' ->
      @enc M E B KS X P Q t w -> @enc M E B KT X P' Q' t' w'.
    Proof.
      intros HF HW (Hp & t1 & w1 & HT & Hq); split; [eapply HP; eauto|].
      destruct (sim_l _ _ _ _ _ _ HF HW HT) as (t1' & w1' & HT' & HF1 & HW1).
      exists t1', w1'; split; [exact HT'|eapply HQ; eauto].
    Qed.

    Lemma sim_auc t t' w w' : Fr t t' -> simW ER RV w w' ->
      @auc M E B KS X P Q t w -> @auc M E B KT X P' Q' t' w'.
    Proof.
      intros HF HW H; revert t' w' HF HW.
      induction H as [t w Hq|t w Hs IH]; intros t' w' HF HW.
      - apply MatchA; eapply HQ; eauto.
      - destruct IH as (Hp & Hcan & HN).
        apply StepA; split; [eapply HP; eauto|].
        split; [eapply sim_can_step; eauto|].
        intros t1' w1' HT'.
        destruct (sim_r _ _ _ _ _ _ HF HW Hcan HT') as (t1 & w1 & HT & HF1 & HW1).
        eapply HN; eauto.
    Qed.

    Lemma sim_euc t t' w w' : Fr t t' -> simW ER RV w w' ->
      @euc M E B KS X P Q t w -> @euc M E B KT X P' Q' t' w'.
    Proof.
      intros HF HW H; revert t' w' HF HW.
      induction H as [t w Hq|t w [Hp [t1 [w1 [HT [Hq IH]]]]]]; intros t' w' HF HW.
      - apply MatchE; eapply HQ; eauto.
      - apply StepE; split; [eapply HP; eauto|].
        destruct (sim_l _ _ _ _ _ _ HF HW HT) as (t1' & w1' & HT' & HF1 & HW1).
        exists t1', w1'; split; [exact HT'|eapply IH; eauto].
    Qed.
  End Binary.

  Section Always.
    Variables P P' : M E B X -> World E -> Prop.
    Hypothesis HP : forall t t' w w', Fr t t' -> simW ER RV w w' -> P t w -> P' t' w'.

    Lemma sim_agc_chain : forall R : Chain (@agcF M E B KT X P'), forall t t' w w',
      Fr t t' -> simW ER RV w w' -> gfp (@agcF M E B KS X P) t w -> `R t' w'.
    Proof.
      apply (tower (b := @agcF M E B KT X P') (P := fun R => forall t t' w w',
        Fr t t' -> simW ER RV w w' -> gfp (@agcF M E B KS X P) t w -> R t' w')).
      - intros T HT t t' w w' HF HW H R HR; eapply HT; eauto.
      - intros R HR t t' w w' HF HW H; cbn; step in H.
        eapply sim_anc; [exact HP|exact HR|exact HF|exact HW|exact H].
    Qed.
    Lemma sim_agc t t' w w' : Fr t t' -> simW ER RV w w' ->
      gfp (@agcF M E B KS X P) t w -> gfp (@agcF M E B KT X P') t' w'.
    Proof. apply (sim_agc_chain (chain_gfp (@agcF M E B KT X P'))). Qed.

    Lemma sim_egc_chain : forall R : Chain (@egcF M E B KT X P'), forall t t' w w',
      Fr t t' -> simW ER RV w w' -> gfp (@egcF M E B KS X P) t w -> `R t' w'.
    Proof.
      apply (tower (b := @egcF M E B KT X P') (P := fun R => forall t t' w w',
        Fr t t' -> simW ER RV w w' -> gfp (@egcF M E B KS X P) t w -> R t' w')).
      - intros T HT t t' w w' HF HW H R HR; eapply HT; eauto.
      - intros R HR t t' w w' HF HW H; cbn; step in H.
        eapply sim_enc; [exact HP|exact HR|exact HF|exact HW|exact H].
    Qed.
    Lemma sim_egc t t' w w' : Fr t t' -> simW ER RV w w' ->
      gfp (@egcF M E B KS X P) t w -> gfp (@egcF M E B KT X P') t' w'.
    Proof. apply (sim_egc_chain (chain_gfp (@egcF M E B KT X P'))). Qed.
  End Always.
End ShallowKripkeSim.

Section KripkeSim.
  Context `{K : Kripke M E B} {X : Type}.
  Variable ER : event_rel E.
  Variable RV : X -> X -> Prop.
  Variable Fr : M E B X -> M E B X -> Prop.

  Hypothesis sim_l : forall t t' w w' t1 w1,
    Fr t t' -> simW ER RV w w' -> |t, w| ↦ |t1, w1| ->
    exists t1' w1', |t', w'| ↦ |t1', w1'| /\ Fr t1 t1' /\ simW ER RV w1 w1'.
  Hypothesis sim_r : forall t t' w w' t1' w1',
    Fr t t' -> simW ER RV w w' -> can_step t w -> |t', w'| ↦ |t1', w1'| ->
    exists t1 w1, |t, w| ↦ |t1, w1| /\ Fr t1 t1' /\ simW ER RV w1 w1'.

  Theorem ticll_sim : forall (p : ticl E None) t t' w w',
    Fr t t' -> simW ER RV w w' -> entails X false p t w ->
    entails X false (framer X false ER RV p) t' w'.
  Proof.
    induction p as
      [P|q p IHp r IHr|q p IHp r IHr|q p IHp|p IHp r IHr|p IHp r IHr] using ticll_ind;
      intros t t' w w' HF HW H.
    - rewrite framer_now; apply ticl_now in H as [HP Hnd]; apply ticl_now.
      split; [exists w; auto|apply (proj1 (simW_not_done_iff ER RV w w' HW)); exact Hnd].
    - rewrite framer_u; destruct q.
      + apply ticl_au in H; apply ticl_au.
        eapply (sim_auc (KS := K) (KT := K) ER RV Fr sim_l sim_r); eauto.
      + apply ticl_eu in H; apply ticl_eu.
        eapply (sim_euc (KS := K) (KT := K) ER RV Fr sim_l); eauto.
    - rewrite framer_n; destruct q.
      + apply ticl_an in H; apply ticl_an.
        eapply (sim_anc (KS := K) (KT := K) ER RV Fr sim_l sim_r); eauto.
      + apply ticl_en in H; apply ticl_en.
        eapply (sim_enc (KS := K) (KT := K) ER RV Fr sim_l); eauto.
    - rewrite framer_g; destruct q.
      + rewrite unfold_entails_ag in *.
        eapply (sim_agc (KS := K) (KT := K) ER RV Fr sim_l sim_r); eauto.
      + rewrite unfold_entails_eg in *.
        eapply (sim_egc (KS := K) (KT := K) ER RV Fr sim_l); eauto.
    - rewrite framer_and; apply ticl_and in H; apply ticl_and; destruct H; split; eauto.
    - rewrite framer_or; apply ticl_or in H; apply ticl_or; destruct H; [left|right]; eauto.
  Qed.

  Lemma sim_done_with (P : X -> World E -> Prop) w w' : simW ER RV w w' ->
    done_with P w ->
    done_with (fun x' z' => exists x z, RV x x' /\ simW ER RV z z' /\ P x z) w'.
  Proof.
    intros HW HD; destruct HD; ddestruction HW; constructor;
      eexists; eexists; repeat split; eauto using SimPure, SimObs.
  Qed.

  Lemma sim_done_of x w z z' : simW ER RV z z' -> done_of x w z ->
    exists x' q', RV x x' /\ simW ER RV w q' /\ done_of x' q' z'.
  Proof.
    intros HW HD; destruct HD; ddestruction HW;
      eexists; eexists; repeat split; eauto using SimPure, SimObs, PureWithDone, ObsWithFinish.
  Qed.

  Theorem ticl_sim : forall (b : bool) (p : ticl E (if b then Some X else None)),
    sim_unique b ER RV -> forall t t' w w',
    Fr t t' -> simW ER RV w w' -> entails X b p t w ->
    entails X b (framer X b ER RV p) t' w'.
  Proof.
    intros b; destruct b.
    - intros p [HEunique HRunique].
      assert (Hsuf : forall (b : bool) (p : ticl E (if b then Some X else None)),
        (if b as flag return ticl E (if flag then Some X else None) -> Prop then
          fun p => forall t t' w w', Fr t t' -> simW ER RV w w' ->
            entails X true p t w -> entails X true (framer X true ER RV p) t' w'
         else fun _ => True) p).
      { apply (@ticl_at_ind E X (fun b p =>
          (if b as flag return ticl E (if flag then Some X else None) -> Prop then
            fun p => forall t t' w w', Fr t t' -> simW ER RV w w' ->
              entails X true p t w -> entails X true (framer X true ER RV p) t' w'
           else fun _ => True) p)).
        - intros; exact I.
        - intros P t t' w w' HF HW H.
          apply ticl_ret in H as (x & Hp & Hnd & Hcan & HN).
          rewrite framer_ret; apply ticl_ret.
          destruct Hcan as (u & z & HT).
          destruct (sim_l _ _ _ _ _ _ HF HW HT) as (u' & z' & HT' & HF1 & HW1).
          destruct (sim_done_of _ _ _ _ HW1 (HN _ _ HT)) as (x' & q' & HR & HQ & HD).
          assert (Eq : q' = w') by (eapply simW_not_done_right_unique; eauto); subst q'.
          exists x'; split; [exists x, w; auto|].
          split; [apply (proj1 (simW_not_done_iff ER RV w w' HW)); exact Hnd|].
          split; [eapply (sim_can_step (KS := K) (KT := K) ER RV Fr sim_l);
            [exact HF|exact HW|now exists u, z]|].
          intros v' r' HV'.
          destruct (sim_r _ _ _ _ _ _ HF HW (ex_intro _ u (ex_intro _ z HT)) HV')
            as (v & r & HV & HF2 & HW2).
          destruct (sim_done_of _ _ _ _ HW2 (HN _ _ HV)) as (y & q & HRy & HQy & HDy).
          assert (Eq : q = w') by (eapply simW_not_done_right_unique; eauto); subst q.
          assert (y = x') by (eapply HRunique; eauto); now subst y.
        - intros b q phi _ psi IH; destruct b; [|exact I].
          intros t t' w w' HF HW H; rewrite framer_u; destruct q.
          + apply ticl_au in H; apply ticl_au.
            eapply (sim_auc (KS := K) (KT := K) ER RV Fr sim_l sim_r);
              [exact (ticll_sim phi)| |exact HF|exact HW|exact H].
            intros; eapply IH; eauto.
          + apply ticl_eu in H; apply ticl_eu.
            eapply (sim_euc (KS := K) (KT := K) ER RV Fr sim_l);
              [exact (ticll_sim phi)| |exact HF|exact HW|exact H].
            intros; eapply IH; eauto.
        - intros b q phi _ psi IH; destruct b; [|exact I].
          intros t t' w w' HF HW H; rewrite framer_n; destruct q.
          + apply ticl_an in H; apply ticl_an.
            eapply (sim_anc (KS := K) (KT := K) ER RV Fr sim_l sim_r);
              [exact (ticll_sim phi)| |exact HF|exact HW|exact H].
            intros; eapply IH; eauto.
          + apply ticl_en in H; apply ticl_en.
            eapply (sim_enc (KS := K) (KT := K) ER RV Fr sim_l);
              [exact (ticll_sim phi)| |exact HF|exact HW|exact H].
            intros; eapply IH; eauto.
        - intros; exact I.
        - intros b phi IHp psi IHr; destruct b; [|exact I].
          intros t t' w w' HF HW H; rewrite framer_and.
          apply ticl_and in H; apply ticl_and; destruct H; split; eauto.
        - intros b phi IHp psi IHr; destruct b; [|exact I].
          intros t t' w w' HF HW H; rewrite framer_or.
          apply ticl_or in H; apply ticl_or; destruct H; [left|right]; eauto. }
      exact (Hsuf true p).
    - intros p _; apply ticll_sim.
  Qed.
End KripkeSim.

Section AtomicTransport.
  Context `{K : Kripke M E B}.

  Lemma prefix_stable_framer {X} ER (RV : X -> X -> Prop) (p : ticl E None) :
    prefix_stable ER RV p -> impl_ticl X false (framer X false ER RV p) p.
  Proof.
    induction p as
      [P|q p IHp r IHr|q p IHp r IHr|q p IHp|p IHp r IHr|p IHp r IHr] using ticll_ind;
      simp prefix_stable in *.
    - intros HS t w H; rewrite framer_now in H.
      apply ticl_now in H as [(z & HW & HP) Hnd]; apply ticl_now; split; [|exact Hnd].
      eapply HS; [apply (proj2 (simW_not_done_iff ER RV z w HW)); exact Hnd|exact HW|exact HP].
    - intros [Hp Hr]; rewrite framer_u.
      eapply (impl_ticl_until (b:=false)); [reflexivity|now apply IHp|now apply IHr].
    - intros [Hp Hr]; rewrite framer_n.
      eapply (impl_ticl_next (b:=false)); [reflexivity|now apply IHp|now apply IHr].
    - intro Hp; rewrite framer_g.
      eapply impl_ticl_global; [reflexivity|now apply IHp].
    - intros [Hp Hr]; rewrite framer_and.
      apply (impl_ticl_and (b:=false)); [now apply IHp|now apply IHr].
    - intros [Hp Hr]; rewrite framer_or.
      apply (impl_ticl_or (b:=false)); [now apply IHp|now apply IHr].
  Qed.

  Lemma framer_event_eq (X : Type) (b : bool) (RV : X -> X -> Prop)
    (p : ticl E (if b then Some X else None)) t w :
    entails X b (framer X b event_eq RV p) t w <->
    (match b as flag return ticl E (if flag then Some X else None) -> Prop with
     | false => fun f => entails X false f t w
     | true => fun f => entails X true
         (map_ret (fun P x' z => exists x, RV x x' /\ P x z) f) t w
     end) p.
  Proof.
    assert (H : forall (b : bool) (p : ticl E (if b then Some X else None)),
      equiv_ticl X b (framer X b event_eq RV p)
        ((match b as flag return
            ticl E (if flag then Some X else None) -> ticl E (if flag then Some X else None) with
          | false => fun f => f
          | true => map_ret (fun P x' z => exists x, RV x x' /\ P x z)
          end) p)).
    { apply (@ticl_at_ind E X).
      - intro P; rewrite framer_now; split; intros u z HP;
          apply ticl_now in HP; apply ticl_now.
        + destruct HP as [(q & HW & HP) Hnd].
          assert (Hq : not_done q) by (apply (proj2 (simW_not_done_iff event_eq RV q z HW)); exact Hnd).
          pose proof (simW_event_eq_not_done RV q z HW Hq) as Eq; subst z; auto.
        + destruct HP as [HP Hnd]; split; [|exact Hnd].
          exists z; split; [apply simW_refl; [apply event_eq_refl|exact Hnd]|exact HP].
      - intro P; rewrite framer_ret; cbn [map_ret]; split; intros u z HP;
          apply ticl_ret in HP; apply ticl_ret.
        + destruct HP as (x' & (x & q & HR & HW & HP) & Hnd & Hcan & HN).
          assert (Hq : not_done q) by (apply (proj2 (simW_not_done_iff event_eq RV q z HW)); exact Hnd).
          pose proof (simW_event_eq_not_done RV q z HW Hq) as Eq; subst z.
          exists x'; repeat split; eauto.
        + destruct HP as (x' & (x & HR & HP) & Hnd & Hcan & HN).
          exists x'; split.
          * exists x, z; repeat split; auto; apply simW_refl; [apply event_eq_refl|exact Hnd].
          * repeat split; auto.
      - intros flag q phi IHphi psi IHpsi; rewrite framer_u; destruct flag; cbn [map_ret].
        + eapply (equiv_ticl_until (b:=true)); [reflexivity|exact IHphi|exact IHpsi].
        + eapply (equiv_ticl_until (b:=false)); [reflexivity|exact IHphi|exact IHpsi].
      - intros flag q phi IHphi psi IHpsi; rewrite framer_n; destruct flag; cbn [map_ret].
        + eapply (equiv_ticl_next (b:=true)); [reflexivity|exact IHphi|exact IHpsi].
        + eapply (equiv_ticl_next (b:=false)); [reflexivity|exact IHphi|exact IHpsi].
      - intros q phi IH; rewrite framer_g; eapply equiv_ticl_global; [reflexivity|exact IH].
      - intros flag phi IHphi psi IHpsi; rewrite framer_and; destruct flag; cbn [map_ret].
        + apply (equiv_ticl_and (b:=true)); assumption.
        + apply (equiv_ticl_and (b:=false)); assumption.
      - intros flag phi IHphi psi IHpsi; rewrite framer_or; destruct flag; cbn [map_ret].
        + apply (equiv_ticl_or (b:=true)); assumption.
        + apply (equiv_ticl_or (b:=false)); assumption. }
    specialize (H b p); destruct b; destruct H as [Hf Hb]; split; [apply Hf|apply Hb|apply Hf|apply Hb].
  Qed.
End AtomicTransport.
