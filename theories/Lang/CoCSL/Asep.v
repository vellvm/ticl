(** * Splitting TICL properties of forked CoCSL programs.

    Global properties of an admitted fork, stated over the anchored split
    [state_sat] with ordinary heap [asep], imply properties of each projected component.  Finite modalities
    split unconditionally; [AN] needs selection-stable targets, [AG] release
    certificates, and [EG] one execution fair to both lineages.  The
    own-action clock [weak_next] transports every modality. *)
From TICL Require Import Lang.CoCSL.Owned CTree.Interp.CSL.Asep.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Relations
  Classes.Morphisms Classes.RelationClasses Program.Equality
  Wellfounded.Transitive_Closure.
From Coinduction Require Import all.
From TICL Require Import Logic.Kripke Logic.Semantics Logic.Setoid
  Logic.Simulation Logic.Congruence CTree.Logic.Sim CTree.Logic.Trans CTree.Logic.CanStep
  Utils.Relations Utils.Execution Utils.Pcm.

Import VectorNotations.
Local Open Scope pcm_scope.

(** ** A Kripke model of a bare transition relation *)

Definition StateModel (S : Type) (E B : Type -> Type) (X : Type) : Type := S.

(** No observations: every world is [Pure]. *)
Definition NoObs : Type -> Type := fun _ => Empty_set.

Definition rel_kripke {S} (R : relation S) : Kripke (StateModel S) NoObs Bn.
Proof.
  refine {| ktrans X s w s' w' := w = Pure /\ w' = Pure /\ R s s' |}.
  intros X t t' w w' [-> _]; constructor.
Defined.

(** Leibniz equality is a model equality for any relation. *)
#[global] Instance rel_kripke_setoid {S} (R : relation S) X :
  @KripkeSetoid (StateModel S) NoObs Bn (rel_kripke R) X eq _.
Proof. intros t s s' w w' -> TR; exists s'; split; [exact TR|reflexivity]. Qed.

Definition hprop := OwnedCfg -> Prop.

Definition hlift (P : hprop) : StateModel OwnedCfg NoObs Bn unit -> World NoObs -> Prop :=
  fun c _ => P c.

Definition hAN (R : relation OwnedCfg) (P Q : hprop) : hprop :=
  fun c => @anc _ _ _ (rel_kripke R) unit (hlift P) (hlift Q) c Pure.
Definition hEN (R : relation OwnedCfg) (P Q : hprop) : hprop :=
  fun c => @enc _ _ _ (rel_kripke R) unit (hlift P) (hlift Q) c Pure.
Definition hAU (R : relation OwnedCfg) (P Q : hprop) : hprop :=
  fun c => @auc _ _ _ (rel_kripke R) unit (hlift P) (hlift Q) c Pure.
Definition hEU (R : relation OwnedCfg) (P Q : hprop) : hprop :=
  fun c => @euc _ _ _ (rel_kripke R) unit (hlift P) (hlift Q) c Pure.
Definition hAG (R : relation OwnedCfg) (P : hprop) : hprop :=
  fun c => gfp (@agcF _ _ _ (rel_kripke R) unit (hlift P)) c Pure.
Definition hEG (R : relation OwnedCfg) (P : hprop) : hprop :=
  fun c => gfp (@egcF _ _ _ (rel_kripke R) unit (hlift P)) c Pure.

Definition hTrue : hprop := fun _ => True.
Definition hAX (R : relation OwnedCfg) (Q : hprop) : hprop := hAN R hTrue Q.
Definition hEX (R : relation OwnedCfg) (Q : hprop) : hprop := hEN R hTrue Q.
Definition hAF (R : relation OwnedCfg) (Q : hprop) : hprop := hAU R hTrue Q.
Definition hEF (R : relation OwnedCfg) (Q : hprop) : hprop := hEU R hTrue Q.
Definition hand (P Q : hprop) : hprop := fun c => P c /\ Q c.
Definition hor (P Q : hprop) : hprop := fun c => P c \/ Q c.

(** ** Termination and results *)

Definition terminal (c : OwnedCfg) : Prop := tp_size (oc_pool c) = 0.

(** A live-state atom. *)
Definition hNow (P : hprop) : hprop := fun c => ~ terminal c /\ P c.

(** Already finished, versus uniformly finishing on the next step. *)
Definition hDone (P : hprop) : hprop := fun c => terminal c /\ P c.

Definition hRet (R : relation OwnedCfg) (P : hprop) : hprop :=
  fun c => exists out, R c out /\
    forall d, R c d -> terminal d /\ same_view d out /\ P d.

(** ** Ordinary heap separation lifted to owned states *)

(** A predicate read on one lineage's projection. *)
Definition at_side (i : side) (P : hprop) : hprop := fun c => P (project i c).

Definition hproper (P : hprop) : Prop := Proper (owned_equ ==> iff) P.


Definition view_pred (P : hprop) : Prop := forall c d, same_view c d -> P c -> P d.

Definition SelectionStable (Q : hprop) : Prop :=
  forall d a d', owned_step d a d' -> action_kind a = OASelect -> (Q d <-> Q d').

Definition hRet_at (i : side) (R : relation OwnedCfg) (P : hprop) : hprop :=
  fun c => exists out, R c out /\
    forall d, R c d -> terminal (project i d) /\
      same_view (project i d) (project i out) /\ P (project i d).

(** ** Model equality for the owned clocks *)

#[global] Instance owned_next_setoid :
  @KripkeSetoid (StateModel OwnedCfg) NoObs Bn (rel_kripke owned_next) unit owned_equ _.
Proof.
  intros t s s' w w' Heq (-> & -> & TR).
  destruct (owned_next_equ _ _ _ Heq TR) as (d' & TR' & E).
  now exists d'.
Qed.

#[global] Instance weak_next_setoid i :
  @KripkeSetoid (StateModel OwnedCfg) NoObs Bn (rel_kripke (weak_next i)) unit owned_equ _.
Proof.
  intros t s s' w w' Heq (-> & -> & TR).
  destruct (weak_next_equ _ _ _ _ Heq TR) as (d' & TR' & E).
  now exists d'.
Qed.

(** ** Unfoldings *)

Local Lemma can_step_rel R c :
  @can_step _ _ _ (rel_kripke R) unit c Pure <-> hcan_step R c.
Proof.
  split.
  - intros (c' & w' & _ & _ & TR); now exists c'.
  - intros (c' & TR); now exists c', Pure.
Qed.

Lemma hAN_iff R P Q c : hAN R P Q c <-> P c /\ hcan_step R c /\ forall c', R c c' -> Q c'.
Proof.
  unfold hAN, anc; rewrite can_step_rel; split.
  - intros (Hp & Hs & H); repeat split; auto.
    intros c' TR; exact (H c' Pure (conj eq_refl (conj eq_refl TR))).
  - intros (Hp & Hs & H); repeat split; auto.
    intros c' w' (_ & -> & TR); now apply H.
Qed.

Lemma hEN_iff R P Q c : hEN R P Q c <-> P c /\ exists c', R c c' /\ Q c'.
Proof.
  unfold hEN, enc; split.
  - intros (Hp & c' & w' & (_ & _ & TR) & HQ); eauto.
  - intros (Hp & c' & TR & HQ); split; auto; now exists c', Pure.
Qed.

Lemma hAU_now R P Q c : Q c -> hAU R P Q c.
Proof. intros; now apply MatchA. Qed.

Lemma hAU_step R P Q c :
  P c -> hcan_step R c -> (forall c', R c c' -> hAU R P Q c') -> hAU R P Q c.
Proof.
  intros Hp Hs H; apply StepA; split; [exact Hp|split].
  - now apply can_step_rel.
  - intros c' w' (_ & -> & TR); now apply H.
Qed.

Lemma hAU_ind R P Q (Z : hprop) :
  (forall c, Q c -> Z c) ->
  (forall c, P c -> hcan_step R c -> (forall c', R c c' -> hAU R P Q c') ->
     (forall c', R c c' -> Z c') -> Z c) ->
  forall c, hAU R P Q c -> Z c.
Proof.
  intros Hb Hs c H.
  enough (G : forall w, @auc _ _ _ (rel_kripke R) unit (hlift P) (hlift Q) c w -> w = Pure -> Z c)
    by exact (G _ H eq_refl).
  intros w A; clear H; induction A as [t w HQ|t w (Hp & Hc & HA) (_ & _ & HZ)]; intros ->; auto.
  apply Hs; auto.
  - now apply can_step_rel.
  - intros c' TR; exact (HA c' Pure (conj eq_refl (conj eq_refl TR))).
  - intros c' TR; exact (HZ c' Pure (conj eq_refl (conj eq_refl TR)) eq_refl).
Qed.

Lemma hEU_now R P Q c : Q c -> hEU R P Q c.
Proof. intros; now apply MatchE. Qed.

Lemma hEU_step R P Q c c' : P c -> R c c' -> hEU R P Q c' -> hEU R P Q c.
Proof. intros Hp TR H; apply StepE; split; auto; now exists c', Pure. Qed.

Lemma hEU_ind R P Q (Z : hprop) :
  (forall c, Q c -> Z c) ->
  (forall c c', P c -> R c c' -> hEU R P Q c' -> Z c' -> Z c) ->
  forall c, hEU R P Q c -> Z c.
Proof.
  intros Hb Hs c H.
  enough (G : forall w, @euc _ _ _ (rel_kripke R) unit (hlift P) (hlift Q) c w -> w = Pure -> Z c)
    by exact (G _ H eq_refl).
  intros w A; clear H; induction A as [t w HQ|t w (Hp & t' & w' & (_ & -> & TR) & HE & HZ)];
    intros ->; auto.
  eapply Hs; eauto.
Qed.

Lemma hAG_unfold R P c :
  hAG R P c <-> P c /\ hcan_step R c /\ forall c', R c c' -> hAG R P c'.
Proof.
  unfold hAG; split.
  - intros H; apply (gfp_fp (agcF (hlift P))) in H; cbn in H.
    destruct H as (Hp & Hs & H); repeat split; auto.
    + now apply can_step_rel.
    + intros c' TR; exact (H c' Pure (conj eq_refl (conj eq_refl TR))).
  - intros (Hp & Hs & H); apply (gfp_fp (agcF (hlift P))); cbn; repeat split; auto.
    + now apply can_step_rel.
    + intros c' w' (_ & -> & TR); now apply H.
Qed.

Lemma hAG_coind R P (I : hprop) :
  (forall c, I c -> P c /\ hcan_step R c /\ forall c', R c c' -> I c') ->
  forall c, I c -> hAG R P c.
Proof.
  intros H c Hc; unfold hAG.
  apply (leq_gfp (agcF (hlift P)) (fun d w => w = Pure /\ I d)); [|now split].
  intros d w (-> & Hd); destruct (H d Hd) as (Hp & Hs & HN); cbn.
  split; [exact Hp|split; [now apply can_step_rel|]].
  intros d' w1 (_ & -> & TR); split; auto.
Qed.

Lemma hEG_unfold R P c : hEG R P c <-> P c /\ exists c', R c c' /\ hEG R P c'.
Proof.
  unfold hEG; split.
  - intros H; apply (gfp_fp (egcF (hlift P))) in H; cbn in H.
    destruct H as (Hp & c' & w' & (_ & -> & TR) & H); eauto.
  - intros (Hp & c' & TR & H); apply (gfp_fp (egcF (hlift P))); cbn; split; auto.
    now exists c', Pure.
Qed.

Lemma hEG_coind R P (I : hprop) :
  (forall c, I c -> P c /\ exists c', R c c' /\ I c') -> forall c, I c -> hEG R P c.
Proof.
  intros H c Hc; unfold hEG.
  apply (leq_gfp (egcF (hlift P)) (fun d w => w = Pure /\ I d)); [|now split].
  intros d w (-> & Hd); destruct (H d Hd) as (Hp & d' & TR & Hd'); cbn; split; auto.
  now exists d', Pure.
Qed.

Lemma hAN_mono R P P' Q Q' c :
  (forall d, P d -> P' d) -> (forall d, Q d -> Q' d) -> hAN R P Q c -> hAN R P' Q' c.
Proof. rewrite !hAN_iff; intros HP HQ (Hp & Hs & H); auto. Qed.

Lemma hEN_mono R P P' Q Q' c :
  (forall d, P d -> P' d) -> (forall d, Q d -> Q' d) -> hEN R P Q c -> hEN R P' Q' c.
Proof. rewrite !hEN_iff; intros HP HQ (Hp & c' & TR & H); split; eauto. Qed.

Lemma hAU_mono R P P' Q Q' c :
  (forall d, P d -> P' d) -> (forall d, Q d -> Q' d) -> hAU R P Q c -> hAU R P' Q' c.
Proof.
  intros HP HQ; revert c; apply hAU_ind.
  - intros; apply hAU_now; auto.
  - intros; apply hAU_step; auto.
Qed.

Lemma hEU_mono R P P' Q Q' c :
  (forall d, P d -> P' d) -> (forall d, Q d -> Q' d) -> hEU R P Q c -> hEU R P' Q' c.
Proof.
  intros HP HQ; revert c; apply hEU_ind.
  - intros; apply hEU_now; auto.
  - intros; eapply hEU_step; eauto.
Qed.

Lemma hAG_mono R P P' c : (forall d, P d -> P' d) -> hAG R P c -> hAG R P' c.
Proof.
  intros HP; apply hAG_coind; intros d H; apply hAG_unfold in H as (? & ? & ?); auto.
Qed.

Lemma hEG_mono R P P' c : (forall d, P d -> P' d) -> hEG R P c -> hEG R P' c.
Proof.
  intros HP; apply hEG_coind; intros d H; apply hEG_unfold in H as (? & ? & ?); eauto.
Qed.

(** ** Properness under [owned_equ] *)

Local Lemma hlift_proper P : hproper P ->
  Proper (owned_equ ==> eq ==> iff) (hlift P).
Proof. intros HP x y E w _ <-; unfold hlift; now apply HP. Qed.

Local Ltac lift_proper := repeat (apply hlift_proper; assumption).

Section Proper.
  Context {R : relation OwnedCfg}
    {KS : @KripkeSetoid (StateModel OwnedCfg) NoObs Bn (rel_kripke R) unit owned_equ _}.

  Local Lemma hAN_proper_gen P Q : hproper P -> hproper Q -> hproper (hAN R P Q).
  Proof.
    intros HP HQ x y E; unfold hAN.
    now apply (@proper_ax_equ _ _ _ _ _ _ _ KS (hlift P) (hlift Q)
                 (hlift_proper _ HP) (hlift_proper _ HQ)).
  Qed.

  Local Lemma hEN_proper_gen P Q : hproper P -> hproper Q -> hproper (hEN R P Q).
  Proof.
    intros HP HQ x y E; unfold hEN.
    now apply (@proper_ex_equ _ _ _ _ _ _ _ KS (hlift P) (hlift Q)
                 (hlift_proper _ HP) (hlift_proper _ HQ)).
  Qed.

  Local Lemma hAU_proper_gen P Q : hproper P -> hproper Q -> hproper (hAU R P Q).
  Proof.
    intros HP HQ x y E; unfold hAU.
    now apply (@proper_au_equ _ _ _ _ _ _ _ KS (hlift P) (hlift Q)
                 (hlift_proper _ HP) (hlift_proper _ HQ)).
  Qed.

  Local Lemma hEU_proper_gen P Q : hproper P -> hproper Q -> hproper (hEU R P Q).
  Proof.
    intros HP HQ x y E; unfold hEU.
    now apply (@proper_eu_equ _ _ _ _ _ _ _ KS (hlift P) (hlift Q)
                 (hlift_proper _ HP) (hlift_proper _ HQ)).
  Qed.

  Local Lemma hAG_proper_gen P : hproper P -> hproper (hAG R P).
  Proof.
    intros HP x y E; unfold hAG.
    now apply (@proper_ag_equ _ _ _ _ _ _ _ KS (hlift P) (hlift_proper _ HP)).
  Qed.

  Local Lemma hEG_proper_gen P : hproper P -> hproper (hEG R P).
  Proof.
    intros HP x y E; unfold hEG.
    now apply (@proper_er_equ _ _ _ _ _ _ _ KS (hlift P) (hlift_proper _ HP)).
  Qed.
End Proper.

Lemma hAN_proper P Q : hproper P -> hproper Q -> hproper (hAN owned_next P Q).
Proof. apply hAN_proper_gen. Qed.
Lemma hEN_proper P Q : hproper P -> hproper Q -> hproper (hEN owned_next P Q).
Proof. apply hEN_proper_gen. Qed.
Lemma hAU_proper P Q : hproper P -> hproper Q -> hproper (hAU owned_next P Q).
Proof. apply hAU_proper_gen. Qed.
Lemma hEU_proper P Q : hproper P -> hproper Q -> hproper (hEU owned_next P Q).
Proof. apply hEU_proper_gen. Qed.
Lemma hAG_proper P : hproper P -> hproper (hAG owned_next P).
Proof. apply hAG_proper_gen. Qed.
Lemma hEG_proper P : hproper P -> hproper (hEG owned_next P).
Proof. apply hEG_proper_gen. Qed.
Lemma hAN_weak_proper i P Q : hproper P -> hproper Q -> hproper (hAN (weak_next i) P Q).
Proof. apply hAN_proper_gen. Qed.
Lemma hAU_weak_proper i P Q : hproper P -> hproper Q -> hproper (hAU (weak_next i) P Q).
Proof. apply hAU_proper_gen. Qed.
Lemma hAG_weak_proper i P : hproper P -> hproper (hAG (weak_next i) P).
Proof. apply hAG_proper_gen. Qed.

Local Lemma owned_equ_size c d : owned_equ c d -> tp_size (oc_pool c) = tp_size (oc_pool d).
Proof.
  intros ((F & _) & _); rewrite <- !tp_slots_length; eapply List.Forall2_length, F.
Qed.

Lemma terminal_proper : hproper terminal.
Proof. intros c d E; unfold terminal; now rewrite (owned_equ_size _ _ E). Qed.

Lemma hDone_proper P : hproper P -> hproper (hDone P).
Proof. intros HP c d E; unfold hDone; now rewrite (terminal_proper _ _ E), (HP _ _ E). Qed.

Lemma hRet_proper P : hproper P -> hproper (hRet owned_next P).
Proof.
  intros HP.
  enough (G : forall c d, owned_equ c d -> hRet owned_next P c -> hRet owned_next P d).
  { intros c d E; split; apply G; auto; now symmetry. }
  intros c d E (out & Hout & H).
  destruct (owned_next_equ _ _ _ E Hout) as (dout & Hdout & Eout).
  exists dout; split; [exact Hdout|].
  intros d' TR.
  destruct (owned_next_equ _ _ _ (symmetry E) TR) as (c' & TR' & E').
  destruct (H _ TR') as (Ht & Hr & Hp).
  split; [exact (proj2 (terminal_proper _ _ E') Ht)|split].
  - transitivity c'; [exact (owned_equ_same_view _ _ E')|].
    transitivity out; [exact Hr|exact (owned_equ_same_view _ _ Eout)].
  - exact (proj2 (HP _ _ E') Hp).
Qed.

Lemma hNow_proper P : hproper P -> hproper (hNow P).
Proof. intros HP c d E; unfold hNow; now rewrite (terminal_proper _ _ E), (HP _ _ E). Qed.

Lemma at_side_proper i P : hproper P -> hproper (at_side i P).
Proof. intros HP c d E; unfold at_side; apply HP, project_equ, E. Qed.

Lemma view_pred_proper P : view_pred P -> hproper P.
Proof.
  intros HV c d E; split; apply HV, owned_equ_same_view; auto; now symmetry.
Qed.

(** Heap/context/counter/observation/termination predicates are stable under
    selection, which changes only the focus. *)
Lemma view_selection_stable P : view_pred P -> SelectionStable P.
Proof.
  intros HV d a d' TR K.
  destruct (owned_step_select_only _ _ _ TR K) as (Hh & _ & Hc & Hb & Hn & Hl & Hs).
  split; apply HV; unfold same_view, terminal; rewrite ?Hh, ?Hc, ?Hb, ?Hn, ?Hl, ?Hs;
    repeat split; auto; intros; apply peq_refl.
Qed.

(** ** Ordinary heap separation lifted to owned states *)

(** ** Finite modalities on the global clock *)

Lemma hTrue_proper : hproper hTrue.
Proof. intros c d _; reflexivity. Qed.

Lemma global_hau_project i P Q c :
  hproper P -> hproper Q ->
  hAU owned_next (at_side i P) (at_side i Q) c -> hAU owned_next P Q (project i c).
Proof.
  intros HP HQ; revert c; apply hAU_ind.
  - intros c Hq; now apply hAU_now.
  - intros c Hp Hcan _ IH.
    destruct (scheduler_shape i c Hcan) as [Hst|[Hloc Hlift]].
    + destruct Hcan as [c1 [a Hs]].
      apply (hAU_proper P Q HP HQ (project i c1) (project i c)).
      * exact (owned_step_foreign i c a c1 Hs (Hst a c1 Hs)).
      * exact (IH c1 (ex_intro _ a Hs)).
    + apply hAU_step; [exact Hp|exact Hloc|].
      intros d' [a' Hs'].
      destruct (Hlift a' d' Hs') as (a & c1 & Hs & _ & _ & He).
      apply (hAU_proper P Q HP HQ (project i c1) d' He).
      exact (IH c1 (ex_intro _ a Hs)).
Qed.

Lemma global_heu_project i P Q c :
  hproper P -> hproper Q ->
  hEU owned_next (at_side i P) (at_side i Q) c -> hEU owned_next P Q (project i c).
Proof.
  intros HP HQ; revert c; apply hEU_ind.
  - intros c Hq; now apply hEU_now.
  - intros c c1 Hp [a Hs] _ IH.
    destruct (side_eq_dec (owner a) i) as [Ho|Ho].
    + destruct (owned_step_own i c a c1 Hs Ho) as (d' & Hs' & He).
      apply (hEU_step owned_next P Q (project i c) d' Hp (ex_intro _ (project_action i c a) Hs')).
      exact (proj1 (hEU_proper P Q HP HQ _ _ He) IH).
    + exact (proj1 (hEU_proper P Q HP HQ _ _ (owned_step_foreign i c a c1 Hs Ho)) IH).
Qed.

Theorem global_hau_split P P' Q Q' c :
  coupled c -> hproper P -> hproper P' -> hproper Q -> hproper Q' ->
  hAU owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c))) (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) c ->
  hAU owned_next P Q (project Child c) /\ hAU owned_next P' Q' (project Parent c).
Proof.
  intros _ HP HP' HQ HQ' H; split.
  - apply global_hau_project; [exact HP|exact HQ|].
    revert H; apply hAU_mono; intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd)).
  - apply global_hau_project; [exact HP'|exact HQ'|].
    revert H; apply hAU_mono; intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd)).
Qed.

Theorem global_heu_split P P' Q Q' c :
  coupled c -> hproper P -> hproper P' -> hproper Q -> hproper Q' ->
  hEU owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c))) (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) c ->
  hEU owned_next P Q (project Child c) /\ hEU owned_next P' Q' (project Parent c).
Proof.
  intros _ HP HP' HQ HQ' H; split.
  - apply global_heu_project; [exact HP|exact HQ|].
    revert H; apply hEU_mono; intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd)).
  - apply global_heu_project; [exact HP'|exact HQ'|].
    revert H; apply hEU_mono; intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd)).
Qed.

Corollary global_haf_split Q Q' c :
  coupled c -> hproper Q -> hproper Q' ->
  hAF owned_next (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) c ->
  hAF owned_next Q (project Child c) /\ hAF owned_next Q' (project Parent c).
Proof.
  intros _ HQ HQ' H; split.
  - apply global_hau_project; [exact hTrue_proper|exact HQ|].
    revert H; apply hAU_mono; [now intros|intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd))].
  - apply global_hau_project; [exact hTrue_proper|exact HQ'|].
    revert H; apply hAU_mono; [now intros|intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd))].
Qed.

Corollary global_hef_split Q Q' c :
  coupled c -> hproper Q -> hproper Q' ->
  hEF owned_next (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) c ->
  hEF owned_next Q (project Child c) /\ hEF owned_next Q' (project Parent c).
Proof.
  intros _ HQ HQ' H; split.
  - apply global_heu_project; [exact hTrue_proper|exact HQ|].
    revert H; apply hEU_mono; [now intros|intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd))].
  - apply global_heu_project; [exact hTrue_proper|exact HQ'|].
    revert H; apply hEU_mono; [now intros|intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd))].
Qed.

(** ** The own-action clock *)

Local Lemma weak_can_local i c :
  hcan_step (weak_next i) c -> hcan_step owned_next (project i c).
Proof.
  intros [c1 Hw]; destruct (weak_next_sound i c c1 Hw) as (d' & Hs & _); now exists d'.
Qed.

Local Lemma weak_project_sim_l i c d w w' c1 w1 :
  owned_equ (project i c) d ->
  simW (@event_eq NoObs) (@eq unit) w w' ->
  @ktrans (StateModel OwnedCfg) NoObs Bn
    (rel_kripke (weak_next i)) unit c w c1 w1 ->
  exists d1 w1', @ktrans (StateModel OwnedCfg) NoObs Bn
    (rel_kripke owned_next) unit d w' d1 w1' /\
    owned_equ (project i c1) d1 /\
    simW (@event_eq NoObs) (@eq unit) w1 w1'.
Proof.
  intros He HW (-> & -> & Hstep).
  assert (w' = Pure) as -> by
    (eapply simW_event_eq_not_done; [exact HW|constructor]).
  destruct (weak_next_sound i c c1 Hstep) as (e & Hlocal & He1).
  destruct (owned_next_equ _ _ _ He Hlocal) as (d1 & Hnext & He2).
  exists d1, Pure; split; [repeat split; assumption|].
  split; [transitivity e; assumption|apply SimPure].
Qed.

Local Lemma weak_project_sim_r i c d w w' d1 w1 :
  owned_equ (project i c) d ->
  simW (@event_eq NoObs) (@eq unit) w w' ->
  @can_step (StateModel OwnedCfg) NoObs Bn
    (rel_kripke (weak_next i)) unit c w ->
  @ktrans (StateModel OwnedCfg) NoObs Bn
    (rel_kripke owned_next) unit d w' d1 w1 ->
  exists c1 w1', @ktrans (StateModel OwnedCfg) NoObs Bn
    (rel_kripke (weak_next i)) unit c w c1 w1' /\
    owned_equ (project i c1) d1 /\
    simW (@event_eq NoObs) (@eq unit) w1' w1.
Proof.
  intros He _ (c0 & w0 & -> & -> & Hweak) (-> & -> & Hnext).
  destruct (owned_next_equ _ _ _ (symmetry He) Hnext) as (e & Hlocal & He1).
  destruct (weak_next_complete i c (ex_intro _ c0 Hweak) e Hlocal)
    as (c1 & Hstep & He2).
  exists c1, Pure; split; [repeat split; assumption|].
  split; [transitivity e; [exact He2|symmetry; exact He1]|apply SimPure].
Qed.

Local Lemma weak_project_atom i P : hproper P ->
  forall c d w w', owned_equ (project i c) d ->
    simW (@event_eq NoObs) (@eq unit) w w' ->
    hlift (at_side i P) c w -> hlift P d w'.
Proof. intros HP c d w w' He _ H; exact (proj1 (HP _ _ He) H). Qed.

Theorem weak_han_to_local i P Q c :
  hproper P -> hproper Q ->
  hAN (weak_next i) (at_side i P) (at_side i Q) c -> hAN owned_next P Q (project i c).
Proof.
  intros HP HQ H.
  eapply (@sim_anc (StateModel OwnedCfg) NoObs Bn
    (rel_kripke (weak_next i)) (rel_kripke owned_next) unit
    event_eq eq (fun c d => owned_equ (project i c) d)
    (weak_project_sim_l i) (weak_project_sim_r i)
    (hlift (at_side i P)) (hlift P) (hlift (at_side i Q)) (hlift Q)
    (weak_project_atom i P HP) (weak_project_atom i Q HQ)
    c (project i c) Pure Pure); [reflexivity|apply SimPure|exact H].
Qed.

Theorem weak_hen_to_local i P Q c :
  hproper P -> hproper Q ->
  hEN (weak_next i) (at_side i P) (at_side i Q) c -> hEN owned_next P Q (project i c).
Proof.
  intros HP HQ H.
  eapply (@sim_enc (StateModel OwnedCfg) NoObs Bn
    (rel_kripke (weak_next i)) (rel_kripke owned_next) unit
    event_eq eq (fun c d => owned_equ (project i c) d)
    (weak_project_sim_l i)
    (hlift (at_side i P)) (hlift P) (hlift (at_side i Q)) (hlift Q)
    (weak_project_atom i P HP) (weak_project_atom i Q HQ)
    c (project i c) Pure Pure); [reflexivity|apply SimPure|exact H].
Qed.

Theorem weak_hau_to_local i P Q c :
  hproper P -> hproper Q ->
  hAU (weak_next i) (at_side i P) (at_side i Q) c -> hAU owned_next P Q (project i c).
Proof.
  intros HP HQ H.
  eapply (@sim_auc (StateModel OwnedCfg) NoObs Bn
    (rel_kripke (weak_next i)) (rel_kripke owned_next) unit
    event_eq eq (fun c d => owned_equ (project i c) d)
    (weak_project_sim_l i) (weak_project_sim_r i)
    (hlift (at_side i P)) (hlift P) (hlift (at_side i Q)) (hlift Q)
    (weak_project_atom i P HP) (weak_project_atom i Q HQ)
    c (project i c) Pure Pure); [reflexivity|apply SimPure|exact H].
Qed.

Theorem weak_heu_to_local i P Q c :
  hproper P -> hproper Q ->
  hEU (weak_next i) (at_side i P) (at_side i Q) c -> hEU owned_next P Q (project i c).
Proof.
  intros HP HQ H.
  eapply (@sim_euc (StateModel OwnedCfg) NoObs Bn
    (rel_kripke (weak_next i)) (rel_kripke owned_next) unit
    event_eq eq (fun c d => owned_equ (project i c) d)
    (weak_project_sim_l i)
    (hlift (at_side i P)) (hlift P) (hlift (at_side i Q)) (hlift Q)
    (weak_project_atom i P HP) (weak_project_atom i Q HQ)
    c (project i c) Pure Pure); [reflexivity|apply SimPure|exact H].
Qed.

Theorem weak_hag_to_local i P c :
  hproper P -> hAG (weak_next i) (at_side i P) c -> hAG owned_next P (project i c).
Proof.
  intros HP H.
  eapply (@sim_agc (StateModel OwnedCfg) NoObs Bn
    (rel_kripke (weak_next i)) (rel_kripke owned_next) unit
    event_eq eq (fun c d => owned_equ (project i c) d)
    (weak_project_sim_l i) (weak_project_sim_r i)
    (hlift (at_side i P)) (hlift P) (weak_project_atom i P HP)
    c (project i c) Pure Pure); [reflexivity|apply SimPure|exact H].
Qed.

Theorem weak_heg_to_local i P c :
  hproper P -> hEG (weak_next i) (at_side i P) c -> hEG owned_next P (project i c).
Proof.
  intros HP H.
  eapply (@sim_egc (StateModel OwnedCfg) NoObs Bn
    (rel_kripke (weak_next i)) (rel_kripke owned_next) unit
    event_eq eq (fun c d => owned_equ (project i c) d)
    (weak_project_sim_l i)
    (hlift (at_side i P)) (hlift P) (weak_project_atom i P HP)
    c (project i c) Pure Pure); [reflexivity|apply SimPure|exact H].
Qed.

Corollary weak_hax_to_local i Q c :
  hproper Q -> hAX (weak_next i) (at_side i Q) c -> hAX owned_next Q (project i c).
Proof.
  intros HQ H; apply weak_han_to_local; [exact hTrue_proper|exact HQ|].
  revert H; apply hAN_mono; now intros.
Qed.

Corollary weak_hex_to_local i Q c :
  hproper Q -> hEX (weak_next i) (at_side i Q) c -> hEX owned_next Q (project i c).
Proof.
  intros HQ H; apply weak_hen_to_local; [exact hTrue_proper|exact HQ|].
  revert H; apply hEN_mono; now intros.
Qed.

Corollary weak_haf_to_local i Q c :
  hproper Q -> hAF (weak_next i) (at_side i Q) c -> hAF owned_next Q (project i c).
Proof.
  intros HQ H; apply weak_hau_to_local; [exact hTrue_proper|exact HQ|].
  revert H; apply hAU_mono; now intros.
Qed.

Corollary weak_hef_to_local i Q c :
  hproper Q -> hEF (weak_next i) (at_side i Q) c -> hEF owned_next Q (project i c).
Proof.
  intros HQ H; apply weak_heu_to_local; [exact hTrue_proper|exact HQ|].
  revert H; apply hEU_mono; now intros.
Qed.

Lemma weak_hdone_to_local i P c : at_side i (hDone P) c -> hDone P (project i c).
Proof. exact (fun H => H). Qed.

Theorem weak_hret_to_local i P c :
  hproper P -> hRet_at i (weak_next i) P c -> hRet owned_next P (project i c).
Proof.
  intros HP (out & Hout & Hall).
  destruct (weak_next_sound i c out Hout) as (dout & Hdout & Eout).
  exists dout; split; [exact Hdout|].
  intros d' Hs.
  destruct (weak_next_complete i c (ex_intro _ out Hout) d' Hs) as (c1 & Hw & He).
  destruct (Hall c1 Hw) as (Ht & Hr & Hp).
  split; [exact (proj1 (terminal_proper _ _ He) Ht)|split].
  - transitivity (project i c1); [apply owned_equ_same_view; now symmetry|].
    transitivity (project i out); [exact Hr|exact (owned_equ_same_view _ _ Eout)].
  - exact (proj1 (HP _ _ He) Hp).
Qed.

(** ** Next: the explicit two-program frame theorem *)

Theorem global_han_owned i P Q c :
  hproper P -> hproper Q -> OwnEnabled i c ->
  hAN owned_next (at_side i P) (at_side i Q) c -> hAN owned_next P Q (project i c).
Proof.
  intros _ HQ [Hloc Hlift] H; apply hAN_iff in H as (Hp & _ & Hall); apply hAN_iff.
  split; [exact Hp|split; [exact Hloc|]].
  intros d' [a' Hs']; destruct (Hlift a' d' Hs') as (a & c1 & Hs & _ & _ & He).
  exact (proj1 (HQ _ _ He) (Hall c1 (ex_intro _ a Hs))).
Qed.

Theorem global_hen_owned i P Q c a c' :
  hproper Q -> P (project i c) -> owned_step c a c' -> owner a = i -> Q (project i c') ->
  hEN owned_next P Q (project i c).
Proof.
  intros HQ Hp Hs Ho Hq; apply hEN_iff; split; [exact Hp|].
  destruct (owned_step_own i c a c' Hs Ho) as (d' & Hs' & He).
  exists d'; split; [now exists (project_action i c a)|exact (proj1 (HQ _ _ He) Hq)].
Qed.

(** One side of the AN split: a stuttering lineage only awaits selection. *)
Local Lemma global_han_side i P Q c :
  hproper P -> hproper Q -> 0 < tp_size (oc_pool (project i c)) -> SelectionStable Q ->
  hAN owned_next (at_side i P) (at_side i Q) c -> hAN owned_next P Q (project i c).
Proof.
  intros HP HQ Hsz HS H.
  pose proof H as H0; apply hAN_iff in H0 as (Hp & Hcan & Hall).
  destruct (scheduler_shape i c Hcan) as [Hst|Hen]; [|exact (global_han_owned i P Q c HP HQ Hen H)].
  destruct (stutter_select i c Hcan Hst Hsz) as (_ & Hloc & Hsel).
  assert (Hq : Q (project i c)).
  { destruct Hcan as [c1 [a Hs]].
    exact (proj1 (HQ _ _ (owned_step_foreign i c a c1 Hs (Hst a c1 Hs))) (Hall c1 (ex_intro _ a Hs))). }
  apply hAN_iff; split; [exact Hp|split; [exact Hloc|]].
  intros d' [a' Hs']; exact (proj1 (HS _ _ _ Hs' (Hsel a' d' Hs')) Hq).
Qed.

Theorem global_han_split P P' Q Q' c :
  coupled c -> hproper P -> hproper P' -> hproper Q -> hproper Q' ->
  0 < tp_size (oc_pool (project Child c)) ->
  0 < tp_size (oc_pool (project Parent c)) ->
  SelectionStable Q -> SelectionStable Q' ->
  hAN owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c))) (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) c ->
  hAN owned_next P Q (project Child c) /\ hAN owned_next P' Q' (project Parent c).
Proof.
  intros _ HP HP' HQ HQ' HC HPa HS HS' H; split.
  - apply global_han_side; [exact HP|exact HQ|exact HC|exact HS|].
    revert H; apply hAN_mono; intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd)).
  - apply global_han_side; [exact HP'|exact HQ'|exact HPa|exact HS'|].
    revert H; apply hAN_mono; intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd)).
Qed.

Corollary global_hax_split Q Q' c :
  coupled c -> hproper Q -> hproper Q' ->
  0 < tp_size (oc_pool (project Child c)) ->
  0 < tp_size (oc_pool (project Parent c)) ->
  SelectionStable Q -> SelectionStable Q' ->
  hAX owned_next (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) c ->
  hAX owned_next Q (project Child c) /\ hAX owned_next Q' (project Parent c).
Proof.
  intros _ HQ HQ' HC HPa HS HS' H; split.
  - apply global_han_side; [exact hTrue_proper|exact HQ|exact HC|exact HS|].
    revert H; apply hAN_mono; [now intros|intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd))].
  - apply global_han_side; [exact hTrue_proper|exact HQ'|exact HPa|exact HS'|].
    revert H; apply hAN_mono; [now intros|intros d Hd; apply (proj2 (proj1 (state_split_iff _ _ _) Hd))].
Qed.

(** ** Always: release certificates *)

Definition step_closed (I : hprop) : Prop := forall d a d', I d -> owned_step d a d' -> I d'.

(** From every progressing invariant state, lineage [i] is enabled after
    finitely many rank-decreasing foreign actions. *)
Definition finite_release (i : side) (I : hprop) (rank : OwnedCfg -> nat) : Prop :=
  forall d, I d -> hcan_step owned_next d ->
    OwnEnabled i d \/ exists d', foreign_next i d d' /\ I d' /\ rank d' < rank d.

(** Finitely many rank-decreasing foreign steps reach an enabled state with
    the same projection. *)
Local Lemma release_descent i I rank P :
  step_closed I -> finite_release i I rank ->
  forall n c, rank c < n -> I c -> hAG owned_next P c ->
  exists c1, I c1 /\ hAG owned_next P c1 /\ OwnEnabled i c1 /\
    owned_equ (project i c1) (project i c).
Proof.
  intros Hcl Hrel n; induction n as [|n IH]; intros c Hr HI HG; [lia|].
  pose proof HG as HG'; apply hAG_unfold in HG' as (_ & Hcan & Hsucc).
  destruct (Hrel c HI Hcan) as [Hen | (c' & (a & Hst & Hown) & HI' & Hlt)].
  - exists c; split; [exact HI|split; [exact HG|split; [exact Hen|reflexivity]]].
  - destruct (IH c' ltac:(lia) HI' (Hsucc c' (ex_intro _ a Hst))) as (c1 & HI1 & HG1 & Hen1 & Heq1).
    exists c1; split; [exact HI1|split; [exact HG1|split; [exact Hen1|]]].
    etransitivity; [exact Heq1|exact (owned_step_foreign i c a c' Hst Hown)].
Qed.

Local Lemma global_hag_one i I rank P c :
  hproper P -> I c -> step_closed I -> finite_release i I rank ->
  hAG owned_next (at_side i P) c -> hAG owned_next P (project i c).
Proof.
  intros HP HI Hcl Hrel HG.
  apply (hAG_coind owned_next P
    (fun d => exists c, I c /\ hAG owned_next (at_side i P) c /\ owned_equ (project i c) d));
    [|exists c; split; [exact HI|split; [exact HG|reflexivity]]].
  intros d (c0 & HI0 & HG0 & Heq).
  destruct (release_descent i I rank (at_side i P) Hcl Hrel (S (rank c0)) c0 ltac:(lia) HI0 HG0)
    as (c1 & HI1 & HG1 & [Hcan1 Hlift] & Heq1).
  assert (Heqd : owned_equ (project i c1) d) by (etransitivity; eassumption).
  split; [|split].
  - apply hAG_unfold in HG0 as [HP0 _]; exact (proj1 (HP _ _ Heq) HP0).
  - destruct Hcan1 as (d1 & Hd1).
    destruct (owned_next_equ _ _ _ Heqd Hd1) as (d' & Hd' & _); exists d'; exact Hd'.
  - intros d' Hd'.
    destruct (owned_next_equ _ _ _ (symmetry Heqd) Hd') as (d1 & (a' & Hst1) & Heq').
    destruct (Hlift a' d1 Hst1) as (a & c' & Hst & _ & _ & Heqc').
    exists c'; split; [exact (Hcl _ _ _ HI1 Hst)|split].
    + apply hAG_unfold in HG1 as (_ & _ & Hs); apply Hs; exists a; exact Hst.
    + etransitivity; [exact Heqc'|symmetry; exact Heq'].
Qed.

Theorem global_hag_split I rankC rankP P P' c :
  coupled c -> hproper P -> hproper P' -> I c -> step_closed I ->
  finite_release Child I rankC -> finite_release Parent I rankP ->
  hAG owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c))) c ->
  hAG owned_next P (project Child c) /\ hAG owned_next P' (project Parent c).
Proof.
  intros _ HP HP' HI Hcl HrC HrP HG; split.
  - apply (global_hag_one Child I rankC P c HP HI Hcl HrC).
    eapply hAG_mono; [|exact HG]; intros d Hd; exact (proj1 (proj2 (proj1 (state_split_iff _ _ _) Hd))).
  - apply (global_hag_one Parent I rankP P' c HP' HI Hcl HrP).
    eapply hAG_mono; [|exact HG]; intros d Hd; exact (proj2 (proj2 (proj1 (state_split_iff _ _ _) Hd))).
Qed.

(** ** Exists-always: one fair witness execution *)

Definition owned_run (e : Execution OwnedCfg OwnedAction unit) : Prop :=
  forall n, owned_step (states e n) (selected e n) (states e (S n)).

Theorem global_heg_fair_one i P c (e : Execution OwnedCfg OwnedAction unit) :
  hproper P -> states e 0 = c -> owned_run e ->
  (forall n, P (project i (states e n))) ->
  infinitely (fun n => owner (selected e n) = i) ->
  hEG owned_next P (project i c).
Proof.
  intros HP H0 Hrun HPn Hinf; subst c.
  set (Z := fun d => exists n, owned_equ (project i (states e n)) d).
  (* The own action at [n] is one local step of the projection. *)
  assert (Hown : forall n d, owner (selected e n) = i -> owned_equ (project i (states e n)) d ->
            exists d', owned_next d d' /\ Z d').
  { intros n d Hi Heq.
    destruct (owned_step_own i _ _ _ (Hrun n) Hi) as (d1 & Hst1 & Heq1).
    assert (Hn1 : owned_next (project i (states e n)) d1) by (eexists; exact Hst1).
    destruct (owned_next_equ _ _ _ Heq Hn1) as (d' & Hd' & Heq').
    exists d'; split; [exact Hd'|exists (S n); etransitivity; eassumption]. }
  (* Bounded search for the first own action; foreign ones keep the projection. *)
  assert (Hfirst : forall k n d, owner (selected e (n + k)) = i ->
            owned_equ (project i (states e n)) d -> exists d', owned_next d d' /\ Z d').
  { induction k as [|k IH]; intros n d Hk Heq;
      destruct (side_eq_dec (owner (selected e n)) i) as [Hi|Hf];
      [exact (Hown n d Hi Heq)|rewrite Nat.add_0_r in Hk; contradiction
      |exact (Hown n d Hi Heq)|].
    apply (IH (S n) d); [replace (S n + k) with (n + S k) by lia; exact Hk|].
    etransitivity; [|exact Heq]; exact (owned_step_foreign i _ _ _ (Hrun n) Hf). }
  apply (hEG_coind owned_next P Z); [|exists 0; reflexivity].
  intros d (n & Heq); split; [exact (proj1 (HP _ _ Heq) (HPn n))|].
  destruct (Hinf n) as (m0 & Hle & Hm0); cbv beta in Hm0.
  apply (Hfirst (m0 - n) n d); [replace (n + (m0 - n)) with m0 by lia; exact Hm0|exact Heq].
Qed.

Theorem global_heg_fair_split P P' c (e : Execution OwnedCfg OwnedAction unit) :
  coupled c -> hproper P -> hproper P' -> states e 0 = c -> owned_run e ->
  (forall n, state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c)) (states e n)) ->
  infinitely (fun n => owner (selected e n) = Child) ->
  infinitely (fun n => owner (selected e n) = Parent) ->
  hEG owned_next P (project Child c) /\ hEG owned_next P' (project Parent c).
Proof.
  intros _ HP HP' H0 Hrun Hsep HinfC HinfP; split.
  - apply (global_heg_fair_one Child P c e HP H0 Hrun); [|exact HinfC].
    intros n; exact (proj1 (proj2 (proj1 (state_split_iff _ _ _) (Hsep n)))).
  - apply (global_heg_fair_one Parent P' c e HP' H0 Hrun); [|exact HinfP].
    intros n; exact (proj2 (proj2 (proj1 (state_split_iff _ _ _) (Hsep n)))).
Qed.

(** ** Terminal and returning suffixes *)

Theorem global_hdone_split P Q c :
  hDone (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent Q c))) c -> hDone P (project Child c) /\ hDone Q (project Parent c).
Proof.
  intros (Ht & Hsplit); destruct (proj1 (state_split_iff _ _ _) Hsplit) as (_ & Hp & Hq).
  split; split; try assumption; now apply project_size_terminal.
Qed.

(** The returning lineage of a last global step. *)
Local Lemma hret_side i P out c a c1 :
  hproper P -> owned_step c a c1 -> owner a = i ->
  (forall c', owned_next c c' -> terminal c' /\ same_view c' out /\ at_side i P c') ->
  hRet owned_next P (project i c).
Proof.
  intros HP Hs Ho Hall.
  destruct (scheduler_shape i c (ex_intro _ c1 (ex_intro _ a Hs))) as [Hst|[_ Hlift]].
  { exfalso; exact (Hst a c1 Hs Ho). }
  destruct (owned_step_own i c a c1 Hs Ho) as (dout & Hdout & Eout).
  destruct (Hall c1 (ex_intro _ a Hs)) as (Ht1 & Hr1 & _).
  exists dout; split; [exists (project_action i c a); exact Hdout|].
  intros d' [a' Hs']; destruct (Hlift a' d' Hs') as (b & c' & Hb & _ & _ & He).
  destruct (Hall c' (ex_intro _ b Hb)) as (Ht & Hr & Hp).
  split; [|split].
  - exact (proj1 (terminal_proper _ _ He) (project_size_terminal i c' Ht)).
  - transitivity (project i c'); [apply owned_equ_same_view; now symmetry|].
    transitivity (project i out); [exact (same_view_project i c' out Ht Hr)|].
    transitivity (project i c1); [symmetry; exact (same_view_project i c1 out Ht1 Hr1)|].
    exact (owned_equ_same_view _ _ Eout).
  - exact (proj1 (HP _ _ He) Hp).
Qed.

(** The other lineage was already done. *)
Local Lemma hdone_side j P c a c1 :
  hproper P -> owned_step c a c1 -> owner a <> j -> terminal c1 -> at_side j P c1 ->
  hDone P (project j c).
Proof.
  intros HP Hs Ho Ht Hp; pose proof (owned_step_foreign j c a c1 Hs Ho) as He.
  split.
  - exact (proj1 (terminal_proper _ _ He) (project_size_terminal j c1 Ht)).
  - exact (proj1 (HP _ _ He) Hp).
Qed.

(** One global step cannot return both lineages. *)
Theorem global_hret_split P Q c :
  hproper P -> hproper Q -> hRet owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent Q c))) c ->
  (hRet owned_next P (project Child c) /\ hDone Q (project Parent c)) \/
  (hDone P (project Child c) /\ hRet owned_next Q (project Parent c)).
Proof.
  intros HP HQ (c1 & [a Hs] & Hall).
  destruct (Hall c1 (ex_intro _ a Hs)) as (Ht & _ & Hsplit).
  destruct (proj1 (state_split_iff _ _ _) Hsplit) as (_ & Hp & Hq).
  destruct (owner a) eqn:Ho; [left|right]; split.
  - apply (hret_side Child P c1 c a c1 HP Hs Ho).
    intros c' Hn; destruct (Hall c' Hn) as (Ht' & Hr' & Hsplit').
    destruct (proj1 (state_split_iff _ _ _) Hsplit') as (_ & Hp' & Hq'); auto.
  - apply (hdone_side Parent Q c a c1 HQ Hs); [now rewrite Ho|exact Ht|exact Hq].
  - apply (hdone_side Child P c a c1 HP Hs); [now rewrite Ho|exact Ht|exact Hp].
  - apply (hret_side Parent Q c1 c a c1 HQ Hs Ho).
    intros c' Hn; destruct (Hall c' Hn) as (Ht' & Hr' & Hsplit').
    destruct (proj1 (state_split_iff _ _ _) Hsplit') as (_ & Hp' & Hq'); auto.
Qed.

(** ** Source corollaries at the outer fork *)

Local Lemma hproper_transport P c d : hproper P -> owned_equ c d -> P c -> P d.
Proof. intros HP Heq; exact (proj1 (HP c d Heq)). Qed.

Local Lemma init_local_same_view i p h ctx base :
  same_view (init_local i p h ctx base false) (init_local i p h ctx base true).
Proof. unfold same_view, terminal; cbn; repeat split; intros; first [reflexivity|assumption]. Qed.

Local Lemma init_local_next i p h ctx base :
  owned_next (init_local i p h ctx base false) (init_local i p h ctx base true).
Proof. exists (act i OASelect); apply init_local_select; split; reflexivity. Qed.

(** The projected child still owes its selection; for predicates that only
    read the heap view, that step can be stripped. *)
Lemma hAU_select_strip i p h ctx base P Q :
  view_pred P -> view_pred Q ->
  hAU owned_next P Q (init_local i p h ctx base false) ->
  hAU owned_next P Q (init_local i p h ctx base true).
Proof.
  intros _ HQ HU.
  apply (hAU_ind owned_next P Q
    (fun c => Q c \/ forall c', owned_next c c' -> hAU owned_next P Q c')) in HU
    as [Hq|Hs]; [| |intros c Hc; left; exact Hc|intros c _ _ Hs _; right; exact Hs].
  - apply hAU_now; exact (HQ _ _ (init_local_same_view i p h ctx base) Hq).
  - exact (Hs _ (init_local_next i p h ctx base)).
Qed.

Lemma hEU_select_strip i p h ctx base P Q :
  view_pred P -> view_pred Q ->
  hEU owned_next P Q (init_local i p h ctx base false) ->
  hEU owned_next P Q (init_local i p h ctx base true).
Proof.
  intros _ HQ HE0.
  apply (hEU_ind owned_next P Q
    (fun c => Q c \/ exists c', owned_next c c' /\ hEU owned_next P Q c')) in HE0
    as [Hq|(c' & (a & Hst) & HE)];
    [| |intros c Hc; left; exact Hc|intros c c' _ Hc' HE _; right; exists c'; split; assumption].
  - apply hEU_now; exact (HQ _ _ (init_local_same_view i p h ctx base) Hq).
  - apply init_local_select in Hst as [_ ->]; exact HE.
Qed.

(** AG already holds at every successor: no stability assumption. *)
Lemma hAG_select_strip i p h ctx base P :
  hAG owned_next P (init_local i p h ctx base false) ->
  hAG owned_next P (init_local i p h ctx base true).
Proof.
  intros HG; apply hAG_unfold in HG as (_ & _ & Hs); exact (Hs _ (init_local_next i p h ctx base)).
Qed.

Theorem fork_hau_split child k h h' ctx base P P' Q Q' :
  admissible child (k tt) h h' ctx base ->
  hproper P -> hproper P' -> hproper Q -> hproper Q' ->
  hAU owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c))) (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) (init_owned child (k tt) h h' ctx base) ->
  hAU owned_next P Q (init_local Child child h ctx base false) /\
  hAU owned_next P' Q' (init_local Parent (k tt) h' ctx base true).
Proof.
  intros Hadm HP HP' HQ HQ' HU.
  destruct (global_hau_split P P' Q Q' _ (coupled_init _ _ _ _ _ _ Hadm) HP HP' HQ HQ' HU)
    as [HC HPa]; split.
  - exact (hproper_transport _ _ _ (hAU_proper P Q HP HQ)
      (project_init_child child (k tt) h h' ctx base) HC).
  - exact (hproper_transport _ _ _ (hAU_proper P' Q' HP' HQ')
      (project_init_parent child (k tt) h h' ctx base) HPa).
Qed.

Theorem fork_heu_split child k h h' ctx base P P' Q Q' :
  admissible child (k tt) h h' ctx base ->
  hproper P -> hproper P' -> hproper Q -> hproper Q' ->
  hEU owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c))) (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) (init_owned child (k tt) h h' ctx base) ->
  hEU owned_next P Q (init_local Child child h ctx base false) /\
  hEU owned_next P' Q' (init_local Parent (k tt) h' ctx base true).
Proof.
  intros Hadm HP HP' HQ HQ' HE.
  destruct (global_heu_split P P' Q Q' _ (coupled_init _ _ _ _ _ _ Hadm) HP HP' HQ HQ' HE)
    as [HC HPa]; split.
  - exact (hproper_transport _ _ _ (hEU_proper P Q HP HQ)
      (project_init_child child (k tt) h h' ctx base) HC).
  - exact (hproper_transport _ _ _ (hEU_proper P' Q' HP' HQ')
      (project_init_parent child (k tt) h h' ctx base) HPa).
Qed.

(** Heap-view assertions at the conventional focused singletons. *)
Corollary fork_hau_split_view child k h h' ctx base P P' Q Q' :
  admissible child (k tt) h h' ctx base ->
  view_pred P -> view_pred P' -> view_pred Q -> view_pred Q' ->
  hAU owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c))) (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) (init_owned child (k tt) h h' ctx base) ->
  hAU owned_next P Q (init_local Child child h ctx base true) /\
  hAU owned_next P' Q' (init_local Parent (k tt) h' ctx base true).
Proof.
  intros Hadm HP HP' HQ HQ' HU.
  destruct (fork_hau_split child k h h' ctx base P P' Q Q' Hadm (view_pred_proper _ HP)
    (view_pred_proper _ HP') (view_pred_proper _ HQ) (view_pred_proper _ HQ') HU) as [HC HPa].
  split; [exact (hAU_select_strip _ _ _ _ _ P Q HP HQ HC)|exact HPa].
Qed.

Corollary fork_heu_split_view child k h h' ctx base P P' Q Q' :
  admissible child (k tt) h h' ctx base ->
  view_pred P -> view_pred P' -> view_pred Q -> view_pred Q' ->
  hEU owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c))) (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) (init_owned child (k tt) h h' ctx base) ->
  hEU owned_next P Q (init_local Child child h ctx base true) /\
  hEU owned_next P' Q' (init_local Parent (k tt) h' ctx base true).
Proof.
  intros Hadm HP HP' HQ HQ' HE.
  destruct (fork_heu_split child k h h' ctx base P P' Q Q' Hadm (view_pred_proper _ HP)
    (view_pred_proper _ HP') (view_pred_proper _ HQ) (view_pred_proper _ HQ') HE) as [HC HPa].
  split; [exact (hEU_select_strip _ _ _ _ _ P Q HP HQ HC)|exact HPa].
Qed.

Theorem fork_han_split child k h h' ctx base P P' Q Q' :
  admissible child (k tt) h h' ctx base ->
  hproper P -> hproper P' -> hproper Q -> hproper Q' ->
  SelectionStable Q -> SelectionStable Q' ->
  hAN owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c))) (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) (init_owned child (k tt) h h' ctx base) ->
  hAN owned_next P Q (init_local Child child h ctx base false) /\
  hAN owned_next P' Q' (init_local Parent (k tt) h' ctx base true).
Proof.
  intros Hadm HP HP' HQ HQ' HsQ HsQ' HN.
  destruct (global_han_split P P' Q Q' _ (coupled_init _ _ _ _ _ _ Hadm) HP HP' HQ HQ'
    ltac:(cbn; lia) ltac:(cbn; lia) HsQ HsQ' HN) as [HC HPa]; split.
  - exact (hproper_transport _ _ _ (hAN_proper P Q HP HQ)
      (project_init_child child (k tt) h h' ctx base) HC).
  - exact (hproper_transport _ _ _ (hAN_proper P' Q' HP' HQ')
      (project_init_parent child (k tt) h h' ctx base) HPa).
Qed.

Corollary fork_hax_split child k h h' ctx base Q Q' :
  admissible child (k tt) h h' ctx base ->
  hproper Q -> hproper Q' -> SelectionStable Q -> SelectionStable Q' ->
  hAX owned_next (state_sat (fun c => asep (state_obligation Child Q c) (state_obligation Parent Q' c))) (init_owned child (k tt) h h' ctx base) ->
  hAX owned_next Q (init_local Child child h ctx base false) /\
  hAX owned_next Q' (init_local Parent (k tt) h' ctx base true).
Proof.
  intros Hadm HQ HQ' HsQ HsQ' HX.
  destruct (global_hax_split Q Q' _ (coupled_init _ _ _ _ _ _ Hadm) HQ HQ'
    ltac:(cbn; lia) ltac:(cbn; lia) HsQ HsQ' HX) as [HC HPa]; split.
  - exact (hproper_transport _ _ _ (hAN_proper hTrue Q hTrue_proper HQ)
      (project_init_child child (k tt) h h' ctx base) HC).
  - exact (hproper_transport _ _ _ (hAN_proper hTrue Q' hTrue_proper HQ')
      (project_init_parent child (k tt) h h' ctx base) HPa).
Qed.

Theorem fork_hag_split child k h h' ctx base I rankC rankP P P' :
  admissible child (k tt) h h' ctx base ->
  hproper P -> hproper P' ->
  I (init_owned child (k tt) h h' ctx base) -> step_closed I ->
  finite_release Child I rankC -> finite_release Parent I rankP ->
  hAG owned_next (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c))) (init_owned child (k tt) h h' ctx base) ->
  hAG owned_next P (init_local Child child h ctx base true) /\
  hAG owned_next P' (init_local Parent (k tt) h' ctx base true).
Proof.
  intros Hadm HP HP' HI Hcl HrC HrP HG.
  destruct (global_hag_split I rankC rankP P P' _ (coupled_init _ _ _ _ _ _ Hadm)
    HP HP' HI Hcl HrC HrP HG) as [HC HPa]; split.
  - apply hAG_select_strip.
    exact (hproper_transport _ _ _ (hAG_proper P HP)
      (project_init_child child (k tt) h h' ctx base) HC).
  - exact (hproper_transport _ _ _ (hAG_proper P' HP')
      (project_init_parent child (k tt) h h' ctx base) HPa).
Qed.

Theorem fork_heg_fair_split child k h h' ctx base P P' (e : Execution OwnedCfg OwnedAction unit) :
  admissible child (k tt) h h' ctx base ->
  hproper P -> hproper P' ->
  states e 0 = init_owned child (k tt) h h' ctx base -> owned_run e ->
  (forall n, state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent P' c)) (states e n)) ->
  infinitely (fun n => owner (selected e n) = Child) ->
  infinitely (fun n => owner (selected e n) = Parent) ->
  hEG owned_next P (init_local Child child h ctx base true) /\
  hEG owned_next P' (init_local Parent (k tt) h' ctx base true).
Proof.
  intros Hadm HP HP' H0 Hrun Hsep HinfC HinfP.
  destruct (global_heg_fair_split P P' _ e (coupled_init _ _ _ _ _ _ Hadm)
    HP HP' H0 Hrun Hsep HinfC HinfP) as [HC HPa]; split.
  - apply (hproper_transport _ _ _ (hEG_proper P HP)
      (project_init_child child (k tt) h h' ctx base)) in HC.
    apply hEG_unfold in HC as (_ & c' & (a & Hst) & HE).
    apply init_local_select in Hst as [_ ->]; exact HE.
  - exact (hproper_transport _ _ _ (hEG_proper P' HP')
      (project_init_parent child (k tt) h h' ctx base) HPa).
Qed.

(** ** Original TICL judgments and the erased action clock *)

Import CTreeNotations TiclNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope nat_scope.


(** Extensional heap equivalence determines the concrete target return. *)
Lemma owned_result_rel_right_unique :
  forall (r r1 r2 : SSig * unit),
    owned_result_rel r r1 -> owned_result_rel r r2 -> r1 = r2.
Proof.
  intros [[[h al] aux] x] [[[h1 al1] aux1] x1] [[[h2 al2] aux2] x2].
  unfold owned_result_rel, csl_memory; cbn.
  intros (Hx1 & HA1 & [Hh1 Hal1]) (Hx2 & HA2 & [Hh2 Hal2]).
  assert (Hh : h1 = h2).
  { apply functional_extensionality; intro a.
    now rewrite <- (Hh1 a), <- (Hh2 a). }
  assert (Hal : al1 = al2).
  { apply functional_extensionality; intro a.
    now rewrite <- (Hal1 a), <- (Hal2 a). }
  subst; reflexivity.
Qed.

(** Canonical execution transports arbitrary formulas between related worlds;
    native return predicates retain the full [owned_result_rel] contract. *)
Theorem owned_ticl_transport c {b : bool}
    (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) w w' :
  erasable c -> simW event_eq owned_result_rel w w' ->
  entails (SSig * unit) b p (owned_interp c) w ->
  entails (SSig * unit) b (framer (SSig * unit) b event_eq owned_result_rel p)
    (interp_schedule_nd sh (tp_size (oc_pool c))
      (tp_threads (oc_pool c)) (tp_focus (oc_pool c)) (joined_state c)) w'.
Proof.
  intros He HW Hp; eapply (ticl_csim b event_eq owned_result_rel p).
  - destruct b; [split; [apply event_eq_right_unique | apply owned_result_rel_right_unique] | exact I].
  - assert (HR : forall t : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit),
        csim event_eq owned_result_rel t t).
    { unfold csim; coinduction R IH; intro t; split.
      - intros l u HT; exists l, u; split; [exact HT|split; [|apply IH]].
        destruct l as [|Y e v|Y v].
        + apply SimLTau.
        + apply SimLObs; reflexivity.
        + pose proof (trans_val_invT HT) as HY; subst Y.
          apply SimLVal; destruct v as [s x]; unfold owned_result_rel;
            repeat split; reflexivity.
      - intros _ l u HT; exists l, u; split; [exact HT|split; [|apply IH]].
        destruct l as [|Y e v|Y v].
        + apply SimLTau.
        + apply SimLObs; reflexivity.
        + pose proof (trans_val_invT HT) as HY; subst Y.
          apply SimLVal; destruct v as [s x]; unfold owned_result_rel;
            repeat split; reflexivity. }
    apply HR.
  - exact HW.
  - exact Hp.
Qed.

Local Lemma silent_owned_reach c d :
  clos_refl_trans _ silent_next c d -> clos_refl_trans _ owned_next c d.
Proof.
  induction 1 as [c d (a & Hs & _)|c|c d e _ IH1 _ IH2].
  - apply rt_step; exists a; exact Hs.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Local Lemma owned_reach_before c d e :
  clos_refl_trans _ owned_next c d ->
  clos_trans _ (fun y x => owned_next x y) e d ->
  clos_trans _ (fun y x => owned_next x y) e c.
Proof.
  induction 1 as [c d Hs|c|c d f _ IH1 _ IH2]; intro H.
  - eapply t_trans; [exact H|now apply t_step].
  - exact H.
  - apply IH1, IH2, H.
Qed.

Local Lemma erased_visible_world a post l
    (t u : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)) w :
  erase_action_label a post = Some l -> not_done w -> trans l t u ->
  exists w', |t, w| ↦ |u, w'| /\ not_done w'.
Proof.
  intros HL Hw HT; destruct a as [i kind];
    destruct kind as [| | | | | | |base|success| |payload global_index];
    try destruct base; try destruct success;
    cbn in HL; try discriminate; injection HL as <-.
  all: try (exists w; split; [apply KtransTau; assumption|exact Hw]).
  all: try (exists (World.Obs (Log (CSLHeap post)) tt);
    split; [apply KtransObs; assumption|constructor]).
  exists (World.Obs (Log (CSLEmit (stamp payload global_index))) tt).
  split; [apply KtransObs; assumption|constructor].
Qed.

(** Inversion keeps exact configurations; only the computed residual uses
    ordinary bisimulation.  In particular this does not use [owned_equ]. *)
Local Lemma erased_terminal_world
    (t u : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)) (r : SSig * unit) w :
  not_done w -> trans (val r) t u ->
  exists w', |t, w| ↦ |u, w'| /\ done_with (fun r' _ => r' = r) w'.
Proof.
  intros Hw HT; destruct Hw as [|Y e v].
  - exists (Done r); split; [now apply KtransDone|constructor; reflexivity].
  - exists (Finish e v r); split; [now apply KtransFinish|constructor; reflexivity].
Qed.

Local Lemma haf_done_next Q c d :
  hAF owned_next (hDone Q) c -> owned_next c d -> hAF owned_next (hDone Q) d.
Proof.
  revert c; apply (hAU_ind owned_next hTrue (hDone Q)
    (fun c => owned_next c d -> hAF owned_next (hDone Q) d));
    [intros c [Ht _] [a Hs]; exfalso; exact (owned_step_empty c a d Ht Hs)
    |intros c _ _ H _ Hs; exact (H d Hs)].
Qed.

Local Lemma haf_done_reach Q c d :
  clos_refl_trans _ owned_next c d ->
  hAF owned_next (hDone Q) c -> hAF owned_next (hDone Q) d.
Proof.
  induction 1 as [c d Hs|c|c d e _ IH1 _ IH2]; intro H;
    [exact (haf_done_next Q c d H Hs)|exact H|exact (IH2 (IH1 H))].
Qed.

Local Lemma haf_done_terminal Q c :
  hAF owned_next (hDone Q) c -> terminal c -> Q c.
Proof.
  revert c; apply (hAU_ind owned_next hTrue (hDone Q) (fun c => terminal c -> Q c)).
  - intros c [_ HQ] _; exact HQ.
  - intros c _ [d [a Hs]] _ _ Ht; exfalso; exact (owned_step_empty c a d Ht Hs).
Qed.

Local Lemma haf_done_acc Q c :
  hAF owned_next (hDone Q) c -> Acc (fun d c => owned_next c d) c.
Proof.
  revert c; apply (hAU_ind owned_next hTrue (hDone Q)
    (fun c => Acc (fun d c => owned_next c d) c)).
  - intros c [Ht _]; constructor; intros d [a Hs]; exfalso;
      exact (owned_step_empty c a d Ht Hs).
  - intros c _ _ _ IH; constructor; exact IH.
Qed.

(** A finite owned proof supplies either a terminal silent frontier, where
    native return closes immediately, or a genuine visible successor. *)
Local Lemma haf_done_frontier Q c :
  hAF owned_next (hDone Q) c ->
  exists d, clos_refl_trans _ silent_next c d /\
    (terminal d \/ exists a d' l, owned_step d a d' /\ erase_action_label a (joined_heap d') = Some l).
Proof.
  revert c; apply (hAU_ind owned_next hTrue (hDone Q)
    (fun c => exists d, clos_refl_trans _ silent_next c d /\
      (terminal d \/ exists a d' l, owned_step d a d' /\ erase_action_label a (joined_heap d') = Some l))).
  - intros c [Ht _]; exists c; split; [apply rt_refl|now left].
  - intros c _ [d [a Hs]] _ IH.
    destruct (erase_action_label a (joined_heap d)) as [l|] eqn:HL.
    + exists c; split; [apply rt_refl|right; exists a, d, l; now split].
    + destruct (IH d (ex_intro _ a Hs)) as (e & Hp & Hf).
      exists e; split; [|exact Hf].
      eapply rt_trans with (y := d); [apply rt_step; exists a; now split|exact Hp].
Qed.

Local Lemma haf_done_can_raw Q c w :
  erasable c -> not_done w -> hAF owned_next (hDone Q) c ->
  can_step (owned_interp c) w.
Proof.
  intros He Hw HA; destruct (haf_done_frontier Q c HA) as (d & Hp & [Ht|(a & d' & l & Hs & HL)]).
  - destruct (owned_interp_terminal_trans c d He Hp Ht) as (T & HT & _).
    destruct (erased_terminal_world _ _ _ _ Hw HT) as (w' & HW & _); now exists T, w'.
  - destruct (owned_interp_visible c d a d' l He Hp Hs HL) as (T & HT & _).
    destruct (erased_visible_world a _ l _ _ _ HL Hw HT) as (w' & HW & _); now exists T, w'.
Qed.

Theorem owned_haf_ret_ticl (Q : SSig * unit -> Prop) c w :
  erasable c -> not_done w -> Proper (owned_result_rel ==> iff) Q ->
  hAF owned_next (hDone (fun d => Q (joined_state d, tt))) c ->
  <( {owned_interp c}, w |=R AF ret {fun r _ => Q r} )>.
Proof.
  intros He Hw _ HA.
  pose proof (Acc_clos_trans _ _ _ (haf_done_acc _ c HA)) as Hacc.
  assert (H : forall d, Acc (clos_trans _ (fun y x => owned_next x y)) d ->
      forall (t : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)) z,
      t ~ owned_interp d -> erasable d -> not_done z ->
      hAF owned_next (hDone (fun d => Q (joined_state d, tt))) d ->
      auc (entails (SSig * unit) false (CNow (fun _ => True)))
        (entails (SSig * unit) true (CRet (fun r _ => Q r))) t z).
  { intros d Hacc0; induction Hacc0 as [d _ IH]; intros t z HB He0 Hz HA0.
    destruct (haf_done_frontier _ d HA0) as (f & Hp & [Ht|(a & f' & l & Hs & HL)]).
    - apply MatchA.
      assert (HE : t ~ (Ret (joined_state f, tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))).
      { etransitivity; [exact HB|]; etransitivity;
          [exact (owned_interp_silent d f He0 Hp)|exact (owned_interp_terminal f (erasable_reach d f He0 (silent_owned_reach d f Hp)) Ht)]. }
      rewrite HE; apply ret_ret; [exact Hz|].
      exact (haf_done_terminal _ f
        (haf_done_reach _ d f (silent_owned_reach d f Hp) HA0) Ht).
    - destruct (owned_interp_visible d f a f' l He0 Hp Hs HL) as (V & HV & _).
      destruct (erased_visible_world a _ l _ _ _ HL Hz HV) as (zv & HWV & Hzv).
      apply StepA; split; [split; [exact I|exact Hz]|split].
      + assert (HC : can_step (owned_interp d) z) by (exists V, zv; exact HWV).
        now rewrite HB.
      + intros T z' HT.
        destruct (ktrans_semiproper _ _ _ _ _ HB HT) as (U & HU & HTU).
        destruct (not_done_dec z') as [Hz'|Hz'].
        * destruct (owned_ktrans_forward d z U z' He0 Hz HU Hz')
            as (g & b & g' & l' & Hpg & Hsg & HLg & HUf & Hworld).
          assert (Hr : clos_refl_trans _ owned_next d g) by now apply silent_owned_reach.
          apply (IH g'); [eapply owned_reach_before; [exact Hr|apply t_step; exists b; exact Hsg]| | |exact Hz'|].
          -- etransitivity; eassumption.
          -- eapply erasable_step; [exact (erasable_reach d g He0 Hr)|exact Hsg].
          -- eapply haf_done_next; [exact (haf_done_reach _ d g Hr HA0)|exists b; exact Hsg].
        * destruct (owned_ktrans_terminal d z U z' He0 HU
            ltac:(destruct Hz' as [X HD]; intro Hnd; inversion HD; subst; inversion Hnd))
            as (g & Hpg & Htg & HUstuck & HD).
          exfalso.
          assert (HE : owned_interp d ~
              (Ret (joined_state g, tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))).
          { etransitivity; [exact (owned_interp_silent d g He0 Hpg)|exact (owned_interp_terminal g (erasable_reach d g He0 (silent_owned_reach d g Hpg)) Htg)]. }
          assert (HR : <( {owned_interp d}, z |=R ret {fun _ _ => True} )>).
          { ticl_normalize; rewrite HE; apply ret_ret; [exact Hz|exact I]. }
          apply ticl_ret in HR as (r & _ & _ & _ & Hreturn).
          specialize (Hreturn V zv HWV); inversion Hreturn; subst; inversion Hzv. }
  apply ticl_au; exact (H c Hacc _ w (reflexivity _) He Hw HA).
Qed.

Theorem owned_haf_done_ticl (Q : SSig * unit -> Prop) c w :
  erasable c -> not_done w -> Proper (owned_result_rel ==> iff) Q ->
  hAF owned_next (hDone (fun d => Q (joined_state d, tt))) c ->
  auc (entails (SSig * unit) false (CNow (fun _ => True)))
    (fun _ wd => done_with (fun r _ => Q r) wd)
    (owned_interp c) w.
Proof. intros He Hw HQ HA; apply af_ret_done; exact (owned_haf_ret_ticl Q c w He Hw HQ HA). Qed.

Theorem owned_hef_ret_ticl (Q : SSig * unit -> Prop) c w :
  erasable c -> not_done w -> Proper (owned_result_rel ==> iff) Q ->
  hEF owned_next (hDone (fun d => Q (joined_state d, tt))) c ->
  <( {owned_interp c}, w |=R EF ret {fun r _ => Q r} )>.
Proof.
  intros He Hw _ HE.
  apply ticl_eu.
  refine ((hEU_ind owned_next hTrue (hDone (fun d => Q (joined_state d, tt)))
    (fun d => forall start, erasable start -> clos_refl_trans _ silent_next start d ->
      forall w, not_done w ->
      euc (entails (SSig * unit) false (CNow (fun _ => True)))
        (entails (SSig * unit) true (CRet (fun r _ => Q r))) (owned_interp start) w)
    _ _ c HE) c He (rt_refl _ _ c) w Hw).
  - intros d [Ht HQ] start He0 Hp z Hz.
    apply MatchE.
    assert (HB : owned_interp start ~
        (Ret (joined_state d, tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))).
    { etransitivity; [exact (owned_interp_silent start d He0 Hp)|exact (owned_interp_terminal d (erasable_reach start d He0 (silent_owned_reach start d Hp)) Ht)]. }
    rewrite HB; apply ret_ret; assumption.
  - intros d d' _ [a Hs] _ IH start He0 Hp z Hz.
    destruct (erase_action_label a (joined_heap d')) as [l|] eqn:HL.
    + destruct (owned_interp_visible start d a d' l He0 Hp Hs HL) as (T & HT & HB).
      destruct (erased_visible_world a _ l _ _ _ HL Hz HT) as (z' & HW & Hz').
      apply StepE; split; [now split|exists T, z'; split; [exact HW|]].
      rewrite HB; apply (IH d'); [|apply rt_refl|exact Hz'].
      eapply erasable_step; [apply (erasable_reach start d He0), silent_owned_reach, Hp|exact Hs].
    + apply (IH start He0); [|exact Hz].
      eapply rt_trans; [exact Hp|apply rt_step; exists a; auto].
Qed.

Theorem owned_hef_done_ticl (Q : SSig * unit -> Prop) c w :
  erasable c -> not_done w -> Proper (owned_result_rel ==> iff) Q ->
  hEF owned_next (hDone (fun d => Q (joined_state d, tt))) c ->
  euc (entails (SSig * unit) false (CNow (fun _ => True)))
    (fun _ wd => done_with (fun r _ => Q r) wd)
    (owned_interp c) w.
Proof. intros He Hw HQ HE; apply ef_ret_done; exact (owned_hef_ret_ticl Q c w He Hw HQ HE). Qed.

Local Lemma hag_owned_reach I c d :
  clos_refl_trans _ owned_next c d -> hAG owned_next I c -> hAG owned_next I d.
Proof.
  induction 1 as [c d Hs|c|c d e _ IH1 _ IH2]; intro HG.
  - apply hAG_unfold in HG as (_ & _ & HN); exact (HN d Hs).
  - exact HG.
  - exact (IH2 (IH1 HG)).
Qed.

Local Lemma hag_visible_frontier I rank :
  (forall d a d', I d -> owned_step d a d' ->
    erase_action_label a (joined_heap d') = None -> rank d' < rank d) ->
  forall c, hAG owned_next I c ->
  exists d a d' l, clos_refl_trans _ silent_next c d /\
    owned_step d a d' /\ erase_action_label a (joined_heap d') = Some l.
Proof.
  intros Hrank.
  assert (H : forall bound c, rank c < bound -> hAG owned_next I c ->
    exists d a d' l, clos_refl_trans _ silent_next c d /\
      owned_step d a d' /\ erase_action_label a (joined_heap d') = Some l).
  { induction bound as [|bound IH]; intros c Hbound HG; [lia|].
    apply hAG_unfold in HG as (HI & [d [a Hs]] & HN).
    destruct (erase_action_label a (joined_heap d)) as [l|] eqn:HL.
    - exists c, a, d, l; split; [apply rt_refl|auto].
    - destruct (IH d ltac:(pose proof (Hrank c a d HI Hs HL); lia)
        (HN d (ex_intro _ a Hs))) as (f & b & f' & l & Hp & Hb & Hbl).
      exists f, b, f', l; split; [|auto].
      eapply rt_trans with (y := d); [apply rt_step; exists a; now split|exact Hp]. }
  intros c HG; apply (H (S (rank c)) c); [lia|exact HG].
Qed.

Theorem owned_hag_ticl (I : hprop) (rank : OwnedCfg -> nat) c w :
  erasable c -> not_done w -> hproper I ->
  (forall d a d', I d -> owned_step d a d' ->
     erase_action_label a (joined_heap d') = None -> rank d' < rank d) ->
  hAG owned_next I c -> <( {owned_interp c}, w |=L AG ⊤ )>.
Proof.
  intros He Hw _ Hrank HG.
  set (Z := fun (t : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))
    (z : World (writerE (CSLObs (nat * nat)))) =>
    not_done z /\ exists d, erasable d /\ hAG owned_next I d /\
      t ~ owned_interp d).
  ticl_normalize; rewrite unfold_entails_ag.
  apply (leq_gfp (agcF (entails (SSig * unit) false (CNow (fun _ => True)))) Z).
  - intros t z (Hz & d & He0 & HG0 & HB).
    change ((True /\ not_done z) /\ can_step t z /\
      forall T z', |t, z| ↦ |T, z'| -> Z T z').
    split; [now split|split].
    + destruct (hag_visible_frontier I rank Hrank d HG0) as (f & a & f' & l & Hp & Hs & HL).
      destruct (owned_interp_visible d f a f' l He0 Hp Hs HL) as (T & HT & _).
      destruct (erased_visible_world a _ l _ _ _ HL Hz HT) as (z' & HW & _).
      destruct (ktrans_semiproper _ _ _ _ _ (symmetry HB) HW) as (U & HU & _).
      now exists U, z'.
    + intros T z' HT.
      destruct (ktrans_semiproper _ _ _ _ _ HB HT) as (U & HU & HTU).
      destruct (not_done_dec z') as [Hz'|Hz'].
      * destruct (owned_ktrans_forward d z U z' He0 Hz HU Hz')
          as (f & a & f' & l & Hp & Hs & HL & HUf & Hworld).
        split; [exact Hz'|exists f']; split; [|split].
        -- eapply erasable_step; [apply (erasable_reach d f He0), silent_owned_reach, Hp|exact Hs].
        -- pose proof (hag_owned_reach I d f (silent_owned_reach d f Hp) HG0) as HGf.
           apply hAG_unfold in HGf as (_ & _ & HN).
           exact (HN f' (ex_intro _ a Hs)).
        -- etransitivity; eassumption.
      * destruct (owned_ktrans_terminal d z U z' He0 HU
          ltac:(destruct Hz' as [X HD]; intro Hnd; inversion HD; subst; inversion Hnd))
          as (f & Hp & Ht & HUstuck & HD).
        pose proof (hag_owned_reach I d f (silent_owned_reach d f Hp) HG0) as HGf.
        apply hAG_unfold in HGf as (_ & [f' [a Hs]] & _).
        exfalso; exact (owned_step_empty f a f' Ht Hs).
  - split; [exact Hw|exists c; split; [exact He|split; [exact HG|reflexivity]]].
Qed.

Local Lemma owned_run_interval (e : Execution OwnedCfg OwnedAction unit) :
  owned_run e -> forall n len,
  clos_refl_trans _ owned_next (states e n) (states e (n + len)).
Proof.
  intros Hrun n len; induction len as [|len IH].
  - rewrite Nat.add_0_r; apply rt_refl.
  - eapply rt_trans; [exact IH|].
    replace (n + S len) with (S (n + len)) by lia.
    apply rt_step; exists (selected e (n + len)); apply Hrun.
Qed.

Local Lemma owned_run_silent_interval (e : Execution OwnedCfg OwnedAction unit) :
  owned_run e -> forall n len,
  (forall j, n <= j < n + len -> erase_action_label (selected e j) (joined_heap (states e (S j))) = None) ->
  clos_refl_trans _ silent_next (states e n) (states e (n + len)).
Proof.
  intros Hrun n len; induction len as [|len IH]; intro Hall.
  - rewrite Nat.add_0_r; apply rt_refl.
  - eapply rt_trans; [apply IH; intros; apply Hall; lia|].
    replace (n + S len) with (S (n + len)) by lia.
    apply rt_step; exists (selected e (n + len)); split; [apply Hrun|apply Hall; lia].
Qed.

Local Lemma owned_run_visible_frontier (e : Execution OwnedCfg OwnedAction unit) :
  owned_run e -> infinitely (fun n => erase_action_label (selected e n) (joined_heap (states e (S n))) <> None) ->
  forall n, exists m l, n <= m /\ erase_action_label (selected e m) (joined_heap (states e (S m))) = Some l /\
    clos_refl_trans _ silent_next (states e n) (states e m).
Proof.
  intros Hrun Hinf n.
  assert (dec : forall j,
    {erase_action_label (selected e j) (joined_heap (states e (S j))) <> None} +
    {~ erase_action_label (selected e j) (joined_heap (states e (S j))) <> None}).
  { intro j; destruct (erase_action_label (selected e j) (joined_heap (states e (S j))));
      [left; discriminate|right; tauto]. }
  destruct (Hinf n) as (bound & Hbound & Hvis).
  destruct (finite_first (fun j => erase_action_label (selected e j) (joined_heap (states e (S j))) <> None)
    dec n (S bound - n)) as [Hnone|(m & Hm & Hvisible & Hfirst)].
  - exfalso; apply (Hnone bound); [lia|exact Hvis].
  - destruct (erase_action_label (selected e m) (joined_heap (states e (S m)))) as [l|] eqn:HL; [|contradiction].
    exists m, l; split; [lia|split; [exact HL|]].
    replace m with (n + (m - n)) by lia.
    apply owned_run_silent_interval; [exact Hrun|].
    intros j Hj; destruct (erase_action_label (selected e j) (joined_heap (states e (S j)))) eqn:HJ; [|reflexivity].
    exfalso; apply (Hfirst j); [lia|rewrite HJ; discriminate].
Qed.

Theorem owned_heg_ticl c w (e : Execution OwnedCfg OwnedAction unit) :
  erasable c -> not_done w -> states e 0 = c -> owned_run e ->
  infinitely (fun n => erase_action_label (selected e n) (joined_heap (states e (S n))) <> None) ->
  <( {owned_interp c}, w |=L EG ⊤ )>.
Proof.
  intros He Hw H0 Hrun Hinf; subst c.
  assert (Herasable : forall n, erasable (states e n)).
  { intro n; apply (erasable_reach (states e 0) _ He).
    pose proof (owned_run_interval e Hrun 0 n) as Hr; cbn in Hr; exact Hr. }
  set (Z := fun (t : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))
    (z : World (writerE (CSLObs (nat * nat)))) =>
    not_done z /\ exists n, t ~ owned_interp (states e n)).
  ticl_normalize; rewrite unfold_entails_eg.
  apply (leq_gfp (egcF (entails (SSig * unit) false (CNow (fun _ => True)))) Z).
  - intros t z (Hz & n & HB).
    change ((True /\ not_done z) /\
      exists T z', |t, z| ↦ |T, z'| /\ Z T z').
    split; [now split|].
    destruct (owned_run_visible_frontier e Hrun Hinf n) as (m & l & Hm & HL & Hp).
    destruct (owned_interp_visible _ _ _ _ l (Herasable n) Hp (Hrun m) HL)
      as (T & HT & HTm).
    destruct (erased_visible_world _ _ l _ _ _ HL Hz HT) as (z' & HW & Hz').
    destruct (ktrans_semiproper _ _ _ _ _ (symmetry HB) HW) as (U & HU & HTU).
    exists U, z'; split; [exact HU|split; [exact Hz'|exists (S m)]].
    etransitivity; [symmetry; exact HTU|exact HTm].
  - split; [exact Hw|exists 0; reflexivity].
Qed.

Section ForkTiclBridges.
  Context (child : CProg unit) (k : unit -> CProg unit)
    (h h' : ManagedHeap) (ctx : Ctx.Ctx) (base : nat).
  Let c0 := init_owned child (k tt) h h' ctx base.
  Let rawFork := run_nd (CBind (CFork child) k) (h ⊎ h', (ctx, base)).

  Theorem fork_ticl {b : bool}
      (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) w :
    entails (SSig * unit) b p (owned_interp c0) w <->
    entails (SSig * unit) b p rawFork w.
  Proof.
    unfold c0, rawFork; rewrite owned_fork_runner; reflexivity.
  Qed.

  Theorem fork_haf_ret_ticl (Q : SSig * unit -> Prop) :
    admissible child (k tt) h h' ctx base ->
    Proper (owned_result_rel ==> iff) Q ->
    hAF owned_next (hDone (fun d => Q (joined_state d, tt))) c0 ->
    <( rawFork, Pure |=R AF ret {fun r _ => Q r} )>.
  Proof.
    intros Hadm HQ HA.
    pose proof (owned_haf_ret_ticl Q c0 Pure
      (admissible_erasable _ _ _ _ _ _ Hadm) (NotDonePure) HQ HA) as Hraw.
    exact (proj1 (fork_ticl _ Pure) Hraw).
  Qed.

  Theorem fork_haf_done_ticl (Q : SSig * unit -> Prop) :
    admissible child (k tt) h h' ctx base ->
    Proper (owned_result_rel ==> iff) Q ->
    hAF owned_next (hDone (fun d => Q (joined_state d, tt))) c0 ->
    auc (entails (SSig * unit) false (CNow (fun _ => True)))
      (fun _ wd => done_with (fun r _ => Q r) wd) rawFork Pure.
  Proof.
    intros Hadm HQ HA; apply af_ret_done; exact (fork_haf_ret_ticl Q Hadm HQ HA).
  Qed.

  Theorem fork_hef_ret_ticl (Q : SSig * unit -> Prop) :
    admissible child (k tt) h h' ctx base ->
    Proper (owned_result_rel ==> iff) Q ->
    hEF owned_next (hDone (fun d => Q (joined_state d, tt))) c0 ->
    <( rawFork, Pure |=R EF ret {fun r _ => Q r} )>.
  Proof.
    intros Hadm HQ HE.
    pose proof (owned_hef_ret_ticl Q c0 Pure
      (admissible_erasable _ _ _ _ _ _ Hadm) (NotDonePure) HQ HE) as Hraw.
    exact (proj1 (fork_ticl _ Pure) Hraw).
  Qed.

  Theorem fork_hef_done_ticl (Q : SSig * unit -> Prop) :
    admissible child (k tt) h h' ctx base ->
    Proper (owned_result_rel ==> iff) Q ->
    hEF owned_next (hDone (fun d => Q (joined_state d, tt))) c0 ->
    euc (entails (SSig * unit) false (CNow (fun _ => True)))
      (fun _ wd => done_with (fun r _ => Q r) wd) rawFork Pure.
  Proof.
    intros Hadm HQ HE; apply ef_ret_done; exact (fork_hef_ret_ticl Q Hadm HQ HE).
  Qed.

  Theorem fork_hag_ticl (I : hprop) (rank : OwnedCfg -> nat) :
    admissible child (k tt) h h' ctx base -> hproper I ->
    (forall d a d', I d -> owned_step d a d' ->
       erase_action_label a (joined_heap d') = None -> rank d' < rank d) ->
    hAG owned_next I c0 -> <( rawFork, Pure |=L AG ⊤ )>.
  Proof.
    intros Hadm HI Hrank HG; ticl_normalize.
    apply (proj1 (fork_ticl (b:=false) _ Pure)).
    exact (owned_hag_ticl I rank c0 Pure
      (admissible_erasable _ _ _ _ _ _ Hadm) NotDonePure HI Hrank HG).
  Qed.

  Theorem fork_heg_ticl (e : Execution OwnedCfg OwnedAction unit) :
    admissible child (k tt) h h' ctx base ->
    states e 0 = c0 -> owned_run e ->
    infinitely (fun n => erase_action_label (selected e n) (joined_heap (states e (S n))) <> None) ->
    <( rawFork, Pure |=L EG ⊤ )>.
  Proof.
    intros Hadm H0 Hrun Hinf; ticl_normalize.
    apply (proj1 (fork_ticl (b:=false) _ Pure)).
    exact (owned_heg_ticl c0 Pure e
      (admissible_erasable _ _ _ _ _ _ Hadm) NotDonePure H0 Hrun Hinf).
  Qed.
End ForkTiclBridges.
