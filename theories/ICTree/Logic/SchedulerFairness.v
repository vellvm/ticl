From Stdlib Require Import
  Fin
  Vector
  Program.Equality.
From Coinduction Require Import lattice.
From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.Interp.Core
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.CanStep
  ICTree.Logic.Trans
  ICTree.Trans
  Events.Core
  Logic.Core
  Logic.Kripke
  ICTree.Events.Yield
  ICTree.Interp.Yield.Mod
  ICTree.Interp.Yield.SBisim
  Utils.Vectors
  ICTree.Interp.Yield.Observed
  ICTree.SBisim.

Import ICtree ICTreeNotations TiclNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

(** Temporal consequences of the observed scheduler of
    [ICTree.Interp.Yield.Observed]: every live slot is offered after each
    scheduling point, conditional on [SchedulerProgress]. *)

Definition offer_live_slot {E : Type} `{Encode E}
    (n : nat) (i : LiveSlot n) : ticll (scheduler_observedE E) :=
  CNow (fun w => w = Obs (inl (ObsOffered (live_slot_ref i))) tt).


Section ObservedScheduler.
  Context {E : Type} `{Encode E}.

  Lemma offer_live_slot_now n (i : LiveSlot n)
      (t : observed_completed E) :
    <( {t}, {Obs (inl (ObsOffered (live_slot_ref i))) tt} |=
         {offer_live_slot n i} )>.
  Proof.
    unfold offer_live_slot.
    split; [reflexivity | constructor].
  Qed.

  Lemma ktrans_vis_raw_inv_no_eqdep {X} (e : scheduler_observedE E)
      (k : encode e -> ictree (scheduler_observedE E) X)
      (w : World (scheduler_observedE E)) t' w' :
    |Vis e k, w| ↦ |t', w'| ->
    exists v (target : ictree (scheduler_observedE E) X),
      w' = Obs e v /\ observe target = observe t' /\
      target ≅ k v /\ not_done w.
  Proof.
    intro Htr.
    cbn in Htr.
    refine (match Htr in ktrans_ ot w0 ot' w0' return
        match ot with
        | VisF e0 k0 =>
            exists v (target : ictree (scheduler_observedE E) X),
              w0' = Obs e0 v /\ observe target = ot' /\
              target ≅ k0 v /\ not_done w0
        | _ => True
        end with
      | KtransObs e0 v k0 target w0 Hnd Heq => _
      | _ => I
      end).
    exists v, target.
    split; [reflexivity | split; [reflexivity | split; assumption]].
  Qed.

  Lemma ktrans_scheduler_vis_inv_no_eqdep {X} (obs : schedulerObsE)
      (k : encode (inl obs : scheduler_observedE E) ->
        ictree (scheduler_observedE E) X)
      (w : World (scheduler_observedE E)) t' w' :
    |Vis (inl obs) k, w| ↦ |t', w'| ->
    exists target : ictree (scheduler_observedE E) X,
      w' = Obs (inl obs) tt /\ observe target = observe t' /\
      target ≅ k tt /\ not_done w.
  Proof.
    intro Htr.
    destruct (ktrans_vis_raw_inv_no_eqdep _ _ _ _ _ Htr) as
      [v [target [Hw [Ht [Heq Hnd]]]]].
    destruct v.
    exists target. split; [exact Hw | split; [exact Ht | split; assumption]].
  Qed.

  Lemma offered_in_scheduler_prefix_chain_implies_AF n
      (i : LiveSlot n) (u actual bridge : observed_completed E) w :
    observe bridge = observe actual ->
    SchedulerEquChain bridge u ->
    not_done w ->
    offered_in_scheduler_prefix n i u ->
    <( {actual}, w |= AF {offer_live_slot n i} )>.
  Proof.
    intros Hbridge Hchain Hnd Hprefix.
    revert actual bridge w Hbridge Hchain Hnd.
    induction Hprefix as [u k Hobs | u obs k Hobs _ IH];
      intros actual bridge w Hbridge Hchain Hnd.
    - destruct (scheduler_equ_chain_scheduler_vis_inv_no_eqdep
        (ObsOffered (live_slot_ref i)) k bridge u Hchain Hobs) as
        [k_actual [Hactual Hcont]].
      rewrite unfold_entailsL.
      apply StepA.
      split.
      + split; [exact I | exact Hnd].
      + split.
        * exists (k_actual tt),
            (Obs (inl (ObsOffered (live_slot_ref i))) tt).
          cbn. rewrite <- Hbridge, Hactual.
          constructor; [exact Hnd | apply observed_equ_refl_no_eqdep].
        * intros t' w' Htr.
          cbn in Htr.
          rewrite <- Hbridge, Hactual in Htr.
          destruct (ktrans_scheduler_vis_inv_no_eqdep
            (ObsOffered (live_slot_ref i)) k_actual w t' w' Htr) as
            [target [Hw' [Htarget [Heqtarget Hsource]]]].
          subst w'.
          apply MatchA.
          unfold offer_live_slot.
          split; [reflexivity | constructor].
    - destruct (scheduler_equ_chain_scheduler_vis_inv_no_eqdep
        obs k bridge u Hchain Hobs) as [k_actual [Hactual Hcont]].
      rewrite unfold_entailsL.
      apply StepA.
      split.
      + split; [exact I | exact Hnd].
      + split.
        * exists (k_actual tt), (Obs (inl obs) tt).
          cbn. rewrite <- Hbridge, Hactual.
          constructor; [exact Hnd | apply observed_equ_refl_no_eqdep].
        * intros t' w' Htr.
          cbn in Htr.
          rewrite <- Hbridge, Hactual in Htr.
          destruct (ktrans_scheduler_vis_inv_no_eqdep obs
            k_actual w t' w' Htr) as
            [target [Hw' [Htarget [Heqtarget Hsource]]]].
          subst w'.
          specialize (IH t' target (Obs (inl obs) tt) Htarget
            (scheduler_equ_chain_cons target (k_actual tt) (k tt)
              Heqtarget Hcont) (NotDoneObs (inl obs) tt)).
          rewrite unfold_entailsL in IH.
          exact IH.
  Qed.

  Theorem offered_in_scheduler_prefix_implies_AF n
      (i : LiveSlot n) (t : observed_completed E) w :
    not_done w ->
    offered_in_scheduler_prefix n i t ->
    <( {t}, w |= AF {offer_live_slot n i} )>.
  Proof.
    intros Hnd Hprefix.
    eapply offered_in_scheduler_prefix_chain_implies_AF.
    - reflexivity.
    - constructor.
    - exact Hnd.
    - exact Hprefix.
  Qed.

  Theorem show_no_focus_offers_every_live_slot n
      (v : pool E (S n)) (i : LiveSlot (S n)) :
    <( {schedule_with_offers (S n) v None}, Pure |=
         AF {offer_live_slot (S n) i} )>.
  Proof.
    apply offered_in_scheduler_prefix_implies_AF.
    - constructor.
    - apply show_no_focus_offers_every_live_slot_prefix.
  Qed.

  Theorem no_focus_offers_every_live_slot n
      (v : pool E (S n)) (i : LiveSlot (S n)) :
    <( {schedule_with_offers (S n) v None}, Pure |=
         AF {offer_live_slot (S n) i} )>.
  Proof.
    apply show_no_focus_offers_every_live_slot.
  Qed.

  Definition scheduling_point_offer_obligation
      (t : observed_completed E) (w : World (scheduler_observedE E))
      : Prop :=
    forall n,
      w = Obs (inl (ObsSchedulingPoint (S n))) tt ->
      forall i : LiveSlot (S n),
        <( {t}, w |= AF {offer_live_slot (S n) i} )>.

  Local Definition non_scheduling_point_world
      (w : World (scheduler_observedE E)) : Prop :=
    forall n,
      w = Obs (inl (ObsSchedulingPoint (S n))) tt -> False.

  Local Lemma pure_non_scheduling_point :
    non_scheduling_point_world Pure.
  Proof. intros n Hcontra. discriminate Hcontra. Qed.

  Local Lemma obs_offered_non_scheduling_point ref :
    non_scheduling_point_world
      (Obs (inl (ObsOffered ref) : scheduler_observedE E) tt).
  Proof. intros n Hcontra. discriminate Hcontra. Qed.

  Local Lemma obs_non_scheduler_non_scheduling_point
      (event : yieldE + (spawnE + E))
      (value : encode (inr event : scheduler_observedE E)) :
    non_scheduling_point_world (Obs (inr event) value).
  Proof. intros n Hcontra. discriminate Hcontra. Qed.

  Private Inductive SchedulerOfferCanonical
      : observed_completed E -> World (scheduler_observedE E) -> Prop :=
  | scheduler_offer_canonical_schedule : forall n
      (v : pool E n) focus w,
      non_scheduling_point_world w ->
      SchedulerOfferCanonical (schedule_with_offers n v focus) w
  | scheduler_offer_canonical_prefix_at_point : forall n
      (v : pool E (S n)),
      SchedulerOfferCanonical
        (schedule_with_offers_offer_prefix (S n) (S n)
          (fun i : LiveSlot (S n) => i) v)
        (Obs (inl (ObsSchedulingPoint (S n))) tt)
  | scheduler_offer_canonical_prefix_elsewhere : forall m r
      (embed : LiveSlot r -> LiveSlot m) (v : pool E m) w,
      non_scheduling_point_world w ->
      SchedulerOfferCanonical
        (schedule_with_offers_offer_prefix m r embed v) w
  | scheduler_offer_canonical_choice : forall n
      (v : pool E (S n)) w,
      non_scheduling_point_world w ->
      SchedulerOfferCanonical
        (Br n (fun i : fin' n =>
          schedule_with_offers (S n) v (Some i))) w
  | scheduler_offer_canonical_done : forall t (x : unit),
      SchedulerOfferCanonical t (Done x)
  | scheduler_offer_canonical_finish : forall t
      (event : scheduler_observedE E) (value : encode event) (x : unit),
      SchedulerOfferCanonical t (Finish event value x).

  Local Definition SchedulerOfferShape
      (t : observed_completed E) (w : World (scheduler_observedE E))
      : Prop :=
    exists u : observed_completed E, t ≅ u /\ SchedulerOfferCanonical u w.

  Local Lemma scheduler_offer_shape_canonical t w :
    SchedulerOfferCanonical t w -> SchedulerOfferShape t w.
  Proof.
    intro Hcanonical.
    exists t. split; [apply observed_equ_refl_no_eqdep | exact Hcanonical].
  Qed.

  Local Lemma scheduler_offer_shape_equ t u w :
    t ≅ u -> SchedulerOfferShape u w -> SchedulerOfferShape t w.
  Proof.
    intros Htu [v [Huv Hcanonical]].
    exists v. split.
    - transitivity u; assumption.
    - exact Hcanonical.
  Qed.


  Local Lemma scheduler_offer_shape_schedule n
      (v : pool E n) focus w :
    non_scheduling_point_world w ->
    SchedulerOfferShape (schedule_with_offers n v focus) w.
  Proof.
    intro Hworld.
    apply scheduler_offer_shape_canonical.
    now constructor.
  Qed.

  Local Lemma scheduler_offer_shape_prefix_at_point n
      (v : pool E (S n)) :
    SchedulerOfferShape
      (schedule_with_offers_offer_prefix (S n) (S n)
        (fun i : LiveSlot (S n) => i) v)
      (Obs (inl (ObsSchedulingPoint (S n))) tt).
  Proof.
    apply scheduler_offer_shape_canonical.
    constructor.
  Qed.

  Local Lemma scheduler_offer_shape_prefix_elsewhere m r
      (embed : LiveSlot r -> LiveSlot m) (v : pool E m) w :
    non_scheduling_point_world w ->
    SchedulerOfferShape
      (schedule_with_offers_offer_prefix m r embed v) w.
  Proof.
    intro Hworld.
    apply scheduler_offer_shape_canonical.
    now constructor.
  Qed.

  Local Lemma scheduler_offer_shape_choice n
      (v : pool E (S n)) w :
    non_scheduling_point_world w ->
    SchedulerOfferShape
      (Br n (fun i : fin' n =>
        schedule_with_offers (S n) v (Some i))) w.
  Proof.
    intro Hworld.
    apply scheduler_offer_shape_canonical.
    now constructor.
  Qed.

  Local Lemma scheduler_offer_shape_done t (x : unit) :
    SchedulerOfferShape t (Done x).
  Proof.
    apply scheduler_offer_shape_canonical.
    constructor.
  Qed.

  Local Lemma scheduler_offer_shape_finish t
      (event : scheduler_observedE E) (value : encode event) (x : unit) :
    SchedulerOfferShape t (Finish event value x).
  Proof.
    apply scheduler_offer_shape_canonical.
    constructor.
  Qed.

  Local Lemma scheduler_offer_canonical_obligation t w :
    SchedulerOfferCanonical t w -> scheduling_point_offer_obligation t w.
  Proof.
    intro Hcanonical.
    destruct Hcanonical as
      [n v focus w Hworld | n v | m r embed v w Hworld |
       n v w Hworld | t x | t event value x].
    - intros k Hsched i.
      exfalso. exact (Hworld k Hsched).
    - intros k Hsched i.
      inversion Hsched; subst.
      apply offered_in_scheduler_prefix_implies_AF.
      + constructor.
      + apply (schedule_with_offers_offer_prefix_offers (S k) (S k)
          (fun j : LiveSlot (S k) => j) v i).
    - intros k Hsched i.
      exfalso. exact (Hworld k Hsched).
    - intros k Hsched i.
      exfalso. exact (Hworld k Hsched).
    - intros k Hsched i. discriminate Hsched.
    - intros k Hsched i. discriminate Hsched.
  Qed.

  Local Lemma scheduler_offer_shape_obligation t w :
    SchedulerOfferShape t w -> scheduling_point_offer_obligation t w.
  Proof.
    intros [u [Htu Hcanonical]] k Hsched i.
    rewrite Htu.
    eapply scheduler_offer_canonical_obligation; eauto.
  Qed.

  Local Lemma scheduler_offer_shape_ret_step
      (w : World (scheduler_observedE E)) t' w' :
    |Ret tt, w| ↦ |t', w'| -> SchedulerOfferShape t' w'.
  Proof.
    intro Htr.
    destruct w as [| event value | x | event value x].
    - apply ktrans_done in Htr as [-> _].
      apply scheduler_offer_shape_done.
    - apply ktrans_finish in Htr as [-> _].
      apply scheduler_offer_shape_finish.
    - apply ktrans_not_done in Htr. inversion Htr.
    - apply ktrans_not_done in Htr. inversion Htr.
  Qed.

  Local Lemma scheduler_offer_canonical_step t w t' w' :
    SchedulerOfferCanonical t w ->
    |t, w| ↦ |t', w'| ->
    SchedulerOfferShape t' w'.
  Proof.
    intros Hcanonical Htr.
    revert t w t' w' Hcanonical Htr.
    fix IH 6.
    intros t w t' w' Hcanonical Htr.
    destruct Hcanonical as
      [n v focus w Hworld | n v | m r embed v w Hworld |
       n v w Hworld | t x | t event value x].
    - destruct focus as [slot |].
      + dependent destruction slot.
        * set (focused_slot := (Fin.F1 : Fin.t (S n))).
          destruct (observe (v $ focused_slot)) eqn:Hthread;
          fold focused_slot in Htr.
          -- destruct x.
             cbn in Htr.
             rewrite (schedule_with_offers_focused_ret
               n v focused_slot Hthread) in Htr.
             dependent destruction Htr.
             eapply scheduler_offer_shape_equ.
             ++ apply observe_eq_equ.
                match goal with
                | Hobs : observe ?mid = observe t' |- _ =>
                    symmetry; exact Hobs
                end.
             ++ eapply IH.
                ** apply scheduler_offer_canonical_schedule.
                   exact Hworld.
                ** exact Htr.
          -- cbn in Htr.
             rewrite (schedule_with_offers_focused_br
               n v focused_slot n0 k Hthread) in Htr.
             apply ktrans_br in Htr as [choice [Htarget [-> _]]].
             eapply scheduler_offer_shape_equ.
             ++ exact Htarget.
             ++ apply scheduler_offer_shape_schedule. exact Hworld.
          -- cbn in Htr.
             rewrite (schedule_with_offers_focused_guard
               n v focused_slot t Hthread) in Htr.
             dependent destruction Htr.
             eapply scheduler_offer_shape_equ.
             ++ apply observe_eq_equ.
                match goal with
                | Hobs : observe ?mid = observe t' |- _ =>
                    symmetry; exact Hobs
                end.
             ++ eapply IH.
                ** apply scheduler_offer_canonical_schedule.
                   exact Hworld.
                ** exact Htr.
          -- destruct e as [yield_event | [spawn_event | user_event]].
             ++ destruct yield_event.
                cbn in Htr.
                rewrite (schedule_with_offers_focused_yield
                  n v focused_slot k Hthread) in Htr.
                dependent destruction Htr.
                eapply scheduler_offer_shape_equ.
                ** apply observe_eq_equ.
                   match goal with
                   | Hobs : observe ?mid = observe t' |- _ =>
                       symmetry; exact Hobs
                   end.
                ** eapply IH.
                   --- apply scheduler_offer_canonical_schedule.
                       exact Hworld.
                   --- exact Htr.
             ++ destruct spawn_event.
                cbn in Htr.
                rewrite (schedule_with_offers_focused_fork
                  n v focused_slot k Hthread) in Htr.
                apply ktrans_vis in Htr as [[] [-> [Htarget _]]].
                eapply scheduler_offer_shape_equ.
                ** symmetry. exact Htarget.
                ** apply scheduler_offer_shape_schedule.
                   apply obs_non_scheduler_non_scheduling_point.
             ++ cbn in Htr.
                rewrite (schedule_with_offers_focused_user_event
                  n v focused_slot user_event k Hthread) in Htr.
                apply ktrans_vis in Htr as [value [-> [Htarget _]]].
                eapply scheduler_offer_shape_equ.
                ** symmetry. exact Htarget.
                ** apply scheduler_offer_shape_schedule.
                   apply obs_non_scheduler_non_scheduling_point.
        * set (focused_slot := Fin.FS slot).
          destruct (observe (v $ focused_slot)) eqn:Hthread;
          fold focused_slot in Htr.
          -- destruct x.
             cbn in Htr.
             rewrite (schedule_with_offers_focused_ret
               n v focused_slot Hthread) in Htr.
             dependent destruction Htr.
             eapply scheduler_offer_shape_equ.
             ++ apply observe_eq_equ.
                match goal with
                | Hobs : observe ?mid = observe t' |- _ =>
                    symmetry; exact Hobs
                end.
             ++ eapply IH.
                ** apply scheduler_offer_canonical_schedule.
                   exact Hworld.
                ** exact Htr.
          -- cbn in Htr.
             rewrite (schedule_with_offers_focused_br
               n v focused_slot n0 k Hthread) in Htr.
             apply ktrans_br in Htr as [choice [Htarget [-> _]]].
             eapply scheduler_offer_shape_equ.
             ++ exact Htarget.
             ++ apply scheduler_offer_shape_schedule. exact Hworld.
          -- cbn in Htr.
             rewrite (schedule_with_offers_focused_guard
               n v focused_slot t Hthread) in Htr.
             dependent destruction Htr.
             eapply scheduler_offer_shape_equ.
             ++ apply observe_eq_equ.
                match goal with
                | Hobs : observe ?mid = observe t' |- _ =>
                    symmetry; exact Hobs
                end.
             ++ eapply IH.
                ** apply scheduler_offer_canonical_schedule.
                   exact Hworld.
                ** exact Htr.
          -- destruct e as [yield_event | [spawn_event | user_event]].
             ++ destruct yield_event.
                cbn in Htr.
                rewrite (schedule_with_offers_focused_yield
                  n v focused_slot k Hthread) in Htr.
                dependent destruction Htr.
                eapply scheduler_offer_shape_equ.
                ** apply observe_eq_equ.
                   match goal with
                   | Hobs : observe ?mid = observe t' |- _ =>
                       symmetry; exact Hobs
                   end.
                ** eapply IH.
                   --- apply scheduler_offer_canonical_schedule.
                       exact Hworld.
                   --- exact Htr.
             ++ destruct spawn_event.
                cbn in Htr.
                rewrite (schedule_with_offers_focused_fork
                  n v focused_slot k Hthread) in Htr.
                apply ktrans_vis in Htr as [[] [-> [Htarget _]]].
                eapply scheduler_offer_shape_equ.
                ** symmetry. exact Htarget.
                ** apply scheduler_offer_shape_schedule.
                   apply obs_non_scheduler_non_scheduling_point.
             ++ cbn in Htr.
                rewrite (schedule_with_offers_focused_user_event
                  n v focused_slot user_event k Hthread) in Htr.
                apply ktrans_vis in Htr as [value [-> [Htarget _]]].
                eapply scheduler_offer_shape_equ.
                ** symmetry. exact Htarget.
                ** apply scheduler_offer_shape_schedule.
                   apply obs_non_scheduler_non_scheduling_point.
      + destruct n as [| n'].
        * cbn in Htr.
          apply scheduler_offer_shape_ret_step with (w := w).
          exact Htr.
        * cbn in Htr.
          apply ktrans_vis in Htr as [[] [-> [Htarget _]]].
          eapply scheduler_offer_shape_equ.
          -- symmetry. exact Htarget.
          -- apply scheduler_offer_shape_prefix_at_point.
    - cbn in Htr.
      apply ktrans_vis in Htr as [[] [-> [Htarget _]]].
      eapply scheduler_offer_shape_equ.
      + symmetry. exact Htarget.
      + apply scheduler_offer_shape_prefix_elsewhere.
        apply obs_offered_non_scheduling_point.
    - destruct r as [| r'].
      + destruct m as [| m'].
        * cbn in Htr.
          apply scheduler_offer_shape_ret_step with (w := w).
          exact Htr.
        * cbn in Htr.
          apply ktrans_vis in Htr as [[] [-> [Htarget _]]].
          eapply scheduler_offer_shape_equ.
          -- symmetry. exact Htarget.
          -- apply scheduler_offer_shape_choice.
             apply obs_non_scheduler_non_scheduling_point.
      + cbn in Htr.
        apply ktrans_vis in Htr as [[] [-> [Htarget _]]].
        eapply scheduler_offer_shape_equ.
        * symmetry. exact Htarget.
        * apply scheduler_offer_shape_prefix_elsewhere.
          apply obs_offered_non_scheduling_point.
    - cbn in Htr.
      apply ktrans_br in Htr as [choice [Htarget [-> _]]].
      eapply scheduler_offer_shape_equ.
      + exact Htarget.
      + apply scheduler_offer_shape_schedule. exact Hworld.
    - apply ktrans_not_done in Htr. inversion Htr.
    - apply ktrans_not_done in Htr. inversion Htr.
  Qed.

  Local Lemma scheduler_offer_shape_step t w t' w' :
    SchedulerOfferShape t w ->
    |t, w| ↦ |t', w'| ->
    SchedulerOfferShape t' w'.
  Proof.
    intros [u [Htu Hcanonical]] Htr.
    rewrite Htu in Htr.
    eapply scheduler_offer_canonical_step; eauto.
  Qed.

  CoInductive SchedulerProgress
      : observed_completed E -> World (scheduler_observedE E) -> Prop :=
  | scheduler_progress_intro : forall t w,
      can_step t w ->
      (forall t' w',
        |t, w| ↦ |t', w'| -> SchedulerProgress t' w') ->
      SchedulerProgress t w.

  Lemma scheduler_progress_shape_implies_AG t w :
    SchedulerProgress t w ->
    SchedulerOfferShape t w ->
    agc scheduling_point_offer_obligation t w.
  Proof.
    intros Hprogress0 Hshape0.
    pose proof (leq_gfp (agcF scheduling_point_offer_obligation)
      (fun t w => SchedulerProgress t w /\ SchedulerOfferShape t w))
      as Hcoind.
    apply Hcoind.
    - clear t w Hprogress0 Hshape0.
      intros t w [Hprogress Hshape].
      destruct Hprogress as [t w Hstep Hnext].
      split.
      + apply scheduler_offer_shape_obligation. exact Hshape.
      + split.
        * exact Hstep.
        * intros t' w' Htr.
          split.
          -- apply Hnext. exact Htr.
          -- eapply scheduler_offer_shape_step; eauto.
    - split; assumption.
  Qed.

  Theorem every_live_slot_is_eventually_offered_at_scheduling_points
      n (v : pool E n) focus :
    SchedulerProgress (schedule_with_offers n v focus) Pure ->
    agc scheduling_point_offer_obligation
      (schedule_with_offers n v focus) Pure.
  Proof.
    intro Hprogress.
    eapply scheduler_progress_shape_implies_AG.
    - exact Hprogress.
    - apply scheduler_offer_shape_schedule.
      apply pure_non_scheduling_point.
  Qed.

  Theorem show_every_live_slot_is_eventually_offered_at_scheduling_points
      n (v : pool E n) focus :
    SchedulerProgress (schedule_with_offers n v focus) Pure ->
    agc scheduling_point_offer_obligation
      (schedule_with_offers n v focus) Pure.
  Proof.
    apply every_live_slot_is_eventually_offered_at_scheduling_points.
  Qed.
End ObservedScheduler.
