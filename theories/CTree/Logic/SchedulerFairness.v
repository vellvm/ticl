From Stdlib Require Import
  Fin
  Vector
  Program.Equality.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.CanStep
  CTree.Logic.Trans
  Logic.Core
  Logic.Kripke
  CTree.Events.Yield
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  Utils.Vectors
  CTree.Interp.Yield.Observed.

Import CTreeNotations TiclNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

Generalizable All Variables.

(** Temporal consequences of the observed scheduler of
    [CTree.Interp.Yield.Observed]: every live slot is offered after each
    scheduling point, conditional on [SchedulerProgress]. *)

Definition offer_live_slot {E : Type -> Type}
    (n : nat) (i : LiveSlot n) : ticll (scheduler_observedE E) :=
  CNow (fun w => w = Obs (inl1 (ObsOffered (live_slot_ref i)) : scheduler_observedE E unit) tt).

Section ObservedScheduler.
  Context {E B : Type -> Type} `{Bn -< B}.

  Local Notation SchedObs o := (inl1 o : scheduler_observedE E unit).

  Lemma offer_live_slot_now n (i : LiveSlot n)
      (t : observed_completed E B) :
    <( {t}, {Obs (SchedObs (ObsOffered (live_slot_ref i))) tt} |=
         {offer_live_slot n i} )>.
  Proof.
    unfold offer_live_slot.
    split; [reflexivity | constructor].
  Qed.

  Lemma ktrans_vis_raw_inv_no_eqdep {X Y} (e : scheduler_observedE E Y)
      (k : Y -> ctree (scheduler_observedE E) B X)
      (w : World (scheduler_observedE E)) t' w' :
    |Vis e k, w| ↦ |t', w'| ->
    exists v, w' = Obs e v /\ k v ≅ t' /\ not_done w.
  Proof. apply ktrans_vis. Qed.

  Lemma ktrans_scheduler_vis_inv_no_eqdep {X} (obs : schedulerObsE unit)
      (k : unit -> ctree (scheduler_observedE E) B X)
      (w : World (scheduler_observedE E)) t' w' :
    |Vis (SchedObs obs) k, w| ↦ |t', w'| ->
    w' = Obs (SchedObs obs) tt /\ k tt ≅ t' /\ not_done w.
  Proof.
    intro Htr.
    apply ktrans_vis in Htr as ([] & -> & Heq & Hnd).
    auto.
  Qed.

  Lemma offered_in_scheduler_prefix_chain_implies_AF n
      (i : LiveSlot n) (u actual bridge : observed_completed E B) w :
    observe bridge = observe actual ->
    SchedulerEquChain bridge u ->
    not_done w ->
    offered_in_scheduler_prefix n i u ->
    <( {actual}, w |= AF {offer_live_slot n i} )>.
  Proof.
    intros Hbridge Hchain Hnd Hprefix.
    revert actual bridge w Hbridge Hchain Hnd.
    induction Hprefix as [u k Hobs | u obs k Hobs _ IH];
      intros actual bridge w Hbridge Hchain Hnd;
      destruct (scheduler_equ_chain_scheduler_vis_inv_no_eqdep
        _ k bridge u Hchain Hobs) as [k_actual [Hactual Hcont]];
      rewrite (ctree_eta actual), <- Hbridge, Hactual;
      apply (afl_vis _ _ tt); right; split; [exact Hnd | intros [] | exact Hnd | intros []].
    - rewrite unfold_entailsL.
      apply MatchA.
      apply offer_live_slot_now.
    - apply (IH (k_actual tt) (k_actual tt) _ eq_refl Hcont).
      constructor.
  Qed.

  Theorem offered_in_scheduler_prefix_implies_AF n
      (i : LiveSlot n) (t : observed_completed E B) w :
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
      (v : pool E B (S n)) (i : LiveSlot (S n)) :
    <( {schedule_with_offers (S n) v None}, Pure |=
         AF {offer_live_slot (S n) i} )>.
  Proof.
    apply offered_in_scheduler_prefix_implies_AF.
    - constructor.
    - apply show_no_focus_offers_every_live_slot_prefix.
  Qed.

  Theorem no_focus_offers_every_live_slot n
      (v : pool E B (S n)) (i : LiveSlot (S n)) :
    <( {schedule_with_offers (S n) v None}, Pure |=
         AF {offer_live_slot (S n) i} )>.
  Proof.
    apply show_no_focus_offers_every_live_slot.
  Qed.

  Definition scheduling_point_offer_obligation
      (t : observed_completed E B) (w : World (scheduler_observedE E))
      : Prop :=
    forall n,
      w = Obs (SchedObs (ObsSchedulingPoint (S n))) tt ->
      forall i : LiveSlot (S n),
        <( {t}, w |= AF {offer_live_slot (S n) i} )>.

  (** Worlds that are not a nonempty scheduling point. *)
  Local Definition non_scheduling_point_world
      (w : World (scheduler_observedE E)) : Prop :=
    match w with
    | Obs (inl1 (ObsSchedulingPoint (S _))) _ => False
    | _ => True
    end.

  Local Lemma pure_non_scheduling_point :
    non_scheduling_point_world Pure.
  Proof. exact I. Qed.

  Local Lemma obs_offered_non_scheduling_point ref :
    non_scheduling_point_world (Obs (SchedObs (ObsOffered ref)) tt).
  Proof. exact I. Qed.

  Local Lemma obs_non_scheduler_non_scheduling_point {Y}
      (event : (yieldE +' (spawnE +' E)) Y) (value : Y) :
    non_scheduling_point_world (Obs (inr1 event : scheduler_observedE E Y) value).
  Proof. exact I. Qed.

  Private Inductive SchedulerOfferCanonical
      : observed_completed E B -> World (scheduler_observedE E) -> Prop :=
  | scheduler_offer_canonical_schedule : forall n
      (v : pool E B n) focus w,
      non_scheduling_point_world w ->
      SchedulerOfferCanonical (schedule_with_offers n v focus) w
  | scheduler_offer_canonical_prefix_at_point : forall n
      (v : pool E B (S n)),
      SchedulerOfferCanonical
        (schedule_with_offers_offer_prefix (S n) (S n)
          (fun i : LiveSlot (S n) => i) v)
        (Obs (SchedObs (ObsSchedulingPoint (S n))) tt)
  | scheduler_offer_canonical_prefix_elsewhere : forall m r
      (embed : LiveSlot r -> LiveSlot m) (v : pool E B m) w,
      non_scheduling_point_world w ->
      SchedulerOfferCanonical
        (schedule_with_offers_offer_prefix m r embed v) w
  | scheduler_offer_canonical_choice : forall n
      (v : pool E B (S n)) w,
      non_scheduling_point_world w ->
      SchedulerOfferCanonical
        (brS (branchn (S n)) (fun i =>
          schedule_with_offers (S n) v (Some i))) w
  | scheduler_offer_canonical_picked : forall n
      (v : pool E B (S n)) (i : Fin.t (S n)) w,
      non_scheduling_point_world w ->
      SchedulerOfferCanonical
        (Step (schedule_with_offers (S n) v (Some i))) w
  | scheduler_offer_canonical_done : forall t (x : unit),
      SchedulerOfferCanonical t (Done x)
  | scheduler_offer_canonical_finish : forall t {Y}
      (event : scheduler_observedE E Y) (value : Y) (x : unit),
      SchedulerOfferCanonical t (Finish event value x).

  Local Definition SchedulerOfferShape
      (t : observed_completed E B) (w : World (scheduler_observedE E))
      : Prop :=
    exists u : observed_completed E B, t ≅ u /\ SchedulerOfferCanonical u w.

  Local Lemma scheduler_offer_shape_canonical t w :
    SchedulerOfferCanonical t w -> SchedulerOfferShape t w.
  Proof.
    intro Hcanonical.
    exists t. split; [reflexivity | exact Hcanonical].
  Qed.

  Local Lemma scheduler_offer_shape_equ t u w :
    t ≅ u -> SchedulerOfferShape u w -> SchedulerOfferShape t w.
  Proof.
    intros Htu [v [Huv Hcanonical]].
    exists v. split.
    - transitivity u; assumption.
    - exact Hcanonical.
  Qed.

  Local Lemma scheduler_offer_shape_observe t u w :
    observe u = observe t -> SchedulerOfferShape u w -> SchedulerOfferShape t w.
  Proof.
    intro Hobs; apply scheduler_offer_shape_equ.
    apply observe_eq_equ; symmetry; exact Hobs.
  Qed.

  Local Lemma scheduler_offer_shape_schedule n
      (v : pool E B n) focus w :
    non_scheduling_point_world w ->
    SchedulerOfferShape (schedule_with_offers n v focus) w.
  Proof.
    intro Hworld.
    apply scheduler_offer_shape_canonical.
    now constructor.
  Qed.

  Local Lemma scheduler_offer_shape_prefix_at_point n
      (v : pool E B (S n)) :
    SchedulerOfferShape
      (schedule_with_offers_offer_prefix (S n) (S n)
        (fun i : LiveSlot (S n) => i) v)
      (Obs (SchedObs (ObsSchedulingPoint (S n))) tt).
  Proof.
    apply scheduler_offer_shape_canonical.
    constructor.
  Qed.

  Local Lemma scheduler_offer_shape_prefix_elsewhere m r
      (embed : LiveSlot r -> LiveSlot m) (v : pool E B m) w :
    non_scheduling_point_world w ->
    SchedulerOfferShape
      (schedule_with_offers_offer_prefix m r embed v) w.
  Proof.
    intro Hworld.
    apply scheduler_offer_shape_canonical.
    now constructor.
  Qed.

  Local Lemma scheduler_offer_shape_choice n
      (v : pool E B (S n)) w :
    non_scheduling_point_world w ->
    SchedulerOfferShape
      (brS (branchn (S n)) (fun i =>
        schedule_with_offers (S n) v (Some i))) w.
  Proof.
    intro Hworld.
    apply scheduler_offer_shape_canonical.
    now constructor.
  Qed.

  Local Lemma scheduler_offer_shape_picked n
      (v : pool E B (S n)) (i : Fin.t (S n)) w :
    non_scheduling_point_world w ->
    SchedulerOfferShape (Step (schedule_with_offers (S n) v (Some i))) w.
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

  Local Lemma scheduler_offer_shape_finish t {Y}
      (event : scheduler_observedE E Y) (value : Y) (x : unit) :
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
       n v w Hworld | n v j w Hworld | t x | t Y event value x];
      intros k Hsched i.
    - exfalso. subst w. exact Hworld.
    - inversion Hsched; subst.
      apply offered_in_scheduler_prefix_implies_AF.
      + constructor.
      + apply (schedule_with_offers_offer_prefix_offers (S k) (S k)
          (fun j : LiveSlot (S k) => j) v i).
    - exfalso. subst w. exact Hworld.
    - exfalso. subst w. exact Hworld.
    - exfalso. subst w. exact Hworld.
    - discriminate Hsched.
    - discriminate Hsched.
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
    |Ret tt : observed_completed E B, w| ↦ |t', w'| -> SchedulerOfferShape t' w'.
  Proof.
    intro Htr.
    destruct w as [| Y event value | x | Y event value x].
    - apply ktrans_done in Htr as [-> _].
      apply scheduler_offer_shape_done.
    - apply ktrans_finish in Htr as [-> _].
      apply scheduler_offer_shape_finish.
    - apply ktrans_not_done in Htr. inversion Htr.
    - apply ktrans_not_done in Htr. inversion Htr.
  Qed.

  (** The world side of a labelled transition, as [ktrans] fixes it. *)
  Local Definition label_world (l : @label (scheduler_observedE E))
      (w w' : World (scheduler_observedE E)) : Prop :=
    match l with
    | τ => not_done w /\ w' = w
    | obs e x => not_done w /\ w' = Obs e x
    | val _ => is_done unit w'
    end.

  Local Lemma ktrans_label_world (t t' : observed_completed E B) w w' :
    |t, w| ↦ |t', w'| -> exists l, trans l t t' /\ label_world l w w'.
  Proof.
    intro Htr; cbn in Htr.
    apply ktrans_trans in Htr.
    destruct Htr as (l & TR & Hl).
    exists l; split; [exact TR |].
    destruct Hl as [(-> & Hnd & ->) | [(Y & e & x & -> & Hnd & ->) |
                 [(x & -> & -> & _ & ->) | (Y & e & v & x & -> & -> & _ & ->)]]];
      cbn; auto; constructor.
  Qed.

  Local Lemma observe_brS_schedule n (v : pool E B (S n)) :
    observe (brS (branchn (S n)) (fun i => schedule_with_offers (S n) v (Some i)))
    = BrF (subevent _ (branchn (S n)))
        (fun i => Step (schedule_with_offers (S n) v (Some i))).
  Proof. reflexivity. Qed.

  Local Lemma observe_prefix_zero_empty
      (embed : LiveSlot 0 -> LiveSlot 0) (v : pool E B 0) :
    observe (schedule_with_offers_offer_prefix 0 0 embed v) = RetF tt.
  Proof. reflexivity. Qed.

  Local Lemma observe_step_schedule n (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (Step (schedule_with_offers (S n) v (Some i)))
    = StepF (schedule_with_offers (S n) v (Some i)).
  Proof. reflexivity. Qed.

  (** Dispatch the head of the focused thread against the scheduler head
      ([Hos : <head> = observe (schedule_with_offers (S n) v (Some i))]). *)
  Local Ltac focused_heads v i Hos Hvi :=
    destruct (observe (v $ i)) as [[] | | t0 | g | Y0 e0 k0 | Y0 c0 k0] eqn:Hvi;
    [ rewrite (schedule_with_offers_focused_ret _ v i Hvi) in Hos
    | rewrite (schedule_with_offers_focused_stuck _ v i Hvi) in Hos
    | rewrite (schedule_with_offers_focused_step _ v i _ Hvi) in Hos
    | rewrite (schedule_with_offers_focused_guard _ v i _ Hvi) in Hos
    | destruct e0 as [y | [f | usr]];
      [ dependent destruction y; rewrite (schedule_with_offers_focused_yield _ v i _ Hvi) in Hos
      | dependent destruction f; rewrite (schedule_with_offers_focused_fork _ v i _ Hvi) in Hos
      | rewrite (schedule_with_offers_focused_user_event _ v i usr _ Hvi) in Hos ]
    | rewrite (schedule_with_offers_focused_br _ v i c0 k0 Hvi) in Hos ];
    try discriminate Hos.

  (** From a done world nothing steps; a [val] transition lands in a done world. *)
  Local Lemma label_world_is_done l w w' (t' : observed_completed E B) :
    is_done unit w -> label_world l w w' -> SchedulerOfferShape t' w'.
  Proof.
    intros Hd Hlw.
    destruct l; cbn in Hlw.
    - destruct Hlw as [Hnd _]; destruct Hd; inversion Hnd.
    - destruct Hlw as [Hnd _]; destruct Hd; inversion Hnd.
    - destruct Hlw; [apply scheduler_offer_shape_done | apply scheduler_offer_shape_finish].
  Qed.

  (** Unfold every canonical head into [Hos]; impossible heads are discharged. *)
  Local Ltac canonical_heads Hcan Hos Hlw :=
    destruct Hcan as
      [n v [i |] w Hworld | n v | m [| r] embed v w Hworld |
       n v w Hworld | n v i w Hworld | td xd | td Yd ed vd xd];
    [ destruct n as [| n]; [inversion i |]
    | destruct n as [| n];
      [ rewrite (schedule_with_offers_empty_none v) in Hos
      | rewrite (schedule_with_offers_no_focus_nonempty n v) in Hos ]
    | rewrite (schedule_with_offers_offer_prefix_succ _ _ _ v) in Hos
    | destruct m as [| m];
      [ rewrite (observe_prefix_zero_empty embed v) in Hos
      | rewrite (schedule_with_offers_offer_prefix_zero_nonempty _ embed v) in Hos ]
    | rewrite (schedule_with_offers_offer_prefix_succ _ _ _ v) in Hos
    | rewrite (observe_brS_schedule n v) in Hos
    | rewrite (observe_step_schedule n v i) in Hos
    | exact (label_world_is_done _ _ _ _ (DoneDone _ xd) Hlw)
    | exact (label_world_is_done _ _ _ _ (DoneFinish _ ed vd xd) Hlw)
    ]; try discriminate Hos.

  Local Lemma scheduler_offer_canonical_trans :
    forall l os ot', trans_ l os ot' ->
    forall (t t' : observed_completed E B) w w',
      os = observe t -> ot' = observe t' ->
      SchedulerOfferCanonical t w -> label_world l w w' ->
      SchedulerOfferShape t' w'.
  Proof.
    intros l os ot' TR.
    induction TR as [Y c x k l u TR IH | u u' l TR IH | u u2 Equ | Y e k x u Equ | r];
      intros t t' w w' Hos Hot' Hcan Hlw.
    - (* Transbr: hidden branch of the focused thread, or the scheduling pick *)
      canonical_heads Hcan Hos Hlw.
      + focused_heads v i Hos Hvi.
        dependent destruction Hos.
        eapply IH; [reflexivity | exact Hot' | | exact Hlw].
        apply scheduler_offer_canonical_schedule; exact Hworld.
      + dependent destruction Hos.
        eapply IH; [reflexivity | exact Hot' | | exact Hlw].
        apply scheduler_offer_canonical_picked; exact Hworld.
    - (* Transguard *)
      canonical_heads Hcan Hos Hlw.
      focused_heads v i Hos Hvi; injection Hos as ->.
      + eapply IH; [reflexivity | exact Hot' | | exact Hlw].
        apply scheduler_offer_canonical_schedule; exact Hworld.
      + eapply IH; [reflexivity | exact Hot' | | exact Hlw].
        apply scheduler_offer_canonical_schedule; exact Hworld.
      + eapply IH; [reflexivity | exact Hot' | | exact Hlw].
        apply scheduler_offer_canonical_schedule; exact Hworld.
    - (* Transtau: a visible step of the focused thread, or of the pick *)
      canonical_heads Hcan Hos Hlw; destruct Hlw as [Hnd ->].
      + focused_heads v i Hos Hvi; injection Hos as ->.
        eapply scheduler_offer_shape_observe; [exact Hot' |].
        eapply scheduler_offer_shape_equ; [exact Equ |].
        apply scheduler_offer_shape_schedule; exact Hworld.
      + injection Hos as ->.
        eapply scheduler_offer_shape_observe; [exact Hot' |].
        eapply scheduler_offer_shape_equ; [exact Equ |].
        apply scheduler_offer_shape_schedule; exact Hworld.
    - (* Transobs *)
      canonical_heads Hcan Hos Hlw; destruct Hlw as [Hnd ->].
      + focused_heads v i Hos Hvi; dependent destruction Hos.
        * (* Fork *)
          destruct x.
          eapply scheduler_offer_shape_observe; [exact Hot' |].
          eapply scheduler_offer_shape_equ; [symmetry; exact Equ |].
          apply scheduler_offer_shape_schedule; exact I.
        * (* user event *)
          eapply scheduler_offer_shape_observe; [exact Hot' |].
          eapply scheduler_offer_shape_equ; [symmetry; exact Equ |].
          apply scheduler_offer_shape_schedule; exact I.
      + (* scheduling point *)
        dependent destruction Hos. destruct x.
        eapply scheduler_offer_shape_observe; [exact Hot' |].
        eapply scheduler_offer_shape_equ; [symmetry; exact Equ |].
        apply scheduler_offer_shape_prefix_at_point.
      + (* offer at the scheduling point *)
        dependent destruction Hos. destruct x.
        eapply scheduler_offer_shape_observe; [exact Hot' |].
        eapply scheduler_offer_shape_equ; [symmetry; exact Equ |].
        apply scheduler_offer_shape_prefix_elsewhere; exact I.
      + (* exhausted prefix: the scheduling Yield *)
        dependent destruction Hos. destruct x.
        eapply scheduler_offer_shape_observe; [exact Hot' |].
        eapply scheduler_offer_shape_equ; [symmetry; exact Equ |].
        apply scheduler_offer_shape_choice; exact I.
      + (* offer elsewhere *)
        dependent destruction Hos. destruct x.
        eapply scheduler_offer_shape_observe; [exact Hot' |].
        eapply scheduler_offer_shape_equ; [symmetry; exact Equ |].
        apply scheduler_offer_shape_prefix_elsewhere; exact I.
    - (* Transval *)
      destruct Hlw as [x | Y e v x].
      + apply scheduler_offer_shape_done.
      + apply scheduler_offer_shape_finish.
  Qed.

  Local Lemma scheduler_offer_canonical_step t w t' w' :
    SchedulerOfferCanonical t w ->
    |t, w| ↦ |t', w'| ->
    SchedulerOfferShape t' w'.
  Proof.
    intros Hcanonical Htr.
    destruct (ktrans_label_world _ _ _ _ Htr) as (l & TR & Hlw).
    exact (scheduler_offer_canonical_trans l _ _ TR t t' w w'
             eq_refl eq_refl Hcanonical Hlw).
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
      : observed_completed E B -> World (scheduler_observedE E) -> Prop :=
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
    cbn in Hcoind.
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
      n (v : pool E B n) focus :
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
      n (v : pool E B n) focus :
    SchedulerProgress (schedule_with_offers n v focus) Pure ->
    agc scheduling_point_offer_obligation
      (schedule_with_offers n v focus) Pure.
  Proof.
    apply every_live_slot_is_eventually_offered_at_scheduling_points.
  Qed.
End ObservedScheduler.
