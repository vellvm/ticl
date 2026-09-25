From Stdlib Require Import
  Fin
  Vector
  Program.Equality.
From Coinduction Require Import coinduction lattice tactics.
From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.Interp.Core
  ICTree.Trans
  Events.Core
  Utils.Utils
  ICTree.Events.Yield
  ICTree.Interp.Yield.Mod
  ICTree.Interp.Yield.SBisim
  Utils.Vectors
  ICTree.SBisim.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

(** Proof-facing scheduler observations for local fairness reasoning.

    The core scheduler is left unchanged.  This module mirrors [schedule] with
    an additive observation tier that records no-focus scheduling points and
    the finite set of slots offered at each such point.
    [forget_scheduler_offers_preserves_schedule] erases the observation tier
    back to [schedule] up to strong bisimulation. *)

Definition LiveSlot (n : nat) : Type := Fin.t n.

Record SlotRef : Type := {
  slot_pool_size : nat;
  slot_live_slot : LiveSlot slot_pool_size;
}.

Definition live_slot_ref {n : nat} (i : LiveSlot n) : SlotRef :=
  {| slot_pool_size := n; slot_live_slot := i |}.

Variant SchedulerObs : Type :=
| ObsSchedulingPoint : nat -> SchedulerObs
| ObsOffered : SlotRef -> SchedulerObs.

Definition schedulerObsE : Type := SchedulerObs.

#[global] Instance Encode_schedulerObsE : Encode SchedulerObs :=
  fun _ => unit.

Definition scheduler_observedE (E : Type) : Type :=
  schedulerObsE + (yieldE + (spawnE + E)).

Definition observed_completed (E : Type) `{Encode E} : Type :=
  ictree (scheduler_observedE E) unit.


Section ObservedScheduler.
  Context {E : Type} `{Encode E}.

  (** Observed scheduler.  The only extra visible events are proof-facing
      [schedulerObsE] events at nonempty no-focus scheduling points. *)
  CoFixpoint schedule_with_offers
      (n : nat) (v : pool E n) (focus : option (Fin.t n))
      : observed_completed E :=
    match focus with
    | None =>
        match n return pool E n -> observed_completed E with
        | 0 => fun _ => Ret tt
        | S n' => fun v =>
            Vis (inl (ObsSchedulingPoint (S n')))
              (fun _ : unit =>
                 schedule_with_offers_offer_prefix (S n') (S n')
                   (fun i => i) v)
        end v
    | Some i =>
        match n return pool E n -> Fin.t n -> observed_completed E with
        | 0 => fun _ i => match i with end
        | S n' => fun v i =>
            match observe (v $ i) with
            | RetF _ =>
                Guard (schedule_with_offers n' ((v -- i)) None)
            | BrF b k =>
                Br b (fun j =>
                  schedule_with_offers (S n')
                    ((v @ i := (k j))) (Some i))
            | GuardF t =>
                Guard (schedule_with_offers (S n')
                  ((v @ i := t)) (Some i))
            | VisF e k =>
                match e as e0 return
                    (encode e0 -> thread E) -> observed_completed E with
                | inl Yield => fun k =>
                    Guard (schedule_with_offers (S n')
                      ((v @ i := (k tt))) None)
                | inr (inl Fork) => fun k =>
                    @go (scheduler_observedE E) _ unit
                      (VisF (inr (inr (inl Spawn))
                         : scheduler_observedE E)
                        (fun _ => schedule_with_offers (S (S n'))
                          (((k true) :: ((v @ i := (k false))))%vector)
                          (Some (Fin.FS i))))
                | inr (inr e') => fun k =>
                    @go (scheduler_observedE E) _ unit
                      (VisF (inr (inr (inr e'))
                         : scheduler_observedE E)
                        (fun x => schedule_with_offers (S n')
                          ((v @ i := (k x))) (Some i)))
                end k
            end
        end v i
    end
  with schedule_with_offers_offer_prefix
      (pool_size remaining : nat)
      (embed : LiveSlot remaining -> LiveSlot pool_size)
      (v : pool E pool_size) : observed_completed E :=
    match remaining return
        (LiveSlot remaining -> LiveSlot pool_size) ->
        pool E pool_size -> observed_completed E with
    | 0 => fun _ v =>
        match pool_size return pool E pool_size -> observed_completed E with
        | 0 => fun _ => Ret tt
        | S n' => fun v =>
            Vis (inr (inl Yield) : scheduler_observedE E)
              (fun _ : unit =>
                 Br n' (fun i =>
                   schedule_with_offers (S n') v (Some i)))
        end v
    | S n' => fun embed v =>
        Vis (inl (ObsOffered (live_slot_ref (embed Fin.F1))))
          (fun _ : unit =>
             schedule_with_offers_offer_prefix pool_size n'
               (fun i => embed (Fin.FS i)) v)
    end embed v.

  Definition handle_scheduler_offers
      : scheduler_observedE E ~> ictree (yieldE + (spawnE + E)) :=
    fun event =>
      match event with
      | inl _ => Ret tt
      | inr event' => ICtree.trigger event'
      end.

  Definition forget_scheduler_offers {X}
      (t : ictree (scheduler_observedE E) X)
      : ictree (yieldE + (spawnE + E)) X :=
    interp handle_scheduler_offers t.

  Lemma forget_scheduler_offers_no_focus_nonempty_unfold n
      (v : pool E (S n)) :
    forget_scheduler_offers (schedule_with_offers (S n) v None) ≅
      Guard (forget_scheduler_offers
        (schedule_with_offers_offer_prefix (S n) (S n)
          (fun i : LiveSlot (S n) => i) v)).
  Proof.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    cbn. rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma forget_scheduler_offers_offer_prefix_succ_stutter m n
      (embed : LiveSlot (S n) -> LiveSlot m) (v : pool E m) :
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix m (S n) embed v) ~
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix m n
        (fun i => embed (Fin.FS i)) v).
  Proof.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    cbn. rewrite bind_ret_l.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_offer_prefix_stutter m r
      (embed : LiveSlot r -> LiveSlot m) (v : pool E m) :
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix m r embed v) ~
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix m 0
        (fun i : LiveSlot 0 => match i with end) v).
  Proof.
    revert m embed v.
    induction r as [| r IHr]; intros m embed v.
    - destruct m as [| m'].
      + unfold forget_scheduler_offers.
        rewrite !unfold_interp.
        cbn.
        apply sb_ret. reflexivity.
      + unfold forget_scheduler_offers.
        rewrite !unfold_interp.
        cbn.
        reflexivity.
    - transitivity (forget_scheduler_offers
        (schedule_with_offers_offer_prefix m r
          (fun i => embed (Fin.FS i)) v)).
      + apply forget_scheduler_offers_offer_prefix_succ_stutter.
      + apply IHr.
  Qed.

  Lemma forget_scheduler_offers_no_focus_stutters_to_offer_prefix n
      (v : pool E (S n)) :
    forget_scheduler_offers (schedule_with_offers (S n) v None) ~
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix (S n) (S n)
        (fun i : LiveSlot (S n) => i) v).
  Proof.
    rewrite forget_scheduler_offers_no_focus_nonempty_unfold.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_offer_prefix_zero_nonempty_unfold n
      (embed : LiveSlot 0 -> LiveSlot (S n)) (v : pool E (S n)) :
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix (S n) 0 embed v) ~
    Vis (inl Yield)
      (fun _ : unit =>
         Br n (fun i =>
           forget_scheduler_offers
             (schedule_with_offers (S n) v (Some i)))).
  Proof.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    cbn.
    unfold ICtree.trigger, resum, ReSum_refl, resum_ret,
      ReSumRet_refl.
    rewrite bind_vis.
    setoid_rewrite bind_ret_l.
    apply sb_vis. intros [].
    apply sb_guard_l.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    cbn.
    apply sb_br_id. intro i.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_no_focus_projection_to_focused n
      (v : pool E (S n)) :
    forget_scheduler_offers (schedule_with_offers (S n) v None) ~
    Vis (inl Yield)
      (fun _ : unit =>
         Br n (fun i =>
           forget_scheduler_offers
             (schedule_with_offers (S n) v (Some i)))).
  Proof.
    transitivity (forget_scheduler_offers
      (schedule_with_offers_offer_prefix (S n) (S n)
        (fun i : LiveSlot (S n) => i) v)).
    - apply forget_scheduler_offers_no_focus_stutters_to_offer_prefix.
    - transitivity (forget_scheduler_offers
        (schedule_with_offers_offer_prefix (S n) 0
          (fun i : LiveSlot 0 => match i with end) v)).
      + apply forget_scheduler_offers_offer_prefix_stutter.
      + apply forget_scheduler_offers_offer_prefix_zero_nonempty_unfold.
  Qed.

  Local Ltac solve_focused_schedule_with_offers H :=
    lazy [schedule_with_offers observe _observe];
    match type of H with
    | observe (Vector.nth ?v ?i) = _ =>
        change (@_observe _ _ unit (Vector.nth v i)) with (observe (Vector.nth v i));
        rewrite H;
        reflexivity
    end.

  Lemma schedule_with_offers_no_focus_nonempty n
      (v : pool E (S n)) :
    observe (schedule_with_offers (S n) v None) =
      VisF (inl (ObsSchedulingPoint (S n)))
        (fun _ : unit =>
           schedule_with_offers_offer_prefix (S n) (S n)
             (fun i => i) v).
  Proof. reflexivity. Qed.

  Lemma schedule_with_offers_offer_prefix_succ m n
      (embed : LiveSlot (S n) -> LiveSlot m) (v : pool E m) :
    observe (schedule_with_offers_offer_prefix m (S n) embed v) =
      VisF (inl (ObsOffered (live_slot_ref (embed Fin.F1))))
        (fun _ : unit =>
           schedule_with_offers_offer_prefix m n
             (fun i => embed (Fin.FS i)) v).
  Proof. reflexivity. Qed.

  Lemma schedule_with_offers_focused_ret n
      (v : pool E (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = RetF tt ->
    observe (schedule_with_offers (S n) v (Some i)) =
      GuardF (schedule_with_offers n ((v -- i)) None).
  Proof.
    intro Hret.
    solve_focused_schedule_with_offers Hret.
  Qed.

  Lemma schedule_with_offers_focused_br n
      (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v $ i) = BrF b k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      BrF b (fun j =>
        schedule_with_offers (S n) ((v @ i := (k j))) (Some i)).
  Proof.
    intro Hbr.
    solve_focused_schedule_with_offers Hbr.
  Qed.

  Lemma schedule_with_offers_focused_guard n
      (v : pool E (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    observe (schedule_with_offers (S n) v (Some i)) =
      GuardF (schedule_with_offers (S n) ((v @ i := t)) (Some i)).
  Proof.
    intro Hg.
    solve_focused_schedule_with_offers Hg.
  Qed.

  Lemma schedule_with_offers_focused_yield n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl Yield) k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      GuardF (schedule_with_offers (S n)
        ((v @ i := (k tt))) None).
  Proof.
    intro Hy.
    solve_focused_schedule_with_offers Hy.
  Qed.

  Lemma schedule_with_offers_focused_fork n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr (inl Fork)) k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      VisF (inr (inr (inl Spawn)) : scheduler_observedE E)
        (fun _ => schedule_with_offers (S (S n))
          (((k true) :: ((v @ i := (k false))))%vector)
          (Some (Fin.FS i))).
  Proof.
    intro Hf.
    solve_focused_schedule_with_offers Hf.
  Qed.

  Lemma schedule_with_offers_focused_user_event n
      (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v $ i) = VisF (inr (inr e)) k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      VisF (inr (inr (inr e)) : scheduler_observedE E)
        (fun x => schedule_with_offers (S n)
          ((v @ i := (k x))) (Some i)).
  Proof.
    intro Hu.
    solve_focused_schedule_with_offers Hu.
  Qed.

  Lemma forget_scheduler_offers_empty_no_focus_projection
      (v : pool E 0) :
    forget_scheduler_offers (schedule_with_offers 0 v None) ~ Ret tt.
  Proof.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    cbn.
    apply sb_ret. reflexivity.
  Qed.

  Lemma forget_scheduler_offers_focused_br_projection n
      (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v $ i) = BrF b k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Br b (fun j =>
      forget_scheduler_offers
        (schedule_with_offers (S n) ((v @ i := (k j))) (Some i))).
  Proof.
    intro Hbr.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_br n v i b k Hbr).
    cbn.
    apply sb_br_id. intro j.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_focused_fork_projection n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr (inl Fork)) k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Vis (inr (inl Spawn) : yieldE + (spawnE + E))
      (fun _ =>
        forget_scheduler_offers (schedule_with_offers (S (S n))
          (((k true) :: ((v @ i := (k false))))%vector)
          (Some (Fin.FS i)))).
  Proof.
    intro Hfork.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_fork n v i k Hfork).
    cbn.
    unfold ICtree.trigger, resum, ReSum_refl, resum_ret,
      ReSumRet_refl.
    rewrite bind_vis.
    setoid_rewrite bind_ret_l.
    apply sb_vis. intros [].
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_focused_user_event_projection n
      (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v $ i) = VisF (inr (inr e)) k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Vis (inr (inr e) : yieldE + (spawnE + E))
      (fun x =>
        forget_scheduler_offers
          (schedule_with_offers (S n) ((v @ i := (k x))) (Some i))).
  Proof.
    intro Huser.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_user_event n v i e k Huser).
    cbn.
    unfold ICtree.trigger, resum, ReSum_refl, resum_ret,
      ReSumRet_refl.
    rewrite bind_vis.
    setoid_rewrite bind_ret_l.
    apply sb_vis. intro x.
    apply sb_guard.
  Qed.

  Local Notation completed' := (completed E).
  Local Notation stR R := (lattice.body (coinduction.t (sb eq)) R).

  Local Definition erased_schedule (n : nat) (v : pool E n)
      (focus : option (Fin.t n)) : completed E :=
    forget_scheduler_offers (schedule_with_offers n v focus).

  Local Lemma erased_focused_ret_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = RetF tt ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule n ((v -- i)) None).
  Proof.
    intro Hret.
    unfold erased_schedule, forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_ret n v i Hret).
    reflexivity.
  Qed.

  Local Lemma erased_focused_br_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v $ i) = BrF b k ->
    erased_schedule (S n) v (Some i) ≅
    Br b (fun j => Guard (erased_schedule (S n)
      ((v @ i := (k j))) (Some i))).
  Proof.
    intro Hbr.
    unfold erased_schedule, forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_br n v i b k Hbr).
    reflexivity.
  Qed.

  Local Lemma erased_focused_guard_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule (S n) ((v @ i := t)) (Some i)).
  Proof.
    intro Hguard.
    unfold erased_schedule, forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_guard n v i t Hguard).
    reflexivity.
  Qed.

  Local Lemma erased_focused_yield_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl Yield) k ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule (S n) ((v @ i := (k tt))) None).
  Proof.
    intro Hyield.
    unfold erased_schedule, forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_yield n v i k Hyield).
    reflexivity.
  Qed.

  Local Lemma erased_focused_fork_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr (inl Fork)) k ->
    erased_schedule (S n) v (Some i) ≅
    Vis (inr (inl Spawn) : yieldE + (spawnE + E))
      (fun _ => Guard (erased_schedule (S (S n))
        (((k true) :: ((v @ i := (k false))))%vector)
        (Some (Fin.FS i)))).
  Proof.
    intro Hfork.
    unfold erased_schedule, forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_fork n v i k Hfork).
    cbn.
    unfold ICtree.trigger, resum, ReSum_refl, resum_ret,
      ReSumRet_refl.
    rewrite bind_vis.
    setoid_rewrite bind_ret_l.
    reflexivity.
  Qed.

  Local Lemma erased_focused_user_event_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v $ i) = VisF (inr (inr e)) k ->
    erased_schedule (S n) v (Some i) ≅
    Vis (inr (inr e) : yieldE + (spawnE + E))
      (fun x => Guard (erased_schedule (S n)
        ((v @ i := (k x))) (Some i))).
  Proof.
    intro Huser.
    unfold erased_schedule, forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_user_event n v i e k Huser).
    cbn.
    unfold ICtree.trigger, resum, ReSum_refl, resum_ret,
      ReSumRet_refl.
    rewrite bind_vis.
    setoid_rewrite bind_ret_l.
    reflexivity.
  Qed.

  Local Lemma schedule_focused_yield_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl Yield) k ->
    schedule (S n) v (Some i) ≅
    Guard (schedule (S n) ((v @ i := (k tt))) None).
  Proof.
    intro Hyield.
    rewrite (ictree_eta (schedule (S n) v (Some i))).
    rewrite (schedule_focused_yield n v i k Hyield).
    reflexivity.
  Qed.

  Local Lemma guard_residual_from_equ (actual target residual : completed') :
    observe actual = GuardF residual ->
    actual ≅ Guard target ->
    residual ≅ target.
  Proof.
    intros Hobs Heq.
    apply equ_guard_invE.
    transitivity actual.
    - rewrite (ictree_eta actual). rewrite Hobs. reflexivity.
    - exact Heq.
  Qed.

  Local Ltac contradiction_from_shape_equ actual Hobs Heq :=
    exfalso;
    rewrite (ictree_eta actual) in Heq;
    rewrite <- Hobs in Heq;
    step in Heq; inversion Heq.

  Local Lemma erased_schedule_match_left_empty
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' (v : pool E 0) :
    actual ≅ erased_schedule 0 v None ->
    trans l actual t' ->
    exists u', trans l (schedule 0 v None) u' /\ stR R t' u'.
  Proof.
    intros Hactual TRactual.
    assert (Hproj : actual ~ Ret tt).
    { rewrite Hactual.
      unfold erased_schedule.
      apply forget_scheduler_offers_empty_no_focus_projection. }
    destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
      [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
    apply trans_ret_inv in Hmid as [Hmid ->].
    exists stuck. split.
    - rewrite (trans_schedule_empty_ret v). apply trans_ret.
    - rewrite Hsb. rewrite Hmid. reflexivity.
  Qed.

  Local Lemma erased_schedule_match_left_no_focus
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' n (v : pool E (S n)) :
    actual ≅ erased_schedule (S n) v None ->
    trans l actual t' ->
    exists u', trans l (schedule (S n) v None) u' /\ stR R t' u'.
  Proof.
    intros Hactual TRactual.
    assert (Hproj : actual ~
      Vis (inl Yield : yieldE + (spawnE + E))
        (fun _ : unit => Br n (fun i =>
           erased_schedule (S n) v (Some i)))).
    { rewrite Hactual.
      unfold erased_schedule.
      apply forget_scheduler_offers_no_focus_projection_to_focused. }
    destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
      [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
    apply trans_vis_inv in Hmid as [x [Hmid Hlabel]].
    subst l. destruct x.
    exists (Br n (fun i => schedule (S n) v (Some i))). split.
    - apply trans_schedule_no_focus_nonempty.
    - rewrite Hsb. rewrite Hmid.
      apply (coinduction.bt_t (sb eq)).
      apply step_sb_br_id; [reflexivity | intro j].
      apply Hch.
  Qed.

  Local Lemma erased_schedule_match_left_br
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' n (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v $ i) = BrF b k ->
    actual ≅ erased_schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (schedule (S n) v (Some i)) u' /\ stR R t' u'.
  Proof.
    intros Hvi Hactual TRactual.
    assert (Hproj : actual ~
      Br b (fun j => erased_schedule (S n)
        ((v @ i := (k j))) (Some i))).
    { rewrite Hactual.
      apply forget_scheduler_offers_focused_br_projection.
      exact Hvi. }
    destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
      [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
    apply trans_br_inv in Hmid as [j [Hmid Hlabel]].
    subst l.
    exists (schedule (S n) ((v @ i := (k j))) (Some i)).
    split.
    - apply trans_schedule_focused_br. exact Hvi.
    - rewrite Hsb. rewrite Hmid. apply Hch.
  Qed.

  Local Lemma erased_schedule_match_left_fork
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr (inl Fork)) k ->
    actual ≅ erased_schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (schedule (S n) v (Some i)) u' /\ stR R t' u'.
  Proof.
    intros Hvi Hactual TRactual.
    assert (Hproj : actual ~
      Vis (inr (inl Spawn) : yieldE + (spawnE + E))
        (fun _ => erased_schedule (S (S n))
          (((k true) :: ((v @ i := (k false))))%vector)
          (Some (Fin.FS i)))).
    { rewrite Hactual.
      apply forget_scheduler_offers_focused_fork_projection.
      exact Hvi. }
    destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
      [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
    apply trans_vis_inv in Hmid as [x [Hmid Hlabel]].
    subst l. destruct x.
    exists (schedule (S (S n))
      (((k true) :: ((v @ i := (k false))))%vector)
      (Some (Fin.FS i))). split.
    - apply trans_schedule_focused_fork. exact Hvi.
    - rewrite Hsb. rewrite Hmid. apply Hch.
  Qed.

  Local Lemma erased_schedule_match_left_user
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' n (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v $ i) = VisF (inr (inr e)) k ->
    actual ≅ erased_schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (schedule (S n) v (Some i)) u' /\ stR R t' u'.
  Proof.
    intros Hvi Hactual TRactual.
    assert (Hproj : actual ~
      Vis (inr (inr e) : yieldE + (spawnE + E))
        (fun x => erased_schedule (S n)
          ((v @ i := (k x))) (Some i))).
    { rewrite Hactual.
      apply forget_scheduler_offers_focused_user_event_projection.
      exact Hvi. }
    destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
      [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
    apply trans_vis_inv in Hmid as [x [Hmid Hlabel]].
    subst l.
    exists (schedule (S n) ((v @ i := (k x))) (Some i)).
    split.
    - apply trans_schedule_focused_user_event. exact Hvi.
    - rewrite Hsb. rewrite Hmid. apply Hch.
  Qed.

  Local Lemma schedule_focused_br_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v $ i) = BrF b k ->
    schedule (S n) v (Some i) ≅
    Br b (fun j => schedule (S n) ((v @ i := (k j))) (Some i)).
  Proof.
    intro Hbr.
    rewrite (ictree_eta (schedule (S n) v (Some i))).
    rewrite (schedule_focused_br n v i b k Hbr).
    reflexivity.
  Qed.

  Local Lemma schedule_focused_fork_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr (inl Fork)) k ->
    schedule (S n) v (Some i) ≅
    Vis (inr (inl Spawn) : yieldE + (spawnE + E))
      (fun _ => schedule (S (S n))
        (((k true) :: ((v @ i := (k false))))%vector)
        (Some (Fin.FS i))).
  Proof.
    intro Hfork.
    rewrite (ictree_eta (schedule (S n) v (Some i))).
    rewrite (schedule_focused_fork n v i k Hfork).
    reflexivity.
  Qed.

  Local Lemma schedule_focused_user_event_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v $ i) = VisF (inr (inr e)) k ->
    schedule (S n) v (Some i) ≅
    Vis (inr (inr e) : yieldE + (spawnE + E))
      (fun x => schedule (S n) ((v @ i := (k x))) (Some i)).
  Proof.
    intro Huser.
    rewrite (ictree_eta (schedule (S n) v (Some i))).
    rewrite (schedule_focused_user_event n v i e k Huser).
    reflexivity.
  Qed.

  Local Lemma erased_schedule_match_right_empty
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' (v : pool E 0) :
    actual ≅ schedule 0 v None ->
    trans l actual t' ->
    exists u', trans l (erased_schedule 0 v None) u' /\ stR R u' t'.
  Proof.
    intros Hactual TRactual.
    assert (Hret : actual ~ Ret tt).
    { rewrite Hactual. rewrite (trans_schedule_empty_ret v). reflexivity. }
    destruct (sbisim_trans actual _ t' l eq Hret TRactual) as
      [l' [mid [Hmid [Hl' Hsb_mid]]]]. subst l'.
    assert (Hproj : Ret tt ~ erased_schedule 0 v None).
    { symmetry.
      unfold erased_schedule.
      apply forget_scheduler_offers_empty_no_focus_projection. }
    destruct (sbisim_trans (Ret tt) _ mid l eq Hproj Hmid) as
      [l'' [u' [Htru [Hl'' Hsb_u]]]]. subst l''.
    exists u'. split.
    - exact Htru.
    - rewrite Hsb_mid. rewrite <- Hsb_u. reflexivity.
  Qed.

  Local Lemma erased_schedule_match_right_no_focus
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' n (v : pool E (S n)) :
    actual ≅ schedule (S n) v None ->
    trans l actual t' ->
    exists u', trans l (erased_schedule (S n) v None) u' /\ stR R u' t'.
  Proof.
    intros Hactual TRactual.
    set (sres := Br n (fun i => schedule (S n) v (Some i))).
    set (lres := Br n (fun i => erased_schedule (S n) v (Some i))).
    assert (Hshape : actual ~
      Vis (inl Yield : yieldE + (spawnE + E)) (fun _ : unit => sres)).
    { rewrite Hactual. rewrite (schedule_no_focus_equ n v). reflexivity. }
    destruct (sbisim_trans actual _ t' l eq Hshape TRactual) as
      [l' [mid [Hmid [Hl' Hsb_mid]]]]. subst l'.
    apply trans_vis_inv in Hmid as [x [Hmid Hlabel]].
    subst l. destruct x.
    assert (Hstep_lres : trans (obs (inl Yield : yieldE + (spawnE + E)) tt)
      (Vis (inl Yield : yieldE + (spawnE + E)) (fun _ : unit => lres))
      lres).
    { apply trans_vis. }
    assert (Hproj :
      Vis (inl Yield : yieldE + (spawnE + E)) (fun _ : unit => lres) ~
      erased_schedule (S n) v None).
    { symmetry.
      unfold erased_schedule.
      apply forget_scheduler_offers_no_focus_projection_to_focused. }
    destruct (sbisim_trans _ _ lres
      (obs (inl Yield : yieldE + (spawnE + E)) tt) eq Hproj
      Hstep_lres) as [l'' [u' [Htru [Hl'' Hsb_u]]]].
    subst l''.
    exists u'. split.
    - exact Htru.
    - rewrite Hsb_mid. rewrite Hmid. rewrite <- Hsb_u.
      apply (coinduction.bt_t (sb eq)).
      apply step_sb_br_id; [reflexivity | intro j].
      apply Hch.
  Qed.

  Local Lemma erased_schedule_match_right_br
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' n (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v $ i) = BrF b k ->
    actual ≅ schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (erased_schedule (S n) v (Some i)) u' /\ stR R u' t'.
  Proof.
    intros Hvi Hactual TRactual.
    set (sres := fun j =>
      schedule (S n) ((v @ i := (k j))) (Some i)).
    set (lres := fun j =>
      erased_schedule (S n) ((v @ i := (k j))) (Some i)).
    assert (Hshape : actual ~ Br b sres).
    { rewrite Hactual. rewrite (schedule_focused_br_equ n v i b k Hvi).
      reflexivity. }
    destruct (sbisim_trans actual _ t' l eq Hshape TRactual) as
      [l' [mid [Hmid [Hl' Hsb_mid]]]]. subst l'.
    apply trans_br_inv in Hmid as [j [Hmid Hlabel]].
    subst l.
    assert (Hstep_lres : trans tau (Br b lres) (lres j)).
    { apply trans_br with (x := j). reflexivity. }
    assert (Hproj : Br b lres ~ erased_schedule (S n) v (Some i)).
    { symmetry.
      apply forget_scheduler_offers_focused_br_projection. exact Hvi. }
    destruct (sbisim_trans _ _ (lres j) tau eq Hproj Hstep_lres)
      as [l'' [u' [Htru [Hl'' Hsb_u]]]]. subst l''.
    exists u'. split.
    - exact Htru.
    - rewrite Hsb_mid. rewrite Hmid. rewrite <- Hsb_u. apply Hch.
  Qed.

  Local Lemma erased_schedule_match_right_fork
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr (inl Fork)) k ->
    actual ≅ schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (erased_schedule (S n) v (Some i)) u' /\ stR R u' t'.
  Proof.
    intros Hvi Hactual TRactual.
    set (sres := schedule (S (S n))
      (((k true) :: ((v @ i := (k false))))%vector)
      (Some (Fin.FS i))).
    set (lres := erased_schedule (S (S n))
      (((k true) :: ((v @ i := (k false))))%vector)
      (Some (Fin.FS i))).
    assert (Hshape : actual ~
      Vis (inr (inl Spawn) : yieldE + (spawnE + E))
        (fun _ : unit => sres)).
    { rewrite Hactual. rewrite (schedule_focused_fork_equ n v i k Hvi).
      reflexivity. }
    destruct (sbisim_trans actual _ t' l eq Hshape TRactual) as
      [l' [mid [Hmid [Hl' Hsb_mid]]]]. subst l'.
    apply trans_vis_inv in Hmid as [x [Hmid Hlabel]].
    subst l. destruct x.
    assert (Hstep_lres : trans
      (obs (inr (inl Spawn) : yieldE + (spawnE + E)) tt)
      (Vis (inr (inl Spawn) : yieldE + (spawnE + E))
        (fun _ : unit => lres)) lres).
    { apply trans_vis. }
    assert (Hproj :
      Vis (inr (inl Spawn) : yieldE + (spawnE + E))
        (fun _ : unit => lres) ~
      erased_schedule (S n) v (Some i)).
    { symmetry.
      apply forget_scheduler_offers_focused_fork_projection. exact Hvi. }
    destruct (sbisim_trans _ _ lres
      (obs (inr (inl Spawn) : yieldE + (spawnE + E)) tt) eq Hproj
      Hstep_lres) as [l'' [u' [Htru [Hl'' Hsb_u]]]].
    subst l''.
    exists u'. split.
    - exact Htru.
    - rewrite Hsb_mid. rewrite Hmid. rewrite <- Hsb_u. apply Hch.
  Qed.

  Local Lemma erased_schedule_match_right_user
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' n (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v $ i) = VisF (inr (inr e)) k ->
    actual ≅ schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (erased_schedule (S n) v (Some i)) u' /\ stR R u' t'.
  Proof.
    intros Hvi Hactual TRactual.
    set (sres := fun x =>
      schedule (S n) ((v @ i := (k x))) (Some i)).
    set (lres := fun x =>
      erased_schedule (S n) ((v @ i := (k x))) (Some i)).
    assert (Hshape : actual ~
      Vis (inr (inr e) : yieldE + (spawnE + E)) sres).
    { rewrite Hactual.
      rewrite (schedule_focused_user_event_equ n v i e k Hvi).
      reflexivity. }
    destruct (sbisim_trans actual _ t' l eq Hshape TRactual) as
      [l' [mid [Hmid [Hl' Hsb_mid]]]]. subst l'.
    apply trans_vis_inv in Hmid as [x [Hmid Hlabel]].
    subst l.
    assert (Hstep_lres : trans
      (obs (inr (inr e) : yieldE + (spawnE + E)) x)
      (Vis (inr (inr e) : yieldE + (spawnE + E)) lres) (lres x)).
    { apply trans_vis. }
    assert (Hproj : Vis (inr (inr e) : yieldE + (spawnE + E)) lres ~
      erased_schedule (S n) v (Some i)).
    { symmetry.
      apply forget_scheduler_offers_focused_user_event_projection. exact Hvi. }
    destruct (sbisim_trans _ _ (lres x)
      (obs (inr (inr e) : yieldE + (spawnE + E)) x) eq Hproj
      Hstep_lres) as [l'' [u' [Htru [Hl'' Hsb_u]]]].
    subst l''.
    exists u'. split.
    - exact Htru.
    - rewrite Hsb_mid. rewrite Hmid. rewrite <- Hsb_u. apply Hch.
  Qed.

  Local Lemma erased_schedule_match_left (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f)) :
    forall l os ot', trans_ l os ot' ->
    forall actual n (v : pool E n) focus t',
      os = observe actual ->
      ot' = observe t' ->
      actual ≅ erased_schedule n v focus ->
      exists u', trans l (schedule n v focus) u' /\ stR R t' u'.
  Proof.
    intros l os ot' TR.
    induction TR; intros actual nn v focus t' Hos Hot Hactual.
    - destruct focus as [i |].
      + destruct nn as [| n']; [inversion i |].
        destruct (observe (v $ i)) as [r | b k | g | e k] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (erased_schedule n' ((v -- i)) None)).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_ret_equ. exact Hvi. }
          assert (Ht : t ≅ erased_schedule n' ((v -- i)) None).
          { eapply guard_residual_from_equ.
            - symmetry. exact Hos.
            - exact Hguard. }
          destruct (IHTR t n' ((v -- i)) None t'
            eq_refl Hot Ht) as [u' [Htru Hres]].
          exists u'. split.
          -- rewrite (trans_schedule_focused_ret n' v i Hvi).
             apply trans_guard. exact Htru.
          -- exact Hres.
        * assert (Hproj : actual ~
            Br b (fun j => erased_schedule (S n')
              ((v @ i := (k j))) (Some i))).
          { rewrite Hactual.
            apply forget_scheduler_offers_focused_br_projection.
            exact Hvi. }
          assert (TRactual : trans l actual t').
          { unfold trans. rewrite <- Hos, <- Hot. constructor. exact TR. }
          destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
            [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
          apply trans_br_inv in Hmid as [j [Hmid ->]].
          exists (schedule (S n') ((v @ i := (k j))) (Some i)).
          split.
          -- apply trans_schedule_focused_br. exact Hvi.
          -- rewrite Hsb. rewrite Hmid. apply Hch.
        * assert (Hguard : actual ≅
            Guard (erased_schedule (S n') ((v @ i := g)) (Some i))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_guard_equ. exact Hvi. }
          assert (Ht : t ≅
            erased_schedule (S n') ((v @ i := g)) (Some i)).
          { eapply guard_residual_from_equ.
            - symmetry. exact Hos.
            - exact Hguard. }
          destruct (IHTR t (S n') ((v @ i := g)) (Some i) t'
            eq_refl Hot Ht) as [u' [Htru Hres]].
          exists u'. split.
          -- rewrite (trans_schedule_focused_guard n' v i g Hvi).
             apply trans_guard. exact Htru.
          -- exact Hres.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (erased_schedule (S n')
                 ((v @ i := (k tt))) None)).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_yield_equ. exact Hvi. }
             assert (Ht : t ≅ erased_schedule (S n')
               ((v @ i := (k tt))) None).
             { eapply guard_residual_from_equ.
               - symmetry. exact Hos.
               - exact Hguard. }
             destruct (IHTR t (S n') ((v @ i := (k tt))) None t'
               eq_refl Hot Ht) as [u' [Htru Hres]].
             exists u'. split.
             ++ rewrite (schedule_focused_yield_equ n' v i k Hvi).
                apply trans_guard. exact Htru.
             ++ exact Hres.
          -- destruct frk.
             assert (Hproj : actual ~
               Vis (inr (inl Spawn) : yieldE + (spawnE + E))
                 (fun _ => erased_schedule (S (S n'))
                   (((k true) :: ((v @ i := (k false))))%vector)
                   (Some (Fin.FS i)))).
             { rewrite Hactual.
               apply forget_scheduler_offers_focused_fork_projection.
               exact Hvi. }
             assert (TRactual : trans l actual t').
             { unfold trans. rewrite <- Hos, <- Hot. constructor. exact TR. }
             destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
               [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
             apply trans_vis_inv in Hmid as [x [Hmid ->]].
             destruct x.
             exists (schedule (S (S n'))
               (((k true) :: ((v @ i := (k false))))%vector)
               (Some (Fin.FS i))). split.
             ++ apply trans_schedule_focused_fork. exact Hvi.
             ++ rewrite Hsb. rewrite Hmid. apply Hch.
          -- assert (Hproj : actual ~
               Vis (inr (inr usr) : yieldE + (spawnE + E))
                 (fun x => erased_schedule (S n')
                   ((v @ i := (k x))) (Some i))).
             { rewrite Hactual.
               apply forget_scheduler_offers_focused_user_event_projection.
               exact Hvi. }
             assert (TRactual : trans l actual t').
             { unfold trans. rewrite <- Hos, <- Hot. constructor. exact TR. }
             destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
               [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
             apply trans_vis_inv in Hmid as [x [Hmid ->]].
             exists (schedule (S n') ((v @ i := (k x))) (Some i)).
             split.
             ++ apply trans_schedule_focused_user_event. exact Hvi.
             ++ rewrite Hsb. rewrite Hmid. apply Hch.
      + destruct nn as [| n'].
        * assert (Hproj : actual ~ Ret tt).
          { rewrite Hactual.
            unfold erased_schedule.
            apply forget_scheduler_offers_empty_no_focus_projection. }
          assert (TRactual : trans l actual t').
          { unfold trans. rewrite <- Hos, <- Hot. constructor. exact TR. }
          destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
            [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
          apply trans_ret_inv in Hmid as [Hmid ->].
          exists stuck. split.
          -- rewrite (trans_schedule_empty_ret v). apply trans_ret.
          -- rewrite Hsb. rewrite Hmid. reflexivity.
        * assert (Hproj : actual ~
            Vis (inl Yield : yieldE + (spawnE + E))
              (fun _ : unit => Br n' (fun i =>
                 erased_schedule (S n') v (Some i)))).
          { rewrite Hactual.
            unfold erased_schedule.
            apply forget_scheduler_offers_no_focus_projection_to_focused. }
          assert (TRactual : trans l actual t').
          { unfold trans. rewrite <- Hos, <- Hot. constructor. exact TR. }
          destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
            [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
          apply trans_vis_inv in Hmid as [x [Hmid ->]].
          destruct x.
          exists (Br n' (fun i => schedule (S n') v (Some i))). split.
          -- apply trans_schedule_no_focus_nonempty.
          -- rewrite Hsb. rewrite Hmid.
             apply (coinduction.bt_t (sb eq)).
             apply step_sb_br_id; [reflexivity | intro j].
             apply Hch.
    - assert (TRactual : trans tau actual t').
      { unfold trans. rewrite <- Hos, <- Hot.
        eapply Steptau. exact H0. }
      destruct focus as [i |].
      + destruct nn as [| n']; [inversion i |].
        destruct (observe (v $ i)) as [r | b k0 | g | e k0] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (erased_schedule n' ((v -- i)) None)).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_ret_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * eapply erased_schedule_match_left_br; eauto.
        * assert (Hguard : actual ≅
            Guard (erased_schedule (S n') ((v @ i := g)) (Some i))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_guard_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (erased_schedule (S n')
                 ((v @ i := (k0 tt))) None)).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_yield_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hguard.
          -- destruct frk.
             assert (Hvis : actual ≅
               Vis (inr (inl Spawn) : yieldE + (spawnE + E))
                 (fun _ => Guard (erased_schedule (S (S n'))
                   (((k0 true) :: ((v @ i := (k0 false))))%vector)
                   (Some (Fin.FS i))))).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_fork_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hvis.
          -- assert (Hvis : actual ≅
               Vis (inr (inr usr) : yieldE + (spawnE + E))
                 (fun x => Guard (erased_schedule (S n')
                   ((v @ i := (k0 x))) (Some i)))).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_user_event_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hvis.
      + destruct nn as [| n'].
        * eapply erased_schedule_match_left_empty; eauto.
        * eapply erased_schedule_match_left_no_focus; eauto.
    - assert (TRactual : trans (obs e x) actual t').
      { unfold trans. rewrite <- Hos, <- Hot.
        eapply Stepobs. exact H0. }
      destruct focus as [i |].
      + destruct nn as [| n']; [inversion i |].
        destruct (observe (v $ i)) as [r | b k0 | g | e0 k0] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (erased_schedule n' ((v -- i)) None)).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_ret_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * assert (Hbr : actual ≅
            Br b (fun j => Guard (erased_schedule (S n')
              ((v @ i := (k0 j))) (Some i)))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_br_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hbr.
        * assert (Hguard : actual ≅
            Guard (erased_schedule (S n') ((v @ i := g)) (Some i))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_guard_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e0 as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (erased_schedule (S n')
                 ((v @ i := (k0 tt))) None)).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_yield_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hguard.
          -- destruct frk.
             eapply erased_schedule_match_left_fork; eauto.
          -- eapply erased_schedule_match_left_user; eauto.
      + destruct nn as [| n'].
        * eapply erased_schedule_match_left_empty; eauto.
        * eapply erased_schedule_match_left_no_focus; eauto.
    - assert (TRactual : trans (val r) actual t').
      { unfold trans. rewrite <- Hos, <- Hot.
        eapply Stepval. exact H0. }
      destruct focus as [i |].
      + destruct nn as [| n']; [inversion i |].
        destruct (observe (v $ i)) as [r0 | b k0 | g | e k0] eqn:Hvi.
        * destruct r0.
          assert (Hguard : actual ≅
            Guard (erased_schedule n' ((v -- i)) None)).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_ret_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * assert (Hbr : actual ≅
            Br b (fun j => Guard (erased_schedule (S n')
              ((v @ i := (k0 j))) (Some i)))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_br_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hbr.
        * assert (Hguard : actual ≅
            Guard (erased_schedule (S n') ((v @ i := g)) (Some i))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_guard_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (erased_schedule (S n')
                 ((v @ i := (k0 tt))) None)).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_yield_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hguard.
          -- destruct frk.
             assert (Hvis : actual ≅
               Vis (inr (inl Spawn) : yieldE + (spawnE + E))
                 (fun _ => Guard (erased_schedule (S (S n'))
                   (((k0 true) :: ((v @ i := (k0 false))))%vector)
                   (Some (Fin.FS i))))).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_fork_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hvis.
          -- assert (Hvis : actual ≅
               Vis (inr (inr usr) : yieldE + (spawnE + E))
                 (fun x => Guard (erased_schedule (S n')
                   ((v @ i := (k0 x))) (Some i)))).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_user_event_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hvis.
      + destruct nn as [| n'].
        * eapply erased_schedule_match_left_empty; eauto.
        * eapply erased_schedule_match_left_no_focus; eauto.
  Qed.

  Local Lemma erased_schedule_match_right (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f)) :
    forall l os ot', trans_ l os ot' ->
    forall actual n (v : pool E n) focus t',
      os = observe actual ->
      ot' = observe t' ->
      actual ≅ schedule n v focus ->
      exists u', trans l (erased_schedule n v focus) u' /\ stR R u' t'.
  Proof.
    intros l os ot' TR.
    induction TR; intros actual nn v focus t' Hos Hot Hactual.
    - assert (TRactual : trans l actual t').
      { unfold trans. rewrite <- Hos, <- Hot. constructor. exact TR. }
      destruct focus as [i |].
      + destruct nn as [| n']; [inversion i |].
        destruct (observe (v $ i)) as [r | b k | g | e k] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (schedule n' ((v -- i)) None)).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_ret. exact Hvi. }
          assert (Ht : t ≅ schedule n' ((v -- i)) None).
          { eapply guard_residual_from_equ.
            - symmetry. exact Hos.
            - exact Hguard. }
          destruct (IHTR t n' ((v -- i)) None t'
            eq_refl Hot Ht) as [u' [Htru Hres]].
          exists u'. split.
          -- rewrite (erased_focused_ret_equ n' v i Hvi).
             apply trans_guard. exact Htru.
          -- exact Hres.
        * eapply erased_schedule_match_right_br; eauto.
        * assert (Hguard : actual ≅
            Guard (schedule (S n') ((v @ i := g)) (Some i))).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_guard. exact Hvi. }
          assert (Ht : t ≅
            schedule (S n') ((v @ i := g)) (Some i)).
          { eapply guard_residual_from_equ.
            - symmetry. exact Hos.
            - exact Hguard. }
          destruct (IHTR t (S n') ((v @ i := g)) (Some i) t'
            eq_refl Hot Ht) as [u' [Htru Hres]].
          exists u'. split.
          -- rewrite (erased_focused_guard_equ n' v i g Hvi).
             apply trans_guard. exact Htru.
          -- exact Hres.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (schedule (S n')
                 ((v @ i := (k tt))) None)).
             { transitivity (schedule (S n') v (Some i)).
               - exact Hactual.
               - apply schedule_focused_yield_equ. exact Hvi. }
             assert (Ht : t ≅ schedule (S n')
               ((v @ i := (k tt))) None).
             { eapply guard_residual_from_equ.
               - symmetry. exact Hos.
               - exact Hguard. }
             destruct (IHTR t (S n') ((v @ i := (k tt))) None t'
               eq_refl Hot Ht) as [u' [Htru Hres]].
             exists u'. split.
             ++ rewrite (erased_focused_yield_equ n' v i k Hvi).
                apply trans_guard. exact Htru.
             ++ exact Hres.
          -- destruct frk.
             eapply erased_schedule_match_right_fork; eauto.
          -- eapply erased_schedule_match_right_user; eauto.
      + destruct nn as [| n'].
        * eapply erased_schedule_match_right_empty; eauto.
        * eapply erased_schedule_match_right_no_focus; eauto.
    - assert (TRactual : trans tau actual t').
      { unfold trans. rewrite <- Hos, <- Hot.
        eapply Steptau. exact H0. }
      destruct focus as [i |].
      + destruct nn as [| n']; [inversion i |].
        destruct (observe (v $ i)) as [r | b k0 | g | e k0] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (schedule n' ((v -- i)) None)).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_ret. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * eapply erased_schedule_match_right_br; eauto.
        * assert (Hguard : actual ≅
            Guard (schedule (S n') ((v @ i := g)) (Some i))).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_guard. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (schedule (S n')
                 ((v @ i := (k0 tt))) None)).
             { transitivity (schedule (S n') v (Some i)).
               - exact Hactual.
               - apply schedule_focused_yield_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hguard.
          -- destruct frk.
             eapply erased_schedule_match_right_fork; eauto.
          -- eapply erased_schedule_match_right_user; eauto.
      + destruct nn as [| n'].
        * eapply erased_schedule_match_right_empty; eauto.
        * eapply erased_schedule_match_right_no_focus; eauto.
    - assert (TRactual : trans (obs e x) actual t').
      { unfold trans. rewrite <- Hos, <- Hot.
        eapply Stepobs. exact H0. }
      destruct focus as [i |].
      + destruct nn as [| n']; [inversion i |].
        destruct (observe (v $ i)) as [r | b k0 | g | e0 k0] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (schedule n' ((v -- i)) None)).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_ret. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * eapply erased_schedule_match_right_br; eauto.
        * assert (Hguard : actual ≅
            Guard (schedule (S n') ((v @ i := g)) (Some i))).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_guard. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e0 as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (schedule (S n')
                 ((v @ i := (k0 tt))) None)).
             { transitivity (schedule (S n') v (Some i)).
               - exact Hactual.
               - apply schedule_focused_yield_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hguard.
          -- destruct frk.
             eapply erased_schedule_match_right_fork; eauto.
          -- eapply erased_schedule_match_right_user; eauto.
      + destruct nn as [| n'].
        * eapply erased_schedule_match_right_empty; eauto.
        * eapply erased_schedule_match_right_no_focus; eauto.
    - assert (TRactual : trans (val r) actual t').
      { unfold trans. rewrite <- Hos, <- Hot.
        eapply Stepval. exact H0. }
      destruct focus as [i |].
      + destruct nn as [| n']; [inversion i |].
        destruct (observe (v $ i)) as [r0 | b k0 | g | e k0] eqn:Hvi.
        * destruct r0.
          assert (Hguard : actual ≅
            Guard (schedule n' ((v -- i)) None)).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_ret. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * eapply erased_schedule_match_right_br; eauto.
        * assert (Hguard : actual ≅
            Guard (schedule (S n') ((v @ i := g)) (Some i))).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_guard. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (schedule (S n')
                 ((v @ i := (k0 tt))) None)).
             { transitivity (schedule (S n') v (Some i)).
               - exact Hactual.
               - apply schedule_focused_yield_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hguard.
          -- destruct frk.
             eapply erased_schedule_match_right_fork; eauto.
          -- eapply erased_schedule_match_right_user; eauto.
      + destruct nn as [| n'].
        * eapply erased_schedule_match_right_empty; eauto.
        * eapply erased_schedule_match_right_no_focus; eauto.
  Qed.

  Theorem forget_scheduler_offers_preserves_schedule
      n (v : pool E n) focus :
    forget_scheduler_offers (schedule_with_offers n v focus) ~
    schedule n v focus.
  Proof.
    change (erased_schedule n v focus ~ schedule n v focus).
    revert n v focus.
    coinduction R CH.
    intros n v focus.
    assert (Hch : forall m (w : pool E m) f,
      stR R (erased_schedule m w f) (schedule m w f)).
    { intros m w f. apply CH. }
    split.
    - intros l t' TR.
      destruct (erased_schedule_match_left R Hch _ _ _ TR
        (erased_schedule n v focus) n v focus t'
        eq_refl eq_refl ltac:(reflexivity)) as [u' [Htru Hres]].
      exists l, u'. split; [exact Htru | split].
      + exact Hres.
      + reflexivity.
    - intros l t' TR.
      destruct (erased_schedule_match_right R Hch _ _ _ TR
        (schedule n v focus) n v focus t'
        eq_refl eq_refl ltac:(reflexivity)) as [u' [Htru Hres]].
      exists l, u'. split; [exact Htru | split].
      + unfold Basics.flip. exact Hres.
      + reflexivity.
  Qed.

  Inductive offered_in_scheduler_prefix (n : nat) (i : LiveSlot n)
      : observed_completed E -> Prop :=
  | offered_prefix_here t k :
      observe t = VisF (inl (ObsOffered (live_slot_ref i))) k ->
      offered_in_scheduler_prefix n i t
  | offered_prefix_later t obs k :
      observe t = VisF (inl obs) k ->
      offered_in_scheduler_prefix n i (k tt) ->
      offered_in_scheduler_prefix n i t.

  Lemma schedule_with_offers_offer_prefix_offers m :
    forall n (embed : LiveSlot n -> LiveSlot m) (v : pool E m)
      (i : LiveSlot n),
      offered_in_scheduler_prefix m (embed i)
        (schedule_with_offers_offer_prefix m n embed v).
  Proof.
    intros n embed v i.
    induction i as [n' | n' i IH].
    - apply offered_prefix_here with
        (k := fun _ : unit =>
          schedule_with_offers_offer_prefix m n'
            (fun i => embed (Fin.FS i)) v).
      apply schedule_with_offers_offer_prefix_succ.
    - apply offered_prefix_later with
        (obs := ObsOffered (live_slot_ref (embed Fin.F1)))
        (k := fun _ : unit =>
          schedule_with_offers_offer_prefix m n'
            (fun j => embed (Fin.FS j)) v).
      + apply schedule_with_offers_offer_prefix_succ.
      + apply (IH (fun j => embed (Fin.FS j))).
  Qed.

  Lemma observed_equ_refl_no_eqdep (t : observed_completed E) : t ≅ t.
  Proof.
    unfold equ.
    apply (leq_gfp (@fequ _ _ unit unit eq)
      (fun u v : observed_completed E => u = v)).
    - intros u v <-. cbn. destruct (observe u); constructor; auto.
    - reflexivity.
  Qed.

  Lemma observed_equ_step_no_eqdep (t u : observed_completed E) :
    t ≅ u -> equF eq (equ eq) (observe t) (observe u).
  Proof.
    intro Htu. unfold equ in Htu.
    exact (proj1 (gfp_fp (@fequ _ _ unit unit eq) t u) Htu).
  Qed.

  Definition equF_scheduler_vis_result
      (p q : ictree' (scheduler_observedE E) unit) : Prop :=
    match q with
    | VisF (inl sched_obs) k_right =>
        exists k_left,
          p = VisF (inl sched_obs) k_left /\ k_left tt ≅ k_right tt
    | _ => True
    end.

  Lemma equF_scheduler_vis_inv_no_eqdep p q :
    equF eq (equ eq) p q -> equF_scheduler_vis_result p q.
  Proof.
    intro Hf.
    destruct Hf as [x y Hxy | e k1 k2 Hk | t1 t2 Ht |
        n k1 k2 Hk]; cbn; try exact I.
    destruct e as [sched_obs | rest]; cbn; try exact I.
    exists k1. split; [reflexivity | apply Hk].
  Qed.

  Lemma equ_scheduler_vis_inv_from_observe_no_eqdep
      (obs : schedulerObsE)
      (k : encode (inl obs : scheduler_observedE E) ->
        observed_completed E)
      (t u : observed_completed E) :
    t ≅ u ->
    observe u = VisF (inl obs) k ->
    exists k_t, observe t = VisF (inl obs) k_t /\ k_t tt ≅ k tt.
  Proof.
    intros Htu Hu.
    pose proof (equF_scheduler_vis_inv_no_eqdep _ _
      (observed_equ_step_no_eqdep _ _ Htu)) as Hshape.
    rewrite Hu in Hshape.
    exact Hshape.
  Qed.

  Inductive SchedulerEquChain :
      observed_completed E -> observed_completed E -> Prop :=
  | scheduler_equ_chain_refl t : SchedulerEquChain t t
  | scheduler_equ_chain_cons t u v :
      t ≅ u ->
      SchedulerEquChain u v ->
      SchedulerEquChain t v.

  Lemma scheduler_equ_chain_scheduler_vis_inv_no_eqdep
      (obs : schedulerObsE)
      (k : encode (inl obs : scheduler_observedE E) ->
        observed_completed E)
      (t u : observed_completed E) :
    SchedulerEquChain t u ->
    observe u = VisF (inl obs) k ->
    exists k_t,
      observe t = VisF (inl obs) k_t /\
      SchedulerEquChain (k_t tt) (k tt).
  Proof.
    intros Hchain Hobs.
    induction Hchain as [u | t mid u Htm _ IH].
    - exists k. split; [exact Hobs | constructor].
    - destruct (IH Hobs) as [k_mid [Hmid Hcont]].
      destruct (equ_scheduler_vis_inv_from_observe_no_eqdep obs k_mid
        t mid Htm Hmid) as [k_t [Ht Hstep]].
      exists k_t. split; [exact Ht |].
      econstructor; [exact Hstep | exact Hcont].
  Qed.

  Lemma show_no_focus_offers_every_live_slot_prefix n
      (v : pool E (S n)) (i : LiveSlot (S n)) :
    offered_in_scheduler_prefix (S n) i
      (schedule_with_offers (S n) v None).
  Proof.
    eapply offered_prefix_later.
    - apply schedule_with_offers_no_focus_nonempty.
    - apply (schedule_with_offers_offer_prefix_offers (S n) (S n)
        (fun i => i) v i).
  Qed.

End ObservedScheduler.
