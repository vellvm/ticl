From Stdlib Require Import
  Fin
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
  Lang.Yield.Events
  Lang.Yield.Scheduler
  Lang.Yield.SBisim
  Lang.Yield.Ticl
  Lang.Yield.Vec
  ICTree.SBisim.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.

(** Proof-facing scheduler observations for local fairness reasoning.

    The core scheduler is left unchanged.  This module mirrors [schedule] with
    an additive observation tier that records no-focus scheduling points and
    the finite set of slots offered at each such point. *)

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

Definition observed_scheduling_point (n : nat) (obs : schedulerObsE) : Prop :=
  obs = ObsSchedulingPoint n.

Definition offer_live_slot_obs (n : nat) (i : LiveSlot n)
    (obs : schedulerObsE) : Prop :=
  obs = ObsOffered (live_slot_ref i).

Definition offer_live_slot {E : Type} `{Encode E}
    (n : nat) (i : LiveSlot n) : ticll (scheduler_observedE E) :=
  CNow (fun w => w = Obs (inl (ObsOffered (live_slot_ref i))) tt).

Definition recognize_live_slot {E : Type} `{Encode E}
    (n : nat) (_ : pool E n) (_ : LiveSlot n) : Prop :=
  True.

Lemma fin_cast_refl {n : nat} (i : Fin.t n) :
  Fin.cast i eq_refl = i.
Proof. induction i; cbn; congruence. Qed.

Lemma live_slot_one_eq (i j : LiveSlot 1) : i = j.
Proof.
  refine (Fin.caseS' i (fun i => forall j, i = j) _ _ j).
  - intro j'.
    refine (Fin.caseS' j' (fun j => Fin.F1 = j) eq_refl _).
    intro j0.
    exact (Fin.case0 (fun j0 => Fin.F1 = Fin.FS j0) j0).
  - intro i0.
    exact (Fin.case0 (fun i0 => forall j, Fin.FS i0 = j) i0).
Qed.

Section ObservedScheduler.
  Context {E : Type} `{Encode E}.

  Definition emit_scheduler_obs (obs : schedulerObsE) : observed_completed E :=
    Vis (inl obs) (fun _ : unit => Ret tt).

  Fixpoint emit_live_slot_offers_into_then
      (m n : nat) (embed : LiveSlot n -> LiveSlot m)
      (k : observed_completed E) {struct n} : observed_completed E :=
    match n return (LiveSlot n -> LiveSlot m) -> observed_completed E with
    | 0 => fun _ => k
    | S n' => fun embed =>
        Vis (inl (ObsOffered (live_slot_ref (embed Fin.F1))))
          (fun _ : unit =>
             emit_live_slot_offers_into_then m n'
               (fun i => embed (Fin.FS i)) k)
    end embed.

  Definition emit_live_slot_offers_then
      (n : nat) (k : observed_completed E) : observed_completed E :=
    emit_live_slot_offers_into_then n n (fun i => i) k.

  Definition emit_live_slot_offers (n : nat) : observed_completed E :=
    emit_live_slot_offers_then n (Ret tt).

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
            match observe (v i) with
            | RetF _ =>
                Guard (schedule_with_offers n' (remove_pool v i) None)
            | BrF b k =>
                Br b (fun j =>
                  schedule_with_offers (S n')
                    (replace_pool v i (k j)) (Some i))
            | GuardF t =>
                Guard (schedule_with_offers (S n')
                  (replace_pool v i t) (Some i))
            | VisF e k =>
                match e as e0 return
                    (encode e0 -> thread E) -> observed_completed E with
                | inl Yield => fun k =>
                    Guard (schedule_with_offers (S n')
                      (replace_pool v i (k tt)) None)
                | inr (inl Fork) => fun k =>
                    @go (scheduler_observedE E) _ unit
                      (VisF (inr (inr (inl Spawn))
                         : scheduler_observedE E)
                        (fun _ => schedule_with_offers (S (S n'))
                          (cons_pool (k true)
                            (replace_pool v i (k false)))
                          (Some (Fin.FS i))))
                | inr (inr e') => fun k =>
                    @go (scheduler_observedE E) _ unit
                      (VisF (inr (inr (inr e'))
                         : scheduler_observedE E)
                        (fun x => schedule_with_offers (S n')
                          (replace_pool v i (k x)) (Some i)))
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

  Definition observe_scheduler_offers
      (n : nat) (v : pool E n) (focus : option (Fin.t n))
      : observed_completed E :=
    schedule_with_offers n v focus.

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

  Lemma handle_scheduler_offers_obs obs :
    handle_scheduler_offers (inl obs) = Ret tt.
  Proof. reflexivity. Qed.

  Lemma handle_scheduler_offers_visible event :
    handle_scheduler_offers (inr event) = ICtree.trigger event.
  Proof. reflexivity. Qed.

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

  Theorem forget_scheduler_offers_preserves_schedule_exact_no_focus_impossible n
      (v : pool E (S n)) :
    ~ forget_scheduler_offers (schedule_with_offers (S n) v None) ≅
        schedule (S n) v None.
  Proof.
    intro Heq.
    step in Heq.
    cbn in Heq.
    inversion Heq.
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

  Lemma emit_live_slot_offers_into_then_zero m
      (embed : LiveSlot 0 -> LiveSlot m) k :
    emit_live_slot_offers_into_then m 0 embed k = k.
  Proof. reflexivity. Qed.

  Lemma emit_live_slot_offers_into_then_succ m n
      (embed : LiveSlot (S n) -> LiveSlot m) k :
    observe (emit_live_slot_offers_into_then m (S n) embed k) =
      VisF (inl (ObsOffered (live_slot_ref (embed Fin.F1))))
        (fun _ : unit =>
           emit_live_slot_offers_into_then m n
             (fun i => embed (Fin.FS i)) k).
  Proof. reflexivity. Qed.

  Lemma emit_live_slot_offers_zero :
    observe (emit_live_slot_offers 0) = RetF tt.
  Proof. reflexivity. Qed.

  Lemma emit_live_slot_offers_succ n :
    observe (emit_live_slot_offers (S n)) =
      VisF (inl (ObsOffered (live_slot_ref (Fin.F1 : LiveSlot (S n)))))
        (fun _ : unit =>
           emit_live_slot_offers_into_then (S n) n
             (fun i => Fin.FS i) (Ret tt)).
  Proof. reflexivity. Qed.

  Local Ltac solve_focused_schedule_with_offers H :=
    lazy [schedule_with_offers observe _observe];
    match type of H with
    | observe (?v ?i) = _ =>
        change (@_observe _ _ unit (v i)) with (observe (v i));
        rewrite H;
        reflexivity
    end.

  Lemma schedule_with_offers_empty_none (v : pool E 0) :
    observe (schedule_with_offers 0 v None) = RetF tt.
  Proof. reflexivity. Qed.

  Lemma schedule_with_offers_no_focus_nonempty n
      (v : pool E (S n)) :
    observe (schedule_with_offers (S n) v None) =
      VisF (inl (ObsSchedulingPoint (S n)))
        (fun _ : unit =>
           schedule_with_offers_offer_prefix (S n) (S n)
             (fun i => i) v).
  Proof. reflexivity. Qed.

  Lemma schedule_with_offers_offer_prefix_zero m
      (embed : LiveSlot 0 -> LiveSlot m) (v : pool E m) :
    observe (schedule_with_offers_offer_prefix m 0 embed v) =
      match m return pool E m -> ictree' (scheduler_observedE E) unit with
      | 0 => fun _ => RetF tt
      | S n => fun v =>
          VisF (inr (inl Yield) : scheduler_observedE E)
            (fun _ : unit =>
               Br n (fun i => schedule_with_offers (S n) v (Some i)))
      end v.
  Proof. destruct m; reflexivity. Qed.

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
    observe (v i) = RetF tt ->
    observe (schedule_with_offers (S n) v (Some i)) =
      GuardF (schedule_with_offers n (remove_pool v i) None).
  Proof.
    intro Hret.
    solve_focused_schedule_with_offers Hret.
  Qed.

  Lemma schedule_with_offers_focused_br n
      (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v i) = BrF b k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      BrF b (fun j =>
        schedule_with_offers (S n) (replace_pool v i (k j)) (Some i)).
  Proof.
    intro Hbr.
    solve_focused_schedule_with_offers Hbr.
  Qed.

  Lemma schedule_with_offers_focused_guard n
      (v : pool E (S n)) (i : Fin.t (S n)) t :
    observe (v i) = GuardF t ->
    observe (schedule_with_offers (S n) v (Some i)) =
      GuardF (schedule_with_offers (S n) (replace_pool v i t) (Some i)).
  Proof.
    intro Hg.
    solve_focused_schedule_with_offers Hg.
  Qed.

  Lemma schedule_with_offers_focused_yield n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inl Yield) k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      GuardF (schedule_with_offers (S n)
        (replace_pool v i (k tt)) None).
  Proof.
    intro Hy.
    solve_focused_schedule_with_offers Hy.
  Qed.

  Lemma schedule_with_offers_focused_fork n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inr (inl Fork)) k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      VisF (inr (inr (inl Spawn)) : scheduler_observedE E)
        (fun _ => schedule_with_offers (S (S n))
          (cons_pool (k true) (replace_pool v i (k false)))
          (Some (Fin.FS i))).
  Proof.
    intro Hf.
    solve_focused_schedule_with_offers Hf.
  Qed.

  Lemma schedule_with_offers_focused_user_event n
      (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v i) = VisF (inr (inr e)) k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      VisF (inr (inr (inr e)) : scheduler_observedE E)
        (fun x => schedule_with_offers (S n)
          (replace_pool v i (k x)) (Some i)).
  Proof.
    intro Hu.
    solve_focused_schedule_with_offers Hu.
  Qed.

  Lemma focused_yield_returns_to_scheduling_point n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inl Yield) k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      GuardF (schedule_with_offers (S n)
        (replace_pool v i (k tt)) None).
  Proof. apply schedule_with_offers_focused_yield. Qed.

  Lemma forget_scheduler_offers_empty_no_focus_projection
      (v : pool E 0) :
    forget_scheduler_offers (schedule_with_offers 0 v None) ~ Ret tt.
  Proof.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    cbn.
    apply sb_ret. reflexivity.
  Qed.

  Lemma forget_scheduler_offers_focused_ret_projection n
      (v : pool E (S n)) (i : Fin.t (S n)) :
    observe (v i) = RetF tt ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    forget_scheduler_offers (schedule_with_offers n (remove_pool v i) None).
  Proof.
    intro Hret.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_ret n v i Hret).
    cbn.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_focused_br_projection n
      (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v i) = BrF b k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Br b (fun j =>
      forget_scheduler_offers
        (schedule_with_offers (S n) (replace_pool v i (k j)) (Some i))).
  Proof.
    intro Hbr.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_br n v i b k Hbr).
    cbn.
    apply sb_br_id. intro j.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_focused_guard_projection n
      (v : pool E (S n)) (i : Fin.t (S n)) t :
    observe (v i) = GuardF t ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    forget_scheduler_offers
      (schedule_with_offers (S n) (replace_pool v i t) (Some i)).
  Proof.
    intro Hguard.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_guard n v i t Hguard).
    cbn.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_focused_yield_projection n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inl Yield) k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    forget_scheduler_offers
      (schedule_with_offers (S n) (replace_pool v i (k tt)) None).
  Proof.
    intro Hyield.
    unfold forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_yield n v i k Hyield).
    cbn.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_focused_fork_projection n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inr (inl Fork)) k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Vis (inr (inl Spawn) : yieldE + (spawnE + E))
      (fun _ =>
        forget_scheduler_offers (schedule_with_offers (S (S n))
          (cons_pool (k true) (replace_pool v i (k false)))
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
    observe (v i) = VisF (inr (inr e)) k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Vis (inr (inr e) : yieldE + (spawnE + E))
      (fun x =>
        forget_scheduler_offers
          (schedule_with_offers (S n) (replace_pool v i (k x)) (Some i))).
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
    observe (v i) = RetF tt ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule n (remove_pool v i) None).
  Proof.
    intro Hret.
    unfold erased_schedule, forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_ret n v i Hret).
    reflexivity.
  Qed.

  Local Lemma erased_focused_br_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v i) = BrF b k ->
    erased_schedule (S n) v (Some i) ≅
    Br b (fun j => Guard (erased_schedule (S n)
      (replace_pool v i (k j)) (Some i))).
  Proof.
    intro Hbr.
    unfold erased_schedule, forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_br n v i b k Hbr).
    reflexivity.
  Qed.

  Local Lemma erased_focused_guard_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) t :
    observe (v i) = GuardF t ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule (S n) (replace_pool v i t) (Some i)).
  Proof.
    intro Hguard.
    unfold erased_schedule, forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_guard n v i t Hguard).
    reflexivity.
  Qed.

  Local Lemma erased_focused_yield_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inl Yield) k ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule (S n) (replace_pool v i (k tt)) None).
  Proof.
    intro Hyield.
    unfold erased_schedule, forget_scheduler_offers.
    rewrite unfold_interp.
    rewrite (schedule_with_offers_focused_yield n v i k Hyield).
    reflexivity.
  Qed.

  Local Lemma erased_focused_fork_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inr (inl Fork)) k ->
    erased_schedule (S n) v (Some i) ≅
    Vis (inr (inl Spawn) : yieldE + (spawnE + E))
      (fun _ => Guard (erased_schedule (S (S n))
        (cons_pool (k true) (replace_pool v i (k false)))
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
    observe (v i) = VisF (inr (inr e)) k ->
    erased_schedule (S n) v (Some i) ≅
    Vis (inr (inr e) : yieldE + (spawnE + E))
      (fun x => Guard (erased_schedule (S n)
        (replace_pool v i (k x)) (Some i))).
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
    observe (v i) = VisF (inl Yield) k ->
    schedule (S n) v (Some i) ≅
    Guard (schedule (S n) (replace_pool v i (k tt)) None).
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
    observe (v i) = BrF b k ->
    actual ≅ erased_schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (schedule (S n) v (Some i)) u' /\ stR R t' u'.
  Proof.
    intros Hvi Hactual TRactual.
    assert (Hproj : actual ~
      Br b (fun j => erased_schedule (S n)
        (replace_pool v i (k j)) (Some i))).
    { rewrite Hactual.
      apply forget_scheduler_offers_focused_br_projection.
      exact Hvi. }
    destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
      [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
    apply trans_br_inv in Hmid as [j [Hmid Hlabel]].
    subst l.
    exists (schedule (S n) (replace_pool v i (k j)) (Some i)).
    split.
    - apply trans_schedule_focused_br. exact Hvi.
    - rewrite Hsb. rewrite Hmid. apply Hch.
  Qed.

  Local Lemma erased_schedule_match_left_fork
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inr (inl Fork)) k ->
    actual ≅ erased_schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (schedule (S n) v (Some i)) u' /\ stR R t' u'.
  Proof.
    intros Hvi Hactual TRactual.
    assert (Hproj : actual ~
      Vis (inr (inl Spawn) : yieldE + (spawnE + E))
        (fun _ => erased_schedule (S (S n))
          (cons_pool (k true) (replace_pool v i (k false)))
          (Some (Fin.FS i)))).
    { rewrite Hactual.
      apply forget_scheduler_offers_focused_fork_projection.
      exact Hvi. }
    destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
      [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
    apply trans_vis_inv in Hmid as [x [Hmid Hlabel]].
    subst l. destruct x.
    exists (schedule (S (S n))
      (cons_pool (k true) (replace_pool v i (k false)))
      (Some (Fin.FS i))). split.
    - apply trans_schedule_focused_fork. exact Hvi.
    - rewrite Hsb. rewrite Hmid. apply Hch.
  Qed.

  Local Lemma erased_schedule_match_left_user
      (R : rel completed' completed')
      (Hch : forall m (w : pool E m) f,
        stR R (erased_schedule m w f) (schedule m w f))
      l actual t' n (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v i) = VisF (inr (inr e)) k ->
    actual ≅ erased_schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (schedule (S n) v (Some i)) u' /\ stR R t' u'.
  Proof.
    intros Hvi Hactual TRactual.
    assert (Hproj : actual ~
      Vis (inr (inr e) : yieldE + (spawnE + E))
        (fun x => erased_schedule (S n)
          (replace_pool v i (k x)) (Some i))).
    { rewrite Hactual.
      apply forget_scheduler_offers_focused_user_event_projection.
      exact Hvi. }
    destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
      [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
    apply trans_vis_inv in Hmid as [x [Hmid Hlabel]].
    subst l.
    exists (schedule (S n) (replace_pool v i (k x)) (Some i)).
    split.
    - apply trans_schedule_focused_user_event. exact Hvi.
    - rewrite Hsb. rewrite Hmid. apply Hch.
  Qed.

  Local Lemma schedule_focused_br_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v i) = BrF b k ->
    schedule (S n) v (Some i) ≅
    Br b (fun j => schedule (S n) (replace_pool v i (k j)) (Some i)).
  Proof.
    intro Hbr.
    rewrite (ictree_eta (schedule (S n) v (Some i))).
    rewrite (schedule_focused_br n v i b k Hbr).
    reflexivity.
  Qed.

  Local Lemma schedule_focused_fork_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inr (inl Fork)) k ->
    schedule (S n) v (Some i) ≅
    Vis (inr (inl Spawn) : yieldE + (spawnE + E))
      (fun _ => schedule (S (S n))
        (cons_pool (k true) (replace_pool v i (k false)))
        (Some (Fin.FS i))).
  Proof.
    intro Hfork.
    rewrite (ictree_eta (schedule (S n) v (Some i))).
    rewrite (schedule_focused_fork n v i k Hfork).
    reflexivity.
  Qed.

  Local Lemma schedule_focused_user_event_equ n
      (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v i) = VisF (inr (inr e)) k ->
    schedule (S n) v (Some i) ≅
    Vis (inr (inr e) : yieldE + (spawnE + E))
      (fun x => schedule (S n) (replace_pool v i (k x)) (Some i)).
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
    observe (v i) = BrF b k ->
    actual ≅ schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (erased_schedule (S n) v (Some i)) u' /\ stR R u' t'.
  Proof.
    intros Hvi Hactual TRactual.
    set (sres := fun j =>
      schedule (S n) (replace_pool v i (k j)) (Some i)).
    set (lres := fun j =>
      erased_schedule (S n) (replace_pool v i (k j)) (Some i)).
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
    observe (v i) = VisF (inr (inl Fork)) k ->
    actual ≅ schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (erased_schedule (S n) v (Some i)) u' /\ stR R u' t'.
  Proof.
    intros Hvi Hactual TRactual.
    set (sres := schedule (S (S n))
      (cons_pool (k true) (replace_pool v i (k false)))
      (Some (Fin.FS i))).
    set (lres := erased_schedule (S (S n))
      (cons_pool (k true) (replace_pool v i (k false)))
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
    observe (v i) = VisF (inr (inr e)) k ->
    actual ≅ schedule (S n) v (Some i) ->
    trans l actual t' ->
    exists u', trans l (erased_schedule (S n) v (Some i)) u' /\ stR R u' t'.
  Proof.
    intros Hvi Hactual TRactual.
    set (sres := fun x =>
      schedule (S n) (replace_pool v i (k x)) (Some i)).
    set (lres := fun x =>
      erased_schedule (S n) (replace_pool v i (k x)) (Some i)).
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
        destruct (observe (v i)) as [r | b k | g | e k] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (erased_schedule n' (remove_pool v i) None)).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_ret_equ. exact Hvi. }
          assert (Ht : t ≅ erased_schedule n' (remove_pool v i) None).
          { eapply guard_residual_from_equ.
            - symmetry. exact Hos.
            - exact Hguard. }
          destruct (IHTR t n' (remove_pool v i) None t'
            eq_refl Hot Ht) as [u' [Htru Hres]].
          exists u'. split.
          -- rewrite (trans_schedule_focused_ret n' v i Hvi).
             apply trans_guard. exact Htru.
          -- exact Hres.
        * assert (Hproj : actual ~
            Br b (fun j => erased_schedule (S n')
              (replace_pool v i (k j)) (Some i))).
          { rewrite Hactual.
            apply forget_scheduler_offers_focused_br_projection.
            exact Hvi. }
          assert (TRactual : trans l actual t').
          { unfold trans. rewrite <- Hos, <- Hot. constructor. exact TR. }
          destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
            [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
          apply trans_br_inv in Hmid as [j [Hmid ->]].
          exists (schedule (S n') (replace_pool v i (k j)) (Some i)).
          split.
          -- apply trans_schedule_focused_br. exact Hvi.
          -- rewrite Hsb. rewrite Hmid. apply Hch.
        * assert (Hguard : actual ≅
            Guard (erased_schedule (S n') (replace_pool v i g) (Some i))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_guard_equ. exact Hvi. }
          assert (Ht : t ≅
            erased_schedule (S n') (replace_pool v i g) (Some i)).
          { eapply guard_residual_from_equ.
            - symmetry. exact Hos.
            - exact Hguard. }
          destruct (IHTR t (S n') (replace_pool v i g) (Some i) t'
            eq_refl Hot Ht) as [u' [Htru Hres]].
          exists u'. split.
          -- rewrite (trans_schedule_focused_guard n' v i g Hvi).
             apply trans_guard. exact Htru.
          -- exact Hres.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (erased_schedule (S n')
                 (replace_pool v i (k tt)) None)).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_yield_equ. exact Hvi. }
             assert (Ht : t ≅ erased_schedule (S n')
               (replace_pool v i (k tt)) None).
             { eapply guard_residual_from_equ.
               - symmetry. exact Hos.
               - exact Hguard. }
             destruct (IHTR t (S n') (replace_pool v i (k tt)) None t'
               eq_refl Hot Ht) as [u' [Htru Hres]].
             exists u'. split.
             ++ rewrite (schedule_focused_yield_equ n' v i k Hvi).
                apply trans_guard. exact Htru.
             ++ exact Hres.
          -- destruct frk.
             assert (Hproj : actual ~
               Vis (inr (inl Spawn) : yieldE + (spawnE + E))
                 (fun _ => erased_schedule (S (S n'))
                   (cons_pool (k true) (replace_pool v i (k false)))
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
               (cons_pool (k true) (replace_pool v i (k false)))
               (Some (Fin.FS i))). split.
             ++ apply trans_schedule_focused_fork. exact Hvi.
             ++ rewrite Hsb. rewrite Hmid. apply Hch.
          -- assert (Hproj : actual ~
               Vis (inr (inr usr) : yieldE + (spawnE + E))
                 (fun x => erased_schedule (S n')
                   (replace_pool v i (k x)) (Some i))).
             { rewrite Hactual.
               apply forget_scheduler_offers_focused_user_event_projection.
               exact Hvi. }
             assert (TRactual : trans l actual t').
             { unfold trans. rewrite <- Hos, <- Hot. constructor. exact TR. }
             destruct (sbisim_trans actual _ t' l eq Hproj TRactual) as
               [l' [mid [Hmid [Hl' Hsb]]]]. subst l'.
             apply trans_vis_inv in Hmid as [x [Hmid ->]].
             exists (schedule (S n') (replace_pool v i (k x)) (Some i)).
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
        destruct (observe (v i)) as [r | b k0 | g | e k0] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (erased_schedule n' (remove_pool v i) None)).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_ret_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * eapply erased_schedule_match_left_br; eauto.
        * assert (Hguard : actual ≅
            Guard (erased_schedule (S n') (replace_pool v i g) (Some i))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_guard_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (erased_schedule (S n')
                 (replace_pool v i (k0 tt)) None)).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_yield_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hguard.
          -- destruct frk.
             assert (Hvis : actual ≅
               Vis (inr (inl Spawn) : yieldE + (spawnE + E))
                 (fun _ => Guard (erased_schedule (S (S n'))
                   (cons_pool (k0 true) (replace_pool v i (k0 false)))
                   (Some (Fin.FS i))))).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_fork_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hvis.
          -- assert (Hvis : actual ≅
               Vis (inr (inr usr) : yieldE + (spawnE + E))
                 (fun x => Guard (erased_schedule (S n')
                   (replace_pool v i (k0 x)) (Some i)))).
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
        destruct (observe (v i)) as [r | b k0 | g | e0 k0] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (erased_schedule n' (remove_pool v i) None)).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_ret_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * assert (Hbr : actual ≅
            Br b (fun j => Guard (erased_schedule (S n')
              (replace_pool v i (k0 j)) (Some i)))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_br_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hbr.
        * assert (Hguard : actual ≅
            Guard (erased_schedule (S n') (replace_pool v i g) (Some i))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_guard_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e0 as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (erased_schedule (S n')
                 (replace_pool v i (k0 tt)) None)).
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
        destruct (observe (v i)) as [r0 | b k0 | g | e k0] eqn:Hvi.
        * destruct r0.
          assert (Hguard : actual ≅
            Guard (erased_schedule n' (remove_pool v i) None)).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_ret_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * assert (Hbr : actual ≅
            Br b (fun j => Guard (erased_schedule (S n')
              (replace_pool v i (k0 j)) (Some i)))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_br_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hbr.
        * assert (Hguard : actual ≅
            Guard (erased_schedule (S n') (replace_pool v i g) (Some i))).
          { transitivity (erased_schedule (S n') v (Some i)).
            - exact Hactual.
            - apply erased_focused_guard_equ. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (erased_schedule (S n')
                 (replace_pool v i (k0 tt)) None)).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_yield_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hguard.
          -- destruct frk.
             assert (Hvis : actual ≅
               Vis (inr (inl Spawn) : yieldE + (spawnE + E))
                 (fun _ => Guard (erased_schedule (S (S n'))
                   (cons_pool (k0 true) (replace_pool v i (k0 false)))
                   (Some (Fin.FS i))))).
             { transitivity (erased_schedule (S n') v (Some i)).
               - exact Hactual.
               - apply erased_focused_fork_equ. exact Hvi. }
             contradiction_from_shape_equ actual Hos Hvis.
          -- assert (Hvis : actual ≅
               Vis (inr (inr usr) : yieldE + (spawnE + E))
                 (fun x => Guard (erased_schedule (S n')
                   (replace_pool v i (k0 x)) (Some i)))).
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
        destruct (observe (v i)) as [r | b k | g | e k] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (schedule n' (remove_pool v i) None)).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_ret. exact Hvi. }
          assert (Ht : t ≅ schedule n' (remove_pool v i) None).
          { eapply guard_residual_from_equ.
            - symmetry. exact Hos.
            - exact Hguard. }
          destruct (IHTR t n' (remove_pool v i) None t'
            eq_refl Hot Ht) as [u' [Htru Hres]].
          exists u'. split.
          -- rewrite (erased_focused_ret_equ n' v i Hvi).
             apply trans_guard. exact Htru.
          -- exact Hres.
        * eapply erased_schedule_match_right_br; eauto.
        * assert (Hguard : actual ≅
            Guard (schedule (S n') (replace_pool v i g) (Some i))).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_guard. exact Hvi. }
          assert (Ht : t ≅
            schedule (S n') (replace_pool v i g) (Some i)).
          { eapply guard_residual_from_equ.
            - symmetry. exact Hos.
            - exact Hguard. }
          destruct (IHTR t (S n') (replace_pool v i g) (Some i) t'
            eq_refl Hot Ht) as [u' [Htru Hres]].
          exists u'. split.
          -- rewrite (erased_focused_guard_equ n' v i g Hvi).
             apply trans_guard. exact Htru.
          -- exact Hres.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (schedule (S n')
                 (replace_pool v i (k tt)) None)).
             { transitivity (schedule (S n') v (Some i)).
               - exact Hactual.
               - apply schedule_focused_yield_equ. exact Hvi. }
             assert (Ht : t ≅ schedule (S n')
               (replace_pool v i (k tt)) None).
             { eapply guard_residual_from_equ.
               - symmetry. exact Hos.
               - exact Hguard. }
             destruct (IHTR t (S n') (replace_pool v i (k tt)) None t'
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
        destruct (observe (v i)) as [r | b k0 | g | e k0] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (schedule n' (remove_pool v i) None)).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_ret. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * eapply erased_schedule_match_right_br; eauto.
        * assert (Hguard : actual ≅
            Guard (schedule (S n') (replace_pool v i g) (Some i))).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_guard. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (schedule (S n')
                 (replace_pool v i (k0 tt)) None)).
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
        destruct (observe (v i)) as [r | b k0 | g | e0 k0] eqn:Hvi.
        * destruct r.
          assert (Hguard : actual ≅
            Guard (schedule n' (remove_pool v i) None)).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_ret. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * eapply erased_schedule_match_right_br; eauto.
        * assert (Hguard : actual ≅
            Guard (schedule (S n') (replace_pool v i g) (Some i))).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_guard. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e0 as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (schedule (S n')
                 (replace_pool v i (k0 tt)) None)).
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
        destruct (observe (v i)) as [r0 | b k0 | g | e k0] eqn:Hvi.
        * destruct r0.
          assert (Hguard : actual ≅
            Guard (schedule n' (remove_pool v i) None)).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_ret. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * eapply erased_schedule_match_right_br; eauto.
        * assert (Hguard : actual ≅
            Guard (schedule (S n') (replace_pool v i g) (Some i))).
          { transitivity (schedule (S n') v (Some i)).
            - exact Hactual.
            - apply trans_schedule_focused_guard. exact Hvi. }
          contradiction_from_shape_equ actual Hos Hguard.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             assert (Hguard : actual ≅
               Guard (schedule (S n')
                 (replace_pool v i (k0 tt)) None)).
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

  Record ReturnSlotTransport {n : nat}
      (v : pool E (S n)) (removed : LiveSlot (S n))
      (v' : pool E n) : Prop := {
    return_new_slots_come_from_old_survivors :
      forall j_new : LiveSlot n,
        exists j_old : LiveSlot (S n),
          j_old <> removed /\ v' j_new = v j_old;
    return_old_survivors_reappear :
      forall j_old : LiveSlot (S n),
        j_old <> removed ->
        exists j_new : LiveSlot n, v' j_new = v j_old
  }.

  Theorem return_removes_live_slot n
      (v : pool E (S n)) (i : Fin.t (S n)) :
    observe (v i) = RetF tt ->
    ReturnSlotTransport v i (remove_pool v i).
  Proof.
    intro Hret; clear Hret.
    revert v i.
    induction n as [| n IH]; intros v i.
    - constructor.
      + intro j_new.
        exact (Fin.case0 (fun j_new => exists j_old : LiveSlot 1,
          j_old <> i /\ remove_pool v i j_new = v j_old) j_new).
      + intros j_old Hneq.
        contradiction Hneq. apply live_slot_one_eq.
    - refine (Fin.caseS' i
        (fun i => ReturnSlotTransport v i (remove_pool v i)) _ _).
      + constructor.
        * intro j_new.
          exists (Fin.FS j_new). split.
          -- discriminate.
          -- reflexivity.
        * intros j_old Hneq.
          refine (Fin.caseS' j_old
            (fun j => j <> Fin.F1 ->
              exists j_new : LiveSlot (S n),
                remove_pool v Fin.F1 j_new = v j) _ _ Hneq).
          -- intro Hcontra. contradiction Hcontra; reflexivity.
          -- intros j_new _. exists j_new. reflexivity.
      + intro i_tail.
        pose proof (IH (fun k => v (Fin.FS k)) i_tail) as IHt.
        destruct IHt as [IHnew IHold].
        constructor.
        * intro j_new.
          refine (Fin.caseS' j_new
            (fun j => exists j_old : LiveSlot (S (S n)),
              j_old <> Fin.FS i_tail /\
              remove_pool v (Fin.FS i_tail) j = v j_old) _ _).
          -- exists Fin.F1. split.
             ++ discriminate.
             ++ reflexivity.
          -- intros j_new'.
             destruct (IHnew j_new') as [j_old [Hneq Hv]].
             exists (Fin.FS j_old). split.
             ++ intro Heq. apply Fin.FS_inj in Heq.
                contradiction Hneq.
             ++ cbn. rewrite !fin_cast_refl. exact Hv.
        * intros j_old Hneq.
          refine (Fin.caseS' j_old
            (fun j => j <> Fin.FS i_tail ->
              exists j_new : LiveSlot (S n),
                remove_pool v (Fin.FS i_tail) j_new = v j) _ _ Hneq).
          -- intros _. exists Fin.F1. reflexivity.
          -- intros j_old' Hneq'.
             assert (Hsurv : j_old' <> i_tail) by
               (intro Heq; subst; apply Hneq'; reflexivity).
             destruct (IHold j_old' Hsurv) as [j_new Hv].
             exists (Fin.FS j_new).
             cbn. rewrite !fin_cast_refl. exact Hv.
  Qed.

  Definition shift_live_slot_across_spawn {n : nat}
      (i : LiveSlot n) : LiveSlot (S n) :=
    Fin.FS i.

  Lemma shift_live_slot_across_spawn_head {n}
      (child : thread E) (v : pool E n) :
    cons_pool child v Fin.F1 = child.
  Proof. apply cons_pool_head. Qed.

  Lemma shift_live_slot_across_spawn_tail {n}
      (child : thread E) (v : pool E n) (i : LiveSlot n) :
    cons_pool child v (shift_live_slot_across_spawn i) = v i.
  Proof. apply cons_pool_tail. Qed.

  Lemma shift_live_slot_across_spawn_parent_slot n
      (v : pool E (S n)) (i : LiveSlot (S n)) k :
    cons_pool (k true) (replace_pool v i (k false))
      (shift_live_slot_across_spawn i) = k false.
  Proof.
    rewrite shift_live_slot_across_spawn_tail.
    apply replace_pool_hit.
  Qed.

  Lemma shift_live_slot_across_spawn_other_slot n
      (v : pool E (S n)) (i j : LiveSlot (S n)) k :
    i <> j ->
    cons_pool (k true) (replace_pool v i (k false))
      (shift_live_slot_across_spawn j) = v j.
  Proof.
    intro Hneq.
    rewrite shift_live_slot_across_spawn_tail.
    now apply replace_pool_miss.
  Qed.

  Lemma transport_live_slots_across_spawn_head {n}
      (child : thread E) (v : pool E n) :
    cons_pool child v Fin.F1 = child.
  Proof. apply shift_live_slot_across_spawn_head. Qed.

  Lemma transport_live_slots_across_spawn_tail {n}
      (child : thread E) (v : pool E n) (i : LiveSlot n) :
    cons_pool child v (shift_live_slot_across_spawn i) = v i.
  Proof. apply shift_live_slot_across_spawn_tail. Qed.

  Lemma transport_live_slots_across_spawn_parent_slot n
      (v : pool E (S n)) (i : LiveSlot (S n)) k :
    cons_pool (k true) (replace_pool v i (k false))
      (shift_live_slot_across_spawn i) = k false.
  Proof. apply shift_live_slot_across_spawn_parent_slot. Qed.

  Lemma transport_live_slots_across_spawn_other_slot n
      (v : pool E (S n)) (i j : LiveSlot (S n)) k :
    i <> j ->
    cons_pool (k true) (replace_pool v i (k false))
      (shift_live_slot_across_spawn j) = v j.
  Proof. apply shift_live_slot_across_spawn_other_slot. Qed.

  Record SpawnSlotTransport {n : nat}
      (v : pool E (S n)) (parent : LiveSlot (S n))
      (k : bool -> thread E) (spawned : pool E (S (S n))) : Prop := {
    spawn_child_at_head : spawned Fin.F1 = k true;
    spawn_parent_at_shifted_slot : spawned (Fin.FS parent) = k false;
    spawn_other_old_slots_shifted :
      forall j : LiveSlot (S n),
        j <> parent -> spawned (Fin.FS j) = v j
  }.

  Theorem transport_live_slots_across_spawn n
      (v : pool E (S n)) (i : LiveSlot (S n)) k :
    observe (v i) = VisF (inr (inl Fork)) k ->
    SpawnSlotTransport v i k
      (cons_pool (k true) (replace_pool v i (k false))).
  Proof.
    intro Hfork; clear Hfork.
    constructor.
    - apply cons_pool_head.
    - rewrite cons_pool_tail. apply replace_pool_hit.
    - intros j Hneq.
      rewrite cons_pool_tail.
      apply replace_pool_miss. congruence.
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

  Lemma emit_live_slot_offers_into_then_offers m :
    forall n (embed : LiveSlot n -> LiveSlot m) k (i : LiveSlot n),
      offered_in_scheduler_prefix m (embed i)
        (emit_live_slot_offers_into_then m n embed k).
  Proof.
    intros n embed k i.
    induction i as [n' | n' i IH].
    - apply offered_prefix_here with
        (k := fun _ : unit =>
          emit_live_slot_offers_into_then m n'
            (fun i => embed (Fin.FS i)) k).
      reflexivity.
    - apply offered_prefix_later with
        (obs := ObsOffered (live_slot_ref (embed Fin.F1)))
        (k := fun _ : unit =>
          emit_live_slot_offers_into_then m n'
            (fun j => embed (Fin.FS j)) k).
      + reflexivity.
      + apply (IH (fun j => embed (Fin.FS j))).
  Qed.

  Lemma emit_live_slot_offers_then_offers n k (i : LiveSlot n) :
    offered_in_scheduler_prefix n i (emit_live_slot_offers_then n k).
  Proof.
    unfold emit_live_slot_offers_then.
    apply (emit_live_slot_offers_into_then_offers n n (fun i => i) k i).
  Qed.

  Lemma emit_live_slot_offers_offers n (i : LiveSlot n) :
    offered_in_scheduler_prefix n i (emit_live_slot_offers n).
  Proof.
    apply emit_live_slot_offers_then_offers.
  Qed.

  Lemma emit_live_slot_offers_contains_every_slot n (i : LiveSlot n) :
    offered_in_scheduler_prefix n i (emit_live_slot_offers n).
  Proof.
    apply emit_live_slot_offers_offers.
  Qed.

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

  Lemma offer_live_slot_now n (i : LiveSlot n)
      (t : observed_completed E) :
    <( {t}, {Obs (inl (ObsOffered (live_slot_ref i))) tt} |=
         {offer_live_slot n i} )>.
  Proof.
    unfold offer_live_slot.
    split; [reflexivity | constructor].
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

  Lemma no_focus_offers_every_live_slot_prefix n
      (v : pool E (S n)) (i : LiveSlot (S n)) :
    offered_in_scheduler_prefix (S n) i
      (schedule_with_offers (S n) v None).
  Proof.
    apply show_no_focus_offers_every_live_slot_prefix.
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

  Local Lemma observed_equ_of_observe_eq (t u : observed_completed E) :
    observe t = observe u -> t ≅ u.
  Proof.
    intro Hobserve.
    transitivity (go (observe t)).
    - apply ictree_eta.
    - rewrite Hobserve.
      symmetry. apply ictree_eta.
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
          destruct (observe (v focused_slot)) eqn:Hthread;
          fold focused_slot in Htr.
          -- destruct x.
             cbn in Htr.
             rewrite (schedule_with_offers_focused_ret
               n v focused_slot Hthread) in Htr.
             dependent destruction Htr.
             eapply scheduler_offer_shape_equ.
             ++ apply observed_equ_of_observe_eq.
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
             ++ apply observed_equ_of_observe_eq.
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
                ** apply observed_equ_of_observe_eq.
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
          destruct (observe (v focused_slot)) eqn:Hthread;
          fold focused_slot in Htr.
          -- destruct x.
             cbn in Htr.
             rewrite (schedule_with_offers_focused_ret
               n v focused_slot Hthread) in Htr.
             dependent destruction Htr.
             eapply scheduler_offer_shape_equ.
             ++ apply observed_equ_of_observe_eq.
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
             ++ apply observed_equ_of_observe_eq.
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
                ** apply observed_equ_of_observe_eq.
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
