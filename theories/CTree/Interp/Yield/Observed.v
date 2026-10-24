From Stdlib Require Import
  Fin
  Vector
  Program.Equality.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  Utils.Utils
  CTree.Events.Yield
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  Utils.Vectors.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

Generalizable All Variables.

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

(** Observation events; every observation answers [unit]. *)
Variant SchedulerObs : Type -> Type :=
| ObsSchedulingPoint : nat -> SchedulerObs unit
| ObsOffered : SlotRef -> SchedulerObs unit.

Abbreviation schedulerObsE := SchedulerObs.

Definition scheduler_observedE (E : Type -> Type) : Type -> Type :=
  schedulerObsE +' (yieldE +' (spawnE +' E)).

Definition observed_completed (E B : Type -> Type) : Type :=
  ctree (scheduler_observedE E) B unit.

Section ObservedSchedulerDef.
  Context {E B : Type -> Type} `{Bn -< B}.

  (** Observed scheduler.  The only extra visible events are proof-facing
      [schedulerObsE] events at nonempty no-focus scheduling points.  The
      scheduling choice itself is the same visible [brS] as in [schedule]. *)
  CoFixpoint schedule_with_offers
      (n : nat) (v : pool E B n) (focus : option (Fin.t n))
      : observed_completed E B :=
    match focus with
    | None =>
        match n return pool E B n -> observed_completed E B with
        | 0 => fun _ => Ret tt
        | S n' => fun v =>
            Vis (inl1 (ObsSchedulingPoint (S n')))
              (fun _ : unit =>
                 schedule_with_offers_offer_prefix (S n') (S n')
                   (fun i => i) v)
        end v
    | Some i =>
        match n return pool E B n -> Fin.t n -> observed_completed E B with
        | 0 => fun _ i => match i with end
        | S n' => fun v i =>
            match observe (v $ i) with
            | RetF _ => Guard (schedule_with_offers n' (v -- i) None)
            | StuckF => Stuck
            | BrF c k =>
                Br c (fun j => schedule_with_offers (S n') (v @ i := (k j)) (Some i))
            | StepF t => Step (schedule_with_offers (S n') (v @ i := t) (Some i))
            | GuardF t => Guard (schedule_with_offers (S n') (v @ i := t) (Some i))
            | @VisF _ _ _ _ Y e k =>
                match e with
                | inl1 y =>
                    match y in yieldE Y0 return (Y0 -> thread E B) -> observed_completed E B with
                    | Yield => fun k =>
                        Guard (schedule_with_offers (S n') (v @ i := (k tt)) None)
                    end k
                | inr1 (inl1 f) =>
                    match f in forkE Y0 return (Y0 -> thread E B) -> observed_completed E B with
                    | Fork => fun k =>
                        Vis (inr1 (inr1 (inl1 Spawn)) : scheduler_observedE E unit)
                          (fun _ => schedule_with_offers (S (S n'))
                                      ((k true :: (v @ i := (k false)))%vector)
                                      (Some (Fin.FS i)))
                    end k
                | inr1 (inr1 e') =>
                    Vis (inr1 (inr1 (inr1 e')) : scheduler_observedE E Y)
                      (fun x => schedule_with_offers (S n') (v @ i := (k x)) (Some i))
                end
            end
        end v i
    end
  with schedule_with_offers_offer_prefix
      (pool_size remaining : nat)
      (embed : LiveSlot remaining -> LiveSlot pool_size)
      (v : pool E B pool_size) : observed_completed E B :=
    match remaining return
        (LiveSlot remaining -> LiveSlot pool_size) ->
        pool E B pool_size -> observed_completed E B with
    | 0 => fun _ v =>
        match pool_size return pool E B pool_size -> observed_completed E B with
        | 0 => fun _ => Ret tt
        | S n' => fun v =>
            Vis (inr1 (inl1 Yield) : scheduler_observedE E unit)
              (fun _ : unit =>
                 brS (branchn (S n')) (fun i =>
                   schedule_with_offers (S n') v (Some i)))
        end v
    | S n' => fun embed v =>
        Vis (inl1 (ObsOffered (live_slot_ref (embed Fin.F1))))
          (fun _ : unit =>
             schedule_with_offers_offer_prefix pool_size n'
               (fun i => embed (Fin.FS i)) v)
    end embed v.
End ObservedSchedulerDef.

(** Erase the observation tier.  The result universe is named for the same
    reason as the handlers of [CTree.Interp.Yield.Mod]. *)
Definition handle_scheduler_offers@{r +} {E B} :
  scheduler_observedE E ~> ctree@{_ _ _ _ r _} (yieldE +' (spawnE +' E)) B :=
  fun _ event =>
    match event with
    | inl1 o =>
        match o in SchedulerObs Y return ctree (yieldE +' (spawnE +' E)) B Y with
        | ObsSchedulingPoint _ => Ret tt
        | ObsOffered _ => Ret tt
        end
    | inr1 event' => CTree.trigger event'
    end.

Definition forget_scheduler_offers {E B X}
    (t : ctree (scheduler_observedE E) B X)
    : ctree (yieldE +' (spawnE +' E)) B X :=
  interp (M := ctree (yieldE +' (spawnE +' E)) B) handle_scheduler_offers t.

#[global] Instance forget_scheduler_offers_equ {E B X} :
  Proper (equ eq ==> equ eq) (@forget_scheduler_offers E B X).
Proof. intros t u Ht. unfold forget_scheduler_offers. now rewrite Ht. Qed.

Section ObservedScheduler.
  Context {E B : Type -> Type} `{Bn -< B}.

  (** ** One-node facts about the observed scheduler. *)

  Local Ltac solve_focused_schedule_with_offers H :=
    lazy [schedule_with_offers observe _observe];
    match type of H with
    | observe (Vector.nth ?v ?i) = _ =>
        change (@_observe _ _ unit (Vector.nth v i)) with (observe (Vector.nth v i));
        rewrite H;
        reflexivity
    end.

  Lemma schedule_with_offers_empty_none (v : pool E B 0) :
    observe (schedule_with_offers 0 v None) = RetF tt.
  Proof. reflexivity. Qed.

  Lemma schedule_with_offers_no_focus_nonempty n
      (v : pool E B (S n)) :
    observe (schedule_with_offers (S n) v None) =
      VisF (inl1 (ObsSchedulingPoint (S n)))
        (fun _ : unit =>
           schedule_with_offers_offer_prefix (S n) (S n)
             (fun i => i) v).
  Proof. reflexivity. Qed.

  Lemma schedule_with_offers_offer_prefix_succ m n
      (embed : LiveSlot (S n) -> LiveSlot m) (v : pool E B m) :
    observe (schedule_with_offers_offer_prefix m (S n) embed v) =
      VisF (inl1 (ObsOffered (live_slot_ref (embed Fin.F1))))
        (fun _ : unit =>
           schedule_with_offers_offer_prefix m n
             (fun i => embed (Fin.FS i)) v).
  Proof. reflexivity. Qed.

  Lemma schedule_with_offers_offer_prefix_zero_nonempty n
      (embed : LiveSlot 0 -> LiveSlot (S n)) (v : pool E B (S n)) :
    observe (schedule_with_offers_offer_prefix (S n) 0 embed v) =
      VisF (inr1 (inl1 Yield) : scheduler_observedE E unit)
        (fun _ : unit =>
           brS (branchn (S n)) (fun i => schedule_with_offers (S n) v (Some i))).
  Proof. reflexivity. Qed.

  (** The exhausted offer prefix does not depend on the (empty) embedding. *)
  Lemma schedule_with_offers_offer_prefix_zero m
      (embed embed' : LiveSlot 0 -> LiveSlot m) (v : pool E B m) :
    schedule_with_offers_offer_prefix m 0 embed v ≅
    schedule_with_offers_offer_prefix m 0 embed' v.
  Proof. step; destruct m; cbn; constructor; intros; reflexivity. Qed.

  Lemma schedule_with_offers_focused_ret n
      (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = RetF tt ->
    observe (schedule_with_offers (S n) v (Some i)) =
      GuardF (schedule_with_offers n (v -- i) None).
  Proof.
    intro Hret.
    solve_focused_schedule_with_offers Hret.
  Qed.

  Lemma schedule_with_offers_focused_stuck n
      (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = StuckF ->
    observe (schedule_with_offers (S n) v (Some i)) = StuckF.
  Proof.
    intro Hst.
    solve_focused_schedule_with_offers Hst.
  Qed.

  Lemma schedule_with_offers_focused_br n
      (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k :
    observe (v $ i) = BrF c k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      BrF c (fun j =>
        schedule_with_offers (S n) (v @ i := (k j)) (Some i)).
  Proof.
    intro Hbr.
    solve_focused_schedule_with_offers Hbr.
  Qed.

  Lemma schedule_with_offers_focused_step n
      (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = StepF t ->
    observe (schedule_with_offers (S n) v (Some i)) =
      StepF (schedule_with_offers (S n) (v @ i := t) (Some i)).
  Proof.
    intro Hs.
    solve_focused_schedule_with_offers Hs.
  Qed.

  Lemma schedule_with_offers_focused_guard n
      (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    observe (schedule_with_offers (S n) v (Some i)) =
      GuardF (schedule_with_offers (S n) (v @ i := t) (Some i)).
  Proof.
    intro Hg.
    solve_focused_schedule_with_offers Hg.
  Qed.

  Lemma schedule_with_offers_focused_yield n
      (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl1 Yield) k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      GuardF (schedule_with_offers (S n) (v @ i := (k tt)) None).
  Proof.
    intro Hy.
    solve_focused_schedule_with_offers Hy.
  Qed.

  Lemma schedule_with_offers_focused_fork n
      (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      VisF (inr1 (inr1 (inl1 Spawn)) : scheduler_observedE E unit)
        (fun _ => schedule_with_offers (S (S n))
          ((k true :: (v @ i := (k false)))%vector)
          (Some (Fin.FS i))).
  Proof.
    intro Hf.
    solve_focused_schedule_with_offers Hf.
  Qed.

  Lemma schedule_with_offers_focused_user_event n
      (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    observe (schedule_with_offers (S n) v (Some i)) =
      VisF (inr1 (inr1 (inr1 e)) : scheduler_observedE E Y)
        (fun x => schedule_with_offers (S n) (v @ i := (k x)) (Some i)).
  Proof.
    intro Hu.
    solve_focused_schedule_with_offers Hu.
  Qed.

  (** [≅]-level forms of the one-node facts, for both schedulers. *)
  Local Ltac node_equ H :=
    match goal with
    | |- ?t ≅ _ => rewrite (ctree_eta t), H; reflexivity
    end.

  Local Lemma swo_empty_equ (v : pool E B 0) :
    schedule_with_offers 0 v None ≅ Ret tt.
  Proof. node_equ (schedule_with_offers_empty_none v). Qed.

  Local Lemma swo_no_focus_equ n (v : pool E B (S n)) :
    schedule_with_offers (S n) v None ≅
    Vis (inl1 (ObsSchedulingPoint (S n)))
      (fun _ : unit => schedule_with_offers_offer_prefix (S n) (S n) (fun i => i) v).
  Proof. node_equ (schedule_with_offers_no_focus_nonempty n v). Qed.

  Local Lemma swo_prefix_succ_equ m n
      (embed : LiveSlot (S n) -> LiveSlot m) (v : pool E B m) :
    schedule_with_offers_offer_prefix m (S n) embed v ≅
    Vis (inl1 (ObsOffered (live_slot_ref (embed Fin.F1))))
      (fun _ : unit => schedule_with_offers_offer_prefix m n (fun i => embed (Fin.FS i)) v).
  Proof. node_equ (schedule_with_offers_offer_prefix_succ m n embed v). Qed.

  Local Lemma swo_prefix_zero_nonempty_equ n
      (embed : LiveSlot 0 -> LiveSlot (S n)) (v : pool E B (S n)) :
    schedule_with_offers_offer_prefix (S n) 0 embed v ≅
    Vis (inr1 (inl1 Yield) : scheduler_observedE E unit)
      (fun _ : unit => brS (branchn (S n)) (fun i => schedule_with_offers (S n) v (Some i))).
  Proof. node_equ (schedule_with_offers_offer_prefix_zero_nonempty n embed v). Qed.

  Local Lemma schedule_empty_equ (v : pool E B 0) :
    schedule 0 v None ≅ Ret tt.
  Proof. node_equ (schedule_empty_none v). Qed.

  Local Lemma schedule_no_focus_equ' n (v : pool E B (S n)) :
    schedule (S n) v None ≅
    Vis (inl1 Yield) (fun _ : unit => brS (branchn (S n)) (fun i => schedule (S n) v (Some i))).
  Proof. node_equ (schedule_no_focus_nonempty n v). Qed.

  Local Lemma schedule_focused_ret_equ n (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = RetF tt ->
    schedule (S n) v (Some i) ≅ Guard (schedule n (v -- i) None).
  Proof. intro Hv; node_equ (schedule_focused_ret n v i Hv). Qed.

  Local Lemma schedule_focused_stuck_equ n (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = StuckF ->
    schedule (S n) v (Some i) ≅ Stuck.
  Proof. intro Hv; node_equ (schedule_focused_stuck n v i Hv). Qed.

  Local Lemma schedule_focused_br_equ n (v : pool E B (S n)) (i : Fin.t (S n))
      {Y} (c : B Y) k :
    observe (v $ i) = BrF c k ->
    schedule (S n) v (Some i) ≅ Br c (fun j => schedule (S n) (v @ i := k j) (Some i)).
  Proof. intro Hv; node_equ (schedule_focused_br n v i c k Hv). Qed.

  Local Lemma schedule_focused_step_equ n (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = StepF t ->
    schedule (S n) v (Some i) ≅ Step (schedule (S n) (v @ i := t) (Some i)).
  Proof. intro Hv; node_equ (schedule_focused_step n v i t Hv). Qed.

  Local Lemma schedule_focused_guard_equ n (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    schedule (S n) v (Some i) ≅ Guard (schedule (S n) (v @ i := t) (Some i)).
  Proof. intro Hv; node_equ (schedule_focused_guard n v i t Hv). Qed.

  Local Lemma schedule_focused_yield_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl1 Yield) k ->
    schedule (S n) v (Some i) ≅
    Guard (schedule (S n) (v @ i := (k tt)) None).
  Proof. intro Hv; node_equ (schedule_focused_yield n v i k Hv). Qed.

  Local Lemma schedule_focused_fork_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    schedule (S n) v (Some i) ≅
    Vis (inr1 (inl1 Spawn) : (yieldE +' (spawnE +' E)) unit)
      (fun _ => schedule (S (S n)) ((k true :: (v @ i := (k false)))%vector) (Some (Fin.FS i))).
  Proof. intro Hv; node_equ (schedule_focused_fork n v i k Hv). Qed.

  Local Lemma schedule_focused_user_event_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    schedule (S n) v (Some i) ≅
    Vis (inr1 (inr1 e) : (yieldE +' (spawnE +' E)) Y)
      (fun x => schedule (S n) (v @ i := (k x)) (Some i)).
  Proof. intro Hv; node_equ (schedule_focused_user_event n v i e k Hv). Qed.

  (** ** Erasure of the observation tier, node by node. *)

  Lemma forget_scheduler_offers_no_focus_nonempty_unfold n
      (v : pool E B (S n)) :
    forget_scheduler_offers (schedule_with_offers (S n) v None) ≅
      Guard (forget_scheduler_offers
        (schedule_with_offers_offer_prefix (S n) (S n)
          (fun i : LiveSlot (S n) => i) v)).
  Proof.
    unfold forget_scheduler_offers.
    rewrite swo_no_focus_equ, interp_vis_node.
    cbn [handle_scheduler_offers]; rewrite bind_ret_l; reflexivity.
  Qed.

  Lemma forget_scheduler_offers_offer_prefix_succ_stutter m n
      (embed : LiveSlot (S n) -> LiveSlot m) (v : pool E B m) :
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix m (S n) embed v) ~
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix m n
        (fun i => embed (Fin.FS i)) v).
  Proof.
    unfold forget_scheduler_offers.
    rewrite swo_prefix_succ_equ, interp_vis_node.
    cbn [handle_scheduler_offers]; rewrite bind_ret_l.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_offer_prefix_stutter m r
      (embed : LiveSlot r -> LiveSlot m) (v : pool E B m) :
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix m r embed v) ~
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix m 0
        (fun i : LiveSlot 0 => match i with end) v).
  Proof.
    revert m embed v.
    induction r as [| r IHr]; intros m embed v.
    - rewrite (schedule_with_offers_offer_prefix_zero m embed
        (fun i : LiveSlot 0 => match i with end) v); reflexivity.
    - transitivity (forget_scheduler_offers
        (schedule_with_offers_offer_prefix m r
          (fun i => embed (Fin.FS i)) v)).
      + apply forget_scheduler_offers_offer_prefix_succ_stutter.
      + apply IHr.
  Qed.

  Lemma forget_scheduler_offers_no_focus_stutters_to_offer_prefix n
      (v : pool E B (S n)) :
    forget_scheduler_offers (schedule_with_offers (S n) v None) ~
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix (S n) (S n)
        (fun i : LiveSlot (S n) => i) v).
  Proof.
    rewrite forget_scheduler_offers_no_focus_nonempty_unfold.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_offer_prefix_zero_nonempty_unfold n
      (embed : LiveSlot 0 -> LiveSlot (S n)) (v : pool E B (S n)) :
    forget_scheduler_offers
      (schedule_with_offers_offer_prefix (S n) 0 embed v) ~
    Vis (inl1 Yield)
      (fun _ : unit =>
         brS (branchn (S n)) (fun i =>
           forget_scheduler_offers
             (schedule_with_offers (S n) v (Some i)))).
  Proof.
    unfold forget_scheduler_offers.
    rewrite swo_prefix_zero_nonempty_equ, interp_vis_node.
    cbn [handle_scheduler_offers]; rewrite bind_trigger.
    apply sb_vis; intros [].
    rewrite sb_guard, interp_br_node.
    apply sb_br_id; intro i.
    rewrite sb_guard, interp_step_node.
    apply sb_step, sb_guard.
  Qed.

  Lemma forget_scheduler_offers_no_focus_projection_to_focused n
      (v : pool E B (S n)) :
    forget_scheduler_offers (schedule_with_offers (S n) v None) ~
    Vis (inl1 Yield)
      (fun _ : unit =>
         brS (branchn (S n)) (fun i =>
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

  Lemma forget_scheduler_offers_empty_no_focus_projection
      (v : pool E B 0) :
    forget_scheduler_offers (schedule_with_offers 0 v None) ~ (Ret tt : completed E B).
  Proof.
    unfold forget_scheduler_offers.
    rewrite swo_empty_equ, interp_ret_node; reflexivity.
  Qed.

  Lemma forget_scheduler_offers_focused_br_projection n
      (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k :
    observe (v $ i) = BrF c k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Br c (fun j =>
      forget_scheduler_offers
        (schedule_with_offers (S n) (v @ i := (k j)) (Some i))).
  Proof.
    intro Hbr.
    unfold forget_scheduler_offers.
    rewrite (ctree_eta (schedule_with_offers (S n) v (Some i))),
      (schedule_with_offers_focused_br n v i c k Hbr), interp_br_node.
    apply sb_br_id; intro j.
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_focused_step_projection n
      (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = StepF t ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Step (forget_scheduler_offers
      (schedule_with_offers (S n) (v @ i := t) (Some i))).
  Proof.
    intro Hs.
    unfold forget_scheduler_offers.
    rewrite (ctree_eta (schedule_with_offers (S n) v (Some i))),
      (schedule_with_offers_focused_step n v i t Hs), interp_step_node.
    apply sb_step, sb_guard.
  Qed.

  Lemma forget_scheduler_offers_focused_fork_projection n
      (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Vis (inr1 (inl1 Spawn) : (yieldE +' (spawnE +' E)) unit)
      (fun _ =>
        forget_scheduler_offers (schedule_with_offers (S (S n))
          ((k true :: (v @ i := (k false)))%vector)
          (Some (Fin.FS i)))).
  Proof.
    intro Hfork.
    unfold forget_scheduler_offers.
    rewrite (ctree_eta (schedule_with_offers (S n) v (Some i))),
      (schedule_with_offers_focused_fork n v i k Hfork), interp_vis_node.
    cbn [handle_scheduler_offers]; rewrite bind_trigger.
    apply sb_vis; intros [].
    apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_focused_user_event_projection n
      (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Vis (inr1 (inr1 e) : (yieldE +' (spawnE +' E)) Y)
      (fun x =>
        forget_scheduler_offers
          (schedule_with_offers (S n) (v @ i := (k x)) (Some i))).
  Proof.
    intro Huser.
    unfold forget_scheduler_offers.
    rewrite (ctree_eta (schedule_with_offers (S n) v (Some i))),
      (schedule_with_offers_focused_user_event n v i e k Huser), interp_vis_node.
    cbn [handle_scheduler_offers]; rewrite bind_trigger.
    apply sb_vis; intro x.
    apply sb_guard.
  Qed.

  (** ** The erased observed scheduler is guard-aligned with [schedule]. *)

  Local Definition erased_schedule (n : nat) (v : pool E B n)
      (focus : option (Fin.t n)) : completed E B :=
    forget_scheduler_offers (schedule_with_offers n v focus).

  Local Ltac erased_node Hnode :=
    unfold erased_schedule, forget_scheduler_offers;
    rewrite (ctree_eta (schedule_with_offers _ _ _)), Hnode.

  Local Lemma erased_focused_ret_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = RetF tt ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule n (v -- i) None).
  Proof.
    intro Hret; erased_node (schedule_with_offers_focused_ret n v i Hret).
    apply interp_guard_node.
  Qed.

  Local Lemma erased_focused_stuck_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = StuckF ->
    erased_schedule (S n) v (Some i) ≅ Stuck.
  Proof.
    intro Hst; erased_node (schedule_with_offers_focused_stuck n v i Hst).
    apply interp_stuck_node.
  Qed.

  Local Lemma erased_focused_br_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k :
    observe (v $ i) = BrF c k ->
    erased_schedule (S n) v (Some i) ≅
    Br c (fun j => Guard (erased_schedule (S n) (v @ i := (k j)) (Some i))).
  Proof.
    intro Hbr; erased_node (schedule_with_offers_focused_br n v i c k Hbr).
    apply interp_br_node.
  Qed.

  Local Lemma erased_focused_step_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = StepF t ->
    erased_schedule (S n) v (Some i) ≅
    Step (Guard (erased_schedule (S n) (v @ i := t) (Some i))).
  Proof.
    intro Hs; erased_node (schedule_with_offers_focused_step n v i t Hs).
    apply interp_step_node.
  Qed.

  Local Lemma erased_focused_guard_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule (S n) (v @ i := t) (Some i)).
  Proof.
    intro Hguard; erased_node (schedule_with_offers_focused_guard n v i t Hguard).
    apply interp_guard_node.
  Qed.

  Local Lemma erased_focused_yield_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl1 Yield) k ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule (S n) (v @ i := (k tt)) None).
  Proof.
    intro Hyield; erased_node (schedule_with_offers_focused_yield n v i k Hyield).
    apply interp_guard_node.
  Qed.

  Local Lemma erased_focused_fork_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    erased_schedule (S n) v (Some i) ≅
    Vis (inr1 (inl1 Spawn) : (yieldE +' (spawnE +' E)) unit)
      (fun _ => Guard (erased_schedule (S (S n))
        ((k true :: (v @ i := (k false)))%vector)
        (Some (Fin.FS i)))).
  Proof.
    intro Hfork; erased_node (schedule_with_offers_focused_fork n v i k Hfork).
    rewrite interp_vis_node.
    cbn [handle_scheduler_offers]; rewrite bind_trigger; reflexivity.
  Qed.

  Local Lemma erased_focused_user_event_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    erased_schedule (S n) v (Some i) ≅
    Vis (inr1 (inr1 e) : (yieldE +' (spawnE +' E)) Y)
      (fun x => Guard (erased_schedule (S n) (v @ i := (k x)) (Some i))).
  Proof.
    intro Huser; erased_node (schedule_with_offers_focused_user_event n v i e k Huser).
    rewrite interp_vis_node.
    cbn [handle_scheduler_offers]; rewrite bind_trigger; reflexivity.
  Qed.

  Local Lemma erased_offer_prefix_guards :
    forall m r (embed : LiveSlot r -> LiveSlot m) (v : pool E B m),
      forget_scheduler_offers (schedule_with_offers_offer_prefix m r embed v) ≅
      guards r (forget_scheduler_offers (schedule_with_offers_offer_prefix m 0
        (fun i : LiveSlot 0 => match i with end) v)).
  Proof.
    intros m r; revert m; induction r as [|r IH]; intros m embed v.
    - cbn [guards]; now rewrite (schedule_with_offers_offer_prefix_zero m embed
        (fun i : LiveSlot 0 => match i with end) v).
    - cbn [guards]; unfold forget_scheduler_offers at 1.
      rewrite swo_prefix_succ_equ, interp_vis_node.
      cbn [handle_scheduler_offers]; rewrite bind_ret_l.
      apply guard_equ_node, IH.
  Qed.

  Local Lemma erased_no_focus_guards :
    forall n (v : pool E B (S n)),
      erased_schedule (S n) v None ≅
      guards (S (S n)) (Vis (inl1 Yield) (fun _ : unit =>
        Guard (Br (subevent _ (branchn (S n))) (fun i =>
          Guard (Step (Guard (erased_schedule (S n) v (Some i)))))))).
  Proof.
    intros n v; unfold erased_schedule at 1.
    rewrite forget_scheduler_offers_no_focus_nonempty_unfold.
    cbn [guards]; apply guard_equ_node.
    rewrite erased_offer_prefix_guards.
    apply (guards_equ (S n)).
    unfold forget_scheduler_offers.
    rewrite swo_prefix_zero_nonempty_equ, interp_vis_node.
    cbn [handle_scheduler_offers]; rewrite bind_trigger.
    apply vis_equ_node; intros []; apply guard_equ_node.
    rewrite interp_br_node; apply br_equ; intro i.
    apply guard_equ_node.
    rewrite interp_step_node; reflexivity.
  Qed.

  Local Lemma erased_offers_galigned :
    forall n (v : pool E B n) focus a b,
      galigned (guards a (erased_schedule n v focus))
               (guards b (schedule n v focus)).
  Proof.
    cofix CH; intros n v focus a b.
    destruct focus as [i|].
    - destruct n as [|n]; [inversion i|].
      destruct (observe (v $ i)) as [r| |t|t|Y e k|Y c k] eqn:Hvi.
      + destruct r.
        apply (galign_guard _ _ a b
          (erased_schedule n (v -- i) None) (schedule n (v -- i) None)).
        * rewrite <- guards_guard; apply (guards_equ a); apply erased_focused_ret_equ; exact Hvi.
        * rewrite <- guards_guard; apply (guards_equ b); apply schedule_focused_ret_equ; exact Hvi.
        * exact (CH _ _ _ 0 0).
      + apply (galign_stuck _ _ a b).
        * apply (guards_equ a); apply erased_focused_stuck_equ; exact Hvi.
        * apply (guards_equ b); apply schedule_focused_stuck_equ; exact Hvi.
      + apply (galign_step _ _ a b
          (Guard (erased_schedule (S n) (v @ i := t) (Some i)))
          (schedule (S n) (v @ i := t) (Some i))).
        * apply (guards_equ a); apply erased_focused_step_equ; exact Hvi.
        * apply (guards_equ b); apply schedule_focused_step_equ; exact Hvi.
        * exact (CH _ _ _ 1 0).
      + apply (galign_guard _ _ a b
          (erased_schedule (S n) (v @ i := t) (Some i))
          (schedule (S n) (v @ i := t) (Some i))).
        * rewrite <- guards_guard; apply (guards_equ a); apply erased_focused_guard_equ; exact Hvi.
        * rewrite <- guards_guard; apply (guards_equ b); apply schedule_focused_guard_equ; exact Hvi.
        * exact (CH _ _ _ 0 0).
      + destruct e as [yld|[frk|usr]].
        * revert k Hvi; destruct yld; intros k Hvi.
          apply (galign_guard _ _ a b
            (erased_schedule (S n) (v @ i := k tt) None)
            (schedule (S n) (v @ i := k tt) None)).
          -- rewrite <- guards_guard; apply (guards_equ a); apply erased_focused_yield_equ; exact Hvi.
          -- rewrite <- guards_guard; apply (guards_equ b); apply schedule_focused_yield_equ; exact Hvi.
          -- exact (CH _ _ _ 0 0).
        * revert k Hvi; destruct frk; intros k Hvi.
          apply (galign_vis _ _ a b (inr1 (inl1 Spawn) : (yieldE +' (spawnE +' E)) unit)
            (fun _ => Guard (erased_schedule (S (S n)) ((k true :: (v @ i := k false))%vector) (Some (Fin.FS i))))
            (fun _ => schedule (S (S n)) ((k true :: (v @ i := k false))%vector) (Some (Fin.FS i)))).
          -- apply (guards_equ a); apply erased_focused_fork_equ; exact Hvi.
          -- apply (guards_equ b); apply schedule_focused_fork_equ; exact Hvi.
          -- intros []; exact (CH _ _ _ 1 0).
        * apply (galign_vis _ _ a b (inr1 (inr1 usr) : (yieldE +' (spawnE +' E)) Y)
            (fun x => Guard (erased_schedule (S n) (v @ i := k x) (Some i)))
            (fun x => schedule (S n) (v @ i := k x) (Some i))).
          -- apply (guards_equ a); apply erased_focused_user_event_equ; exact Hvi.
          -- apply (guards_equ b); apply schedule_focused_user_event_equ; exact Hvi.
          -- intro x; exact (CH _ _ _ 1 0).
      + apply (galign_br _ _ a b c
          (fun j => Guard (erased_schedule (S n) (v @ i := k j) (Some i)))
          (fun j => schedule (S n) (v @ i := k j) (Some i))).
        * apply (guards_equ a); apply erased_focused_br_equ; exact Hvi.
        * apply (guards_equ b); apply schedule_focused_br_equ; exact Hvi.
        * intro j; exact (CH _ _ _ 1 0).
    - destruct n as [|n].
      + apply (galign_ret _ _ a b tt).
        * apply (guards_equ a); unfold erased_schedule, forget_scheduler_offers.
          rewrite swo_empty_equ; apply interp_ret_node.
        * apply (guards_equ b); apply schedule_empty_equ.
      + apply (galign_vis _ _ (a + S (S n))%nat b (inl1 Yield : (yieldE +' (spawnE +' E)) unit)
          (fun _ : unit => Guard (Br (subevent _ (branchn (S n))) (fun i =>
             Guard (Step (Guard (erased_schedule (S n) v (Some i)))))))
          (fun _ : unit => Br (subevent _ (branchn (S n))) (fun i =>
             Step (schedule (S n) v (Some i))))).
        * rewrite guards_add; apply (guards_equ a); apply erased_no_focus_guards.
        * apply (guards_equ b); apply schedule_no_focus_equ'.
        * intros [].
          apply (galign_br _ _ 1 0 (subevent _ (branchn (S n)))
            (fun i => Guard (Step (Guard (erased_schedule (S n) v (Some i)))))
            (fun i => Step (schedule (S n) v (Some i)))); [reflexivity|reflexivity|].
          intro i.
          apply (galign_step _ _ 1 0
            (Guard (erased_schedule (S n) v (Some i))) (schedule (S n) v (Some i)));
            [reflexivity|reflexivity|].
          exact (CH _ _ _ 1 0).
  Qed.

  Theorem forget_scheduler_offers_preserves_schedule
      n (v : pool E B n) focus :
    forget_scheduler_offers (schedule_with_offers n v focus) ~
    schedule n v focus.
  Proof.
    apply galigned_sbisim.
    exact (erased_offers_galigned n v focus 0 0).
  Qed.

  (** ** Every live slot is offered at a no-focus scheduling point. *)

  Inductive offered_in_scheduler_prefix (n : nat) (i : LiveSlot n)
      : observed_completed E B -> Prop :=
  | offered_prefix_here t k :
      observe t = VisF (inl1 (ObsOffered (live_slot_ref i))) k ->
      offered_in_scheduler_prefix n i t
  | offered_prefix_later t (obs : schedulerObsE unit) k :
      observe t = VisF (inl1 obs) k ->
      offered_in_scheduler_prefix n i (k tt) ->
      offered_in_scheduler_prefix n i t.

  Lemma schedule_with_offers_offer_prefix_offers m :
    forall n (embed : LiveSlot n -> LiveSlot m) (v : pool E B m)
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

  Lemma observed_equ_refl_no_eqdep (t : observed_completed E B) : t ≅ t.
  Proof.
    unfold equ.
    apply (leq_gfp (@fequ _ _ unit unit eq)
      (fun u v : observed_completed E B => u = v)).
    - intros u v <-.
      change (equb eq (fun u v : observed_completed E B => u = v) (observe u) (observe u)).
      destruct (observe u); constructor; auto.
    - reflexivity.
  Qed.

  Lemma observed_equ_step_no_eqdep (t u : observed_completed E B) :
    t ≅ u -> equb eq (equ eq) (observe t) (observe u).
  Proof.
    intro Htu. step in Htu. exact Htu.
  Qed.

  Definition equF_scheduler_vis_result
      (p q : ctree' (scheduler_observedE E) B unit) : Prop :=
    match q with
    | VisF e k_right =>
        match e with
        | inl1 sched_obs =>
            exists k_left,
              p = VisF (inl1 sched_obs) k_left /\ forall y, k_left y ≅ k_right y
        | _ => True
        end
    | _ => True
    end.

  Lemma equF_scheduler_vis_inv_no_eqdep p q :
    equb eq (equ eq) p q -> equF_scheduler_vis_result p q.
  Proof.
    intro Hf.
    destruct Hf as [x y Hxy | | t1 t2 Ht | t1 t2 Ht | Y e k1 k2 Hk | Y c k1 k2 Hk];
      cbn; try exact I.
    destruct e as [sched_obs | rest]; cbn; try exact I.
    exists k1. split; [reflexivity | exact Hk].
  Qed.

  Lemma equ_scheduler_vis_inv_from_observe_no_eqdep
      (obs : schedulerObsE unit)
      (k : unit -> observed_completed E B)
      (t u : observed_completed E B) :
    t ≅ u ->
    observe u = VisF (inl1 obs) k ->
    exists k_t, observe t = VisF (inl1 obs) k_t /\ k_t tt ≅ k tt.
  Proof.
    intros Htu Hu.
    pose proof (equF_scheduler_vis_inv_no_eqdep _ _
      (observed_equ_step_no_eqdep _ _ Htu)) as Hshape.
    rewrite Hu in Hshape.
    destruct Hshape as (k_t & Ht & Hk).
    exists k_t; split; [exact Ht | exact (Hk tt)].
  Qed.

  Inductive SchedulerEquChain :
      observed_completed E B -> observed_completed E B -> Prop :=
  | scheduler_equ_chain_refl t : SchedulerEquChain t t
  | scheduler_equ_chain_cons t u v :
      t ≅ u ->
      SchedulerEquChain u v ->
      SchedulerEquChain t v.

  Lemma scheduler_equ_chain_scheduler_vis_inv_no_eqdep
      (obs : schedulerObsE unit)
      (k : unit -> observed_completed E B)
      (t u : observed_completed E B) :
    SchedulerEquChain t u ->
    observe u = VisF (inl1 obs) k ->
    exists k_t,
      observe t = VisF (inl1 obs) k_t /\
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
      (v : pool E B (S n)) (i : LiveSlot (S n)) :
    offered_in_scheduler_prefix (S n) i
      (schedule_with_offers (S n) v None).
  Proof.
    eapply offered_prefix_later.
    - apply schedule_with_offers_no_focus_nonempty.
    - apply (schedule_with_offers_offer_prefix_offers (S n) (S n)
        (fun i => i) v i).
  Qed.

End ObservedScheduler.
