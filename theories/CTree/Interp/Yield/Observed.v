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
  CTree.Interp.Yield.Policy
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
  schedulerObsE +' (E +' schedE).

Definition observed_completed (E B : Type -> Type) : Type :=
  ctree (scheduler_observedE E) B unit.

Section ObservedSchedulerDef.
  Context {E B : Type -> Type} `{Bn -< B}.

  (** Proof observations precede the native ND selection. A singleton pool
      selects directly; larger pools branch without adding a silent step. *)
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
                        Guard (schedule_with_offers (S (S n'))
                          ((k true :: (v @ i := (k false)))%vector)
                          (Some (Fin.FS i)))
                    end k
                | inr1 (inr1 e') =>
                    Vis (inr1 (inl1 e') : scheduler_observedE E Y)
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
            match n' as n0 return pool E B (S n0) -> observed_completed E B with
            | 0 => fun v =>
                Vis (inr1 (inr1 (Scheduled 0)) : scheduler_observedE E unit)
                  (fun _ => schedule_with_offers 1 v (Some Fin.F1))
            | S n0 => fun v =>
                Br (subevent _ (branchn (S (S n0)))) (fun i =>
                  Vis (inr1 (inr1 (Scheduled (slot_index i))) : scheduler_observedE E unit)
                    (fun _ => schedule_with_offers (S (S n0)) v (Some i)))
            end v
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
  scheduler_observedE E ~> ctree@{_ _ _ _ r _} (E +' schedE) B :=
  fun _ event =>
    match event with
    | inl1 o =>
        match o in SchedulerObs Y return ctree (E +' schedE) B Y with
        | ObsSchedulingPoint _ => Ret tt
        | ObsOffered _ => Ret tt
        end
    | inr1 event' => CTree.trigger event'
    end.

Definition forget_scheduler_offers {E B X}
    (t : ctree (scheduler_observedE E) B X)
    : ctree (E +' schedE) B X :=
  interp (M := ctree (E +' schedE) B) handle_scheduler_offers t.

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
      observe (match n as n0 return pool E B (S n0) -> observed_completed E B with
      | 0 => fun v =>
          Vis (inr1 (inr1 (Scheduled 0)) : scheduler_observedE E unit)
            (fun _ => schedule_with_offers 1 v (Some Fin.F1))
      | S n0 => fun v =>
          Br (subevent _ (branchn (S (S n0)))) (fun i =>
            Vis (inr1 (inr1 (Scheduled (slot_index i))) : scheduler_observedE E unit)
              (fun _ => schedule_with_offers (S (S n0)) v (Some i)))
      end v).
  Proof. destruct n; reflexivity. Qed.

  (** The exhausted offer prefix does not depend on the (empty) embedding. *)
  Lemma schedule_with_offers_offer_prefix_zero m
      (embed embed' : LiveSlot 0 -> LiveSlot m) (v : pool E B m) :
    schedule_with_offers_offer_prefix m 0 embed v ≅
    schedule_with_offers_offer_prefix m 0 embed' v.
  Proof. step; destruct m as [|[|m]]; cbn; reflexivity. Qed.

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
      GuardF (schedule_with_offers (S (S n))
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
      VisF (inr1 (inl1 e) : scheduler_observedE E Y)
        (fun x => schedule_with_offers (S n) (v @ i := (k x)) (Some i)).
  Proof.
    intro Hu.
    solve_focused_schedule_with_offers Hu.
  Qed.

  (** [≅]-level forms of the observed scheduler's one-node facts. *)
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
    match n as n0 return pool E B (S n0) -> observed_completed E B with
    | 0 => fun v =>
        Vis (inr1 (inr1 (Scheduled 0)) : scheduler_observedE E unit)
          (fun _ => schedule_with_offers 1 v (Some Fin.F1))
    | S n0 => fun v =>
        Br (subevent _ (branchn (S (S n0)))) (fun i =>
          Vis (inr1 (inr1 (Scheduled (slot_index i))) : scheduler_observedE E unit)
            (fun _ => schedule_with_offers (S (S n0)) v (Some i)))
    end v.
  Proof. destruct n; node_equ (schedule_with_offers_offer_prefix_zero_nonempty _ embed v). Qed.

  (** Congruence includes the offer, choice, and selected phases: source
      branches and scheduler choices have different continuations. *)
  Inductive observed_pool_rel : observed_completed E B -> observed_completed E B -> Prop :=
  | observed_pool_root n (v w : pool E B n) focus :
      pool_equ v w ->
      observed_pool_rel (schedule_with_offers n v focus) (schedule_with_offers n w focus)
  | observed_pool_offer m r embed (v w : pool E B m) :
      pool_equ v w ->
      observed_pool_rel (schedule_with_offers_offer_prefix m r embed v)
        (schedule_with_offers_offer_prefix m r embed w)
  | observed_pool_choice n (v w : pool E B (S (S n))) :
      pool_equ v w ->
      observed_pool_rel
        (Br (subevent _ (branchn (S (S n)))) (fun i =>
          Vis (inr1 (inr1 (Scheduled (slot_index i))) : scheduler_observedE E unit)
            (fun _ => schedule_with_offers (S (S n)) v (Some i))))
        (Br (subevent _ (branchn (S (S n)))) (fun i =>
          Vis (inr1 (inr1 (Scheduled (slot_index i))) : scheduler_observedE E unit)
            (fun _ => schedule_with_offers (S (S n)) w (Some i))))
  | observed_pool_selected n (v w : pool E B (S n)) i :
      pool_equ v w ->
      observed_pool_rel
        (Vis (inr1 (inr1 (Scheduled (slot_index i))) : scheduler_observedE E unit)
          (fun _ => schedule_with_offers (S n) v (Some i)))
        (Vis (inr1 (inr1 (Scheduled (slot_index i))) : scheduler_observedE E unit)
          (fun _ => schedule_with_offers (S n) w (Some i))).

  Local Lemma observed_pool_rel_step :
    observed_pool_rel <= fequ eq observed_pool_rel.
  Proof.
    intros t u Hr; change (equb eq observed_pool_rel (observe t) (observe u)).
    destruct Hr as [n v w focus Hp|m r embed v w Hp|n v w Hp|n v w i Hp].
    - destruct focus as [i|].
      + destruct n as [|n]; [inversion i|].
        assert (Hgo : go (observe (v $ i)) ≅ go (observe (w $ i)))
          by (rewrite <- !ctree_eta; apply Hp).
        destruct (observe (v $ i)) as [r| |s|g|Y e k|Y c k] eqn:Hv;
        destruct (observe (w $ i)) as [r'| |s'|g'|Y' e' k'|Y' c' k'] eqn:Hw;
          try (step in Hgo; cbn in Hgo; inversion Hgo; fail).
        * destruct r, r'.
          rewrite (schedule_with_offers_focused_ret n v i Hv),
            (schedule_with_offers_focused_ret n w i Hw).
          constructor; constructor; apply remove_pool_equ, Hp.
        * rewrite (schedule_with_offers_focused_stuck n v i Hv),
            (schedule_with_offers_focused_stuck n w i Hw); constructor.
        * apply equ_step_inv in Hgo.
          rewrite (schedule_with_offers_focused_step n v i s Hv),
            (schedule_with_offers_focused_step n w i s' Hw).
          constructor; constructor; apply replace_pool_equ; assumption.
        * apply equ_guard_inv in Hgo.
          rewrite (schedule_with_offers_focused_guard n v i g Hv),
            (schedule_with_offers_focused_guard n w i g' Hw).
          constructor; constructor; apply replace_pool_equ; assumption.
        * pose proof (equ_vis_invT _ _ _ _ Hgo) as HY; subst Y'.
          pose proof (equ_vis_invE _ _ _ _ Hgo) as [He Hk]; subst e'.
          destruct e as [y|[f|e]].
          -- destruct y.
             rewrite (schedule_with_offers_focused_yield n v i k Hv),
               (schedule_with_offers_focused_yield n w i k' Hw).
             constructor; constructor; apply replace_pool_equ; [exact Hp|apply Hk].
          -- destruct f.
             rewrite (schedule_with_offers_focused_fork n v i k Hv),
               (schedule_with_offers_focused_fork n w i k' Hw).
             constructor; constructor; apply cons_pool_equ; [apply Hk|].
             apply replace_pool_equ; [exact Hp|apply Hk].
          -- rewrite (schedule_with_offers_focused_user_event n v i e k Hv),
               (schedule_with_offers_focused_user_event n w i e k' Hw).
             constructor; intro x; constructor; apply replace_pool_equ; [exact Hp|apply Hk].
        * pose proof (equ_br_invT _ _ _ _ Hgo) as HY; subst Y'.
          pose proof (equ_br_invE _ _ _ _ Hgo) as [Hc Hk]; subst c'.
          rewrite (schedule_with_offers_focused_br n v i c k Hv),
            (schedule_with_offers_focused_br n w i c k' Hw).
          constructor; intro x; constructor; apply replace_pool_equ; [exact Hp|apply Hk].
      + destruct n as [|n].
        * rewrite !schedule_with_offers_empty_none; constructor; reflexivity.
        * rewrite !schedule_with_offers_no_focus_nonempty.
          constructor; intros []; constructor; exact Hp.
    - destruct r as [|r].
      + destruct m as [|[|m]]; cbn [schedule_with_offers_offer_prefix observe _observe].
        * constructor; reflexivity.
        * constructor; intros []; constructor; exact Hp.
        * constructor; intro i; constructor; exact Hp.
      + rewrite !schedule_with_offers_offer_prefix_succ.
        constructor; intros []; constructor; exact Hp.
    - cbn; constructor; intro i; constructor; exact Hp.
    - cbn; constructor; intros []; constructor; exact Hp.
  Qed.

  Lemma schedule_with_offers_pool_proper n (v w : pool E B n) focus :
    pool_equ v w -> schedule_with_offers n v focus ≅ schedule_with_offers n w focus.
  Proof.
    intro Hp; unfold equ; apply (leq_gfp (fequ eq) observed_pool_rel).
    - exact observed_pool_rel_step.
    - constructor; exact Hp.
  Qed.

  Lemma schedule_with_offers_focus_guards : forall a n (v : pool E B (S n)) i x,
    (v $ i) ≅ guards a x ->
    schedule_with_offers (S n) v (Some i) ≅
      guards a (schedule_with_offers (S n) (v @ i := x) (Some i)).
  Proof.
    induction a as [|a IH]; intros n v i x Hx; cbn [guards] in *.
    - apply schedule_with_offers_pool_proper.
      intro j; destruct (Fin.eq_dec j i) as [->|Hne].
      + rewrite Vector.nth_replace_eq; exact Hx.
      + rewrite Vector.nth_replace_neq by congruence; reflexivity.
    - transitivity (schedule_with_offers (S n) (v @ i := Guard (guards a x)) (Some i)).
      { apply schedule_with_offers_pool_proper.
        intro j; destruct (Fin.eq_dec j i) as [->|Hne].
        - rewrite Vector.nth_replace_eq; exact Hx.
        - rewrite Vector.nth_replace_neq by congruence; reflexivity. }
      rewrite (ctree_eta (schedule_with_offers (S n) (v @ i := Guard (guards a x)) (Some i))),
        (schedule_with_offers_focused_guard n (v @ i := Guard (guards a x)) i (guards a x)
          ltac:(rewrite Vector.nth_replace_eq; reflexivity)).
      cbn; rewrite Vector.replace_replace_eq.
      apply guard_equ_node.
      rewrite (IH n (v @ i := guards a x) i x)
        by (rewrite Vector.nth_replace_eq; reflexivity).
      rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  (** ** Erasure of the observation tier, node by node. *)

  Lemma forget_scheduler_offers_no_focus_nonempty_unfold n
      (v : pool E B (S n)) :
    forget_scheduler_offers (schedule_with_offers (S n) v None) ≅
      Guard (forget_scheduler_offers
        (schedule_with_offers_offer_prefix (S n) (S n)
          (fun i : LiveSlot (S n) => i) v)).
  Proof.
    unfold forget_scheduler_offers.
    rewrite swo_no_focus_equ, interp_vis.
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
    rewrite swo_prefix_succ_equ, interp_vis.
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
    Br (subevent _ (branchn (S n))) (fun i =>
      Vis (inr1 (Scheduled (slot_index i))) (fun _ =>
        forget_scheduler_offers (schedule_with_offers (S n) v (Some i)))).
  Proof.
    destruct n as [|n].
    - unfold forget_scheduler_offers.
      rewrite swo_prefix_zero_nonempty_equ, interp_vis.
      cbn [handle_scheduler_offers]; rewrite bind_trigger.
      symmetry; apply sb_br_l with (y := Fin.F1); intro i.
      assert (Hi : i = Fin.F1) by (dependent destruction i; [reflexivity|inversion i]).
      subst i; cbn [slot_index]. apply sb_vis; intros []; symmetry; apply sb_guard.
    - unfold forget_scheduler_offers.
      rewrite swo_prefix_zero_nonempty_equ, interp_br'.
      apply sb_br_id; intro i; rewrite sb_guard, interp_vis.
      cbn [handle_scheduler_offers]; rewrite bind_trigger.
      apply sb_vis; intros []; apply sb_guard.
  Qed.

  Lemma forget_scheduler_offers_no_focus_projection_to_focused n
      (v : pool E B (S n)) :
    forget_scheduler_offers (schedule_with_offers (S n) v None) ~
    Br (subevent _ (branchn (S n))) (fun i =>
      Vis (inr1 (Scheduled (slot_index i))) (fun _ =>
        forget_scheduler_offers (schedule_with_offers (S n) v (Some i)))).
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
    rewrite swo_empty_equ, interp_ret; reflexivity.
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
      (schedule_with_offers_focused_br n v i c k Hbr), interp_br'.
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
      (schedule_with_offers_focused_step n v i t Hs), interp_step.
    apply sb_step, sb_guard.
  Qed.

  Lemma forget_scheduler_offers_focused_fork_projection n
      (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Guard (forget_scheduler_offers (schedule_with_offers (S (S n))
      ((k true :: (v @ i := (k false)))%vector) (Some (Fin.FS i)))).
  Proof.
    intro Hfork.
    unfold forget_scheduler_offers.
    rewrite (ctree_eta (schedule_with_offers (S n) v (Some i))),
      (schedule_with_offers_focused_fork n v i k Hfork), interp_guard.
    reflexivity.
  Qed.

  Lemma forget_scheduler_offers_focused_user_event_projection n
      (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    forget_scheduler_offers (schedule_with_offers (S n) v (Some i)) ~
    Vis (inl1 e : (E +' schedE) Y)
      (fun x =>
        forget_scheduler_offers
          (schedule_with_offers (S n) (v @ i := (k x)) (Some i))).
  Proof.
    intro Huser.
    unfold forget_scheduler_offers.
    rewrite (ctree_eta (schedule_with_offers (S n) v (Some i))),
      (schedule_with_offers_focused_user_event n v i e k Huser), interp_vis.
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
    apply interp_guard.
  Qed.

  Local Lemma erased_focused_stuck_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = StuckF ->
    erased_schedule (S n) v (Some i) ≅ Stuck.
  Proof.
    intro Hst; erased_node (schedule_with_offers_focused_stuck n v i Hst).
    apply interp_stuck.
  Qed.

  Local Lemma erased_focused_br_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k :
    observe (v $ i) = BrF c k ->
    erased_schedule (S n) v (Some i) ≅
    Br c (fun j => Guard (erased_schedule (S n) (v @ i := (k j)) (Some i))).
  Proof.
    intro Hbr; erased_node (schedule_with_offers_focused_br n v i c k Hbr).
    rewrite interp_br'; reflexivity.
  Qed.

  Local Lemma erased_focused_step_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = StepF t ->
    erased_schedule (S n) v (Some i) ≅
    Step (Guard (erased_schedule (S n) (v @ i := t) (Some i))).
  Proof.
    intro Hs; erased_node (schedule_with_offers_focused_step n v i t Hs).
    apply interp_step.
  Qed.

  Local Lemma erased_focused_guard_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule (S n) (v @ i := t) (Some i)).
  Proof.
    intro Hguard; erased_node (schedule_with_offers_focused_guard n v i t Hguard).
    apply interp_guard.
  Qed.

  Local Lemma erased_focused_yield_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl1 Yield) k ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule (S n) (v @ i := (k tt)) None).
  Proof.
    intro Hyield; erased_node (schedule_with_offers_focused_yield n v i k Hyield).
    apply interp_guard.
  Qed.

  Local Lemma erased_focused_fork_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    erased_schedule (S n) v (Some i) ≅
    Guard (erased_schedule (S (S n))
      ((k true :: (v @ i := (k false)))%vector) (Some (Fin.FS i))).
  Proof.
    intro Hfork; erased_node (schedule_with_offers_focused_fork n v i k Hfork).
    apply interp_guard.
  Qed.

  Local Lemma erased_focused_user_event_equ n
      (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    erased_schedule (S n) v (Some i) ≅
    Vis (inl1 e : (E +' schedE) Y)
      (fun x => Guard (erased_schedule (S n) (v @ i := (k x)) (Some i))).
  Proof.
    intro Huser; erased_node (schedule_with_offers_focused_user_event n v i e k Huser).
    rewrite interp_vis.
    cbn [handle_scheduler_offers]; rewrite bind_trigger; reflexivity.
  Qed.

  Local Lemma forget_scheduler_offers_guards a (t : observed_completed E B) :
    forget_scheduler_offers (guards a t) ≅ guards a (forget_scheduler_offers t).
  Proof.
    induction a as [|a IH]; cbn [guards]; [reflexivity|].
    unfold forget_scheduler_offers at 1; rewrite interp_guard.
    apply guard_equ_node; exact IH.
  Qed.

  Local Lemma erased_focus_guards a n (v : pool E B (S n)) i x :
    (v $ i) ≅ guards a x ->
    erased_schedule (S n) v (Some i) ≅
      guards a (erased_schedule (S n) (v @ i := x) (Some i)).
  Proof.
    intro Hx; unfold erased_schedule.
    rewrite (schedule_with_offers_focus_guards a n v i x Hx).
    apply forget_scheduler_offers_guards.
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
      rewrite swo_prefix_succ_equ, interp_vis.
      cbn [handle_scheduler_offers]; rewrite bind_ret_l.
      apply guard_equ_node, IH.
  Qed.

  Local Definition erased_pick n (v : pool E B (S n)) : completed E B :=
    match n as n0 return pool E B (S n0) -> completed E B with
    | 0 => fun v => Vis (inr1 (Scheduled 0))
        (fun _ => Guard (erased_schedule 1 v (Some Fin.F1)))
    | S n0 => fun v => Br (subevent _ (branchn (S (S n0)))) (fun i =>
        Guard (Vis (inr1 (Scheduled (slot_index i)))
          (fun _ => Guard (erased_schedule (S (S n0)) v (Some i)))))
    end v.

  Local Lemma erased_prefix_zero_equ n embed (v : pool E B (S n)) :
    forget_scheduler_offers (schedule_with_offers_offer_prefix (S n) 0 embed v) ≅
    erased_pick n v.
  Proof.
    destruct n as [|n]; unfold forget_scheduler_offers at 1;
      rewrite swo_prefix_zero_nonempty_equ; cbn [erased_pick].
    - rewrite interp_vis; cbn [handle_scheduler_offers]; rewrite bind_trigger; reflexivity.
    - rewrite interp_br'; apply br_equ; intro i; apply guard_equ_node.
      rewrite interp_vis; cbn [handle_scheduler_offers]; rewrite bind_trigger; reflexivity.
  Qed.

  Local Lemma erased_no_focus_guards n (v : pool E B (S n)) :
    erased_schedule (S n) v None ≅ guards (S (S n)) (erased_pick n v).
  Proof.
    unfold erased_schedule at 1; rewrite forget_scheduler_offers_no_focus_nonempty_unfold.
    cbn [guards]; apply guard_equ_node.
    rewrite erased_offer_prefix_guards; apply (guards_equ (S n)), erased_prefix_zero_equ.
  Qed.

  (** The mixed-pool invariant keeps all four phases. Guard alignment is not
      composed transitively: both focused slots are normalized together. *)
  Inductive erased_offers_rel : completed E B -> completed E B -> Prop :=
  | erased_offers_at a b n (ts us : pool E B n) focus T U :
      pool_guard_equ ts us ->
      T ≅ guards a (erased_schedule n ts focus) ->
      U ≅ guards b (schedule n us focus) -> erased_offers_rel T U
  | erased_offers_offer a b n r embed (ts us : pool E B (S n)) T U :
      pool_guard_equ ts us ->
      T ≅ guards a (forget_scheduler_offers
        (schedule_with_offers_offer_prefix (S n) r embed ts)) ->
      U ≅ guards b (schedule (S n) us None) -> erased_offers_rel T U
  | erased_offers_choice a b n (ts us : pool E B (S (S n))) T U :
      pool_guard_equ ts us ->
      T ≅ guards a (erased_pick (S n) ts) ->
      U ≅ guards b (Br (subevent _ (branchn (S (S n)))) (fun i =>
        Vis (inr1 (Scheduled (slot_index i)))
          (fun _ => schedule (S (S n)) us (Some i)))) -> erased_offers_rel T U
  | erased_offers_selected a b n (ts us : pool E B (S n)) i T U :
      pool_guard_equ ts us ->
      T ≅ guards a (Vis (inr1 (Scheduled (slot_index i)))
        (fun _ => Guard (erased_schedule (S n) ts (Some i)))) ->
      U ≅ guards b (Vis (inr1 (Scheduled (slot_index i)))
        (fun _ => schedule (S n) us (Some i))) -> erased_offers_rel T U.

  Local Lemma erased_pick_step a b n (ts us : pool E B (S n)) T U :
    pool_guard_equ ts us ->
    T ≅ guards a (erased_pick n ts) ->
    U ≅ guards b (schedule (S n) us None) -> galignF erased_offers_rel T U.
  Proof.
    intros Hp ET EU; rewrite schedule_no_focus_equ in EU; destruct n as [|n].
    - apply (galignF_vis _ T U a b (inr1 (Scheduled 0) : (E +' schedE) unit)
        (fun _ => Guard (erased_schedule 1 ts (Some Fin.F1)))
        (fun _ => schedule 1 us (Some Fin.F1))); [exact ET|exact EU|].
      intros []; apply (erased_offers_at 1 0 1 ts us (Some Fin.F1));
        [exact Hp|reflexivity|reflexivity].
    - apply (galignF_br _ T U a b (subevent _ (branchn (S (S n))))
        (fun i => Guard (Vis (inr1 (Scheduled (slot_index i)))
          (fun _ => Guard (erased_schedule (S (S n)) ts (Some i)))))
        (fun i => Vis (inr1 (Scheduled (slot_index i)))
          (fun _ => schedule (S (S n)) us (Some i)))); [exact ET|exact EU|].
      intro i; apply (erased_offers_selected 1 0 (S n) ts us i);
        [exact Hp|reflexivity|reflexivity].
  Qed.

  Local Lemma erased_offers_rel_step T U :
    erased_offers_rel T U -> galignF erased_offers_rel T U.
  Proof.
    intros [a b n ts us focus T' U' Hp ET EU
      |a b n r embed ts us T' U' Hp ET EU
      |a b n ts us T' U' Hp ET EU
      |a b n ts us i T' U' Hp ET EU].
    2: { apply (erased_pick_step (a + r) b n ts us); [exact Hp| |exact EU].
         rewrite ET, erased_offer_prefix_guards, erased_prefix_zero_equ, <- guards_add; reflexivity. }
    2: { apply (galignF_br _ T' U' a b (subevent _ (branchn (S (S n))))
           (fun i => Guard (Vis (inr1 (Scheduled (slot_index i)))
             (fun _ => Guard (erased_schedule (S (S n)) ts (Some i)))))
           (fun i => Vis (inr1 (Scheduled (slot_index i)))
             (fun _ => schedule (S (S n)) us (Some i)))); [exact ET|exact EU|].
         intro i; apply (erased_offers_selected 1 0 (S n) ts us i);
           [exact Hp|reflexivity|reflexivity]. }
    2: { eapply galignF_vis; [exact ET|exact EU|].
         intros []; apply (erased_offers_at 1 0 (S n) ts us (Some i));
           [exact Hp|reflexivity|reflexivity]. }
    destruct focus as [i|].
    2: { destruct n as [|n].
         - apply (galignF_ret _ T' U' a b tt).
           + rewrite ET; apply (guards_equ a); unfold erased_schedule, forget_scheduler_offers.
             rewrite swo_empty_equ; apply interp_ret.
           + rewrite EU; apply (guards_equ b), trans_schedule_empty_ret.
         - apply (erased_pick_step (a + S (S n)) b n ts us); [exact Hp| |exact EU].
           rewrite ET, erased_no_focus_guards, <- guards_add; reflexivity. }
    destruct n as [|n]; [inversion i|].
    destruct (guard_equ_guards _ _ (Hp i)) as (p & q & x & Ex & Ey).
    pose proof (pool_guard_equ_replace ts us i x Hp) as Hp'.
    set (ts' := ts @ i := x) in *; set (us' := us @ i := x) in *.
    assert (ET' : T' ≅ guards (a + p) (erased_schedule (S n) ts' (Some i)))
      by (rewrite ET, (erased_focus_guards p n ts i x Ex), <- guards_add; reflexivity).
    assert (EU' : U' ≅ guards (b + q) (schedule (S n) us' (Some i)))
      by (rewrite EU, (schedule_focus_guards q n us i x Ey), <- guards_add; reflexivity).
    assert (Hts : observe (ts' $ i) = observe x) by (unfold ts'; now rewrite Vector.nth_replace_eq).
    assert (Hus : observe (us' $ i) = observe x) by (unfold us'; now rewrite Vector.nth_replace_eq).
    clearbody ts' us'; clear ET EU.
    destruct (observe x) as [[]| |next|g|Y e k|Y c k] eqn:Hx.
    - apply (galignF_guard _ T' U' (a + p) (b + q)
        (erased_schedule n (ts' -- i) None) (schedule n (us' -- i) None)).
      + rewrite ET', (erased_focused_ret_equ n ts' i Hts), <- guards_guard; reflexivity.
      + rewrite EU', (trans_schedule_focused_ret n us' i Hus), <- guards_guard; reflexivity.
      + apply (erased_offers_at 0 0 n (ts' -- i) (us' -- i) None);
          [apply pool_guard_equ_remove, Hp'|reflexivity|reflexivity].
    - apply (galignF_stuck _ T' U' (a + p) (b + q)).
      + rewrite ET', (erased_focused_stuck_equ n ts' i Hts); reflexivity.
      + rewrite EU', (trans_schedule_focused_stuck n us' i Hus); reflexivity.
    - apply (galignF_step _ T' U' (a + p) (b + q)
        (Guard (erased_schedule (S n) (ts' @ i := next) (Some i)))
        (schedule (S n) (us' @ i := next) (Some i))).
      + rewrite ET', (erased_focused_step_equ n ts' i next Hts); reflexivity.
      + rewrite EU', (SBisim.schedule_focused_step_equ n us' i next Hus); reflexivity.
      + apply (erased_offers_at 1 0 (S n) (ts' @ i := next) (us' @ i := next) (Some i));
          [apply pool_guard_equ_replace, Hp'|reflexivity|reflexivity].
    - apply (galignF_guard _ T' U' (a + p) (b + q)
        (erased_schedule (S n) (ts' @ i := g) (Some i))
        (schedule (S n) (us' @ i := g) (Some i))).
      + rewrite ET', (erased_focused_guard_equ n ts' i g Hts), <- guards_guard; reflexivity.
      + rewrite EU', (trans_schedule_focused_guard n us' i g Hus), <- guards_guard; reflexivity.
      + eapply (erased_offers_at 0 0 (S n) (ts' @ i := g) (us' @ i := g) (Some i));
          [apply pool_guard_equ_replace, Hp'|reflexivity|reflexivity].
    - destruct e as [y|[f|e]]; [dependent destruction y|dependent destruction f|].
      + apply (galignF_guard _ T' U' (a + p) (b + q)
          (erased_schedule (S n) (ts' @ i := k tt) None)
          (schedule (S n) (us' @ i := k tt) None)).
        * rewrite ET', (erased_focused_yield_equ n ts' i k Hts), <- guards_guard; reflexivity.
        * unfold schedule in EU' |- *.
          rewrite EU', (schedule_policy_focused_yield_equ nd_scheduler n us' i k tt Hus),
            <- guards_guard; reflexivity.
        * eapply (erased_offers_at 0 0 (S n) (ts' @ i := k tt) (us' @ i := k tt) None);
            [apply pool_guard_equ_replace, Hp'|reflexivity|reflexivity].
      + apply (galignF_guard _ T' U' (a + p) (b + q)
          (erased_schedule (S (S n)) (k true :: (ts' @ i := k false)) (Some (Fin.FS i)))
          (schedule (S (S n)) (k true :: (us' @ i := k false)) (Some (Fin.FS i)))).
        * rewrite ET', (erased_focused_fork_equ n ts' i k Hts), <- guards_guard; reflexivity.
        * unfold schedule in EU' |- *.
          rewrite EU', (schedule_policy_focused_fork_equ nd_scheduler n us' i k tt Hus),
            <- guards_guard; reflexivity.
        * eapply (erased_offers_at 0 0 (S (S n)) (k true :: (ts' @ i := k false)) (k true :: (us' @ i := k false)) (Some (Fin.FS i)));
            [apply pool_guard_equ_cons, pool_guard_equ_replace, Hp'|reflexivity|reflexivity].
      + apply (galignF_vis _ T' U' (a + p) (b + q) (inl1 e : (E +' schedE) Y)
          (fun z => Guard (erased_schedule (S n) (ts' @ i := k z) (Some i)))
          (fun z => schedule (S n) (us' @ i := k z) (Some i))).
        * rewrite ET', (erased_focused_user_event_equ n ts' i e k Hts); reflexivity.
        * unfold schedule in EU' |- *.
          rewrite EU', (schedule_policy_focused_user_event_equ nd_scheduler n us' i e k tt Hus);
            reflexivity.
        * intro z; eapply (erased_offers_at 1 0 (S n) (ts' @ i := k z) (us' @ i := k z) (Some i));
            [apply pool_guard_equ_replace, Hp'|reflexivity|reflexivity].
    - apply (galignF_br _ T' U' (a + p) (b + q) c
        (fun z => Guard (erased_schedule (S n) (ts' @ i := k z) (Some i)))
        (fun z => schedule (S n) (us' @ i := k z) (Some i))).
      + rewrite ET', (erased_focused_br_equ n ts' i c k Hts); reflexivity.
      + rewrite EU', (SBisim.schedule_focused_br_equ n us' i c k Hus); reflexivity.
      + intro z; eapply (erased_offers_at 1 0 (S n) (ts' @ i := k z) (us' @ i := k z) (Some i));
          [apply pool_guard_equ_replace, Hp'|reflexivity|reflexivity].
  Qed.

  Theorem forget_scheduler_offers_schedule_galigned n (ts us : pool E B n) focus :
    pool_guard_equ ts us ->
    galigned (forget_scheduler_offers (schedule_with_offers n ts focus)) (schedule n us focus).
  Proof.
    intro Hp; apply (galigned_coind erased_offers_rel erased_offers_rel_step).
    apply (erased_offers_at 0 0 n ts us focus); [exact Hp|reflexivity|reflexivity].
  Qed.

  Lemma forget_scheduler_offers_offer_prefix_galigned n r embed
      (ts us : pool E B (S n)) :
    pool_guard_equ ts us ->
    galigned (forget_scheduler_offers (schedule_with_offers_offer_prefix (S n) r embed ts))
      (schedule (S n) us None).
  Proof.
    intro Hp; apply (galigned_coind erased_offers_rel erased_offers_rel_step).
    apply (erased_offers_offer 0 0 n r embed ts us); [exact Hp|reflexivity|reflexivity].
  Qed.

  Theorem forget_scheduler_offers_preserves_schedule n (v : pool E B n) focus :
    forget_scheduler_offers (schedule_with_offers n v focus) ~ schedule n v focus.
  Proof.
    apply galigned_sbisim, forget_scheduler_offers_schedule_galigned.
    intro i; reflexivity.
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
