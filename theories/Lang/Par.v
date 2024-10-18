From Coq Require Import
     Program
     List
     Classes.Morphisms
     Logic.FinFun
     Logic.FunctionalExtensionality
     Logic.IndefiniteDescription
     micromega.Lia
     Init.Specif
     Fin.

From Coinduction Require Import
  coinduction rel tactics.

From Equations Require Import Equations.

From TICL Require Import
  ICTree.Core
  ICTree.Events.Writer
  Logic.Kripke
  Equ
  Logic.Trans
  Lang.Vec
  ICTree.Interp.State.

Import ListNotations.
Import ICTreeNotations.

Local Open Scope ticl_scope.
Local Open Scope ictree_scope.

Generalizable All Variables.

(** Events used to model yields and forks in our language.
    Yield is reused to label a yield after scheduling *)
Variant yieldE : Type :=
  | Yield : yieldE.

Global Instance encode_yieldE: Encode yieldE :=
  fun _ => unit. 

Variant forkE : Type :=
  | Fork : forkE.

Global Instance encode_forkE: Encode forkE :=
  fun _ => bool. 

Section parallel.
  Context `{HE: Encode E}.

  Definition thread := ictree (yieldE + forkE + E) unit.
  Definition vec n := fin n -> thread.

  (** World notation for Thread and Scheduler *)
  Notation WT := (World (yieldE + forkE + E)).
  Notation WS := (World E). 
  
  (** Relates worlds of threads to worlds of scheduler *)
  Variant world_sched_equiv: rel WS WT :=
    | WorldSchedE: forall (e: E) x,
        world_sched_equiv (Obs e x) (Obs (inr e) x)
    | WorldSchedPure:
      world_sched_equiv Pure Pure.
  
  (** Scheduling a thread pool *)
  Equations schedule_match
             (schedule : forall (n : nat), vec n -> option (fin n) -> ictree E unit)
             (n : nat)
             (v: vec n)
    : option (fin n) -> ictree E unit :=
    (* If no thread is focused, and there are none left in the pool, we are done *)
    schedule_match schedule 0 v None :=
      Ret tt;

    (* If no thread is focused, but there are some left in the pool, we pick one *)
    schedule_match schedule (S n) v None :=
      Br n (fun i' => schedule (S n) v (Some i'));

    (* If a thread is focused on, we analyze its head constructor *)
    schedule_match schedule (S n) v (Some i) with observe (v i) =>
      {
        (* If it's a [Ret], we simply remove it from the pool and focus *)
        schedule_match _ _ _ _ (RetF _) :=
          Guard (schedule n (remove_vec v i) None);

        (* If it's a [Guard], we propagate the guard and update the thread *)
        schedule_match _ _ _ _ (GuardF t') :=
          Guard (schedule (S n) (replace_vec v i t') (Some i));
        
        (* If it's a [Br], we propagate the br and update the thread *)
        schedule_match _ _ _ _ (BrF n' k) :=
          Br n' (fun i' => schedule (S n) (replace_vec v i (k i')) (Some i));

        (* If it's a [Yield], we remove the focus *)
        schedule_match _ _ _ _ (VisF (inl (inl Yield)) k) :=
          Guard (schedule (S n) (replace_vec v i (k tt)) None);
        
        (* If it's a [Fork], we extend the pool *)
        schedule_match _ _ _ _ (VisF (inl (inr Fork)) k) :=
          step
            (schedule
               (S (S n))
               (* Note that [cons_vec] puts the new thread on the front of the vector *)
               (cons_vec (k true) (replace_vec v i (k false)))
               (* We stay with the old thread; we don't yield at a fork *)
               (Some (FS i)));
        
        (* Other events are not touched in scheduling *)
        schedule_match _ _ _ _ (VisF (inr e) k) :=
          Vis e (fun x => schedule (S n) (replace_vec v i (k x)) (Some i))
      }.
  
  (* Transparent schedule_match. *)
  CoFixpoint schedule := schedule_match schedule.

  Lemma unfold_schedule n v i : schedule n v i ≅ schedule_match schedule n v i.
  Proof.
    step; cbn; eauto.
  Qed.

  #[global] Instance equ_schedule n :
    Proper ((pwr (equ eq)) ==> pwr (equ eq)) (schedule n).
  Proof.
    cbn. revert n.
    coinduction r CIH. intros n v1 v2 Hv i.
    do 2 rewrite unfold_schedule.
    destruct i as [i |].
    2: {
      destruct n; auto. constructor. intros.
      apply CIH; auto.
    }
    destruct n as [| n]; auto.
    pose proof (Hv i).
    simp schedule_match.
    step in H; cbn in H. inv H; eauto.
    2: destruct e.
    2: destruct s.
    all: cbn.
    - clear H0 H1. destruct y; cbn in *; auto.
      constructor. intros. apply CIH.
      apply remove_vec_relation; auto.
    - clear H0 H1. destruct y.
      constructor. intros. eapply CIH.
      apply replace_vec_relation; auto.
      apply H2.
    - destruct f. constructor. intros. eapply CIH.
      apply cons_vec_relation; auto.
      + apply H2.
      + apply replace_vec_relation; auto.
        apply H2.
    - constructor. intros. apply CIH.
      apply replace_vec_relation; auto.
      apply H2.
    - constructor. intros. apply CIH.
      apply replace_vec_relation; auto.
    - constructor. intros. apply CIH.
      apply replace_vec_relation; auto.
      apply H2.
  Qed.

  (*** how the scheduler behaves affects a thread ***)  
  (** inverting the case when a [schedule] is a [BrD] *)
  Lemma guard_schedule_inv t n (v : vec n) i :
    Guard t ≅ schedule n v (Some i) ->
    (* 1. Return thread *)
    (exists n' H1, v i ≅ Ret tt /\
                t ≅ schedule n' (remove_vec_helper n n' v i H1) None) \/
    (* 2. Guarded focused thread *)
    (exists t', v i ≅ Guard t' /\
             t ≅ schedule n (replace_vec v i t') (Some i)) \/
    (* 3. Yield *)
    (exists k', v i ≅ Vis (inl (inl Yield)) k' /\
             t ≅ schedule n (replace_vec v i (k' tt)) None).
  Proof.
    intros Hequ.
    rewrite unfold_schedule in Hequ.
    destruct n as [| n]. 
    - inv i.
    - rewrite ictree_eta in Hequ.
      simp schedule_match in Hequ.
      destruct (observe (Guard t)) eqn:Heqt;
        desobs (v i); cbn in Hequ;
        step in Hequ; cbn in Hequ; dependent destruction Hequ; inv Heqt.
      + destruct x.
        left.        
        exists n, eq_refl; intuition.
        rewrite (ictree_eta (v i)), Heqt0; reflexivity.
      + right. left.
        exists t1; intuition.
        rewrite (ictree_eta (v i)), Heqt0; reflexivity.
      + destruct e eqn:He; try destruct s; try destruct y; try destruct f;
          cbn in x; inv x.                                                               
        right. right. 
        exists k; intuition.
        rewrite (ictree_eta (v i)), Heqt0; reflexivity.
  Qed.

  (** Helper lemmas for when [schedule] transitions to [done] *)
  Lemma ktrans_schedule_done_1 w w' n v i (t: ictree E unit) R:
    [schedule n v (Some i), w] ↦ [t, w'] ->
    done_with (X:=unit) R w' ->    
    n = 1%nat.
  Proof.
    intros.
    cbn in H.
    remember (observe (schedule n v (Some i))).
    pose proof (ictree_eta (go (observe (schedule n v (Some i))))) as Eqt.
    rewrite <- Heqi0 in Eqt at 1. cbn in Eqt. clear Heqi0.    
    remember (observe t).
    revert n t v i R Eqt Heqi1 H0.
    induction H; intros; try inv Heqi1; subst.
    - rewrite <- ictree_eta in Eqt.
      apply guard_schedule_inv in Eqt.
      destruct Eqt as [? | [? | ?]].
      + (* Ret *)
        destruct H1 as (n'' & Hn2' & Hvic & Hk).
        destruct n''; auto.
        rewrite unfold_schedule in Hk.
        simp schedule_match in Hk.        
        rewrite Hk in H.
        ddestruction H.
        inv H; inv H1.
      + (* Guarded focuses *)
        destruct H1 as (t_ & Ht_ & Ht).
        destruct n; try solve [inv i].
        destruct (observe (v i)) eqn:Hv; cbn in H;
          step in Ht_; cbn in Ht_; rewrite Hv in Ht_; inv Ht_.
        eapply IHktrans_ with (v:=replace_vec v i t_) (i:=i); eauto.
        now rewrite <- ?ictree_eta.
      + (* Vis (Yield) *)
        destruct H1 as (k_ & Hv & Ht).
        destruct n; try solve [inv i].
        rewrite unfold_schedule in Ht.
        simp schedule_match in Ht.
        rewrite Ht in H.
        ddestruction H.
        inv H; inv H1.
    - inv H; inv H1.
    - inv H1.
    - destruct n; try solve [inv i].
      rewrite unfold_schedule in Eqt.
      simp schedule_match in Eqt.      
      destruct (observe (v i)) eqn:Hv; cbn in Eqt;
        step in Eqt; cbn in Eqt; inv Eqt.
      destruct e; destruct y; [destruct s; [destruct y| destruct f] |]; inv H3.
    - destruct n; try solve [inv i].
      rewrite unfold_schedule in Eqt.
      simp schedule_match in Eqt.      
      destruct (observe (v0 i)) eqn:Hv; cbn in Eqt;
        step in Eqt; cbn in Eqt; inv Eqt.
      destruct e0; [destruct s; [destruct y0| destruct f]|]; inv H3.
  Qed.

  Opaque ICtree.stuck.
  Lemma ktrans_schedule_thread_done (ws ws': WS) (wt wt': WT) v i (t: ictree E unit):
    [schedule 1%nat v (Some i), ws] ↦ [t, ws'] ->    
    world_sched_equiv ws wt ->
    done_of tt ws ws' ->
    done_of tt wt wt' ->
    [v i, wt] ↦ [ICtree.stuck, wt'].
  Proof.
    intros.
    unfold ktrans in *.
    cbn in *. 
    remember (observe (schedule 1 v (Some i))).
    pose proof (ictree_eta (go (observe (schedule 1 v (Some i))))).
    rewrite <- Heqi0 in H3 at 1. cbn in H3. clear Heqi0.
    remember (observe t).
    revert t v i  Heqi1 H0 H1 H2 H3.
    induction H; intros t_ v' i' x' Heqw Hws Hwt Hequ. 
    - rewrite <- ictree_eta in Hequ. 
      apply guard_schedule_inv in Hequ.
      destruct Hequ as [? | [? | ?]].
      + (* Ret *)
        destruct H0 as (k' & Hvic & Hv & Hk).
        ddestruction Hvic.
        rewrite Hv; cbn.
        inv Heqw; ddestruction Hws; ddestruction Hwt; now constructor.
      + (* Guard *)
        destruct H0 as (t'' & Hvic & Hk).
        rewrite Hk in H.
        destruct (observe (v' i')) eqn:Hv'; cbn in H.
        * destruct x.
          inv Heqw; ddestruction Hws; ddestruction Hwt; now constructor.
        * step in Hvic; cbn in Hvic; rewrite Hv' in Hvic; inv Hvic.
        * step in Hvic; cbn in Hvic; rewrite Hv' in Hvic; inv Hvic.
          rewrite (ictree_eta t), (ictree_eta (schedule 1 (replace_vec v' i' t'') (Some i'))) in Hk.
          inv Heqw; ddestruction Hws; ddestruction Hwt; econstructor. 
          -- specialize (IHktrans_  t_ (replace_vec v' i' t'') i' x' (WorldSchedE _ _) (ObsWithFinish _ _ _) (ObsWithFinish _ _ _) Hk).
             rewrite replace_vec_eq in IHktrans_.
             now rewrite H2.
          -- specialize (IHktrans_  t_ (replace_vec v' i' t'') i' x' WorldSchedPure (PureWithDone _) (PureWithDone _) Hk). 
             rewrite replace_vec_eq in IHktrans_.
             now rewrite H2.
        * step in Hvic; cbn in Hvic; rewrite Hv' in Hvic; inv Hvic.
      + (* Yield *)
        destruct H0 as (k' & Hvic & Hk).
        rewrite Hk in H.
        rewrite unfold_schedule in H.
        simp schedule_match in H.
        ddestruction H.
        inv Hws.
    - inv Hws. 
    - rewrite unfold_schedule in Hequ.
      simp schedule_match in Hequ.
      destruct (observe (v' i')) eqn:Hv; cbn in Hequ;
        step in Hequ; cbn in Hequ; ddestruction Hequ.
      destruct e0; [destruct s; [destruct y| destruct f] |]; inv Hws.
    - rewrite unfold_schedule in Hequ.
      simp schedule_match in Hequ.
      destruct (observe (v' i')) eqn:Hv; cbn in Hequ;
        step in Hequ; cbn in Hequ; ddestruction Hequ.
      destruct e; [destruct s; [destruct y| destruct f] |]; ddestruction Hws; inv x.
    - rewrite unfold_schedule in Hequ.
      simp schedule_match in Hequ.
      destruct (observe (v' i')) eqn:Hv; cbn in Hequ;
        step in Hequ; cbn in Hequ; ddestruction Hequ.
      destruct e0; [destruct s; [destruct y| destruct f] |]; ddestruction Hws; inv x.      
  Qed.

End parallel.
