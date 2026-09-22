From Stdlib Require Import
  Fin
  Vector
  Morphisms.

From TICL Require Import
  Classes
  Events.Core
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Interp.Core
  ICTree.Interp.State.Mod
  ICTree.Events.Yield
  ICTree.Events.State
  ICTree.Events.Writer
  Utils.Vectors.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

Generalizable All Variables.

(** * Cooperative scheduling over raw [ictree] pools *)
(** This module is language independent.  It owns the cooperative scheduler,
    the event-erasure handlers, and the instrumentation algebra that lifts a
    raw thread or a raw scheduled pool into the writer-instrumented view. *)

Section Scheduler.
  Context {E : Type} `{Encode E}.

  (** Cooperative scheduler for a finite pool.

      [None] focus means the scheduler chooses a runnable thread after emitting
      a scheduling [Yield].  [Some i] observes one step of thread [i], removing
      finished threads, clearing focus on source yields, and turning source forks
      into scheduler-visible [Spawn] events. *)
  CoFixpoint schedule (n : nat) (v : pool E n) (focus : option (Fin.t n)) : completed E :=
    match focus with
    | None =>
        match n return pool E n -> completed E with
        | 0 => fun _ => Ret tt
        | S n' => fun v => Vis (inl Yield) (fun _ => Br n' (fun i => schedule (S n') v (Some i)))
        end v
    | Some i =>
        match n return pool E n -> Fin.t n -> completed E with
        | 0 => fun _ i => match i with end
        | S n' => fun v i =>
            match observe (v $ i) with
            | RetF _ => Guard (schedule n' (v -- i) None)
            | BrF b k => Br b (fun j => schedule (S n') (v @ i := (k j)) (Some i))
            | GuardF t => Guard (schedule (S n') (v @ i := t) (Some i))
            | VisF e k =>
                match e as e0 return (encode e0 -> thread E) -> completed E with
                | inl Yield => fun k => Guard (schedule (S n') (v @ i := (k tt)) None)
                | inr (inl Fork) => fun k =>
                    @go (yieldE + (spawnE + E)) _ unit
                      (VisF ((inr (inl Spawn)) : yieldE + (spawnE + E))
                         (fun _ => schedule (S (S n'))
                                     ((k true :: (v @ i := (k false)))%vector)
                                     (Some (FS i))))
                | inr (inr e') => fun k =>
                    @go (yieldE + (spawnE + E)) _ unit
                      (VisF ((inr (inr e')) : yieldE + (spawnE + E))
                         (fun x => schedule (S n') (v @ i := (k x)) (Some i)))
                end k
            end
        end v i
    end.
End Scheduler.

(** * Event erasure handlers *)

(** Erase scheduler spawn observations while preserving yield and user events. *)
Definition handle_spawn {E} `{HE : Encode E} :
  (yieldE + (spawnE + E)) ~> ictree (yieldE + E) :=
  fun event =>
    match event with
    | inl y => ICtree.trigger y
    | inr (inl Spawn) => Ret tt
    | inr (inr m) => ICtree.trigger m
    end.

Definition interp_spawn {E} `{HE : Encode E} {X}
    (t : ictree (yieldE + (spawnE + E)) X) : ictree (yieldE + E) X :=
  interp handle_spawn t.

(** Erase cooperative yield observations, leaving only user events. *)
Definition handle_yield {E} `{HE : Encode E} : (yieldE + E) ~> ictree E :=
  fun event =>
    match event with
    | inl Yield => Ret tt
    | inr m => ICtree.trigger m
    end.

Definition interp_yield {E} `{HE : Encode E} {X}
    (t : ictree (yieldE + E) X) : ictree E X :=
  interp handle_yield t.

(** Interpret a raw thread without scheduling by resolving [Fork] to [false],
    so a standalone thread behaves as the parent path and never starts the
    fork body. *)
Definition handle_thread {E} `{HE : Encode E} :
  (yieldE + (forkE + E)) ~> ictree (yieldE + E) :=
  fun event =>
    match event with
    | inl y => ICtree.trigger y
    | inr (inl Fork) => Ret false
    | inr (inr m) => ICtree.trigger m
    end.

Definition interp_thread {E} `{HE : Encode E} {X}
    (t : ictree (yieldE + (forkE + E)) X) : ictree E X :=
  interp_yield (interp handle_thread t).

(** The erasure interpreters are [equ]-congruences; this lets structural
    equations be rewritten underneath them. *)
#[global] Instance interp_spawn_equ {E} `{HE : Encode E} {X} :
  Proper (equ eq ==> equ eq) (@interp_spawn E HE X).
Proof. intros t u Ht. unfold interp_spawn. now rewrite Ht. Qed.

#[global] Instance interp_yield_equ {E} `{HE : Encode E} {X} :
  Proper (equ eq ==> equ eq) (@interp_yield E HE X).
Proof. intros t u Ht. unfold interp_yield. now rewrite Ht. Qed.

#[global] Instance interp_thread_equ_proper {E} `{HE : Encode E} {X} :
  Proper (equ eq ==> equ eq) (@interp_thread E HE X).
Proof. intros t u Ht. unfold interp_thread, interp_yield. now rewrite Ht. Qed.

(** Erasure handlers intentionally hide scheduler/thread observations. *)
Lemma handle_spawn_spawn_erased {E} {HE : Encode E} :
  @handle_spawn E HE (inr (inl Spawn)) = Ret tt.
Proof. reflexivity. Qed.

Lemma handle_yield_yield_erased {E} {HE : Encode E} :
  @handle_yield E HE (inl Yield) = Ret tt.
Proof. reflexivity. Qed.

(** * Scheduler one-step/case regression facts. *)
Section SchedulerFacts.
  Context {E : Type} `{Encode E}.

  Local Ltac solve_focused_schedule H :=
    lazy [schedule observe _observe];
    match type of H with
    | observe (Vector.nth ?v ?i) = _ =>
        change (@_observe _ _ unit (Vector.nth v i)) with (observe (Vector.nth v i));
        rewrite H;
        reflexivity
    end.

  Lemma schedule_empty_none (v : pool E 0) :
    observe (schedule 0 v None) = RetF tt.
  Proof. reflexivity. Qed.

  Lemma schedule_no_focus_nonempty n (v : pool E (S n)) :
    observe (schedule (S n) v None) =
      VisF (inl Yield) (fun _ => Br n (fun i => schedule (S n) v (Some i))).
  Proof. reflexivity. Qed.

  Lemma schedule_focused_ret n (v : pool E (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = RetF tt ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule n (v -- i) None).
  Proof.
    intro Hret.
    solve_focused_schedule Hret.
  Qed.

  Lemma schedule_focused_br n (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v $ i) = BrF b k ->
    observe (schedule (S n) v (Some i)) =
      BrF b (fun j => schedule (S n) (v @ i := (k j)) (Some i)).
  Proof.
    intro Hbr.
    solve_focused_schedule Hbr.
  Qed.

  Lemma schedule_focused_guard n (v : pool E (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S n) (v @ i := t) (Some i)).
  Proof.
    intro Hg.
    solve_focused_schedule Hg.
  Qed.

  Lemma schedule_focused_yield n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl Yield) k ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S n) (v @ i := (k tt)) None).
  Proof.
    intro Hy.
    solve_focused_schedule Hy.
  Qed.

  Lemma schedule_focused_fork n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr (inl Fork)) k ->
    observe (schedule (S n) v (Some i)) =
      VisF ((inr (inl Spawn)) : yieldE + (spawnE + E))
        (fun _ => schedule (S (S n))
                    ((k true :: (v @ i := (k false)))%vector)
                    (Some (Fin.FS i))).
  Proof.
    intro Hf.
    solve_focused_schedule Hf.
  Qed.

  Lemma schedule_focused_user_event n (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v $ i) = VisF (inr (inr e)) k ->
    observe (schedule (S n) v (Some i)) =
      VisF ((inr (inr e)) : yieldE + (spawnE + E))
        (fun x => schedule (S n) (v @ i := (k x)) (Some i)).
  Proof.
    intro Hu.
    solve_focused_schedule Hu.
  Qed.
End SchedulerFacts.

(** * Non-degenerate finite-pool scheduler regressions. *)
Section SchedulerPoolRegressions.
  Context {E : Type} `{Encode E}.

  Lemma schedule_yield_two_threads_one_step (next other : thread E) :
    observe
      (schedule 2
         [Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next);
          other]%vector
         (Some Fin.F1)) =
      GuardF
        (schedule 2
           ([Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next);
             other]%vector @ Fin.F1 := next)
           None).
  Proof. reflexivity. Qed.

  Lemma schedule_yield_two_threads_focused_slot (next other : thread E) :
    (([Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next);
       other]%vector @ Fin.F1 := next) $ Fin.F1) = next.
  Proof. apply Vector.nth_replace_eq. Qed.

  Lemma schedule_yield_two_threads_other_slot (next other : thread E) :
    (([Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next);
       other]%vector @ Fin.F1 := next) $ (Fin.FS Fin.F1)) = other.
  Proof.
    rewrite Vector.nth_replace_neq by discriminate.
    reflexivity.
  Qed.

  Lemma schedule_fork_two_threads_one_step
      (child parent other : thread E) :
    observe
      (schedule 2
         [Vis ((inr (inl Fork)) : yieldE + (forkE + E))
            (fun in_child : bool => if in_child then child else parent);
          other]%vector
         (Some Fin.F1)) =
      VisF ((inr (inl Spawn)) : yieldE + (spawnE + E))
        (fun _ =>
           schedule 3
             ((child ::
               ([Vis ((inr (inl Fork)) : yieldE + (forkE + E))
                   (fun in_child : bool => if in_child then child else parent);
                 other]%vector @ Fin.F1 := parent))%vector)
             (Some (Fin.FS Fin.F1))).
  Proof. reflexivity. Qed.

  Lemma schedule_fork_two_threads_child_slot
      (child parent other : thread E) :
    (((child ::
       ([Vis ((inr (inl Fork)) : yieldE + (forkE + E))
           (fun in_child : bool => if in_child then child else parent);
         other]%vector @ Fin.F1 := parent))%vector) $ Fin.F1) = child.
  Proof. reflexivity. Qed.

  Lemma schedule_fork_two_threads_parent_slot
      (child parent other : thread E) :
    (((child ::
       ([Vis ((inr (inl Fork)) : yieldE + (forkE + E))
           (fun in_child : bool => if in_child then child else parent);
         other]%vector @ Fin.F1 := parent))%vector) $ (Fin.FS Fin.F1)) = parent.
  Proof. apply Vector.nth_replace_eq. Qed.

  Lemma schedule_fork_two_threads_other_slot
      (child parent other : thread E) :
    (((child ::
       ([Vis ((inr (inl Fork)) : yieldE + (forkE + E))
           (fun in_child : bool => if in_child then child else parent);
         other]%vector @ Fin.F1 := parent))%vector)
      $ (Fin.FS (Fin.FS Fin.F1))) = other.
  Proof.
    change ((([Vis ((inr (inl Fork)) : yieldE + (forkE + E))
                 (fun in_child : bool => if in_child then child else parent);
               other]%vector @ Fin.F1 := parent) $ (Fin.FS Fin.F1)) = other).
    rewrite Vector.nth_replace_neq by discriminate.
    reflexivity.
  Qed.
End SchedulerPoolRegressions.

(** * Raw instrumentation entry points *)

(** Instrument a standalone raw thread: erase [Fork] to the parent branch and
    erase cooperative [Yield], then instrument the residual state effects. *)
Definition instr_thread {Σ X}
    (t : ictree (yieldE + (forkE + stateE Σ)) X) (σ : Σ)
    : ictreeW Σ (X * Σ) :=
  instr_stateE (interp_thread t) σ.

(** Instrument a scheduled pool: erase scheduler [Spawn] and cooperative
    [Yield] observations, then instrument the residual state effects. *)
Definition instr_schedule {Σ} (n : nat) (v : pool (stateE Σ) n)
    (focus : option (Fin.t n)) (σ : Σ) : ictreeW Σ (unit * Σ) :=
  instr_stateE (interp_yield (interp_spawn (schedule n v focus))) σ.

(** ** Structural [interp] and [equ] equations used by the erasure algebra. *)
Lemma interp_ret_node `{Encode E} `{Encode F} {X}
    (h : E ~> ictree F) (x : X) :
  interp h (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp; reflexivity. Qed.

Lemma interp_guard_node `{Encode E} `{Encode F} {X}
    (h : E ~> ictree F) (t : ictree E X) :
  interp h (Guard t) ≅ Guard (interp h t).
Proof. rewrite unfold_interp; reflexivity. Qed.

Lemma interp_br_node `{Encode E} `{Encode F} {X}
    (h : E ~> ictree F) n (k : fin' n -> ictree E X) :
  interp h (Br n k) ≅ Br n (fun i => Guard (interp h (k i))).
Proof. rewrite unfold_interp; reflexivity. Qed.

Lemma interp_vis_node `{Encode E} `{Encode F} {X}
    (h : E ~> ictree F) (e : E) (k : encode e -> ictree E X) :
  interp h (Vis e k) ≅ h e >>= (fun x => Guard (interp h (k x))).
Proof. rewrite unfold_interp; reflexivity. Qed.

Lemma guard_equ_node `{Encode E} {X} (t u : ictree E X) :
  t ≅ u -> Guard t ≅ Guard u.
Proof. intro Ht. step. constructor. exact Ht. Qed.

Lemma vis_equ_node `{Encode E} {X} (e : E) (k1 k2 : encode e -> ictree E X) :
  (forall x, k1 x ≅ k2 x) -> Vis e k1 ≅ Vis e k2.
Proof. intro Hk. step. constructor. exact Hk. Qed.

Local Ltac erase_resum :=
  unfold resum, resum_ret,
    ReSum_inl, ReSum_inr, ReSum_refl,
    ReSumRet_inl, ReSumRet_inr, ReSumRet_refl.

(** ** Composed erasure equations for a single raw thread node. *)

Lemma interp_thread_yield_node {E} `{Encode E} {X}
    (k : unit -> ictree (yieldE + (forkE + E)) X) :
  interp_thread (Vis (inl Yield) k) ≅ Guard (Guard (interp_thread (k tt))).
Proof.
  unfold interp_thread, interp_yield.
  rewrite interp_vis_node.
  cbn [handle_thread].
  unfold ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  erase_resum.
  rewrite interp_vis_node.
  cbn [handle_yield].
  rewrite bind_ret_l.
  apply guard_equ_node.
  rewrite interp_guard_node.
  reflexivity.
Qed.

Lemma interp_thread_fork_node {E} `{Encode E} {X}
    (k : bool -> ictree (yieldE + (forkE + E)) X) :
  interp_thread (Vis (inr (inl Fork)) k) ≅ Guard (interp_thread (k false)).
Proof.
  unfold interp_thread, interp_yield.
  rewrite interp_vis_node.
  cbn [handle_thread].
  rewrite bind_ret_l.
  rewrite interp_guard_node.
  reflexivity.
Qed.

Lemma interp_thread_user_node {E} `{Encode E} {X} (m : E)
    (k : encode m -> ictree (yieldE + (forkE + E)) X) :
  interp_thread (Vis (inr (inr m)) k)
    ≅ Vis m (fun x => Guard (Guard (interp_thread (k x)))).
Proof.
  unfold interp_thread, interp_yield.
  rewrite interp_vis_node.
  cbn [handle_thread].
  unfold ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  erase_resum.
  rewrite interp_vis_node.
  cbn [handle_yield].
  unfold ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  erase_resum.
  apply vis_equ_node; intro x.
  apply guard_equ_node.
  rewrite interp_guard_node.
  reflexivity.
Qed.

(** ** Instrumentation algebra for raw threads. *)

#[global] Instance instr_thread_equ {Σ X} :
  Proper (equ eq ==> eq ==> equ eq) (@instr_thread Σ X).
Proof.
  intros t t' Ht σ σ' <-.
  unfold instr_thread, interp_thread, interp_yield, instr_stateE.
  now rewrite Ht.
Qed.

Lemma instr_thread_ret {Σ X} (x : X) (σ : Σ) :
  instr_thread (Ret x) σ ≅ Ret (x, σ).
Proof.
  unfold instr_thread, interp_thread, interp_yield, instr_stateE.
  rewrite interp_ret_node, interp_ret_node.
  apply interp_state_ret.
Qed.

Lemma instr_thread_bind {Σ A B}
    (t : ictree (yieldE + (forkE + stateE Σ)) A)
    (k : A -> ictree (yieldE + (forkE + stateE Σ)) B) (σ : Σ) :
  instr_thread (t >>= k) σ
    ≅ (instr_thread t σ >>= fun '(x, σ') => instr_thread (k x) σ').
Proof.
  unfold instr_thread, interp_thread, interp_yield, instr_stateE.
  rewrite !interp_bind_hetero.
  apply interp_state_bind.
Qed.

Lemma instr_thread_yield {Σ X}
    (k : unit -> ictree (yieldE + (forkE + stateE Σ)) X) (σ : Σ) :
  instr_thread (Vis (inl Yield) k) σ ~ instr_thread (k tt) σ.
Proof.
  unfold instr_thread, instr_stateE.
  rewrite interp_thread_yield_node.
  rewrite interp_state_tau, sb_guard, interp_state_tau, sb_guard.
  reflexivity.
Qed.

Lemma instr_thread_fork {Σ X}
    (k : bool -> ictree (yieldE + (forkE + stateE Σ)) X) (σ : Σ) :
  instr_thread (Vis (inr (inl Fork)) k) σ ~ instr_thread (k false) σ.
Proof.
  unfold instr_thread, instr_stateE.
  rewrite interp_thread_fork_node.
  rewrite interp_state_tau, sb_guard.
  reflexivity.
Qed.

Lemma instr_thread_get {Σ X}
    (k : Σ -> ictree (yieldE + (forkE + stateE Σ)) X) (σ : Σ) :
  instr_thread (Vis (inr (inr Get)) k) σ ~ instr_thread (k σ) σ.
Proof.
  unfold instr_thread, instr_stateE.
  rewrite interp_thread_user_node.
  rewrite interp_state_vis.
  cbn [h_stateW runStateT].
  rewrite bind_ret_l, sb_guard.
  rewrite interp_state_tau, sb_guard, interp_state_tau, sb_guard.
  reflexivity.
Qed.

Lemma instr_thread_put {Σ X} (σ' : Σ)
    (k : unit -> ictree (yieldE + (forkE + stateE Σ)) X) (σ : Σ) :
  instr_thread (Vis (inr (inr (Put σ'))) k) σ
    ~ (log σ';; instr_thread (k tt) σ').
Proof with eauto.
  unfold instr_thread, instr_stateE.
  rewrite interp_thread_user_node.
  rewrite interp_state_vis.
  cbn [h_stateW runStateT].
  rewrite bind_bind.
  __upto_bind_sbisim...
  intros [].
  rewrite bind_ret_l, sb_guard.
  rewrite interp_state_tau, sb_guard, interp_state_tau, sb_guard.
  reflexivity.
Qed.

(** ** Composed erasure equations for a single scheduled node. *)
(** [interp_yield (interp_spawn _)] is the erased view of a scheduled pool:
    scheduler [Spawn] and cooperative [Yield] observations are removed, and the
    residual user events are preserved. *)

Lemma interp_erase_ret {E} `{Encode E} {X} (x : X) :
  interp_yield (interp_spawn (Ret x : ictree (yieldE + (spawnE + E)) X)) ≅ Ret x.
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_ret_node, interp_ret_node.
  reflexivity.
Qed.

Lemma interp_erase_guard {E} `{Encode E} {X}
    (t : ictree (yieldE + (spawnE + E)) X) :
  interp_yield (interp_spawn (Guard t)) ≅ Guard (interp_yield (interp_spawn t)).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_guard_node, interp_guard_node.
  reflexivity.
Qed.

Lemma interp_erase_guard_ret {E} `{Encode E} {X} (x : X) :
  interp_yield (interp_spawn (Guard (Ret x) : ictree (yieldE + (spawnE + E)) X))
    ≅ Guard (Ret x).
Proof.
  rewrite interp_erase_guard.
  apply guard_equ_node, interp_erase_ret.
Qed.

Lemma interp_erase_br {E} `{Encode E} {X} n
    (k : fin' n -> ictree (yieldE + (spawnE + E)) X) :
  interp_yield (interp_spawn (Br n k))
    ≅ Br n (fun i => Guard (Guard (interp_yield (interp_spawn (k i))))).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_br_node, interp_br_node.
  apply br_equ; intro i.
  apply guard_equ_node, interp_guard_node.
Qed.

Lemma interp_erase_yield {E} `{Encode E} {X}
    (k : unit -> ictree (yieldE + (spawnE + E)) X) :
  interp_yield (interp_spawn (Vis (inl Yield) k))
    ≅ Guard (Guard (interp_yield (interp_spawn (k tt)))).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_vis_node.
  cbn [handle_spawn].
  unfold ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  erase_resum.
  rewrite interp_vis_node.
  cbn [handle_yield].
  rewrite bind_ret_l.
  apply guard_equ_node.
  rewrite interp_guard_node.
  reflexivity.
Qed.

Lemma interp_erase_guard_yield {E} `{Encode E} {X}
    (k : unit -> ictree (yieldE + (spawnE + E)) X) :
  interp_yield (interp_spawn (Guard (Vis (inl Yield) k)))
    ≅ Guard (Guard (Guard (interp_yield (interp_spawn (k tt))))).
Proof.
  rewrite interp_erase_guard.
  apply guard_equ_node, interp_erase_yield.
Qed.

Lemma interp_erase_spawn {E} `{Encode E} {X}
    (k : unit -> ictree (yieldE + (spawnE + E)) X) :
  interp_yield (interp_spawn (Vis (inr (inl Spawn)) k))
    ≅ Guard (interp_yield (interp_spawn (k tt))).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_vis_node.
  cbn [handle_spawn].
  rewrite bind_ret_l.
  rewrite interp_guard_node.
  reflexivity.
Qed.

Lemma interp_erase_user {E} `{Encode E} {X} (m : E)
    (k : encode m -> ictree (yieldE + (spawnE + E)) X) :
  interp_yield (interp_spawn (Vis (inr (inr m)) k))
    ≅ Vis m (fun x => Guard (Guard (interp_yield (interp_spawn (k x))))).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_vis_node.
  cbn [handle_spawn].
  unfold ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  erase_resum.
  rewrite interp_vis_node.
  cbn [handle_yield].
  unfold ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  erase_resum.
  apply vis_equ_node; intro x.
  apply guard_equ_node.
  rewrite interp_guard_node.
  reflexivity.
Qed.
