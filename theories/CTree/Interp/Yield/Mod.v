From Stdlib Require Import
  Fin
  Vector
  Morphisms.

From TICL Require Import
  CTree.Core
  CTree.Interp.State.Mod
  CTree.Events.Yield
  CTree.Events.State
  CTree.Events.Writer
  Utils.Vectors.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

Generalizable All Variables.

(** * Cooperative scheduling over raw [ctree] pools *)
(** This module is language independent.  It owns the cooperative scheduler,
    the event-erasure handlers, and the instrumentation algebra that lifts a
    raw thread or a raw scheduled pool into the writer-instrumented view. *)

Section Scheduler.
  Context {E B : Type -> Type} `{Bn -< B}.

  (** Cooperative scheduler for a finite pool.

      [None] focus means the scheduler chooses a runnable thread after emitting
      a scheduling [Yield]; the choice is one observable step ([brS]).
      [Some i] observes one node of thread [i], removing finished threads,
      clearing focus on source yields, and turning source forks into
      scheduler-visible [Spawn] events.  Hidden branches of the thread stay
      hidden, visible steps stay visible. *)
  CoFixpoint schedule (n : nat) (v : pool E B n) (focus : option (Fin.t n)) : completed E B :=
    match focus with
    | None =>
        match n return pool E B n -> completed E B with
        | 0 => fun _ => Ret tt
        | S n' => fun v =>
            Vis (inl1 Yield)
              (fun _ => brS (branchn (S n')) (fun i => schedule (S n') v (Some i)))
        end v
    | Some i =>
        match n return pool E B n -> Fin.t n -> completed E B with
        | 0 => fun _ i => match i with end
        | S n' => fun v i =>
            match observe (v $ i) with
            | RetF _ => Guard (schedule n' (v -- i) None)
            | StuckF => Stuck
            | BrF c k => Br c (fun j => schedule (S n') (v @ i := (k j)) (Some i))
            | StepF t => Step (schedule (S n') (v @ i := t) (Some i))
            | GuardF t => Guard (schedule (S n') (v @ i := t) (Some i))
            | @VisF _ _ _ _ Y e k =>
                match e with
                | inl1 y =>
                    match y in yieldE Y0 return (Y0 -> thread E B) -> completed E B with
                    | Yield => fun k => Guard (schedule (S n') (v @ i := (k tt)) None)
                    end k
                | inr1 (inl1 f) =>
                    match f in forkE Y0 return (Y0 -> thread E B) -> completed E B with
                    | Fork => fun k =>
                        Vis (inr1 (inl1 Spawn) : (yieldE +' (spawnE +' E)) unit)
                          (fun _ => schedule (S (S n'))
                                      ((k true :: (v @ i := (k false)))%vector)
                                      (Some (FS i)))
                    end k
                | inr1 (inr1 e') =>
                    Vis (inr1 (inr1 e') : (yieldE +' (spawnE +' E)) Y)
                      (fun x => schedule (S n') (v @ i := (k x)) (Some i))
                end
            end
        end v i
    end.
End Scheduler.

(** * Event erasure handlers *)

(** Erase scheduler spawn observations while preserving yield and user events.

    The result universe [r] is named on every handler: the dependent match on a
    (monomorphic) event index would otherwise minimise it to that index's global
    universe, which [interp] (needing it strictly above the event domain) rejects. *)
Definition handle_spawn@{r +} {E B} :
  (yieldE +' (spawnE +' E)) ~> ctree@{_ _ _ _ r _} (yieldE +' E) B :=
  fun _ event =>
    match event with
    | inl1 y => CTree.trigger (inl1 y)
    | inr1 (inl1 s) => match s in spawnE Y return ctree (yieldE +' E) B Y with Spawn => Ret tt end
    | inr1 (inr1 m) => CTree.trigger (inr1 m)
    end.

Definition interp_spawn {E B X}
    (t : ctree (yieldE +' (spawnE +' E)) B X) : ctree (yieldE +' E) B X :=
  interp (M := ctree (yieldE +' E) B) handle_spawn t.

(** Erase cooperative yield observations, leaving only user events. *)
Definition handle_yield@{r +} {E B} : (yieldE +' E) ~> ctree@{_ _ _ _ r _} E B :=
  fun _ event =>
    match event with
    | inl1 y => match y in yieldE Y return ctree E B Y with Yield => Ret tt end
    | inr1 m => CTree.trigger m
    end.

Definition interp_yield {E B X}
    (t : ctree (yieldE +' E) B X) : ctree E B X :=
  interp (M := ctree E B) handle_yield t.

(** Interpret a raw thread without scheduling by resolving [Fork] to [false],
    so a standalone thread behaves as the parent path and never starts the
    fork body. *)
Definition handle_thread@{r +} {E B} :
  (yieldE +' (forkE +' E)) ~> ctree@{_ _ _ _ r _} (yieldE +' E) B :=
  fun _ event =>
    match event with
    | inl1 y => CTree.trigger (inl1 y)
    | inr1 (inl1 f) => match f in forkE Y return ctree (yieldE +' E) B Y with Fork => Ret false end
    | inr1 (inr1 m) => CTree.trigger (inr1 m)
    end.

Definition interp_thread {E B X}
    (t : ctree (yieldE +' (forkE +' E)) B X) : ctree E B X :=
  interp_yield (interp (M := ctree (yieldE +' E) B) handle_thread t).

(** The erasure interpreters are [equ]-congruences; this lets structural
    equations be rewritten underneath them. *)
#[global] Instance interp_spawn_equ {E B X} :
  Proper (equ eq ==> equ eq) (@interp_spawn E B X).
Proof. intros t u Ht. unfold interp_spawn. now rewrite Ht. Qed.

#[global] Instance interp_yield_equ {E B X} :
  Proper (equ eq ==> equ eq) (@interp_yield E B X).
Proof. intros t u Ht. unfold interp_yield. now rewrite Ht. Qed.

#[global] Instance interp_thread_equ_proper {E B X} :
  Proper (equ eq ==> equ eq) (@interp_thread E B X).
Proof. intros t u Ht. unfold interp_thread, interp_yield. now rewrite Ht. Qed.

(** * Scheduler one-step/case regression facts. *)
Section SchedulerFacts.
  Context {E B : Type -> Type} `{Bn -< B}.

  Local Ltac solve_focused_schedule H :=
    lazy [schedule observe _observe];
    match type of H with
    | observe (Vector.nth ?v ?i) = _ =>
        change (@_observe _ _ unit (Vector.nth v i)) with (observe (Vector.nth v i));
        rewrite H;
        reflexivity
    end.

  Lemma schedule_empty_none (v : pool E B 0) :
    observe (schedule 0 v None) = RetF tt.
  Proof. reflexivity. Qed.

  Lemma schedule_no_focus_nonempty n (v : pool E B (S n)) :
    observe (schedule (S n) v None) =
      VisF (inl1 Yield) (fun _ => brS (branchn (S n)) (fun i => schedule (S n) v (Some i))).
  Proof. reflexivity. Qed.

  Lemma schedule_focused_ret n (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = RetF tt ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule n (v -- i) None).
  Proof.
    intro Hret.
    solve_focused_schedule Hret.
  Qed.

  Lemma schedule_focused_stuck n (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = StuckF ->
    observe (schedule (S n) v (Some i)) = StuckF.
  Proof.
    intro Hst.
    solve_focused_schedule Hst.
  Qed.

  Lemma schedule_focused_br n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k :
    observe (v $ i) = BrF c k ->
    observe (schedule (S n) v (Some i)) =
      BrF c (fun j => schedule (S n) (v @ i := (k j)) (Some i)).
  Proof.
    intro Hbr.
    solve_focused_schedule Hbr.
  Qed.

  Lemma schedule_focused_step n (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = StepF t ->
    observe (schedule (S n) v (Some i)) =
      StepF (schedule (S n) (v @ i := t) (Some i)).
  Proof.
    intro Hs.
    solve_focused_schedule Hs.
  Qed.

  Lemma schedule_focused_guard n (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S n) (v @ i := t) (Some i)).
  Proof.
    intro Hg.
    solve_focused_schedule Hg.
  Qed.

  Lemma schedule_focused_yield n (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl1 Yield) k ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S n) (v @ i := (k tt)) None).
  Proof.
    intro Hy.
    solve_focused_schedule Hy.
  Qed.

  Lemma schedule_focused_fork n (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    observe (schedule (S n) v (Some i)) =
      VisF (inr1 (inl1 Spawn) : (yieldE +' (spawnE +' E)) unit)
        (fun _ => schedule (S (S n))
                    ((k true :: (v @ i := (k false)))%vector)
                    (Some (Fin.FS i))).
  Proof.
    intro Hf.
    solve_focused_schedule Hf.
  Qed.

  Lemma schedule_focused_user_event n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    observe (schedule (S n) v (Some i)) =
      VisF (inr1 (inr1 e) : (yieldE +' (spawnE +' E)) Y)
        (fun x => schedule (S n) (v @ i := (k x)) (Some i)).
  Proof.
    intro Hu.
    solve_focused_schedule Hu.
  Qed.
End SchedulerFacts.

(** * Raw instrumentation entry points *)

(** Instrument a standalone raw thread: erase [Fork] to the parent branch and
    erase cooperative [Yield], then instrument the residual state effects. *)
Definition instr_thread {Σ B X}
    (t : ctree (yieldE +' (forkE +' stateE Σ)) B X) (σ : Σ)
    : ctreeW Σ B (Σ * X) :=
  instr_stateE (interp_thread t) σ.

(** Instrument a scheduled pool: erase scheduler [Spawn] and cooperative
    [Yield] observations, then instrument the residual state effects. *)
Definition instr_schedule {Σ B} `{Bn -< B} (n : nat) (v : pool (stateE Σ) B n)
    (focus : option (Fin.t n)) (σ : Σ) : ctreeW Σ B (Σ * unit) :=
  instr_stateE (interp_yield (interp_spawn (schedule n v focus))) σ.

(** ** Structural [interp] and [equ] equations used by the erasure algebra.

    Thin wrappers over the [ctrees] equations, kept under their TICL names.
    The handler's result universe is named ([r]) so that [interp] can place it
    strictly above the event domain; [M] is fixed to keep instance search finite. *)
Section InterpNodes.
  Universe r.
  Context {E F B : Type -> Type} (h : E ~> ctree@{_ _ _ _ r _} F B).

  Lemma interp_ret_node {X} (x : X) :
    interp (M := ctree F B) h (Ret x : ctree E B X) ≅ Ret x.
  Proof. apply interp_ret. Qed.

  Lemma interp_stuck_node {X} :
    interp (M := ctree F B) h (Stuck : ctree E B X) ≅ Stuck.
  Proof. apply interp_stuck. Qed.

  Lemma interp_guard_node {X} (t : ctree E B X) :
    interp (M := ctree F B) h (Guard t) ≅ Guard (interp (M := ctree F B) h t).
  Proof. apply interp_guard. Qed.

  Lemma interp_step_node {X} (t : ctree E B X) :
    interp (M := ctree F B) h (Step t) ≅ Step (Guard (interp (M := ctree F B) h t)).
  Proof. apply interp_step. Qed.

  Lemma interp_br_node {X Y} (c : B Y) (k : Y -> ctree E B X) :
    interp (M := ctree F B) h (Br c k) ≅ Br c (fun i => Guard (interp (M := ctree F B) h (k i))).
  Proof. rewrite interp_br'; reflexivity. Qed.

  Lemma interp_vis_node {X Y} (e : E Y) (k : Y -> ctree E B X) :
    interp (M := ctree F B) h (Vis e k) ≅ h _ e >>= (fun x => Guard (interp (M := ctree F B) h (k x))).
  Proof. apply interp_vis. Qed.
End InterpNodes.

Lemma guard_equ_node {E B X} (t u : ctree E B X) :
  t ≅ u -> Guard t ≅ Guard u.
Proof. apply guard_equ. Qed.

Lemma vis_equ_node {E B X Y} (e : E Y) (k1 k2 : Y -> ctree E B X) :
  (forall x, k1 x ≅ k2 x) -> Vis e k1 ≅ Vis e k2.
Proof. intro Hk. step. constructor. exact Hk. Qed.

(** ** Composed erasure equations for a single raw thread node. *)

Lemma interp_thread_yield_node {E B X}
    (k : unit -> ctree (yieldE +' (forkE +' E)) B X) :
  interp_thread (Vis (inl1 Yield) k) ≅ Guard (Guard (interp_thread (k tt))).
Proof.
  unfold interp_thread, interp_yield.
  rewrite interp_vis_node.
  cbn [handle_thread].
  rewrite bind_trigger.
  rewrite interp_vis_node.
  cbn [handle_yield].
  rewrite bind_ret_l.
  apply guard_equ_node.
  rewrite interp_guard_node.
  reflexivity.
Qed.

Lemma interp_thread_user_node {E B X Y} (m : E Y)
    (k : Y -> ctree (yieldE +' (forkE +' E)) B X) :
  interp_thread (Vis (inr1 (inr1 m)) k)
    ≅ Vis m (fun x => Guard (Guard (interp_thread (k x)))).
Proof.
  unfold interp_thread, interp_yield.
  rewrite interp_vis_node.
  cbn [handle_thread].
  rewrite bind_trigger.
  rewrite interp_vis_node.
  cbn [handle_yield].
  rewrite bind_trigger.
  apply vis_equ_node; intro x.
  apply guard_equ_node.
  rewrite interp_guard_node.
  reflexivity.
Qed.

(** ** Thread erasure under an arbitrary state handler.

    The same algebra as [instr_thread], for any handler [h]: a standalone
    raw thread erases [Fork] to the parent branch and erases cooperative
    [Yield], then interprets its residual user events with [h]. *)
Section ThreadStateInterp.
  Context {E F B : Type -> Type} {S : Type} (h : E ~> stateT S (ctree F B)).

  Lemma interp_state_thread_ret {X} (x : X) (s : S) :
    interp_state h (interp_thread (Ret x : ctree (yieldE +' (forkE +' E)) B X)) s ≅ Ret (s, x).
  Proof.
    unfold interp_thread, interp_yield.
    rewrite interp_ret_node, interp_ret_node.
    apply interp_state_ret.
  Qed.

  Lemma interp_state_thread_bind {A C}
      (t : ctree (yieldE +' (forkE +' E)) B A)
      (k : A -> ctree (yieldE +' (forkE +' E)) B C) (s : S) :
    interp_state h (interp_thread (t >>= k)) s
      ≅ (interp_state h (interp_thread t) s >>= fun '(s', x) =>
           interp_state h (interp_thread (k x)) s').
  Proof.
    unfold interp_thread, interp_yield.
    rewrite !interp_bind, interp_state_bind.
    upto_bind_eq; intros [s' x]; reflexivity.
  Qed.

  Lemma interp_state_thread_yield {X}
      (k : unit -> ctree (yieldE +' (forkE +' E)) B X) (s : S) :
    interp_state h (interp_thread (Vis (inl1 Yield) k)) s
      ~ interp_state h (interp_thread (k tt)) s.
  Proof.
    rewrite interp_thread_yield_node.
    rewrite interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.

  Lemma interp_state_thread_user {X Y} (e : E Y)
      (k : Y -> ctree (yieldE +' (forkE +' E)) B X) (s : S) :
    interp_state h (interp_thread (Vis (inr1 (inr1 e)) k)) s
      ~ (h _ e s >>= fun '(s', x) =>
           interp_state h (interp_thread (k x)) s').
  Proof.
    rewrite interp_thread_user_node, interp_state_vis.
    __upto_bind_sbisim_eq; intros [s' x]; cbn.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.
End ThreadStateInterp.

(** ** Instrumentation algebra for raw threads. *)

#[global] Instance instr_thread_equ {Σ B X} :
  Proper (equ eq ==> eq ==> equ eq) (@instr_thread Σ B X).
Proof.
  intros t t' Ht σ σ' <-.
  unfold instr_thread, interp_thread, interp_yield, instr_stateE.
  now rewrite Ht.
Qed.

Lemma instr_thread_ret {Σ B X} (x : X) (σ : Σ) :
  instr_thread (B:=B) (Ret x) σ ≅ Ret (σ, x).
Proof. exact (interp_state_thread_ret h_stateW x σ). Qed.

Lemma instr_thread_bind {Σ B A C}
    (t : ctree (yieldE +' (forkE +' stateE Σ)) B A)
    (k : A -> ctree (yieldE +' (forkE +' stateE Σ)) B C) (σ : Σ) :
  instr_thread (t >>= k) σ
    ≅ (instr_thread t σ >>= fun '(σ', x) => instr_thread (k x) σ').
Proof. exact (interp_state_thread_bind h_stateW t k σ). Qed.

Lemma instr_thread_yield {Σ B X}
    (k : unit -> ctree (yieldE +' (forkE +' stateE Σ)) B X) (σ : Σ) :
  instr_thread (Vis (inl1 Yield) k) σ ~ instr_thread (k tt) σ.
Proof. exact (interp_state_thread_yield h_stateW k σ). Qed.

Lemma instr_thread_get {Σ B X}
    (k : Σ -> ctree (yieldE +' (forkE +' stateE Σ)) B X) (σ : Σ) :
  instr_thread (Vis (inr1 (inr1 Get)) k) σ ~ instr_thread (k σ) σ.
Proof.
  unfold instr_thread, instr_stateE.
  rewrite interp_thread_user_node.
  rewrite interp_state_vis.
  cbn [h_stateW].
  change (Monad.bind ?a ?b) with (CTree.bind a b).
  rewrite bind_ret_l; cbn [fst snd].
  rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
  reflexivity.
Qed.

Lemma instr_thread_put {Σ B X} (σ' : Σ)
    (k : unit -> ctree (yieldE +' (forkE +' stateE Σ)) B X) (σ : Σ) :
  instr_thread (Vis (inr1 (inr1 (Put σ'))) k) σ
    ~ (log σ';; instr_thread (k tt) σ').
Proof.
  unfold instr_thread, instr_stateE.
  rewrite interp_thread_user_node.
  rewrite interp_state_vis.
  cbn [h_stateW].
  change (Monad.bind ?a ?b) with (CTree.bind a b).
  rewrite bind_bind.
  __upto_bind_sbisim_eq; intros [].
  rewrite bind_ret_l; cbn [fst snd].
  rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
  reflexivity.
Qed.

(** ** Composed erasure equations for a single scheduled node. *)
(** [interp_yield (interp_spawn _)] is the erased view of a scheduled pool:
    scheduler [Spawn] and cooperative [Yield] observations are removed, and the
    residual user events are preserved. *)

Lemma interp_erase_ret {E B X} (x : X) :
  interp_yield (interp_spawn (Ret x : ctree (yieldE +' (spawnE +' E)) B X)) ≅ Ret x.
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_ret_node, interp_ret_node.
  reflexivity.
Qed.

Lemma interp_erase_stuck {E B X} :
  interp_yield (interp_spawn (Stuck : ctree (yieldE +' (spawnE +' E)) B X)) ≅ Stuck.
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_stuck_node, interp_stuck_node.
  reflexivity.
Qed.

Lemma interp_erase_guard {E B X}
    (t : ctree (yieldE +' (spawnE +' E)) B X) :
  interp_yield (interp_spawn (Guard t)) ≅ Guard (interp_yield (interp_spawn t)).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_guard_node, interp_guard_node.
  reflexivity.
Qed.

Lemma interp_erase_step {E B X}
    (t : ctree (yieldE +' (spawnE +' E)) B X) :
  interp_yield (interp_spawn (Step t)) ≅ Step (Guard (Guard (interp_yield (interp_spawn t)))).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_step_node, interp_step_node.
  do 2 (step; constructor).
  rewrite interp_guard_node.
  reflexivity.
Qed.

Lemma interp_erase_br {E B X Y} (c : B Y)
    (k : Y -> ctree (yieldE +' (spawnE +' E)) B X) :
  interp_yield (interp_spawn (Br c k))
    ≅ Br c (fun i => Guard (Guard (interp_yield (interp_spawn (k i))))).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_br_node, interp_br_node.
  apply br_equ; intro i.
  apply guard_equ_node, interp_guard_node.
Qed.

Lemma interp_erase_yield {E B X}
    (k : unit -> ctree (yieldE +' (spawnE +' E)) B X) :
  interp_yield (interp_spawn (Vis (inl1 Yield) k))
    ≅ Guard (Guard (interp_yield (interp_spawn (k tt)))).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_vis_node.
  cbn [handle_spawn].
  rewrite bind_trigger.
  rewrite interp_vis_node.
  cbn [handle_yield].
  rewrite bind_ret_l.
  apply guard_equ_node.
  rewrite interp_guard_node.
  reflexivity.
Qed.

Lemma interp_erase_spawn {E B X}
    (k : unit -> ctree (yieldE +' (spawnE +' E)) B X) :
  interp_yield (interp_spawn (Vis (inr1 (inl1 Spawn)) k))
    ≅ Guard (interp_yield (interp_spawn (k tt))).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_vis_node.
  cbn [handle_spawn].
  rewrite bind_ret_l.
  rewrite interp_guard_node.
  reflexivity.
Qed.

Lemma interp_erase_user {E B X Y} (m : E Y)
    (k : Y -> ctree (yieldE +' (spawnE +' E)) B X) :
  interp_yield (interp_spawn (Vis (inr1 (inr1 m)) k))
    ≅ Vis m (fun x => Guard (Guard (interp_yield (interp_spawn (k x))))).
Proof.
  unfold interp_yield, interp_spawn.
  rewrite interp_vis_node.
  cbn [handle_spawn].
  rewrite bind_trigger.
  rewrite interp_vis_node.
  cbn [handle_yield].
  rewrite bind_trigger.
  apply vis_equ_node; intro x.
  apply guard_equ_node.
  rewrite interp_guard_node.
  reflexivity.
Qed.
