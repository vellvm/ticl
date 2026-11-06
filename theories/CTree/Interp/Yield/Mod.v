From Stdlib Require Import
  List
  Arith.PeanoNat
  Program.Equality
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

(** * Scheduling policies *)

Definition rr_pick (n cursor : nat) : Fin.t (S n) :=
  @Fin.of_nat_lt (cursor mod S n) (S n)
    (Nat.mod_upper_bound cursor (S n) (Nat.neq_succ_0 n)).

(** A singleton round-robin pool always picks its only slot. *)
Lemma rr_pick_0 m : rr_pick 0 m = Fin.F1.
Proof. apply Fin.to_nat_inj; unfold rr_pick; rewrite Fin.to_nat_of_nat; cbn; reflexivity. Qed.

(** Compare numeric choices, not the proof arguments of finite indices. *)
Lemma rr_pick_mod_congr n cursor cursor' :
  cursor mod S n = cursor' mod S n -> rr_pick n cursor = rr_pick n cursor'.
Proof.
  intro Hmod; apply Fin.to_nat_inj; unfold rr_pick.
  rewrite !Fin.to_nat_of_nat; exact Hmod.
Qed.

Lemma rr_pick_even n : Nat.even n = true -> rr_pick 1 n = Fin.F1.
Proof.
  intro Hn; apply Nat.even_spec in Hn; destruct Hn as [k ->].
  transitivity (rr_pick 1 0); [apply rr_pick_mod_congr|reflexivity].
  change ((2 * k) mod 2 = 0).
  rewrite Nat.mul_comm; apply Nat.Div0.mod_mul.
Qed.

Lemma rr_pick_odd n : Nat.even n = false -> rr_pick 1 n = Fin.FS Fin.F1.
Proof.
  intro Hn.
  assert (Ho : Nat.odd n = true) by (unfold Nat.odd; now rewrite Hn).
  apply Nat.odd_spec in Ho; destruct Ho as [k ->].
  transitivity (rr_pick 1 1); [apply rr_pick_mod_congr|reflexivity].
  change ((2 * k + 1) mod 2 = 1).
  rewrite Nat.Div0.add_mod.
  rewrite (Nat.mul_comm 2 k), Nat.Div0.mod_mul.
  reflexivity.
Qed.

(** A policy carries its own state; at a scheduling point of a pool of size
    [S n] it offers [S (sched_arity n st)] alternatives, each resolving to a
    slot and a successor state.  Plain record: the policy is always passed
    explicitly, nothing drives inference. *)
Record Scheduler : Type := {
  sched_state : Type;
  sched_arity : nat -> sched_state -> nat;
  sched_pick  : forall n (st : sched_state),
                Fin.t (S (sched_arity n st)) -> Fin.t (S n) * sched_state;
}.

Definition rr_scheduler : Scheduler :=
  {| sched_state := nat; sched_arity := fun _ _ => 0;
     sched_pick := fun n m _ => (rr_pick n m, S m) |}.

(** Nondeterministic selection is stateless and can avoid a slot forever;
    [Fair.nd_not_fair] proves that it has no fairness instance. *)
Definition nd_scheduler : Scheduler :=
  {| sched_state := unit; sched_arity := fun n _ => n;
     sched_pick := fun n _ c => (c, tt) |}.

Lemma slot_index_rr_pick n cursor : slot_index (rr_pick n cursor) = cursor mod S n.
Proof. unfold slot_index, rr_pick; rewrite Fin.to_nat_of_nat; reflexivity. Qed.

(** Logged selections while an unfocused pool of returning slots shrinks. *)
Fixpoint rr_return_picks (size cursor : nat) : list nat :=
  match size with
  | 0 => List.nil
  | S n => List.cons (slot_index (rr_pick n cursor)) (rr_return_picks n (S cursor))
  end.

(** [S m] alternatives: a single alternative is taken directly, more are a
    hidden branch. *)
Definition br_alts {E B X} `{Bn -< B} (m : nat) : (Fin.t (S m) -> ctree E B X) -> ctree E B X :=
  match m with
  | 0 => fun k => k Fin.F1
  | S m' => fun k => br (branchn (S (S m'))) k
  end.

Lemma br_alts_equ {E B X} `{Bn -< B} m (k k' : Fin.t (S m) -> ctree E B X) :
  (forall a, k a ≅ k' a) -> br_alts m k ≅ br_alts m k'.
Proof.
  intro Hk; destruct m as [|m]; cbn [br_alts]; [apply Hk|].
  step; constructor; exact Hk.
Qed.

Lemma br_alts_sbisim {E B X} `{Bn -< B} m (k k' : Fin.t (S m) -> ctree E B X) :
  (forall a, k a ~ k' a) -> br_alts m k ~ br_alts m k'.
Proof.
  intro Hk; destruct m as [|m]; cbn [br_alts]; [apply Hk|].
  apply sb_br_id; exact Hk.
Qed.

Lemma trans_br_alts_inv {E B X} `{Bn -< B} m (k : Fin.t (S m) -> ctree E B X) l t' :
  trans l (br_alts m k) t' -> exists a, trans l (k a) t'.
Proof.
  destruct m as [|m]; cbn [br_alts]; intro TR; [exists Fin.F1; exact TR|].
  apply trans_br_inv in TR; exact TR.
Qed.

Lemma trans_br_alts {E B X} `{Bn -< B} m (k : Fin.t (S m) -> ctree E B X) l a t' :
  trans l (k a) t' -> trans l (br_alts m k) t'.
Proof.
  destruct m as [|m]; cbn [br_alts]; intro TR; [rewrite (fin1_eq a) in TR; exact TR|].
  eapply trans_br; [exact TR|reflexivity].
Qed.

(** Interpreting a state handler through the alternatives. *)
Lemma interp_state_br_alts_sb {E F B : Type -> Type} {Σ : Type} `{Bn -< B}
    (h : E ~> stateT Σ (ctree F B)) {X} m (k : Fin.t (S m) -> ctree E B X) (s : Σ) :
  interp_state h (br_alts m k) s ~ br_alts m (fun a => interp_state h (k a) s).
Proof.
  destruct m as [|m]; cbn [br_alts]; [reflexivity|].
  rewrite interp_state_br.
  change (Monad.bind (mbr ?c) ?f) with (CTree.bind (branch c : ctree F B _) f).
  rewrite bind_branch.
  apply sb_br_id; intro a; rewrite sb_guard; reflexivity.
Qed.


Section Scheduler.
  Context {E B : Type -> Type} `{Bn -< B}.

  (** Select only at an unfocused boundary. Focused source branches are
      preserved, and all focused clauses leave the policy state unchanged. *)
  CoFixpoint schedule_policy (sch : Scheduler) (n : nat) (v : pool E B n)
      (focus : option (Fin.t n)) (st : sched_state sch) : completed E B :=
    match focus with
    | None =>
        match n return pool E B n -> completed E B with
        | 0 => fun _ => Ret tt
        | S n' => fun v =>
            match sched_arity sch n' st as a return
              (Fin.t (S a) -> Fin.t (S n') * sched_state sch) -> completed E B with
            | 0 => fun pick => let '(i, st') := pick Fin.F1 in
                Vis (inr1 (Scheduled (slot_index i)))
                  (fun _ => schedule_policy sch (S n') v (Some i) st')
            | S a => fun pick => Br (subevent _ (branchn (S (S a))))
                (fun x => let '(i, st') := pick x in
                  Vis (inr1 (Scheduled (slot_index i)))
                    (fun _ => schedule_policy sch (S n') v (Some i) st'))
            end (sched_pick sch n' st)
        end v
    | Some i =>
        match n return pool E B n -> Fin.t n -> completed E B with
        | 0 => fun _ i => match i with end
        | S n' => fun v i =>
            match observe (v $ i) with
            | RetF _ => Guard (schedule_policy sch n' (v -- i) None st)
            | StuckF => Stuck
            | BrF c k => Br c (fun j => schedule_policy sch (S n') (v @ i := k j) (Some i) st)
            | StepF t => Step (schedule_policy sch (S n') (v @ i := t) (Some i) st)
            | GuardF t => Guard (schedule_policy sch (S n') (v @ i := t) (Some i) st)
            | @VisF _ _ _ _ Y e k =>
                match e with
                | inl1 y =>
                    match y in yieldE Y0 return (Y0 -> thread E B) -> completed E B with
                    | Yield => fun k => Guard (schedule_policy sch (S n') (v @ i := k tt) None st)
                    end k
                | inr1 (inl1 f) =>
                    match f in forkE Y0 return (Y0 -> thread E B) -> completed E B with
                    | Fork => fun k => Guard (schedule_policy sch (S (S n'))
                        (k true :: (v @ i := k false)) (Some (Fin.FS i)) st)
                    end k
                | inr1 (inr1 e') => Vis (inl1 e')
                    (fun x => schedule_policy sch (S n') (v @ i := k x) (Some i) st)
                end
            end
        end v i
    end.

  Lemma unfold_schedule_policy (sch : Scheduler) n (v : pool E B n) focus st :
    schedule_policy sch n v focus st ≅
match focus with
    | None =>
        match n return pool E B n -> completed E B with
        | 0 => fun _ => Ret tt
        | S n' => fun v =>
            match sched_arity sch n' st as a return
              (Fin.t (S a) -> Fin.t (S n') * sched_state sch) -> completed E B with
            | 0 => fun pick => let '(i, st') := pick Fin.F1 in
                Vis (inr1 (Scheduled (slot_index i)))
                  (fun _ => schedule_policy sch (S n') v (Some i) st')
            | S a => fun pick => Br (subevent _ (branchn (S (S a))))
                (fun x => let '(i, st') := pick x in
                  Vis (inr1 (Scheduled (slot_index i)))
                    (fun _ => schedule_policy sch (S n') v (Some i) st'))
            end (sched_pick sch n' st)
        end v
    | Some i =>
        match n return pool E B n -> Fin.t n -> completed E B with
        | 0 => fun _ i => match i with end
        | S n' => fun v i =>
            match observe (v $ i) with
            | RetF _ => Guard (schedule_policy sch n' (v -- i) None st)
            | StuckF => Stuck
            | BrF c k => Br c (fun j => schedule_policy sch (S n') (v @ i := k j) (Some i) st)
            | StepF t => Step (schedule_policy sch (S n') (v @ i := t) (Some i) st)
            | GuardF t => Guard (schedule_policy sch (S n') (v @ i := t) (Some i) st)
            | @VisF _ _ _ _ Y e k =>
                match e with
                | inl1 y =>
                    match y in yieldE Y0 return (Y0 -> thread E B) -> completed E B with
                    | Yield => fun k => Guard (schedule_policy sch (S n') (v @ i := k tt) None st)
                    end k
                | inr1 (inl1 f) =>
                    match f in forkE Y0 return (Y0 -> thread E B) -> completed E B with
                    | Fork => fun k => Guard (schedule_policy sch (S (S n'))
                        (k true :: (v @ i := k false)) (Some (Fin.FS i)) st)
                    end k
                | inr1 (inr1 e') => Vis (inl1 e')
                    (fun x => schedule_policy sch (S n') (v @ i := k x) (Some i) st)
                end
            end
        end v i
    end.
  Proof. step; cbn; reflexivity. Qed.

  Definition schedule n (v : pool E B n) focus : completed E B :=
    schedule_policy nd_scheduler n v focus tt.

  Definition schedule_rr n (v : pool E B n) focus cursor : completed E B :=
    schedule_policy rr_scheduler n v focus cursor.

  Lemma schedule_policy_no_focus_nonempty (sch : Scheduler) n (v : pool E B (S n)) st :
    schedule_policy sch (S n) v None st ≅
    br_alts (sched_arity sch n st) (fun a =>
      Vis (inr1 (Scheduled (slot_index (fst (sched_pick sch n st a)))))
        (fun _ => schedule_policy sch (S n) v
          (Some (fst (sched_pick sch n st a))) (snd (sched_pick sch n st a)))).
  Proof.
    rewrite unfold_schedule_policy.
    generalize (sched_pick sch n st); destruct (sched_arity sch n st); intro pick;
      cbn [br_alts].
    - destruct (pick Fin.F1); reflexivity.
    - step; constructor; intro a; destruct (pick a); reflexivity.
  Qed.
End Scheduler.

(** * Event erasure handlers *)

(** Preserve user effects and project each native selection to one silent
    step. The named result universe keeps [interp]'s target above the event
    domain. This handler interprets observations; it makes no choices. *)
Definition handle_scheduled_step@{r +} {E B} :
  (E +' schedE) ~> ctree@{_ _ _ _ r _} E B :=
  fun _ event =>
    match event with
    | inl1 e => CTree.trigger e
    | inr1 s => match s in schedE Y return ctree E B Y with
      | Scheduled _ => Step (Ret tt)
      end
    end.

Definition project_scheduled {E B X}
    (t : ctree (E +' schedE) B X) : ctree E B X :=
  interp (M := ctree E B) handle_scheduled_step t.

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
#[global] Instance project_scheduled_equ {E B X} :
  Proper (equ eq ==> equ eq) (@project_scheduled E B X).
Proof. intros t u Ht; unfold project_scheduled; now rewrite Ht. Qed.

#[global] Instance interp_yield_equ {E B X} :
  Proper (equ eq ==> equ eq) (@interp_yield E B X).
Proof. intros t u Ht. unfold interp_yield. now rewrite Ht. Qed.

#[global] Instance interp_thread_equ_proper {E B X} :
  Proper (equ eq ==> equ eq) (@interp_thread E B X).
Proof. intros t u Ht. unfold interp_thread, interp_yield. now rewrite Ht. Qed.

(** * Exact scheduler node observations. *)
Section SchedulerFacts.
  Context {E B : Type -> Type} `{Bn -< B}.

  Local Ltac solve_focused_schedule Hobs :=
    lazy [schedule schedule_rr schedule_policy observe _observe];
    match type of Hobs with
    | observe (Vector.nth ?v ?i) = _ =>
        change (@_observe _ _ unit (Vector.nth v i)) with (observe (Vector.nth v i));
        rewrite Hobs; reflexivity
    end.

  Lemma schedule_policy_empty_none (sch : Scheduler) (v : pool E B 0) (st : sched_state sch) :
    observe (schedule_policy sch 0 v None st) = RetF tt.
  Proof. reflexivity. Qed.

  Lemma schedule_policy_focused_ret (sch : Scheduler) n (v : pool E B (S n)) (i : Fin.t (S n)) (st : sched_state sch) :
    observe (v $ i) = RetF tt ->
    observe (schedule_policy sch (S n) v (Some i) st) =
      GuardF (schedule_policy sch n (v -- i) None st).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_policy_focused_stuck (sch : Scheduler) n (v : pool E B (S n)) (i : Fin.t (S n)) (st : sched_state sch) :
    observe (v $ i) = StuckF ->
    observe (schedule_policy sch (S n) v (Some i) st) =
      StuckF.
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_policy_focused_br (sch : Scheduler) n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k (st : sched_state sch) :
    observe (v $ i) = BrF c k ->
    observe (schedule_policy sch (S n) v (Some i) st) =
      BrF c (fun j => schedule_policy sch (S n) (v @ i := k j) (Some i) st).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_policy_focused_step (sch : Scheduler) n (v : pool E B (S n)) (i : Fin.t (S n)) t (st : sched_state sch) :
    observe (v $ i) = StepF t ->
    observe (schedule_policy sch (S n) v (Some i) st) =
      StepF (schedule_policy sch (S n) (v @ i := t) (Some i) st).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_policy_focused_guard (sch : Scheduler) n (v : pool E B (S n)) (i : Fin.t (S n)) t (st : sched_state sch) :
    observe (v $ i) = GuardF t ->
    observe (schedule_policy sch (S n) v (Some i) st) =
      GuardF (schedule_policy sch (S n) (v @ i := t) (Some i) st).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_policy_focused_yield (sch : Scheduler) n (v : pool E B (S n)) (i : Fin.t (S n)) k (st : sched_state sch) :
    observe (v $ i) = VisF (inl1 Yield) k ->
    observe (schedule_policy sch (S n) v (Some i) st) =
      GuardF (schedule_policy sch (S n) (v @ i := k tt) None st).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_policy_focused_fork (sch : Scheduler) n (v : pool E B (S n)) (i : Fin.t (S n)) k (st : sched_state sch) :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    observe (schedule_policy sch (S n) v (Some i) st) =
      GuardF (schedule_policy sch (S (S n)) (k true :: (v @ i := k false)) (Some (Fin.FS i)) st).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_policy_focused_user_event (sch : Scheduler) n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k (st : sched_state sch) :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    observe (schedule_policy sch (S n) v (Some i) st) =
      VisF (inl1 e) (fun x => schedule_policy sch (S n) (v @ i := k x) (Some i) st).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_empty_none (v : pool E B 0) :
    observe (schedule 0 v None) = RetF tt.
  Proof. reflexivity. Qed.

  Lemma schedule_focused_ret n (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = RetF tt ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule n (v -- i) None).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_focused_stuck n (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = StuckF ->
    observe (schedule (S n) v (Some i)) =
      StuckF.
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_focused_br n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k :
    observe (v $ i) = BrF c k ->
    observe (schedule (S n) v (Some i)) =
      BrF c (fun j => schedule (S n) (v @ i := k j) (Some i)).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_focused_step n (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = StepF t ->
    observe (schedule (S n) v (Some i)) =
      StepF (schedule (S n) (v @ i := t) (Some i)).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_focused_guard n (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S n) (v @ i := t) (Some i)).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_focused_yield n (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl1 Yield) k ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S n) (v @ i := k tt) None).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_focused_fork n (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S (S n)) (k true :: (v @ i := k false)) (Some (Fin.FS i))).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_focused_user_event n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    observe (schedule (S n) v (Some i)) =
      VisF (inl1 e) (fun x => schedule (S n) (v @ i := k x) (Some i)).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_rr_empty_none (v : pool E B 0) cursor :
    observe (schedule_rr 0 v None cursor) = RetF tt.
  Proof. reflexivity. Qed.

  Lemma schedule_rr_focused_ret n (v : pool E B (S n)) (i : Fin.t (S n)) cursor :
    observe (v $ i) = RetF tt ->
    observe (schedule_rr (S n) v (Some i) cursor) =
      GuardF (schedule_rr n (v -- i) None cursor).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_rr_focused_stuck n (v : pool E B (S n)) (i : Fin.t (S n)) cursor :
    observe (v $ i) = StuckF ->
    observe (schedule_rr (S n) v (Some i) cursor) =
      StuckF.
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_rr_focused_br n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k cursor :
    observe (v $ i) = BrF c k ->
    observe (schedule_rr (S n) v (Some i) cursor) =
      BrF c (fun j => schedule_rr (S n) (v @ i := k j) (Some i) cursor).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_rr_focused_step n (v : pool E B (S n)) (i : Fin.t (S n)) t cursor :
    observe (v $ i) = StepF t ->
    observe (schedule_rr (S n) v (Some i) cursor) =
      StepF (schedule_rr (S n) (v @ i := t) (Some i) cursor).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_rr_focused_guard n (v : pool E B (S n)) (i : Fin.t (S n)) t cursor :
    observe (v $ i) = GuardF t ->
    observe (schedule_rr (S n) v (Some i) cursor) =
      GuardF (schedule_rr (S n) (v @ i := t) (Some i) cursor).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_rr_focused_yield n (v : pool E B (S n)) (i : Fin.t (S n)) k cursor :
    observe (v $ i) = VisF (inl1 Yield) k ->
    observe (schedule_rr (S n) v (Some i) cursor) =
      GuardF (schedule_rr (S n) (v @ i := k tt) None cursor).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_rr_focused_fork n (v : pool E B (S n)) (i : Fin.t (S n)) k cursor :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    observe (schedule_rr (S n) v (Some i) cursor) =
      GuardF (schedule_rr (S (S n)) (k true :: (v @ i := k false)) (Some (Fin.FS i)) cursor).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_rr_focused_user_event n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k cursor :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    observe (schedule_rr (S n) v (Some i) cursor) =
      VisF (inl1 e) (fun x => schedule_rr (S n) (v @ i := k x) (Some i) cursor).
  Proof. intro Hobs; solve_focused_schedule Hobs. Qed.

  Lemma schedule_no_focus_nonempty n (v : pool E B (S n)) :
    observe (schedule (S n) v None) =
      (match n as m return pool E B (S m) -> ctree' (E +' schedE) B unit with
      | 0 => fun v => VisF (inr1 (Scheduled 0))
          (fun _ => schedule 1 v (Some Fin.F1))
      | S m => fun v => BrF (subevent _ (branchn (S (S m))))
          (fun i => Vis (inr1 (Scheduled (slot_index i)))
            (fun _ => schedule (S (S m)) v (Some i)))
      end) v.
  Proof. destruct n; reflexivity. Qed.

  Lemma schedule_rr_no_focus_nonempty n (v : pool E B (S n)) cursor :
    observe (schedule_rr (S n) v None cursor) =
      VisF (inr1 (Scheduled (slot_index (rr_pick n cursor))))
        (fun _ => schedule_rr (S n) v (Some (rr_pick n cursor)) (S cursor)).
  Proof. reflexivity. Qed.
End SchedulerFacts.

(** * Raw instrumentation entry points *)

(** Instrument a standalone raw thread: erase [Fork] to the parent branch and
    erase cooperative [Yield], then instrument the residual state effects. *)
Definition instr_thread {Σ B X}
    (t : ctree (yieldE +' (forkE +' stateE Σ)) B X) (σ : Σ)
    : ctreeW Σ B (Σ * X) :=
  instr_stateE (interp_thread t) σ.

(** Project scheduling selections to silent steps, then instrument user effects. *)
Definition instr_schedule {Σ B} `{Bn -< B} (n : nat) (v : pool (stateE Σ) B n)
    (focus : option (Fin.t n)) (σ : Σ) : ctreeW Σ B (Σ * unit) :=
  instr_stateE (project_scheduled (schedule n v focus)) σ.

(** ** Composed erasure equations for a single raw thread node. *)

Lemma interp_thread_yield_node {E B X}
    (k : unit -> ctree (yieldE +' (forkE +' E)) B X) :
  interp_thread (Vis (inl1 Yield) k) ≅ Guard (Guard (interp_thread (k tt))).
Proof.
  unfold interp_thread, interp_yield.
  rewrite interp_vis.
  cbn [handle_thread].
  rewrite bind_trigger.
  rewrite interp_vis.
  cbn [handle_yield].
  rewrite bind_ret_l.
  apply guard_equ_node.
  rewrite interp_guard.
  reflexivity.
Qed.

Lemma interp_thread_user_node {E B X Y} (m : E Y)
    (k : Y -> ctree (yieldE +' (forkE +' E)) B X) :
  interp_thread (Vis (inr1 (inr1 m)) k)
    ≅ Vis m (fun x => Guard (Guard (interp_thread (k x)))).
Proof.
  unfold interp_thread, interp_yield.
  rewrite interp_vis.
  cbn [handle_thread].
  rewrite bind_trigger.
  rewrite interp_vis.
  cbn [handle_yield].
  rewrite bind_trigger.
  apply vis_equ_node; intro x.
  apply guard_equ_node.
  rewrite interp_guard.
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
    rewrite interp_ret, interp_ret.
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

(** ** Exact equations of the scheduling observation projection. *)

Lemma project_scheduled_ret {E B X} (x : X) :
  project_scheduled (Ret x : ctree (E +' schedE) B X) ≅ Ret x.
Proof. unfold project_scheduled; apply (interp_ret (C:=B) (D:=B) (h:=handle_scheduled_step)). Qed.

Lemma project_scheduled_stuck {E B X} :
  project_scheduled (Stuck : ctree (E +' schedE) B X) ≅ Stuck.
Proof. unfold project_scheduled; apply (interp_stuck (C:=B) (D:=B) (h:=handle_scheduled_step)). Qed.

Lemma project_scheduled_guard {E B X} (t : ctree (E +' schedE) B X) :
  project_scheduled (Guard t) ≅ Guard (project_scheduled t).
Proof. unfold project_scheduled; apply (interp_guard (C:=B) (D:=B) (h:=handle_scheduled_step)). Qed.

Lemma project_scheduled_step {E B X} (t : ctree (E +' schedE) B X) :
  project_scheduled (Step t) ≅ Step (Guard (project_scheduled t)).
Proof. unfold project_scheduled; apply (interp_step (C:=B) (D:=B) (h:=handle_scheduled_step)). Qed.

Lemma project_scheduled_br {E B X Y} (c : B Y) (k : Y -> ctree (E +' schedE) B X) :
  project_scheduled (Br c k) ≅ Br c (fun x => Guard (project_scheduled (k x))).
Proof. unfold project_scheduled; rewrite interp_br'; reflexivity. Qed.

Lemma project_scheduled_user {E B X Y} (e : E Y) (k : Y -> ctree (E +' schedE) B X) :
  project_scheduled (Vis (inl1 e) k) ≅ Vis e (fun x => Guard (project_scheduled (k x))).
Proof.
  unfold project_scheduled; rewrite interp_vis; cbn [handle_scheduled_step].
  rewrite bind_trigger; reflexivity.
Qed.

Lemma project_scheduled_scheduled {E B X} i (k : unit -> ctree (E +' schedE) B X) :
  project_scheduled (Vis (inr1 (Scheduled i)) k) ≅ Step (Guard (project_scheduled (k tt))).
Proof.
  unfold project_scheduled; rewrite interp_vis; cbn [handle_scheduled_step].
  rewrite bind_step, bind_ret_l; reflexivity.
Qed.
