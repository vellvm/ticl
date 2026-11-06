(** Direct scheduling regressions: program choices are not scheduling turns. *)
From Stdlib Require Import List Vector Fin Arith.PeanoNat Arith.Compare_dec
  Arith.Wf_nat Lia Program.Equality.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core CTree.Events.Yield CTree.Events.Writer
  CTree.Interp.Refine CTree.Interp.State.Mod
  CTree.Interp.Yield.Policy CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim CTree.Interp.Yield.Nondeterministic
  CTree.Interp.Yield.RoundRobin CTree.Interp.Yield.Segments
  CTree.Interp.Yield.Fair CTree.Interp.Yield.Observed
  Logic.Kripke CTree.Logic.Trans Utils.Vectors.

Import CTreeNotations CoindNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

Variant pulseE : Type -> Type := Pulse : nat -> pulseE unit.

CoFixpoint worker (id : nat) (internal : bool) : thread pulseE Bn :=
  Vis (inr1 (inr1 (Pulse id))) (fun _ =>
    if internal then
      Br (branchn 1) (fun _ => Vis (inl1 Yield) (fun _ => worker id internal))
    else Vis (inl1 Yield) (fun _ => worker id internal)).

Definition worker0 := worker 0 true.
Definition worker1 := worker 1 false.
Definition two_workers : pool pulseE Bn 2 := [worker0; worker1].

Definition pulse_or_pick {X} (e : (pulseE +' schedE) X) : X * (bool * nat) :=
  match e with
  | inl1 p => match p in pulseE Y return Y * (bool * nat) with
              | Pulse i => (tt, (false,i)) end
  | inr1 s => match s in schedE Y return Y * (bool * nat) with
              | Scheduled i => (tt, (true,i)) end
  end.

(** The evaluator is deliberately partial. A prefix is successful only when
    all requested observations have been collected. Hidden singleton choices
    do not consume the script; every genuinely branching choice does. *)
Fixpoint bounded_prefix {E A Z X}
    (decode : forall Y, E Y -> Y * A) (keep : A -> option Z)
    (allow_step : bool) (fuel needed : nat) (script : list nat)
    (t : ctree E Bn X) : option (list Z) :=
  match needed with
  | 0 => Some List.nil
  | S needed' => match fuel with
    | 0 => None
    | S fuel' => match observe t with
      | StepF u => if allow_step then
          bounded_prefix decode keep allow_step fuel' needed script u else None
      | GuardF u => bounded_prefix decode keep allow_step fuel' needed script u
      | VisF e k => let '(answer,event) := decode _ e in
          match keep event with
          | None => bounded_prefix decode keep allow_step fuel' needed script (k answer)
          | Some z =>
              match bounded_prefix decode keep allow_step fuel' needed' script (k answer) with
              | Some zs => Some (List.cons z zs) | None => None end
          end
      | BrF (branchn arity) k =>
          match arity as m return (Fin.t m -> ctree E Bn X) -> option (list Z) with
          | 0 => fun _ => None
          | 1 => fun k => bounded_prefix decode keep allow_step fuel' needed script (k Fin.F1)
          | S (S m) => fun k => match script with
              | List.nil => None
              | List.cons i rest => match lt_dec i (S (S m)) with
                  | left Hi => bounded_prefix decode keep allow_step fuel' needed rest
                      (k (Fin.of_nat_lt Hi))
                  | right _ => None end
              end
          end k
      | _ => None
      end
    end
  end.

Definition sample fuel needed picks script (t : completed pulseE Bn) :=
  bounded_prefix (@pulse_or_pick)
    (fun '(is_pick,i) => if Bool.eqb picks is_pick then Some i else None)
    true fuel needed script t.

Definition events_sample fuel needed script (t : completed pulseE Bn) :=
  bounded_prefix (@pulse_or_pick) (@Some (bool * nat)) true fuel needed script t.

(** 1. RR advances only at pool selections, never at source branches. *)
Definition rr_internal_branch_picks : option (list nat) :=
  sample 1000 8 true List.nil (schedule_rr 2 two_workers None 0).
Definition rr_internal_branch_pulses : option (list nat) :=
  sample 1000 8 false List.nil (schedule_rr 2 two_workers None 0).
Definition rr_three_thread_picks : option (list nat) :=
  sample 1000 6 true List.nil
    (schedule_rr 3 [worker 0 false; worker 1 false; worker 2 false] None 1).

Example rr_internal_branch_picks_correct :
  rr_internal_branch_picks = Some [0;1;0;1;0;1;0;1]%list.
Proof. vm_compute; reflexivity. Qed.
Example rr_internal_branch_pulses_correct :
  rr_internal_branch_pulses = Some [0;1;0;1;0;1;0;1]%list.
Proof. vm_compute; reflexivity. Qed.
Example rr_three_thread_picks_correct :
  rr_three_thread_picks = Some [1;2;0;1;2;0]%list.
Proof. vm_compute; reflexivity. Qed.

Lemma yielding_worker_branchfree : forall id, BranchFree (worker id false).
Proof.
  intro id; eapply branchfree_invariant with
    (R := fun t => exists id (phase: bool),
      t = if phase then worker id false
          else Vis (inl1 Yield) (fun _ => worker id false)).
  - intros t (who & phase & ->); destruct phase; cbn;
      constructor; intros [].
    + exists who, false; reflexivity.
    + exists who, true; reflexivity.
  - exists id, true; reflexivity.
Qed.

Example rr_yielding_pool_branchfree focus cursor :
  BranchFree (schedule_rr 2 [worker 0 false; worker 1 false] focus cursor).
Proof.
  apply branchfree_schedule_rr; intro i.
  dependent destruction i; [apply yielding_worker_branchfree|].
  dependent destruction i; [apply yielding_worker_branchfree|inversion i].
Qed.

(** 2. Source nondeterminism remains visible before any selection. *)
Definition choice_body (i : Fin.t 2) : thread pulseE Bn :=
  Vis (inr1 (inr1 (Pulse (if Nat.eqb (slot_index i) 0 then 10 else 20))))
    (fun _ => Stuck).
Definition program_choice : thread pulseE Bn := Br (branchn 2) choice_body.
Definition choice_pool : pool pulseE Bn 2 := [program_choice; worker1].

Theorem focused_program_branch_state {E B} {HB : Bn -< B}
    (sch : Scheduler) n (ts : pool E B n) {Y} (c : B Y)
    (k : Y -> thread E B) (st : sched_state sch) :
  schedule_policy sch (S n) (Br c k :: ts)%vector (Some Fin.F1) st ≅
    Br c (fun a => schedule_policy sch (S n)
      ((Br c k :: ts)%vector @ Fin.F1 := k a) (Some Fin.F1) st).
Proof. apply schedule_policy_focused_br_equ; reflexivity. Qed.

Lemma focused_pulse_transition (sch : Scheduler) n
    (ts : pool pulseE Bn (S n)) i id k st :
  observe (ts $ i) = VisF (inr1 (inr1 (Pulse id))) k ->
  exists u, trans (obs (inl1 (Pulse id)) tt)
    (schedule_policy sch (S n) ts (Some i) st) u.
Proof.
  intro Hobs.
  setoid_rewrite (schedule_policy_focused_user_event_equ sch n ts i (Pulse id) k st Hobs).
  eexists; apply trans_vis.
Qed.

Theorem policy_program_choice_first (sch : Scheduler) st (a : Fin.t 2) :
  exists u, trans
    (obs (inl1 (Pulse (if Nat.eqb (slot_index a) 0 then 10 else 20))) tt)
    (schedule_policy sch 2 choice_pool (Some Fin.F1) st) u.
Proof.
  setoid_rewrite (schedule_policy_focused_br_equ sch 1 choice_pool Fin.F1
    (branchn 2) choice_body st eq_refl).
  destruct (focused_pulse_transition sch 1
    (choice_pool @ Fin.F1 := choice_body a) Fin.F1
    (if Nat.eqb (slot_index a) 0 then 10 else 20)
    (fun _ => Stuck) st eq_refl) as [u Hu].
  exists u; eapply trans_br with (x:=a); [exact Hu|reflexivity].
Qed.

Example nd_program_choice_both :
  (exists u, trans (obs (inl1 (Pulse 10)) tt)
    (schedule 2 choice_pool (Some Fin.F1)) u) /\
  (exists u, trans (obs (inl1 (Pulse 20)) tt)
    (schedule 2 choice_pool (Some Fin.F1)) u).
Proof.
  split; [exact (policy_program_choice_first nd_scheduler tt Fin.F1)|
          exact (policy_program_choice_first nd_scheduler tt (Fin.FS Fin.F1))].
Qed.

Example rr_program_choice_both cursor :
  (exists u, trans (obs (inl1 (Pulse 10)) tt)
    (schedule_rr 2 choice_pool (Some Fin.F1) cursor) u) /\
  (exists u, trans (obs (inl1 (Pulse 20)) tt)
    (schedule_rr 2 choice_pool (Some Fin.F1) cursor) u).
Proof.
  split; [exact (policy_program_choice_first rr_scheduler cursor Fin.F1)|
          exact (policy_program_choice_first rr_scheduler cursor (Fin.FS Fin.F1))].
Qed.

Example nd_program_choice_prefixes :
  events_sample 1000 1 [0]%list (schedule 2 choice_pool (Some Fin.F1)) =
    Some [(false,10)]%list /\
  events_sample 1000 1 [1]%list (schedule 2 choice_pool (Some Fin.F1)) =
    Some [(false,20)]%list.
Proof. vm_compute; split; reflexivity. Qed.

Example rr_program_choice_prefixes :
  events_sample 1000 1 [0]%list (schedule_rr 2 choice_pool (Some Fin.F1) 5) =
    Some [(false,10)]%list /\
  events_sample 1000 1 [1]%list (schedule_rr 2 choice_pool (Some Fin.F1) 5) =
    Some [(false,20)]%list.
Proof. vm_compute; split; reflexivity. Qed.

Definition empty_program_branch : thread pulseE Bn :=
  Br (branchn 0) (fun i => Fin.case0 (fun _ => thread pulseE Bn) i).

Example policy_empty_program_branch (sch : Scheduler) st :
  observe (schedule_policy sch 1 [empty_program_branch] (Some Fin.F1) st) =
  BrF (branchn 0) (fun a => schedule_policy sch 1
    ([empty_program_branch]%vector @ Fin.F1 :=
      Fin.case0 (fun _ => thread pulseE Bn) a) (Some Fin.F1) st).
Proof. apply schedule_policy_focused_br; reflexivity. Qed.

Example nd_empty_program_branch :
  events_sample 1000 1 List.nil
    (schedule 1 [empty_program_branch] (Some Fin.F1)) = None.
Proof. vm_compute; reflexivity. Qed.
Example rr_empty_program_branch :
  events_sample 1000 1 List.nil
    (schedule_rr 1 [empty_program_branch] (Some Fin.F1) 7) = None.
Proof. vm_compute; reflexivity. Qed.

(** 3. ND's hidden choice reports the actual selected vector slot. *)
Lemma nd_two_boundary :
  schedule 2 two_workers None ≅
    Br (branchn 2) (fun i => Vis (inr1 (Scheduled (slot_index i)))
      (fun _ => schedule 2 two_workers (Some i))).
Proof. step; reflexivity. Qed.

Example nd_pick0_then_pulse0 :
  exists u v,
    trans (obs (inr1 (Scheduled 0)) tt) (schedule 2 two_workers None) u /\
    trans (obs (inl1 (Pulse 0)) tt) u v.
Proof.
  destruct (focused_pulse_transition nd_scheduler 1 two_workers Fin.F1 0
    (fun _ => Br (branchn 1) (fun _ => Vis (inl1 Yield)
      (fun _ => worker 0 true))) tt eq_refl) as [v Hv].
  exists (schedule 2 two_workers (Some Fin.F1)), v; split; [|exact Hv].
  rewrite nd_two_boundary.
  eapply trans_br with (x:=Fin.F1); [|reflexivity].
  apply (trans_vis (inr1 (Scheduled 0)) tt).
Qed.

Example nd_pick1_then_pulse1 :
  exists u v,
    trans (obs (inr1 (Scheduled 1)) tt) (schedule 2 two_workers None) u /\
    trans (obs (inl1 (Pulse 1)) tt) u v.
Proof.
  destruct (focused_pulse_transition nd_scheduler 1 two_workers (Fin.FS Fin.F1) 1
    (fun _ => Vis (inl1 Yield) (fun _ => worker 1 false)) tt eq_refl) as [v Hv].
  exists (schedule 2 two_workers (Some (Fin.FS Fin.F1))), v; split; [|exact Hv].
  rewrite nd_two_boundary.
  eapply trans_br with (x:=Fin.FS Fin.F1); [|reflexivity].
  apply (trans_vis (inr1 (Scheduled 1)) tt).
Qed.

Theorem nd_first_label_is_scheduled l u :
  trans l (schedule 2 two_workers None) u ->
  exists i : Fin.t 2, l = obs (inr1 (Scheduled (slot_index i))) tt.
Proof.
  rewrite nd_two_boundary; intro H.
  apply trans_br_inv in H as [i H].
  apply trans_vis_inv in H as ([] & _ & Hl).
  exists i; exact Hl.
Qed.

Example nd_boundary_not_tau u : ~ trans τ (schedule 2 two_workers None) u.
Proof.
  intro H; apply nd_first_label_is_scheduled in H as [i H]; discriminate.
Qed.

Example nd_selected_prefixes :
  events_sample 1000 2 [0]%list (schedule 2 two_workers None) =
    Some [(true,0);(false,0)]%list /\
  events_sample 1000 2 [1]%list (schedule 2 two_workers None) =
    Some [(true,1);(false,1)]%list.
Proof. vm_compute; split; reflexivity. Qed.

Example nd_singleton_direct :
  observe (schedule 1 [worker0] None) =
    VisF (inr1 (Scheduled 0)) (fun _ => schedule 1 [worker0] (Some Fin.F1)).
Proof. reflexivity. Qed.

(** 4. A genuinely branching fair policy may repeat a cursor once. *)
Definition optional_duplicate_pick n (st : nat * bool) :
    Fin.t (S (if snd st then 0 else 1)) -> Fin.t (S n) * (nat * bool) :=
  match st as s return
    Fin.t (S (if snd s then 0 else 1)) -> Fin.t (S n) * (nat * bool) with
  | (cursor,true) => fun _ => (rr_pick n cursor, (S cursor,false))
  | (cursor,false) => fun a =>
      match a with
      | Fin.F1 => (rr_pick n cursor, (cursor,true))
      | Fin.FS _ => (rr_pick n cursor, (S cursor,false))
      end
  end.

Definition optional_duplicate_rr : Scheduler :=
  {| sched_state := (nat * bool)%type;
     sched_arity := fun _ st => if snd st then 0 else 1;
     sched_pick := optional_duplicate_pick |}.


Theorem optional_duplicate_eventually_picks n (i : Fin.t (S n)) st :
  EventuallyPicks optional_duplicate_rr n i st.
Proof.
  destruct st as [cursor duplicate_due].
  eapply eventually_picks_simulation with
    (source := rr_scheduler) (src := cursor)
    (Rel := fun (dst: nat * bool) (src: nat) => fst dst = src)
    (rank := fun (dst: nat * bool) => if snd dst then 0 else 1) (ltV := lt).
  - apply Nat.lt_wf_0.
  - intros [c due] src offer Hrel; cbn in Hrel; subst src; destruct due.
    + exists Fin.F1; split; [reflexivity | left; reflexivity].
    + dependent destruction offer.
      * exists Fin.F1; split; [reflexivity | right; split; [reflexivity | cbn; lia]].
      * exists Fin.F1; split; [reflexivity | left; reflexivity].
  - apply rr_eventually_picks.
  - reflexivity.
Qed.

#[global] Instance optional_duplicate_fair : FairScheduler optional_duplicate_rr :=
  eventually_picks_fair optional_duplicate_rr optional_duplicate_eventually_picks.

Definition fair_repeat_picks : option (list nat) :=
  sample 1000 8 true (List.repeat 0 8)
    (schedule_policy optional_duplicate_rr 2 two_workers None (0,false)).
Definition fair_advance_picks : option (list nat) :=
  sample 1000 8 true (List.repeat 1 8)
    (schedule_policy optional_duplicate_rr 2 two_workers None (0,false)).

Example fair_repeat_picks_correct :
  fair_repeat_picks = Some [0;0;1;1;0;0;1;1]%list.
Proof. vm_compute; reflexivity. Qed.
Example fair_advance_picks_correct :
  fair_advance_picks = Some [0;1;0;1;0;1;0;1]%list.
Proof. vm_compute; reflexivity. Qed.

Example policy_program_choice_prefixes :
  events_sample 1000 1 [0]%list
    (schedule_policy optional_duplicate_rr 2 choice_pool (Some Fin.F1) (5,false)) =
      Some [(false,10)]%list /\
  events_sample 1000 1 [1]%list
    (schedule_policy optional_duplicate_rr 2 choice_pool (Some Fin.F1) (5,false)) =
      Some [(false,20)]%list.
Proof. vm_compute; split; reflexivity. Qed.

Definition hpulse : pulseE ~> stateT nat (ctreeW nat Bn) :=
  fun X e sigma => match e in pulseE Y return ctreeW nat Bn (nat * Y) with
  | Pulse i => Vis (Log i) (fun _ => Ret (sigma,tt)) end.

Definition log_payload {A X} (e : writerE A X) : X * A :=
  match e in writerE _ Y return Y * A with Log x => (tt,x) end.

Definition fair_sample fuel needed script
    (t : ctreeW (nat + nat) Bn (nat * unit)) :=
  bounded_prefix (@log_payload (nat + nat)) (@Some (nat + nat))
    false fuel needed script t.

Example fair_pick_directly_precedes_worker :
  fair_sample 1000 2 [0]%list
    (interp_schedule_fair optional_duplicate_rr hpulse 2 two_workers None (0,false) 42) =
      Some [inr 0; inl 0]%list.
Proof. vm_compute; reflexivity. Qed.

Example fair_pick_not_program (P : nat -> Prop) i :
  ~ fair_obs P (inr i).
Proof. exact (fun H => H). Qed.

(** 5. Boundaries, faults, focus, fork, and removal use current positions. *)
Example empty_pool_no_pick (sch : Scheduler) st :
  observe (schedule_policy sch 0 ([] : pool pulseE Bn 0) None st) = RetF tt.
Proof. reflexivity. Qed.

Example rr_stuck_slot_selected :
  schedule_rr 2 [Stuck;worker1] None 0 ≅
    Vis (inr1 (Scheduled 0)) (fun _ => Stuck).
Proof.
  rewrite (observe_equ_go _ _ (schedule_rr_no_focus_nonempty 1
    [Stuck;worker1]%vector 0)).
  apply vis_equ_node; intros [].
  apply observe_equ_go; reflexivity.
Qed.

Example rr_stuck_slot_not_skipped :
  events_sample 1000 1 List.nil (schedule_rr 2 [Stuck;worker1] None 0) =
    Some [(true,0)]%list /\
  events_sample 1000 2 List.nil (schedule_rr 2 [Stuck;worker1] None 0) = None.
Proof. vm_compute; split; reflexivity. Qed.

Example initially_focused_no_pick :
  events_sample 1000 1 List.nil
    (schedule_rr 2 two_workers (Some Fin.F1) 13) = Some [(false,0)]%list.
Proof. vm_compute; reflexivity. Qed.

Definition fork_workers : thread pulseE Bn :=
  Vis (inr1 (inl1 Fork))
    (fun child : bool => if child then worker 1 false else worker 0 false).

Example focused_fork_parent_keeps_turn :
  events_sample 1000 5 List.nil
    (schedule_rr 1 [fork_workers] (Some Fin.F1) 0) =
      Some [(false,0);(true,0);(false,1);(true,1);(false,0)]%list.
Proof. vm_compute; reflexivity. Qed.

Example return_reindexes_slots :
  events_sample 1000 3 List.nil
    (schedule_rr 2 [Ret tt;worker1] None 0) =
      Some [(true,0);(true,0);(false,1)]%list.
Proof. vm_compute; reflexivity. Qed.

Example yield_does_not_spend_cursor :
  events_sample 1000 3 List.nil
    (schedule_rr 2 two_workers (Some Fin.F1) 1) =
      Some [(false,0);(true,1);(false,1)]%list.
Proof. vm_compute; reflexivity. Qed.

Example focused_return_does_not_spend_cursor :
  events_sample 1000 2 List.nil
    (schedule_rr 3 [Ret tt;worker 7 false;worker 8 false] (Some Fin.F1) 1) =
      Some [(true,1);(false,8)]%list.
Proof. vm_compute; reflexivity. Qed.

(** 6. Nondeterministic projection, logged RR, handler choices, and truthful offers. *)
Definition one_pulse id : thread pulseE Bn :=
  Vis (inr1 (inr1 (Pulse id))) (fun _ => Ret tt).

Record finite_result (A X : Type) := {
  silent_steps : nat;
  visible_events : list A;
  final_value : X
}.
Arguments silent_steps {A X} _.
Arguments visible_events {A X} _.
Arguments final_value {A X} _.

(** Unlike [bounded_prefix], this evaluator explicitly demands termination.
    It counts all Steps and records the final handler state. *)
Fixpoint finish_sample {E A X} (decode : forall Y, E Y -> Y * A)
    (fuel : nat) (script : list nat) (t : ctree E Bn X) : option (finite_result A X) :=
  match fuel with
  | 0 => None
  | S fuel' => match observe t with
    | RetF x => Some {| silent_steps := 0; visible_events := List.nil; final_value := x |}
    | StuckF => None
    | GuardF u => finish_sample decode fuel' script u
    | StepF u => match finish_sample decode fuel' script u with
        | Some r => Some {| silent_steps := S (silent_steps r);
            visible_events := visible_events r; final_value := final_value r |}
        | None => None end
    | VisF e k => let '(answer,event) := decode _ e in
        match finish_sample decode fuel' script (k answer) with
        | Some r => Some {| silent_steps := silent_steps r;
            visible_events := List.cons event (visible_events r); final_value := final_value r |}
        | None => None end
    | BrF (branchn arity) k =>
        match arity as m return (Fin.t m -> ctree E Bn X) -> option (finite_result A X) with
        | 0 => fun _ => None
        | 1 => fun k => finish_sample decode fuel' script (k Fin.F1)
        | S (S m) => fun k => match script with
            | List.nil => None
            | List.cons i rest => match lt_dec i (S (S m)) with
                | left Hi => finish_sample decode fuel' rest (k (Fin.of_nat_lt Hi))
                | right _ => None end
            end
        end k
    end
  end.

Example nd_selection_one_tau_state sigma :
  finish_sample (@log_payload nat) 1000 List.nil
    (interp_schedule_nd hpulse 1 [one_pulse 7] None sigma) =
  Some {| silent_steps := 1; visible_events := [7]%list; final_value := (sigma,tt) |}.
Proof. vm_compute; reflexivity. Qed.

Example rr_selection_one_log_state sigma :
  finish_sample (@log_payload (nat + nat)) 1000 List.nil
    (interp_schedule_rr hpulse 1 [one_pulse 7] None 0 sigma) =
  Some {| silent_steps := 0; visible_events := [inr 0; inl 7]%list;
          final_value := (sigma,tt) |}.
Proof. vm_compute; reflexivity. Qed.

Lemma nd_singleton_selection_exact sigma :
  interp_schedule_nd hpulse 1 [one_pulse 7] None sigma ≅
  Step (guards 2 (interp_schedule_nd hpulse 1 [one_pulse 7] (Some Fin.F1) sigma)).
Proof.
  unfold interp_schedule_nd at 1.
  rewrite (observe_equ_go _ _ (schedule_no_focus_nonempty 0 [one_pulse 7]%vector)),
    project_scheduled_scheduled, interp_state_step, interp_state_guard.
  reflexivity.
Qed.

Theorem nd_selection_world_unchanged sigma w u w' :
  ktrans (interp_schedule_nd hpulse 1 [one_pulse 7] None sigma) w u w' <->
    u ≅ guards 2 (interp_schedule_nd hpulse 1 [one_pulse 7] (Some Fin.F1) sigma) /\
    w = w' /\ not_done w.
Proof. rewrite nd_singleton_selection_exact; apply ktrans_step. Qed.

Theorem rr_selection_world_logged sigma w u w' :
  ktrans (interp_schedule_rr hpulse 1 [one_pulse 7] None 0 sigma) w u w' <->
    u ≅ Guard (interp_schedule_rr hpulse 1 [one_pulse 7] (Some Fin.F1) 1 sigma) /\
    w' = Obs (Log (inr 0)) tt /\ not_done w.
Proof.
  rewrite (segment_rr_select_exact hpulse 0 [one_pulse 7]%vector 0 sigma), ktrans_vis.
  split.
  - intros ([] & -> & Hu & Hw); split; [symmetry; exact Hu|split; [reflexivity|exact Hw]].
  - intros (Hu & -> & Hw); exists tt; split; [reflexivity|split; [symmetry; exact Hu|exact Hw]].
Qed.

Example fair_selection_one_log_state sigma :
  finish_sample (@log_payload (nat + nat)) 1000 [0]%list
    (interp_schedule_fair optional_duplicate_rr hpulse 1 [one_pulse 7] None (0,false) sigma) =
  Some {| silent_steps := 0; visible_events := [inr 0;inl 7]%list;
          final_value := (sigma,tt) |}.
Proof. vm_compute; reflexivity. Qed.

Definition branching_hpulse : pulseE ~> stateT nat (ctreeW nat Bn) :=
  fun X e sigma => match e in pulseE Y return ctreeW nat Bn (nat * Y) with
  | Pulse _ => Br (branchn 2) (fun i =>
      Vis (Log (if Nat.eqb (slot_index i) 0 then 10 else 20))
        (fun _ => Ret (sigma,tt))) end.

Definition program_log_sample fuel needed script (t : ctreeW nat Bn (nat * unit)) :=
  bounded_prefix (@log_payload nat) (@Some nat) true fuel needed script t.

Example nd_handler_choices_preserved :
  program_log_sample 1000 1 [0]%list
    (interp_schedule_nd branching_hpulse 1 [one_pulse 7] None 42) = Some [10]%list /\
  program_log_sample 1000 1 [1]%list
    (interp_schedule_nd branching_hpulse 1 [one_pulse 7] None 42) = Some [20]%list.
Proof. vm_compute; split; reflexivity. Qed.

Example rr_handler_choices_preserved :
  fair_sample 1000 2 [0]%list
    (interp_schedule_rr branching_hpulse 1 [one_pulse 7] None 0 42) =
      Some [inr 0; inl 10]%list /\
  fair_sample 1000 2 [1]%list
    (interp_schedule_rr branching_hpulse 1 [one_pulse 7] None 0 42) =
      Some [inr 0; inl 20]%list.
Proof. vm_compute; split; reflexivity. Qed.

Example fair_handler_choices_preserved :
  fair_sample 1000 2 [0;0]%list
    (interp_schedule_fair optional_duplicate_rr branching_hpulse 1 [one_pulse 7]
      None (0,false) 42) = Some [inr 0;inl 10]%list /\
  fair_sample 1000 2 [0;1]%list
    (interp_schedule_fair optional_duplicate_rr branching_hpulse 1 [one_pulse 7]
      None (0,false) 42) = Some [inr 0;inl 20]%list.
Proof. vm_compute; split; reflexivity. Qed.

Inductive sampled_event :=
| Point : nat -> sampled_event
| Offered : nat -> nat -> sampled_event
| Pick : nat -> sampled_event
| User : nat -> sampled_event.

Definition observed_payload {X} (e : scheduler_observedE pulseE X) : X * sampled_event :=
  match e with
  | inl1 o => match o in SchedulerObs Y return Y * sampled_event with
      | ObsSchedulingPoint n => (tt,Point n)
      | ObsOffered slot => (tt,Offered (slot_pool_size slot)
          (slot_index (slot_live_slot slot))) end
  | inr1 (inl1 p) => match p in pulseE Y return Y * sampled_event with
      | Pulse i => (tt,User i) end
  | inr1 (inr1 s) => match s in schedE Y return Y * sampled_event with
      | Scheduled i => (tt,Pick i) end
  end.

Definition offer_sample fuel needed script (t : observed_completed pulseE Bn) :=
  bounded_prefix (@observed_payload) (@Some sampled_event) true fuel needed script t.

Example offers_precede_selection0 :
  offer_sample 1000 5 [0]%list (schedule_with_offers 2 two_workers None) =
    Some [Point 2;Offered 2 0;Offered 2 1;Pick 0;User 0]%list.
Proof. vm_compute; reflexivity. Qed.
Example offers_precede_selection1 :
  offer_sample 1000 5 [1]%list (schedule_with_offers 2 two_workers None) =
    Some [Point 2;Offered 2 0;Offered 2 1;Pick 1;User 1]%list.
Proof. vm_compute; reflexivity. Qed.

Theorem forgetting_offers_agrees_with_nd :
  forget_scheduler_offers (schedule_with_offers 2 two_workers None) ~
    schedule 2 two_workers None.
Proof. apply forget_scheduler_offers_preserves_schedule. Qed.

Example forgetting_offers_preserves_selected_observations :
  events_sample 1000 2 [1]%list
    (forget_scheduler_offers (schedule_with_offers 2 two_workers None)) =
    Some [(true,1);(false,1)]%list /\
  events_sample 1000 2 [1]%list (schedule 2 two_workers None) =
    Some [(true,1);(false,1)]%list.
Proof. vm_compute; split; reflexivity. Qed.

(** Failure behavior is part of the prefix evaluator's contract, not a
    default interpretation of unfinished executions. *)
Example prefix_failures_are_not_successes :
  events_sample 0 1 List.nil (schedule_rr 2 two_workers None 0) = None /\
  events_sample 1000 1 List.nil (Ret tt) = None /\
  events_sample 1000 1 List.nil Stuck = None /\
  events_sample 1000 1 List.nil (schedule 2 two_workers None) = None /\
  events_sample 1000 1 [2]%list (schedule 2 two_workers None) = None /\
  sample 1000 2 false List.nil (schedule_rr 1 [one_pulse 7] None 0) = None.
Proof. vm_compute; repeat split; reflexivity. Qed.
