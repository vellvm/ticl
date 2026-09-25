(** * Constructive counterexamples for the allocator's liveness premises.

    Two infinite executions of the actual model, each realized by the actual
    source program:

    - [Starvation]: fair choices under which remote 1 holds block 8 forever
      and retries its CAS infinitely often, while block 6 keeps cycling
      through retire, reclaim and allocation;
    - [OwnerStall]: after turn 5 the owner is never selected, so block 6,
      retired at turn 8, is never reclaimed.

    Witness scripts, heaps and observation tables are section [Let]s: they
    are discharged into the public statements and leave no global name.  The
    periodic heaps are pointwise representatives only; every execution state
    is the actual result of its preceding turns, never a reset. *)

From Stdlib Require Import List Lia Arith.PeanoNat.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Program
  CSL.Allocator.Model CSL.Allocator.Execution CSL.Allocator.Liveness.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Trans ICTree.Trace ICTree.Interp.Yield.Execution.
From TICL Require Import Utils.Relations Utils.Lists Utils.Execution.

Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Section Starvation.

Let starvation_cycle : list Actor :=
  [Remote1; Remote1; Remote0; Remote0; Remote0; Remote0; Remote1;
   Owner; Owner; Owner; Owner; Owner; Owner].
Let starvation_prefix : list Actor :=
  [Owner; Owner; Owner; Owner; Owner; Remote1] ++ starvation_cycle.

Let starve_prefix_logs (c : nat) : list (indexed (nat * nat)) :=
  [stamp (tag_alloc,6) c; stamp (tag_alloc,8) (1+c);
   stamp (tag_retire,6) (2+c); stamp (tag_retry,8) (3+c);
   stamp (tag_reclaim,6) (4+c); stamp (tag_alloc,6) (5+c)].
Let starve_cycle_logs (c : nat) : list (indexed (nat * nat)) :=
  [stamp (tag_retire,6) c; stamp (tag_retry,8) (1+c);
   stamp (tag_reclaim,6) (2+c); stamp (tag_alloc,6) (3+c)].

(** A pointwise representative only: the infinite witness always retains
    the actual heap returned by its preceding turn. *)
Let starve_boundary_heap : Heap := fun x =>
  match x with
  | 1 => Some 0 | 2 => Some 0 | 3 => Some 0 | 4 => Some 6
  | 5 => Some 0 | 6 => Some 0 | 7 => Some 1 | 8 => Some 0
  | 9 => Some 2 | _ => None
  end.
Let starve_boundary (c : nat) : AState :=
  {| aheap := starve_boundary_heap; acount := c;
     owner_state := ORead; remote0_state := RPoll;
     remote1_state := RRead 8 |}.

(** The observation of each individual turn, including every silent turn. *)
Let starve_prefix_event (c i : nat) : option (indexed (nat * nat)) :=
  match i with
  | 3 => Some (stamp (tag_alloc,6) c)
  | 4 => Some (stamp (tag_alloc,8) (1+c))
  | 11 => Some (stamp (tag_retire,6) (2+c))
  | 12 => Some (stamp (tag_retry,8) (3+c))
  | 15 => Some (stamp (tag_reclaim,6) (4+c))
  | 17 => Some (stamp (tag_alloc,6) (5+c))
  | _ => None
  end.
Let starve_cycle_event (c i : nat) : option (indexed (nat * nat)) :=
  match i with
  | 5 => Some (stamp (tag_retire,6) c)
  | 6 => Some (stamp (tag_retry,8) (1+c))
  | 9 => Some (stamp (tag_reclaim,6) (2+c))
  | 11 => Some (stamp (tag_alloc,6) (3+c))
  | _ => None
  end.

Local Lemma starve_prefix_run c : exists last,
  run_turns (turn 1) event_obs starvation_prefix (initial_state 2 c) =
    Some (last,starve_prefix_logs c) /\
  state_equiv last (starve_boundary (6+c)).
Proof.
  eexists; split; [vm_compute; reflexivity|].
  unfold state_equiv; split.
  - intro x.
    do 10 (destruct x as [|x]; [vm_compute; reflexivity|]).
    vm_compute; reflexivity.
  - vm_compute; repeat split; reflexivity.
Qed.

Local Lemma starve_cycle_run c : exists last,
  run_turns (turn 1) event_obs starvation_cycle (starve_boundary c) =
    Some (last,starve_cycle_logs c) /\
  state_equiv last (starve_boundary (4+c)).
Proof.
  eexists; split; [vm_compute; reflexivity|].
  unfold state_equiv; split.
  - intro x.
    do 10 (destruct x as [|x]; [vm_compute; reflexivity|]).
    vm_compute; reflexivity.
  - vm_compute; repeat split; reflexivity.
Qed.

Local Lemma starve_cycle_run_actual c s :
  state_equiv s (starve_boundary c) ->
  exists last,
    run_turns (turn 1) event_obs starvation_cycle s = Some (last,starve_cycle_logs c) /\
    state_equiv last (starve_boundary (4+c)).
Proof.
  intro Hs; destruct (starve_cycle_run c) as (last & Hrun & Hlast).
  destruct (run_turns_some_compatible (turn 1) event_obs state_equiv (turn_proper 1)
    starvation_cycle (starve_boundary c) s last (starve_cycle_logs c)
    (state_equiv_sym _ _ Hs) Hrun) as (actual & Hactual & Heq).
  exists actual; split; [exact Hactual|].
  eapply state_equiv_trans; [apply state_equiv_sym; exact Heq|exact Hlast].
Qed.

Local Lemma starve_prefix_position c i : i < 19 ->
  exists middle logs next,
    run_turns (turn 1) event_obs (List.firstn i starvation_prefix) (initial_state 2 c) =
      Some (middle,logs) /\
    turn 1 (List.nth i starvation_prefix Remote1) middle =
      Some (next,starve_prefix_event c i).
Proof.
  intro Hi.
  do 19 (destruct i as [|i];
    [eexists; eexists; eexists; split; vm_compute; reflexivity|]).
  lia.
Qed.

Local Lemma starve_cycle_position c i : i < 13 ->
  exists middle logs next,
    run_turns (turn 1) event_obs (List.firstn i starvation_cycle) (starve_boundary c) =
      Some (middle,logs) /\
    held (remote1_state middle) = [8] /\
    turn 1 (List.nth i starvation_cycle Remote1) middle =
      Some (next,starve_cycle_event c i).
Proof.
  intro Hi.
  do 13 (destruct i as [|i];
    [eexists; eexists; eexists; split;
      [vm_compute; reflexivity|]; split;
      [vm_compute; reflexivity|vm_compute; reflexivity]|]).
  lia.
Qed.

(** The infinite execution follows the periodic script from the actual
    initial state.  It is bound only after the finite calculations above,
    whose existential witnesses must not range over its closure. *)
Let starvation_choices : nat -> Actor :=
  periodic_choices starvation_prefix Remote1 (List.tl starvation_cycle).
Let starvation_execution : Execution AState Actor (option (indexed (nat * nat))) :=
  allocator_execution 2 0 starvation_choices.

Local Lemma starvation_execution_valid : allocator_valid 2 0 starvation_execution.
Proof. unfold starvation_execution, allocator_execution; apply execution_of_choices_valid. Qed.

Local Lemma starve_prefix_script :
  List.map (selected starvation_execution)
    (List.seq 0 (List.length starvation_prefix)) = starvation_prefix.
Proof.
  change (List.map
    (periodic_choices starvation_prefix Remote1 (List.tl starvation_cycle))
    (List.seq 0 (List.length starvation_prefix)) = starvation_prefix).
  apply periodic_prefix_script.
Qed.

Local Lemma starve_selected_prefix k : k < 19 ->
  selected starvation_execution k = List.nth k starvation_prefix Remote1.
Proof.
  intro Hk; change (starvation_choices k = List.nth k starvation_prefix Remote1).
  unfold starvation_choices; apply periodic_choices_before; exact Hk.
Qed.

Local Lemma starve_selected_cycle n i : i < 13 ->
  selected starvation_execution (19+13*n+i) =
    List.nth i starvation_cycle Remote1.
Proof.
  intro Hi.
  change (periodic_choices starvation_prefix Remote1 (List.tl starvation_cycle)
    (19+13*n+i) = List.nth i starvation_cycle Remote1).
  replace (19+13*n+i) with
    (List.length starvation_prefix + n * S (List.length (List.tl starvation_cycle)) + i)
    by (cbn [starvation_prefix starvation_cycle List.length List.tl List.app]; lia).
  apply periodic_choices_round; exact Hi.
Qed.

Local Lemma starve_cycle_script n :
  List.map (selected starvation_execution)
    (List.seq (19+13*n) (List.length starvation_cycle)) = starvation_cycle.
Proof.
  apply (map_seq_eq _ _ _ _ Remote1); [reflexivity|].
  intros i Hi; apply starve_selected_cycle; exact Hi.
Qed.

Local Lemma starve_initial_equiv :
  state_equiv (states starvation_execution 0) (initial_state 2 0).
Proof.
  rewrite (proj1 starvation_execution_valid); apply state_equiv_refl.
Qed.

Local Lemma starve_boundaries n :
  state_equiv (states starvation_execution (19+13*n))
    (starve_boundary (6+4*n)).
Proof.
  induction n as [|n IH].
  - destruct (starve_prefix_run 0) as (last & Hrun & Hlast).
    eapply state_equiv_trans; [|exact Hlast].
    destruct (execution_window_state (turn 1) event_obs
      (fun s => s = initial_state 2 0) state_equiv (turn_proper 1)
      starvation_execution 0 (List.length starvation_prefix) (initial_state 2 0)
      starvation_execution_valid starve_initial_equiv) as (actual & Hactual & Hstate).
    rewrite starve_prefix_script, Hrun in Hactual.
    assert (Elast : actual = last) by congruence; subst actual.
    replace (19+13*0) with (0 + List.length starvation_prefix) by reflexivity.
    exact Hstate.
  - destruct (starve_cycle_run (6+4*n)) as (last & Hrun & Hlast).
    replace (6+4*S n) with (4+(6+4*n)) by lia.
    eapply state_equiv_trans; [|exact Hlast].
    replace (19+13*S n) with
      ((19+13*n)+List.length starvation_cycle)
      by (cbn [starvation_cycle List.length]; lia).
    destruct (execution_window_state (turn 1) event_obs
      (fun s => s = initial_state 2 0) state_equiv (turn_proper 1)
      starvation_execution (19+13*n) (List.length starvation_cycle)
      (starve_boundary (6+4*n)) starvation_execution_valid IH)
      as (actual & Hactual & Hstate).
    rewrite starve_cycle_script, Hrun in Hactual.
    assert (Elast : actual = last) by congruence; subst actual; exact Hstate.
Qed.

Local Lemma starve_actual_cycle_run n : exists last,
  run_turns (turn 1) event_obs starvation_cycle (states starvation_execution (19+13*n)) =
    Some (last,starve_cycle_logs (6+4*n)) /\
  state_equiv last (starve_boundary (6+4*S n)).
Proof.
  replace (6+4*S n) with (4+(6+4*n)) by lia.
  apply starve_cycle_run_actual; apply starve_boundaries.
Qed.

(** Every intermediate state is the result of a finite fold from the actual
    returned boundary, not from a periodically reset representative. *)
Local Lemma starve_actual_cycle_position n i : i < 13 ->
  exists logs next,
    run_turns (turn 1) event_obs (List.firstn i starvation_cycle)
      (states starvation_execution (19+13*n)) =
      Some (states starvation_execution (19+13*n+i),logs) /\
    held (remote1_state (states starvation_execution (19+13*n+i))) = [8] /\
    turn 1 (List.nth i starvation_cycle Remote1)
      (states starvation_execution (19+13*n+i)) =
      Some (next,starve_cycle_event (6+4*n) i).
Proof.
  intro Hi.
  destruct (starve_cycle_position (6+4*n) i Hi)
    as (middle & logs & next & Hrun & Hheld & Hturn).
  destruct (run_turns_some_compatible (turn 1) event_obs state_equiv (turn_proper 1)
    (List.firstn i starvation_cycle)
    (starve_boundary (6+4*n)) (states starvation_execution (19+13*n))
    middle logs (state_equiv_sym _ _ (starve_boundaries n)) Hrun)
    as (actual & Hactual & Heq).
  assert (Hscript : List.map (selected starvation_execution)
    (List.seq (19+13*n) i) = List.firstn i starvation_cycle).
  {
    rewrite <- (map_seq_firstn (selected starvation_execution) (19+13*n)
      (List.length starvation_cycle) i ltac:(change (i <= 13); lia)).
    rewrite (starve_cycle_script n); reflexivity.
  }
  pose proof (execution_run_turns (turn 1) event_obs
    (fun s => s = initial_state 2 0) starvation_execution (19+13*n) i
    starvation_execution_valid) as Hwindow.
  rewrite Hscript, Hactual in Hwindow.
  assert (Estate : actual = states starvation_execution (19+13*n+i))
    by congruence.
  subst actual.
  destruct (step_some_compatible (turn 1) state_equiv (turn_proper 1)
    (List.nth i starvation_cycle Remote1)
    middle (states starvation_execution (19+13*n+i)) next
    (starve_cycle_event (6+4*n) i) Heq Hturn)
    as (actual_next & Hnext & Hnext_eq).
  exists logs, actual_next; split; [exact Hactual|]; split; [|exact Hnext].
  destruct Heq as (_ & _ & _ & _ & Hremote1).
  rewrite <- Hremote1; exact Hheld.
Qed.

Local Lemma starve_cycle_emitted n i : i < 13 ->
  emitted starvation_execution (19+13*n+i) = starve_cycle_event (6+4*n) i.
Proof.
  intro Hi.
  destruct (starve_actual_cycle_position n i Hi)
    as (logs & next & Hrun & Hheld & Hturn).
  pose proof (execution_step (turn 1) (fun s => s = initial_state 2 0)
    starvation_execution (19+13*n+i) starvation_execution_valid) as Hstep.
  rewrite (starve_selected_cycle n i Hi), Hturn in Hstep; congruence.
Qed.

Local Lemma starve_prefix_emitted i : i < 19 ->
  emitted starvation_execution i = starve_prefix_event 0 i.
Proof.
  intro Hi.
  destruct (starve_prefix_position 0 i Hi) as (middle & logs & next & Hrun & Hturn).
  assert (Hscript : List.map (selected starvation_execution) (List.seq 0 i) =
    List.firstn i starvation_prefix).
  {
    rewrite <- (map_seq_firstn (selected starvation_execution) 0
      (List.length starvation_prefix) i ltac:(change (i <= 19); lia)).
    rewrite starve_prefix_script; reflexivity.
  }
  destruct (execution_window_state (turn 1) event_obs
    (fun s => s = initial_state 2 0) state_equiv (turn_proper 1)
    starvation_execution 0 i (initial_state 2 0)
    starvation_execution_valid starve_initial_equiv) as (actual & Hactual & Heq).
  rewrite Hscript, Hrun in Hactual.
  assert (Emiddle : actual = middle) by congruence; subst actual.
  rewrite Nat.add_0_l in Heq.
  rewrite <- (starve_selected_prefix i Hi) in Hturn.
  destruct (execution_turn_observation (turn 1) (fun s => s = initial_state 2 0)
    state_equiv (turn_proper 1) starvation_execution i middle
    starvation_execution_valid Heq) as (next' & Hturn' & _).
  rewrite Hturn in Hturn'; congruence.
Qed.

Local Lemma starve_cycle_event_offsets n :
  emitted starvation_execution (19+13*n+5) = Some (stamp (tag_retire,6) (6+4*n)) /\
  emitted starvation_execution (19+13*n+6) = Some (stamp (tag_retry,8) (1+(6+4*n))) /\
  emitted starvation_execution (19+13*n+9) = Some (stamp (tag_reclaim,6) (2+(6+4*n))) /\
  emitted starvation_execution (19+13*n+11) = Some (stamp (tag_alloc,6) (3+(6+4*n))).
Proof.
  split; [exact (starve_cycle_emitted n 5 ltac:(lia))|].
  split; [exact (starve_cycle_emitted n 6 ltac:(lia))|].
  split; [exact (starve_cycle_emitted n 9 ltac:(lia))|].
  exact (starve_cycle_emitted n 11 ltac:(lia)).
Qed.

Local Lemma starve_index k : 19 <= k ->
  exists n i, i < 13 /\ k = 19+13*n+i.
Proof.
  intro Hk; exists ((k-19)/13), ((k-19) mod 13); split.
  - apply Nat.mod_upper_bound; lia.
  - pose proof (Nat.div_mod (k-19) 13 ltac:(lia)); lia.
Qed.

Local Lemma starve_fair : fair_choices (selected starvation_execution).
Proof.
  intros actor lo; destruct actor.
  - exists (19+13*lo+7); split; [lia|].
    exact (starve_selected_cycle lo 7 ltac:(lia)).
  - exists (19+13*lo+2); split; [lia|].
    exact (starve_selected_cycle lo 2 ltac:(lia)).
  - exists (19+13*lo+0); split; [lia|].
    exact (starve_selected_cycle lo 0 ltac:(lia)).
Qed.

Local Lemma starve_held_forever k : 19 <= k ->
  held (remote1_state (states starvation_execution k)) = [8].
Proof.
  intro Hk; destruct (starve_index k Hk) as (n & i & Hi & ->).
  destruct (starve_actual_cycle_position n i Hi)
    as (logs & next & Hrun & Hheld & Hturn); exact Hheld.
Qed.

Local Lemma starve_prefix_never_retire8 c i idx : i < 19 ->
  starve_prefix_event c i <> Some (stamp (tag_retire,8) idx).
Proof.
  intro Hi.
  do 19 (destruct i as [|i]; [vm_compute; discriminate|]).
  lia.
Qed.
Local Lemma starve_cycle_never_retire8 c i idx : i < 13 ->
  starve_cycle_event c i <> Some (stamp (tag_retire,8) idx).
Proof.
  intro Hi.
  do 13 (destruct i as [|i]; [vm_compute; discriminate|]).
  lia.
Qed.

Local Lemma starve_never_retire8 k :
  ~ block_event tag_retire 8 (emitted starvation_execution k).
Proof.
  intros [idx Hevent]; destruct (Nat.lt_ge_cases k 19) as [Hprefix|Hcycle].
  - rewrite (starve_prefix_emitted k Hprefix) in Hevent.
    exact (starve_prefix_never_retire8 0 k idx Hprefix Hevent).
  - destruct (starve_index k Hcycle) as (n & i & Hi & ->).
    rewrite (starve_cycle_emitted n i Hi) in Hevent.
    exact (starve_cycle_never_retire8 (6+4*n) i idx Hi Hevent).
Qed.

Local Lemma starve_infinitely_retry8 :
  infinitely (fun k => block_event tag_retry 8 (emitted starvation_execution k)).
Proof.
  intro lo; exists (19+13*lo+6); split; [lia|].
  exists (1+(6+4*lo)); exact (starve_cycle_emitted lo 6 ltac:(lia)).
Qed.
Local Lemma starve_infinitely_retire6 :
  infinitely (fun k => block_event tag_retire 6 (emitted starvation_execution k)).
Proof.
  intro lo; exists (19+13*lo+5); split; [lia|].
  exists (6+4*lo); exact (starve_cycle_emitted lo 5 ltac:(lia)).
Qed.
Local Lemma starve_infinitely_reclaim6 :
  infinitely (fun k => block_event tag_reclaim 6 (emitted starvation_execution k)).
Proof.
  intro lo; exists (19+13*lo+9); split; [lia|].
  exists (2+(6+4*lo)); exact (starve_cycle_emitted lo 9 ltac:(lia)).
Qed.
Local Lemma starve_infinitely_alloc6 :
  infinitely (fun k => block_event tag_alloc 6 (emitted starvation_execution k)).
Proof.
  intro lo; exists (19+13*lo+11); split; [lia|].
  exists (3+(6+4*lo)); exact (starve_cycle_emitted lo 11 ltac:(lia)).
Qed.

Theorem fair_starvation_exists : exists e,
  allocator_valid 2 0 e /\ fair_choices (selected e) /\
  (forall k, 19 <= k -> held (remote1_state (states e k)) = [8]) /\
  infinitely (fun k => block_event tag_retry 8 (emitted e k)) /\
  (forall k, ~ block_event tag_retire 8 (emitted e k)) /\
  infinitely (fun k => block_event tag_retire 6 (emitted e k)) /\
  infinitely (fun k => block_event tag_reclaim 6 (emitted e k)) /\
  infinitely (fun k => block_event tag_alloc 6 (emitted e k)) /\
  realizes (fun j => turn_labels (emitted e j)) 0 (run_nd (allocator_program 2) hemp 0).
Proof.
  exists starvation_execution.
  split; [exact starvation_execution_valid|].
  split; [exact starve_fair|].
  split; [exact starve_held_forever|].
  split; [exact starve_infinitely_retry8|].
  split; [exact starve_never_retire8|].
  split; [exact starve_infinitely_retire6|].
  split; [exact starve_infinitely_reclaim6|].
  split; [exact starve_infinitely_alloc6|].
  apply valid_execution_realizes_source; exact starvation_execution_valid.
Qed.

(** The first cycle, chained from the ACTUAL prefix result, is a finite
    source trace with one genuine scheduler tau per turn. *)
Theorem starvation_chained_cycle_actual_source : exists last labels residual,
  run_turns (turn 1) event_obs (starvation_prefix ++ starvation_cycle) (initial_state 2 0) =
    Some (last,starve_prefix_logs 0 ++ starve_cycle_logs 6) /\
  label_logs labels = starve_prefix_logs 0 ++ starve_cycle_logs 6 /\
  label_taus labels = 32 /\
  finite_steps (run_nd (allocator_program 2) hemp 0) labels residual /\
  residual ~ (model_nd 2 actor_of_slot (turn 1) last
                : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  destruct (starve_prefix_run 0) as (first & Hprefix & Hfirst).
  destruct (starve_cycle_run_actual 6 first Hfirst) as (last & Hcycle & Hlast).
  pose proof (run_turns_compose (turn 1) event_obs
    starvation_prefix starvation_cycle
    (initial_state 2 0) first last (starve_prefix_logs 0) (starve_cycle_logs 6)
    Hprefix Hcycle) as Hrun.
  destruct (run_turns_realizes_source 2 0 (starvation_prefix ++ starvation_cycle)
    last (starve_prefix_logs 0 ++ starve_cycle_logs 6) Hrun)
    as (labels & residual & Hlabels & Hlogs & Htaus & Hsteps & Htail).
  exists last, labels, residual; repeat first [assumption | split].
Qed.

End Starvation.

Section OwnerStall.

Let owner_stall_prefix : list Actor :=
  List.repeat Owner 5 ++ List.repeat Remote0 4 ++ List.repeat Remote1 4.
Let owner_stall_cycle : list Actor := [Remote0; Remote1].
Let owner_stall_choices : nat -> Actor :=
  periodic_choices owner_stall_prefix Remote0 [Remote1].

Let stalled_prefix_logs (c : nat) : list (indexed (nat * nat)) :=
  [stamp (tag_alloc,6) c; stamp (tag_alloc,8) (1+c);
   stamp (tag_retire,6) (2+c); stamp (tag_retire,8) (3+c)].

Let stalled_prefix_observations : list (option (indexed (nat * nat))) :=
  [None; None; None; Some (stamp (tag_alloc,6) 0);
   Some (stamp (tag_alloc,8) 1); None; None; None;
   Some (stamp (tag_retire,6) 2); None; None; None;
   Some (stamp (tag_retire,8) 3)].

(** This is only a pointwise representative of the returned heap.  The
    execution always runs the actual preceding turn. *)
Let stalled_boundary_heap : Heap := fun x =>
  match x with
  | 1 => Some 8 | 2 => Some 0 | 3 => Some 0 | 4 => Some 0
  | 5 => Some 0 | 6 => Some 0 | 7 => Some 1 | 8 => Some 6
  | 9 => Some 2 | _ => None
  end.
Let stalled_boundary (c : nat) : AState :=
  {| aheap := stalled_boundary_heap; acount := c;
     owner_state := ORead; remote0_state := RPoll;
     remote1_state := RPoll |}.

Local Lemma stalled_prefix_run c : exists last,
  run_turns (turn 1) event_obs owner_stall_prefix (initial_state 2 c) =
    Some (last,stalled_prefix_logs c) /\
  state_equiv last (stalled_boundary (c+4)).
Proof.
  replace (c+4) with (4+c) by lia.
  eexists; split; [vm_compute; reflexivity|].
  unfold state_equiv; split.
  - intro x.
    do 10 (destruct x as [ | x ]; [vm_compute; reflexivity|]).
    vm_compute; reflexivity.
  - vm_compute; repeat split; reflexivity.
Qed.

Local Lemma stalled_polling_turn c who :
  who = Remote0 \/ who = Remote1 ->
  turn 1 who (stalled_boundary c) = Some (stalled_boundary c,None).
Proof.
  intros [-> | ->]; vm_compute; reflexivity.
Qed.

Local Lemma stalled_cycle_run c :
  run_turns (turn 1) event_obs owner_stall_cycle (stalled_boundary c) =
    Some (stalled_boundary c,[]).
Proof. reflexivity. Qed.

(** Transfer the finite polling calculation to the actual accumulated heap;
    neither this lemma nor the infinite witness resets that heap. *)
Local Lemma stalled_cycle_run_actual c s :
  state_equiv s (stalled_boundary c) ->
  exists last, run_turns (turn 1) event_obs owner_stall_cycle s = Some (last,[]) /\
    state_equiv last s.
Proof.
  intro Hs.
  destruct (run_turns_some_compatible (turn 1) event_obs state_equiv (turn_proper 1)
    owner_stall_cycle (stalled_boundary c) s (stalled_boundary c) []
    (state_equiv_sym _ _ Hs) (stalled_cycle_run c))
    as (last & Hrun & Hlast).
  exists last; split; [exact Hrun|].
  eapply state_equiv_trans; [apply state_equiv_sym; exact Hlast|].
  apply state_equiv_sym; exact Hs.
Qed.

Local Lemma stalled_prefix_position k : k < 13 ->
  exists before after logs,
    run_turns (turn 1) event_obs (List.firstn k owner_stall_prefix) (initial_state 2 0) =
      Some (before,logs) /\
    turn 1 (owner_stall_choices k) before =
      Some (after,List.nth k stalled_prefix_observations None).
Proof.
  intro Hk.
  do 13 (destruct k as [ | k ];
    [eexists; eexists; eexists; split; vm_compute; reflexivity|]).
  lia.
Qed.

(** The infinite execution follows the periodic script from the actual
    initial state; bound after the finite calculations above. *)
Let owner_stall_execution : Execution AState Actor (option (indexed (nat * nat))) :=
  allocator_execution 2 0 owner_stall_choices.

Local Lemma owner_stall_execution_valid : allocator_valid 2 0 owner_stall_execution.
Proof. unfold owner_stall_execution, allocator_execution; apply execution_of_choices_valid. Qed.

Local Lemma stalled_prefix_script :
  List.map (selected owner_stall_execution)
    (List.seq 0 (List.length owner_stall_prefix)) = owner_stall_prefix.
Proof.
  change (List.map (periodic_choices owner_stall_prefix Remote0 [Remote1])
    (List.seq 0 (List.length owner_stall_prefix)) = owner_stall_prefix).
  apply periodic_prefix_script.
Qed.

Local Lemma stalled_initial_equiv :
  state_equiv (states owner_stall_execution 0) (initial_state 2 0).
Proof.
  rewrite (proj1 owner_stall_execution_valid); apply state_equiv_refl.
Qed.

Local Lemma stalled_prefix_state :
  state_equiv (states owner_stall_execution 13) (stalled_boundary 4).
Proof.
  destruct (stalled_prefix_run 0) as (last & Hrun & Hlast).
  destruct (execution_window_state (turn 1) event_obs
    (fun s => s = initial_state 2 0) state_equiv (turn_proper 1)
    owner_stall_execution 0 (List.length owner_stall_prefix) (initial_state 2 0)
    owner_stall_execution_valid stalled_initial_equiv) as (actual & Hactual & Hstate).
  rewrite stalled_prefix_script, Hrun in Hactual.
  assert (Elast : actual = last) by congruence; subst actual.
  replace (0 + List.length owner_stall_prefix) with 13 in Hstate by reflexivity.
  eapply state_equiv_trans; [exact Hstate|exact Hlast].
Qed.

Local Lemma stalled_prefix_observation k : k < 13 ->
  emitted owner_stall_execution k =
    List.nth k stalled_prefix_observations None.
Proof.
  intro Hk.
  destruct (stalled_prefix_position k Hk) as (before & after & logs & Hrun & Hturn).
  assert (Hscript : List.map (selected owner_stall_execution) (List.seq 0 k) =
      List.firstn k owner_stall_prefix).
  {
    rewrite <- (map_seq_firstn (selected owner_stall_execution) 0
      (List.length owner_stall_prefix) k ltac:(change (k <= 13); lia)).
    rewrite stalled_prefix_script; reflexivity.
  }
  destruct (execution_window_state (turn 1) event_obs
    (fun s => s = initial_state 2 0) state_equiv (turn_proper 1)
    owner_stall_execution 0 k (initial_state 2 0)
    owner_stall_execution_valid stalled_initial_equiv) as (actual & Hactual & Hstate).
  rewrite Hscript, Hrun in Hactual.
  assert (Ebefore : actual = before) by congruence; subst actual.
  rewrite Nat.add_0_l in Hstate.
  change (turn 1 (selected owner_stall_execution k) before =
    Some (after,List.nth k stalled_prefix_observations None)) in Hturn.
  destruct (execution_turn_observation (turn 1) (fun s => s = initial_state 2 0)
    state_equiv (turn_proper 1) owner_stall_execution k before
    owner_stall_execution_valid Hstate) as (next & Hnext & _).
  rewrite Hturn in Hnext; congruence.
Qed.

Local Lemma stalled_prefix_events :
  List.map (emitted owner_stall_execution) (List.seq 0 13) =
    stalled_prefix_observations.
Proof.
  apply (map_seq_eq 0 13 _ _ None); [reflexivity|].
  intros i Hi; cbn [Nat.add]; now apply stalled_prefix_observation.
Qed.

Local Lemma stalled_retire6 :
  emitted owner_stall_execution 8 = Some (stamp (tag_retire,6) 2).
Proof. exact (stalled_prefix_observation 8 ltac:(lia)). Qed.

Local Lemma stalled_retire8 :
  emitted owner_stall_execution 12 = Some (stamp (tag_retire,8) 3).
Proof. exact (stalled_prefix_observation 12 ltac:(lia)). Qed.

Local Lemma stalled_tail_choices n :
  selected owner_stall_execution (13+n) =
    List.nth (n mod 2) owner_stall_cycle Remote0.
Proof.
  change (periodic_choices owner_stall_prefix Remote0 [Remote1]
    (List.length owner_stall_prefix+n) =
    List.nth (n mod 2) owner_stall_cycle Remote0).
  rewrite periodic_choices_nth; reflexivity.
Qed.

Local Lemma stalled_tail_client n :
  selected owner_stall_execution (13+n) = Remote0 \/
  selected owner_stall_execution (13+n) = Remote1.
Proof.
  rewrite stalled_tail_choices.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hbound.
  remember (n mod 2) as r eqn:Hr.
  destruct r as [ | r ]; [left; reflexivity|].
  destruct r as [ | r ]; [right; reflexivity|lia].
Qed.

Local Lemma stalled_cycle_selection n i : i < 2 ->
  selected owner_stall_execution (13+n*2+i) =
    List.nth i owner_stall_cycle Remote0.
Proof.
  intro Hi.
  change (periodic_choices owner_stall_prefix Remote0 [Remote1]
    (List.length owner_stall_prefix+n*S (List.length [Remote1])+i) =
    List.nth i (Remote0 :: [Remote1]) Remote0).
  apply periodic_choices_round; exact Hi.
Qed.

Local Lemma stalled_no_owner k : 5 <= k ->
  selected owner_stall_execution k <> Owner.
Proof.
  intro Hfive; destruct (Nat.lt_ge_cases k 13) as [Hprefix|Htail].
  - change (owner_stall_choices k <> Owner).
    do 13 (destruct k as [ | k ]; [vm_compute; congruence || lia|]).
    lia.
  - replace k with (13+(k-13)) by lia.
    destruct (stalled_tail_client (k-13)) as [-> | ->]; discriminate.
Qed.

Local Lemma stalled_remote0_infinitely :
  infinitely (fun k => selected owner_stall_execution k = Remote0).
Proof.
  intro n; exists (13+n*2); split; [lia|].
  replace (13+n*2) with (13+n*2+0) by lia.
  exact (stalled_cycle_selection n 0 ltac:(lia)).
Qed.

Local Lemma stalled_remote1_infinitely :
  infinitely (fun k => selected owner_stall_execution k = Remote1).
Proof.
  intro n; exists (13+n*2+1); split; [lia|].
  exact (stalled_cycle_selection n 1 ltac:(lia)).
Qed.

Local Lemma stalled_suffix_state n :
  state_equiv (states owner_stall_execution (13+n)) (stalled_boundary 4).
Proof.
  induction n as [ | n IH ].
  - exact stalled_prefix_state.
  - replace (13+S n) with (S (13+n)) by lia.
    destruct (execution_turn_observation (turn 1) (fun s => s = initial_state 2 0)
      state_equiv (turn_proper 1) owner_stall_execution (13+n) (stalled_boundary 4)
      owner_stall_execution_valid IH) as (next & Hnext & Hstate).
    rewrite (stalled_polling_turn 4 _ (stalled_tail_client n)) in Hnext.
    assert (Enext : next = stalled_boundary 4) by congruence; subst next.
    exact Hstate.
Qed.

Local Lemma stalled_suffix_silent n : emitted owner_stall_execution (13+n) = None.
Proof.
  destruct (execution_turn_observation (turn 1) (fun s => s = initial_state 2 0)
    state_equiv (turn_proper 1) owner_stall_execution (13+n) (stalled_boundary 4)
    owner_stall_execution_valid (stalled_suffix_state n)) as (next & Hnext & _).
  rewrite (stalled_polling_turn 4 _ (stalled_tail_client n)) in Hnext.
  congruence.
Qed.

Local Lemma stalled_suffix_stable n :
  state_equiv (states owner_stall_execution (13+n))
    (states owner_stall_execution 13) /\
  emitted owner_stall_execution (13+n) = None.
Proof.
  split; [|apply stalled_suffix_silent].
  eapply state_equiv_trans; [apply stalled_suffix_state|].
  apply state_equiv_sym; exact stalled_prefix_state.
Qed.

Local Lemma stalled_remote_chain n :
  aheap (states owner_stall_execution (13+n)) (remote_head 1) = Some 8 /\
  linked (fun a next => aheap (states owner_stall_execution (13+n)) a = Some next) [8;6] 0 /\
  acount (states owner_stall_execution (13+n)) = 4 /\
  owner_state (states owner_stall_execution (13+n)) = ORead /\
  remote0_state (states owner_stall_execution (13+n)) = RPoll /\
  remote1_state (states owner_stall_execution (13+n)) = RPoll.
Proof.
  destruct (stalled_suffix_state n) as (Hheap & Hcount & Howner & Hzero & Hone).
  split; [rewrite Hheap; reflexivity|].
  split.
  - cbn [linked List.hd]; repeat split; rewrite Hheap; reflexivity.
  - exact (conj Hcount (conj Howner (conj Hzero Hone))).
Qed.

Local Lemma stalled_no_reclaim k block :
  ~ block_event tag_reclaim block (emitted owner_stall_execution k).
Proof.
  intros [idx Hobs]; destruct (Nat.lt_ge_cases k 13) as [Hprefix|Htail].
  - rewrite (stalled_prefix_observation k Hprefix) in Hobs.
    do 13 (destruct k as [ | k ]; [vm_compute in Hobs; discriminate|]).
    lia.
  - replace k with (13+(k-13)) in Hobs by lia.
    rewrite stalled_suffix_silent in Hobs; discriminate.
Qed.

Theorem stalled_prefix_source : exists last labels residual,
  run_turns (turn 1) event_obs owner_stall_prefix (initial_state 2 0) =
    Some (last,stalled_prefix_logs 0) /\
  state_equiv last (stalled_boundary 4) /\
  label_logs labels = stalled_prefix_logs 0 /\
  label_taus labels = 13 /\
  finite_steps (run_nd (allocator_program 2) hemp 0) labels residual /\
  residual ~ (model_nd 2 actor_of_slot (turn 1) last
                : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  destruct (stalled_prefix_run 0) as (last & Hrun & Hstate).
  destruct (run_turns_realizes_source 2 0 owner_stall_prefix last
    (stalled_prefix_logs 0) Hrun)
    as (labels & residual & Hlabels & Hlogs & Htaus & Hsteps & Hresidual).
  exists last, labels, residual; split; [exact Hrun|].
  split; [exact Hstate|].
  split; [exact Hlogs|].
  split; [exact Htaus|].
  split; [exact Hsteps|exact Hresidual].
Qed.

(** Every silent polling choice still consumes one real scheduler tau. *)
Theorem stalled_tail_source_tau n
  (t : ictreeW (indexed (nat * nat)) (unit * SSig)) :
  realizes (fun j => turn_labels (emitted owner_stall_execution j)) (13+n) t ->
  exists next, finite_steps t [tau] next /\
    realizes (fun j => turn_labels (emitted owner_stall_execution j)) (S (13+n)) next.
Proof.
  intros [next Hne Hsteps Hrest].
  exists next; split; [|exact Hrest].
  rewrite stalled_suffix_silent in Hsteps; exact Hsteps.
Qed.

Theorem owner_stall_prevents_reclamation : exists e,
  allocator_valid 2 0 e /\
  (forall k, 5 <= k -> selected e k <> Owner) /\
  infinitely (fun k => selected e k = Remote0) /\
  infinitely (fun k => selected e k = Remote1) /\
  emitted e 8 = Some (stamp (tag_retire,6) 2) /\
  (forall k, ~ block_event tag_reclaim 6 (emitted e k)) /\
  realizes (fun j => turn_labels (emitted e j)) 0 (run_nd (allocator_program 2) hemp 0).
Proof.
  exists owner_stall_execution; split; [exact owner_stall_execution_valid|].
  split; [exact stalled_no_owner|].
  split; [exact stalled_remote0_infinitely|].
  split; [exact stalled_remote1_infinitely|].
  split; [exact stalled_retire6|].
  split; [intro k; apply stalled_no_reclaim|].
  apply valid_execution_realizes_source; exact owner_stall_execution_valid.
Qed.

End OwnerStall.
