From Stdlib Require Import List Lia Arith.PeanoNat.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Trans.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Program
  CSL.Allocator.Model CSL.Allocator.Execution CSL.Allocator.Liveness.

Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Definition has_event (kind block : nat) (e : AExecution) (k : nat) : Prop :=
  exists idx, emitted e k = Some (SPop kind block idx).

(** The cycle is nonempty by construction.  Every state is still obtained
    by executing the preceding turns through [execution_of_choices]. *)
Definition periodic_choices (prefix : list Actor) (first : Actor) (rest : list Actor)
  (k : nat) : Actor :=
  if Nat.ltb k (List.length prefix)
  then List.nth k prefix first
  else List.nth ((k - List.length prefix) mod (S (List.length rest))) (first :: rest) first.

Definition starvation_cycle : list Actor :=
  [Remote1; Remote1; Remote0; Remote0; Remote0; Remote0; Remote1;
   Owner; Owner; Owner; Owner; Owner; Owner].
Definition starvation_prefix : list Actor :=
  [Owner; Owner; Owner; Owner; Owner; Remote1] ++ starvation_cycle.
Definition starvation_choices : nat -> Actor :=
  periodic_choices starvation_prefix Remote1 (List.tl starvation_cycle).
Definition starvation_execution : AExecution := execution_of_choices 2 0 starvation_choices.

Definition owner_stall_prefix : list Actor :=
  List.repeat Owner 5 ++ List.repeat Remote0 4 ++ List.repeat Remote1 4.
Definition owner_stall_cycle : list Actor := [Remote0; Remote1].
Definition owner_stall_choices : nat -> Actor :=
  periodic_choices owner_stall_prefix Remote0 [Remote1].
Definition owner_stall_execution : AExecution := execution_of_choices 2 0 owner_stall_choices.

Lemma periodic_choices_before prefix first rest k :
  k < List.length prefix ->
  periodic_choices prefix first rest k = List.nth k prefix first.
Proof.
  intro Hk; unfold periodic_choices; apply Nat.ltb_lt in Hk; now rewrite Hk.
Qed.
Lemma periodic_choices_after prefix first rest k :
  periodic_choices prefix first rest (List.length prefix + k) =
    List.nth (k mod (S (List.length rest))) (first :: rest) first.
Proof.
  unfold periodic_choices.
  assert (E : Nat.ltb (List.length prefix + k) (List.length prefix) = false)
    by (apply Nat.ltb_ge; lia).
  rewrite E; f_equal; f_equal; lia.
Qed.
Lemma periodic_choices_nth prefix first rest rounds i :
  i < S (List.length rest) ->
  periodic_choices prefix first rest
    (List.length prefix + rounds * S (List.length rest) + i) =
    List.nth i (first :: rest) first.
Proof.
  intro Hi.
  replace (List.length prefix + rounds * S (List.length rest) + i)
    with (List.length prefix + (i + rounds * S (List.length rest))) by lia.
  rewrite periodic_choices_after, Nat.Div0.mod_add.
  now rewrite Nat.mod_small by exact Hi.
Qed.

Lemma witness_map_seq_nth {A} len start (f : nat -> A) xs d :
  List.length xs = len ->
  (forall i, i < len -> f (start+i) = List.nth i xs d) ->
  List.map f (List.seq start len) = xs.
Proof.
  intros Hlen Hnth; apply List.nth_ext with (d := f start) (d' := d).
  - rewrite List.length_map, List.length_seq; symmetry; exact Hlen.
  - intros i Hi; rewrite List.length_map, List.length_seq in Hi.
    rewrite List.map_nth, List.seq_nth by exact Hi; now apply Hnth.
Qed.
Lemma periodic_prefix_script prefix first rest :
  List.map (periodic_choices prefix first rest) (List.seq 0 (List.length prefix)) = prefix.
Proof.
  apply (witness_map_seq_nth _ _ _ _ first); [reflexivity|].
  intros i Hi; cbn [Nat.add]; now apply periodic_choices_before.
Qed.
Lemma periodic_cycle_script prefix first rest rounds :
  List.map (periodic_choices prefix first rest)
    (List.seq (List.length prefix + rounds * S (List.length rest))
      (S (List.length rest))) = first :: rest.
Proof.
  apply (witness_map_seq_nth _ _ _ _ first); [reflexivity|].
  intros i Hi; now apply periodic_choices_nth.
Qed.

Lemma starvation_execution_valid : valid_execution 2 0 starvation_execution.
Proof. apply execution_of_choices_valid. Qed.
Lemma owner_stall_execution_valid : valid_execution 2 0 owner_stall_execution.
Proof. apply execution_of_choices_valid. Qed.

Lemma witness_window_state capacity c e start script s last logs :
  valid_execution capacity c e -> state_equiv (states e start) s ->
  List.map (selected e) (List.seq start (List.length script)) = script ->
  run_turns 1 script s = Some (last,logs) ->
  state_equiv (states e (start + List.length script)) last.
Proof.
  intros Hvalid Hstate Hchoices Hrun.
  destruct (run_turns_respects_heq_some 1 script s (states e start) last logs
    (state_equiv_sym _ _ Hstate) Hrun) as (actual & Hactual & Hlast).
  pose proof (execution_run_turns capacity c e start (List.length script) Hvalid) as Hexec.
  rewrite Hchoices in Hexec; rewrite Hexec in Hactual.
  inversion Hactual; subst actual; now apply state_equiv_sym.
Qed.

Lemma witness_turn_observation capacity c e k s next event :
  valid_execution capacity c e -> state_equiv (states e k) s ->
  turn 1 (selected e k) s = Some (next,event) ->
  emitted e k = event /\ state_equiv (states e (S k)) next.
Proof.
  intros Hvalid Hstate Hturn.
  destruct (turn_respects_heq_some 1 (selected e k) s (states e k) next event
    (state_equiv_sym _ _ Hstate) Hturn) as (actual & Hactual & Hnext).
  rewrite (execution_step capacity c e k Hvalid) in Hactual.
  inversion Hactual; subst actual event; split; [reflexivity|now apply state_equiv_sym].
Qed.

Lemma witness_firstn_seq start n len :
  n <= len -> List.firstn n (List.seq start len) = List.seq start n.
Proof.
  revert start len; induction n as [|n IH]; intros start len H; [reflexivity|].
  destruct len; [lia|]. cbn [List.firstn List.seq]; now rewrite IH by lia.
Qed.

Lemma witness_window_prefix e start script n :
  n <= List.length script ->
  List.map (selected e) (List.seq start (List.length script)) = script ->
  List.map (selected e) (List.seq start n) = List.firstn n script.
Proof.
  intros Hn Hscript.
  rewrite <- (witness_firstn_seq start n (List.length script) Hn),
    <- List.firstn_map, Hscript; reflexivity.
Qed.

From Stdlib Require Import List Lia Arith.PeanoNat.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Trans.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Program
  CSL.Allocator.Model CSL.Allocator.Execution CSL.Allocator.Liveness.

Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Definition starve_prefix_logs (c : nat) : list SObs :=
  [SPop tag_alloc 6 c; SPop tag_alloc 8 (1+c);
   SPop tag_retire 6 (2+c); SPop tag_retry 8 (3+c);
   SPop tag_reclaim 6 (4+c); SPop tag_alloc 6 (5+c)].
Definition starve_cycle_logs (c : nat) : list SObs :=
  [SPop tag_retire 6 c; SPop tag_retry 8 (1+c);
   SPop tag_reclaim 6 (2+c); SPop tag_alloc 6 (3+c)].

(** A pointwise representative only: the infinite witness always retains
    the actual heap returned by its preceding turn. *)
Definition starve_boundary_heap : Heap := fun x =>
  match x with
  | 1 => Some 0 | 2 => Some 0 | 3 => Some 0 | 4 => Some 6
  | 5 => Some 0 | 6 => Some 0 | 7 => Some 1 | 8 => Some 0
  | 9 => Some 2 | _ => None
  end.
Definition starve_boundary (c : nat) : AState :=
  {| aheap := starve_boundary_heap; acount := c;
     owner_state := ORead; remote0_state := RPoll;
     remote1_state := RRead 8 |}.

Lemma starve_prefix_run c : exists last,
  run_turns 1 starvation_prefix (initial_state 2 c) =
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

Lemma starve_cycle_run c : exists last,
  run_turns 1 starvation_cycle (starve_boundary c) =
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

Lemma starve_cycle_run_actual c s :
  state_equiv s (starve_boundary c) ->
  exists last,
    run_turns 1 starvation_cycle s = Some (last,starve_cycle_logs c) /\
    state_equiv last (starve_boundary (4+c)).
Proof.
  intro Hs; destruct (starve_cycle_run c) as (last & Hrun & Hlast).
  destruct (run_turns_respects_heq_some 1 starvation_cycle
    (starve_boundary c) s last (starve_cycle_logs c)
    (state_equiv_sym _ _ Hs) Hrun) as (actual & Hactual & Heq).
  exists actual; split; [exact Hactual|].
  eapply state_equiv_trans; [apply state_equiv_sym; exact Heq|exact Hlast].
Qed.

(** The observation of each individual turn, including every silent turn. *)
Definition starve_prefix_event (c i : nat) : option SObs :=
  match i with
  | 3 => Some (SPop tag_alloc 6 c)
  | 4 => Some (SPop tag_alloc 8 (1+c))
  | 11 => Some (SPop tag_retire 6 (2+c))
  | 12 => Some (SPop tag_retry 8 (3+c))
  | 15 => Some (SPop tag_reclaim 6 (4+c))
  | 17 => Some (SPop tag_alloc 6 (5+c))
  | _ => None
  end.
Definition starve_cycle_event (c i : nat) : option SObs :=
  match i with
  | 5 => Some (SPop tag_retire 6 c)
  | 6 => Some (SPop tag_retry 8 (1+c))
  | 9 => Some (SPop tag_reclaim 6 (2+c))
  | 11 => Some (SPop tag_alloc 6 (3+c))
  | _ => None
  end.

Lemma starve_prefix_position c i : i < 19 ->
  exists middle logs next,
    run_turns 1 (List.firstn i starvation_prefix) (initial_state 2 c) =
      Some (middle,logs) /\
    turn 1 (List.nth i starvation_prefix Remote1) middle =
      Some (next,starve_prefix_event c i).
Proof.
  intro Hi.
  do 19 (destruct i as [|i];
    [eexists; eexists; eexists; split; vm_compute; reflexivity|]).
  lia.
Qed.

Lemma starve_cycle_position c i : i < 13 ->
  exists middle logs next,
    run_turns 1 (List.firstn i starvation_cycle) (starve_boundary c) =
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

Lemma starve_prefix_script :
  List.map (selected starvation_execution)
    (List.seq 0 (List.length starvation_prefix)) = starvation_prefix.
Proof.
  change (List.map
    (periodic_choices starvation_prefix Remote1 (List.tl starvation_cycle))
    (List.seq 0 (List.length starvation_prefix)) = starvation_prefix).
  apply periodic_prefix_script.
Qed.

Lemma starve_selected_prefix k : k < 19 ->
  selected starvation_execution k = List.nth k starvation_prefix Remote1.
Proof.
  intro Hk; change (starvation_choices k = List.nth k starvation_prefix Remote1).
  unfold starvation_choices; apply periodic_choices_before; exact Hk.
Qed.

Lemma starve_selected_cycle n i : i < 13 ->
  selected starvation_execution (19+13*n+i) =
    List.nth i starvation_cycle Remote1.
Proof.
  intro Hi.
  change (periodic_choices starvation_prefix Remote1 (List.tl starvation_cycle)
    (19+13*n+i) = List.nth i starvation_cycle Remote1).
  replace (19+13*n+i) with
    (List.length starvation_prefix + n * S (List.length (List.tl starvation_cycle)) + i)
    by (cbn [starvation_prefix starvation_cycle List.length List.tl List.app]; lia).
  apply periodic_choices_nth; exact Hi.
Qed.

Lemma starve_cycle_script n :
  List.map (selected starvation_execution)
    (List.seq (19+13*n) (List.length starvation_cycle)) = starvation_cycle.
Proof.
  apply (witness_map_seq_nth _ _ _ _ Remote1); [reflexivity|].
  intros i Hi; apply starve_selected_cycle; exact Hi.
Qed.

Lemma starve_initial_equiv :
  state_equiv (states starvation_execution 0) (initial_state 2 0).
Proof.
  rewrite (proj1 starvation_execution_valid); apply state_equiv_refl.
Qed.

Lemma starve_boundaries n :
  state_equiv (states starvation_execution (19+13*n))
    (starve_boundary (6+4*n)).
Proof.
  induction n as [|n IH].
  - destruct (starve_prefix_run 0) as (last & Hrun & Hlast).
    eapply state_equiv_trans; [|exact Hlast].
    change (state_equiv
      (states starvation_execution (0+List.length starvation_prefix)) last).
    eapply witness_window_state with (capacity := 2) (c := 0)
      (s := initial_state 2 0) (logs := starve_prefix_logs 0).
    + exact starvation_execution_valid.
    + exact starve_initial_equiv.
    + exact starve_prefix_script.
    + exact Hrun.
  - destruct (starve_cycle_run (6+4*n)) as (last & Hrun & Hlast).
    replace (6+4*S n) with (4+(6+4*n)) by lia.
    eapply state_equiv_trans; [|exact Hlast].
    replace (19+13*S n) with
      ((19+13*n)+List.length starvation_cycle)
      by (cbn [starvation_cycle List.length]; lia).
    eapply witness_window_state with (capacity := 2) (c := 0)
      (s := starve_boundary (6+4*n)) (logs := starve_cycle_logs (6+4*n)).
    + exact starvation_execution_valid.
    + exact IH.
    + exact (starve_cycle_script n).
    + exact Hrun.
Qed.

Lemma starve_actual_cycle_run n : exists last,
  run_turns 1 starvation_cycle (states starvation_execution (19+13*n)) =
    Some (last,starve_cycle_logs (6+4*n)) /\
  state_equiv last (starve_boundary (6+4*S n)).
Proof.
  replace (6+4*S n) with (4+(6+4*n)) by lia.
  apply starve_cycle_run_actual; apply starve_boundaries.
Qed.

(** Every intermediate state is the result of a finite fold from the actual
    returned boundary, not from a periodically reset representative. *)
Lemma starve_actual_cycle_position n i : i < 13 ->
  exists logs next,
    run_turns 1 (List.firstn i starvation_cycle)
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
  destruct (run_turns_respects_heq_some 1 (List.firstn i starvation_cycle)
    (starve_boundary (6+4*n)) (states starvation_execution (19+13*n))
    middle logs (state_equiv_sym _ _ (starve_boundaries n)) Hrun)
    as (actual & Hactual & Heq).
  assert (Hscript : List.map (selected starvation_execution)
    (List.seq (19+13*n) i) = List.firstn i starvation_cycle).
  {
    eapply witness_window_prefix.
    - change (i <= 13); lia.
    - exact (starve_cycle_script n).
  }
  pose proof (execution_run_turns 2 0 starvation_execution (19+13*n) i
    starvation_execution_valid) as Hwindow.
  rewrite Hscript, Hactual in Hwindow.
  assert (Estate : actual = states starvation_execution (19+13*n+i))
    by congruence.
  subst actual.
  destruct (turn_respects_heq_some 1 (List.nth i starvation_cycle Remote1)
    middle (states starvation_execution (19+13*n+i)) next
    (starve_cycle_event (6+4*n) i) Heq Hturn)
    as (actual_next & Hnext & Hnext_eq).
  exists logs, actual_next; split; [exact Hactual|]; split; [|exact Hnext].
  destruct Heq as (_ & _ & _ & _ & Hremote1).
  rewrite <- Hremote1; exact Hheld.
Qed.

Lemma starve_cycle_emitted n i : i < 13 ->
  emitted starvation_execution (19+13*n+i) = starve_cycle_event (6+4*n) i.
Proof.
  intro Hi.
  destruct (starve_actual_cycle_position n i Hi)
    as (logs & next & Hrun & Hheld & Hturn).
  pose proof (execution_step 2 0 starvation_execution (19+13*n+i)
    starvation_execution_valid) as Hstep.
  rewrite (starve_selected_cycle n i Hi), Hturn in Hstep; congruence.
Qed.

Lemma starve_prefix_emitted i : i < 19 ->
  emitted starvation_execution i = starve_prefix_event 0 i.
Proof.
  intro Hi.
  destruct (starve_prefix_position 0 i Hi) as (middle & logs & next & Hrun & Hturn).
  assert (Hlen : List.length (List.firstn i starvation_prefix) = i).
  {
    rewrite List.length_firstn; apply Nat.min_l; change (i <= 19); lia.
  }
  assert (Hscript : List.map (selected starvation_execution)
    (List.seq 0 (List.length (List.firstn i starvation_prefix))) =
    List.firstn i starvation_prefix).
  {
    rewrite Hlen; eapply witness_window_prefix.
    - change (i <= 19); lia.
    - exact starve_prefix_script.
  }
  pose proof (witness_window_state 2 0 starvation_execution 0
    (List.firstn i starvation_prefix) (initial_state 2 0) middle logs
    starvation_execution_valid starve_initial_equiv Hscript Hrun) as Heq.
  rewrite Hlen, Nat.add_0_l in Heq.
  rewrite <- (starve_selected_prefix i Hi) in Hturn.
  exact (proj1 (witness_turn_observation 2 0 starvation_execution i middle next
    (starve_prefix_event 0 i) starvation_execution_valid Heq Hturn)).
Qed.

Lemma starve_cycle_event_offsets n :
  emitted starvation_execution (19+13*n+5) = Some (SPop tag_retire 6 (6+4*n)) /\
  emitted starvation_execution (19+13*n+6) = Some (SPop tag_retry 8 (1+(6+4*n))) /\
  emitted starvation_execution (19+13*n+9) = Some (SPop tag_reclaim 6 (2+(6+4*n))) /\
  emitted starvation_execution (19+13*n+11) = Some (SPop tag_alloc 6 (3+(6+4*n))).
Proof.
  split; [exact (starve_cycle_emitted n 5 ltac:(lia))|].
  split; [exact (starve_cycle_emitted n 6 ltac:(lia))|].
  split; [exact (starve_cycle_emitted n 9 ltac:(lia))|].
  exact (starve_cycle_emitted n 11 ltac:(lia)).
Qed.

Lemma starve_index k : 19 <= k ->
  exists n i, i < 13 /\ k = 19+13*n+i.
Proof.
  intro Hk; exists ((k-19)/13), ((k-19) mod 13); split.
  - apply Nat.mod_upper_bound; lia.
  - pose proof (Nat.div_mod (k-19) 13 ltac:(lia)); lia.
Qed.

Lemma starve_fair : fair starvation_execution.
Proof.
  intros actor lo; destruct actor.
  - exists (19+13*lo+7); split; [lia|].
    exact (starve_selected_cycle lo 7 ltac:(lia)).
  - exists (19+13*lo+2); split; [lia|].
    exact (starve_selected_cycle lo 2 ltac:(lia)).
  - exists (19+13*lo+0); split; [lia|].
    exact (starve_selected_cycle lo 0 ltac:(lia)).
Qed.

Lemma starve_held_forever k : 19 <= k ->
  held (remote1_state (states starvation_execution k)) = [8].
Proof.
  intro Hk; destruct (starve_index k Hk) as (n & i & Hi & ->).
  destruct (starve_actual_cycle_position n i Hi)
    as (logs & next & Hrun & Hheld & Hturn); exact Hheld.
Qed.

Lemma starve_prefix_never_retire8 c i idx : i < 19 ->
  starve_prefix_event c i <> Some (SPop tag_retire 8 idx).
Proof.
  intro Hi.
  do 19 (destruct i as [|i]; [vm_compute; discriminate|]).
  lia.
Qed.
Lemma starve_cycle_never_retire8 c i idx : i < 13 ->
  starve_cycle_event c i <> Some (SPop tag_retire 8 idx).
Proof.
  intro Hi.
  do 13 (destruct i as [|i]; [vm_compute; discriminate|]).
  lia.
Qed.

Lemma starve_never_retire8 k : ~ has_event tag_retire 8 starvation_execution k.
Proof.
  intros [idx Hevent]; destruct (Nat.lt_ge_cases k 19) as [Hprefix|Hcycle].
  - rewrite (starve_prefix_emitted k Hprefix) in Hevent.
    exact (starve_prefix_never_retire8 0 k idx Hprefix Hevent).
  - destruct (starve_index k Hcycle) as (n & i & Hi & ->).
    rewrite (starve_cycle_emitted n i Hi) in Hevent.
    exact (starve_cycle_never_retire8 (6+4*n) i idx Hi Hevent).
Qed.

Lemma starve_infinitely_retry8 : infinitely (has_event tag_retry 8 starvation_execution).
Proof.
  intro lo; exists (19+13*lo+6); split; [lia|].
  exists (1+(6+4*lo)); exact (starve_cycle_emitted lo 6 ltac:(lia)).
Qed.
Lemma starve_infinitely_retire6 : infinitely (has_event tag_retire 6 starvation_execution).
Proof.
  intro lo; exists (19+13*lo+5); split; [lia|].
  exists (6+4*lo); exact (starve_cycle_emitted lo 5 ltac:(lia)).
Qed.
Lemma starve_infinitely_reclaim6 : infinitely (has_event tag_reclaim 6 starvation_execution).
Proof.
  intro lo; exists (19+13*lo+9); split; [lia|].
  exists (2+(6+4*lo)); exact (starve_cycle_emitted lo 9 ltac:(lia)).
Qed.
Lemma starve_infinitely_alloc6 : infinitely (has_event tag_alloc 6 starvation_execution).
Proof.
  intro lo; exists (19+13*lo+11); split; [lia|].
  exists (3+(6+4*lo)); exact (starve_cycle_emitted lo 11 ltac:(lia)).
Qed.

Theorem fair_starvation_exists : exists e,
  valid_execution 2 0 e /\ fair e /\
  (forall k, 19 <= k -> held (remote1_state (states e k)) = [8]) /\
  infinitely (has_event tag_retry 8 e) /\
  (forall k, ~ has_event tag_retire 8 e k) /\
  infinitely (has_event tag_retire 6 e) /\
  infinitely (has_event tag_reclaim 6 e) /\
  infinitely (has_event tag_alloc 6 e) /\
  realizes e 0 (run_nd (allocator_program 2) hemp 0).
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

From Stdlib Require Import List Lia Arith.PeanoNat.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Trans.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Program
  CSL.Allocator.Model CSL.Allocator.Execution CSL.Allocator.Liveness.

Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Definition stalled_prefix_logs (c : nat) : list SObs :=
  [SPop tag_alloc 6 c; SPop tag_alloc 8 (1+c);
   SPop tag_retire 6 (2+c); SPop tag_retire 8 (3+c)].

Definition stalled_prefix_observations : list (option SObs) :=
  [None; None; None; Some (SPop tag_alloc 6 0);
   Some (SPop tag_alloc 8 1); None; None; None;
   Some (SPop tag_retire 6 2); None; None; None;
   Some (SPop tag_retire 8 3)].

(** This is only a pointwise representative of the returned heap.  The
    predefined execution always runs the actual preceding turn. *)
Definition stalled_boundary_heap : Heap := fun x =>
  match x with
  | 1 => Some 8 | 2 => Some 0 | 3 => Some 0 | 4 => Some 0
  | 5 => Some 0 | 6 => Some 0 | 7 => Some 1 | 8 => Some 6
  | 9 => Some 2 | _ => None
  end.
Definition stalled_boundary (c : nat) : AState :=
  {| aheap := stalled_boundary_heap; acount := c;
     owner_state := ORead; remote0_state := RPoll;
     remote1_state := RPoll |}.

Lemma stalled_prefix_run c : exists last,
  run_turns 1 owner_stall_prefix (initial_state 2 c) =
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

Lemma stalled_polling_turn c who :
  who = Remote0 \/ who = Remote1 ->
  turn 1 who (stalled_boundary c) = Some (stalled_boundary c,None).
Proof.
  intros [-> | ->]; vm_compute; reflexivity.
Qed.

Lemma stalled_cycle_run c :
  run_turns 1 owner_stall_cycle (stalled_boundary c) =
    Some (stalled_boundary c,[]).
Proof. reflexivity. Qed.

(** Transfer the finite polling calculation to the actual accumulated heap;
    neither this lemma nor the infinite witness resets that heap. *)
Lemma stalled_cycle_run_actual c s :
  state_equiv s (stalled_boundary c) ->
  exists last, run_turns 1 owner_stall_cycle s = Some (last,[]) /\
    state_equiv last s.
Proof.
  intro Hs.
  destruct (run_turns_respects_heq_some 1 owner_stall_cycle
    (stalled_boundary c) s (stalled_boundary c) []
    (state_equiv_sym _ _ Hs) (stalled_cycle_run c))
    as (last & Hrun & Hlast).
  exists last; split; [exact Hrun|].
  eapply state_equiv_trans; [apply state_equiv_sym; exact Hlast|].
  apply state_equiv_sym; exact Hs.
Qed.

Lemma stalled_prefix_script :
  List.map (selected owner_stall_execution)
    (List.seq 0 (List.length owner_stall_prefix)) = owner_stall_prefix.
Proof.
  change (List.map (periodic_choices owner_stall_prefix Remote0 [Remote1])
    (List.seq 0 (List.length owner_stall_prefix)) = owner_stall_prefix).
  apply periodic_prefix_script.
Qed.

Lemma stalled_initial_equiv :
  state_equiv (states owner_stall_execution 0) (initial_state 2 0).
Proof.
  rewrite (proj1 owner_stall_execution_valid); apply state_equiv_refl.
Qed.

Lemma stalled_prefix_state :
  state_equiv (states owner_stall_execution 13) (stalled_boundary 4).
Proof.
  destruct (stalled_prefix_run 0) as (last & Hrun & Hlast).
  pose proof (witness_window_state 2 0 owner_stall_execution 0
    owner_stall_prefix (initial_state 2 0) last (stalled_prefix_logs 0)
    owner_stall_execution_valid stalled_initial_equiv
    stalled_prefix_script Hrun) as Hstate.
  change (state_equiv (states owner_stall_execution 13) last) in Hstate.
  eapply state_equiv_trans; [exact Hstate|exact Hlast].
Qed.

Lemma stalled_prefix_observation k : k < 13 ->
  emitted owner_stall_execution k =
    List.nth k stalled_prefix_observations None.
Proof.
  intro Hk.
  assert (Hfinite : exists before after logs,
    run_turns 1 (List.firstn k owner_stall_prefix) (initial_state 2 0) =
      Some (before,logs) /\
    turn 1 (owner_stall_choices k) before =
      Some (after,List.nth k stalled_prefix_observations None)).
  {
    do 13 (destruct k as [ | k ];
      [eexists; eexists; eexists; split; vm_compute; reflexivity|]).
    lia.
  }
  destruct Hfinite as (before & after & logs & Hrun & Hturn).
  assert (Hlen : List.length (List.firstn k owner_stall_prefix) = k).
  {
    rewrite List.length_firstn.
    change (Nat.min k 13 = k).
    apply Nat.min_l; lia.
  }
  assert (Hscript : List.map (selected owner_stall_execution)
    (List.seq 0 (List.length (List.firstn k owner_stall_prefix))) =
      List.firstn k owner_stall_prefix).
  {
    rewrite Hlen.
    apply witness_window_prefix with (script := owner_stall_prefix).
    - change (k <= 13); lia.
    - exact stalled_prefix_script.
  }
  pose proof (witness_window_state 2 0 owner_stall_execution 0
    (List.firstn k owner_stall_prefix) (initial_state 2 0) before logs
    owner_stall_execution_valid stalled_initial_equiv Hscript Hrun) as Hstate.
  cbn [Nat.add] in Hstate; rewrite Hlen in Hstate.
  change (turn 1 (selected owner_stall_execution k) before =
    Some (after,List.nth k stalled_prefix_observations None)) in Hturn.
  exact (proj1 (witness_turn_observation 2 0 owner_stall_execution k
    before after (List.nth k stalled_prefix_observations None)
    owner_stall_execution_valid Hstate Hturn)).
Qed.

Lemma stalled_prefix_events :
  List.map (emitted owner_stall_execution) (List.seq 0 13) =
    stalled_prefix_observations.
Proof.
  apply (witness_map_seq_nth 13 0 _ _ None); [reflexivity|].
  intros i Hi; cbn [Nat.add]; now apply stalled_prefix_observation.
Qed.

Lemma stalled_retire6 :
  emitted owner_stall_execution 8 = Some (SPop tag_retire 6 2).
Proof. exact (stalled_prefix_observation 8 ltac:(lia)). Qed.

Lemma stalled_retire8 :
  emitted owner_stall_execution 12 = Some (SPop tag_retire 8 3).
Proof. exact (stalled_prefix_observation 12 ltac:(lia)). Qed.

Lemma stalled_tail_choices n :
  selected owner_stall_execution (13+n) =
    List.nth (n mod 2) owner_stall_cycle Remote0.
Proof.
  change (periodic_choices owner_stall_prefix Remote0 [Remote1]
    (List.length owner_stall_prefix+n) =
    List.nth (n mod 2) owner_stall_cycle Remote0).
  rewrite periodic_choices_after; reflexivity.
Qed.

Lemma stalled_tail_client n :
  selected owner_stall_execution (13+n) = Remote0 \/
  selected owner_stall_execution (13+n) = Remote1.
Proof.
  rewrite stalled_tail_choices.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hbound.
  remember (n mod 2) as r eqn:Hr.
  destruct r as [ | r ]; [left; reflexivity|].
  destruct r as [ | r ]; [right; reflexivity|lia].
Qed.

Lemma stalled_cycle_selection n i : i < 2 ->
  selected owner_stall_execution (13+n*2+i) =
    List.nth i owner_stall_cycle Remote0.
Proof.
  intro Hi.
  change (periodic_choices owner_stall_prefix Remote0 [Remote1]
    (List.length owner_stall_prefix+n*S (List.length [Remote1])+i) =
    List.nth i (Remote0 :: [Remote1]) Remote0).
  apply periodic_choices_nth; exact Hi.
Qed.

Lemma stalled_no_owner k : 5 <= k ->
  selected owner_stall_execution k <> Owner.
Proof.
  intro Hfive; destruct (Nat.lt_ge_cases k 13) as [Hprefix|Htail].
  - change (owner_stall_choices k <> Owner).
    do 13 (destruct k as [ | k ]; [vm_compute; congruence || lia|]).
    lia.
  - replace k with (13+(k-13)) by lia.
    destruct (stalled_tail_client (k-13)) as [-> | ->]; discriminate.
Qed.

Lemma stalled_remote0_infinitely :
  infinitely (fun k => selected owner_stall_execution k = Remote0).
Proof.
  intro n; exists (13+n*2); split; [lia|].
  replace (13+n*2) with (13+n*2+0) by lia.
  exact (stalled_cycle_selection n 0 ltac:(lia)).
Qed.

Lemma stalled_remote1_infinitely :
  infinitely (fun k => selected owner_stall_execution k = Remote1).
Proof.
  intro n; exists (13+n*2+1); split; [lia|].
  exact (stalled_cycle_selection n 1 ltac:(lia)).
Qed.

Lemma stalled_suffix_state n :
  state_equiv (states owner_stall_execution (13+n)) (stalled_boundary 4).
Proof.
  induction n as [ | n IH ].
  - exact stalled_prefix_state.
  - replace (13+S n) with (S (13+n)) by lia.
    exact (proj2 (witness_turn_observation 2 0 owner_stall_execution (13+n)
      (stalled_boundary 4) (stalled_boundary 4) None
      owner_stall_execution_valid IH
      (stalled_polling_turn 4 _ (stalled_tail_client n)))).
Qed.

Lemma stalled_suffix_silent n : emitted owner_stall_execution (13+n) = None.
Proof.
  exact (proj1 (witness_turn_observation 2 0 owner_stall_execution (13+n)
    (stalled_boundary 4) (stalled_boundary 4) None
    owner_stall_execution_valid (stalled_suffix_state n)
    (stalled_polling_turn 4 _ (stalled_tail_client n)))).
Qed.

Lemma stalled_suffix_stable n :
  state_equiv (states owner_stall_execution (13+n))
    (states owner_stall_execution 13) /\
  emitted owner_stall_execution (13+n) = None.
Proof.
  split; [|apply stalled_suffix_silent].
  eapply state_equiv_trans; [apply stalled_suffix_state|].
  apply state_equiv_sym; exact stalled_prefix_state.
Qed.

Lemma stalled_remote_chain n :
  aheap (states owner_stall_execution (13+n)) (remote_head 1) = Some 8 /\
  free_chain (aheap (states owner_stall_execution (13+n))) [8;6] /\
  acount (states owner_stall_execution (13+n)) = 4 /\
  owner_state (states owner_stall_execution (13+n)) = ORead /\
  remote0_state (states owner_stall_execution (13+n)) = RPoll /\
  remote1_state (states owner_stall_execution (13+n)) = RPoll.
Proof.
  destruct (stalled_suffix_state n) as (Hheap & Hcount & Howner & Hzero & Hone).
  split; [rewrite Hheap; reflexivity|].
  split.
  - cbn [free_chain List.hd]; repeat split; rewrite Hheap; reflexivity.
  - exact (conj Hcount (conj Howner (conj Hzero Hone))).
Qed.

Lemma stalled_no_reclaim k block :
  ~ has_event tag_reclaim block owner_stall_execution k.
Proof.
  intros [idx Hobs]; destruct (Nat.lt_ge_cases k 13) as [Hprefix|Htail].
  - rewrite (stalled_prefix_observation k Hprefix) in Hobs.
    do 13 (destruct k as [ | k ]; [vm_compute in Hobs; discriminate|]).
    lia.
  - replace k with (13+(k-13)) in Hobs by lia.
    rewrite stalled_suffix_silent in Hobs; discriminate.
Qed.

Lemma stalled_prefix_source : exists last labels residual,
  run_turns 1 owner_stall_prefix (initial_state 2 0) =
    Some (last,stalled_prefix_logs 0) /\
  state_equiv last (stalled_boundary 4) /\
  label_logs labels = stalled_prefix_logs 0 /\
  label_taus labels = 13 /\
  finite_steps (run_nd (allocator_program 2) hemp 0) labels residual /\
  residual ~ model_nd 1 last.
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
Lemma stalled_tail_source_tau n t :
  realizes owner_stall_execution (13+n) t ->
  exists next, finite_steps t [tau] next /\
    realizes owner_stall_execution (S (13+n)) next.
Proof.
  intros [next Hsteps Hrest].
  exists next; split; [|exact Hrest].
  rewrite stalled_suffix_silent in Hsteps; exact Hsteps.
Qed.

Theorem owner_stall_prevents_reclamation : exists e,
  valid_execution 2 0 e /\
  (forall k, 5 <= k -> selected e k <> Owner) /\
  infinitely (fun k => selected e k = Remote0) /\
  infinitely (fun k => selected e k = Remote1) /\
  emitted e 8 = Some (SPop tag_retire 6 2) /\
  (forall k, ~ has_event tag_reclaim 6 e k) /\
  realizes e 0 (run_nd (allocator_program 2) hemp 0).
Proof.
  exists owner_stall_execution; split; [exact owner_stall_execution_valid|].
  split; [exact stalled_no_owner|].
  split; [exact stalled_remote0_infinitely|].
  split; [exact stalled_remote1_infinitely|].
  split; [exact stalled_retire6|].
  split; [intro k; apply stalled_no_reclaim|].
  apply valid_execution_realizes_source; exact owner_stall_execution_valid.
Qed.
