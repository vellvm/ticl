From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Sorting.Permutation.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Interp.Yield.RoundRobin
  ICTree.Logic.State Logic.Core Utils.Vectors.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Program
  CSL.Allocator.Model CSL.Allocator.Execution CSL.Allocator.Liveness
  CSL.Allocator.NegativeTests.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope list_scope.
Local Open Scope ticl_scope.
Local Open Scope nat_scope.

(** These probes execute allocation and checked initialization before reading.
    The arbitrary continuation observes the returned base/value, exact heap,
    unchanged counter, and unchanged scheduling focus/cursor. *)
Example new_page_two_source n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE) cursor c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (new_page 2) >>= K)) (Some i) cursor (hemp,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some 1)) (Some i) cursor
    (page_heap 1 2 hemp,c).
Proof. apply interp_rr_new_page_hemp. Qed.

Example new_page_two_source_reads n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE) cursor c :
  List.Forall (fun '(offset,value) =>
    interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow (CBind (new_page 2)
        (fun base => CRead (base+offset))) >>= K)) (Some i) cursor (hemp,c) ~
    interp_schedule_rr sh (S n) (ts @ i := K (Some value)) (Some i) cursor
      (page_heap 1 2 hemp,c))
    [(0,0);(1,6);(2,0);(3,0);(4,0);(5,8);(6,0);(7,0);(8,0)].
Proof.
  repeat constructor; apply interp_rr_new_page_read; reflexivity.
Qed.

Example new_page_two_exact_domain x :
  page_heap 1 2 hemp x <> None <-> 1 <= x /\ x <= 9.
Proof. rewrite page_heap_closed_dom; unfold page_size; lia. Qed.

Example new_page_two_source_missing n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE) cursor c :
  List.Forall (fun address =>
    interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow (CBind (new_page 2)
        (fun _ => CRead address)) >>= K)) (Some i) cursor (hemp,c) ~
      (stuck : ictreeW SObs (unit * SSig))) [0;10].
Proof.
  repeat constructor; apply interp_rr_new_page_read_missing; reflexivity.
Qed.

Example new_page_zero_source n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE) c :
  interp_nd (S n)
    (ts @ i := (denote_flow (new_page 0) >>= K)) (Some i) (hemp,c) ~
  interp_nd (S n) (ts @ i := K (Some 1)) (Some i) (page_heap 1 0 hemp,c).
Proof. apply interp_nd_new_page_hemp. Qed.

Example new_page_zero_source_reads n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE) c :
  List.Forall (fun offset =>
    interp_nd (S n)
      (ts @ i := (denote_flow (CBind (new_page 0)
        (fun base => CRead (base+offset))) >>= K)) (Some i) (hemp,c) ~
    interp_nd (S n) (ts @ i := K (Some 0)) (Some i) (page_heap 1 0 hemp,c))
    [0;1;2;3;4].
Proof.
  repeat constructor; apply interp_nd_new_page_read; reflexivity.
Qed.

Example new_page_zero_exact_domain x :
  page_heap 1 0 hemp x <> None <-> 1 <= x /\ x <= 5.
Proof. rewrite page_heap_closed_dom; unfold page_size; lia. Qed.

Definition fixture_events (result : option (AState * list SObs)) : option (list SObs) :=
  match result with None => None | Some (_,logs) => Some logs end.
Definition fixture_cells (addresses : list nat) (result : option (AState * list SObs))
  : option (list (option nat)) :=
  match result with None => None | Some (s,_) => Some (List.map (aheap s) addresses) end.
Definition fixture_counter (result : option (AState * list SObs)) : option nat :=
  match result with None => None | Some (s,_) => Some (acount s) end.
Definition fixture_controls (result : option (AState * list SObs))
  : option (owner_pc * remote_pc * remote_pc) :=
  match result with None => None
  | Some (s,_) => Some (owner_state s,remote0_state s,remote1_state s) end.

Definition rr_prefix_fixture :=
  run_turns 1 (demo_rr_script 0 57) (initial_state 2 0).
Definition rr_cycle_fixture :=
  match rr_prefix_fixture with None => None | Some (s,_) =>
    run_turns 1 (demo_rr_script 57 42) s end.
Definition aba_before_reuse :=
  List.repeat Owner 5 ++ List.repeat Remote0 4 ++ List.repeat Remote1 3.
Definition aba_before_commit :=
  aba_before_reuse ++ List.repeat Owner 6 ++ List.repeat Remote0 4.
Definition aba_script := aba_before_commit ++ [Remote1].
Definition aba_fixture := run_turns 1 aba_script (initial_state 2 0).
Definition starvation_prefix_fixture :=
  run_turns 1 starvation_prefix (initial_state 2 0).
Definition starvation_cycle_fixture :=
  match starvation_prefix_fixture with None => None | Some (s,_) =>
    run_turns 1 starvation_cycle s end.
Definition owner_stall_prefix_fixture :=
  run_turns 1 owner_stall_prefix (initial_state 2 0).
Definition owner_stall_polling_fixture :=
  match owner_stall_prefix_fixture with None => None | Some (s,_) =>
    run_turns 1 owner_stall_cycle s end.

Example rr_prefix_events : fixture_events rr_prefix_fixture = Some
  [SPop 0 6 0; SPop 0 8 1; SPop 1 6 2; SPop 3 8 3; SPop 1 8 4;
   SPop 2 8 5; SPop 2 6 6; SPop 0 6 7; SPop 0 8 8].
Proof. vm_compute; reflexivity. Qed.
Example rr_prefix_state :
  fixture_cells (List.seq 1 9) rr_prefix_fixture =
    Some (List.map (@Some nat) [0;0;0;0;8;8;1;0;2]) /\
  fixture_counter rr_prefix_fixture = Some 9 /\
  fixture_controls rr_prefix_fixture = Some (ORead,RRead 6,RPoll).
Proof. vm_compute; repeat split; reflexivity. Qed.
Example rr_next_cycle_events : fixture_events rr_cycle_fixture = Some
  [SPop 1 6 9; SPop 3 8 10; SPop 1 8 11; SPop 2 8 12;
   SPop 2 6 13; SPop 0 6 14; SPop 0 8 15].
Proof. vm_compute; reflexivity. Qed.
Example rr_next_cycle_state :
  fixture_cells (List.seq 1 9) rr_cycle_fixture = fixture_cells (List.seq 1 9) rr_prefix_fixture /\
  fixture_controls rr_cycle_fixture = fixture_controls rr_prefix_fixture /\
  fixture_counter rr_cycle_fixture = Some 16.
Proof. vm_compute; repeat split; reflexivity. Qed.
Example rr_actual_source :
  run_rr (allocator_program 2) hemp 0 ~ emit_list (demo_prefix 0) (demo_cycle 9).
Proof. exact (run_rr_allocator_demo_bisim 0). Qed.

Definition aba_logs : list SObs :=
  [SPop 0 6 0; SPop 0 8 1; SPop 1 6 2; SPop 2 6 3;
   SPop 0 6 4; SPop 1 6 5; SPop 1 8 6].
Example aba_snapshot_survives_reuse :
  fixture_controls (run_turns 1 aba_before_reuse (initial_state 2 0)) =
    Some (ORead,RPoll,RCAS 8 6) /\
  fixture_controls (run_turns 1 aba_before_commit (initial_state 2 0)) =
    Some (ORead,RPoll,RCAS 8 6) /\
  fixture_cells [1] (run_turns 1 aba_before_reuse (initial_state 2 0)) = Some [Some 6] /\
  fixture_cells [1] (run_turns 1 aba_before_commit (initial_state 2 0)) = Some [Some 6].
Proof. vm_compute; repeat split; reflexivity. Qed.
Example aba_events : fixture_events aba_fixture = Some aba_logs.
Proof. vm_compute; reflexivity. Qed.
Example aba_links_and_counter :
  fixture_cells [1;8;6] aba_fixture = Some [Some 8;Some 6;Some 0] /\
  fixture_counter aba_fixture = Some 7.
Proof. vm_compute; split; reflexivity. Qed.
Lemma aba_run_no_loss : exists last,
  aba_fixture = Some (last,aba_logs) /\
  allocator_inv 1 2 last /\
  aheap last (remote_head 1) = Some 8 /\ free_chain (aheap last) [8;6] /\
  NoDup [8;6] /\ Permutation [8;6] (page_blocks 1 2).
Proof.
  assert (Hrun : exists last, aba_fixture = Some (last,aba_logs)).
  { eexists; vm_compute; reflexivity. }
  destruct Hrun as [last Hrun]; exists last; split; [exact Hrun|]; split.
  - eapply run_turns_preserves_inv; [apply initial_state_inv|exact Hrun].
  - vm_compute in Hrun; inversion Hrun; subst last.
    split; [reflexivity|]; split; [repeat split; reflexivity|]; split.
    + repeat constructor; cbn; intuition congruence.
    + change (Permutation [8;6] [6;8]); apply perm_swap.
Qed.
Theorem aba_actual_source_no_loss : exists last labels residual,
  aba_fixture = Some (last,aba_logs) /\ allocator_inv 1 2 last /\
  aheap last (remote_head 1) = Some 8 /\ free_chain (aheap last) [8;6] /\
  label_logs labels = aba_logs /\ label_taus labels = 23 /\
  finite_steps (run_nd (allocator_program 2) hemp 0) labels residual /\
  residual ~ model_nd 1 last.
Proof.
  destruct aba_run_no_loss as (last & Hrun & Hinv & Hhead & Hchain & Hnd & Hp).
  destruct (run_turns_realizes_source 2 0 aba_script last aba_logs Hrun)
    as (labels & residual & Hlabels & Hlogs & Htaus & Hsteps & Htail).
  exists last, labels, residual; repeat first [assumption | split].
Qed.

Example starvation_prefix_events : fixture_events starvation_prefix_fixture = Some
  [SPop 0 6 0; SPop 0 8 1; SPop 1 6 2; SPop 3 8 3; SPop 2 6 4; SPop 0 6 5].
Proof. vm_compute; reflexivity. Qed.
Example starvation_cycle_events : fixture_events starvation_cycle_fixture = Some
  [SPop 1 6 6; SPop 3 8 7; SPop 2 6 8; SPop 0 6 9].
Proof. vm_compute; reflexivity. Qed.
Example starvation_chained_cycle_state :
  fixture_cells (List.seq 1 9) starvation_prefix_fixture =
    Some (List.map (@Some nat) [0;0;0;6;0;0;1;0;2]) /\
  fixture_cells (List.seq 1 9) starvation_cycle_fixture =
    fixture_cells (List.seq 1 9) starvation_prefix_fixture /\
  fixture_controls starvation_cycle_fixture = Some (ORead,RPoll,RRead 8) /\
  fixture_counter starvation_cycle_fixture = Some 10.
Proof. vm_compute; repeat split; reflexivity. Qed.
Theorem starvation_chained_cycle_actual_source : exists last labels residual,
  run_turns 1 (starvation_prefix ++ starvation_cycle) (initial_state 2 0) =
    Some (last,starve_prefix_logs 0 ++ starve_cycle_logs 6) /\
  label_logs labels = starve_prefix_logs 0 ++ starve_cycle_logs 6 /\
  label_taus labels = 32 /\
  finite_steps (run_nd (allocator_program 2) hemp 0) labels residual /\
  residual ~ model_nd 1 last.
Proof.
  destruct (starve_prefix_run 0) as (first & Hprefix & Hfirst).
  destruct (starve_cycle_run_actual 6 first Hfirst) as (last & Hcycle & Hlast).
  pose proof (run_turns_compose 1 starvation_prefix starvation_cycle
    (initial_state 2 0) first last (starve_prefix_logs 0) (starve_cycle_logs 6)
    Hprefix Hcycle) as Hrun.
  destruct (run_turns_realizes_source 2 0 (starvation_prefix ++ starvation_cycle)
    last (starve_prefix_logs 0 ++ starve_cycle_logs 6) Hrun)
    as (labels & residual & Hlabels & Hlogs & Htaus & Hsteps & Htail).
  exists last, labels, residual; repeat first [assumption | split].
Qed.

Example owner_stall_prefix_events : fixture_events owner_stall_prefix_fixture = Some
  [SPop 0 6 0; SPop 0 8 1; SPop 1 6 2; SPop 1 8 3].
Proof. vm_compute; reflexivity. Qed.
Example owner_stall_polling_retains_remote_list :
  fixture_events owner_stall_polling_fixture = Some [] /\
  fixture_cells [1;8;6] owner_stall_polling_fixture = Some [Some 8;Some 6;Some 0] /\
  fixture_counter owner_stall_polling_fixture = Some 4 /\
  fixture_controls owner_stall_polling_fixture = Some (ORead,RPoll,RPoll).
Proof. vm_compute; repeat split; reflexivity. Qed.

Example allocator_allocation_recurs_fresh :
  <( {run_rr (allocator_program 2) hemp 0}, Pure
      |= AG (AF visW {fun o => stag o = tag_alloc /\ 100 <= sidx o}) )>.
Proof. apply allocator_demo_agaf_fresh; cbn; auto. Qed.
Example allocator_remote_free_recurs_fresh :
  <( {run_rr (allocator_program 2) hemp 0}, Pure
      |= AG (AF visW {fun o => stag o = tag_retire /\ 100 <= sidx o}) )>.
Proof. apply allocator_demo_agaf_fresh; cbn; auto. Qed.
Example allocator_reclamation_recurs_fresh :
  <( {run_rr (allocator_program 2) hemp 0}, Pure
      |= AG (AF visW {fun o => stag o = tag_reclaim /\ 100 <= sidx o}) )>.
Proof. apply allocator_demo_agaf_fresh; cbn; auto. Qed.
