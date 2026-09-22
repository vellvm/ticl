From Stdlib Require Import List.
From TICL Require Import
  Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Events.Writer
  ICTree.Interp.State.Mod ICTree.Interp.Yield.RoundRobin
  ICTree.Logic.AG ICTree.Logic.Trans Logic.Core.
From TICL Require Import Lang.CSL.Queue.Representation Lang.CSL.Queue.Recurrence
  Lang.CSL.Queue.Alternating Lang.CSL.Queue.Program Lang.CSL.Queue.Ticl
  Lang.CSL.Queue.Operations.
From examples Require Import CSL.Layout CSL.Overlap.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

(* Ownership controls retain their original statements in CSL.Overlap:
   overlap_rejected, overlap_frame_not_preserved, null_frame_disjoint_but_bad.
   Sequential controls live in Lang.CSL.Queue.Recurrence and do not quantify
   over concurrent pools. Lang.CSL.Queue.Alternating.sfresh_excludes_retained
   rules out reusing an old tagged observation. *)

Lemma empty_heap_parallel_stuck :
  run_rr (parallel_queues 2 10) hemp 0 ~
    (stuck : ictreeW SObs (unit * SSig)).
Proof.
  unfold parallel_queues; rewrite run_rr_fork_bind.
  change (interp_schedule_rr sh 2 (queue_workers 2 10 false false)
    (Some (queue_slot 0)) 0 (hemp,0) ~
    (stuck : ictreeW SObs (unit * SSig))).
  etransitivity; [apply queue_pool_turn|].
  assert (Hfault : interp_state sh (turn 1 2) (hemp,0) ≅
    (stuck : ictreeW SObs (unit * SSig))).
  {
    unfold turn, turnk, queue_turn.
    etransitivity; [apply interp_state_bind|].
    lazymatch goal with
    | |- (interp_state sh (heap_read (E:=sE) 3) (hemp,0) >>= ?next) ≅ _ =>
      etransitivity;
      [ apply equ_clo_bind with (S := eq) (k2 := next);
        [exact (sinterp_srd_stuck 3 hemp 0 eq_refl) | intros x y <-; reflexivity]
      | apply bind_stuck_equ ]
    end.
  }
  lazymatch goal with
  | |- (interp_state sh ?p ?s >>= ?kont) ~ _ =>
    let Hwhole := fresh "Hwhole" in
    assert (Hwhole : (interp_state sh p s >>= kont) ≅
      (stuck : ictreeW SObs (unit * SSig))) by
      (etransitivity;
       [apply equ_clo_bind with (S := eq) (k2 := kont);
         [exact Hfault | intros x y <-; reflexivity]
       | apply bind_stuck_equ]);
    eapply equ_clos_sbisim_goal; [exact Hwhole | reflexivity | reflexivity]
  end.
Qed.

Local Typeclasses Transparent equ sbisim.

Lemma empty_heap_parallel_no_recurrence :
  ~ <( {run_rr (parallel_queues 2 10) hemp 0}, Pure
       |= AG (AF visW {spopped 1 7}) )>.
Proof.
  rewrite empty_heap_parallel_stuck.
  apply ag_stuck.
Qed.

Lemma allocated_empty_queue_stuck :
  run_rr (allocated_parallel_queues [] [8]) hemp 0 ~
    (stuck : ictreeW SObs (unit * SSig)).
Proof.
  destruct (run_rr_allocated_parallel [] [8] 0)
    as (u & v & h & Finite & Owned & Run).
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  destruct H1 as (_ & Hhead & _ & _ & Hnull & _).
  change (h (S u) = Some 0) in Hhead.
  rewrite Run; unfold parallel_queues; rewrite run_rr_fork_bind.
  change (interp_schedule_rr sh 2 (queue_workers u v false false)
    (Some (queue_slot 0)) 0 (h,0) ~
    (stuck : ictreeW SObs (unit * SSig))).
  etransitivity; [apply queue_pool_turn |].
  assert (Hfault : interp_state sh (turn 1 u) (h,0) ~
    (stuck : ictreeW SObs (unit * SSig))).
  { unfold turn, turnk, queue_turn.
    etransitivity; [eapply sinterp_rd; exact Hhead |].
    eapply equ_clos_sbisim_goal; [apply interp_state_bind | reflexivity |].
    lazymatch goal with
    | |- (interp_state sh (heap_read (E:=sE) 0) (h,0) >>= ?next) ~ _ =>
      eapply equ_clos_sbisim_goal;
      [ etransitivity;
        [ apply equ_clo_bind with (S := eq) (k2 := next);
          [exact (sinterp_srd_stuck 0 h 0 Hnull) | intros x y <-; reflexivity]
        | apply bind_stuck_equ ]
      | reflexivity | reflexivity ]
    end. }
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hfault | intro result; reflexivity] |]
  end.
  eapply equ_clos_sbisim_goal; [apply bind_stuck_equ | reflexivity | reflexivity].
Qed.

Lemma allocated_empty_queue_no_recurrence :
  ~ <( {run_rr (allocated_parallel_queues [] [8]) hemp 0}, Pure
       |= AG (AF visW {spopped 1 7}) )>.
Proof.
  rewrite allocated_empty_queue_stuck; apply ag_stuck.
Qed.
