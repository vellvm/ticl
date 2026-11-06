From TICL Require Import CTree.Interp.Yield.Policy.
(** * Regression: two cooperative loops never fault and never stop.

    [fork2 (lproc 1) (lproc 2)]: each process loops forever on its own cell.
    Both schedulers compose framed finite turns directly with the pool
    invariant.  The contract is [AG ⊤], including starvation; no fairness
    premise is required. *)
From Stdlib Require Import Fin Vector.
From examples Require Import CSL.Frame.Shared CSL.Frame.Asep.

(** The exact source turns already establish closure of this shared pool.
    Pool invariance supplies the infinite safety argument, without recording
    intermediate thread shapes in the client. *)
Theorem ag_two_procs_rr a b ctx c :
  <( {run_rr (fork2 (lproc 1) (lproc 2)) (shared a b ctx c)}, Pure |=L AG ⊤ )>.
Proof.
  unfold fork2; rewrite run_rr_fork_bind.
  change (interp_schedule_rr sh 2 [denote (lproc 1);denote (lproc 2)]%vector
    (Some parent) 0 (shared a b ctx c))
    with (run_rr_pool [lproc 1;lproc 2]%vector (Some parent) 0 (shared a b ctx c)).
  apply (ag_csl_rr_invariance _ (InvariantSeparation.loop_inv ctx) _
    (ranked_turns_closed sh _ _ _ _ _ (InvariantSeparation.loop_ranked ctx 0)))
    with (g:=(a,b,c)).
  - intros o t w Hw Hphi; csplit; auto with ticl.
  - intros g s focus cursor w Hinv Hw; csplit; auto with ticl.
  - split; [apply InvariantSeparation.split_cells_iff_both, peq_refl|reflexivity].
  - constructor.
Qed.

(** Pool safety does not require fair selection of either component. *)
Theorem ag_two_procs_nd a b ctx c :
  <( {run_nd (fork2 (lproc 1) (lproc 2)) (shared a b ctx c)}, Pure |=L AG ⊤ )>.
Proof.
  unfold fork2; rewrite run_nd_fork_bind.
  change (interp_schedule_nd sh 2 [denote (lproc 1);denote (lproc 2)]%vector
    (Some parent) (shared a b ctx c))
    with (run_nd_pool [lproc 1;lproc 2]%vector (Some parent) (shared a b ctx c)).
  apply (ag_csl_nd_invariance _ (InvariantSeparation.loop_inv ctx) _
    (ranked_turns_closed sh _ _ _ _ _ (InvariantSeparation.loop_ranked ctx 0)))
    with (g:=(a,b,c)).
  - intros o t w Hw Hphi; csplit; auto with ticl.
  - intros g s focus w Hinv Hw; csplit; auto with ticl.
  - split; [apply InvariantSeparation.split_cells_iff_both, peq_refl|reflexivity].
  - constructor.
Qed.

(** Instantiate round-robin loop safety with concrete initial cell values. *)
Example ag_rr_3_5 ctx : <( {run_rr (fork2 (lproc 1) (lproc 2)) (shared 3 5 ctx 0)}, Pure |=L AG ⊤ )>.
Proof. apply ag_two_procs_rr. Qed.
(** Instantiate nondeterministic loop safety with concrete initial cell values. *)
Example ag_nd_3_5 ctx : <( {run_nd (fork2 (lproc 1) (lproc 2)) (shared 3 5 ctx 0)}, Pure |=L AG ⊤ )>.
Proof. apply ag_two_procs_nd. Qed.

Print Assumptions ag_two_procs_rr.
Print Assumptions ag_two_procs_nd.
