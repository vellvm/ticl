(** * Formal-evidence roots.

    One [Check] and [Print Assumptions] pair per theorem-map row, in CSV order.
    The evidence driver supplies query-output delimiters externally.
    Assumption controls are not claims of identical historical source code. *)
From TICL Require Import
  CTree.Interp.CSL.Frame
  CTree.Interp.Yield.Fair
  CTree.Interp.Yield.Execution
  Logic.Simulation
  CTree.Interp.Yield.RoundRobin
  Lang.CoCSL.Mod.
From TICL Require Import Logic.Setoid CTree.Logic.Iter CTree.Logic.Bind.

From examples Require Import
  CSL.Queue.Shared
  CSL.Queue.Ticl
  CSL.Queue.Client
  CSL.Frame.Shared
  CSL.Frame.AN
  CSL.Control
  HiddenBr
  CSL.Allocator.Execution
  CSL.Allocator.Liveness
  CSL.Allocator.Counterexamples.

Check TICL.CTree.Interp.CSL.Frame.csim_interp_sh_frame.
Print Assumptions TICL.CTree.Interp.CSL.Frame.csim_interp_sh_frame.

Check TICL.CTree.Interp.CSL.Frame.ticll_csl_frame.
Print Assumptions TICL.CTree.Interp.CSL.Frame.ticll_csl_frame.

Check TICL.CTree.Interp.CSL.Frame.ticlr_csl_frame.
Print Assumptions TICL.CTree.Interp.CSL.Frame.ticlr_csl_frame.

Check TICL.CTree.Interp.CSL.Frame.anr_csl_frame_done.
Print Assumptions TICL.CTree.Interp.CSL.Frame.anr_csl_frame_done.

Check TICL.CTree.Interp.CSL.Frame.aur_csl_frame_done.
Print Assumptions TICL.CTree.Interp.CSL.Frame.aur_csl_frame_done.

Check TICL.CTree.Interp.Yield.Fair.rr_fair.
Print Assumptions TICL.CTree.Interp.Yield.Fair.rr_fair.

Check TICL.CTree.Interp.Yield.Fair.agaf_pool_fair.
Print Assumptions TICL.CTree.Interp.Yield.Fair.agaf_pool_fair.

Check TICL.CTree.Interp.Yield.Fair.agaf_pool_simulation_fair.
Print Assumptions TICL.CTree.Interp.Yield.Fair.agaf_pool_simulation_fair.

Check TICL.CTree.Interp.Yield.Execution.pool_simulation_rr_bisim.
Print Assumptions TICL.CTree.Interp.Yield.Execution.pool_simulation_rr_bisim.

Check TICL.CTree.Interp.Yield.Execution.source_execution_complete.
Print Assumptions TICL.CTree.Interp.Yield.Execution.source_execution_complete.

Check examples.CSL.Queue.Shared.exact_worker_turn.
Print Assumptions examples.CSL.Queue.Shared.exact_worker_turn.

Check examples.CSL.Queue.Shared.shared_worker_turn.
Print Assumptions examples.CSL.Queue.Shared.shared_worker_turn.

Check examples.CSL.Queue.Shared.shared_rotate_agaf_pop_alloc_nd_fresh.
Print Assumptions examples.CSL.Queue.Shared.shared_rotate_agaf_pop_alloc_nd_fresh.

Check examples.CSL.Queue.Shared.shared_rotate_agaf_pop_alloc_rr_fresh.
Print Assumptions examples.CSL.Queue.Shared.shared_rotate_agaf_pop_alloc_rr_fresh.

Check examples.CSL.Queue.Ticl.rotate_agaf_pop_alloc_fresh.
Print Assumptions examples.CSL.Queue.Ticl.rotate_agaf_pop_alloc_fresh.

Check examples.CSL.Queue.Ticl.rotate_agaf_pop_alloc_q2_fresh.
Print Assumptions examples.CSL.Queue.Ticl.rotate_agaf_pop_alloc_q2_fresh.

Check examples.CSL.Queue.Client.allocated_shared_queue_passive_fresh_rr.
Print Assumptions examples.CSL.Queue.Client.allocated_shared_queue_passive_fresh_rr.

Check examples.CSL.Queue.Client.allocated_shared_queue_split_passive_fresh_rr.
Print Assumptions examples.CSL.Queue.Client.allocated_shared_queue_split_passive_fresh_rr.

Check examples.CSL.Queue.Client.allocated_shared_queue_rr_contract.
Print Assumptions examples.CSL.Queue.Client.allocated_shared_queue_rr_contract.

Check examples.CSL.Queue.Client.rotate_once_split_cps.
Print Assumptions examples.CSL.Queue.Client.rotate_once_split_cps.

Check examples.CSL.Queue.Client.denote_flow_worker_split.
Print Assumptions examples.CSL.Queue.Client.denote_flow_worker_split.

Check examples.CSL.Queue.Client.denote_worker_split.
Print Assumptions examples.CSL.Queue.Client.denote_worker_split.

Check examples.CSL.Queue.Client.worker_split_pool_rr.
Print Assumptions examples.CSL.Queue.Client.worker_split_pool_rr.

Check examples.CSL.Queue.Client.shared_queue_split_rr.
Print Assumptions examples.CSL.Queue.Client.shared_queue_split_rr.

Check examples.CSL.Queue.Client.allocated_shared_queue_split_rr.
Print Assumptions examples.CSL.Queue.Client.allocated_shared_queue_split_rr.

Check examples.CSL.Queue.Client.client_passive_10.
Print Assumptions examples.CSL.Queue.Client.client_passive_10.

Check examples.CSL.Queue.Client.client_split_passive_10.
Print Assumptions examples.CSL.Queue.Client.client_split_passive_10.

Check examples.CSL.Queue.Client.client_split_prefix3.
Print Assumptions examples.CSL.Queue.Client.client_split_prefix3.

Check examples.CSL.Queue.Client.client_frame_preserved.
Print Assumptions examples.CSL.Queue.Client.client_frame_preserved.

Check examples.CSL.Queue.Client.client_heap_cycle3.
Print Assumptions examples.CSL.Queue.Client.client_heap_cycle3.

Check examples.CSL.Frame.Shared.write_ret.
Print Assumptions examples.CSL.Frame.Shared.write_ret.

Check examples.CSL.Frame.Shared.write_ax_framed.
Print Assumptions examples.CSL.Frame.Shared.write_ax_framed.

Check examples.CSL.Frame.AN.an_two_procs_nd.
Print Assumptions examples.CSL.Frame.AN.an_two_procs_nd.

Check examples.CSL.Frame.AN.an_two_procs_rr.
Print Assumptions examples.CSL.Frame.AN.an_two_procs_rr.

Check examples.CSL.Control.captured_before_yield_rr.
Print Assumptions examples.CSL.Control.captured_before_yield_rr.

Check examples.HiddenBr.delayed_branch_permutation.
Print Assumptions examples.HiddenBr.delayed_branch_permutation.

Check examples.HiddenBr.refine_rr_branch01_zero.
Print Assumptions examples.HiddenBr.refine_rr_branch01_zero.

Check examples.HiddenBr.refine_rr_branch10_zero.
Print Assumptions examples.HiddenBr.refine_rr_branch10_zero.

Check examples.HiddenBr.refine_rr_not_sbisim_congruent.
Print Assumptions examples.HiddenBr.refine_rr_not_sbisim_congruent.

Check examples.CSL.Allocator.Execution.allocator_simulation.
Print Assumptions examples.CSL.Allocator.Execution.allocator_simulation.

Check examples.CSL.Allocator.Liveness.allocator_agaf_fair.
Print Assumptions examples.CSL.Allocator.Liveness.allocator_agaf_fair.

Check examples.CSL.Allocator.Liveness.source_remote_free_lockfree.
Print Assumptions examples.CSL.Allocator.Liveness.source_remote_free_lockfree.

Check examples.CSL.Allocator.Liveness.source_retired_eventually_reclaimed.
Print Assumptions examples.CSL.Allocator.Liveness.source_retired_eventually_reclaimed.

Check examples.CSL.Allocator.Counterexamples.fair_starvation_exists.
Print Assumptions examples.CSL.Allocator.Counterexamples.fair_starvation_exists.

Check examples.CSL.Allocator.Counterexamples.owner_stall_prevents_reclamation.
Print Assumptions examples.CSL.Allocator.Counterexamples.owner_stall_prevents_reclamation.

Check TICL.Logic.Simulation.ticll_sim.
Print Assumptions TICL.Logic.Simulation.ticll_sim.

Check TICL.Logic.Simulation.ticlr_sim.
Print Assumptions TICL.Logic.Simulation.ticlr_sim.

Check TICL.CTree.Interp.Yield.RoundRobin.interp_schedule_rr_user_bind.
Print Assumptions TICL.CTree.Interp.Yield.RoundRobin.interp_schedule_rr_user_bind.

Check TICL.Lang.CoCSL.Mod.run_rr_fork_bind.
Print Assumptions TICL.Lang.CoCSL.Mod.run_rr_fork_bind.

Check TICL.Logic.Setoid.proper_entailsL_meq.
Print Assumptions TICL.Logic.Setoid.proper_entailsL_meq.

Check TICL.Logic.Setoid.proper_entailsR_meq.
Print Assumptions TICL.Logic.Setoid.proper_entailsR_meq.

Check TICL.CTree.Logic.Iter.ag_iter.
Print Assumptions TICL.CTree.Logic.Iter.ag_iter.

Check TICL.CTree.Logic.Bind.aur_bind_r.
Print Assumptions TICL.CTree.Logic.Bind.aur_bind_r.
