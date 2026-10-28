(** * Formal-evidence roots.

    Each proof root has a [Check] and [Print Assumptions] pair.
    The evidence driver supplies query-output delimiters externally.
    Assumption controls are not claims of identical historical source code. *)
From TICL Require Import
  CTree.Interp.CSL.Frame
  CTree.Interp.Yield.Fair
  CTree.Interp.Yield.Execution
  Logic.Simulation
  CTree.Interp.Yield.RoundRobin
  Lang.CoCSL.Mod
  Lang.CoCSL.Owned
  Lang.CoCSL.Separation.
From TICL Require Import Logic.Setoid CTree.Logic.Iter CTree.Logic.Bind.

From examples Require Import
  CSL.Queue.Shared
  CSL.Queue.Ticl
  CSL.Queue.Client
  CSL.Frame.Shared
  CSL.Frame.AF
  CSL.Frame.AG
  CSL.Frame.AN
  CSL.Control
  HiddenBr
  CSL.Allocator.Execution
  CSL.Allocator.Liveness
  CSL.Allocator.Counterexamples
  CSL.Frame.Separation.

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

Check TICL.Lang.CoCSL.Owned.owned_erasure.
Print Assumptions TICL.Lang.CoCSL.Owned.owned_erasure.

Check TICL.Lang.CoCSL.Owned.owned_fork_erasure.
Print Assumptions TICL.Lang.CoCSL.Owned.owned_fork_erasure.

Check TICL.Lang.CoCSL.Owned.instrument_owned_adequate.
Print Assumptions TICL.Lang.CoCSL.Owned.instrument_owned_adequate.

Check TICL.Lang.CoCSL.Separation.global_hau_split.
Print Assumptions TICL.Lang.CoCSL.Separation.global_hau_split.

Check TICL.Lang.CoCSL.Separation.global_heu_split.
Print Assumptions TICL.Lang.CoCSL.Separation.global_heu_split.

Check TICL.Lang.CoCSL.Separation.global_han_split.
Print Assumptions TICL.Lang.CoCSL.Separation.global_han_split.

Check TICL.Lang.CoCSL.Separation.global_hag_split.
Print Assumptions TICL.Lang.CoCSL.Separation.global_hag_split.

Check TICL.Lang.CoCSL.Separation.global_heg_fair_split.
Print Assumptions TICL.Lang.CoCSL.Separation.global_heg_fair_split.

Check TICL.Lang.CoCSL.Separation.global_heg_fair_one.
Print Assumptions TICL.Lang.CoCSL.Separation.global_heg_fair_one.

Check TICL.Lang.CoCSL.Separation.global_hdone_split.
Print Assumptions TICL.Lang.CoCSL.Separation.global_hdone_split.

Check TICL.Lang.CoCSL.Separation.global_hret_split.
Print Assumptions TICL.Lang.CoCSL.Separation.global_hret_split.

Check TICL.Lang.CoCSL.Separation.global_han_owned.
Print Assumptions TICL.Lang.CoCSL.Separation.global_han_owned.

Check TICL.Lang.CoCSL.Separation.global_hen_owned.
Print Assumptions TICL.Lang.CoCSL.Separation.global_hen_owned.

Check TICL.Lang.CoCSL.Separation.weak_han_to_local.
Print Assumptions TICL.Lang.CoCSL.Separation.weak_han_to_local.

Check TICL.Lang.CoCSL.Separation.weak_hen_to_local.
Print Assumptions TICL.Lang.CoCSL.Separation.weak_hen_to_local.

Check TICL.Lang.CoCSL.Separation.weak_hau_to_local.
Print Assumptions TICL.Lang.CoCSL.Separation.weak_hau_to_local.

Check TICL.Lang.CoCSL.Separation.weak_heu_to_local.
Print Assumptions TICL.Lang.CoCSL.Separation.weak_heu_to_local.

Check TICL.Lang.CoCSL.Separation.weak_hag_to_local.
Print Assumptions TICL.Lang.CoCSL.Separation.weak_hag_to_local.

Check TICL.Lang.CoCSL.Separation.weak_heg_to_local.
Print Assumptions TICL.Lang.CoCSL.Separation.weak_heg_to_local.

Check TICL.Lang.CoCSL.Separation.weak_hret_to_local.
Print Assumptions TICL.Lang.CoCSL.Separation.weak_hret_to_local.

Check TICL.Lang.CoCSL.Separation.fork_hau_split.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_hau_split.

Check TICL.Lang.CoCSL.Separation.fork_heu_split.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_heu_split.

Check TICL.Lang.CoCSL.Separation.fork_hau_split_view.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_hau_split_view.

Check TICL.Lang.CoCSL.Separation.fork_han_split.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_han_split.

Check TICL.Lang.CoCSL.Separation.fork_hag_split.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_hag_split.

Check TICL.Lang.CoCSL.Separation.fork_heg_fair_split.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_heg_fair_split.

Check examples.CSL.Frame.Separation.FiniteRegression.fork_run_nd_trace.
Print Assumptions examples.CSL.Frame.Separation.FiniteRegression.fork_run_nd_trace.

Check TICL.CTree.Logic.Sim.sbisim_csim.
Print Assumptions TICL.CTree.Logic.Sim.sbisim_csim.

Check TICL.Lang.CoCSL.Owned.erase_owned_trans_forward.
Print Assumptions TICL.Lang.CoCSL.Owned.erase_owned_trans_forward.

Check TICL.Lang.CoCSL.Owned.erase_owned_visible_trans.
Print Assumptions TICL.Lang.CoCSL.Owned.erase_owned_visible_trans.

Check TICL.Lang.CoCSL.Owned.erase_owned_terminal_trans.
Print Assumptions TICL.Lang.CoCSL.Owned.erase_owned_terminal_trans.

Check TICL.Lang.CoCSL.Owned.erase_owned_silent_path.
Print Assumptions TICL.Lang.CoCSL.Owned.erase_owned_silent_path.

Check TICL.Lang.CoCSL.Owned.erase_owned_select.
Print Assumptions TICL.Lang.CoCSL.Owned.erase_owned_select.

Check TICL.Lang.CoCSL.Owned.erase_owned_terminal.
Print Assumptions TICL.Lang.CoCSL.Owned.erase_owned_terminal.

Check TICL.Lang.CoCSL.Separation.owned_ticll_erasure.
Print Assumptions TICL.Lang.CoCSL.Separation.owned_ticll_erasure.

Check TICL.Lang.CoCSL.Separation.owned_ticlr_erasure.
Print Assumptions TICL.Lang.CoCSL.Separation.owned_ticlr_erasure.

Check TICL.Lang.CoCSL.Separation.fork_ticll_erasure.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_ticll_erasure.

Check TICL.Lang.CoCSL.Separation.fork_ticlr_erasure.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_ticlr_erasure.

Check TICL.Lang.CoCSL.Separation.owned_haf_done_ticl.
Print Assumptions TICL.Lang.CoCSL.Separation.owned_haf_done_ticl.

Check TICL.Lang.CoCSL.Separation.owned_hef_done_ticl.
Print Assumptions TICL.Lang.CoCSL.Separation.owned_hef_done_ticl.

Check TICL.Lang.CoCSL.Separation.owned_hag_ticl.
Print Assumptions TICL.Lang.CoCSL.Separation.owned_hag_ticl.

Check TICL.Lang.CoCSL.Separation.owned_heg_ticl.
Print Assumptions TICL.Lang.CoCSL.Separation.owned_heg_ticl.

Check TICL.Lang.CoCSL.Separation.fork_haf_done_ticl.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_haf_done_ticl.

Check TICL.Lang.CoCSL.Separation.fork_hef_done_ticl.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_hef_done_ticl.

Check TICL.Lang.CoCSL.Separation.fork_hag_ticl.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_hag_ticl.

Check TICL.Lang.CoCSL.Separation.fork_heg_ticl.
Print Assumptions TICL.Lang.CoCSL.Separation.fork_heg_ticl.

Check examples.CSL.Frame.Separation.FiniteTiclRegression.finite_raw_af_done.
Print Assumptions examples.CSL.Frame.Separation.FiniteTiclRegression.finite_raw_af_done.

Check examples.CSL.Frame.Separation.FiniteTiclRegression.finite_raw_ef_done.
Print Assumptions examples.CSL.Frame.Separation.FiniteTiclRegression.finite_raw_ef_done.

Check examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_zero_owned_actions.
Print Assumptions examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_zero_owned_actions.

Check examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_raw_value_transition.
Print Assumptions examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_raw_value_transition.

Check examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_not_raw_done.
Print Assumptions examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_not_raw_done.

Check examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_raw_af_done.
Print Assumptions examples.CSL.Frame.Separation.FiniteTiclRegression.terminal_raw_af_done.

Check examples.CSL.Frame.Separation.AlwaysTiclRegression.loops_raw_ag.
Print Assumptions examples.CSL.Frame.Separation.AlwaysTiclRegression.loops_raw_ag.

Check examples.CSL.Frame.Separation.AlwaysTiclRegression.loops_raw_eg.
Print Assumptions examples.CSL.Frame.Separation.AlwaysTiclRegression.loops_raw_eg.

Check examples.CSL.Frame.Separation.AlwaysTiclRegression.fair_exec_infinitely_visible.
Print Assumptions examples.CSL.Frame.Separation.AlwaysTiclRegression.fair_exec_infinitely_visible.

Check examples.CSL.Frame.Separation.SilentReadTiclRegression.read_admissible.
Print Assumptions examples.CSL.Frame.Separation.SilentReadTiclRegression.read_admissible.

Check examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_owned_hag.
Print Assumptions examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_owned_hag.

Check examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_focused_owned_hag.
Print Assumptions examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_focused_owned_hag.

Check examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_erasure_stuck.
Print Assumptions examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_erasure_stuck.

Check examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_erasure_no_ag.
Print Assumptions examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_erasure_no_ag.

Check examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_original_stuck.
Print Assumptions examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_original_stuck.

Check examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_original_no_ag.
Print Assumptions examples.CSL.Frame.Separation.SilentReadTiclRegression.read_loop_original_no_ag.

Check examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_run.
Print Assumptions examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_run.

Check examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_infinitely_reads.
Print Assumptions examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_infinitely_reads.

Check examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_not_infinitely_visible.
Print Assumptions examples.CSL.Frame.Separation.SilentReadTiclRegression.read_forever_not_infinitely_visible.

Check examples.CSL.Frame.AF.af_two_procs_rr.
Print Assumptions examples.CSL.Frame.AF.af_two_procs_rr.

Check examples.CSL.Frame.AF.af_two_procs_nd.
Print Assumptions examples.CSL.Frame.AF.af_two_procs_nd.

Check examples.CSL.Frame.AG.ag_two_procs_rr.
Print Assumptions examples.CSL.Frame.AG.ag_two_procs_rr.

Check examples.CSL.Frame.AG.ag_two_procs_nd.
Print Assumptions examples.CSL.Frame.AG.ag_two_procs_nd.
