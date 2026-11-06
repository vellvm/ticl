(** * Formal-evidence roots.

    Each proof root has a [Check] and [Print Assumptions] pair.
    The evidence driver supplies query-output delimiters externally.
    Assumption controls are not claims of identical historical source code. *)
From TICL Require Import
  CTree.Interp.CSL.Frame
  CTree.Interp.CSL.Asep
  CTree.Interp.Yield.Fair
  CTree.Interp.Yield.Execution
  Logic.Simulation
  CTree.Interp.Yield.RoundRobin
  Lang.CoCSL.Mod
  Lang.CoCSL.Owned
  Lang.CoCSL.Asep.
From TICL Require Import Logic.Setoid CTree.Logic.Iter CTree.Logic.Bind
  CTree.Logic.Soundness CTree.Logic.AX CTree.Logic.State CTree.Logic.EG.
From TICL Require Import CTree.Logic.Trace.

From examples Require Import
  CSL.Queue.Shared
  CSL.Queue.Ticl
  CSL.Queue.Client
  CSL.Frame.Shared
  CSL.Frame.Asep
  CSL.Frame.AF
  CSL.Frame.AG
  CSL.Frame.AN
  CSL.Control
  HiddenBr
  CSL.Allocator.Execution
  CSL.Allocator.Liveness
  CSL.Allocator.Counterexamples
  CSL.Frame.HeapObservations
  CSL.Frame.Separation
  CSL.Frame.Active.

Check TICL.CTree.Interp.CSL.Frame.csim_interp_frame.
Print Assumptions TICL.CTree.Interp.CSL.Frame.csim_interp_frame.

Check TICL.CTree.Interp.CSL.Frame.ticl_csl_frame.
Print Assumptions TICL.CTree.Interp.CSL.Frame.ticl_csl_frame.

Check TICL.CTree.Interp.CSL.Frame.ticl_csl_frameW.
Print Assumptions TICL.CTree.Interp.CSL.Frame.ticl_csl_frameW.

Check TICL.CTree.Interp.CSL.Frame.anr_csl_frame_done.
Print Assumptions TICL.CTree.Interp.CSL.Frame.anr_csl_frame_done.

Check TICL.CTree.Interp.CSL.Frame.aur_csl_frame_done.
Print Assumptions TICL.CTree.Interp.CSL.Frame.aur_csl_frame_done.

Check TICL.CTree.Interp.Yield.Fair.rr_fair.
Print Assumptions TICL.CTree.Interp.Yield.Fair.rr_fair.

Check TICL.CTree.Interp.Yield.Fair.nd_not_fair.
Print Assumptions TICL.CTree.Interp.Yield.Fair.nd_not_fair.

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

Check TICL.CTree.Logic.Trace.af_vis_eventually_label.
Print Assumptions TICL.CTree.Logic.Trace.af_vis_eventually_label.

Check TICL.CTree.Logic.Trace.agaf_family_recurrent_label.
Print Assumptions TICL.CTree.Logic.Trace.agaf_family_recurrent_label.

Check TICL.CTree.Interp.CSL.Mod.csl_fresh_implies_recurrent_emission.
Print Assumptions TICL.CTree.Interp.CSL.Mod.csl_fresh_implies_recurrent_emission.

Check examples.CSL.Frame.HeapObservations.EventRecurrenceControls.repeat_plain_payload_recurrent.
Print Assumptions examples.CSL.Frame.HeapObservations.EventRecurrenceControls.repeat_plain_payload_recurrent.

Check examples.CSL.Frame.HeapObservations.EventRecurrenceControls.retained_payload_not_recurrent.
Print Assumptions examples.CSL.Frame.HeapObservations.EventRecurrenceControls.retained_payload_not_recurrent.

Check examples.CSL.Frame.HeapObservations.EventRecurrenceControls.universal_recurrence_rejects_silent_branch.
Print Assumptions examples.CSL.Frame.HeapObservations.EventRecurrenceControls.universal_recurrence_rejects_silent_branch.

Check examples.CSL.Frame.HeapObservations.EventRecurrenceControls.event_recurrence_rejects_return.
Print Assumptions examples.CSL.Frame.HeapObservations.EventRecurrenceControls.event_recurrence_rejects_return.


Check examples.CSL.Frame.Shared.write_ax_ret.
Print Assumptions examples.CSL.Frame.Shared.write_ax_ret.

Check examples.CSL.Frame.Shared.write_ax_done_framed.
Print Assumptions examples.CSL.Frame.Shared.write_ax_done_framed.

Check examples.CSL.Frame.AN.an_two_procs_nd.
Print Assumptions examples.CSL.Frame.AN.an_two_procs_nd.

Check examples.CSL.Frame.AN.an_two_procs_rr.
Print Assumptions examples.CSL.Frame.AN.an_two_procs_rr.

Check examples.CSL.Frame.AN.wproc_own_2_no_ax6_nd.
Print Assumptions examples.CSL.Frame.AN.wproc_own_2_no_ax6_nd.

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

Check examples.HiddenBr.rr_preserves_thread_branch.
Print Assumptions examples.HiddenBr.rr_preserves_thread_branch.

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

Check TICL.Logic.Simulation.ticl_sim.
Print Assumptions TICL.Logic.Simulation.ticl_sim.

Check TICL.CTree.Interp.Yield.Policy.interp_schedule_fair_user_bind.
Print Assumptions TICL.CTree.Interp.Yield.Policy.interp_schedule_fair_user_bind.

Check TICL.Lang.CoCSL.Mod.run_rr_fork_bind.
Print Assumptions TICL.Lang.CoCSL.Mod.run_rr_fork_bind.

Check TICL.Logic.Setoid.proper_entails_meq.
Print Assumptions TICL.Logic.Setoid.proper_entails_meq.

Check TICL.CTree.Logic.Iter.ag_iter.
Print Assumptions TICL.CTree.Logic.Iter.ag_iter.

Check TICL.CTree.Logic.Bind.u_bind_r.
Print Assumptions TICL.CTree.Logic.Bind.u_bind_r.

Check TICL.CTree.Logic.Soundness.soundness.
Print Assumptions TICL.CTree.Logic.Soundness.soundness.

Check TICL.CTree.Logic.AX.an_step.
Print Assumptions TICL.CTree.Logic.AX.an_step.

Check TICL.CTree.Logic.State.au_state_bind_r.
Print Assumptions TICL.CTree.Logic.State.au_state_bind_r.

Check TICL.CTree.Interp.CSL.Owned.prim_reflect_joined.
Print Assumptions TICL.CTree.Interp.CSL.Owned.prim_reflect_joined.

Check TICL.Lang.CoCSL.Owned.owned_fork_runner.
Print Assumptions TICL.Lang.CoCSL.Owned.owned_fork_runner.

Check TICL.CTree.Interp.CSL.Owned.owned_interp_action.
Print Assumptions TICL.CTree.Interp.CSL.Owned.owned_interp_action.

Check TICL.Lang.CoCSL.Asep.global_hau_split.
Print Assumptions TICL.Lang.CoCSL.Asep.global_hau_split.

Check TICL.Lang.CoCSL.Asep.global_heu_split.
Print Assumptions TICL.Lang.CoCSL.Asep.global_heu_split.

Check TICL.Lang.CoCSL.Asep.global_han_split.
Print Assumptions TICL.Lang.CoCSL.Asep.global_han_split.

Check TICL.Lang.CoCSL.Asep.global_hag_split.
Print Assumptions TICL.Lang.CoCSL.Asep.global_hag_split.

Check TICL.Lang.CoCSL.Asep.global_heg_fair_split.
Print Assumptions TICL.Lang.CoCSL.Asep.global_heg_fair_split.

Check TICL.Lang.CoCSL.Asep.global_heg_fair_one.
Print Assumptions TICL.Lang.CoCSL.Asep.global_heg_fair_one.

Check TICL.Lang.CoCSL.Asep.global_hdone_split.
Print Assumptions TICL.Lang.CoCSL.Asep.global_hdone_split.

Check TICL.Lang.CoCSL.Asep.global_hret_split.
Print Assumptions TICL.Lang.CoCSL.Asep.global_hret_split.

Check TICL.CTree.Interp.CSL.Owned.same_view_equivalence.
Print Assumptions TICL.CTree.Interp.CSL.Owned.same_view_equivalence.

Check TICL.CTree.Interp.CSL.Owned.owned_equ_same_view.
Print Assumptions TICL.CTree.Interp.CSL.Owned.owned_equ_same_view.

Check TICL.CTree.Interp.CSL.Owned.same_view_project.
Print Assumptions TICL.CTree.Interp.CSL.Owned.same_view_project.

Check examples.CSL.Frame.Separation.NextRegression.unequal_lineage_counts_not_uniform.
Print Assumptions examples.CSL.Frame.Separation.NextRegression.unequal_lineage_counts_not_uniform.

Check TICL.Lang.CoCSL.Asep.global_han_owned.
Print Assumptions TICL.Lang.CoCSL.Asep.global_han_owned.

Check TICL.Lang.CoCSL.Asep.global_hen_owned.
Print Assumptions TICL.Lang.CoCSL.Asep.global_hen_owned.

Check TICL.Lang.CoCSL.Asep.weak_han_to_local.
Print Assumptions TICL.Lang.CoCSL.Asep.weak_han_to_local.

Check TICL.Lang.CoCSL.Asep.weak_hen_to_local.
Print Assumptions TICL.Lang.CoCSL.Asep.weak_hen_to_local.

Check TICL.Lang.CoCSL.Asep.weak_hau_to_local.
Print Assumptions TICL.Lang.CoCSL.Asep.weak_hau_to_local.

Check TICL.Lang.CoCSL.Asep.weak_heu_to_local.
Print Assumptions TICL.Lang.CoCSL.Asep.weak_heu_to_local.

Check TICL.Lang.CoCSL.Asep.weak_hag_to_local.
Print Assumptions TICL.Lang.CoCSL.Asep.weak_hag_to_local.

Check TICL.Lang.CoCSL.Asep.weak_heg_to_local.
Print Assumptions TICL.Lang.CoCSL.Asep.weak_heg_to_local.

Check TICL.Lang.CoCSL.Asep.weak_hret_to_local.
Print Assumptions TICL.Lang.CoCSL.Asep.weak_hret_to_local.

Check TICL.Lang.CoCSL.Asep.fork_hau_split.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_hau_split.

Check TICL.Lang.CoCSL.Asep.fork_heu_split.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_heu_split.

Check TICL.Lang.CoCSL.Asep.fork_hau_split_view.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_hau_split_view.

Check TICL.Lang.CoCSL.Asep.fork_han_split.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_han_split.

Check TICL.Lang.CoCSL.Asep.fork_hag_split.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_hag_split.

Check TICL.Lang.CoCSL.Asep.fork_heg_fair_split.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_heg_fair_split.

Check examples.CSL.Frame.Separation.FiniteRegression.fork_run_nd_trace.
Print Assumptions examples.CSL.Frame.Separation.FiniteRegression.fork_run_nd_trace.

Check TICL.CTree.Logic.Sim.sbisim_csim.
Print Assumptions TICL.CTree.Logic.Sim.sbisim_csim.

Check TICL.CTree.Interp.CSL.Owned.owned_interp_trans_forward.
Print Assumptions TICL.CTree.Interp.CSL.Owned.owned_interp_trans_forward.

Check TICL.CTree.Interp.CSL.Owned.owned_interp_visible.
Print Assumptions TICL.CTree.Interp.CSL.Owned.owned_interp_visible.

Check TICL.CTree.Interp.CSL.Owned.owned_interp_terminal_trans.
Print Assumptions TICL.CTree.Interp.CSL.Owned.owned_interp_terminal_trans.

Check TICL.CTree.Interp.CSL.Owned.owned_interp_silent.
Print Assumptions TICL.CTree.Interp.CSL.Owned.owned_interp_silent.

Check TICL.CTree.Interp.CSL.Owned.owned_interp_select.
Print Assumptions TICL.CTree.Interp.CSL.Owned.owned_interp_select.

Check TICL.CTree.Interp.CSL.Owned.owned_interp_terminal.
Print Assumptions TICL.CTree.Interp.CSL.Owned.owned_interp_terminal.

Check TICL.Lang.CoCSL.Asep.owned_ticl_transport.
Print Assumptions TICL.Lang.CoCSL.Asep.owned_ticl_transport.

Check TICL.Lang.CoCSL.Asep.fork_ticl.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_ticl.

Check TICL.Lang.CoCSL.Asep.owned_haf_done_ticl.
Print Assumptions TICL.Lang.CoCSL.Asep.owned_haf_done_ticl.

Check TICL.Lang.CoCSL.Asep.owned_hef_done_ticl.
Print Assumptions TICL.Lang.CoCSL.Asep.owned_hef_done_ticl.

Check TICL.Lang.CoCSL.Asep.owned_hag_ticl.
Print Assumptions TICL.Lang.CoCSL.Asep.owned_hag_ticl.

Check TICL.Lang.CoCSL.Asep.owned_heg_ticl.
Print Assumptions TICL.Lang.CoCSL.Asep.owned_heg_ticl.

Check TICL.Lang.CoCSL.Asep.fork_haf_done_ticl.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_haf_done_ticl.

Check TICL.Lang.CoCSL.Asep.fork_hef_done_ticl.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_hef_done_ticl.

Check TICL.Lang.CoCSL.Asep.fork_hag_ticl.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_hag_ticl.

Check TICL.Lang.CoCSL.Asep.fork_heg_ticl.
Print Assumptions TICL.Lang.CoCSL.Asep.fork_heg_ticl.

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

Check TICL.Logic.Syntax.map_atoms.
Print Assumptions TICL.Logic.Syntax.map_atoms.

Check TICL.Logic.Simulation.framer_event_eq.
Print Assumptions TICL.Logic.Simulation.framer_event_eq.

Check TICL.CTree.Interp.CSL.Frame.frameER_right_unique.
Print Assumptions TICL.CTree.Interp.CSL.Frame.frameER_right_unique.

Check TICL.CTree.Logic.State.ag_state_iter_logs.
Print Assumptions TICL.CTree.Logic.State.ag_state_iter_logs.

Check TICL.CTree.Trace.realizes_emit_list_prefix.
Print Assumptions TICL.CTree.Trace.realizes_emit_list_prefix.

Check TICL.CTree.Interp.Heap.heap_handlerW_alloc_no_space.
Print Assumptions TICL.CTree.Interp.Heap.heap_handlerW_alloc_no_space.

Check examples.CSL.Frame.Shared.write_ax_ret_framed.
Print Assumptions examples.CSL.Frame.Shared.write_ax_ret_framed.

Check examples.CSL.Frame.AN.an_two_procs_nd_ret.
Print Assumptions examples.CSL.Frame.AN.an_two_procs_nd_ret.

Check examples.CSL.Frame.AN.an_two_procs_rr_ret.
Print Assumptions examples.CSL.Frame.AN.an_two_procs_rr_ret.

Check examples.CSL.Frame.AN.an_rr_3_5.
Print Assumptions examples.CSL.Frame.AN.an_rr_3_5.

Check examples.CSL.Frame.AN.an_nd_3_5.
Print Assumptions examples.CSL.Frame.AN.an_nd_3_5.

Check examples.CSL.Frame.HeapObservations.mutation_probe_spec.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_probe_spec.

Check examples.CSL.Frame.HeapObservations.same_value_mutations_visible.
Print Assumptions examples.CSL.Frame.HeapObservations.same_value_mutations_visible.

Check examples.CSL.Frame.HeapObservations.fault_prefix_preserved.
Print Assumptions examples.CSL.Frame.HeapObservations.fault_prefix_preserved.

Check examples.CSL.Frame.HeapObservations.mutation_loop_prefix_nd.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_loop_prefix_nd.

Check examples.CSL.Frame.HeapObservations.mutation_loop_prefix_rr.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_loop_prefix_rr.

Check examples.CSL.Frame.HeapObservations.mutation_loop_agaf_nd.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_loop_agaf_nd.

Check examples.CSL.Frame.HeapObservations.mutation_loop_agaf_rr.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_loop_agaf_rr.

Check examples.CSL.Frame.HeapObservations.mutation_spin_no_heap_nd.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_spin_no_heap_nd.

Check examples.CSL.Frame.HeapObservations.mutation_spin_no_heap_rr.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_spin_no_heap_rr.

Check examples.CSL.Frame.HeapObservations.mutation_observation_replaced.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_observation_replaced.

Check examples.CSL.Frame.HeapObservations.mutation_loop_framed_nd.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_loop_framed_nd.

Check examples.CSL.Frame.HeapObservations.mutation_loop_framed_rr.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_loop_framed_rr.

Check examples.CSL.Frame.HeapObservations.mutation_return_framed.
Print Assumptions examples.CSL.Frame.HeapObservations.mutation_return_framed.

Check examples.CSL.Frame.HeapObservations.queue_snapshot_prefix.
Print Assumptions examples.CSL.Frame.HeapObservations.queue_snapshot_prefix.

Check examples.CSL.Frame.HeapObservations.allocator_snapshot_prefix.
Print Assumptions examples.CSL.Frame.HeapObservations.allocator_snapshot_prefix.

Check examples.CSL.Frame.HeapObservations.allocator_partial_fault_prefix.
Print Assumptions examples.CSL.Frame.HeapObservations.allocator_partial_fault_prefix.

Check examples.CSL.Frame.HeapObservations.two_log_iterator_recurrence.
Print Assumptions examples.CSL.Frame.HeapObservations.two_log_iterator_recurrence.

Check examples.CSL.Frame.HeapObservations.two_log_detached_suffix_no_target.
Print Assumptions examples.CSL.Frame.HeapObservations.two_log_detached_suffix_no_target.

Check examples.CSL.Frame.HeapObservations.empty_log_pool_selection.
Print Assumptions examples.CSL.Frame.HeapObservations.empty_log_pool_selection.

Check examples.CSL.Frame.HeapObservations.finish_heap_predecessor_framed.
Print Assumptions examples.CSL.Frame.HeapObservations.finish_heap_predecessor_framed.

Check examples.CSL.Frame.HeapObservations.emission_prefix_stable.
Print Assumptions examples.CSL.Frame.HeapObservations.emission_prefix_stable.

Check examples.CSL.Frame.HeapObservations.exact_heap_prefix_not_stable.
Print Assumptions examples.CSL.Frame.HeapObservations.exact_heap_prefix_not_stable.

Check examples.CSL.Frame.HeapObservations.invalid_and_double_free_prefix.
Print Assumptions examples.CSL.Frame.HeapObservations.invalid_and_double_free_prefix.

Check examples.CSL.Frame.HeapObservations.initialization_fault_prefix.
Print Assumptions examples.CSL.Frame.HeapObservations.initialization_fault_prefix.

Check examples.CSL.Frame.HeapObservations.allocation_no_space_silent.
Print Assumptions examples.CSL.Frame.HeapObservations.allocation_no_space_silent.

Check examples.CSL.Frame.HeapObservations.empty_log_closed_turns.
Print Assumptions examples.CSL.Frame.HeapObservations.empty_log_closed_turns.

Check examples.CSL.Frame.HeapObservations.empty_log_pool_invariance_nd_rr.
Print Assumptions examples.CSL.Frame.HeapObservations.empty_log_pool_invariance_nd_rr.

Check TICL.CTree.Interp.CSL.Asep.asep_anc_compose.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_anc_compose.

Check TICL.CTree.Interp.CSL.Asep.asep_enc_compose.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_enc_compose.

Check TICL.CTree.Interp.CSL.Asep.asep_agc_compose.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_agc_compose.

Check TICL.CTree.Interp.CSL.Asep.asep_ret_compose.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_ret_compose.

Check TICL.CTree.Interp.CSL.Asep.asep_auc_ret_compose.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_auc_ret_compose.

Check TICL.CTree.Interp.CSL.Asep.asep_euc_ret_compose.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_euc_ret_compose.

Check TICL.CTree.Interp.CSL.Asep.asep_egc_run.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_egc_run.

Check TICL.CTree.Interp.CSL.Asep.asep_af_ret_compose.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_af_ret_compose.

Check TICL.CTree.Interp.CSL.Asep.asep_ef_ret_compose.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_ef_ret_compose.

Check TICL.CTree.Interp.CSL.Asep.asep_sat.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_sat.

Check TICL.CTree.Interp.CSL.Asep.asep_sat_intro.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_sat_intro.

Check TICL.CTree.Interp.CSL.Asep.local_obligation_proper.
Print Assumptions TICL.CTree.Interp.CSL.Asep.local_obligation_proper.

Check TICL.CTree.Interp.CSL.Asep.asep_ret.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_ret.

Check TICL.CTree.Interp.CSL.Asep.asep_ret_elim.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_ret_elim.

Check TICL.CTree.Logic.EG.egc_of_sequence.
Print Assumptions TICL.CTree.Logic.EG.egc_of_sequence.

Check TICL.CTree.Interp.CSL.Asep.state_split_proper.
Print Assumptions TICL.CTree.Interp.CSL.Asep.state_split_proper.

Check TICL.CTree.Interp.CSL.Asep.state_split_iff.
Print Assumptions TICL.CTree.Interp.CSL.Asep.state_split_iff.

Check TICL.CTree.Interp.CSL.Asep.state_split_forget.
Print Assumptions TICL.CTree.Interp.CSL.Asep.state_split_forget.

Check TICL.CTree.Interp.CSL.Asep.asep_at_inv.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_at_inv.

Check TICL.CTree.Interp.CSL.Asep.asep_sat_inv.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_sat_inv.

Check TICL.CTree.Interp.CSL.Asep.asep_local_step_inv.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_local_step_inv.

Check TICL.CTree.Interp.CSL.Asep.asep_at_auc_ret_step.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_at_auc_ret_step.

Check TICL.CTree.Interp.CSL.Asep.asep_auc_ret_empty.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_auc_ret_empty.

Check TICL.CTree.Interp.CSL.Asep.asep_ax_compose.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_ax_compose.

Check TICL.CTree.Interp.CSL.Asep.asep_ex_compose.
Print Assumptions TICL.CTree.Interp.CSL.Asep.asep_ex_compose.

Check examples.CSL.Frame.Active.NativeReturnRegression.native_ret_silent_frontier.
Print Assumptions examples.CSL.Frame.Active.NativeReturnRegression.native_ret_silent_frontier.

Check examples.CSL.Frame.Active.OperationalNextRegression.one_write_has_single_owner.
Print Assumptions examples.CSL.Frame.Active.OperationalNextRegression.one_write_has_single_owner.

Check examples.CSL.Frame.Active.AsyncNextRegression.asynchronous_AN.
Print Assumptions examples.CSL.Frame.Active.AsyncNextRegression.asynchronous_AN.

Check examples.CSL.Frame.Active.AsyncNextRegression.asynchronous_EN.
Print Assumptions examples.CSL.Frame.Active.AsyncNextRegression.asynchronous_EN.

Check examples.CSL.Frame.Active.AsyncNextRegression.global_next_retains_failed_target.
Print Assumptions examples.CSL.Frame.Active.AsyncNextRegression.global_next_retains_failed_target.

Check examples.CSL.Frame.Active.AsyncNextRegression.global_next_exactly_one_action.
Print Assumptions examples.CSL.Frame.Active.AsyncNextRegression.global_next_exactly_one_action.

Check examples.CSL.Frame.Active.TerminationActiveRegression.termination_inv_init.
Print Assumptions examples.CSL.Frame.Active.TerminationActiveRegression.termination_inv_init.

Check examples.CSL.Frame.Active.TerminationActiveRegression.termination_inv_closed.
Print Assumptions examples.CSL.Frame.Active.TerminationActiveRegression.termination_inv_closed.

Check examples.CSL.Frame.Active.TerminationActiveRegression.early_termination_inv.
Print Assumptions examples.CSL.Frame.Active.TerminationActiveRegression.early_termination_inv.

Check examples.CSL.Frame.Active.TerminationActiveRegression.early_inv_init.
Print Assumptions examples.CSL.Frame.Active.TerminationActiveRegression.early_inv_init.

Check examples.CSL.Frame.Active.TerminationActiveRegression.early_inv_closed.
Print Assumptions examples.CSL.Frame.Active.TerminationActiveRegression.early_inv_closed.

Check examples.CSL.Frame.Active.TerminationActiveRegression.both_af_final_cells.
Print Assumptions examples.CSL.Frame.Active.TerminationActiveRegression.both_af_final_cells.

Check examples.CSL.Frame.Active.TerminationActiveRegression.both_ef_final_cells.
Print Assumptions examples.CSL.Frame.Active.TerminationActiveRegression.both_ef_final_cells.

Check examples.CSL.Frame.Active.TerminationActiveRegression.early_parent_return_phase.
Print Assumptions examples.CSL.Frame.Active.TerminationActiveRegression.early_parent_return_phase.

Check examples.CSL.Frame.Active.TerminationActiveRegression.early_not_live_live.
Print Assumptions examples.CSL.Frame.Active.TerminationActiveRegression.early_not_live_live.

Check examples.CSL.Frame.Active.TerminationActiveRegression.early_until_ret.
Print Assumptions examples.CSL.Frame.Active.TerminationActiveRegression.early_until_ret.

Check examples.CSL.Frame.Active.AlwaysActiveRegression.loops_active_ag.
Print Assumptions examples.CSL.Frame.Active.AlwaysActiveRegression.loops_active_ag.

Check examples.CSL.Frame.Active.CommonEGActiveRegression.fair_view_exec_valid.
Print Assumptions examples.CSL.Frame.Active.CommonEGActiveRegression.fair_view_exec_valid.

Check examples.CSL.Frame.Active.CommonEGActiveRegression.fair_local_assertions.
Print Assumptions examples.CSL.Frame.Active.CommonEGActiveRegression.fair_local_assertions.

Check examples.CSL.Frame.Active.CommonEGActiveRegression.common_visible_execution_eg.
Print Assumptions examples.CSL.Frame.Active.CommonEGActiveRegression.common_visible_execution_eg.

Check examples.CSL.Frame.Active.CommonEGActiveRegression.silent_reads_are_not_visible_recurrence.
Print Assumptions examples.CSL.Frame.Active.CommonEGActiveRegression.silent_reads_are_not_visible_recurrence.

Check examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_init.
Print Assumptions examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_init.

Check examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_closed.
Print Assumptions examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_closed.

Check examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_inv.
Print Assumptions examples.CSL.Frame.Active.TransientActiveRegression.phase_inv_inv.

Check examples.CSL.Frame.Active.TransientActiveRegression.phase_view_step.
Print Assumptions examples.CSL.Frame.Active.TransientActiveRegression.phase_view_step.

Check examples.CSL.Frame.Active.TransientActiveRegression.parent_progress_remembered.
Print Assumptions examples.CSL.Frame.Active.TransientActiveRegression.parent_progress_remembered.

Check examples.CSL.Frame.Active.TransientActiveRegression.child_local_af.
Print Assumptions examples.CSL.Frame.Active.TransientActiveRegression.child_local_af.

Check examples.CSL.Frame.Active.TransientActiveRegression.parent_local_af.
Print Assumptions examples.CSL.Frame.Active.TransientActiveRegression.parent_local_af.

Check examples.CSL.Frame.Active.TransientActiveRegression.no_global_ef_separated_transient_endpoints.
Print Assumptions examples.CSL.Frame.Active.TransientActiveRegression.no_global_ef_separated_transient_endpoints.

Check examples.CSL.Frame.Active.FaultRegression.invalid_write_stuck.
Print Assumptions examples.CSL.Frame.Active.FaultRegression.invalid_write_stuck.

Check examples.CSL.Frame.Active.FaultRegression.invalid_write_not_admissible.
Print Assumptions examples.CSL.Frame.Active.FaultRegression.invalid_write_not_admissible.

(** Independent actual-shared-run proofs using ordinary [asep]; these eight
    concrete roots do not replace the generic pointwise composition rules. *)
Check examples.CSL.Frame.Asep.InvariantSeparation.bind_keeps_parent_post.
Print Assumptions examples.CSL.Frame.Asep.InvariantSeparation.bind_keeps_parent_post.

Check examples.CSL.Frame.Asep.InvariantSeparation.asep_two_procs_nd_ret.
Print Assumptions examples.CSL.Frame.Asep.InvariantSeparation.asep_two_procs_nd_ret.

Check examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ax2.
Print Assumptions examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ax2.

Check examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_not_ax1.
Print Assumptions examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_not_ax1.

Check examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ex_child.
Print Assumptions examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ex_child.

Check examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ex_parent.
Print Assumptions examples.CSL.Frame.Asep.InvariantSeparation.asep_writes_ex_parent.

Check examples.CSL.Frame.Asep.InvariantSeparation.asep_lprocs_agaf_nd.
Print Assumptions examples.CSL.Frame.Asep.InvariantSeparation.asep_lprocs_agaf_nd.

Check examples.CSL.Frame.Asep.InvariantSeparation.asep_lprocs_agaf_rr.
Print Assumptions examples.CSL.Frame.Asep.InvariantSeparation.asep_lprocs_agaf_rr.
