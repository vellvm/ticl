(** * Regression: two cooperating processes, [AF] under both schedulers.

    [fork2 (proc 1) (proc 2)]: each process reads, increments and emits its
    own cell, then yields. Each process's native [AF ret] fact is proved on its
    own region and framed by the other's ([work_af_framed_ret]); the cooperative prefix
    equation ([run_rr_prefix]/[run_nd_prefix]) runs the focused process alone,
    then [CYield] rejoins the pool.  Both processes finish and the heap is the
    join of the two incremented regions. *)
From Stdlib Require Import Fin Vector.
From Coinduction Require Import all.
From TICL Require Import CTree.Interp.Yield.Policy CTree.Logic.Yield CTree.Logic.Trace.
From examples Require Import CSL.Frame.Shared.

(** Round-robin execution finishes both processes with their incremented regions. *)
Local Theorem af_two_procs_rr_ret a b ctx c :
  <( {run_rr (fork2 (proc 1) (proc 2)) (shared a b ctx c)}, Pure |=R
     AF ret {fun '(s', _) _ => both (S a) (S b) (csl_memory s')} )>.
Proof.
  ticl_normalize.
  unfold fork2; rewrite run_rr_fork_bind.
  unfold denote.
  change ([denote_flow (proc 1);; Ret tt; denote_flow (proc 2);; Ret tt]%vector)
    with (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (proc 2) >>= fun _ => Ret tt)).
  unfold proc at 2; rr_prefix work_yield_fork_free.
  eapply (u_bind_r (b:=true) Q_A); [apply (work_af_framed_ret_W 2 1 b a ctx c); [constructor|apply frame_rel_shared_2] |].
  intros [s1 r] w1 HP; apply frame_post_work_W in HP as (-> & HM1 & HS1 & ->).
  rewrite interp_rr_bind, interp_rr_yield.
  rewrite interp_schedule_rr_select; cright; apply (an_vis (b:=true) _ _ tt); split; [csplit; auto with ticl|intros []].
  rewrite rr_pick_1_0.
  change (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt);; Ret tt))
    with (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) @ child := (denote_flow (proc 1) >>= fun _ => Ret tt)).
  unfold proc; rr_prefix work_yield_fork_free.
  eapply (u_bind_r (b:=true) Q_A); [apply (work_af_framed_ret_W 1 2 a (S b) ctx (S c)); [constructor|apply frame_rel_both_1; [|exact HS1]] |].
  { eapply peq_trans; [exact HM1|apply pop_comm, region_disj; auto]. }
  intros [s2 r] w2 HP; apply frame_post_work_W in HP as (-> & HM2 & _ & ->).
  rewrite interp_rr_bind, interp_rr_yield.
  change (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2)
    @ child := (denote_flow (CRet tt);; Ret tt))
    with (csl_pool (Vector.const (CRet tt) 2)).
  change (interp_schedule_rr sh 2 (csl_pool (Vector.const (CRet tt) 2)) None 1 s2)
    with (run_rr_pool (Vector.const (CRet tt) 2) None 1 s2).
  rewrite run_rr_pool_returns.
  apply (f_emit_list (b:=true) Q_A); [constructor|].
  cleft; apply ret_ret; [apply after_logs_not_done; constructor|exact HM2].
Qed.

(** Preserve the original eventual terminal claim. *)
Theorem af_two_procs_rr a b ctx c :
  auc (entails _ false (CNow (fun _ => True)))
    (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => both (S a) (S b) (csl_memory s')) wd)
    (run_rr (fork2 (proc 1) (proc 2)) (shared a b ctx c)) Pure.
Proof. apply af_ret_done, af_two_procs_rr_ret. Qed.

(** Process 1 alone in the pool, framed by process 2's finished region. *)
Local Lemma nd_tail_work1_ret a b ctx c (s : SSig) w : not_done w ->
  csl_memory s ≈ region 1 a ⊎ region 2 (S b) -> snd s = (ctx, S c) ->
  <( {interp_schedule_nd sh 1 ([denote_flow (proc 1);; Ret tt]%vector) None s}, w |=R
     AF ret {fun '(s', _) _ => both (S a) (S b) (csl_memory s')} )>.
Proof.
  ticl_normalize.
  intros Hw HM HS.
  rewrite interp_schedule_nd_select; cright; apply (an_brS (b:=true) _ _ Fin.F1); split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|inversion j].
  change ([denote_flow (proc 1);; Ret tt]%vector : pool sE Bn 1)
    with (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow (proc 1) >>= fun _ => Ret tt)).
  unfold proc; nd_prefix work_yield_fork_free.
  eapply (u_bind_r (b:=true) Q_A); [apply (work_af_framed_ret 1 2 a (S b) ctx (S c)); [exact Hw|apply frame_rel_both_1; [exact HM|exact HS]] |].
  intros [s2 r] w2 HP; apply frame_post_work in HP as (-> & HM2 & _ & ->).
  rewrite interp_nd_source_bind, interp_nd_source_yield.
  change (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow (CRet tt);; Ret tt))
    with (csl_pool (Vector.const (CRet tt) 1)).
  change (interp_schedule_nd sh 1 (csl_pool (Vector.const (CRet tt) 1)) None s2)
    with (run_nd_pool (Vector.const (CRet tt) 1) None s2).
  rewrite run_nd_pool_returns; cbn [Nat.iter].
  cright; apply (an_step (b:=true)); split; [csplit; auto with ticl|].
  close_ret; exact HM2.
Qed.

(** Every nondeterministic schedule finishes both processes with their incremented regions. *)
Local Theorem af_two_procs_nd_ret a b ctx c :
  <( {run_nd (fork2 (proc 1) (proc 2)) (shared a b ctx c)}, Pure |=R
     AF ret {fun '(s', _) _ => both (S a) (S b) (csl_memory s')} )>.
Proof.
  ticl_normalize.
  unfold fork2; rewrite run_nd_fork_bind.
  unfold denote.
  change ([denote_flow (proc 1);; Ret tt; denote_flow (proc 2);; Ret tt]%vector)
    with (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (proc 2) >>= fun _ => Ret tt)).
  unfold proc at 2; nd_prefix work_yield_fork_free.
  eapply (u_bind_r (b:=true) Q_A); [apply (work_af_framed_ret 2 1 b a ctx c); [constructor|apply frame_rel_shared_2] |].
  intros [s1 r] w1 HP; apply frame_post_work in HP as (-> & HM1 & HS1 & ->).
  assert (HM1' : csl_memory s1 ≈ region 1 a ⊎ region 2 (S b))
    by (eapply peq_trans; [exact HM1|apply pop_comm, region_disj; auto]).
  rewrite interp_nd_source_bind, interp_nd_source_yield.
  rewrite interp_schedule_nd_select; cright; apply (an_brS (b:=true) _ _ Fin.F1); split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|dependent destruction j; [|inversion j]].
  - (* child first *)
    change (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt);; Ret tt))
      with (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) @ child := (denote_flow (proc 1) >>= fun _ => Ret tt)).
    unfold proc; nd_prefix work_yield_fork_free.
    eapply (u_bind_r (b:=true) Q_A); [apply (work_af_framed_ret 1 2 a (S b) ctx (S c)); [constructor|apply frame_rel_both_1; [exact HM1'|exact HS1]] |].
    intros [s2 r] w2 HP; apply frame_post_work in HP as (-> & HM2 & _ & ->).
    rewrite interp_nd_source_bind, interp_nd_source_yield.
    change (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2)
      @ child := (denote_flow (CRet tt);; Ret tt))
      with (csl_pool (Vector.const (CRet tt) 2)).
    change (interp_schedule_nd sh 2 (csl_pool (Vector.const (CRet tt) 2)) None s2)
      with (run_nd_pool (Vector.const (CRet tt) 2) None s2).
    rewrite run_nd_pool_returns; cbn [Nat.iter].
    do 2 (cright; apply (an_step (b:=true)); split; [csplit; auto with ticl|]).
    close_ret; exact HM2.
  - (* parent first *)
    change (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt);; Ret tt))
      with (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt) >>= fun _ => Ret tt)).
    rewrite interp_nd_source_ret.
    rewrite (interp_schedule_nd_ret sh) by reflexivity.
    change ((([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := Ret tt) -- parent)
      with (vector_remove ([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) (Fin.FS Fin.F1)).
    rewrite vector_remove_tail, vector_remove_head.
    apply (nd_tail_work1_ret a b ctx c); [constructor|exact HM1'|exact HS1].
Qed.

(** Preserve the original eventual terminal claim for every schedule. *)
Theorem af_two_procs_nd a b ctx c :
  auc (entails _ false (CNow (fun _ => True)))
    (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => both (S a) (S b) (csl_memory s')) wd)
    (run_nd (fork2 (proc 1) (proc 2)) (shared a b ctx c)) Pure.
Proof. apply af_ret_done, af_two_procs_nd_ret. Qed.

(** Concrete round-robin result for initial cell values [3] and [5]. *)
Example af_rr_3_5 ctx :
  auc (entails _ false (CNow (fun _ => True)))
    (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => fst (csl_memory s') 1 = Some 4 /\ fst (csl_memory s') 2 = Some 6) wd)
    (run_rr (fork2 (proc 1) (proc 2)) (shared 3 5 ctx 0)) Pure.
Proof.
  eapply aur_done_mono; [|apply af_two_procs_rr].
  intros [s' []] _ HB; exact (both_lookup _ _ _ HB).
Qed.

(** Concrete nondeterministic result for initial cell values [3] and [5]. *)
Example af_nd_3_5 ctx :
  auc (entails _ false (CNow (fun _ => True)))
    (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => fst (csl_memory s') 1 = Some 4 /\ fst (csl_memory s') 2 = Some 6) wd)
    (run_nd (fork2 (proc 1) (proc 2)) (shared 3 5 ctx 0)) Pure.
Proof.
  eapply aur_done_mono; [|apply af_two_procs_nd].
  intros [s' []] _ HB; exact (both_lookup _ _ _ HB).
Qed.

Print Assumptions af_two_procs_rr.
