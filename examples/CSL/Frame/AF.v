(** * Regression: two cooperating processes, [AF] under both schedulers.

    [fork2 (proc 1) (proc 2)]: each process reads, increments and emits its
    own cell, then yields. Each process's native [AF ret] fact is proved on its
    own region and framed by the other's ([work_af_framed_ret]); the cooperative prefix
    equation ([run_rr_prefix]/[run_nd_prefix]) runs the focused process alone,
    then [CYield] rejoins the pool.  Both processes finish and the heap is the
    join of the two incremented regions. *)
From Stdlib Require Import Fin Vector.
From Coinduction Require Import all.
From examples Require Import CSL.Frame.Shared.

(** Round-robin execution finishes both processes with their incremented regions. *)
Local Theorem af_two_procs_rr_ret a b ctx c :
  <[ {run_rr (fork2 (proc 1) (proc 2)) (shared a b ctx c)}, Pure |=
     AF ret {fun '(s', _) _ => both (S a) (S b) (csl_memory s')} ]>.
Proof.
  unfold fork2; rewrite run_rr_fork_bind.
  unfold denote.
  change ([denote_flow (proc 1);; Ret tt; denote_flow (proc 2);; Ret tt]%vector)
    with (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (proc 2) >>= fun _ => Ret tt)).
  unfold proc at 2; rr_prefix work_yield_fork_free.
  eapply aur_bind_r; [apply (work_af_framed_ret 2 1 b a ctx c); [constructor|apply frame_rel_shared_2] |].
  intros [s1 r] w1 HP; apply frame_post_work in HP as (-> & HM1 & HS1 & ->).
  rewrite interp_rr_bind, interp_rr_yield.
  rewrite interp_schedule_rr_select; cright; apply anr_step; split; [csplit; auto with ticl|].
  rewrite rr_pick_1_0.
  change (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt);; Ret tt))
    with (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) @ child := (denote_flow (proc 1) >>= fun _ => Ret tt)).
  unfold proc; rr_prefix work_yield_fork_free.
  eapply aur_bind_r; [apply (work_af_framed_ret 1 2 a (S b) ctx (S c)); [constructor|apply frame_rel_both_1; [|exact HS1]] |].
  { eapply peq_trans; [exact HM1|apply pop_comm, region_disj; auto]. }
  intros [s2 r] w2 HP; apply frame_post_work in HP as (-> & HM2 & _ & ->).
  rewrite interp_rr_bind, interp_rr_yield.
  rewrite interp_schedule_rr_select; cright; apply anr_step; split; [csplit; auto with ticl|].
  rewrite rr_pick_1_1.
  change (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) @ child := (denote_flow (CRet tt);; Ret tt))
    with (([denote_flow (CRet tt);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt) >>= fun _ => Ret tt)).
  rewrite interp_rr_ret.
  rewrite (interp_schedule_rr_ret sh) by reflexivity.
  change ((([denote_flow (CRet tt);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := Ret tt) -- parent)
    with (vector_remove ([denote_flow (CRet tt);; Ret tt; Ret tt]%vector : pool sE Bn 2) (Fin.FS Fin.F1)).
  rewrite vector_remove_tail, vector_remove_head.
  rewrite interp_schedule_rr_select; cright; apply anr_step; split; [csplit; auto with ticl|].
  rewrite rr_pick_0.
  change ([denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 1)
    with (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow (CRet tt) >>= fun _ => Ret tt)).
  rewrite interp_rr_ret.
  rewrite (interp_schedule_rr_ret sh) by reflexivity.
  rewrite (interp_schedule_rr_empty sh).
  close_ret.
  exact HM2.
Qed.

(** Preserve the original eventual terminal claim. *)
Theorem af_two_procs_rr a b ctx c :
  auc (entailsL _ (CNow (fun _ => True)))
    (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => both (S a) (S b) (csl_memory s')) wd)
    (run_rr (fork2 (proc 1) (proc 2)) (shared a b ctx c)) Pure.
Proof. apply af_ret_done, af_two_procs_rr_ret. Qed.

(** A singleton pool with a returning process finishes with the current heap. *)
Local Lemma nd_tail1_ret a b (s : SSig) w : not_done w -> both (S a) (S b) (csl_memory s) ->
  <[ {interp_schedule_nd sh 1 ([denote_flow (CRet tt);; Ret tt]%vector) None s}, w |=
     AX AF ret {fun '(s', _) _ => both (S a) (S b) (csl_memory s')} ]>.
Proof.
  intros Hw HB.
  rewrite interp_schedule_nd_select; apply (anr_brS _ _ Fin.F1); split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|inversion j].
  change ([denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 1)
    with (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow (CRet tt) >>= fun _ => Ret tt)).
  rewrite interp_nd_source_ret.
  rewrite (interp_schedule_nd_ret sh) by reflexivity.
  rewrite (interp_schedule_nd_empty sh).
  close_ret; exact HB.
Qed.

Local Lemma nd_tail1 a b (s : SSig) w : not_done w -> both (S a) (S b) (csl_memory s) ->
  anc (entailsL _ (CNow (fun _ => True)))
    (auc (entailsL _ (CNow (fun _ => True)))
      (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => both (S a) (S b) (csl_memory s')) wd))
    (interp_schedule_nd sh 1 ([denote_flow (CRet tt);; Ret tt]%vector) None s) w.
Proof.
  intros Hw HB; eapply anc_mono_r; [intros t w' H; apply af_ret_done; exact H|].
  pose proof (nd_tail1_ret a b s w Hw HB) as Hnative.
  rewrite unfold_entailsR in Hnative; exact Hnative.
Qed.

(** Either removal order of two returning processes preserves the final heap. *)
Local Lemma nd_tail2_ret a b (s : SSig) w : not_done w -> both (S a) (S b) (csl_memory s) ->
  <[ {interp_schedule_nd sh 2 ([denote_flow (CRet tt);; Ret tt; denote_flow (CRet tt);; Ret tt]%vector) None s}, w |=
     AX AF ret {fun '(s', _) _ => both (S a) (S b) (csl_memory s')} ]>.
Proof.
  intros Hw HB.
  rewrite interp_schedule_nd_select; apply (anr_brS _ _ Fin.F1); split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|dependent destruction j; [|inversion j]].
  - change ([denote_flow (CRet tt);; Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2)
      with (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) @ child := (denote_flow (CRet tt) >>= fun _ => Ret tt)).
    rewrite interp_nd_source_ret.
    rewrite (interp_schedule_nd_ret sh) by reflexivity.
    change ((([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) @ child := Ret tt) -- child)
      with (vector_remove ([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) Fin.F1).
    rewrite vector_remove_head.
    cright; apply nd_tail1_ret; auto.
  - change ([denote_flow (CRet tt);; Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2)
      with (([denote_flow (CRet tt);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt) >>= fun _ => Ret tt)).
    rewrite interp_nd_source_ret.
    rewrite (interp_schedule_nd_ret sh) by reflexivity.
    change ((([denote_flow (CRet tt);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := Ret tt) -- parent)
      with (vector_remove ([denote_flow (CRet tt);; Ret tt; Ret tt]%vector : pool sE Bn 2) (Fin.FS Fin.F1)).
    rewrite vector_remove_tail, vector_remove_head.
    cright; apply nd_tail1_ret; auto.
Qed.

Local Lemma nd_tail2 a b (s : SSig) w : not_done w -> both (S a) (S b) (csl_memory s) ->
  anc (entailsL _ (CNow (fun _ => True)))
    (auc (entailsL _ (CNow (fun _ => True)))
      (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => both (S a) (S b) (csl_memory s')) wd))
    (interp_schedule_nd sh 2 ([denote_flow (CRet tt);; Ret tt; denote_flow (CRet tt);; Ret tt]%vector) None s) w.
Proof.
  intros Hw HB; eapply anc_mono_r; [intros t w' H; apply af_ret_done; exact H|].
  pose proof (nd_tail2_ret a b s w Hw HB) as Hnative.
  rewrite unfold_entailsR in Hnative; exact Hnative.
Qed.

(** Process 1 alone in the pool, framed by process 2's finished region. *)
Local Lemma nd_tail_work1_ret a b ctx c (s : SSig) w : not_done w ->
  csl_memory s ≈ region 1 a ⊎ region 2 (S b) -> snd s = (ctx, S c) ->
  <[ {interp_schedule_nd sh 1 ([denote_flow (proc 1);; Ret tt]%vector) None s}, w |=
     AF ret {fun '(s', _) _ => both (S a) (S b) (csl_memory s')} ]>.
Proof.
  intros Hw HM HS.
  rewrite interp_schedule_nd_select; cright; apply (anr_brS _ _ Fin.F1); split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|inversion j].
  change ([denote_flow (proc 1);; Ret tt]%vector : pool sE Bn 1)
    with (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow (proc 1) >>= fun _ => Ret tt)).
  unfold proc; nd_prefix work_yield_fork_free.
  eapply aur_bind_r; [apply (work_af_framed_ret 1 2 a (S b) ctx (S c)); [exact Hw|apply frame_rel_both_1; [exact HM|exact HS]] |].
  intros [s2 r] w2 HP; apply frame_post_work in HP as (-> & HM2 & _ & ->).
  rewrite interp_nd_source_bind, interp_nd_source_yield.
  change (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow (CRet tt);; Ret tt))
    with ([denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 1).
  cright; apply nd_tail1_ret; [constructor|exact HM2].
Qed.

Local Lemma nd_tail_work1 a b ctx c (s : SSig) w : not_done w ->
  csl_memory s ≈ region 1 a ⊎ region 2 (S b) -> snd s = (ctx, S c) ->
  auc (entailsL _ (CNow (fun _ => True)))
    (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => both (S a) (S b) (csl_memory s')) wd)
    (interp_schedule_nd sh 1 ([denote_flow (proc 1);; Ret tt]%vector) None s) w.
Proof. intros Hw HM HS; apply af_ret_done; apply (nd_tail_work1_ret a b ctx c); assumption. Qed.

(** Every nondeterministic schedule finishes both processes with their incremented regions. *)
Local Theorem af_two_procs_nd_ret a b ctx c :
  <[ {run_nd (fork2 (proc 1) (proc 2)) (shared a b ctx c)}, Pure |=
     AF ret {fun '(s', _) _ => both (S a) (S b) (csl_memory s')} ]>.
Proof.
  unfold fork2; rewrite run_nd_fork_bind.
  unfold denote.
  change ([denote_flow (proc 1);; Ret tt; denote_flow (proc 2);; Ret tt]%vector)
    with (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (proc 2) >>= fun _ => Ret tt)).
  unfold proc at 2; nd_prefix work_yield_fork_free.
  eapply aur_bind_r; [apply (work_af_framed_ret 2 1 b a ctx c); [constructor|apply frame_rel_shared_2] |].
  intros [s1 r] w1 HP; apply frame_post_work in HP as (-> & HM1 & HS1 & ->).
  assert (HM1' : csl_memory s1 ≈ region 1 a ⊎ region 2 (S b))
    by (eapply peq_trans; [exact HM1|apply pop_comm, region_disj; auto]).
  rewrite interp_nd_source_bind, interp_nd_source_yield.
  rewrite interp_schedule_nd_select; cright; apply (anr_brS _ _ Fin.F1); split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|dependent destruction j; [|inversion j]].
  - (* child first *)
    change (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt);; Ret tt))
      with (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) @ child := (denote_flow (proc 1) >>= fun _ => Ret tt)).
    unfold proc; nd_prefix work_yield_fork_free.
    eapply aur_bind_r; [apply (work_af_framed_ret 1 2 a (S b) ctx (S c)); [constructor|apply frame_rel_both_1; [exact HM1'|exact HS1]] |].
    intros [s2 r] w2 HP; apply frame_post_work in HP as (-> & HM2 & _ & ->).
    rewrite interp_nd_source_bind, interp_nd_source_yield.
    change (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) @ child := (denote_flow (CRet tt);; Ret tt))
      with ([denote_flow (CRet tt);; Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2).
    cright; apply nd_tail2_ret; [constructor|exact HM2].
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
  auc (entailsL _ (CNow (fun _ => True)))
    (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => both (S a) (S b) (csl_memory s')) wd)
    (run_nd (fork2 (proc 1) (proc 2)) (shared a b ctx c)) Pure.
Proof. apply af_ret_done, af_two_procs_nd_ret. Qed.

(** Concrete round-robin result for initial cell values [3] and [5]. *)
Example af_rr_3_5 ctx :
  auc (entailsL _ (CNow (fun _ => True)))
    (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => fst (csl_memory s') 1 = Some 4 /\ fst (csl_memory s') 2 = Some 6) wd)
    (run_rr (fork2 (proc 1) (proc 2)) (shared 3 5 ctx 0)) Pure.
Proof.
  eapply aur_done_mono; [|apply af_two_procs_rr].
  intros [s' []] _ HB; exact (both_lookup _ _ _ HB).
Qed.

(** Concrete nondeterministic result for initial cell values [3] and [5]. *)
Example af_nd_3_5 ctx :
  auc (entailsL _ (CNow (fun _ => True)))
    (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => fst (csl_memory s') 1 = Some 4 /\ fst (csl_memory s') 2 = Some 6) wd)
    (run_nd (fork2 (proc 1) (proc 2)) (shared 3 5 ctx 0)) Pure.
Proof.
  eapply aur_done_mono; [|apply af_two_procs_nd].
  intros [s' []] _ HB; exact (both_lookup _ _ _ HB).
Qed.

Print Assumptions af_two_procs_rr.
