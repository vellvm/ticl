(** * Regression: two silently-writing processes joined through [CYield].

    [fork2 (wproc 1) (wproc 2)]: each process writes [1] into its own cell
    and yields.  Writes are silent, so the only visible steps are the
    scheduler's; exactly three of them precede the native return. Each write is proved
    on the process's own region and framed by the other one. *)

(** [run_rr_prefix]/[run_nd_prefix] expose the standalone write in a bind.
    [write_ret_framed] transports its native return through framing, and
    [anr_bind_r] consumes it without a visible step. [frame_post_write]
    recovers the joined memory, unchanged context/counter and old world.
    Three scheduler picks precede native return; its final value transition
    gives the original four-next terminal contracts below. *)
From Stdlib Require Import Fin Vector.
From Coinduction Require Import all.
From examples Require Import CSL.Frame.Shared.

(** Make one slot of a concrete two-slot pool a syntactic [replace] so the
    slot equations ([interp_rr_*], [run_rr_prefix], …) can fire. *)
Local Ltac focus_parent :=
  match goal with
  | |- context [[?X; ?Y]%vector] =>
      change ([X; Y]%vector) with (([X; Ret tt]%vector : pool sE Bn 2) @ parent := Y)
  end.
(** Expose the child slot as a pool replacement. *)
Local Ltac focus_child :=
  match goal with
  | |- context [[?X; ?Y]%vector] =>
      change ([X; Y]%vector) with (([Ret tt; Y]%vector : pool sE Bn 2) @ child := X)
  end.
(** Expose the only slot as a pool replacement. *)
Local Ltac focus_single :=
  match goal with
  | |- context [[?X]%vector] =>
      change ([X]%vector) with (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := X)
  end.
(** Reduce a concrete slot replacement back to its vector. *)
Local Ltac unfocus := cbn [Vector.replace caseS' parent child].

(** Finish a nondeterministic singleton pool whose return satisfies [Hpost]. *)
Local Ltac finish_nd_singleton Hpost :=
  focus_single; rewrite interp_nd_source_ret; unfocus;
  rewrite (interp_schedule_nd_ret sh) by reflexivity;
  rewrite vector_remove_head, (interp_schedule_nd_empty sh);
  apply ret_ret; [constructor|exact Hpost].



(** The frame of process [1] after process [2] wrote: the shared memory seen
    with region [1] first. *)
Lemma frame_rel_after_2 a (s : SSig) ctx c :
  csl_memory s ≈ region 2 1 ⊎ region 1 a -> snd s = (ctx, c) ->
  frame_rel (region 2 1) (own 1 a ctx c) s.
Proof.
  intros Hm Hs; apply frame_rel_both_1; [|exact Hs].
  eapply peq_trans; [exact Hm|apply pop_comm, region_disj; auto].
Qed.

(** Native return follows three round-robin scheduler steps. *)
Local Lemma an_two_procs_rr_ret a b ctx c :
  <[ {run_rr (fork2 (wproc 1) (wproc 2)) (shared a b ctx c)}, Pure |=
     AX (AX (AX ret {fun '(s', _) _ => both 1 1 (csl_memory s')})) ]>.
Proof.
  unfold fork2; rewrite run_rr_fork_bind; unfold denote.
  (* parent: write 2, yield *)
  focus_parent; unfold wproc at 2; rr_prefix write_yield_fork_free.
  eapply anr_bind_r; [apply (write_ret_framed 2 1 b a ctx c _ Pure); [constructor|apply frame_rel_shared_2]|].
  intros [s1 r] w1 HP; apply frame_post_write in HP as (-> & Hm1 & Hs1 & ->); unfocus.
  focus_parent; rewrite interp_rr_bind, interp_rr_yield.
  rewrite interp_schedule_rr_select; apply anr_step; split; [csplit; auto with ticl|].
  rewrite rr_pick_1_0; unfocus.
  (* child: write 1, yield *)
  focus_child; unfold wproc; rr_prefix write_yield_fork_free.
  eapply anr_bind_r; [apply (write_ret_framed 1 2 a 1 ctx c _ Pure); [constructor|apply frame_rel_after_2; assumption]|].
  intros [s2 r] w2 HP; apply frame_post_write in HP as (-> & Hm2 & _ & ->); unfocus.
  focus_child; rewrite interp_rr_bind, interp_rr_yield.
  rewrite interp_schedule_rr_select; apply anr_step; split; [csplit; auto with ticl|].
  rewrite rr_pick_1_1; unfocus.
  (* parent returns *)
  focus_parent; rewrite interp_rr_ret; unfocus.
  rewrite (interp_schedule_rr_ret sh) by reflexivity.
  unfold parent; rewrite vector_remove_tail, vector_remove_head.
  rewrite interp_schedule_rr_select; apply anr_step; split; [csplit; auto with ticl|].
  rewrite rr_pick_0.
  (* child returns *)
  focus_single; rewrite interp_rr_ret; unfocus.
  rewrite (interp_schedule_rr_ret sh) by reflexivity.
  rewrite vector_remove_head, (interp_schedule_rr_empty sh).
  apply ret_ret; [constructor|exact Hm2].
Qed.

(** Nondeterministic scheduler: every pick order reaches the terminal
    postcondition at the same four-transition depth. *)
Local Ltac nd_select :=
  rewrite (interp_schedule_nd_select sh); apply (anr_brS _ _ Fin.F1); split; [csplit; auto with ticl|].
(** Split a nonempty finite choice into its head and remaining indices. *)
Local Ltac fin_case := let j := fresh "j" in intro j; pattern j; apply Fin.caseS'; clear j.
(** Eliminate an index of the empty finite type. *)
Local Ltac fin_none := let j := fresh "j" in intro j; inversion j.
(** Enumerate the two possible scheduler choices. *)
Local Ltac fin2_cases := fin_case; [|fin_case; [|fin_none]].
(** Enumerate the only remaining scheduler choice. *)
Local Ltac fin1_case := fin_case; [|fin_none].

(** Consequence under four [AX] layers. *)
Lemma ax4_done_mono {X} (t : ctreeW (CSLObs (nat * nat)) Bn X) w
  (P Q : X -> World (writerE (CSLObs (nat * nat))) -> Prop) :
  (forall x w, P x w -> Q x w) ->
  anc (entailsL X (CNow (fun _ => True)))
    (anc (entailsL X (CNow (fun _ => True)))
      (anc (entailsL X (CNow (fun _ => True)))
        (anc (entailsL X (CNow (fun _ => True))) (fun _ wd => done_with P wd)))) t w ->
  anc (entailsL X (CNow (fun _ => True)))
    (anc (entailsL X (CNow (fun _ => True)))
      (anc (entailsL X (CNow (fun _ => True)))
        (anc (entailsL X (CNow (fun _ => True))) (fun _ wd => done_with Q wd)))) t w.
Proof.
  intros HPQ; apply anc_mono_r; intros t1 w1.
  apply anc_mono_r; intros t2 w2.
  apply anc_mono_r; intros t3 w3.
  apply anc_mono_r; intros t4 w4.
  apply done_with_mono; exact HPQ.
Qed.
(** Native return follows three nondeterministic scheduler steps. *)
Local Lemma an_two_procs_nd_ret a b ctx c :
  <[ {run_nd (fork2 (wproc 1) (wproc 2)) (shared a b ctx c)}, Pure |=
     AX (AX (AX ret {fun '(s', _) _ => both 1 1 (csl_memory s')})) ]>.
Proof.
  unfold fork2; rewrite run_nd_fork_bind; unfold denote.
  (* parent: write 2, yield *)
  focus_parent; unfold wproc at 2; nd_prefix write_yield_fork_free.
  eapply anr_bind_r; [apply (write_ret_framed 2 1 b a ctx c _ Pure); [constructor|apply frame_rel_shared_2]|].
  intros [s1 r] w1 HP; apply frame_post_write in HP as (-> & Hm1 & Hs1 & ->); unfocus.
  focus_parent; rewrite interp_nd_source_bind, interp_nd_source_yield.
  nd_select; fin2_cases; unfocus.
  - (* child first: write 1, yield *)
    focus_child; unfold wproc; nd_prefix write_yield_fork_free.
    eapply anr_bind_r; [apply (write_ret_framed 1 2 a 1 ctx c _ Pure); [constructor|apply frame_rel_after_2; assumption]|].
    intros [s2 r] w2 HP; apply frame_post_write in HP as (-> & Hm2 & _ & ->); unfocus.
    focus_child; rewrite interp_nd_source_bind, interp_nd_source_yield.
    nd_select; fin2_cases; unfocus.
    + (* child returns, then parent *)
      focus_child; rewrite interp_nd_source_ret; unfocus.
      rewrite (interp_schedule_nd_ret sh) by reflexivity.
      unfold child; rewrite vector_remove_head.
      nd_select; fin1_case.
      finish_nd_singleton Hm2.
    + (* parent returns, then child *)
      focus_parent; rewrite interp_nd_source_ret; unfocus.
      rewrite (interp_schedule_nd_ret sh) by reflexivity.
      unfold parent; rewrite vector_remove_tail, vector_remove_head.
      nd_select; fin1_case.
      finish_nd_singleton Hm2.
  - (* parent first: returns; then the child writes, yields, returns *)
    focus_parent; rewrite interp_nd_source_ret; unfocus.
    rewrite (interp_schedule_nd_ret sh) by reflexivity.
    unfold parent; rewrite vector_remove_tail, vector_remove_head.
    nd_select; fin1_case.
    focus_single; unfold wproc; nd_prefix write_yield_fork_free.
    eapply anr_bind_r; [apply (write_ret_framed 1 2 a 1 ctx c _ Pure); [constructor|apply frame_rel_after_2; assumption]|].
    intros [s2 r] w2 HP; apply frame_post_write in HP as (-> & Hm2 & _ & ->); unfocus.
    focus_single; rewrite interp_nd_source_bind, interp_nd_source_yield.
    nd_select; fin1_case.
    finish_nd_singleton Hm2.
Qed.

(** Preserve the original four-transition terminal properties. *)
Theorem an_two_procs_rr a b ctx c :
  anc (entailsL (SSig * unit) (CNow (fun _ => True)))
    (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
      (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
        (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
          (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => both 1 1 (csl_memory s')) wd))))
    (run_rr (fork2 (wproc 1) (wproc 2)) (shared a b ctx c)) Pure.
Proof.
  eapply anc_mono_r; [intros t1 w1|exact (an_two_procs_rr_ret a b ctx c)].
  apply anc_mono_r; intros t2 w2.
  apply anc_mono_r; intros t3 w3.
  intros H; apply ret_done_next; apply ticlr_ret; exact H.
Qed.

Theorem an_two_procs_nd a b ctx c :
  anc (entailsL (SSig * unit) (CNow (fun _ => True)))
    (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
      (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
        (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
          (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => both 1 1 (csl_memory s')) wd))))
    (run_nd (fork2 (wproc 1) (wproc 2)) (shared a b ctx c)) Pure.
Proof.
  eapply anc_mono_r; [intros t1 w1|exact (an_two_procs_nd_ret a b ctx c)].
  apply anc_mono_r; intros t2 w2.
  apply anc_mono_r; intros t3 w3.
  intros H; apply ret_done_next; apply ticlr_ret; exact H.
Qed.

(** ** Closed terms *)


(** Instantiate the round-robin result and expose both final cell values. *)
Example an_rr_3_5 ctx :
  anc (entailsL (SSig * unit) (CNow (fun _ => True)))
    (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
      (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
        (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
          (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => fst (csl_memory s') 1 = Some 1 /\ fst (csl_memory s') 2 = Some 1) wd))))
    (run_rr (fork2 (wproc 1) (wproc 2)) (shared 3 5 ctx 0)) Pure.
Proof.
  eapply ax4_done_mono; [|apply an_two_procs_rr].
  intros [s' _] _ H; apply both_lookup, H.
Qed.

(** Instantiate the nondeterministic result and expose both final cell values. *)
Example an_nd_3_5 ctx :
  anc (entailsL (SSig * unit) (CNow (fun _ => True)))
    (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
      (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
        (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
          (fun _ wd => done_with (X := SSig * unit) (fun '(s', _) _ => fst (csl_memory s') 1 = Some 1 /\ fst (csl_memory s') 2 = Some 1) wd))))
    (run_nd (fork2 (wproc 1) (wproc 2)) (shared 3 5 ctx 0)) Pure.
Proof.
  eapply ax4_done_mono; [|apply an_two_procs_nd].
  intros [s' _] _ H; apply both_lookup, H.
Qed.

(** ** Negative control: without region [1] the child's write faults. *)

(** The parent's write and yield are silent; the first scheduler step hands
    the child a heap without cell [1], where [CWrite 1 1] is [Stuck]. *)
Lemma wproc_own_2_stuck b ctx c :
  run_rr (fork2 (wproc 1) (wproc 2)) (own 2 b ctx c) ~
  (Step Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  unfold fork2; rewrite run_rr_fork_bind; unfold denote.
  focus_parent; unfold wproc at 2; rr_prefix write_yield_fork_free.
  rewrite instr_flow_write_single by (cbn; discriminate).
  rewrite bind_ret_l; cbn [Vector.replace caseS' parent own region csl_memory fst snd].
  focus_parent; rewrite interp_rr_bind, interp_rr_yield, interp_schedule_rr_select, rr_pick_1_0.
  apply sb_step; unfocus.
  focus_child; unfold wproc; rewrite interp_rr_bind.
  rewrite interp_rr_write_missing; reflexivity.
Qed.

Goal forall b ctx c,
  ~ anc (entailsL (SSig * unit) (CNow (fun _ => True)))
    (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
      (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
        (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
          (fun _ wd => done_with (fun (_ : SSig * unit) _ => True) wd))))
    (run_rr (fork2 (wproc 1) (wproc 2)) (own 2 b ctx c)) Pure.
Proof.
  intros b ctx c H.
  rewrite wproc_own_2_stuck in H.
  destruct H as (_ & _ & H).
  specialize (H Stuck Pure ltac:(apply ktrans_step; split; [reflexivity|split; [reflexivity|constructor]])).
  destruct H as (_ & Hs & _); exact (can_step_stuck _ Hs).
Qed.

(** A permitted child selection faults without region [1], refuting universal next. *)
Lemma wproc_own_2_no_ax4_nd b ctx c :
  ~ anc (entailsL (SSig * unit) (CNow (fun _ => True)))
    (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
      (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
        (anc (entailsL (SSig * unit) (CNow (fun _ => True)))
          (fun _ wd => done_with (fun (_ : SSig * unit) _ => True) wd))))
    (run_nd (fork2 (wproc 1) (wproc 2)) (own 2 b ctx c)) Pure.
Proof.
  intro H.
  unfold fork2 in H; rewrite run_nd_fork_bind in H; unfold denote in H.
  change ([denote_flow (wproc 1);; Ret tt; denote_flow (wproc 2);; Ret tt]%vector)
    with (([denote_flow (wproc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2)
      @ parent := (denote_flow (wproc 2) >>= fun _ => Ret tt)) in H.
  unfold wproc at 2 in H.
  rewrite interp_nd_source_bind, run_nd_prefix in H by apply write_yield_fork_free.
  rewrite instr_flow_write_single in H by (cbn; discriminate).
  rewrite bind_ret_l in H.
  cbn [Vector.replace caseS' parent own region csl_memory fst snd] in H.
  change ([denote_flow (wproc 1);; Ret tt; denote_flow (CBind CYield (fun _ => CRet tt));; Ret tt]%vector)
    with (([denote_flow (wproc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2)
      @ parent := (denote_flow (CBind CYield (fun _ => CRet tt)) >>= fun _ => Ret tt)) in H.
  rewrite interp_nd_source_bind, interp_nd_source_yield, interp_schedule_nd_select in H.
  destruct H as (_ & _ & H).
  specialize (H _ Pure ltac:(apply ktrans_brS; exists Fin.F1; split; [reflexivity|split; [reflexivity|constructor]])).
  cbn [Vector.replace caseS' parent] in H.
  change ([denote_flow (wproc 1);; Ret tt; denote_flow (CRet tt);; Ret tt]%vector)
    with (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2)
      @ child := (denote_flow (wproc 1) >>= fun _ => Ret tt)) in H.
  unfold wproc in H; rewrite interp_nd_source_bind in H.
  rewrite interp_nd_source_write_missing in H by reflexivity.
  destruct H as (_ & Hs & _); exact (can_step_stuck _ Hs).
Qed.

Print Assumptions an_two_procs_rr.
