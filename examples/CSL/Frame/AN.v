(** * Regression: two silently-writing processes joined through [CYield].

    [fork2 (wproc 1) (wproc 2)]: each process writes [1] into its own cell
    and yields.  Writes are silent, so the only visible steps are the
    scheduler's; exactly three of them precede [done].  Each write is proved
    on the process's own region and framed by the other one. *)

(** Round-robin retains the standalone frame proof through [run_rr_prefix].
    ND uses [OwnedAN.write_safe_split] for the components' owned next step,
    [OwnedAN.four_raw] for the erased clock, and [fork_ticlr_erasure] with a
    result-setoid-proper final predicate.  The missing-child-region RR
    negative control remains below. *)
From Stdlib Require Import Fin Vector Relations.
From Coinduction Require Import all.
From examples Require Import CSL.Frame.Shared.
From TICL Require Import Lang.CoCSL.Separation.

(** Make one slot of a concrete two-slot pool a syntactic [replace] so the
    slot equations ([interp_rr_*], [run_rr_prefix], …) can fire. *)
Ltac focus_parent :=
  match goal with
  | |- context [[?X; ?Y]%vector] =>
      change ([X; Y]%vector) with (([X; Ret tt]%vector : pool sE Bn 2) @ parent := Y)
  end.
(** Expose the child slot as a pool replacement. *)
Ltac focus_child :=
  match goal with
  | |- context [[?X; ?Y]%vector] =>
      change ([X; Y]%vector) with (([Ret tt; Y]%vector : pool sE Bn 2) @ child := X)
  end.
(** Expose the only slot as a pool replacement. *)
Ltac focus_single :=
  match goal with
  | |- context [[?X]%vector] =>
      change ([X]%vector) with (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := X)
  end.
(** Reduce a concrete slot replacement back to its vector. *)
Ltac unfocus := cbn [Vector.replace caseS' parent child].


(** The frame of process [1] after process [2] wrote: the shared memory seen
    with region [1] first. *)
Lemma frame_rel_after_2 a (s : SSig) ctx c :
  csl_memory s ≈ region 2 1 ⊎ region 1 a -> snd s = (ctx, c) ->
  frame_rel (region 2 1) (own 1 a ctx c) s.
Proof.
  intros Hm Hs; apply frame_rel_both_1; [|exact Hs].
  eapply peq_trans; [exact Hm|apply pop_comm, region_disj; auto].
Qed.

(** Both silently-writing processes finish after four round-robin steps. *)
Theorem an_two_procs_rr a b ctx c :
  <[ {run_rr (fork2 (wproc 1) (wproc 2)) (shared a b ctx c)}, Pure |=
     AX (AX (AX (AX done {fun '(s', _) _ => both 1 1 (csl_memory s')}))) ]>.
Proof.
  unfold fork2; rewrite run_rr_fork_bind; unfold denote.
  (* parent: write 2, yield *)
  focus_parent; unfold wproc at 2; rr_prefix write_yield_fork_free.
  eapply anr_bind_r; [apply (write_ax_framed 2 1 b a ctx c _ Pure); [constructor|apply frame_rel_shared_2]|].
  intros [s1 r] w1 HP; apply frame_post_write in HP as (-> & Hm1 & Hs1 & ->); unfocus.
  focus_parent; rewrite interp_rr_bind, interp_rr_yield.
  rewrite interp_schedule_rr_select; apply anr_step; split; [csplit; auto with ticl|].
  rewrite rr_pick_1_0; unfocus.
  (* child: write 1, yield *)
  focus_child; unfold wproc; rr_prefix write_yield_fork_free.
  eapply anr_bind_r; [apply (write_ax_framed 1 2 a 1 ctx c _ Pure); [constructor|apply frame_rel_after_2; assumption]|].
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
  apply axr_ret; [constructor|exact Hm2].
Qed.

(** ** The owned clock: writes, yields and removals are silent; each
    selection contributes one raw step, followed by the final value step. *)
Module OwnedAN.
Import VectorNotations.

Definition tY : thread sE Bn := Vis (inl1 Yield : CEff unit) (fun _ => Ret tt).
Definition tW i : thread sE Bn :=
  Vis (inr1 (inr1 (inl1 (HWrite i 1))) : CEff unit) (fun _ => tY).
Definition wrote d i addr :=
  set_heap d i (upd (fst (oc_heap d i)) addr 1, snd (oc_heap d i)).
Definition final (r : SSig * unit) : Prop := both 1 1 (csl_memory (fst r)).

Lemma write_head i : denote (wproc i) ≅ tW i.
Proof.
  unfold denote, wproc; rewrite source_raw_bind, source_raw_write_head.
  unfold tW; step; constructor; intros [].
  unfold source_yield, CTree.trigger, tY.
  rewrite !bind_bind, bind_vis.
  apply vis_equ_node; intros []; rewrite !bind_ret_l; reflexivity.
Qed.

Lemma admission a b ctx c :
  admissible (wproc 1) (wproc 2) (region 1 a) (region 2 b) ctx c.
Proof.
  apply admissible_intro.
  - apply managed_wf_preallocated.
  - apply managed_wf_preallocated.
  - apply region_disj; discriminate.
  - cbn; repeat split; auto.
  - cbn; repeat split; auto.
  - cbn; repeat split; discriminate.
  - cbn; repeat split; discriminate.
Qed.

Lemma final_proper : Proper (owned_result_rel ==> iff) final.
Proof.
  intros [s x] [s' x'] (_ & _ & Hm).
  change (csl_memory s ≈ region 1 1 ⊎ region 2 1 <->
    csl_memory s' ≈ region 1 1 ⊎ region 2 1); split; intro H.
  - eapply peq_trans; [apply peq_sym; exact Hm|exact H].
  - eapply peq_trans; [exact Hm|exact H].
Qed.

Lemma erase_write d n v g j addr k :
  oc_pool d = mk_pool (S n) v g (Some j) ->
  headed (v $ j) (Vis (inr1 (inr1 (inl1 (HWrite addr 1))) : CEff unit) k) ->
  fst (oc_heap d (g $ j)) addr <> None ->
  erase_owned (instrument_owned d) ~
  erase_owned (instrument_owned
    (set_pool (wrote d (g $ j) addr) (mk_pool (S n) (v @ j := k tt) g (Some j)))).
Proof.
  intros Hp Hhead Hcell; apply erase_owned_silent_path, rt_step.
  exists (act (g $ j) OAWrite); split; [|reflexivity].
  unfold owned_step; rewrite Hp; cbn -[focus_step].
  right; right; right; right.
  exists unit, (inl1 (HWrite addr 1) : sE unit), k, OAWrite, tt, (wrote d (g $ j) addr).
  split; [exact Hhead|split; [|split; reflexivity]].
  cbn [prim_step heap_prim]; destruct (fst (oc_heap d (g $ j)) addr);
    [reflexivity|contradiction].
Qed.

Lemma erase_yield d n v g j k :
  oc_pool d = mk_pool (S n) v g (Some j) ->
  headed (v $ j) (Vis (inl1 Yield : CEff unit) k) ->
  erase_owned (instrument_owned d) ~
  erase_owned (instrument_owned (set_pool d (mk_pool (S n) (v @ j := k tt) g None))).
Proof.
  intros Hp Hhead; apply erase_owned_silent_path, rt_step.
  exists (act (g $ j) OAYield); split; [|reflexivity].
  unfold owned_step; rewrite Hp; cbn -[focus_step].
  right; left; exists k; split; [exact Hhead|split; reflexivity].
Qed.

Lemma erase_return d n v g j :
  oc_pool d = mk_pool (S n) v g (Some j) -> headed (v $ j) (Ret tt) ->
  erase_owned (instrument_owned d) ~
  erase_owned (instrument_owned (set_pool d (mk_pool n (v -- j) (g -- j) None))).
Proof.
  intros Hp Hhead; apply erase_owned_silent_path, rt_step.
  exists (act (g $ j) OAReturn); split; [|reflexivity].
  unfold owned_step; rewrite Hp; cbn -[focus_step].
  right; right; right; left; split; [exact Hhead|split; reflexivity].
Qed.

Lemma finish_one d i w : not_done w -> both 1 1 (joined_heap d) ->
  <[ {erase_owned (instrument_owned (set_pool d (mk_pool 1 [Ret tt] [i] None)))}, w |=
     AX (AX done {fun r _ => final r}) ]>.
Proof.
  intros Hw HB; rewrite erase_owned_select.
  apply (anr_brS _ _ Fin.F1); split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|inversion j].
  erewrite erase_return with (n := 0) (v := [Ret tt]) (g := [i]) (j := Fin.F1);
    [|reflexivity|exists 0; reflexivity].
  rewrite !vector_remove_head, erase_owned_terminal by reflexivity.
  apply axr_ret; [exact Hw|exact HB].
Qed.

Lemma finish_two d w : not_done w -> both 1 1 (joined_heap d) ->
  <[ {erase_owned (instrument_owned
       (set_pool d (mk_pool 2 [Ret tt; Ret tt] [Child; Parent] None)))}, w |=
     AX (AX (AX done {fun r _ => final r})) ]>.
Proof.
  intros Hw HB; rewrite erase_owned_select.
  apply (anr_brS _ _ Fin.F1); split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|dependent destruction j; [|inversion j]].
  - erewrite erase_return with (n := 1) (v := [Ret tt; Ret tt])
      (g := [Child; Parent]) (j := Fin.F1);
      [|reflexivity|exists 0; reflexivity].
    rewrite !vector_remove_head; apply finish_one; assumption.
  - erewrite erase_return with (n := 1) (v := [Ret tt; Ret tt])
      (g := [Child; Parent]) (j := Fin.FS Fin.F1);
      [|reflexivity|exists 0; reflexivity].
    rewrite !vector_remove_tail, !vector_remove_head; apply finish_one; assumption.
Qed.

Lemma finish_child a d w :
  oc_heap d Child = region 1 a -> oc_heap d Parent ≈ region 2 1 -> not_done w ->
  <[ {erase_owned (instrument_owned
       (set_pool d (mk_pool 1 [denote (wproc 1)] [Child] None)))}, w |=
     AX (AX (AX done {fun r _ => final r})) ]>.
Proof.
  intros HC HP Hw; rewrite erase_owned_select.
  apply (anr_brS _ _ Fin.F1); split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|inversion j].
  erewrite erase_write with (n := 0) (v := [denote (wproc 1)])
    (g := [Child]) (j := Fin.F1) (addr := 1) (k := fun _ => tY);
    [|reflexivity|exists 0; apply write_head|].
  2:{ change (fst (oc_heap d Child) 1 <> None); rewrite HC; discriminate. }
  erewrite erase_yield with (n := 0) (v := [tY]) (g := [Child])
    (j := Fin.F1) (k := fun _ => Ret tt);
    [|reflexivity|exists 0; reflexivity].
  change (<[ {erase_owned (instrument_owned
    (set_pool (wrote d Child 1) (mk_pool 1 [Ret tt] [Child] None)))}, w |=
    AX (AX done {fun r _ => final r}) ]>).
  apply finish_one; [exact Hw|].
  unfold joined_heap, wrote; cbn [set_heap oc_heap side_upd side_eqb].
  apply pop_resp; [rewrite HC; apply upd_region|exact HP].
Qed.

Lemma pair_raw a b d w :
  oc_heap d Child = region 1 a -> oc_heap d Parent = region 2 b -> not_done w ->
  <[ {erase_owned (instrument_owned (set_pool d
       (mk_pool 2 [denote (wproc 1); denote (wproc 2)] [Child; Parent]
         (Some (Fin.FS Fin.F1)))))}, w |=
     AX (AX (AX (AX done {fun r _ => final r}))) ]>.
Proof.
  intros HC HP Hw.
  erewrite erase_write with (n := 1) (v := [denote (wproc 1); denote (wproc 2)])
    (g := [Child; Parent]) (j := Fin.FS Fin.F1) (addr := 2) (k := fun _ => tY);
    [|reflexivity|exists 0; apply write_head|].
  2:{ change (fst (oc_heap d Parent) 2 <> None); rewrite HP; discriminate. }
  erewrite erase_yield with (n := 1) (v := [denote (wproc 1); tY])
    (g := [Child; Parent]) (j := Fin.FS Fin.F1) (k := fun _ => Ret tt);
    [|reflexivity|exists 0; reflexivity].
  change (<[ {erase_owned (instrument_owned (set_pool (wrote d Parent 2)
    (mk_pool 2 [denote (wproc 1); Ret tt] [Child; Parent] None)))}, w |=
    AX (AX (AX (AX done {fun r _ => final r}))) ]>).
  rewrite erase_owned_select.
  apply (anr_brS _ _ Fin.F1); split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|dependent destruction j; [|inversion j]].
  - erewrite erase_write with (n := 1) (v := [denote (wproc 1); Ret tt])
      (g := [Child; Parent]) (j := Fin.F1) (addr := 1) (k := fun _ => tY);
      [|reflexivity|exists 0; apply write_head|].
    2:{ change (fst (oc_heap d Child) 1 <> None); rewrite HC; discriminate. }
    erewrite erase_yield with (n := 1) (v := [tY; Ret tt])
      (g := [Child; Parent]) (j := Fin.F1) (k := fun _ => Ret tt);
      [|reflexivity|exists 0; reflexivity].
    change (<[ {erase_owned (instrument_owned (set_pool (wrote (wrote d Parent 2) Child 1)
      (mk_pool 2 [Ret tt; Ret tt] [Child; Parent] None)))}, w |=
      AX (AX (AX done {fun r _ => final r})) ]>).
    apply finish_two; [exact Hw|].
    unfold joined_heap, wrote; cbn [set_heap oc_heap side_upd side_eqb].
    apply pop_resp; [rewrite HC|rewrite HP]; apply upd_region.
  - erewrite erase_return with (n := 1) (v := [denote (wproc 1); Ret tt])
      (g := [Child; Parent]) (j := Fin.FS Fin.F1);
      [|reflexivity|exists 0; reflexivity].
    rewrite !vector_remove_tail, !vector_remove_head.
    change (<[ {erase_owned (instrument_owned (set_pool (wrote d Parent 2)
      (mk_pool 1 [denote (wproc 1)] [Child] None)))}, w |=
      AX (AX (AX done {fun r _ => final r})) ]>).
    apply (finish_child a); [| |exact Hw].
    + cbn [wrote set_heap oc_heap side_upd side_eqb]; exact HC.
    + cbn [wrote set_heap oc_heap side_upd side_eqb]; rewrite HP; apply upd_region.
Qed.

Lemma four_raw a b ctx c :
  <[ {erase_owned (instrument_owned
       (init_owned (wproc 1) (wproc 2) (region 1 a) (region 2 b) ctx c))}, Pure |=
     AX (AX (AX (AX done {fun r _ => final r}))) ]>.
Proof.
  change (<[ {erase_owned (instrument_owned (set_pool
    (init_owned (wproc 1) (wproc 2) (region 1 a) (region 2 b) ctx c)
    (mk_pool 2 [denote (wproc 1); denote (wproc 2)] [Child; Parent]
      (Some (Fin.FS Fin.F1)))))}, Pure |=
    AX (AX (AX (AX done {fun r _ => final r}))) ]>).
  apply (pair_raw a b); [reflexivity|reflexivity|constructor].
Qed.
(** This is one action of the owned clock, not one raw scheduler tick. *)
Lemma first_frame a b ctx c :
  hAX owned_next (hsep hTrue hTrue)
    (init_owned (wproc 1) (wproc 2) (region 1 a) (region 2 b) ctx c).
Proof.
  set (d := init_owned (wproc 1) (wproc 2) (region 1 a) (region 2 b) ctx c).
  assert (W : owned_wf d).
  { apply init_owned_wf; try apply managed_wf_preallocated; apply region_disj; discriminate. }
  apply hAN_iff; split; [exact I|split].
  - eexists; exists (act Parent OAWrite).
    unfold owned_step, d, init_owned; cbn -[focus_step denote].
    right; right; right; right.
    exists unit, (inl1 (HWrite 2 1) : sE unit), (fun _ => tY), OAWrite, tt, (wrote d Parent 2).
    split; [exists 0; apply write_head|split; [reflexivity|split; reflexivity]].
  - intros d' [a' Hs]; split; [exact (owned_step_wf d a' d' W Hs)|split; exact I].
Qed.

Theorem write_safe_split a b ctx c :
  hAX owned_next hTrue (init_local Child (wproc 1) (region 1 a) ctx c false) /\
  hAX owned_next hTrue (init_local Parent (wproc 2) (region 2 b) ctx c true).
Proof.
  exact (fork_hax_split (wproc 1) (fun _ => wproc 2) (region 1 a) (region 2 b) ctx c
    hTrue hTrue (admission a b ctx c)
    ltac:(intros x y E; reflexivity) ltac:(intros x y E; reflexivity)
    ltac:(intros d a' d' Hs Ha; reflexivity) ltac:(intros d a' d' Hs Ha; reflexivity)
    (first_frame a b ctx c)).
Qed.

End OwnedAN.

(** Consequence under four [AX] layers. *)
Lemma ax4_done_mono {X} (t : ctreeW (CSLObs (nat * nat)) Bn X) w
  (P Q : X -> World (writerE (CSLObs (nat * nat))) -> Prop) :
  (forall x w, P x w -> Q x w) ->
  <[ t, w |= AX (AX (AX (AX done P))) ]> -> <[ t, w |= AX (AX (AX (AX done Q))) ]>.
Proof.
  intros HPQ.
  pose proof (done_impl_ticlr (M := ctree) (B := Bn) P Q HPQ) as HI.
  do 4 apply (impl_ticlr_next Q_A Q_A eq_refl <( ⊤ )> <( ⊤ )> (reflexivity _)) in HI.
  exact (HI t w).
Qed.
(** Every nondeterministic pick order finishes both writes after four steps. *)
Theorem an_two_procs_nd a b ctx c :
  <[ {run_nd (fork2 (wproc 1) (wproc 2)) (shared a b ctx c)}, Pure |=
     AX (AX (AX (AX done {fun '(s', _) _ => both 1 1 (csl_memory s')}))) ]>.
Proof.
  unfold fork2, shared.
  pose proof (fork_ticlr_erasure (wproc 1) (fun _ => wproc 2)
    (region 1 a) (region 2 b) ctx c
    <[ AX (AX (AX (AX done {fun r _ => OwnedAN.final r}))) ]>
    (OwnedAN.admission a b ctx c) (OwnedAN.four_raw a b ctx c)) as H.
  eapply ax4_done_mono; [|exact H].
  intros [s x] w (r0 & HR & HQ); exact (proj1 (OwnedAN.final_proper r0 (s, x) HR) HQ).
Qed.

(** ** Closed terms *)


(** Instantiate the round-robin result and expose both final cell values. *)
Example an_rr_3_5 ctx :
  <[ {run_rr (fork2 (wproc 1) (wproc 2)) (shared 3 5 ctx 0)}, Pure |=
     AX (AX (AX (AX done {fun '(s', _) _ => fst (csl_memory s') 1 = Some 1 /\ fst (csl_memory s') 2 = Some 1}))) ]>.
Proof.
  eapply ax4_done_mono; [|apply an_two_procs_rr].
  intros [s' _] _ H; apply both_lookup, H.
Qed.

(** Instantiate the nondeterministic result and expose both final cell values. *)
Example an_nd_3_5 ctx :
  <[ {run_nd (fork2 (wproc 1) (wproc 2)) (shared 3 5 ctx 0)}, Pure |=
     AX (AX (AX (AX done {fun '(s', _) _ => fst (csl_memory s') 1 = Some 1 /\ fst (csl_memory s') 2 = Some 1}))) ]>.
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
  ~ <[ {run_rr (fork2 (wproc 1) (wproc 2)) (own 2 b ctx c)}, Pure |=
       AX (AX (AX (AX done {fun _ _ => True}))) ]>.
Proof.
  intros b ctx c H.
  rewrite wproc_own_2_stuck in H.
  apply anr_step in H as [_ H].
  exact (anr_stuck H).
Qed.

Print Assumptions an_two_procs_rr.
