(** * Regression: two cooperating processes, [AF] under both schedulers.

    [fork2 (proc 1) (proc 2)]: each process reads, increments and emits its
    own cell, then yields.  RR uses the cooperative prefix equation and
    standalone framing.  ND proves finite progress in the owned action
    machine, splits that proof into its two owned components, and erases it
    back to the original runner. *)
From Stdlib Require Import Fin Vector Lia.
From Coinduction Require Import all.
From examples Require Import CSL.Frame.Shared.
From TICL Require Import Lang.CoCSL.Owned Lang.CoCSL.Separation.

(** Round-robin execution finishes both processes with their incremented regions. *)
Theorem af_two_procs_rr a b ctx c :
  <[ {run_rr (fork2 (proc 1) (proc 2)) (shared a b ctx c)}, Pure |=
     AF done {fun '(s', _) _ => both (S a) (S b) (csl_memory s')} ]>.
Proof.
  unfold fork2; rewrite run_rr_fork_bind.
  unfold denote.
  change ([denote_flow (proc 1);; Ret tt; denote_flow (proc 2);; Ret tt]%vector)
    with (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (proc 2) >>= fun _ => Ret tt)).
  unfold proc at 2; rr_prefix work_yield_fork_free.
  cright.
  eapply aur_bind_r_done; [constructor| apply (work_af_framed 2 1 b a ctx c); [constructor|apply frame_rel_shared_2] |].
  intros [s1 r] w1 HP; apply frame_post_work in HP as (-> & HM1 & HS1 & ->).
  rewrite interp_rr_bind, interp_rr_yield.
  rewrite interp_schedule_rr_select; apply anr_step; split; [csplit; auto with ticl|].
  rewrite rr_pick_1_0.
  change (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt);; Ret tt))
    with (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) @ child := (denote_flow (proc 1) >>= fun _ => Ret tt)).
  unfold proc; rr_prefix work_yield_fork_free.
  cright.
  eapply aur_bind_r_done; [constructor| apply (work_af_framed 1 2 a (S b) ctx (S c)); [constructor|apply frame_rel_both_1; [|exact HS1]] |].
  { eapply peq_trans; [exact HM1|apply pop_comm, region_disj; auto]. }
  intros [s2 r] w2 HP; apply frame_post_work in HP as (-> & HM2 & _ & ->).
  rewrite interp_rr_bind, interp_rr_yield.
  rewrite interp_schedule_rr_select; apply anr_step; split; [csplit; auto with ticl|].
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

(** ** Finite owned progress, including the final yield and removals *)
Module OwnedAF.
Import VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

Definition live : hprop := hsep hTrue hTrue.
Definition owns (i : side) (addr value : nat) : hprop :=
  fun d => oc_heap d i ≈ region addr value.
Definition post a b : hprop :=
  hsep (hDone (owns Child 1 (S a))) (hDone (owns Parent 2 (S b))).

Lemma true_proper : hproper hTrue.
Proof. intros x y _; reflexivity. Qed.
Lemma live_proper : hproper live.
Proof. apply hsep_proper; apply true_proper. Qed.
Lemma owns_proper i addr value : hproper (owns i addr value).
Proof.
  intros x y (_ & _ & Hh & _); unfold owns; split; intro H.
  - eapply peq_trans; [apply peq_sym, Hh|exact H].
  - eapply peq_trans; [apply Hh|exact H].
Qed.
Lemma post_proper a b : hproper (post a b).
Proof. apply hsep_proper; apply hDone_proper, owns_proper. Qed.

(** The helpers consume actual [owned_step] rules.  Continuations are
    compared with [owned_equ], never equality of ctree proof terms. *)
Lemma action_hau Q d a d' :
  hproper Q -> owned_wf d -> owned_step d a d' ->
  (forall b e, owned_step d b e -> owned_equ e d') ->
  (owned_wf d' -> hAU owned_next live Q d') ->
  hAU owned_next live Q d.
Proof.
  intros HQ W Hs Hall IH.
  pose proof (IH (owned_step_wf _ _ _ W Hs)) as HU.
  apply hAU_step; [split; [exact W|split; exact I]|exists d', a; exact Hs|].
  intros e [b Hb].
  exact (proj2 (hAU_proper live Q live_proper HQ e d' (Hall b e Hb)) HU).
Qed.

Lemma prim_hau Q d n v g j Y (e : sE Y) k kind y d1 :
  hproper Q -> owned_wf d -> oc_pool d = mk_pool (S n) v g (Some j) ->
  (v $ j) ≅ guards 0 (Vis (inr1 (inr1 e) : CEff Y) k) ->
  prim_step (g $ j) d e = Some (kind, y, d1) ->
  (owned_wf (set_pool d1 (mk_pool (S n) (v @ j := k y) g (Some j))) ->
   hAU owned_next live Q (set_pool d1 (mk_pool (S n) (v @ j := k y) g (Some j)))) ->
  hAU owned_next live Q d.
Proof.
  intros HQ W Hpool Hhead Hp IH.
  eapply action_hau; [exact HQ|exact W| | |exact IH].
  - unfold owned_step; rewrite Hpool; cbn -[focus_step].
    apply (focus_step_head_prim _ _ _ _ _ _ _ 0 _ _ Hhead).
    exists k, kind, y, d1; split; [intro; reflexivity|split; [exact Hp|split; reflexivity]].
  - intros b d' Hs; unfold owned_step in Hs; rewrite Hpool in Hs; cbn -[focus_step] in Hs.
    apply (focus_step_head_prim _ _ _ _ _ _ _ 0 _ _ Hhead) in Hs
      as (k' & kind' & y' & d1' & Hk & Hp' & -> & ->).
    rewrite Hp in Hp'; injection Hp' as <- <- <-.
    apply set_pool_equ; [reflexivity|apply tp_equ_mk].
    split; [apply vector_replace_pointwise; [intros; reflexivity|apply Hk]|split; reflexivity].
Qed.

Lemma yield_hau Q d n v g j k :
  hproper Q -> owned_wf d -> oc_pool d = mk_pool (S n) v g (Some j) ->
  (v $ j) ≅ guards 0 (Vis (inl1 Yield : CEff unit) k) ->
  (owned_wf (set_pool d (mk_pool (S n) (v @ j := k tt) g None)) ->
   hAU owned_next live Q (set_pool d (mk_pool (S n) (v @ j := k tt) g None))) ->
  hAU owned_next live Q d.
Proof.
  intros HQ W Hpool Hhead IH.
  eapply action_hau; [exact HQ|exact W| | |exact IH].
  - unfold owned_step; rewrite Hpool; cbn -[focus_step].
    apply (focus_step_head_yield _ _ _ _ _ _ 0 _ _ Hhead).
    exists k; split; [intro; reflexivity|split; reflexivity].
  - intros b d' Hs; unfold owned_step in Hs; rewrite Hpool in Hs; cbn -[focus_step] in Hs.
    apply (focus_step_head_yield _ _ _ _ _ _ 0 _ _ Hhead) in Hs as (k' & Hk & -> & ->).
    apply set_pool_equ; [reflexivity|apply tp_equ_mk].
    split; [apply vector_replace_pointwise; [intros; reflexivity|apply Hk]|split; reflexivity].
Qed.

Lemma ret_hau Q d n v g j :
  hproper Q -> owned_wf d -> oc_pool d = mk_pool (S n) v g (Some j) ->
  (v $ j) ≅ guards 0 (Ret tt) ->
  (owned_wf (set_pool d (mk_pool n (v -- j) (g -- j) None)) ->
   hAU owned_next live Q (set_pool d (mk_pool n (v -- j) (g -- j) None))) ->
  hAU owned_next live Q d.
Proof.
  intros HQ W Hpool Hhead IH.
  eapply action_hau; [exact HQ|exact W| | |exact IH].
  - unfold owned_step; rewrite Hpool; cbn -[focus_step].
    apply (focus_step_head_ret _ _ _ _ _ 0 _ _ Hhead); split; reflexivity.
  - intros b d' Hs; unfold owned_step in Hs; rewrite Hpool in Hs; cbn -[focus_step] in Hs.
    apply (focus_step_head_ret _ _ _ _ _ 0 _ _ Hhead) in Hs as [-> ->]; reflexivity.
Qed.

Lemma select_hau Q d n v g :
  owned_wf d -> oc_pool d = mk_pool (S n) v g None ->
  (forall j, owned_wf (set_pool d (mk_pool (S n) v g (Some j))) ->
    hAU owned_next live Q (set_pool d (mk_pool (S n) v g (Some j)))) ->
  hAU owned_next live Q d.
Proof.
  intros W Hpool IH.
  assert (Hs : forall j, owned_step d (act (g $ j) OASelect)
    (set_pool d (mk_pool (S n) v g (Some j)))).
  { intro j; unfold owned_step; rewrite Hpool; cbn; exists j; split; reflexivity. }
  apply hAU_step; [split; [exact W|split; exact I]| |].
  - eexists; exists (act (g $ Fin.F1) OASelect); apply Hs.
  - intros d' [a Ha]; unfold owned_step in Ha; rewrite Hpool in Ha; cbn in Ha.
    destruct Ha as (j & -> & ->); apply IH; exact (owned_step_wf _ _ _ W (Hs j)).
Qed.

Definition tY : thread sE Bn := Vis (inl1 Yield : CEff unit) (fun _ => Ret tt).
Definition tE i value : thread sE Bn :=
  Vis (inr1 (inr1 (inr1 (inr1 (Log (i, value))))) : CEff unit) (fun _ => tY).
Definition tW i value : thread sE Bn :=
  Vis (inr1 (inr1 (inl1 (HWrite i value))) : CEff unit) (fun _ => tE i value).
Definition tR i : thread sE Bn :=
  Vis (inr1 (inr1 (inl1 (HRead i))) : CEff nat) (fun value => tW i (S value)).

Lemma proc_head i : denote (proc i) ≅ tR i.
Proof.
  unfold denote, proc, work; rewrite source_raw_bind, source_raw_bind, source_raw_read_head.
  unfold tR; step; constructor; intro value.
  unfold tW, tE, tY, heap_write, source_yield, CTree.trigger.
  do 3 (rewrite !bind_bind, bind_vis; apply vis_equ_node; intros []; rewrite !bind_ret_l).
  reflexivity.
Qed.

Lemma proc_admissible a b ctx c :
  admissible (proc 1) (proc 2) (region 1 a) (region 2 b) ctx c.
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

Lemma terminal_post a b d :
  terminal d -> oc_heap d Child ≈ region 1 (S a) -> oc_heap d Parent ≈ region 2 (S b) ->
  owned_wf d -> post a b d.
Proof.
  intros Ht HC HP W; split; [exact W|split; split].
  - apply project_size_terminal, Ht.
  - exact HC.
  - apply project_size_terminal, Ht.
  - exact HP.
Qed.

(** Finite normalization follows the real action rules above; selection is
    universally quantified, including either order of the final returns. *)
Local Ltac finish_owned :=
  match goal with W : owned_wf _ |- _ => clear - W end;
  cbn [tR tW tE tY Vector.replace Vector.nth caseS'] in *;
  (* Keep configuration update chains shared in the proof term. *)
  lazymatch goal with |- hAU _ _ _ ?state =>
    let s := fresh "owned_cfg" in set (s := state) in *
  end;
  first
    [ apply hAU_now; apply terminal_post; [reflexivity|apply upd_region|apply upd_region|assumption]
    | lazymatch goal with |- hAU _ _ _ ?state =>
        let p := eval hnf in (oc_pool state) in
        lazymatch p with Build_TaggedPool (S ?n0) ?threads0 ?tags0 (Some ?j0) =>
          let head := eval hnf in (threads0 $ j0) in
          lazymatch head with
          | Vis (inr1 (inr1 ?event0)) ?cont0 =>
            let T := type of cont0 in
            lazymatch T with ?response0 -> _ =>
              eapply prim_hau with (n := n0) (v := threads0) (g := tags0) (j := j0)
                (Y := response0) (e := event0) (k := cont0);
                [apply post_proper|assumption|reflexivity|reflexivity|reflexivity|]
            end
          | Vis (inl1 Yield) ?cont0 =>
            eapply yield_hau with (n := n0) (v := threads0) (g := tags0) (j := j0) (k := cont0);
              [apply post_proper|assumption|reflexivity|reflexivity|]
          | Ret tt =>
            eapply ret_hau with (n := n0) (v := threads0) (g := tags0) (j := j0);
              [apply post_proper|assumption|reflexivity|reflexivity|]
          end
        end
      end; intro; rewrite ?vector_remove_tail, ?vector_remove_head; finish_owned
    | eapply select_hau; [assumption|reflexivity|];
      let j := fresh "j" in let W := fresh "W" in
      intros j W; clear - W;
      repeat match goal with k : Fin.t _ |- _ => dependent destruction k end;
      finish_owned ].

Lemma global_hau a b ctx c :
  hAU owned_next live (post a b)
    (init_owned (proc 1) (proc 2) (region 1 a) (region 2 b) ctx c).
Proof.
  set (d := init_owned (proc 1) (proc 2) (region 1 a) (region 2 b) ctx c).
  set (d' := set_pool d (mk_pool 2 [tR 1; tR 2] [Child; Parent] (Some (Fin.FS Fin.F1)))).
  assert (He : owned_equ d d').
  { split.
    - apply tp_equ_mk; split; [|split; reflexivity].
      intro j; dependent destruction j; [apply proc_head|].
      dependent destruction j; [apply proc_head|inversion j].
    - split; [intro; apply peq_refl|split; [intro; apply peq_refl|]].
      split; [reflexivity|split; [reflexivity|split; intro; reflexivity]]. }
  apply (proj2 (hAU_proper live (post a b) live_proper (post_proper a b) d d' He)).
  assert (W : owned_wf d').
  { apply (owned_wf_equ d d' He), init_owned_wf;
      try apply managed_wf_preallocated; apply region_disj; discriminate. }
  unfold d', d; finish_owned.
Qed.

(** A direct, directional consumer of the source AU splitting theorem. *)
Theorem proc_split a b ctx c :
  hAF owned_next (hDone (owns Child 1 (S a)))
    (init_local Child (proc 1) (region 1 a) ctx c false) /\
  hAF owned_next (hDone (owns Parent 2 (S b)))
    (init_local Parent (proc 2) (region 2 b) ctx c true).
Proof.
  exact (fork_hau_split (proc 1) (fun _ => proc 2) (region 1 a) (region 2 b) ctx c
    hTrue hTrue (hDone (owns Child 1 (S a))) (hDone (owns Parent 2 (S b)))
    (proc_admissible a b ctx c) true_proper true_proper
    (hDone_proper _ (owns_proper _ _ _)) (hDone_proper _ (owns_proper _ _ _))
    (global_hau a b ctx c)).
Qed.

Definition final a b (r : SSig * unit) : Prop := both (S a) (S b) (csl_memory (fst r)).
Lemma final_proper a b : Proper (owned_result_rel ==> iff) (final a b).
Proof.
  intros [s x] [s' x'] (_ & _ & Hm).
  change (csl_memory s ≈ region 1 (S a) ⊎ region 2 (S b) <->
    csl_memory s' ≈ region 1 (S a) ⊎ region 2 (S b)); split; intro H.
  - eapply peq_trans; [apply peq_sym; exact Hm|exact H].
  - eapply peq_trans; [exact Hm|exact H].
Qed.

Lemma post_joined a b d : post a b d -> hDone (fun d => final a b (joined_state d, tt)) d.
Proof.
  intros (_ & [HCt HC] & [HPt HP]); split.
  - unfold terminal in *; pose proof (project_size_partition d); lia.
  - apply pop_resp; [exact HC|exact HP].
Qed.

Lemma finite_haf a b ctx c :
  hAF owned_next (hDone (fun d => final a b (joined_state d, tt)))
    (init_owned (proc 1) (proc 2) (region 1 a) (region 2 b) ctx c).
Proof.
  eapply hAU_mono; [intros; exact I|apply post_joined|apply global_hau].
Qed.
End OwnedAF.

(** Every nondeterministic schedule finishes, by owned finite progress and
    the result-setoid-aware erasure bridge, not raw scheduler enumeration. *)
Theorem af_two_procs_nd a b ctx c :
  <[ {run_nd (fork2 (proc 1) (proc 2)) (shared a b ctx c)}, Pure |=
     AF done {fun '(s', _) _ => both (S a) (S b) (csl_memory s')} ]>.
Proof.
  eapply aur_done_mono; [|exact (fork_haf_done_ticl (proc 1) (fun _ => proc 2)
    (region 1 a) (region 2 b) ctx c (OwnedAF.final a b)
    (OwnedAF.proc_admissible a b ctx c) (OwnedAF.final_proper a b)
    (OwnedAF.finite_haf a b ctx c))].
  intros [s' []] _ HB; exact HB.
Qed.

(** Concrete round-robin result for initial cell values [3] and [5]. *)
Example af_rr_3_5 ctx :
  <[ {run_rr (fork2 (proc 1) (proc 2)) (shared 3 5 ctx 0)}, Pure |=
     AF done {fun '(s', _) _ => fst (csl_memory s') 1 = Some 4 /\ fst (csl_memory s') 2 = Some 6} ]>.
Proof.
  eapply aur_done_mono; [|apply af_two_procs_rr].
  intros [s' []] _ HB; exact (both_lookup _ _ _ HB).
Qed.

(** Concrete nondeterministic result for initial cell values [3] and [5]. *)
Example af_nd_3_5 ctx :
  <[ {run_nd (fork2 (proc 1) (proc 2)) (shared 3 5 ctx 0)}, Pure |=
     AF done {fun '(s', _) _ => fst (csl_memory s') 1 = Some 4 /\ fst (csl_memory s') 2 = Some 6} ]>.
Proof.
  eapply aur_done_mono; [|apply af_two_procs_nd].
  intros [s' []] _ HB; exact (both_lookup _ _ _ HB).
Qed.

Print Assumptions af_two_procs_rr.
