(** * Cursor-free concrete separation experiments.

    Ordinary managed-heap [asep] supplies spatial invariants. Native-return
    postconditions retain obtained local proofs across foreign observations;
    neither observations nor program/scheduler state carry provenance. *)
From Stdlib Require Import Fin Vector List Arith.PeanoNat Arith.Wf_nat Lia.
From Coinduction Require Import all.
From TICL Require Import Logic.Congruence CTree.Logic.Yield CTree.Logic.EX
  CTree.Interp.Yield.Segments CTree.Interp.Yield.Policy.
From examples Require Import CSL.Frame.Shared.

Module InvariantSeparation.
Import ListNotations.
Local Open Scope nat_scope.

Definition exact_cell (i value : nat) : assn ManagedHeap :=
  fun m => m ≈ region i value.

Definition split_cells (a b : nat) : assn ManagedHeap :=
  asep (exact_cell 1 a) (exact_cell 2 b).

Lemma exact_cell_proper i value : @AProper ManagedHeap _ (exact_cell i value).
Proof.
  intros m n Hmn Hm; unfold exact_cell in *.
  eapply peq_trans; [apply peq_sym; exact Hmn|exact Hm].
Qed.

Lemma split_cells_iff_both a b m : split_cells a b m <-> both a b m.
Proof.
  split.
  - intros (m1 & m2 & Hd & Hm & H1 & H2).
    eapply peq_trans; [exact Hm|apply pop_resp; assumption].
  - intro Hm; exists (region 1 a), (region 2 b).
    split; [apply region_disj; lia|].
    split; [exact Hm|split; apply peq_refl].
Qed.

Lemma split_cells_lookup a b m : split_cells a b m ->
  fst m 1 = Some a /\ fst m 2 = Some b.
Proof. intro H; apply both_lookup, split_cells_iff_both; exact H. Qed.

Local Definition ObsWorld := World (writerE (CSLObs (nat * nat))).
Definition emit_world i v k : ObsWorld :=
  Obs (Log (CSLEmit (stamp (i,v) k))) tt.

Definition parent_post a b ctx c
  : SSig * option unit -> ObsWorld -> Prop :=
  frame_post (region 1 a) (Qwork 2 b ctx c).

Definition workers_post a b ctx c
  : SSig * unit -> ObsWorld -> Prop :=
  fun '(s, _) w =>
    split_cells (S a) (S b) (csl_memory s) /\
    snd s = (ctx, S (S c)) /\
    w = emit_world 1 (S a) (S c) /\
    exists sp wp, parent_post a b ctx c (sp, Some tt) wp /\ wp <> w.

Definition sequence_post a b ctx c
  : SSig * option unit -> ObsWorld -> Prop :=
  fun '(s,x) w => x = Some tt /\ workers_post a b ctx c (s,tt) w.

(** Consume Child's post while retaining the actual obtained Parent proof. *)
Local Lemma child_keeps_parent a b ctx c sp wp s r w :
  parent_post a b ctx c (sp, Some tt) wp ->
  frame_post (region 2 (S b)) (Qwork 1 a ctx (S c)) (s,r) w ->
  sequence_post a b ctx c (s,r) w.
Proof.
  intros HP HC; pose proof HP as HPfacts.
  apply frame_post_work in HPfacts as (_ & _ & _ & Hwp).
  apply frame_post_work in HC as (-> & HM & HS & Hw).
  split; [reflexivity|].
  split; [apply split_cells_iff_both; exact HM|].
  split; [exact HS|split; [exact Hw|]].
  exists sp, wp; split; [exact HP|].
  rewrite Hwp, Hw; discriminate.
Qed.

Theorem bind_keeps_parent_post a b ctx c :
  <( {instr_flow_erased (work 2) (shared a b ctx c) >>=
       fun '(s,_) => instr_flow_erased (work 1) s},
     Pure |=R AF ret {sequence_post a b ctx c} )>.
Proof.
  ticl_normalize.
  eapply (u_bind_r (b:=true) Q_A) with (R:=parent_post a b ctx c).
  - apply (work_af_framed_ret 2 1 b a ctx c);
      [constructor|apply frame_rel_shared_2].
  - intros [sp rp] wp HP; pose proof HP as HPfacts.
    apply frame_post_work in HPfacts as (-> & HM & HS & Hwp).
    eapply aur_ret_mono.
    + intros [s r] w HC; exact (child_keeps_parent a b ctx c sp wp s r w HP HC).
    + apply (work_af_framed_ret 1 2 a (S b) ctx (S c)).
      * rewrite Hwp; constructor.
      * apply frame_rel_both_1; [|exact HS].
        eapply peq_trans; [exact HM|apply pop_comm, region_disj; lia].
Qed.

(** Parent has already returned: its obtained proof remains a hypothesis while
    the unfocused singleton Child is selected and performs its work. *)
Local Lemma nd_tail_work1_ret a b ctx c sp wp :
  parent_post a b ctx c (sp,Some tt) wp ->
  <( {interp_schedule_nd sh 1 ([denote_flow (proc 1);; Ret tt]%vector) None sp}, wp |=R
     AF ret {workers_post a b ctx c} )>.
Proof.
  ticl_normalize; intro HP; pose proof HP as HPfacts.
  apply frame_post_work in HPfacts as (_ & HM & HS & Hwp).
  assert (HM' : csl_memory sp ≈ region 1 a ⊎ region 2 (S b))
    by (eapply peq_trans; [exact HM|apply pop_comm, region_disj; lia]).
  rewrite interp_schedule_nd_select; cright; apply (an_brS (b:=true) _ _ Fin.F1);
    split; [rewrite Hwp; csplit; auto with ticl|].
  intro j; dependent destruction j; [|inversion j].
  change ([denote_flow (proc 1);; Ret tt]%vector : pool sE Bn 1)
    with (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow (proc 1) >>= fun _ => Ret tt)).
  unfold proc; nd_prefix work_yield_fork_free.
  eapply (u_bind_r (b:=true) Q_A).
  - apply (work_af_framed_ret 1 2 a (S b) ctx (S c));
      [rewrite Hwp; constructor|apply frame_rel_both_1; assumption].
  - intros [s r] w HC.
    pose proof (child_keeps_parent a b ctx c sp wp s r w HP HC) as (Hr & HB).
    subst r; destruct HB as (HM2 & HS2 & Hw & Hsaved).
    rewrite interp_nd_source_bind, interp_nd_source_yield.
    change (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow (CRet tt);; Ret tt))
      with (csl_pool (Vector.const (CRet tt) 1)).
    change (interp_schedule_nd sh 1 (csl_pool (Vector.const (CRet tt) 1)) None s)
      with (run_nd_pool (Vector.const (CRet tt) 1) None s).
    rewrite run_nd_pool_returns; cbn [Nat.iter].
    assert (Hlive : not_done w) by (rewrite Hw; constructor).
    cright; apply (an_step (b:=true)); split; [csplit; auto with ticl|].
    close_ret; exact (conj HM2 (conj HS2 (conj Hw Hsaved))).
Qed.

Theorem asep_two_procs_nd_ret a b ctx c :
  <( {run_nd (fork2 (proc 1) (proc 2)) (shared a b ctx c)},
     Pure |=R AF ret {workers_post a b ctx c} )>.
Proof.
  ticl_normalize.
  unfold fork2; rewrite run_nd_fork_bind.
  unfold denote.
  change ([denote_flow (proc 1);; Ret tt; denote_flow (proc 2);; Ret tt]%vector)
    with (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (proc 2) >>= fun _ => Ret tt)).
  unfold proc at 2; nd_prefix work_yield_fork_free.
  eapply (u_bind_r (b:=true) Q_A) with (R:=parent_post a b ctx c).
  - apply (work_af_framed_ret 2 1 b a ctx c);
      [constructor|apply frame_rel_shared_2].
  - intros [sp r] wp HP; pose proof HP as HPfacts.
    apply frame_post_work in HPfacts as (-> & HM & HS & Hwp).
    assert (HM' : csl_memory sp ≈ region 1 a ⊎ region 2 (S b))
      by (eapply peq_trans; [exact HM|apply pop_comm, region_disj; lia]).
    rewrite interp_nd_source_bind, interp_nd_source_yield.
    rewrite interp_schedule_nd_select; cright; apply (an_brS (b:=true) _ _ Fin.F1);
      split; [rewrite Hwp; csplit; auto with ticl|].
    intro j; dependent destruction j; [|dependent destruction j; [|inversion j]].
    + (* Child first: retain HP across its foreign emission. *)
      change (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt);; Ret tt))
        with (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2) @ child := (denote_flow (proc 1) >>= fun _ => Ret tt)).
      unfold proc; nd_prefix work_yield_fork_free.
      eapply (u_bind_r (b:=true) Q_A).
      * apply (work_af_framed_ret 1 2 a (S b) ctx (S c));
          [rewrite Hwp; constructor|apply frame_rel_both_1; assumption].
      * intros [s r] w HC.
        pose proof (child_keeps_parent a b ctx c sp wp s r w HP HC) as (Hr & HB).
        subst r; destruct HB as (HM2 & HS2 & Hw & Hsaved).
        rewrite interp_nd_source_bind, interp_nd_source_yield.
        change (([Ret tt; denote_flow (CRet tt);; Ret tt]%vector : pool sE Bn 2)
          @ child := (denote_flow (CRet tt);; Ret tt))
          with (csl_pool (Vector.const (CRet tt) 2)).
        change (interp_schedule_nd sh 2 (csl_pool (Vector.const (CRet tt) 2)) None s)
          with (run_nd_pool (Vector.const (CRet tt) 2) None s).
        rewrite run_nd_pool_returns; cbn [Nat.iter].
        assert (Hlive : not_done w) by (rewrite Hw; constructor).
        do 2 (cright; apply (an_step (b:=true)); split; [csplit; auto with ticl|]).
        close_ret; exact (conj HM2 (conj HS2 (conj Hw Hsaved))).
    + (* Parent first: remove Parent before Child performs any work. *)
      change (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt);; Ret tt))
        with (([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CRet tt) >>= fun _ => Ret tt)).
      rewrite interp_nd_source_ret.
      rewrite (interp_schedule_nd_ret sh) by reflexivity.
      change ((([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := Ret tt) -- parent)
        with (vector_remove ([denote_flow (proc 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) (Fin.FS Fin.F1)).
      rewrite vector_remove_tail, vector_remove_head.
      apply (nd_tail_work1_ret a b ctx c sp wp); exact HP.
Qed.

Example asep_two_procs_nd_3_5 ctx :
  <( {run_nd (fork2 (proc 1) (proc 2)) (shared 3 5 ctx 0)}, Pure |=R
     AF ret {fun '(s,_) w =>
       fst (csl_memory s) 1 = Some 4 /\ fst (csl_memory s) 2 = Some 6 /\
       snd s = (ctx,2) /\ w = emit_world 1 4 1 /\
       exists sp wp, parent_post 3 5 ctx 0 (sp,Some tt) wp /\
         wp = emit_world 2 6 0 /\ wp <> w} )>.
Proof.
  eapply aur_ret_mono; [|apply asep_two_procs_nd_ret].
  intros [s []] w (HM & HS & Hw & sp & wp & HP & Hneq).
  destruct (split_cells_lookup _ _ _ HM) as [H1 H2].
  pose proof HP as HPfacts; apply frame_post_work in HPfacts as (_ & _ & _ & Hwp).
  split; [exact H1|split; [exact H2|split; [exact HS|split; [exact Hw|]]]].
  exists sp, wp; auto.
Qed.

Definition heap_10 (o : CSLObs (nat * nat)) : Prop :=
  match o with CSLHeap m => split_cells 1 0 m | _ => False end.
Definition heap_01 (o : CSLObs (nat * nat)) : Prop :=
  match o with CSLHeap m => split_cells 0 1 m | _ => False end.
Definition one_write_obs o := heap_10 o \/ heap_01 o.

(** A focused write advances exactly one spatial component. *)
Local Lemma focused_write_child ctx c :
  <( {interp_schedule_nd sh 2 (csl_pool [CWrite 1 1; CWrite 2 1]%vector)
       (Some child) (shared 0 0 ctx c)}, Pure |=L AX visW {heap_10} )>.
Proof.
  ticl_normalize; unfold csl_pool, denote; cbn [Vector.map].
  change ([denote_flow (CWrite 1 1);; Ret tt; denote_flow (CWrite 2 1);; Ret tt]%vector)
    with (([Ret tt; denote_flow (CWrite 2 1);; Ret tt]%vector : pool sE Bn 2) @ child := (denote_flow (CWrite 1 1) >>= fun _ => Ret tt)).
  rewrite run_nd_prefix by apply write_yield_fork_free.
  eapply (an_bind_l (b:=false)).
  - apply (write_ax_ret_framed 1 2 0 0 ctx c);
      [constructor|apply frame_rel_both_1; [apply peq_refl|reflexivity]].
  - intros [s r] w HP; apply frame_post_write in HP as (_ & HM & _ & ->).
    csplit; apply split_cells_iff_both; exact HM.
Qed.

Local Lemma focused_write_parent ctx c :
  <( {interp_schedule_nd sh 2 (csl_pool [CWrite 1 1; CWrite 2 1]%vector)
       (Some parent) (shared 0 0 ctx c)}, Pure |=L AX visW {heap_01} )>.
Proof.
  ticl_normalize; unfold csl_pool, denote; cbn [Vector.map].
  change ([denote_flow (CWrite 1 1);; Ret tt; denote_flow (CWrite 2 1);; Ret tt]%vector)
    with (([denote_flow (CWrite 1 1);; Ret tt; Ret tt]%vector : pool sE Bn 2) @ parent := (denote_flow (CWrite 2 1) >>= fun _ => Ret tt)).
  rewrite run_nd_prefix by apply write_yield_fork_free.
  eapply (an_bind_l (b:=false)).
  - apply (write_ax_ret_framed 2 1 0 0 ctx c);
      [constructor|apply frame_rel_shared_2].
  - intros [s r] w HP; apply frame_post_write in HP as (_ & HM & _ & ->).
    csplit; apply split_cells_iff_both.
    eapply peq_trans; [exact HM|apply pop_comm, region_disj; lia].
Qed.

Theorem asep_writes_ax2 ctx c :
  <( {run_nd_pool [CWrite 1 1; CWrite 2 1]%vector None (shared 0 0 ctx c)},
     Pure |=L AX AX visW {one_write_obs} )>.
Proof.
  ticl_normalize; unfold run_nd_pool.
  rewrite interp_schedule_nd_select; apply (an_brS (b:=false) _ _ Fin.F1);
    split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|dependent destruction j; [|inversion j]].
  - pose proof (focused_write_child ctx c) as Hwrite.
    apply ticl_an in Hwrite as (Ht & Hs & Hnext).
    apply ticl_an; split; [exact Ht|split; [exact Hs|]].
    intros t w TR; specialize (Hnext t w TR); cdestruct Hnext;
      csplit; destruct e; destruct v; left; exact H.
  - pose proof (focused_write_parent ctx c) as Hwrite.
    apply ticl_an in Hwrite as (Ht & Hs & Hnext).
    apply ticl_an; split; [exact Ht|split; [exact Hs|]].
    intros t w TR; specialize (Hnext t w TR); cdestruct Hnext;
      csplit; destruct e; destruct v; right; exact H.
Qed.

Theorem asep_writes_not_ax1 ctx c :
  ~ <( {run_nd_pool [CWrite 1 1; CWrite 2 1]%vector None (shared 0 0 ctx c)},
       Pure |=L AX visW {one_write_obs} )>.
Proof.
  ticl_normalize; unfold run_nd_pool; rewrite interp_schedule_nd_select.
  intro H; apply (an_brS (b:=false) _ _ Fin.F1) in H as [_ H].
  specialize (H Fin.F1); cdestruct H.
Qed.

Theorem asep_writes_ex_child ctx c :
  <( {run_nd_pool [CWrite 1 1; CWrite 2 1]%vector None (shared 0 0 ctx c)},
     Pure |=L EX AX visW {heap_10} )>.
Proof.
  ticl_normalize; unfold run_nd_pool; rewrite interp_schedule_nd_select.
  apply (en_brS (b:=false)); split; [csplit; auto with ticl|].
  exists child; exact (focused_write_child ctx c).
Qed.

Theorem asep_writes_ex_parent ctx c :
  <( {run_nd_pool [CWrite 1 1; CWrite 2 1]%vector None (shared 0 0 ctx c)},
     Pure |=L EX AX visW {heap_01} )>.
Proof.
  ticl_normalize; unfold run_nd_pool; rewrite interp_schedule_nd_select.
  apply (en_brS (b:=false)); split; [csplit; auto with ticl|].
  exists parent; exact (focused_write_parent ctx c).
Qed.

Definition loop_inv (ctx : Ctx.Ctx) (g : nat * nat * nat) (s : SSig) : Prop :=
  let '(a,b,c) := g in
  split_cells a b (csl_memory s) /\ snd s = (ctx,c).

Definition fresh_emit (k : nat) (o : CSLObs (nat * nat)) : Prop :=
  csl_indexed (fun e => k <= indexed_index e) o.

(** Exact first-yield segment; the guard is normalized without a raw step. *)
Local Lemma exact_lproc_turn i v h allocs ctx c : h i = Some v ->
  segment_to sh csl_equ (denote (lproc i)) ((h,allocs),(ctx,c))
    [CSLHeap (upd h i (S v),allocs); CSLEmit (stamp (i,S v) c)]%list
    (denote (lproc i)) ((upd h i (S v),allocs),(ctx,S c)).
Proof.
  intro HV; unfold denote, lproc, lproc_body.
  apply exact_source_until; apply exact_source_bind; unfold work.
  apply exact_source_bind; eapply exact_source_read; [exact HV|]; cbn beta iota.
  apply exact_source_bind; apply exact_source_write; [rewrite HV; discriminate|]; cbn beta iota.
  apply exact_source_emit; cbn beta iota.
  apply exact_source_bind; apply exact_source_yield.
  eapply guard_equ_trans; [apply guard_equ_equ, source_raw_ret|].
  cbn [until_tail]; apply guard_equ_left, guard_equ_equ; reflexivity.
Qed.

Lemma loop_child_turn ctx a b c s : loop_inv ctx (a,b,c) s ->
  exists s',
    segment_to sh csl_equ (denote (lproc 1)) s
      [CSLHeap (csl_memory s'); CSLEmit (stamp (1,S a) c)]%list
      (denote (lproc 1)) s' /\ loop_inv ctx (S a,b,S c) s'.
Proof.
  intros [HM HS]; destruct s as [[h allocs] [ctx0 c0]]; cbn in HS; inversion HS; subst.
  destruct (split_cells_lookup _ _ _ HM) as [H1 H2].
  exists ((upd h 1 (S a),allocs),(ctx,S c)); split.
  - apply exact_lproc_turn; exact H1.
  - split; [|reflexivity]; apply split_cells_iff_both.
    pose proof (frame_rel_both_1 a b ctx c ((h,allocs),(ctx,c))
      (proj1 (split_cells_iff_both _ _ _) HM) eq_refl) as HR.
    pose proof (frame_rel_write _ _ _ 1 (S a) HR
      ltac:(change (hsingle 1 a 1 <> None); rewrite hsingle_eq; discriminate)) as HW.
    eapply peq_trans; [exact (proj2 (proj2 HW))|].
    apply pop_resp; [apply upd_region|apply peq_refl].
Qed.

Lemma loop_parent_turn ctx a b c s : loop_inv ctx (a,b,c) s ->
  exists s',
    segment_to sh csl_equ (denote (lproc 2)) s
      [CSLHeap (csl_memory s'); CSLEmit (stamp (2,S b) c)]%list
      (denote (lproc 2)) s' /\ loop_inv ctx (a,S b,S c) s'.
Proof.
  intros [HM HS]; destruct s as [[h allocs] [ctx0 c0]]; cbn in HS; inversion HS; subst.
  destruct (split_cells_lookup _ _ _ HM) as [H1 H2].
  exists ((upd h 2 (S b),allocs),(ctx,S c)); split.
  - apply exact_lproc_turn; exact H2.
  - split; [|reflexivity]; apply split_cells_iff_both.
    pose proof (frame_rel_both_2 a b ctx c ((h,allocs),(ctx,c))
      (proj1 (split_cells_iff_both _ _ _) HM) eq_refl) as HR.
    pose proof (frame_rel_write _ _ _ 2 (S b) HR
      ltac:(change (hsingle 2 b 2 <> None); rewrite hsingle_eq; discriminate)) as HW.
    eapply peq_trans; [exact (proj2 (proj2 HW))|].
    eapply peq_trans; [apply pop_resp; [apply upd_region|apply peq_refl]|].
    apply pop_comm, region_disj; lia.
Qed.

Lemma loop_ranked ctx k :
  RankedTurns sh (csl_pool [lproc 1;lproc 2]%vector) (loop_inv ctx)
    (fun '(a,b,c) => k - c) Nat.lt (fresh_emit k).
Proof.
  intros [[a b] c] s i Hinv; pattern i; apply Fin.caseS'.
  - destruct (loop_child_turn ctx a b c s Hinv) as (s' & Hseg & Hinv').
    exists (S a,b,S c), s', [CSLHeap (csl_memory s'); CSLEmit (stamp (1,S a) c)]%list.
    split; [exact Hseg|split; [exact Hinv'|]].
    destruct (Nat.le_gt_cases k c) as [Hle|Hgt].
    + left; apply List.Exists_cons_tl, List.Exists_cons_hd; exact Hle.
    + right; cbn; lia.
  - intro j; pattern j; apply Fin.caseS'.
    + destruct (loop_parent_turn ctx a b c s Hinv) as (s' & Hseg & Hinv').
      exists (a,S b,S c), s', [CSLHeap (csl_memory s'); CSLEmit (stamp (2,S b) c)]%list.
      split; [exact Hseg|split; [exact Hinv'|]].
      destruct (Nat.le_gt_cases k c) as [Hle|Hgt].
      * left; apply List.Exists_cons_tl, List.Exists_cons_hd; exact Hle.
      * right; cbn; lia.
    + intro z; inversion z.
Qed.

Theorem asep_lprocs_agaf_nd a b ctx c k :
  <( {run_nd (fork2 (lproc 1) (lproc 2)) (shared a b ctx c)},
     Pure |=L AG (AF visW {fresh_emit k}) )>.
Proof.
  unfold fork2; rewrite run_nd_fork_bind.
  change (interp_schedule_nd sh 2 [denote (lproc 1);denote (lproc 2)]%vector
    (Some parent) (shared a b ctx c))
    with (run_nd_pool [lproc 1;lproc 2]%vector (Some parent) (shared a b ctx c)).
  apply (ag_csl_nd_invariance _ (loop_inv ctx) _
    (ranked_turns_closed sh _ _ _ _ _ (loop_ranked ctx k))) with (g:=(a,b,c)).
  - intros o t w Hw Hphi.
    pose proof (af_log (b:=false) o t w _ Hw Hphi) as Hlog.
    unfold log in Hlog; rewrite bind_vis in Hlog; setoid_rewrite bind_ret_l in Hlog; exact Hlog.
  - intros g s focus w Hinv Hw.
    exact (aul_csl_nd_eventually _ _ _ Nat.lt _ lt_wf (loop_ranked ctx k) g s focus w Hinv Hw).
  - split; [apply split_cells_iff_both, peq_refl|reflexivity].
  - constructor.
Qed.

Theorem asep_lprocs_agaf_rr a b ctx c k :
  <( {run_rr (fork2 (lproc 1) (lproc 2)) (shared a b ctx c)},
     Pure |=L AG (AF visW {fair_obs (fresh_emit k)}) )>.
Proof.
  unfold fork2; rewrite run_rr_fork_bind.
  change (interp_schedule_rr sh 2 [denote (lproc 1);denote (lproc 2)]%vector
    (Some parent) 0 (shared a b ctx c))
    with (run_rr_pool [lproc 1;lproc 2]%vector (Some parent) 0 (shared a b ctx c)).
  apply (ag_csl_rr_invariance _ (loop_inv ctx) _
    (ranked_turns_closed sh _ _ _ _ _ (loop_ranked ctx k))) with (g:=(a,b,c)).
  - intros o t w Hw Hphi.
    pose proof (af_log (b:=false) (inl o) t w _ Hw Hphi) as Hlog.
    unfold log in Hlog; rewrite bind_vis in Hlog; setoid_rewrite bind_ret_l in Hlog; exact Hlog.
  - intros g s focus turn w Hinv Hw.
    exact (aul_csl_rr_eventually _ _ _ Nat.lt _ lt_wf (loop_ranked ctx k) g s focus turn w Hinv Hw).
  - split; [apply split_cells_iff_both, peq_refl|reflexivity].
  - constructor.
Qed.

End InvariantSeparation.
