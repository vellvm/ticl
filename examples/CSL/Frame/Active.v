(** * Active-component separation at the canonical state interpreter. *)
From Stdlib Require Import List Vector Fin Lia Relations Program.Equality FunctionalExtensionality.
From Coinduction Require Import all.
From TICL Require Import CTree.Interp.CSL.Owned CTree.Interp.CSL.Asep
  Lang.CoCSL.Owned CTree.Logic.AF CTree.Logic.Ret CTree.Logic.Trans
  CTree.Interp.Yield.SBisim CTree.Interp.Yield.Nondeterministic
  CTree.Interp.State.Mod CTree.Interp.Yield.Mod CTree.Trace
  Logic.Core Logic.World Logic.Setoid Logic.Semantics Utils.Pcm.
From examples Require Import Scheduling CSL.Frame.Shared.

Import CTreeNotations TiclNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.
#[local] Unset Universe Polymorphism.

Module NativeReturnRegression.
Definition cfg : OwnedCfg :=
  init_local_thread Parent (Ret tt) (region 2 6) []%list 1 true.
Definition initial : AsepState :=
  {| as_cfg := cfg; as_global := Pure; as_local := fun _ => Pure |}.
Definition empty_cfg : OwnedCfg :=
  set_pool cfg (mk_pool 0 []%vector []%vector None).

Lemma cfg_wf : owned_wf cfg.
Proof.
  eapply (owned_wf_equ _ _
    (project_init_threads_parent (Ret tt) (Ret tt) managed_empty (region 2 6) []%list 1)).
  apply owned_wf_project, init_owned_threads_wf.
  - apply managed_wf_empty.
  - apply managed_wf_preallocated.
  - split; intro a; left; reflexivity.
Qed.

Lemma cfg_erasable : erasable cfg.
Proof.
  apply (erasable_single_side Parent cfg).
  - exact cfg_wf.
  - intro j; dependent destruction j; [reflexivity|inversion j].
  - apply pool_framable_cons; [apply fr_ret|intro j; inversion j].
  - apply pool_branchfree_cons; [step; cbn; constructor|intro j; inversion j].
  - eapply confined_equ with
      (c := init_local Parent (CoCSLSyntax.CRet tt) (region 2 6) []%list 1 true).
    + apply owned_equ_pool_fields.
      * apply tp_equ_mk; split.
        -- intro j; dependent destruction j; [|inversion j].
           change (denote (CoCSLSyntax.CRet tt) ≅ (Ret tt : thread sE Bn)).
           unfold denote; cbn [denote_flow]; rewrite bind_ret_l; reflexivity.
        -- split; reflexivity.
      * repeat split.
    + apply addr_ok_confined; exact I.
Qed.

Lemma cfg_parent_equ : owned_equ (project Parent cfg) cfg.
Proof.
  split; [split|].
  - cbn [project oc_pool]; rewrite tp_slots_project; cbn; apply Forall2_slot_refl.
  - cbn [project oc_pool]; rewrite focus_nat_project; reflexivity.
  - refine (conj _ (conj _ (conj eq_refl (conj eq_refl (conj _ _))))); intros [];
      first [apply peq_refl|reflexivity].
Qed.

Lemma cfg_child_erasable : erasable (project Child cfg).
Proof.
  split; [apply owned_wf_project, cfg_wf|split].
  - intro j; inversion j.
  - split; [intro j; inversion j|].
    intros d Hd; apply clos_rt_rt1n in Hd.
    destruct Hd as [|d1 d2 [a Ha] Htail].
    + unfold head_confined; intros t i Y e k Hf.
      discriminate Hf.
    + exfalso; exact (owned_step_empty (project Child cfg) a d1 eq_refl Ha).
Qed.

Lemma initial_ok : asep_state_ok initial.
Proof.
  split.
  - split; [exact cfg_erasable|split; [exact cfg_child_erasable|]].
    eapply erasable_equ; [symmetry; exact cfg_parent_equ|exact cfg_erasable].
  - split; [constructor|intro i; constructor].
Qed.

Lemma focused_ret_run :
  owned_interp cfg ~ (Ret (joined_state cfg,tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  change (interp_schedule_nd sh 1 [Ret tt]%vector (Some Fin.F1) (joined_state cfg) ~
    (Ret (joined_state cfg,tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))).
  rewrite (interp_schedule_nd_ret sh 0 [Ret tt]%vector Fin.F1 (joined_state cfg) eq_refl).
  apply interp_schedule_nd_empty.
Qed.

Example focused_ret_not_empty :
  tp_size (oc_pool cfg) = 1 /\
  entails (SSig * unit) true
    (TICL.Logic.Syntax.CRet (fun r w => r = (joined_state cfg,tt) /\ w = Pure))
    (owned_interp cfg) Pure.
Proof.
  split; [reflexivity|].
  rewrite focused_ret_run; apply ret_ret; [constructor|split; reflexivity].
Qed.

Example empty_ret_run :
  tp_size (oc_pool empty_cfg) = 0 /\
  owned_interp empty_cfg ~ (Ret (joined_state empty_cfg,tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof. split; [reflexivity|apply interp_schedule_nd_empty]. Qed.

Example native_ret_silent_frontier :
  exists s', clos_refl_trans _ asep_silent initial s' /\
    tp_size (oc_pool (as_cfg s')) = 0 /\
    owned_interp cfg ~ (Ret (joined_state (as_cfg s'),tt) : AsepTree) /\
    as_global s' = Pure /\ forall i, as_local s' i = Pure.
Proof.
  assert (HP :
    entails (SSig * unit) true (TICL.Logic.Syntax.CRet (fun _ _ => True))
      (owned_interp (project Child cfg)) Pure /\
    entails (SSig * unit) true (TICL.Logic.Syntax.CRet (fun _ _ => True))
      (owned_interp (project Parent cfg)) Pure).
  { split.
    - assert (E : owned_interp (project Child cfg) ~
        (Ret (joined_state (project Child cfg),tt) : AsepTree))
        by apply interp_schedule_nd_empty.
      rewrite E; apply ret_ret; [constructor|exact I].
    - rewrite (owned_interp_equ _ _ cfg_parent_equ), focused_ret_run.
      apply ret_ret; [constructor|exact I]. }
  destruct (asep_ret_frontier initial _ _ initial_ok HP)
    as (s' & Hsil & Ew & El & Hz & HE & _).
  exists s'; split; [exact Hsil|split; [exact Hz|]].
  split; [exact HE|split; [exact Ew|exact El]].
Qed.

End NativeReturnRegression.

Module FaultRegression.
Example invalid_write_stuck :
  finish_sample (@log_payload (CSLObs (nat * nat))) 1000 []%list
    (interp_schedule_nd sh 2
      [denote (CWrite 1 4);denote (CoCSLSyntax.CRet tt)]%vector
      (Some Fin.F1) (region 2 5,([]%list,0))) = None.
Proof. vm_compute; reflexivity. Qed.

Example invalid_write_not_admissible :
  ~ admissible (CWrite 1 4) (CoCSLSyntax.CRet tt)
      managed_empty (region 2 5) []%list 0.
Proof.
  intros (_ & _ & _ & _ & _ & HC & _).
  assert (Hlocal : confined managed_empty
    (init_local Child (CWrite 1 4) managed_empty []%list 0 false)).
  { eapply confined_equ; [apply project_init_child|exact HC]. }
  assert (Hselect : clos_refl_trans _ owned_next
    (init_local Child (CWrite 1 4) managed_empty []%list 0 false)
    (init_local Child (CWrite 1 4) managed_empty []%list 0 true)).
  { apply rt_step; exists (act Child OASelect).
    apply init_local_select; split; reflexivity. }
  pose proof (Hlocal _ Hselect (denote (CWrite 1 4)) Child unit
    (inl1 (HWrite 1 4)) (fun _ => Ret tt) eq_refl
    ltac:(exists 0; apply source_raw_write_head)) as Hbad.
  exact (Hbad eq_refl).
Qed.
End FaultRegression.

Module OperationalNextRegression.
Definition cfg := init_owned (CWrite 1 4) (CWrite 2 6)
  (region 1 3) (region 2 5) []%list 0.
Definition initial : AsepState :=
  {| as_cfg := cfg; as_global := Pure; as_local := fun _ => Pure |}.

Lemma admitted : admissible (CWrite 1 4) (CWrite 2 6)
  (region 1 3) (region 2 5) []%list 0.
Proof.
  apply admissible_intro; try apply managed_wf_preallocated;
    try (apply region_disj; discriminate); cbn; try exact I; discriminate.
Qed.

Lemma initial_ok : asep_state_ok initial.
Proof.
  split; [apply admissible_active_erasable, admitted|].
  split; [constructor|intro i; constructor].
Qed.

Definition post := set_pool
  (set_heap cfg Parent (upd (fst (region 2 5)) 2 6, snd (region 2 5)))
  (mk_pool 2 [denote (CWrite 1 4);Ret tt]%vector [Child;Parent]%vector (Some (Fin.FS Fin.F1))).

Lemma write_step : owned_step cfg (act Parent OAWrite) post.
Proof.
  change (focus_step cfg 1 [denote (CWrite 1 4);denote (CWrite 2 6)]%vector
    [Child;Parent]%vector (Fin.FS Fin.F1) (act Parent OAWrite) post).
  right; right; right; right.
  exists unit, (inl1 (HWrite 2 6)), (fun _ => Ret tt), OAWrite, tt,
    (set_heap cfg Parent (upd (fst (region 2 5)) 2 6, snd (region 2 5))).
  split; [exists 0; apply source_raw_write_head|split; [reflexivity|split; reflexivity]].
Qed.

Example one_write_has_single_owner :
  exists t' s' u i,
    ktrans (owned_interp cfg) Pure t' (Obs (Log (CSLHeap (joined_heap post))) tt) /\
    asep_frontier initial s' /\ t' ~ owned_interp (as_cfg s') /\
    ktrans (owned_interp (project i cfg)) Pure u (as_local s' i) /\
    u ~ owned_interp (project i (as_cfg s')) /\
    owned_interp (project (other i) (as_cfg s')) ~ owned_interp (project (other i) cfg) /\
    as_local s' (other i) = Pure.
Proof.
  destruct (owned_interp_visible cfg cfg (act Parent OAWrite) post
    (obs (Log (CSLHeap (joined_heap post))) tt)
    (proj1 (proj1 initial_ok)) (rt_refl _ _ cfg) write_step eq_refl) as (t' & HT & _).
  assert (HK : ktrans (owned_interp cfg) Pure t' (Obs (Log (CSLHeap (joined_heap post))) tt)).
  { exact (owned_label_ktrans (act Parent OAWrite) (joined_heap post) _ _ _ Pure
      eq_refl HT ltac:(constructor)). }
  destruct (asep_visible_forward_owner initial t' _ initial_ok HK ltac:(constructor))
    as (s' & u & i & Hfront & Et & _ & HC).
  exists t', s', u, i.
  split; [exact HK|split; [exact Hfront|split; [exact Et|exact HC]]].
Qed.

End OperationalNextRegression.

From Stdlib Require Import Arith.PeanoNat.
From examples Require Import CSL.Frame.Separation.
From TICL Require Import CTree.Logic.Trace CTree.Logic.Yield CTree.Interp.Yield.Segments.

Module AlwaysActiveRegression.
Import AlwaysRegression.

Definition initial : AsepState :=
  {| as_cfg := c0; as_global := Pure; as_local := fun _ => Pure |}.
Lemma loop_turn a v tag (h : ManagedHeap) ctx c :
  fst h a = Some v ->
  segment_to sh csl_equ (denote (cloop a v tag)) (h,(ctx,c))
    [CSLHeap (upd (fst h) a v,snd h);CSLEmit (stamp (tag,v) c)]%list
    (denote (cloop a v tag)) ((upd (fst h) a v,snd h),(ctx,S c)).
Proof.
  intro Hv; exists (Guard (denote (cloop a v tag))); split.
  - eapply segment_equ with (u := tW a v tag)
      (u' := Guard (denote (cloop a v tag))).
    + apply cloop_unfold.
    + unfold tW.
      change (ThreadSegment sh csl_equ
        (Vis (inr1 (inr1 (inl1 (HWrite a v))) : CEff unit) (fun _ => tE a v tag))
        (h,(ctx,c))
        ([CSLHeap (upd (fst h) a v,snd h)] ++ [CSLEmit (stamp (tag,v) c)])%list
        (Guard (denote (cloop a v tag))) ((upd (fst h) a v,snd h),(ctx,S c))).
      eapply segment_user with (result := tt)
        (sigma1 := ((upd (fst h) a v,snd h),(ctx,c))).
      * destruct h as [heap allocs]; cbn [sh h_sum emit_list fst snd] in *.
        rewrite (heap_handlerW_wr_some CSLHeap a heap allocs (ctx,c) v v Hv); reflexivity.
      * unfold tE.
        change (ThreadSegment sh csl_equ
          (Vis (inr1 (inr1 (inr1 (inr1 (Log (tag,v))))) : CEff unit) (fun _ => tY a v tag))
          ((upd (fst h) a v,snd h),(ctx,c))
          ([CSLEmit (stamp (tag,v) c)] ++ [])%list
          (Guard (denote (cloop a v tag))) ((upd (fst h) a v,snd h),(ctx,S c))).
        eapply segment_user with (result := tt)
          (sigma1 := ((upd (fst h) a v,snd h),(ctx,S c))).
        -- cbn [sh h_sum emit_list]; rewrite csl_emit_handler_log; reflexivity.
        -- unfold tY; apply segment_yield.
    + reflexivity.
  - apply guard_equ_left; reflexivity.
Qed.

Definition loop_inv a v (_ : unit) (s : SSig) : Prop := fst (csl_memory s) a = Some v.

Lemma loop_closed a v tag :
  ClosedTurns sh (csl_pool [cloop a v tag]%vector) (loop_inv a v).
Proof.
  intros [] [h [ctx c]] i Hv.
  assert (Hi : i = Fin.F1) by (dependent destruction i; [reflexivity|inversion i]); subst i.
  exists tt, ((upd (fst h) a v,snd h),(ctx,S c)),
    [CSLHeap (upd (fst h) a v,snd h);CSLEmit (stamp (tag,v) c)]%list.
  split.
  - apply loop_turn; exact Hv.
  - change (upd (fst h) a v a = Some v); unfold upd; rewrite Nat.eqb_refl; reflexivity.
Qed.

Lemma loop_af_focused a v tag s w :
  loop_inv a v tt s -> not_done w ->
  <( {run_nd_pool [cloop a v tag]%vector (Some Fin.F1) s}, w
      |=L AF visW {csl_indexed (fun e => indexed_value e = (tag,v))} )>.
Proof.
  destruct s as [h [ctx c]]; intros Hv Hw.
  rewrite (run_nd_pool_turn [cloop a v tag]%vector Fin.F1 _ _ _
    (loop_turn a v tag h ctx c Hv)).
  eapply af_emit_list_member with (o := CSLEmit (stamp (tag,v) c));
    [exact Hw|cbn; auto|reflexivity].
Qed.

Lemma loop_af a v tag s focus w :
  loop_inv a v tt s -> not_done w ->
  <( {run_nd_pool [cloop a v tag]%vector focus s}, w
      |=L AF visW {csl_indexed (fun e => indexed_value e = (tag,v))} )>.
Proof.
  intros Hv Hw; destruct focus as [i|].
  - dependent destruction i; [apply loop_af_focused; assumption|inversion i].
  - rewrite run_nd_pool_select.
    apply ((au_brS (b:=false)) _ _ Fin.F1); right; split; [apply ticll_top; exact Hw|].
    intro i; dependent destruction i; [apply loop_af_focused; assumption|inversion i].
Qed.

Lemma loop_agaf a v tag s focus w :
  loop_inv a v tt s -> not_done w ->
  <( {run_nd_pool [cloop a v tag]%vector focus s}, w
      |=L AG (AF visW {csl_indexed (fun e => indexed_value e = (tag,v))}) )>.
Proof.
  intros Hv Hw.
  apply (ag_csl_nd_invariance [cloop a v tag]%vector (loop_inv a v)
    <( AF visW {csl_indexed (fun e => indexed_value e = (tag,v))} )>
    (loop_closed a v tag)) with (g := tt).
  - intros o t z Hz Hphi.
    pose proof (af_log (b:=false) o t z _ Hz Hphi) as Hlog.
    unfold log in Hlog; rewrite bind_vis in Hlog; setoid_rewrite bind_ret_l in Hlog; exact Hlog.
  - intros [] st f z Hinv Hz; apply loop_af; assumption.
  - exact Hv.
  - exact Hw.
Qed.

Definition child_obligation : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) false :=
  <( AF visW {csl_indexed (fun e => indexed_value e = (1,1))} )>.
Definition parent_obligation : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) false :=
  <( AF visW {csl_indexed (fun e => indexed_value e = (0,8))} )>.
Definition child_pred : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) ->
  World (writerE (CSLObs (nat * nat))) -> Prop :=
  entails (SSig * unit) false child_obligation.
Definition parent_pred : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) ->
  World (writerE (CSLObs (nat * nat))) -> Prop :=
  entails (SSig * unit) false parent_obligation.

Lemma child_local_ag : agc child_pred (owned_interp (project Child c0)) Pure.
Proof.
  rewrite (owned_interp_equ _ _ (project_init_child pc pp hC hP ctx0 0)).
  change <( {run_nd_pool [pc]%vector None (joined_state (init_local Child pc hC ctx0 0 false))}, Pure
    |=L AG (AF visW {csl_indexed (fun e => indexed_value e = (1,1))}) )>.
  apply loop_agaf; [reflexivity|constructor].
Qed.

Lemma parent_local_ag : agc parent_pred (owned_interp (project Parent c0)) Pure.
Proof.
  rewrite (owned_interp_equ _ _ (project_init_parent pc pp hC hP ctx0 0)).
  change <( {run_nd_pool [pp]%vector (Some Fin.F1) (joined_state (init_local Parent pp hP ctx0 0 true))}, Pure
    |=L AG (AF visW {csl_indexed (fun e => indexed_value e = (0,8))}) )>.
  apply loop_agaf; [reflexivity|constructor].
Qed.

Lemma initial_ok : asep_state_ok initial.
Proof.
  split; [apply admissible_active_erasable, loops_admissible|].
  split; [constructor|intro i; constructor].
Qed.

Theorem loops_active_ag :
  agc (asep_sat (fun _ => True) child_pred parent_pred) (owned_interp c0) Pure.
Proof.
  apply asep_agc_compose.
  - exact asep_closed_true.
  - apply asep_pred_ok_entails.
  - apply asep_pred_ok_entails.
  - apply (asep_sat_intro _ _ _ initial), asep_at_intro;
      [exact initial_ok|exact I|exact child_local_ag|exact parent_local_ag].
Qed.

End AlwaysActiveRegression.

Module TerminationActiveRegression.

Definition cfg := init_owned (proc 1) (proc 2)
  (region 1 3) (region 2 5) []%list 0.
Definition initial : AsepState :=
  {| as_cfg := cfg; as_global := Pure; as_local := fun _ => Pure |}.
Definition local_post (i value : nat)
  : SSig * unit -> World (writerE (CSLObs (nat * nat))) -> Prop :=
  fun '(s, _) w => csl_memory s ≈ region i value /\
    csl_context s = []%list /\ csl_counter s = 1 /\
    w = Obs (Log (CSLEmit (stamp (i,value) 0))) tt.
Definition RC := local_post 1 4.
Definition RP := local_post 2 6.
Definition live : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) ->
  World (writerE (CSLObs (nat * nat))) -> Prop :=
  entails (SSig * unit) false (CNow (fun _ => True)).

Lemma admitted : admissible (proc 1) (proc 2)
  (region 1 3) (region 2 5) []%list 0.
Proof.
  apply admissible_intro; try apply managed_wf_preallocated;
    try (apply region_disj; discriminate);
    unfold proc, work; cbn; intuition discriminate.
Qed.

Lemma initial_ok : asep_state_ok initial.
Proof.
  split; [apply admissible_active_erasable, admitted|].
  split; [constructor|intro i; constructor].
Qed.

Lemma focused_proc_af i a w : not_done w ->
  entails (SSig * unit) true
    (Cu Q_A (CNow (fun _ => True)) (TICL.Logic.Syntax.CRet (local_post i (S a))))
    (interp_schedule_nd sh 1 [denote (proc i)]%vector (Some Fin.F1)
      (own i a []%list 0)) w.
Proof.
  intro Hw; ticl_normalize.
  unfold denote at 1.
  change ([denote_flow (proc i);; Ret tt]%vector : pool sE Bn 1)
    with (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 :=
      (denote_flow (proc i) >>= fun _ => Ret tt)).
  unfold proc; nd_prefix work_yield_fork_free.
  eapply (u_bind_r (b:=true) Q_A); [apply work_af_ret; exact Hw|].
  intros [s r] w' (-> & Hm & Haux & ->).
  rewrite interp_nd_source_bind, interp_nd_source_yield.
  rewrite interp_schedule_nd_select.
  cright; apply (an_brS (b:=true) _ _ Fin.F1).
  split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [|inversion j].
  rewrite interp_nd_source_ret.
  rewrite (interp_schedule_nd_ret sh) by reflexivity.
  rewrite interp_schedule_nd_empty.
  close_ret.
  unfold local_post; split; [exact Hm|].
  unfold csl_context, csl_counter; rewrite Haux; repeat split.
Qed.

Lemma singleton_state i p h focused :
  joined_state (init_local i p h []%list 0 focused) = (h,([]%list,0)).
Proof.
  unfold init_local, init_local_thread, joined_state, joined_heap, global_count.
  destruct i; cbn [side_only side_eqb oc_heap oc_ctx oc_base oc_count].
  - f_equal; apply managed_heap_ext.
    apply (@Pcm.pop_emp_r ManagedHeap
      (@Pcm.ProductPCM Heap Heap HeapModel.HeapPCM HeapModel.HeapPCM)).
    apply Pcm.pdef_emp_r.
  - f_equal; apply managed_heap_ext.
    apply (@Pcm.pop_emp ManagedHeap
      (@Pcm.ProductPCM Heap Heap HeapModel.HeapPCM HeapModel.HeapPCM)).
Qed.

Lemma local_proc_af i a tag focused :
  entails (SSig * unit) true
    (Cu Q_A (CNow (fun _ => True)) (TICL.Logic.Syntax.CRet (local_post i (S a))))
    (owned_interp (init_local tag (proc i) (region i a) []%list 0 focused)) Pure.
Proof.
  unfold owned_interp; rewrite singleton_state.
  change (entails (SSig * unit) true
    (Cu Q_A (CNow (fun _ => True)) (TICL.Logic.Syntax.CRet (local_post i (S a))))
    (interp_schedule_nd sh 1 [denote (proc i)]%vector
      (if focused then Some Fin.F1 else None) (own i a []%list 0)) Pure).
  destruct focused; [apply focused_proc_af; constructor|].
  rewrite interp_schedule_nd_select.
  cright; apply (an_brS (b:=true) _ _ Fin.F1).
  split; [csplit; auto with ticl|].
  intro j; dependent destruction j; [apply focused_proc_af; constructor|inversion j].
Qed.

Lemma local_returns :
  entails (SSig * unit) true
    (Cu Q_A (CNow (fun _ => True)) (TICL.Logic.Syntax.CRet RC))
    (owned_interp (project Child cfg)) Pure /\
  entails (SSig * unit) true
    (Cu Q_A (CNow (fun _ => True)) (TICL.Logic.Syntax.CRet RP))
    (owned_interp (project Parent cfg)) Pure.
Proof.
  split; unfold cfg.
  - rewrite (owned_interp_equ _ _ (project_init_child _ _ _ _ _ _)).
    apply local_proc_af.
  - rewrite (owned_interp_equ _ _ (project_init_parent _ _ _ _ _ _)).
    apply local_proc_af.
Qed.

Definition base_inv (s : AsepState) : Prop := oc_base (as_cfg s) = 0.
Definition termination_inv (s : AsepState) : Prop :=
  asep_at base_inv
    (entails (SSig * unit) true
      (TICL.Logic.Syntax.Cu Q_A (CNow (fun _ => True))
        (TICL.Logic.Syntax.CRet RC)))
    (entails (SSig * unit) true
      (TICL.Logic.Syntax.Cu Q_A (CNow (fun _ => True))
        (TICL.Logic.Syntax.CRet RP))) s.

Lemma base_inv_closed : asep_closed base_inv.
Proof.
  intros s a s' _ Hbase [Hstep _].
  unfold base_inv in *.
  rewrite (proj2 (proj2 (owned_step_frozen _ _ _ Hstep))); exact Hbase.
Qed.

Lemma termination_inv_init : termination_inv initial.
Proof.
  destruct local_returns as [HC HP].
  apply asep_at_intro; [exact initial_ok|reflexivity|exact HC|exact HP].
Qed.

Lemma termination_inv_closed : asep_closed termination_inv.
Proof.
  intros s a s' Hok Hinv Hstep.
  apply asep_at_inv in Hinv as (_ & _ & Hbase & HC & HP).
  apply ticl_au in HC, HP.
  assert (Hlocal : asep_at base_inv
    (auc live (entails (SSig * unit) true (TICL.Logic.Syntax.CRet RC)))
    (auc live (entails (SSig * unit) true (TICL.Logic.Syntax.CRet RP))) s).
  { apply asep_at_intro; assumption. }
  pose proof (asep_at_auc_ret_step base_inv live live RC RP s a s'
    base_inv_closed (asep_pred_ok_entails _)
    (asep_pred_ok_entails _) Hlocal Hstep) as Hnext.
  apply asep_at_inv in Hnext as (Hok' & _ & Hbase' & HC' & HP').
  apply asep_at_intro; [exact Hok'|exact Hbase'|apply ticl_au; exact HC'|apply ticl_au; exact HP'].
Qed.

Theorem both_af_ret :
  entails (SSig * unit) true
    (Cu Q_A (CNow (fun _ => True))
      (TICL.Logic.Syntax.CRet (asep_ret base_inv RC RP)))
    (owned_interp cfg) Pure.
Proof.
  apply asep_af_ret_compose; [exact base_inv_closed|].
  apply (asep_sat_intro _ _ _ initial); exact termination_inv_init.
Qed.

Theorem both_ef_ret :
  entails (SSig * unit) true
    (Cu Q_E (CNow (fun _ => True))
      (TICL.Logic.Syntax.CRet (asep_ret base_inv RC RP)))
    (owned_interp cfg) Pure.
Proof.
  apply asep_ef_ret_compose; [exact base_inv_closed|].
  pose proof termination_inv_init as Hinv.
  apply asep_at_inv in Hinv as (Hok & _ & Hbase & HC & HP).
  apply ticl_au_eu in HC, HP.
  apply (asep_sat_intro _ _ _ initial), asep_at_intro; assumption.
Qed.

Lemma final_state r w : asep_ret base_inv RC RP r w ->
  fst (csl_memory (fst r)) 1 = Some 4 /\
  fst (csl_memory (fst r)) 2 = Some 6 /\
  csl_context (fst r) = []%list /\ csl_counter (fst r) = 2.
Proof.
  destruct r as [st []].
  intro Hret.
  destruct (asep_ret_elim base_inv RC RP st w Hret)
    as (s & _ & Hbase & _ & _ & Es & _ & HC & HP).
  destruct HC as (HC & Hctx & HcountC & _), HP as (HP & _ & HcountP & _).
  cbn [fst]; rewrite Es.
  unfold base_inv in Hbase.
  assert (Hm : both 4 6 (joined_heap (as_cfg s))).
  { unfold both, joined_heap; apply pop_resp; assumption. }
  destruct (both_lookup 4 6 _ Hm) as [H1 H2].
  split; [exact H1|split; [exact H2|split; [exact Hctx|]]].
  unfold csl_counter, joined_state, global_count; cbn [fst snd].
  unfold csl_counter, local_state in HcountC, HcountP; cbn [fst snd] in HcountC, HcountP.
  lia.
Qed.

Definition final_cells : SSig * unit -> World (writerE (CSLObs (nat * nat))) -> Prop :=
  fun r _ => fst (csl_memory (fst r)) 1 = Some 4 /\
    fst (csl_memory (fst r)) 2 = Some 6 /\
    csl_context (fst r) = []%list /\ csl_counter (fst r) = 2.

Theorem both_af_final_cells :
  entails (SSig * unit) true
    (Cu Q_A (CNow (fun _ => True)) (TICL.Logic.Syntax.CRet final_cells))
    (owned_interp cfg) Pure.
Proof.
  eapply aur_ret_mono; [|exact both_af_ret].
  intros r w H; exact (final_state r w H).
Qed.

Theorem both_ef_final_cells :
  entails (SSig * unit) true
    (Cu Q_E (CNow (fun _ => True)) (TICL.Logic.Syntax.CRet final_cells))
    (owned_interp cfg) Pure.
Proof.
  eapply (impl_ticl_until (X:=SSig * unit) (b:=true) Q_E Q_E eq_refl).
  - intros t w H; exact H.
  - apply ret_impl_ticl; intros r w H; exact (final_state r w H).
  - exact both_ef_ret.
Qed.

(* The script [1] selects Parent after its yield.  The following configurations
   record those existing machine actions, then remove its native return. *)
Definition tY : thread sE Bn := Vis (inl1 Yield : CEff unit) (fun _ => Ret tt).
Definition tE : thread sE Bn :=
  Vis (inr1 (inr1 (inr1 (inr1 (Log (2,6))))) : CEff unit) (fun _ => tY).
Definition tW (v : nat) : thread sE Bn :=
  Vis (inr1 (inr1 (inl1 (HWrite 2 v))) : CEff unit)
    (fun _ => Vis (inr1 (inr1 (inr1 (inr1 (Log (2,v))))) : CEff unit) (fun _ => tY)).
Definition c1 := set_pool cfg
  (mk_pool 2 [denote (proc 1);tW 6]%vector [Child;Parent]%vector (Some (Fin.FS Fin.F1))).
Definition c2 := set_pool
  (set_heap c1 Parent (upd (fst (region 2 5)) 2 6, snd (region 2 5)))
  (mk_pool 2 [denote (proc 1);tE]%vector [Child;Parent]%vector (Some (Fin.FS Fin.F1))).
Definition c3 := set_pool (emit_cfg c2 Parent (2,6))
  (mk_pool 2 [denote (proc 1);tY]%vector [Child;Parent]%vector (Some (Fin.FS Fin.F1))).
Definition c4 := set_pool c3
  (mk_pool 2 [denote (proc 1);Ret tt]%vector [Child;Parent]%vector None).
Definition c5 := set_pool c4
  (mk_pool 2 [denote (proc 1);Ret tt]%vector [Child;Parent]%vector (Some (Fin.FS Fin.F1))).
Definition c6 := set_pool c5
  (mk_pool 1 [denote (proc 1)]%vector [Child]%vector None).

Lemma proc_parent_head : denote (proc 2) ≅
  Vis (inr1 (inr1 (inl1 (HRead 2))) : CEff nat) (fun v => tW (S v)).
Proof.
  unfold denote, proc, work.
  rewrite source_raw_bind, source_raw_bind, source_raw_read_head.
  apply vis_equ_node; intro v; cbn beta iota zeta.
  rewrite source_raw_bind, source_raw_write_head.
  unfold tW; apply vis_equ_node; intros []; cbn beta iota zeta.
  rewrite source_raw_emit_head.
  apply vis_equ_node; intros []; cbn beta iota zeta.
  rewrite source_raw_bind, source_raw_yield_head.
  unfold tY; apply vis_equ_node; intros []; cbn beta iota zeta.
  rewrite source_raw_ret; reflexivity.
Qed.

Lemma step01 : owned_step cfg (act Parent OARead) c1.
Proof.
  change (focus_step cfg 1 [denote (proc 1);denote (proc 2)]%vector
    [Child;Parent]%vector (Fin.FS Fin.F1) (act Parent OARead) c1).
  right; right; right; right.
  exists nat, (inl1 (HRead 2)), (fun v => tW (S v)), OARead, 5, cfg.
  split; [exists 0; exact proc_parent_head|split; [reflexivity|split; reflexivity]].
Qed.
Lemma step12 : owned_step c1 (act Parent OAWrite) c2.
Proof.
  change (focus_step c1 1 [denote (proc 1);tW 6]%vector [Child;Parent]%vector
    (Fin.FS Fin.F1) (act Parent OAWrite) c2).
  right; right; right; right.
  exists unit, (inl1 (HWrite 2 6)), (fun _ => tE), OAWrite, tt,
    (set_heap c1 Parent (upd (fst (region 2 5)) 2 6, snd (region 2 5))).
  split; [exists 0; reflexivity|split; [reflexivity|split; reflexivity]].
Qed.
Lemma step23 : owned_step c2 (act Parent (OAEmit (2,6) 0)) c3.
Proof.
  change (focus_step c2 1 [denote (proc 1);tE]%vector [Child;Parent]%vector
    (Fin.FS Fin.F1) (act Parent (OAEmit (2,6) 0)) c3).
  right; right; right; right.
  exists unit, (inr1 (inr1 (Log (2,6)))), (fun _ => tY),
    (OAEmit (2,6) 0), tt, (emit_cfg c2 Parent (2,6)).
  split; [exists 0; reflexivity|split; [reflexivity|split; reflexivity]].
Qed.
Lemma step34 : owned_step c3 (act Parent OAYield) c4.
Proof.
  change (focus_step c3 1 [denote (proc 1);tY]%vector [Child;Parent]%vector
    (Fin.FS Fin.F1) (act Parent OAYield) c4).
  right; left; exists (fun _ => Ret tt).
  split; [exists 0; reflexivity|split; reflexivity].
Qed.
Lemma step45 : owned_step c4 (act Parent OASelect) c5.
Proof. exists (Fin.FS Fin.F1); split; reflexivity. Qed.
Lemma step56 : owned_step c5 (act Parent OAReturn) c6.
Proof.
  change (focus_step c5 1 [denote (proc 1);Ret tt]%vector [Child;Parent]%vector
    (Fin.FS Fin.F1) (act Parent OAReturn) c6).
  right; right; right; left.
  split; [exists 0; reflexivity|split; reflexivity].
Qed.

Definition early1 := asep_advance initial (act Parent OARead) c1.
Definition early2 := asep_advance early1 (act Parent OAWrite) c2.
Definition early3 := asep_advance early2 (act Parent (OAEmit (2,6) 0)) c3.
Definition early4 := asep_advance early3 (act Parent OAYield) c4.
Definition early5 := asep_advance early4 (act Parent OASelect) c5.
Definition early6 := asep_advance early5 (act Parent OAReturn) c6.

Lemma early_steps :
  asep_step initial (act Parent OARead) early1 /\
  asep_step early1 (act Parent OAWrite) early2 /\
  asep_step early2 (act Parent (OAEmit (2,6) 0)) early3 /\
  asep_step early3 (act Parent OAYield) early4 /\
  asep_step early4 (act Parent OASelect) early5 /\
  asep_step early5 (act Parent OAReturn) early6.
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  all: split; [first [exact step01|exact step12|exact step23|exact step34
    |exact step45|exact step56]|reflexivity].
Qed.

Lemma early_termination_inv : termination_inv early6.
Proof.
  destruct early_steps as (H01 & H12 & H23 & H34 & H45 & H56).
  pose proof (asep_state_ok_step _ _ _ initial_ok H01) as Hok1.
  pose proof (termination_inv_closed _ _ _ initial_ok termination_inv_init H01) as HI1.
  pose proof (asep_state_ok_step _ _ _ Hok1 H12) as Hok2.
  pose proof (termination_inv_closed _ _ _ Hok1 HI1 H12) as HI2.
  pose proof (asep_state_ok_step _ _ _ Hok2 H23) as Hok3.
  pose proof (termination_inv_closed _ _ _ Hok2 HI2 H23) as HI3.
  pose proof (asep_state_ok_step _ _ _ Hok3 H34) as Hok4.
  pose proof (termination_inv_closed _ _ _ Hok3 HI3 H34) as HI4.
  pose proof (asep_state_ok_step _ _ _ Hok4 H45) as Hok5.
  pose proof (termination_inv_closed _ _ _ Hok4 HI4 H45) as HI5.
  exact (termination_inv_closed _ _ _ Hok5 HI5 H56).
Qed.

Lemma early_worlds :
  as_global early6 = Obs (Log (CSLEmit (stamp (2,6) 0))) tt /\
  as_local early6 Parent = Obs (Log (CSLEmit (stamp (2,6) 0))) tt /\
  as_local early6 Child = Pure /\
  tp_size (oc_pool (as_cfg early6)) = 1 /\ tp_focus (oc_pool (as_cfg early6)) = None.
Proof. repeat split. Qed.

Lemma early_child_af : auc live (entails (SSig * unit) true (TICL.Logic.Syntax.CRet RC))
  (owned_interp (project Child (as_cfg early6))) (as_local early6 Child).
Proof.
  pose proof early_termination_inv as Hinv.
  apply asep_at_inv in Hinv as (_ & _ & _ & HC & _).
  apply ticl_au in HC; exact HC.
Qed.

Lemma early_parent_ret :
  entails (SSig * unit) true (TICL.Logic.Syntax.CRet RP)
    (owned_interp (project Parent (as_cfg early6))) (as_local early6 Parent).
Proof.
  pose proof early_termination_inv as Hinv.
  apply asep_at_inv in Hinv as (Hok & _ & _ & _ & HP).
  apply ticl_au in HP.
  eapply asep_auc_ret_empty with (P := live);
    [exact (proj2 (proj2 (proj1 Hok)))|reflexivity|apply asep_pred_ok_entails|exact HP].
Qed.

(* The completed side needs no live guard: this one is deliberately false. *)
Definition finished_guard : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) ->
  World (writerE (CSLObs (nat * nat))) -> Prop := fun _ _ => False.
Lemma finished_guard_ok : asep_pred_ok finished_guard.
Proof. split; [intros t w H; contradiction|intros t u E w v Ew; reflexivity]. Qed.

Definition early_inv (s : AsepState) : Prop :=
  asep_at base_inv
    (entails (SSig * unit) true
      (TICL.Logic.Syntax.Cu Q_A (CNow (fun _ => True))
        (TICL.Logic.Syntax.CRet RC)))
    (entails (SSig * unit) true (TICL.Logic.Syntax.CRet RP)) s.

Lemma early_inv_init : early_inv early6.
Proof.
  pose proof early_termination_inv as Hinv.
  apply asep_at_inv in Hinv as (Hok & _ & Hbase & _ & _).
  apply asep_at_intro;
    [exact Hok|exact Hbase|apply ticl_au; exact early_child_af|exact early_parent_ret].
Qed.

Lemma early_inv_closed : asep_closed early_inv.
Proof.
  intros s a s' Hok Hinv Hstep.
  apply asep_at_inv in Hinv as (_ & _ & Hbase & HC & HP).
  apply ticl_au in HC.
  assert (Hlocal : asep_at base_inv
    (auc live (entails (SSig * unit) true (TICL.Logic.Syntax.CRet RC)))
    (auc finished_guard (entails (SSig * unit) true (TICL.Logic.Syntax.CRet RP))) s).
  { apply asep_at_intro; [exact Hok|exact Hbase|exact HC|apply MatchA; exact HP]. }
  pose proof (asep_at_auc_ret_step base_inv live finished_guard RC RP s a s'
    base_inv_closed (asep_pred_ok_entails _) finished_guard_ok Hlocal Hstep) as Hnext.
  apply asep_at_inv in Hnext as (Hok' & _ & Hbase' & HC' & HP').
  apply asep_at_intro; [exact Hok'|exact Hbase'|apply ticl_au; exact HC'|].
  inversion HP' as [t w HR|t w HN]; subst; [exact HR|].
  destruct HN as [HF _]; contradiction.
Qed.

Theorem early_parent_return_phase :
  asep_until_guard base_inv live finished_guard RC RP
    (owned_interp (as_cfg early6)) (as_global early6).
Proof.
  pose proof early_inv_init as Hinv.
  apply asep_at_inv in Hinv as (Hok & _ & Hbase & HC & HP).
  unfold asep_until_guard; right; right.
  apply (asep_sat_intro _ _ _ early6), asep_at_intro;
    [exact Hok|exact Hbase| |exact HP].
  unfold live; apply ticl_now; split; [exact I|eapply ticl_not_done; exact HC].
Qed.

Lemma early_not_live_live :
  ~ asep_sat base_inv live finished_guard
    (owned_interp (as_cfg early6)) (as_global early6).
Proof.
  intro Hsat; apply asep_sat_inv in Hsat as (s & _ & _ & _ & _ & _ & _ & HP).
  exact HP.
Qed.

Theorem early_until_ret :
  auc (asep_until_guard base_inv live finished_guard RC RP)
    (entails (SSig * unit) true (TICL.Logic.Syntax.CRet (asep_ret base_inv RC RP)))
    (owned_interp (as_cfg early6)) (as_global early6).
Proof.
  pose proof early_inv_init as Hinv.
  apply asep_at_inv in Hinv as (Hok & _ & Hbase & HC & HP).
  apply ticl_au in HC.
  apply asep_auc_ret_compose;
    [exact base_inv_closed|apply asep_pred_ok_entails|exact finished_guard_ok|].
  apply (asep_sat_intro _ _ _ early6), asep_at_intro;
    [exact Hok|exact Hbase|exact HC|apply MatchA; exact HP].
Qed.

End TerminationActiveRegression.


From TICL Require Import Utils.Execution Utils.Relations.
From examples Require Import CSL.Frame.Separation.

Module CommonEGActiveRegression.
#[local] Unset Universe Polymorphism.
Import AlwaysRegression.

Definition initial : AsepState :=
  {| as_cfg := c0; as_global := Pure; as_local := fun _ => Pure |}.

Lemma initial_ok : asep_state_ok initial.
Proof.
  split; [apply admissible_active_erasable, loops_admissible|].
  split; [constructor|intro i; constructor].
Qed.

Fixpoint fair_state (n : nat) : AsepState :=
  match n with
  | 0 => initial
  | S k => asep_advance (fair_state k) (selected fair_exec k) (states fair_exec (S k))
  end.

Definition fair_view_exec : Execution AsepState OwnedAction unit :=
  {| states := fair_state;
     selected := selected fair_exec;
     emitted := emitted fair_exec |}.

Lemma fair_state_cfg n : as_cfg (fair_state n) = states fair_exec n.
Proof. destruct n; reflexivity. Qed.

Definition seen (i : side) (w : World (writerE (CSLObs (nat * nat)))) : Prop :=
  match w with
  | Pure => True
  | Obs (Log (CSLHeap m)) _ =>
      match i with Child => m ≈ region 1 1 | Parent => m ≈ region 2 8 end
  | Obs (Log (CSLEmit e)) _ =>
      indexed_value e = match i with Child => (1, 1) | Parent => (0, 8) end
  | _ => False
  end.

Definition local_pred (i : side) :
  ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) ->
  World (writerE (CSLObs (nat * nat))) -> Prop :=
  entails (SSig * unit) false (TICL.Logic.Syntax.CNow (seen i)).

Lemma projected_heap i c : joined_heap (project i c) = oc_heap c i.
Proof. exact (f_equal fst (owned_joined_state_project i c)). Qed.

Definition fair_resources (s : AsepState) : Prop :=
  AlwaysRegression.Inv (as_cfg s) /\
  oc_heap (as_cfg s) Child ≈ region 1 1 /\
  oc_heap (as_cfg s) Parent ≈ region 2 8.
Definition fair_inv (s : AsepState) : Prop :=
  asep_at fair_resources (local_pred Child) (local_pred Parent) s.

Lemma fair_view_exec_spec :
  (forall n, fair_inv (states fair_view_exec n)) /\
  (forall n, asep_step (states fair_view_exec n) (selected fair_view_exec n)
    (states fair_view_exec (S n))).
Proof.
  apply (execution_invariant_steps
    (fun a s (_ : unit) s' => asep_step s a s') fair_inv fair_view_exec).
  - apply asep_at_intro.
    + exact initial_ok.
    + split; [exact Inv_c0|split; apply peq_refl].
    + unfold local_pred; apply ticl_now; split; [exact I|constructor].
    + unfold local_pred; apply ticl_now; split; [exact I|constructor].
  - intros k Hinv.
    apply asep_at_inv in Hinv as (Hok & _ & (HI & HC & HP) & TC & TP).
    rewrite fair_state_cfg in HI, HC, HP.
    pose proof HI as (_ & HcellC & HcellP & _).
    pose proof (run_step k HcellC HcellP) as Hstep.
    assert (HS : asep_step (fair_state k) (selected fair_exec k) (fair_state (S k))).
    { split; [rewrite !fair_state_cfg; exact Hstep|reflexivity]. }
    split; [exact HS|].
    pose proof (asep_state_ok_step _ _ _ Hok HS) as Hok'.
    assert (Hregions : oc_heap (states fair_exec (S k)) Child ≈ region 1 1 /\
      oc_heap (states fair_exec (S k)) Parent ≈ region 2 8).
    { change (oc_heap (snd (run k)) Child ≈ region 1 1) in HC.
      change (oc_heap (snd (run k)) Parent ≈ region 2 8) in HP.
      change (oc_heap
        (snd (let '(p, c) := run k in
          (next_pos p, set_pool (pos_cfg p c) (pool_of (next_pos p))))) Child ≈ region 1 1 /\
        oc_heap
        (snd (let '(p, c) := run k in
          (next_pos p, set_pool (pos_cfg p c) (pool_of (next_pos p))))) Parent ≈ region 2 8).
      destruct (run k) as [p c]; cbn [snd] in HC, HP |- *.
      pose proof (managed_heap_ext _ _ HC) as EC.
      pose proof (managed_heap_ext _ _ HP) as EP.
      destruct p;
        cbn [pos_cfg pos_phase pos_owner side_cell phase_cfg set_pool oc_heap
          set_heap side_upd side_eqb emit_cfg];
        rewrite ?EC, ?EP; split; try apply peq_refl; apply upd_region. }
    apply ticl_now in TC as [TC _]; apply ticl_now in TP as [TP _].
    assert (HH : forall i, seen i (as_local (fair_state k) i)).
    { intros []; assumption. }
    assert (Hseen : forall i, seen i (as_local (fair_state (S k)) i)).
    { intro i.
      change (seen i
        (if side_eqb (owner (selected fair_exec k)) i then
           after_logs
             (action_logs (project_action i (as_cfg (fair_state k))
               (selected fair_exec k))
               (joined_heap (project i (states fair_exec (S k)))))
             (as_local (fair_state k) i)
         else as_local (fair_state k) i)).
      rewrite fair_state_cfg; cbn [selected fair_exec].
      destruct (fst (run k)); destruct i;
        cbn [pos_owner pos_kind pos_phase phase_kind side_cell act owner side_eqb
          project_action action_kind action_logs erase_action_label label_logs
          List.flat_map app after_logs seen indexed_value];
        try reflexivity; try apply HH.
      all: rewrite projected_heap; tauto. }
    apply asep_at_intro.
    + exact Hok'.
    + unfold fair_resources; rewrite fair_state_cfg.
      split; [exact (Inv_closed _ _ _ HI Hstep)|exact Hregions].
    + unfold local_pred; apply ticl_now; split;
        [apply Hseen|exact (proj2 (proj2 Hok') Child)].
    + unfold local_pred; apply ticl_now; split;
        [apply Hseen|exact (proj2 (proj2 Hok') Parent)].
Qed.

Lemma fair_view_exec_valid :
  execution_valid (fun a s (_ : unit) s' => asep_step s a s') (eq initial) fair_view_exec.
Proof. split; [reflexivity|exact (proj2 fair_view_exec_spec)]. Qed.

Lemma fair_local_assertions n : fair_inv (fair_state n).
Proof. exact (proj1 fair_view_exec_spec n). Qed.

(* Each witness is an emit position of this very phase cycle, rather than
   merely a position belonging to the requested owner. *)
Lemma fair_owner_visible i :
  infinitely (fun n =>
    owner_visible i (as_cfg (states fair_view_exec n)) (selected fair_view_exec n)
      (as_cfg (states fair_view_exec (S n)))).
Proof.
  intro n.
  cbn [states selected fair_view_exec]; setoid_rewrite fair_state_cfg.
  assert (H : exists k,
    pos_owner (Nat.iter k next_pos (fst (run n))) = i /\
    pos_phase (Nat.iter k next_pos (fst (run n))) = Some PE).
  { destruct i, (fst (run n));
      solve [exists 0; split; reflexivity | exists 1; split; reflexivity
        | exists 2; split; reflexivity | exists 3; split; reflexivity
        | exists 4; split; reflexivity | exists 5; split; reflexivity
        | exists 6; split; reflexivity | exists 7; split; reflexivity]. }
  destruct H as (k & Ho & He).
  exists (k + n); split; [lia|].
  unfold owner_visible.
  assert (Epos : fst (run (k + n)) = Nat.iter k next_pos (fst (run n))).
  { unfold run; rewrite Nat.iter_add.
    apply Nat.iter_swap_gen; intros [p c]; reflexivity. }
  cbn [selected fair_exec]; rewrite Epos.
  split; [exact Ho|].
  unfold pos_kind; rewrite He.
  destruct (pos_owner (Nat.iter k next_pos (fst (run n)))); discriminate.
Qed.

Theorem common_visible_execution_eg :
  egc (asep_sat fair_resources (local_pred Child) (local_pred Parent))
    (owned_interp c0) Pure /\
  asep_sat fair_resources (egc (local_pred Child)) (egc (local_pred Parent))
    (owned_interp c0) Pure.
Proof.
  apply (asep_egc_run fair_resources (local_pred Child) (local_pred Parent) initial fair_view_exec).
  - apply asep_pred_ok_entails.
  - apply asep_pred_ok_entails.
  - exact fair_view_exec_valid.
  - exact fair_local_assertions.
  - exact fair_owner_visible.
Qed.

Theorem silent_reads_are_not_visible_recurrence :
  infinitely (fun n =>
    owner (selected SilentReadTiclRegression.read_forever n) = Parent) /\
  ~ infinitely (fun n =>
    erase_action_label (selected SilentReadTiclRegression.read_forever n)
      (joined_heap (states SilentReadTiclRegression.read_forever (S n))) <> None).
Proof.
  split.
  - intro n.
    destruct (SilentReadTiclRegression.read_forever_infinitely_reads n)
      as (k & Hle & Hread).
    exists k; split; [exact Hle|rewrite Hread; reflexivity].
  - exact SilentReadTiclRegression.read_forever_not_infinitely_visible.
Qed.

End CommonEGActiveRegression.


Module TransientActiveRegression.

Definition child : CProg unit := CEmit 1 1.
Definition parent : CProg unit :=
  CBind (CEmit 2 1) (fun _ =>
    CBind (CEmit 2 0) (fun _ => CoCSLSyntax.CRet tt)).
Definition cfg := init_owned child parent (region 1 3) (region 2 5) []%list 0.
Definition initial : AsepState :=
  {| as_cfg := cfg; as_global := Pure; as_local := fun _ => Pure |}.

Definition emit_head (payload : nat * nat) (k : thread sE Bn) : thread sE Bn :=
  Vis (inr1 (inr1 (inr1 (inr1 (Log payload)))) : CEff unit) (fun _ => k).
Definition tc := emit_head (1,1) (Ret tt).
Definition tp1 := emit_head (2,0) (Ret tt).
Definition tp0 := emit_head (2,1) tp1.

Lemma child_head : denote child ≅ tc.
Proof. exact (source_raw_emit_head 1 1 (fun _ => Ret tt)). Qed.
Lemma parent_head : denote parent ≅ tp0.
Proof.
  unfold parent, denote at 1; rewrite source_raw_bind, source_raw_emit_head.
  unfold tp0, emit_head at 1; apply vis_equ_node; intros [].
  rewrite source_raw_bind, source_raw_emit_head.
  unfold tp1, emit_head; apply vis_equ_node; intros [].
  rewrite source_raw_ret; reflexivity.
Qed.

Lemma initial_ok : asep_state_ok initial.
Proof.
  split.
  - apply admissible_active_erasable, admissible_intro;
      try apply managed_wf_preallocated; try (apply region_disj; lia);
      cbn [child parent component_ok prog_ok addr_ok]; repeat split; intros; exact I.
  - split; [constructor|intros []; constructor].
Qed.

(** The seven finite phases record existing owned actions, not a scheduler.
    In particular, P3 is the sole unfocused selection frontier. *)
Inductive phase := P0 | P1 | P2 | P3 | P4 | P5 | P6.
Definition c0 := init_owned_threads tc tp0 (region 1 3) (region 2 5) []%list 0.
Definition c1 := set_pool (emit_cfg c0 Parent (2,1))
  (mk_pool 2 [tc;tp1]%vector [Child;Parent]%vector (Some (Fin.FS Fin.F1))).
Definition c2 := set_pool (emit_cfg c1 Parent (2,0))
  (mk_pool 2 [tc;Ret tt]%vector [Child;Parent]%vector (Some (Fin.FS Fin.F1))).
Definition c3 := set_pool c2 (mk_pool 1 [tc]%vector [Child]%vector None).
Definition c4 := set_pool c3 (mk_pool 1 [tc]%vector [Child]%vector (Some Fin.F1)).
Definition c5 := set_pool (emit_cfg c4 Child (1,1))
  (mk_pool 1 [Ret tt]%vector [Child]%vector (Some Fin.F1)).
Definition c6 := set_pool c5 (mk_pool 0 []%vector []%vector None).
Definition phase_cfg ph :=
  match ph with P0 => c0 | P1 => c1 | P2 => c2 | P3 => c3
  | P4 => c4 | P5 => c5 | P6 => c6 end.
Definition next ph :=
  match ph with P0 => P1 | P1 => P2 | P2 => P3 | P3 => P4
  | P4 => P5 | P5 => P6 | P6 => P6 end.
Definition phase_action ph :=
  match ph with
  | P0 => act Parent (OAEmit (2,1) 0)
  | P1 => act Parent (OAEmit (2,0) 1)
  | P2 => act Parent OAReturn
  | P3 => act Child OASelect
  | P4 => act Child (OAEmit (1,1) 2)
  | P5 | P6 => act Child OAReturn
  end.
Definition emission (p : nat * nat) (n : nat) : World (writerE (CSLObs (nat * nat))) :=
  Obs (Log (CSLEmit (stamp p n))) tt.
Definition local_child ph : World (writerE (CSLObs (nat * nat))) :=
  match ph with P5 | P6 => emission (1,1) 0 | _ => Pure end.
Definition local_parent ph : World (writerE (CSLObs (nat * nat))) :=
  match ph with P0 => Pure | P1 => emission (2,1) 0 | _ => emission (2,0) 1 end.
Definition global_world ph : World (writerE (CSLObs (nat * nat))) :=
  match ph with P0 => Pure | P1 => emission (2,1) 0
  | P5 | P6 => emission (1,1) 2 | _ => emission (2,0) 1 end.

Definition phase_view (ph : phase) : AsepState :=
  {| as_cfg := phase_cfg ph; as_global := global_world ph;
     as_local := fun i => match i with Child => local_child ph | Parent => local_parent ph end |}.

Lemma cfg_equ_c0 : owned_equ cfg c0.
Proof.
  split.
  - apply tp_equ_mk; split.
    + intros j; dependent destruction j; [exact child_head|].
      dependent destruction j; [exact parent_head|inversion j].
    + split; reflexivity.
  - repeat split; intros []; reflexivity.
Qed.

Lemma replace_equ c n (v : pool sE Bn n) g f j t u :
  t ≅ u ->
  owned_equ (set_pool c (mk_pool n (v @ j := t) g f))
    (set_pool c (mk_pool n (v @ j := u) g f)).
Proof.
  intro H; apply set_pool_equ; [reflexivity|apply tp_equ_mk].
  split; [apply vector_replace_pointwise; [intros; reflexivity|exact H]|split; reflexivity].
Qed.

Lemma finite_step ph a c' : owned_step (phase_cfg ph) a c' ->
  ph <> P6 /\ a = phase_action ph /\ owned_equ c' (phase_cfg (next ph)).
Proof.
  destruct ph; cbn [phase_cfg next phase_action]; intro H.
  - apply (owned_step_focus c0 1 [tc;tp0]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) a c' eq_refl) in H.
    apply (focus_step_head_prim c0 1 [tc;tp0]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) _ _ 0 a c' (reflexivity _)) in H
      as (k & kind & y & d & Hk & Hp & -> & ->).
    cbn [prim_step emit_prim] in Hp; injection Hp as <- <- <-.
    split; [discriminate|split; [reflexivity|]].
    change (owned_equ
      (set_pool (emit_cfg c0 Parent (2,1))
        (mk_pool 2 ([tc;tp0]%vector @ Fin.FS Fin.F1 := k tt) [Child;Parent]%vector (Some (Fin.FS Fin.F1))))
      (set_pool (emit_cfg c0 Parent (2,1))
        (mk_pool 2 ([tc;tp0]%vector @ Fin.FS Fin.F1 := tp1) [Child;Parent]%vector (Some (Fin.FS Fin.F1))))).
    apply replace_equ, Hk.
  - apply (owned_step_focus c1 1 [tc;tp1]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) a c' eq_refl) in H.
    apply (focus_step_head_prim c1 1 [tc;tp1]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) _ _ 0 a c' (reflexivity _)) in H
      as (k & kind & y & d & Hk & Hp & -> & ->).
    cbn [prim_step emit_prim] in Hp; injection Hp as <- <- <-.
    split; [discriminate|split; [reflexivity|]].
    change (owned_equ
      (set_pool (emit_cfg c1 Parent (2,0))
        (mk_pool 2 ([tc;tp1]%vector @ Fin.FS Fin.F1 := k tt) [Child;Parent]%vector (Some (Fin.FS Fin.F1))))
      (set_pool (emit_cfg c1 Parent (2,0))
        (mk_pool 2 ([tc;tp1]%vector @ Fin.FS Fin.F1 := Ret tt) [Child;Parent]%vector (Some (Fin.FS Fin.F1))))).
    apply replace_equ, Hk.
  - apply (owned_step_focus c2 1 [tc;Ret tt]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) a c' eq_refl) in H.
    apply (focus_step_head_ret c2 1 [tc;Ret tt]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) 0 a c' (reflexivity _)) in H as [-> ->].
    split; [discriminate|split; reflexivity].
  - apply (owned_step_sel c3 0 [tc]%vector [Child]%vector a c' eq_refl) in H
      as (j & -> & ->).
    dependent destruction j; [|inversion j].
    split; [discriminate|split; reflexivity].
  - apply (owned_step_focus c4 0 [tc]%vector [Child]%vector Fin.F1 a c' eq_refl) in H.
    apply (focus_step_head_prim c4 0 [tc]%vector [Child]%vector Fin.F1
      _ _ 0 a c' (reflexivity _)) in H
      as (k & kind & y & d & Hk & Hp & -> & ->).
    cbn [prim_step emit_prim] in Hp; injection Hp as <- <- <-.
    split; [discriminate|split; [reflexivity|]].
    change (owned_equ
      (set_pool (emit_cfg c4 Child (1,1))
        (mk_pool 1 ([tc]%vector @ Fin.F1 := k tt) [Child]%vector (Some Fin.F1)))
      (set_pool (emit_cfg c4 Child (1,1))
        (mk_pool 1 ([tc]%vector @ Fin.F1 := Ret tt) [Child]%vector (Some Fin.F1)))).
    apply replace_equ, Hk.
  - apply (owned_step_focus c5 0 [Ret tt]%vector [Child]%vector Fin.F1 a c' eq_refl) in H.
    apply (focus_step_head_ret c5 0 [Ret tt]%vector [Child]%vector Fin.F1
      0 a c' (reflexivity _)) in H as [-> ->].
    split; [discriminate|split; reflexivity].
  - change False in H; contradiction.
Qed.

Lemma finite_step_exists ph : ph <> P6 ->
  owned_step (phase_cfg ph) (phase_action ph) (phase_cfg (next ph)).
Proof.
  destruct ph; intro Hlast.
  - apply (owned_step_focus c0 1 [tc;tp0]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) _ _ eq_refl).
    apply (focus_step_head_prim c0 1 [tc;tp0]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) _ _ 0 _ _ (reflexivity _)).
    exists (fun _ => tp1), (OAEmit (2,1) 0), tt, (emit_cfg c0 Parent (2,1));
      repeat split; reflexivity.
  - apply (owned_step_focus c1 1 [tc;tp1]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) _ _ eq_refl).
    apply (focus_step_head_prim c1 1 [tc;tp1]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) _ _ 0 _ _ (reflexivity _)).
    exists (fun _ => Ret tt), (OAEmit (2,0) 1), tt, (emit_cfg c1 Parent (2,0));
      repeat split; reflexivity.
  - apply (owned_step_focus c2 1 [tc;Ret tt]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) _ _ eq_refl).
    apply (focus_step_head_ret c2 1 [tc;Ret tt]%vector [Child;Parent]%vector
      (Fin.FS Fin.F1) 0 _ _ (reflexivity _)); split; reflexivity.
  - apply (owned_step_sel c3 0 [tc]%vector [Child]%vector _ _ eq_refl).
    exists Fin.F1; split; reflexivity.
  - apply (owned_step_focus c4 0 [tc]%vector [Child]%vector Fin.F1 _ _ eq_refl).
    apply (focus_step_head_prim c4 0 [tc]%vector [Child]%vector Fin.F1
      _ _ 0 _ _ (reflexivity _)).
    exists (fun _ => Ret tt), (OAEmit (1,1) 2), tt, (emit_cfg c4 Child (1,1));
      repeat split; reflexivity.
  - apply (owned_step_focus c5 0 [Ret tt]%vector [Child]%vector Fin.F1 _ _ eq_refl).
    apply (focus_step_head_ret c5 0 [Ret tt]%vector [Child]%vector Fin.F1
      0 _ _ (reflexivity _)); split; reflexivity.
  - contradiction.
Qed.

Lemma phase_view_step ph : ph <> P6 ->
  asep_step (phase_view ph) (phase_action ph) (phase_view (next ph)).
Proof.
  intro Hlast; split; [apply finite_step_exists; exact Hlast|].
  destruct ph; try contradiction; unfold phase_view, asep_advance;
    cbn [phase_cfg next phase_action global_world local_child local_parent
      project_action action_logs erase_action_label owner action_kind side_eqb
      after_logs label_logs act oc_base oc_count global_count];
    f_equal; apply functional_extensionality; intros []; reflexivity.
Qed.

Lemma phase_advance c ph : owned_equ c (phase_cfg ph) -> ph <> P6 ->
  exists c', owned_step c (phase_action ph) c' /\ owned_equ c' (phase_cfg (next ph)).
Proof.
  intros E Hlast; symmetry in E.
  destruct (owned_step_equ _ _ _ _ E (finite_step_exists ph Hlast)) as (d & Hd & Ed).
  exists d; split; [exact Hd|symmetry; exact Ed].
Qed.

Theorem concrete_action_order : exists d1 d2 d3 d4 d5 d6,
  owned_step cfg (act Parent (OAEmit (2,1) 0)) d1 /\
  owned_step d1 (act Parent (OAEmit (2,0) 1)) d2 /\
  owned_step d2 (act Parent OAReturn) d3 /\
  owned_step d3 (act Child OASelect) d4 /\
  owned_step d4 (act Child (OAEmit (1,1) 2)) d5 /\
  owned_step d5 (act Child OAReturn) d6.
Proof.
  destruct (phase_advance cfg P0 cfg_equ_c0 ltac:(discriminate)) as (d1 & H1 & E1).
  destruct (phase_advance d1 P1 E1 ltac:(discriminate)) as (d2 & H2 & E2).
  destruct (phase_advance d2 P2 E2 ltac:(discriminate)) as (d3 & H3 & E3).
  destruct (phase_advance d3 P3 E3 ltac:(discriminate)) as (d4 & H4 & E4).
  destruct (phase_advance d4 P4 E4 ltac:(discriminate)) as (d5 & H5 & E5).
  destruct (phase_advance d5 P5 E5 ltac:(discriminate)) as (d6 & H6 & E6).
  exists d1, d2, d3, d4, d5, d6.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

Definition phase_inv (s : AsepState) : Prop := exists ph,
  owned_equ (as_cfg s) (phase_cfg ph) /\
  as_local s Child = local_child ph /\
  as_local s Parent = local_parent ph /\
  as_global s = global_world ph.

Lemma phase_inv_init : phase_inv initial.
Proof. exists P0; split; [exact cfg_equ_c0|repeat split; reflexivity]. Qed.

Lemma phase_inv_closed : asep_closed phase_inv.
Proof.
  intros s a s' _ (ph & E & EC & EP & EW) [Hs Eupdate].
  destruct (owned_step_equ _ _ _ _ E Hs) as (d & Hd & Ed).
  destruct (finite_step ph a d Hd) as (Hlast & Ha & En).
  exists (next ph); split; [etransitivity; eassumption|].
  pose proof E as (_ & _ & _ & _ & Ebase & Ecount & _).
  split; [|split].
  - rewrite Eupdate; cbn [asep_advance as_local]; rewrite EC, Ha.
    destruct ph; try contradiction;
      cbn [next phase_action local_child action_logs project_action erase_action_label
        owner action_kind side_eqb after_logs label_logs act];
      unfold emission; rewrite ?Ebase, ?Ecount; reflexivity.
  - rewrite Eupdate; cbn [asep_advance as_local]; rewrite EP, Ha.
    destruct ph; try contradiction;
      cbn [next phase_action local_parent action_logs project_action erase_action_label
        owner action_kind side_eqb after_logs label_logs act];
      unfold emission; rewrite ?Ebase, ?Ecount; reflexivity.
  - rewrite Eupdate; cbn [asep_advance as_global]; rewrite EW, Ha.
    destruct ph; try contradiction;
      cbn [next phase_action global_world action_logs erase_action_label
        action_kind after_logs label_logs act]; reflexivity.
Qed.

Definition seen (payload : nat * nat) (w : World (writerE (CSLObs (nat * nat)))) : Prop :=
  match w with Obs (Log (CSLEmit e)) _ => indexed_value e = payload | _ => False end.
Definition endpoint (payload : nat * nat) :
  ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> World (writerE (CSLObs (nat * nat))) -> Prop :=
  entails (SSig * unit) false (CNow (seen payload)).

Lemma phase_inv_inv s : phase_inv s -> exists ph,
  owned_equ (as_cfg s) (phase_cfg ph) /\
  as_local s Child = local_child ph /\
  as_local s Parent = local_parent ph /\
  as_global s = global_world ph /\
  (endpoint (1,1) (owned_interp (project Child (as_cfg s))) (as_local s Child)
    <-> ph = P5 \/ ph = P6) /\
  (endpoint (2,1) (owned_interp (project Parent (as_cfg s))) (as_local s Parent)
    <-> ph = P1).
Proof.
  intros (ph & E & EC & EP & EW).
  exists ph; refine (conj E (conj EC (conj EP (conj EW (conj _ _))))).
  - unfold endpoint; rewrite ticl_now, EC.
    destruct ph; cbn [local_child seen emission indexed_value]; split.
    all: try (intros [H _]; contradiction).
    all: try solve [intros [H|H]; discriminate].
    all: try solve [intro H; auto].
    all: intro H; split; [reflexivity|constructor].
  - unfold endpoint; rewrite ticl_now, EP.
    destruct ph; cbn [local_parent seen emission indexed_value]; split.
    all: try solve [intros [H _]; contradiction].
    all: try solve [intros [H _]; discriminate].
    all: try solve [intro H; discriminate].
    all: try solve [intro H; reflexivity].
    all: intro H; split; [reflexivity|constructor].
Qed.

Theorem parent_progress_remembered (s : AsepState) :
  phase_inv s ->
  endpoint (1,1) (owned_interp (project Child (as_cfg s))) (as_local s Child) ->
  oc_count (as_cfg s) Parent = 2 /\
  entails (SSig * unit) false
    (CNow (fun w => w = emission (2,0) 1))
    (owned_interp (project Parent (as_cfg s))) (as_local s Parent) /\
  ~ endpoint (2,1) (owned_interp (project Parent (as_cfg s))) (as_local s Parent).
Proof.
  intros Hinv Hchild.
  destruct (phase_inv_inv s Hinv) as (ph & E & _ & EP & _ & HC & HP).
  apply HC in Hchild.
  pose proof E as (_ & _ & _ & _ & _ & Ecount & _).
  split.
  - destruct Hchild as [Hphase|Hphase]; subst ph; rewrite Ecount; reflexivity.
  - split.
    + apply ticl_now; rewrite EP.
      destruct Hchild as [Hphase|Hphase]; subst ph; split;
        [reflexivity|constructor|reflexivity|constructor].
    + intro Hparent; apply HP in Hparent; subst ph.
      destruct Hchild; discriminate.
Qed.

Lemma initial_local_state i t h ctx base focused :
  joined_state (init_local_thread i t h ctx base focused) = (h,(ctx,base)).
Proof.
  destruct i.
  - change ((h ⊎ managed_empty,(ctx,base + 0 + 0)) = (h,(ctx,base))).
    replace (base + 0 + 0) with base by lia; f_equal; apply managed_heap_ext.
    split; intro x; cbn; unfold hunion;
      [destruct (fst h x)|destruct (snd h x)]; reflexivity.
  - change ((managed_empty ⊎ h,(ctx,base + 0 + 0)) = (h,(ctx,base))).
    replace (base + 0 + 0) with base by lia; f_equal; apply managed_heap_ext.
    split; intro x; reflexivity.
Qed.

Theorem child_local_af :
  entails (SSig * unit) false
    (Cu Q_A (CNow (fun _ => True)) (CNow (seen (1,1))))
    (owned_interp (project Child cfg)) Pure.
Proof.
  rewrite (owned_interp_equ _ _
    (project_init_child child parent (region 1 3) (region 2 5) []%list 0)).
  change (entails (SSig * unit) false
    (Cu Q_A (CNow (fun _ => True)) (CNow (seen (1,1))))
    (interp_schedule_nd sh 1 [denote child]%vector None
      (joined_state (init_local_thread Child (denote child) (region 1 3) []%list 0 false))) Pure).
  rewrite initial_local_state.
  apply (proj2 (au_csl_nd_select (b:=false) 0 [denote child]%vector (region 1 3) []%list 0 Pure
    (CNow (fun _ => True)) (CNow (seen (1,1))))).
  right; split.
  - change (True /\ not_done (Pure : World (writerE (CSLObs (nat * nat))))); split; constructor.
  - intro j; dependent destruction j; [|inversion j].
  change (entails (SSig * unit) false
    (Cu Q_A (CNow (fun _ => True)) (CNow (seen (1,1))))
    (interp_schedule_nd sh 1
      ([Ret tt]%vector @ Fin.F1 := (denote_flow (CEmit 1 1) >>= fun _ => Ret tt))
      (Some Fin.F1) (own 1 3 []%list 0)) Pure).
  rewrite (interp_nd_source_emit_log 0 [Ret tt]%vector Fin.F1 1 1
    (fun _ => Ret tt) (region 1 3) []%list 0).
  apply (af_log (b:=false)); [constructor|].
  cleft; change (seen (1,1) (emission (1,1) 0) /\ not_done (emission (1,1) 0)).
  split; [reflexivity|constructor].
Qed.

Theorem parent_local_af :
  entails (SSig * unit) false
    (Cu Q_A (CNow (fun _ => True)) (CNow (seen (2,1))))
    (owned_interp (project Parent cfg)) Pure.
Proof.
  rewrite (owned_interp_equ _ _
    (project_init_parent child parent (region 1 3) (region 2 5) []%list 0)).
  change (entails (SSig * unit) false
    (Cu Q_A (CNow (fun _ => True)) (CNow (seen (2,1))))
    (interp_schedule_nd sh 1
      ([Ret tt]%vector @ Fin.F1 := (denote_flow parent >>= fun _ => Ret tt))
      (Some Fin.F1)
      (joined_state (init_local_thread Parent (denote parent) (region 2 5) []%list 0 true))) Pure).
  rewrite initial_local_state.
  unfold parent.
  rewrite (interp_nd_source_bind 0 [Ret tt]%vector Fin.F1
    (CEmit 2 1) (fun _ => CBind (CEmit 2 0) (fun _ => CoCSLSyntax.CRet tt))
    (fun _ => Ret tt) (own 2 5 []%list 0)).
  rewrite (interp_nd_source_emit_log 0 [Ret tt]%vector Fin.F1 2 1
    (fun flow => match flow with None => Ret tt | Some _ =>
      denote_flow (CBind (CEmit 2 0) (fun _ => CoCSLSyntax.CRet tt)) >>= fun _ => Ret tt end)
    (region 2 5) []%list 0).
  apply (af_log (b:=false)); [constructor|].
  cleft; change (seen (2,1) (emission (2,1) 0) /\ not_done (emission (2,1) 0)).
  split; [reflexivity|constructor].
Qed.

Lemma no_current_pair (s : AsepState) :
  ~ asep_at phase_inv (endpoint (1,1)) (endpoint (2,1)) s.
Proof.
  intro Hinv; apply asep_at_inv in Hinv as (_ & _ & Hphase & HC & HP).
  destruct (phase_inv_inv s Hphase) as (ph & _ & _ & _ & _ & HCphase & HPphase).
  apply HCphase in HC; apply HPphase in HP; subst ph.
  destruct HC; discriminate.
Qed.

Lemma separated_endpoint_impossible t w :
  ~ asep_sat phase_inv (endpoint (1,1)) (endpoint (2,1)) t w.
Proof.
  intro Hsat; apply asep_sat_inv in Hsat as (s & _ & _ & Hok & _ & HI & HC & HP).
  apply (no_current_pair s), asep_at_intro; assumption.
Qed.

Theorem no_global_ef_separated_transient_endpoints :
  ~ euc (entails (SSig * unit) false (CNow (fun _ => True)))
      (asep_sat phase_inv (endpoint (1,1)) (endpoint (2,1)))
      (owned_interp cfg) Pure.
Proof.
  intro H; apply euc_endpoint_exists in H as (t & w & HE).
  exact (separated_endpoint_impossible t w HE).
Qed.

End TransientActiveRegression.

Module AsyncNextRegression.
Definition cfg : OwnedCfg := set_pool OperationalNextRegression.cfg
  (mk_pool 2 [denote (CWrite 1 4);denote (CWrite 2 6)]%vector
    [Child;Parent]%vector None).
Definition initial : AsepState :=
  {| as_cfg := cfg; as_global := Pure; as_local := fun _ => Pure |}.
Lemma first_action_selects a c : owned_step cfg a c ->
  exists j : Fin.t 2,
    a = act ([Child;Parent]%vector $ j) OASelect /\
    c = set_pool cfg (mk_pool 2
      [denote (CWrite 1 4);denote (CWrite 2 6)]%vector
      [Child;Parent]%vector (Some j)).
Proof. exact (fun H => H). Qed.
Definition yielding := init_owned (CWrite 1 4)
  (CBind CYield (fun _ => CWrite 2 6))
  (region 1 3) (region 2 5) []%list 0.
Lemma yielding_admitted : admissible (CWrite 1 4)
  (CBind CYield (fun _ => CWrite 2 6))
  (region 1 3) (region 2 5) []%list 0.
Proof.
  apply admissible_intro; try apply managed_wf_preallocated;
    try (apply region_disj; discriminate); cbn; repeat split;
      try exact I; try discriminate; intros _; discriminate.
Qed.
Lemma yielding_step : owned_step yielding (act Parent OAYield) cfg.
Proof.
  change (focus_step yielding 1
    [denote (CWrite 1 4);denote (CBind CYield (fun _ => CWrite 2 6))]%vector
    [Child;Parent]%vector (Fin.FS Fin.F1) (act Parent OAYield) cfg).
  right; left; exists (fun _ => denote (CWrite 2 6)); split.
  - exists 0; change (denote (CBind CYield (fun _ => CWrite 2 6)) ≅
      Vis (inl1 Yield : CEff unit) (fun _ => denote (CWrite 2 6))).
    unfold denote at 1; rewrite source_raw_bind; apply source_raw_yield_head.
  - split; reflexivity.
Qed.
Lemma initial_ok : asep_state_ok initial.
Proof.
  split.
  - eapply active_erasable_step; [apply admissible_active_erasable, yielding_admitted|apply yielding_step].
  - split; [constructor|intro i; constructor].
Qed.
Local Abbreviation Pred := (ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) ->
  World (writerE (CSLObs (nat * nat))) -> Prop).
Definition guard : Pred := entails (SSig * unit) false (CNow (fun _ => True)).
Definition post (i v : nat) : SSig * unit -> World (writerE (CSLObs (nat * nat))) -> Prop :=
  fun '(s,_) _ => csl_memory s ≈ region i v /\ snd s = ([]%list,0).
Definition target (i v : nat) : Pred := entails (SSig * unit) true
  (Cx Q_A (CNow (fun _ => True)) (TICL.Logic.Syntax.CRet (post i v))).
Lemma local_run i : owned_interp (project i cfg) ~
  interp_schedule_nd sh 1
    [denote (match i with Child => CWrite 1 4 | Parent => CWrite 2 6 end)]%vector
    None (match i with Child => own 1 3 []%list 0 | Parent => own 2 5 []%list 0 end).
Proof.
  unfold owned_interp; rewrite owned_joined_state_project; destruct i; reflexivity.
Qed.
Lemma focused_write i a v :
  anc guard (entails (SSig * unit) true (TICL.Logic.Syntax.CRet (post i v)))
    (interp_schedule_nd sh 1 [denote (CWrite i v)]%vector (Some Fin.F1)
      (own i a []%list 0)) Pure.
Proof.
  change (target i v (interp_schedule_nd sh 1 [denote (CWrite i v)]%vector
    (Some Fin.F1) (own i a []%list 0)) Pure).
  unfold target.
  change ([denote (CWrite i v)]%vector) with
    (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := denote (CWrite i v)).
  unfold denote, own, region; rewrite interp_nd_source_write_present.
  2: { cbn; rewrite hsingle_eq; discriminate. }
  apply (ax_log (b:=true)); [constructor|].
  rewrite (interp_schedule_nd_ret sh) by reflexivity.
  rewrite (interp_schedule_nd_empty sh).
  apply ret_ret; [constructor|].
  split; [apply upd_region|reflexivity].
Qed.
Lemma unfocused_write i a v : anc guard (target i v)
  (interp_schedule_nd sh 1 [denote (CWrite i v)]%vector None (own i a []%list 0)) Pure.
Proof.
  change (entails (SSig * unit) true
    (Cx Q_A (CNow (fun _ => True))
      (Cx Q_A (CNow (fun _ => True)) (TICL.Logic.Syntax.CRet (post i v))))
    (interp_schedule_nd sh 1 [denote (CWrite i v)]%vector None (own i a []%list 0)) Pure).
  rewrite interp_schedule_nd_select.
  apply (an_brS (b:=true) _ _ Fin.F1); split.
  - csplit; auto with ticl.
  - intro j; dependent destruction j; [ticl_normalize; exact (focused_write i a v)|inversion j].
Qed.
Lemma local_next i : anc guard
  (match i with Child => target 1 4 | Parent => target 2 6 end)
  (owned_interp (project i cfg)) Pure.
Proof.
  destruct i.
  all: eapply asep_pred_transport;
      [apply asep_pred_ok_anc; apply asep_pred_ok_entails
      |symmetry; apply local_run|].
  all: apply unfocused_write.
Qed.
Lemma pair_next :
  anc guard (target 1 4) (owned_interp (project Child cfg)) Pure /\
  anc guard (target 2 6) (owned_interp (project Parent cfg)) Pure.
Proof. split; [exact (local_next Child)|exact (local_next Parent)]. Qed.
Example asynchronous_AN :
  anc (asep_sat (fun _ => True) guard guard)
    (fun t w => asep_sat (fun _ => True) (target 1 4) guard t w \/
      asep_sat (fun _ => True) guard (target 2 6) t w)
    (owned_interp cfg) Pure.
Proof.
  apply asep_anc_compose; try apply asep_pred_ok_entails.
  - exact asep_closed_true.
  - destruct pair_next as [HC HP].
    apply (asep_sat_intro _ _ _ initial), asep_at_intro;
      [exact initial_ok|exact I|exact HC|exact HP].
Qed.
Example asynchronous_EN :
  enc (asep_sat (fun _ => True) guard guard)
    (fun t w => asep_sat (fun _ => True) (target 1 4) guard t w \/
      asep_sat (fun _ => True) guard (target 2 6) t w)
    (owned_interp cfg) Pure.
Proof.
  apply asep_enc_compose; try apply asep_pred_ok_entails.
  - exact asep_closed_true.
  - apply (asep_sat_intro _ _ _ initial), asep_at_intro; [exact initial_ok|exact I| |].
    + destruct (local_next Child) as (HG & (u & v & HT) & HN).
      split; [exact HG|exists u,v; split; [exact HT|apply HN; exact HT]].
    + destruct (local_next Parent) as (HG & (u & v & HT) & HN).
      split; [exact HG|exists u,v; split; [exact HT|apply HN; exact HT]].
Qed.
Lemma local_target_false i :
  ~ (match i with Child => target 1 4 | Parent => target 2 6 end)
      (owned_interp (project i cfg)) Pure.
Proof.
  destruct i; unfold target; rewrite local_run;
    rewrite interp_schedule_nd_select;
    rewrite (an_brS (b:=true) _ _ Fin.F1);
    intros (_ & H); specialize (H Fin.F1);
    apply ticl_ret in H as (x & HR & Hd & Hs & HN).
  - destruct (focused_write 1 3 4) as (_ & (u & v & HT) & HP).
    assert (Hv : not_done v) by (eapply ticl_not_done; exact (HP _ _ HT)).
    specialize (HN _ _ HT); inversion HN; subst; inversion Hv.
  - destruct (focused_write 2 5 6) as (_ & (u & v & HT) & HP).
    assert (Hv : not_done v) by (eapply ticl_not_done; exact (HP _ _ HT)).
    specialize (HN _ _ HT); inversion HN; subst; inversion Hv.
Qed.
Lemma retained_foreign_excludes_targets t w (s : AsepState) :
  ktrans (owned_interp cfg) Pure t w -> not_done w ->
  asep_frontier initial s -> t ~ owned_interp (as_cfg s) -> w = as_global s ->
  (owned_interp (project Child (as_cfg s)) ~ owned_interp (project Child cfg) /\
     as_local s Child = Pure \/
   owned_interp (project Parent (as_cfg s)) ~ owned_interp (project Parent cfg) /\
     as_local s Parent = Pure) ->
  ~ asep (local_obligation Child (target 1 4) s)
      (local_obligation Parent (target 2 6) s) (joined_heap (as_cfg s)).
Proof.
  intros HT Hw Hfront Et Ew Hforeign HI.
  pose proof (asep_closed_frontier (fun _ => True) initial s
    asep_closed_true initial_ok I Hfront) as [Hok _].
  apply (proj1 (asep_local_pinned s _ _ (proj1 (proj1 (proj1 Hok))))) in HI.
  destruct Hforeign as [[E W]|[E W]], HI as [TC TP].
  - apply (local_target_false Child).
    rewrite W in TC.
    eapply asep_pred_transport; [apply asep_pred_ok_entails|exact E|exact TC].
  - apply (local_target_false Parent).
    rewrite W in TP.
    eapply asep_pred_transport; [apply asep_pred_ok_entails|exact E|exact TP].
Qed.
Example global_next_retains_failed_target t w :
  ktrans (owned_interp cfg) Pure t w -> not_done w ->
  exists s, asep_frontier initial s /\ t ~ owned_interp (as_cfg s) /\
    w = as_global s /\
    ~ asep (local_obligation Child (target 1 4) s)
        (local_obligation Parent (target 2 6) s) (joined_heap (as_cfg s)).
Proof.
  intros HT Hw.
  destruct (asep_visible_forward_owner initial t w initial_ok HT Hw)
    as (s & u & i & Hfront & Et & Ew & HC).
  exists s; split; [exact Hfront|split; [exact Et|split; [exact Ew|]]].
  eapply retained_foreign_excludes_targets;
    [exact HT|exact Hw|exact Hfront|exact Et|exact Ew|].
  destruct i; [right|left]; exact (proj2 (proj2 HC)).
Qed.
Lemma one_action_excludes_both a d : owned_step cfg a d ->
  ~ asep (local_obligation Child (target 1 4) (asep_advance initial a d))
      (local_obligation Parent (target 2 6) (asep_advance initial a d))
      (joined_heap d).
Proof.
  intros HS HI.
  apply (proj1 (asep_local_pinned (asep_advance initial a d) _ _
    (proj1 (proj1 (active_erasable_step cfg a d (proj1 initial_ok) HS))))) in HI.
  destruct HI as [HC HP]; destruct (owner a) eqn:HO.
  - assert (E : owned_interp (project Parent d) ~ owned_interp (project Parent cfg)).
    { apply owned_interp_equ, (owned_step_foreign Parent cfg a d);
        [exact HS|rewrite HO; discriminate]. }
    cbn [asep_advance as_local initial] in HP; rewrite HO in HP; cbn [side_eqb] in HP.
    rewrite E in HP; exact (local_target_false Parent HP).
  - assert (E : owned_interp (project Child d) ~ owned_interp (project Child cfg)).
    { apply owned_interp_equ, (owned_step_foreign Child cfg a d);
        [exact HS|rewrite HO; discriminate]. }
    cbn [asep_advance as_local initial] in HC; rewrite HO in HC; cbn [side_eqb] in HC.
    rewrite E in HC; exact (local_target_false Child HC).
Qed.
Lemma no_initial_silent d : ~ silent_next cfg d.
Proof.
  intros (a & HS & HL).
  destruct (first_action_selects a d HS) as (j & -> & _).
  discriminate HL.
Qed.
Lemma initial_silent_refl d : clos_refl_trans _ silent_next cfg d -> d = cfg.
Proof.
  intro H; apply clos_rt_rt1n in H; destruct H as [|y z Hfirst Hrest].
  - reflexivity.
  - exfalso; exact (no_initial_silent y Hfirst).
Qed.
Example global_next_exactly_one_action t w :
  ktrans (owned_interp cfg) Pure t w -> not_done w ->
  exists a d, owned_step cfg a d /\ asep_step initial a (asep_advance initial a d) /\
    t ~ owned_interp d /\ w = as_global (asep_advance initial a d) /\
    ~ asep (local_obligation Child (target 1 4) (asep_advance initial a d))
        (local_obligation Parent (target 2 6) (asep_advance initial a d))
        (joined_heap d).
Proof.
  intros HT Hw.
  destruct (owned_ktrans_forward cfg Pure t w (proj1 (proj1 initial_ok))
    ltac:(constructor) HT Hw) as (d & a & d' & l & Hsil & HS & HL & ET & EW).
  apply initial_silent_refl in Hsil; subst d.
  exists a, d'; split; [exact HS|split].
  - split; [exact HS|reflexivity].
  - split; [exact ET|split; [exact EW|exact (one_action_excludes_both a d' HS)]].
Qed.
End AsyncNextRegression.
