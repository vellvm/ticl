From TICL Require Import CTree.Interp.Yield.Policy.
(** * Shared material for the two-process frame regressions.

    Two processes own cells [1] and [2].  Each process's facts are proved
    standalone on its own region ([own]) and transported to the shared heap by
    framing with the other region ([work_af_framed], [write_ax_done_framed]).
    The AF/AN/AG files join these through the cooperative prefix equation. *)
From Stdlib Require Import Fin Vector List Arith.PeanoNat Lia.
From Coinduction Require Import all.
From TICL Require Export
  CTree.Core
  CTree.Trace
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.Bind
  CTree.Logic.Sim
  CTree.Interp.State.Mod
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.Nondeterministic
  CTree.Interp.CSL.Mod
  CTree.Interp.Refine
  Logic.Core
  Lang.CoCSL.Mod
  Lang.CoCSL.Frame
  Lang.CoCSL.Sequential
  Utils.Pcm.

Export CTreeNotations TiclNotations VectorNotations.
Import ListNotations.
Global Open Scope ctree_scope.
Global Open Scope ticl_scope.
Global Open Scope fin_vector_scope.
Global Open Scope pcm_scope.

(** Close a returning [AF ret] goal at a [not_done] world. *)
Ltac close_ret :=
  cleft; apply ret_ret; [auto with ticl|].
(** Run the focused slot's yield-free head standalone after exposing its replacement. *)
Ltac rr_prefix free := rewrite interp_rr_bind; rewrite run_rr_prefix by apply free.
(** Run the nondeterministic focused slot's yield-free head standalone. *)
Ltac nd_prefix free := rewrite interp_nd_source_bind; rewrite run_nd_prefix by apply free.

(** ** Programs *)
(** Read, increment, write, and emit one owned cell. *)
Definition work (i : nat) : CProg unit :=
  CBind (CRead i) (fun v => CBind (CWrite i (S v)) (fun _ => CEmit i (S v))).
(** Perform work, yield once, and return. *)
Definition proc (i : nat) : CProg unit := CBind (work i) (fun _ => CBind CYield (fun _ => CRet tt)).
(** Write one, yield once, and return. *)
Definition wproc (i : nat) : CProg unit := CBind (CWrite i 1) (fun _ => CBind CYield (fun _ => CRet tt)).
(** One iteration of the looping worker: work, yield, and continue. *)
Definition lproc_body (i : nat) : CProg (option unit) :=
  CBind (work i) (fun _ => CBind CYield (fun _ => CRet (Some tt))).
(** Repeat the yielding worker indefinitely. *)
Definition lproc (i : nat) : CProg unit := CUntilNone (lproc_body i).
(** Fork one program and continue with the other. *)
Definition fork2 (p1 p2 : CProg unit) : CProg unit := CBind (CFork p1) (fun _ => p2).

(** ** Regions and states *)
(** A single owned cell with no managed allocation extent. *)
Definition region (i a : nat) : ManagedHeap := (hsingle i a, hemp).
(** A process state containing only its own cell. *)
Definition own (i a : nat) (ctx : Ctx.Ctx) (c : nat) : SSig := (region i a, (ctx, c)).
(** Two disjoint cells with shared context and emission counter. *)
Definition shared (a b : nat) (ctx : Ctx.Ctx) (c : nat) : SSig := (region 1 a ⊎ region 2 b, (ctx, c)).
(** The managed heap consists of exactly the two owned regions. *)
Definition both (a b : nat) (m : ManagedHeap) : Prop := m ≈ region 1 a ⊎ region 2 b.

(** A singleton heap contains its own cell. *)
Lemma hsingle_eq i a : hsingle i a i = Some a.
Proof. unfold hsingle; destruct (Nat.eq_dec i i); congruence. Qed.

(** A singleton heap is empty at any distinct address. *)
Lemma hsingle_neq i j a : i <> j -> hsingle i a j = None.
Proof. unfold hsingle; destruct (Nat.eq_dec i j); congruence. Qed.

(** Distinct singleton regions are disjoint. *)
Lemma region_disj i j a b : i <> j -> region i a # region j b.
Proof.
  intro Hij; split; cbn.
  - intro x; destruct (Nat.eq_dec i x); [right; subst; apply hsingle_neq; auto|left; apply hsingle_neq; auto].
  - intro x; left; reflexivity.
Qed.


(** A process region is well formed and disjoint from another cell. *)
Lemma region_frame_inv i j a b ctx c : i <> j -> frame_inv (region j b) (own i a ctx c).
Proof. intro; split; [apply region_disj; auto|apply managed_wf_preallocated]. Qed.

(** [upd] on a single-cell region is the region at the new value. *)
Lemma upd_region i a v : (upd (fst (region i a)) i v, snd (region i a)) ≈ region i v.
Proof.
  split; cbn; [|intro; reflexivity].
  intro x; unfold upd, hsingle; destruct (Nat.eq_dec i x); subst;
    [rewrite Nat.eqb_refl|rewrite (proj2 (Nat.eqb_neq x i)) by auto]; reflexivity.
Qed.


(** ** Standalone process facts *)
(** Standalone work returns its incremented region and one stamped emission. *)
Definition Qwork (i a : nat) (ctx : Ctx.Ctx) (c : nat)
  : SSig * option unit -> World (writerE (CSLObs (nat * nat))) -> Prop :=
  fun '(s', r) w' => r = Some tt /\ csl_memory s' ≈ region i (S a) /\ snd s' = (ctx, S c) /\
                     w' = Obs (Log (CSLEmit (stamp (i, S a) c))) tt.

(** The standalone worker reads, writes, and emits in order. *)
Lemma work_run i a (memory : ManagedHeap) ctx c :
  fst memory i = Some a ->
  instr_flow_erased (work i) (memory, (ctx, c)) ~
  (emit_list [CSLHeap (upd (fst memory) i (S a), snd memory);
              CSLEmit (stamp (i, S a) c)]%list
   (Ret (((upd (fst memory) i (S a), snd memory), (ctx, S c)), Some tt))
    : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)).
Proof.
  intro HV; unfold work.
  rewrite instr_flow_read with (v := a) by exact HV.
  rewrite instr_flow_write; [|cbn; rewrite HV; discriminate].
  cbn [csl_memory fst snd].
  rewrite emit_list_cons; unfold log at 1; rewrite bind_vis; setoid_rewrite bind_ret_l.
  apply sb_vis; intros [].
  rewrite instr_flow_head with (e := inr1 (inr1 (Log (i, S a)))) (k := fun _ => Ret (Some tt)).
  2:{ cbn [denote_flow]; unfold CTree.trigger; rewrite bind_vis; step; constructor; intro;
      rewrite bind_ret_l; reflexivity. }
  cbn [sh h_sum csl_emit_handler csl_counter csl_context csl_memory fst snd].
  unfold emit_list; cbn [List.fold_right].
  unfold log, CTree.trigger; rewrite !bind_bind; setoid_rewrite bind_ret_l.
  setoid_rewrite interp_state_thread_ret.
  reflexivity.
Qed.

(** Standalone work eventually returns its postcondition. *)
Lemma work_af_ret i a ctx c w : not_done w ->
  <( {instr_flow_erased (work i) (own i a ctx c)}, w |=R AF ret {Qwork i a ctx c} )>.
Proof.
  intro Hw; ticl_normalize; unfold own; rewrite work_run by apply hsingle_eq.
  apply (af_log (b:=true)); [exact Hw|].
  apply (af_log (b:=true)); [constructor|].
  close_ret.
  split; [reflexivity|split; [apply upd_region|split; reflexivity]].
Qed.

(** The original eventual terminal claim follows through the final value transition. *)
Lemma work_af i a ctx c w : not_done w ->
  auc (entails _ false (CNow (fun _ => True)))
    (fun _ wd => done_with (Qwork i a ctx c) wd)
    (instr_flow_erased (work i) (own i a ctx c)) w.
Proof. intro Hw; apply af_ret_done, work_af_ret; exact Hw. Qed.

(** A standalone write preserves context and counter and records its post-memory. *)
Definition Qwrite (i : nat) (ctx : Ctx.Ctx) (c : nat)
  : SSig * option unit -> World (writerE (CSLObs (nat * nat))) -> Prop :=
  fun '(s', r) w' => r = Some tt /\ csl_memory s' ≈ region i 1 /\ snd s' = (ctx, c) /\
                     w' = Obs (Log (CSLHeap (csl_memory s'))) tt.

(** The write's heap observation precedes its native return. *)
Lemma write_ax_ret i a ctx c w : not_done w ->
  <( {instr_flow_erased (CWrite i 1) (own i a ctx c)}, w |=R AX ret {Qwrite i ctx c} )>.
Proof.
  intro Hw; ticl_normalize.
  rewrite instr_flow_write_single; [|cbn; rewrite hsingle_eq; discriminate].
  apply (ax_log (b:=true)); [exact Hw|].
  apply ret_ret; [constructor|]; cbn.
  split; [reflexivity|split; [apply upd_region|split; reflexivity]].
Qed.

(** ** Framed process facts *)
(** The worker head neither yields nor forks. *)
Lemma work_yield_fork_free i : yield_fork_free (work i).
Proof. cbn; tauto. Qed.
(** A write neither yields nor forks. *)
Lemma write_yield_fork_free i : yield_fork_free (CWrite i 1).
Proof. cbn; tauto. Qed.

(** Work on a framed state eventually returns the framed postcondition. *)
Lemma work_af_framed_ret i j a b ctx c s' w : not_done w ->
  frame_rel (region j b) (own i a ctx c) s' ->
  <( {instr_flow_erased (work i) s'}, w |=R AF ret {frame_post (region j b) (Qwork i a ctx c)} )>.
Proof.
  intros Hw HR; destruct s' as [memory aux].
  assert (HA : aux = (ctx, c)) by exact (proj1 (proj2 HR)).
  subst aux.
  assert (HV : fst memory i = Some a).
  { exact (frame_rel_read (region j b) (own i a ctx c) (memory, (ctx, c))
      i a HR (hsingle_eq i a)). }
  ticl_normalize; rewrite work_run by exact HV.
  apply (af_log (b:=true)); [exact Hw|].
  apply (af_log (b:=true)); [constructor|].
  close_ret.
  exists (((upd (fst (region i a)) i (S a), snd (region i a)), (ctx, S c)), Some tt),
    (Obs (Log (CSLEmit (stamp (i, S a) c))) tt).
  split.
  - split; [reflexivity|].
    assert (Present : fst (csl_memory (own i a ctx c)) i <> None).
    { cbn; rewrite hsingle_eq; discriminate. }
    pose proof (frame_rel_write (region j b) (own i a ctx c) (memory, (ctx, c))
      i (S a) HR Present) as Hwrite.
    exact (frame_rel_aux (region j b)
      ((upd (fst (region i a)) i (S a), snd (region i a)), (ctx, c))
      ((upd (fst memory) i (S a), snd memory), (ctx, c)) (ctx, S c) Hwrite).
  - split.
    + constructor; apply frameER_emit.
    + split; [reflexivity|split; [apply upd_region|split; reflexivity]].
Qed.

(** Preserve the original eventual terminal claim on a framed state. *)
Lemma work_af_framed i j a b ctx c s' w : not_done w ->
  frame_rel (region j b) (own i a ctx c) s' ->
  auc (entails _ false (CNow (fun _ => True)))
    (fun _ wd => done_with (frame_post (region j b) (Qwork i a ctx c)) wd)
    (instr_flow_erased (work i) s') w.
Proof. intros Hw HR; apply af_ret_done; apply work_af_framed_ret; assumption. Qed.

(** A framed write records its post-memory before returning, from any live world. *)
Lemma write_ax_ret_framed i j a b ctx c s' w : not_done w ->
  frame_rel (region j b) (own i a ctx c) s' ->
  <( {instr_flow_erased (CWrite i 1) s'}, w |=R AX ret {frame_post (region j b) (Qwrite i ctx c)} )>.
Proof.
  intros Hw HR.
  assert (Present : fst (csl_memory (own i a ctx c)) i <> None).
  { cbn; rewrite hsingle_eq; discriminate. }
  assert (Present' : fst (csl_memory s') i <> None).
  { rewrite (frame_rel_read (region j b) (own i a ctx c) s' i a HR (hsingle_eq i a)); discriminate. }
  pose proof (frame_rel_write (region j b) (own i a ctx c) s' i 1 HR Present) as Hwrite.
  ticl_normalize; rewrite instr_flow_write_single by exact Present'.
  apply (ax_log (b:=true)); [exact Hw|].
  apply ret_ret; [constructor|].
  exists (((upd (fst (region i a)) i 1, snd (region i a)), (ctx, c)), Some tt),
    (Obs (Log (CSLHeap (upd (fst (region i a)) i 1, snd (region i a)))) tt).
  split; [split; [reflexivity|exact Hwrite]|].
  split.
  - constructor; exact (conj (proj1 (proj1 Hwrite))
      (conj (proj2 (proj1 Hwrite)) (proj2 (proj2 Hwrite)))).
  - split; [reflexivity|split; [apply upd_region|split; reflexivity]].
Qed.

(** The heap observation and final value transition give two semantic next steps. *)
Lemma write_ax_done_framed i j a b ctx c s' w : not_done w ->
  frame_rel (region j b) (own i a ctx c) s' ->
  anc (entails _ false (CNow (fun _ => True)))
    (anc (entails _ false (CNow (fun _ => True)))
      (fun _ wd => done_with (frame_post (region j b) (Qwrite i ctx c)) wd))
    (instr_flow_erased (CWrite i 1) s') w.
Proof.
  intros Hw HR.
  pose proof (write_ax_ret_framed i j a b ctx c s' w Hw HR) as Hwrite.
  ticl_normalize in Hwrite.
  eapply anc_mono_r; [|exact Hwrite].
  intros t1 w1 Hret; apply ret_done_next; apply ticl_ret; exact Hret.
Qed.

(** A passive heap frame preserves an indexed user emission exactly. *)
Lemma frame_emit_world {A X} fr (emission : indexed A) w' :
  simW (frameER fr) (@frameRV X fr)
    (Obs (Log (CSLEmit emission)) tt) w' ->
  w' = Obs (Log (CSLEmit emission)) tt.
Proof.
  intro HW.
  eapply (simW_not_done_right_unique (frameER fr) (@frameRV X fr)
    (frameER_right_unique fr) (Obs (Log (CSLEmit emission)) tt)).
  - constructor.
  - exact HW.
  - constructor; apply frameER_emit.
Qed.


(** Unpack the shared shape of the two framed process postconditions. *)
Local Ltac unpack_frame_post :=
  intros ([[m aux] x] & source & [Hx [_ [HA HE]]] & HW & [Hr [Hm [Haux Hw]]]);
  subst x; cbn [snd] in HA, Haux; unfold csl_memory in Hm; cbn [fst] in Hm;
  split; [exact Hr|split; [|split; [congruence|]]];
    [eapply peq_trans; [exact HE|]; apply pop_resp; [exact Hm|apply peq_refl]
    |rewrite Hw in HW].
(** Unpacking a framed postcondition. *)
Lemma frame_post_work i j a b ctx c s'' r w' :
  frame_post (region j b) (Qwork i a ctx c) (s'', r) w' ->
  r = Some tt /\ csl_memory s'' ≈ region i (S a) ⊎ region j b /\ snd s'' = (ctx, S c) /\
  w' = Obs (Log (CSLEmit (stamp (i, S a) c))) tt.
Proof. unpack_frame_post; now apply frame_emit_world in HW. Qed.

(** Unpack a framed write into memory, auxiliary state, and world facts. *)
Lemma frame_post_write i j b ctx c s'' r w' :
  frame_post (region j b) (Qwrite i ctx c) (s'', r) w' ->
  r = Some tt /\ csl_memory s'' ≈ region i 1 ⊎ region j b /\ snd s'' = (ctx, c) /\
  w' = Obs (Log (CSLHeap (csl_memory s''))) tt.
Proof.
  intros ([[m aux] x] & source & [Hx [[HD Hwf] [HA HE]]] & HW & [Hr [Hm [Haux Hw]]]);
    subst x; cbn [snd] in HA, Haux; unfold csl_memory in Hm; cbn [fst] in Hm.
  split; [exact Hr|split; [|split; [congruence|]]].
  - eapply peq_trans; [exact HE|]; apply pop_resp; [exact Hm|apply peq_refl].
  - rewrite Hw in HW.
    assert (HEq : csl_memory s'' = m ⊎ region j b) by (apply managed_heap_ext; exact HE).
    rewrite HEq.
    eapply (simW_not_done_right_unique (frameER (region j b))
      (frameRV (X:=option unit) (region j b)) (frameER_right_unique (region j b))
      (Obs (Log (CSLHeap m)) tt)); [constructor|exact HW|].
    constructor; split; [exact HD|split; [exact Hwf|apply peq_refl]].
Qed.

(** ** Logged round-robin views of the standalone facts.

    Program observations are relabelled under [inl], including every heap
    snapshot. Scheduling selections occupy [inr] and remain separate. *)
Abbreviation rr_obs := (CSLObs (nat * nat) + nat)%type.

Definition QworkW (i a : nat) (ctx : Ctx.Ctx) (c : nat)
  : SSig * option unit -> World (writerE rr_obs) -> Prop :=
  fun '(s', r) w' => r = Some tt /\ csl_memory s' ≈ region i (S a) /\ snd s' = (ctx, S c) /\
                     w' = Obs (Log (inl (CSLEmit (stamp (i, S a) c)))) tt.

Definition QwriteW (i : nat) (ctx : Ctx.Ctx) (c : nat)
  : SSig * option unit -> World (writerE rr_obs) -> Prop :=
  fun '(s', r) w' => r = Some tt /\ csl_memory s' ≈ region i 1 /\ snd s' = (ctx, c) /\
                     w' = Obs (Log (inl (CSLHeap (csl_memory s')))) tt.

(** Relabelling preserves the worker's two-observation prefix exactly. *)
Lemma work_run_W i a (memory : ManagedHeap) ctx c :
  fst memory i = Some a ->
  translate relabel_log (instr_flow_erased (work i) (memory, (ctx, c))) ~
  (emit_list [inl (CSLHeap (upd (fst memory) i (S a), snd memory));
              inl (CSLEmit (stamp (i, S a) c))]%list
   (Ret (((upd (fst memory) i (S a), snd memory), (ctx, S c)), Some tt))
    : ctreeW rr_obs Bn (SSig * option unit)).
Proof.
  intro HV; rewrite work_run by exact HV.
  etransitivity; [apply equ_sbisim, translate_emit_list|].
  apply emit_list_sbisim, equ_sbisim, translate_ret.
Qed.

Lemma work_af_ret_W i a ctx c w : not_done w ->
  <( {translate relabel_log (instr_flow_erased (work i) (own i a ctx c))}, w
     |=R AF ret {QworkW i a ctx c} )>.
Proof.
  intro Hw; ticl_normalize; unfold own; rewrite work_run_W by apply hsingle_eq.
  apply (af_log (b:=true)); [exact Hw|].
  apply (af_log (b:=true)); [constructor|].
  close_ret.
  split; [reflexivity|split; [apply upd_region|split; reflexivity]].
Qed.

Lemma write_ax_ret_W i a ctx c w : not_done w ->
  <( {translate relabel_log (instr_flow_erased (CWrite i 1) (own i a ctx c))}, w
     |=R AX ret {QwriteW i ctx c} )>.
Proof.
  intro Hw; ticl_normalize.
  rewrite instr_flow_write_single by (cbn; rewrite hsingle_eq; discriminate).
  unfold log; rewrite bind_vis, translate_vis; cbn [relabel_log].
  setoid_rewrite bind_ret_l; setoid_rewrite translate_ret.
  apply (an_vis (b:=true) _ _ tt); split; [csplit; auto with ticl|intros []].
  apply ret_ret; [constructor|].
  split; [reflexivity|split; [apply upd_region|split; reflexivity]].
Qed.

(** Framing still relates the local and whole-heap snapshots; it does not
    identify them merely because both observations are under [inl]. *)
Lemma work_af_framed_ret_W i j a b ctx c s' w : not_done w ->
  frame_rel (region j b) (own i a ctx c) s' ->
  <( {translate relabel_log (instr_flow_erased (work i) s')}, w
     |=R AF ret {frame_postW (region j b) (QworkW i a ctx c)} )>.
Proof.
  intros Hw HR; destruct s' as [memory aux].
  assert (HA : aux = (ctx, c)) by exact (proj1 (proj2 HR)); subst aux.
  assert (HV : fst memory i = Some a).
  { exact (frame_rel_read (region j b) (own i a ctx c) (memory, (ctx, c))
      i a HR (hsingle_eq i a)). }
  ticl_normalize; rewrite work_run_W by exact HV.
  apply (af_log (b:=true)); [exact Hw|].
  apply (af_log (b:=true)); [constructor|].
  close_ret.
  exists (((upd (fst (region i a)) i (S a), snd (region i a)), (ctx, S c)), Some tt),
    (Obs (Log (inl (CSLEmit (stamp (i, S a) c)))) tt).
  split.
  - split; [reflexivity|].
    assert (Present : fst (csl_memory (own i a ctx c)) i <> None).
    { cbn; rewrite hsingle_eq; discriminate. }
    pose proof (frame_rel_write (region j b) (own i a ctx c) (memory, (ctx, c))
      i (S a) HR Present) as Hwrite.
    exact (frame_rel_aux (region j b)
      ((upd (fst (region i a)) i (S a), snd (region i a)), (ctx, c))
      ((upd (fst memory) i (S a), snd memory), (ctx, c)) (ctx, S c) Hwrite).
  - split.
    + constructor; apply frameERW_emit.
    + split; [reflexivity|split; [apply upd_region|split; reflexivity]].
Qed.

Lemma write_ax_ret_framed_W i j a b ctx c s' w : not_done w ->
  frame_rel (region j b) (own i a ctx c) s' ->
  <( {translate relabel_log (instr_flow_erased (CWrite i 1) s')}, w
     |=R AX ret {frame_postW (region j b) (QwriteW i ctx c)} )>.
Proof.
  intros Hw HR.
  assert (Present : fst (csl_memory (own i a ctx c)) i <> None).
  { cbn; rewrite hsingle_eq; discriminate. }
  assert (Present' : fst (csl_memory s') i <> None).
  { rewrite (frame_rel_read (region j b) (own i a ctx c) s' i a HR (hsingle_eq i a)); discriminate. }
  pose proof (frame_rel_write (region j b) (own i a ctx c) s' i 1 HR Present) as Hwrite.
  ticl_normalize; rewrite instr_flow_write_single by exact Present'.
  unfold log; rewrite bind_vis, translate_vis; cbn [relabel_log].
  setoid_rewrite bind_ret_l; setoid_rewrite translate_ret.
  apply (an_vis (b:=true) _ _ tt); split; [csplit; auto with ticl|intros []].
  apply ret_ret; [constructor|].
  exists (((upd (fst (region i a)) i 1, snd (region i a)), (ctx, c)), Some tt),
    (Obs (Log (inl (CSLHeap (upd (fst (region i a)) i 1, snd (region i a))))) tt).
  split; [split; [reflexivity|exact Hwrite]|].
  split.
  - apply SimObs.
    exact (frameERW_heap (A:=nat * nat) (region j b) _ _ Hwrite).
  - split; [reflexivity|split; [apply upd_region|split; reflexivity]].
Qed.

Lemma frame_emit_world_W {A X} fr (emission : indexed A) w' :
  simW (frameERW fr) (@frameRV X fr)
    (Obs (Log (inl (CSLEmit emission))) tt) w' ->
  w' = Obs (Log (inl (CSLEmit emission))) tt.
Proof.
  intro HW.
  eapply (simW_not_done_right_unique (frameERW fr) (@frameRV X fr)
    (frameERW_right_unique fr) (Obs (Log (inl (CSLEmit emission))) tt)).
  - constructor.
  - exact HW.
  - constructor; apply frameERW_emit.
Qed.

Lemma frame_post_work_W i j a b ctx c s'' r w' :
  frame_postW (region j b) (QworkW i a ctx c) (s'', r) w' ->
  r = Some tt /\ csl_memory s'' ≈ region i (S a) ⊎ region j b /\ snd s'' = (ctx, S c) /\
  w' = Obs (Log (inl (CSLEmit (stamp (i, S a) c)))) tt.
Proof. unpack_frame_post; now apply frame_emit_world_W in HW. Qed.

Lemma frame_post_write_W i j b ctx c s'' r w' :
  frame_postW (region j b) (QwriteW i ctx c) (s'', r) w' ->
  r = Some tt /\ csl_memory s'' ≈ region i 1 ⊎ region j b /\ snd s'' = (ctx, c) /\
  w' = Obs (Log (inl (CSLHeap (csl_memory s'')))) tt.
Proof.
  intros ([[m aux] x] & source & [Hx [[HD Hwf] [HA HE]]] & HW & [Hr [Hm [Haux Hw]]]);
    subst x; cbn [snd] in HA, Haux; unfold csl_memory in Hm; cbn [fst] in Hm.
  split; [exact Hr|split; [|split; [congruence|]]].
  - eapply peq_trans; [exact HE|]; apply pop_resp; [exact Hm|apply peq_refl].
  - rewrite Hw in HW.
    assert (HEq : csl_memory s'' = m ⊎ region j b) by (apply managed_heap_ext; exact HE).
    rewrite HEq.
    eapply (simW_not_done_right_unique (frameERW (region j b))
      (frameRV (X:=option unit) (region j b)) (frameERW_right_unique (region j b))
      (Obs (Log (inl (CSLHeap m))) tt)); [constructor|exact HW|].
    apply SimObs.
    exact (frameERW_heap (A:=nat * nat) (region j b) (m,aux)
      (frame_state (region j b) (m,aux))
      (frame_rel_state (region j b) (m,aux) (conj HD Hwf))).
Qed.

(** The shared state frames each own state. *)
Lemma frame_rel_shared_2 a b ctx c : frame_rel (region 1 a) (own 2 b ctx c) (shared a b ctx c).
Proof.
  split; [apply (region_frame_inv 2 1); auto|].
  split; [reflexivity|].
  unfold shared, own, csl_memory; cbn [fst]; apply pop_comm, region_disj; auto.
Qed.


(** A heap with both regions frames the first process state. *)
Lemma frame_rel_both_1 a b ctx c (s : SSig) :
  csl_memory s ≈ region 1 a ⊎ region 2 b -> snd s = (ctx, c) ->
  frame_rel (region 2 b) (own 1 a ctx c) s.
Proof. intros HE HA; split; [apply (region_frame_inv 1 2); auto|split; [exact HA|exact HE]]. Qed.

(** A heap with both regions frames the second process state. *)
Lemma frame_rel_both_2 a b ctx c (s : SSig) :
  csl_memory s ≈ region 1 a ⊎ region 2 b -> snd s = (ctx, c) ->
  frame_rel (region 1 a) (own 2 b ctx c) s.
Proof.
  intros HE HA; split; [apply (region_frame_inv 2 1); auto|split; [exact HA|]].
  eapply peq_trans; [exact HE|apply pop_comm, region_disj; auto].
Qed.

(** ** Pool bookkeeping *)
(** The child is the first slot. *)
Definition child : Fin.t 2 := Fin.F1.
(** The parent is the second slot. *)
Definition parent : Fin.t 2 := Fin.FS Fin.F1.

(** Round-robin cursor zero picks the child in a two-slot pool. *)
Lemma rr_pick_1_0 : rr_pick 1 0 = child.
Proof. reflexivity. Qed.
(** Round-robin cursor one picks the parent in a two-slot pool. *)
Lemma rr_pick_1_1 : rr_pick 1 1 = parent.
Proof. reflexivity. Qed.
(** A singleton round-robin pool always picks its only slot. *)
Lemma rr_pick_0 m : rr_pick 0 m = Fin.F1.
Proof. apply Fin.to_nat_inj; unfold rr_pick; rewrite Fin.to_nat_of_nat; cbn; reflexivity. Qed.

(** Closed-term extraction of [both]. *)
Lemma both_lookup a b m : both a b m -> fst m 1 = Some a /\ fst m 2 = Some b.
Proof.
  intros [HE _]; split; [rewrite (HE 1)|rewrite (HE 2)]; cbn; unfold hunion;
    rewrite ?hsingle_eq, ?hsingle_neq by lia; reflexivity.
Qed.
