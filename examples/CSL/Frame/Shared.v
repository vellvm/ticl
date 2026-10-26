(** * Shared material for the two-process frame regressions.

    Two processes own cells [1] and [2].  Each process's facts are proved
    standalone on its own region ([own]) and transported to the shared heap by
    framing with the other region ([work_af_framed], [write_ax_framed]).
    The AF/AN/AG files join these through the cooperative prefix equation. *)
From Stdlib Require Import Fin Vector Arith.PeanoNat Lia.
From Coinduction Require Import all.
From TICL Require Export
  CTree.Core
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
  Lang.CSL.Mod
  Lang.CSL.Frame
  Lang.CSL.Sequential
  Utils.Pcm.

Export CTreeNotations TiclNotations VectorNotations.
Global Open Scope ctree_scope.
Global Open Scope ticl_scope.
Global Open Scope fin_vector_scope.
Global Open Scope pcm_scope.

(** Close a returning [AU done] or [AX done] goal at a [not_done] world. *)
Ltac close_ret :=
  cright; csplit; [csplit; auto with ticl | apply can_step_ret; auto with ticl |];
  intros ?t' ?w' ?TR;
  first [apply ktrans_done in TR as (-> & _) | apply ktrans_finish in TR as (-> & _)];
  cleft; csplit; cbn.
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
                     w' = Obs (Log (inr (stamp (i, S a) c))) tt.

(** The standalone worker reads, writes, and emits in order. *)
Lemma work_run i a ctx c :
  instr_flow_erased (work i) (own i a ctx c) ~
  (log (inr (stamp (i, S a) c) : CSLObs (nat * nat));;
   Ret (((upd (fst (region i a)) i (S a), snd (region i a)), (ctx, S c)), Some tt)
    : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)).
Proof.
  unfold work.
  rewrite instr_flow_read with (v := a) by apply hsingle_eq.
  rewrite instr_flow_write; [|cbn; rewrite hsingle_eq; discriminate].
  unfold own, csl_memory; cbn [fst snd].
  rewrite instr_flow_head with (e := inr1 (inr1 (Log (i, S a)))) (k := fun _ => Ret (Some tt)).
  2:{ cbn [denote_flow]; unfold CTree.trigger; rewrite bind_vis; step; constructor; intro;
      rewrite bind_ret_l; reflexivity. }
  cbn [sh h_sum csl_emit_handler csl_counter csl_context csl_memory fst snd].
  unfold log, CTree.trigger; rewrite !bind_bind; setoid_rewrite bind_ret_l.
  setoid_rewrite interp_state_thread_ret.
  reflexivity.
Qed.

(** Standalone work eventually returns its postcondition. *)
Lemma work_af i a ctx c w : not_done w ->
  <[ {instr_flow_erased (work i) (own i a ctx c)}, w |= AF done {Qwork i a ctx c} ]>.
Proof.
  intro Hw; rewrite work_run.
  apply afr_log; [exact Hw|].
  close_ret.
  split; [reflexivity|split; [apply upd_region|split; reflexivity]].
Qed.

(** A standalone write preserves context, counter, and observation world. *)
Definition Qwrite (i : nat) (ctx : Ctx.Ctx) (c : nat) (w : World (writerE (CSLObs (nat * nat))))
  : SSig * option unit -> World (writerE (CSLObs (nat * nat))) -> Prop :=
  fun '(s', r) w' => r = Some tt /\ csl_memory s' ≈ region i 1 /\ snd s' = (ctx, c) /\ w' = w.

(** Standalone writing returns [Qwrite] without an intervening transition. *)
Lemma write_ret i a ctx c w : not_done w ->
  <[ {instr_flow_erased (CWrite i 1) (own i a ctx c)}, w |= ret {Qwrite i ctx c w} ]>.
Proof.
  intro Hw.
  rewrite instr_flow_write_single; [|cbn; rewrite hsingle_eq; discriminate].
  apply ret_ret; [exact Hw|]; cbn.
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
Lemma work_af_framed i j a b ctx c s' w : not_done w ->
  frame_rel (region j b) (own i a ctx c) s' ->
  <[ {instr_flow_erased (work i) s'}, w |= AF done {frame_post (region j b) (Qwork i a ctx c)} ]>.
Proof.
  intros Hw HR.
  apply (aur_csl_frame_done (region j b) _ _ _
    (instr_flow_framable (work i) ltac:(cbn; tauto)) HR); auto using work_af.
Qed.
(** Writing on a framed state satisfies the framed universal-next postcondition. *)
Lemma write_ax_framed i j a b ctx c s' w : not_done w ->
  frame_rel (region j b) (own i a ctx c) s' ->
  <[ {instr_flow_erased (CWrite i 1) s'}, w |= AX done {frame_post (region j b) (Qwrite i ctx c w)} ]>.
Proof.
  intros Hw HR.
  exact (ticlr_csl_frame (region j b) _ _ _
    (instr_flow_framable (CWrite i 1) I) HR
    <[ ret {Qwrite i ctx c w} ]> w Hw (write_ret i a ctx c w Hw)).
Qed.

(** Unpack the shared shape of the two framed process postconditions. *)
Local Ltac unpack_frame_post :=
  intros ([[m aux] x] & [Hx [_ [HA HE]]] & [Hr [Hm [Haux Hw]]]);
  subst x; cbn [snd] in HA, Haux; unfold csl_memory in Hm; cbn [fst] in Hm;
  split; [exact Hr|split; [|split; [congruence|exact Hw]]];
  eapply peq_trans; [exact HE|]; apply pop_resp; [exact Hm|apply peq_refl].
(** Unpacking a framed postcondition. *)
Lemma frame_post_work i j a b ctx c s'' r w' :
  frame_post (region j b) (Qwork i a ctx c) (s'', r) w' ->
  r = Some tt /\ csl_memory s'' ≈ region i (S a) ⊎ region j b /\ snd s'' = (ctx, S c) /\
  w' = Obs (Log (inr (stamp (i, S a) c))) tt.
Proof. unpack_frame_post. Qed.

(** Unpack a framed write into memory, auxiliary state, and world facts. *)
Lemma frame_post_write i j b ctx c w s'' r w' :
  frame_post (region j b) (Qwrite i ctx c w) (s'', r) w' ->
  r = Some tt /\ csl_memory s'' ≈ region i 1 ⊎ region j b /\ snd s'' = (ctx, c) /\ w' = w.
Proof. unpack_frame_post. Qed.

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
