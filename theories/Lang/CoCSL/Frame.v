(** * Heap frame rules for CoCSL source programs.

    The same program runs on a heap extended by a disjoint [ManagedHeap].
    All atoms acquire their [framer] image; native postconditions acquire
    [frame_post]. Literal prefix transport additionally needs [prefix_stable].
    Unconditional admission excludes allocation. A conditional allocation rule
    requires common first fit and the full allocated managed-state relation. *)

From TICL Require Export Lang.CoCSL.Mod CTree.Interp.CSL.Frame CTree.Interp.Yield.Frame.
From Stdlib Require Import Fin Vector Strings.String Arith.PeanoNat.
From ExtLib Require Import Structures.Maps Data.Map.FMapAList Data.String.
From TICL Require Import
  CTree.Core
  CTree.Events.Heap
  CTree.Interp.State.Mod
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.Nondeterministic
  CTree.Logic.Sim
  Logic.Simulation
  Logic.World
  Logic.Kripke
  Logic.Semantics
  Utils.Vectors
  Utils.Pcm.

Import CTreeNotations TiclNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.
Local Open Scope pcm_scope.

(** [okE] admits every event the expression can trigger. *)
Fixpoint exp_ok (okE : forall Y, CEff Y -> Prop) (e : CExp) : Prop :=
  match e with
  | CVar _ => okE _ (inr1 (inr1 (inr1 (inl1 Get)))) /\ okE _ (inl1 Yield)
  | CLit _ => True
  | CPlus a b | CMinus a b | CMult a b => exp_ok okE a /\ exp_ok okE b
  end.
(** [okE] admits every event the program can trigger. *)
Fixpoint prog_ok (okE : forall Y, CEff Y -> Prop) {A} (p : CProg A) : Prop :=
  match p with
  | CRead a => okE _ (inr1 (inr1 (inl1 (HRead a))))
  | CWrite a v => okE _ (inr1 (inr1 (inl1 (HWrite a v))))
  | CEmit tag v => okE _ (inr1 (inr1 (inr1 (inr1 (Log (tag, v))))))
  | CYield => okE _ (inl1 Yield)
  | CFork body => okE _ (inr1 (inl1 Fork)) /\ prog_ok okE body
  | CoCSLSyntax.CRet _ => True
  | CBind body next => prog_ok okE body /\ forall a, prog_ok okE (next a)
  | CUntilNone body => prog_ok okE body
  | CAlloc size => okE _ (inr1 (inr1 (inl1 (HAlloc size))))
  | CFree base => okE _ (inr1 (inr1 (inl1 (HFree base))))
  | CCAS a expected desired =>
      exp_ok okE a /\ exp_ok okE expected /\ exp_ok okE desired /\
      forall addr old value, okE _ (inr1 (inr1 (inl1 (HCAS addr old value))))
  | CEval e => exp_ok okE e
  | CAssign _ e => exp_ok okE e /\ okE _ (inr1 (inr1 (inr1 (inl1 Get)))) /\
      forall ctx, okE _ (inr1 (inr1 (inr1 (inl1 (Put ctx)))))
  | CIf e yes no => exp_ok okE e /\ prog_ok okE yes /\ prog_ok okE no
  | CWhile e body => exp_ok okE e /\ prog_ok okE body
  end.
(** No allocation: first-fit allocation is deterministic in the absolute heap. *)
Definition alloc_free {A} (p : CProg A) : Prop := prog_ok (okE_thread no_alloc_sE) p.

Local Ltac fr_trigger H :=
  unfold heap_read, heap_write, heap_free, heap_cas, heap_alloc, source_get, source_put,
    source_yield, source_fork, CTree.trigger;
  apply fr_vis; [exact H|intro; apply fr_ret].

(** Admissible expressions denote framable trees. *)
Lemma denote_exp_framable okE (e : CExp) : exp_ok okE e -> Framable okE (denote_exp e).
Proof.
  induction e as [name|n|a IHa b IHb|a IHa b IHb|a IHa b IHb];
    cbn [denote_exp exp_ok]; intro He.
  { destruct He as [HG HY]; apply framable_bind; [fr_trigger HG|].
    intro ctx; destruct (lookup name ctx).
    - apply framable_bind; [fr_trigger HY|intros []; apply fr_ret].
    - apply fr_stuck. }
  { apply fr_ret. }
  all: destruct He as [Ha Hb]; apply framable_bind; [apply IHa, Ha|intro x];
    apply framable_bind; [apply IHb, Hb|intro y; apply fr_ret].
Qed.

(** The shared admissibility walk certifies framability of every program constructor. *)
Lemma denote_flow_framable okE {A} (p : CProg A) :
  prog_ok okE p -> Framable okE (denote_flow p).
Proof.
  induction p as [a|a v|q v| |body IH|A x|A B body IH next IHnext|A body IH|size|base
    |a expected desired|e|name e|A test yes IHyes no IHno|test body IH];
    cbn [denote_flow prog_ok]; intro Hp.
  - apply framable_bind; [fr_trigger Hp|intro x; apply fr_ret].
  - apply framable_bind; [fr_trigger Hp|intros []; apply fr_ret].
  - apply framable_bind; [unfold CTree.trigger; apply fr_vis; [exact Hp|intro; apply fr_ret]|].
    intros []; apply fr_ret.
  - apply framable_bind; [fr_trigger Hp|intros []; apply fr_ret].
  - destruct Hp as [HF Hb]; apply framable_bind; [fr_trigger HF|].
    intros []; cbn.
    + apply framable_bind; [exact (IH Hb)|intro flow; apply fr_ret].
    + apply fr_ret.
  - apply fr_ret.
  - destruct Hp as [Hb Hn].
    apply framable_bind; [exact (IH Hb)|].
    intros [x|]; [apply IHnext, Hn|apply fr_ret].
  - apply framable_iter; intros [].
    apply framable_bind; [exact (IH Hp)|].
    intros [[x|]|]; apply fr_ret.
  - apply framable_bind; [fr_trigger Hp|intro a; apply fr_ret].
  - apply framable_bind; [fr_trigger Hp|intros []; apply fr_ret].
  - destruct Hp as [Ha [He [Hd HC]]].
    apply framable_bind; [apply denote_exp_framable, Ha|intro addr].
    apply framable_bind; [apply denote_exp_framable, He|intro old].
    apply framable_bind; [apply denote_exp_framable, Hd|intro value].
    apply framable_bind; [fr_trigger (HC addr old value)|intro b; apply fr_ret].
  - apply framable_bind; [apply denote_exp_framable, Hp|intro v; apply fr_ret].
  - destruct Hp as [He [HG HP]].
    apply framable_bind; [apply denote_exp_framable, He|intro v].
    apply framable_bind; [fr_trigger HG|].
    intro ctx; apply framable_bind; [fr_trigger (HP (add name v ctx))|intros []; apply fr_ret].
  - destruct Hp as [He [Hy Hn]].
    apply framable_bind; [apply denote_exp_framable, He|intro v].
    destruct (CoCSLSyntax.is_true v); auto.
  - destruct Hp as [He Hb]; apply framable_iter; intros [].
    apply framable_bind; [apply denote_exp_framable, He|intro v].
    destruct (CoCSLSyntax.is_true v); [|apply fr_ret].
    apply framable_bind; [exact (IH Hb)|].
    intros [[]|]; apply fr_ret.
Qed.

(** Allocation-free programs denote framable complete threads. *)
Lemma denote_framable (p : CProg unit) :
  alloc_free p -> Framable (okE_thread no_alloc_sE) (denote p).
Proof.
  intro Hp; unfold denote; apply framable_bind;
    [apply denote_flow_framable, Hp|intro flow; apply fr_ret].
Qed.

(** Source denotations form a branch-free scheduler pool. *)
Lemma csl_pool_branchfree {n} (ps : Vector.t (CProg unit) n) : pool_branchfree (csl_pool ps).
Proof. intro i; unfold csl_pool; rewrite (Vector.nth_map denote ps i i eq_refl); apply denote_branchfree. Qed.

(** An allocation-free source pool is framable. *)
Lemma csl_pool_framable {n} (ps : Vector.t (CProg unit) n) :
  Vector.Forall alloc_free ps -> pool_framable no_alloc_sE (csl_pool ps).
Proof.
  intros Hps i; unfold csl_pool; rewrite (Vector.nth_map denote ps i i eq_refl).
  apply denote_framable; now apply Vector.Forall_nth.
Qed.

(** ** Framability of each runner's erased tree. *)
(** The erased nondeterministic pool runner is framable. *)
Lemma run_nd_pool_framable {n} (ps : Vector.t (CProg unit) n) focus :
  Vector.Forall alloc_free ps ->
  Framable no_alloc_sE (project_scheduled (schedule n (csl_pool ps) focus)).
Proof. intro; apply framable_erased_nd; auto using csl_pool_branchfree, csl_pool_framable. Qed.

(** The round-robin scheduled pool is framable: scheduling events are always
    admitted. *)
Lemma run_rr_pool_framable {n} (ps : Vector.t (CProg unit) n) focus cursor :
  Vector.Forall alloc_free ps ->
  Framable (okE_policy no_alloc_sE) (schedule_policy rr_scheduler n (csl_pool ps) focus cursor).
Proof. intro; apply framable_schedule_rr; auto using csl_pool_branchfree, csl_pool_framable. Qed.

(** The standalone erased flow of an allocation-free program is framable. *)
Lemma instr_flow_framable {A} (p : CProg A) :
  alloc_free p -> Framable no_alloc_sE (interp_thread (denote_flow p)).
Proof. intro; apply framable_thread, denote_flow_framable; assumption. Qed.
(** The singleton nondeterministic runner has a framable erased tree. *)
Lemma run_nd_framable p : alloc_free p ->
  Framable no_alloc_sE (project_scheduled (schedule 1 (csl_pool [p]%vector) (Some Fin.F1))).
Proof. intro; apply run_nd_pool_framable; repeat constructor; assumption. Qed.

(** The singleton round-robin runner has a framable scheduled tree. *)
Lemma run_rr_framable p : alloc_free p ->
  Framable (okE_policy no_alloc_sE)
    (schedule_policy rr_scheduler 1 (csl_pool [p]%vector) (Some Fin.F1) 0).
Proof. intro; apply run_rr_pool_framable; repeat constructor; assumption. Qed.

(** Standalone source flow embedded under the instrumented policy handler. *)
Lemma instr_flow_sched_framable {A} (p : CProg A) :
  alloc_free p ->
  Framable (okE_policy no_alloc_sE) (translate inl1 (interp_thread (denote_flow p))).
Proof. intro; apply framable_translate_inl1, instr_flow_framable; assumption. Qed.

(** ** All-atom framing for the existing source execution shapes. *)
Lemma instr_exp_csl_frame {b} (fr : ManagedHeap) (e : CExp) (s s' : SSig)
  (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * nat) b) w w' :
  exp_ok (okE_thread no_alloc_sE) e -> frame_rel fr s s' ->
  simW (frameER fr) (@frameRV nat fr) w w' ->
  entails (SSig * nat) b p (instr_exp_erased e s) w ->
  entails (SSig * nat) b (framer (SSig * nat) b (frameER fr) (frameRV fr) p)
    (instr_exp_erased e s') w'.
Proof.
  intros HF HR HW H; unfold instr_exp_erased in *.
  eapply ticl_csl_frame; [|exact HR|exact HW|exact H].
  apply framable_thread, denote_exp_framable; exact HF.
Qed.

Lemma instr_flow_csl_frame {A b} (fr : ManagedHeap) (source : CProg A) (s s' : SSig)
  (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * option A) b) w w' :
  alloc_free source -> frame_rel fr s s' ->
  simW (frameER fr) (@frameRV (option A) fr) w w' ->
  entails (SSig * option A) b p (instr_flow_erased source s) w ->
  entails (SSig * option A) b
    (framer (SSig * option A) b (frameER fr) (frameRV fr) p)
    (instr_flow_erased source s') w'.
Proof.
  intros HF HR HW H; unfold instr_flow_erased in *.
  eapply ticl_csl_frame; [apply instr_flow_framable; exact HF|exact HR|exact HW|exact H].
Qed.

Lemma run_nd_pool_csl_frame {n b} (fr : ManagedHeap)
  (ps : Vector.t (CProg unit) n) focus (s s' : SSig)
  (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) w w' :
  Vector.Forall alloc_free ps -> frame_rel fr s s' ->
  simW (frameER fr) (@frameRV unit fr) w w' ->
  entails (SSig * unit) b p (run_nd_pool ps focus s) w ->
  entails (SSig * unit) b (framer (SSig * unit) b (frameER fr) (frameRV fr) p)
    (run_nd_pool ps focus s') w'.
Proof.
  intros HF HR HW H; unfold run_nd_pool, interp_schedule_nd in *.
  eapply ticl_csl_frame;
    [apply run_nd_pool_framable; exact HF|exact HR|exact HW|exact H].
Qed.

Lemma run_rr_pool_csl_frame {n b} (fr : ManagedHeap)
  (ps : Vector.t (CProg unit) n) focus cursor (s s' : SSig)
  (p : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) w w' :
  Vector.Forall alloc_free ps -> frame_rel fr s s' ->
  simW (frameERW fr) (@frameRV unit fr) w w' ->
  entails (SSig * unit) b p (run_rr_pool ps focus cursor s) w ->
  entails (SSig * unit) b (framer (SSig * unit) b (frameERW fr) (frameRV fr) p)
    (run_rr_pool ps focus cursor s') w'.
Proof.
  intros HF HR HW H; unfold run_rr_pool, interp_schedule_fair in *.
  eapply ticl_csl_frameW;
    [apply run_rr_pool_framable; exact HF|exact HR|exact HW|exact H].
Qed.

Lemma run_nd_csl_frame {b} (fr : ManagedHeap) (source : CProg unit) (s s' : SSig)
  (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) w w' :
  alloc_free source -> frame_rel fr s s' ->
  simW (frameER fr) (@frameRV unit fr) w w' ->
  entails (SSig * unit) b p (run_nd source s) w ->
  entails (SSig * unit) b (framer (SSig * unit) b (frameER fr) (frameRV fr) p)
    (run_nd source s') w'.
Proof.
  intros HF HR HW H; unfold run_nd, run_nd_pool, interp_schedule_nd in *.
  eapply ticl_csl_frame; [apply run_nd_framable; exact HF|exact HR|exact HW|exact H].
Qed.

Lemma run_rr_csl_frame {b} (fr : ManagedHeap) (source : CProg unit) (s s' : SSig)
  (p : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) w w' :
  alloc_free source -> frame_rel fr s s' ->
  simW (frameERW fr) (@frameRV unit fr) w w' ->
  entails (SSig * unit) b p (run_rr source s) w ->
  entails (SSig * unit) b (framer (SSig * unit) b (frameERW fr) (frameRV fr) p)
    (run_rr source s') w'.
Proof.
  intros HF HR HW H; unfold run_rr, run_rr_pool, interp_schedule_fair in *.
  eapply ticl_csl_frameW; [apply run_rr_framable; exact HF|exact HR|exact HW|exact H].
Qed.


(** A scheduled allocation may frame only when both heaps select the same
    first-fit block and the full allocated memories remain frame-related. *)
Lemma ticl_csl_nd_alloc_frame_at {b} (fr : ManagedHeap) n
  (ts : pool sE Bn (S n)) (i : Fin.t (S n)) (size base : nat)
  (K : option nat -> thread sE Bn) (s s' : SSig)
  (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) w w' :
  frame_rel fr s s' -> Nat.lt 0 size -> Nat.lt 0 base ->
  block_free (fst (csl_memory s)) base size ->
  block_free (fst (csl_memory s')) base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free (fst (csl_memory s)) j size) ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free (fst (csl_memory s')) j size) ->
  frame_rel fr (managed_alloc (csl_memory s) base size, snd s)
    (managed_alloc (csl_memory s') base size, snd s') ->
  Framable no_alloc_sE
    (project_scheduled (schedule (S n) (ts @ i := K (Some base)) (Some i))) ->
  simW (frameER fr) (@frameRV unit fr) w w' ->
  entails (SSig * unit) b p
    (interp_schedule_nd sh (S n)
      (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) s) w ->
  entails (SSig * unit) b (framer (SSig * unit) b (frameER fr) (frameRV fr) p)
    (interp_schedule_nd sh (S n)
      (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) s') w'.
Proof.
  intros HR Hsize Hbase Hfree Hfree' Hfirst Hfirst' Hpost HF HW H.
  destruct s as [[h allocs] [ctx c]], s' as [[h' allocs'] [ctx' c']].
  cbn [csl_memory] in Hfree, Hfree', Hfirst, Hfirst', Hpost.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c
    Hsize Hbase Hfree Hfirst) in H.
  rewrite (interp_nd_source_alloc_first n ts i size base K h' allocs' ctx' c'
    Hsize Hbase Hfree' Hfirst').
  unfold interp_schedule_nd in *.
  eapply ticl_csl_frame_log; [exact HF|exact Hpost| |exact HW|exact H].
  exact (frameER_heap fr _ _ Hpost).
Qed.

Lemma ticl_csl_rr_alloc_frame_at {b} (fr : ManagedHeap) n
  (ts : pool sE Bn (S n)) (i : Fin.t (S n)) (size base : nat)
  (K : option nat -> thread sE Bn) (cursor : nat) (s s' : SSig)
  (p : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) w w' :
  frame_rel fr s s' -> Nat.lt 0 size -> Nat.lt 0 base ->
  block_free (fst (csl_memory s)) base size ->
  block_free (fst (csl_memory s')) base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free (fst (csl_memory s)) j size) ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free (fst (csl_memory s')) j size) ->
  frame_rel fr (managed_alloc (csl_memory s) base size, snd s)
    (managed_alloc (csl_memory s') base size, snd s') ->
  Framable (okE_policy no_alloc_sE)
    (schedule_policy rr_scheduler (S n) (ts @ i := K (Some base)) (Some i) cursor) ->
  simW (frameERW fr) (@frameRV unit fr) w w' ->
  entails (SSig * unit) b p
    (interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor s) w ->
  entails (SSig * unit) b (framer (SSig * unit) b (frameERW fr) (frameRV fr) p)
    (interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor s') w'.
Proof.
  intros HR Hsize Hbase Hfree Hfree' Hfirst Hfirst' Hpost HF HW H.
  destruct s as [[h allocs] [ctx c]], s' as [[h' allocs'] [ctx' c']].
  cbn [csl_memory] in Hfree, Hfree', Hfirst, Hfirst', Hpost.
  rewrite (interp_rr_alloc_first n ts i size base K cursor h allocs ctx c
    Hsize Hbase Hfree Hfirst) in H.
  rewrite (interp_rr_alloc_first n ts i size base K cursor h' allocs' ctx' c'
    Hsize Hbase Hfree' Hfirst').
  unfold interp_schedule_fair in *.
  eapply ticl_csl_frameW_log; [exact HF|exact Hpost| |exact HW|exact H].
  exact (frameERW_heap fr _ _ Hpost).
Qed.

(** Client-facing unfolding of a framed postcondition on the memory component. *)
Lemma frame_post_iff {X} fr (P : SSig * X -> World (writerE (CSLObs (nat * nat))) -> Prop)
  M aux x w' :
  frame_post fr P ((M, aux), x) w' <->
  exists m w, m # fr /\ managed_wf m /\ M ≈ m ⊎ fr /\
    simW (frameER fr) (frameRV (X:=X) fr) w w' /\ P ((m, aux), x) w.
Proof.
  split.
  - intros ([[m aux'] x'] & w & [Hx [[HD HW] [HA HE]]] & Hworld & HP); cbn in *; subst.
    exists m, w; auto.
  - intros (m & w & HD & HW & HE & Hworld & HP).
    exists ((m, aux), x), w; split; [|auto].
    split; [reflexivity|split; [split; assumption|split; [reflexivity|exact HE]]].
Qed.

(** Logged postconditions preserve both framed memory and predecessor worlds. *)
Lemma frame_postW_iff {X} fr
  (P : SSig * X -> World (writerE (CSLObs (nat * nat) + nat)) -> Prop)
  M aux x w' :
  frame_postW fr P ((M, aux), x) w' <->
  exists m w, m # fr /\ managed_wf m /\ M ≈ m ⊎ fr /\
    simW (frameERW fr) (frameRV (X:=X) fr) w w' /\ P ((m, aux), x) w.
Proof.
  split.
  - intros ([[m aux'] x'] & w & [Hx [[HD HW] [HA HE]]] & Hworld & HP); cbn in *; subst.
    exists m, w; auto.
  - intros (m & w & HD & HW & HE & Hworld & HP).
    exists ((m, aux), x), w; split; [|auto].
    split; [reflexivity|split; [split; assumption|split; [reflexivity|exact HE]]].
Qed.
