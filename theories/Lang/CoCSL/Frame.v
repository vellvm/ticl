(** * Heap frame rules for CoCSL source programs.

    A framed run is the same program on a heap extended by a disjoint
    [ManagedHeap] region; every proved prefix property survives and every
    suffix postcondition acquires the frame ([frame_post]).  Allocation is
    excluded ([alloc_free]) because first-fit allocation is deterministic in
    the absolute heap. *)

From TICL Require Export Lang.CoCSL.Mod CTree.Interp.CSL.Frame CTree.Interp.Yield.Frame.
From Stdlib Require Import Fin Vector Strings.String.
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
  Framable no_alloc_sE (interp_yield (interp_spawn (schedule n (csl_pool ps) focus))).
Proof. intro; apply framable_erased_nd; auto using csl_pool_branchfree, csl_pool_framable. Qed.

(** The erased round-robin pool runner is framable. *)
Lemma run_rr_pool_framable {n} (ps : Vector.t (CProg unit) n) focus cursor :
  Vector.Forall alloc_free ps ->
  Framable no_alloc_sE (interp_yield (interp_spawn
    (run_round_robin (schedule n (csl_pool ps) focus) cursor))).
Proof. intro; apply framable_erased_rr; auto using csl_pool_branchfree, csl_pool_framable. Qed.

(** The standalone erased flow of an allocation-free program is framable. *)
Lemma instr_flow_framable {A} (p : CProg A) :
  alloc_free p -> Framable no_alloc_sE (interp_thread (denote_flow p)).
Proof. intro; apply framable_thread, denote_flow_framable; assumption. Qed.
(** The singleton nondeterministic runner has a framable erased tree. *)
Lemma run_nd_framable p : alloc_free p ->
  Framable no_alloc_sE (interp_yield (interp_spawn (schedule 1 (csl_pool [p]%vector) (Some Fin.F1)))).
Proof. intro; apply run_nd_pool_framable; repeat constructor; assumption. Qed.

(** The singleton round-robin runner has a framable erased tree. *)
Lemma run_rr_framable p : alloc_free p ->
  Framable no_alloc_sE (interp_yield (interp_spawn
    (run_round_robin (schedule 1 (csl_pool [p]%vector) (Some Fin.F1)) 0))).
Proof. intro; apply run_rr_pool_framable; repeat constructor; assumption. Qed.


(** Client-facing unfolding of a framed postcondition on the memory component. *)
Lemma frame_post_iff {X} fr (P : SSig * X -> World (writerE (CSLObs (nat * nat))) -> Prop)
  M aux x w :
  frame_post fr P ((M, aux), x) w <->
  exists m, m # fr /\ managed_wf m /\ M ≈ m ⊎ fr /\ P ((m, aux), x) w.
Proof.
  split.
  - intros ([[m aux'] x'] & [Hx [[HD HW] [HA HE]]] & HP); cbn in *; subst.
    exists m; auto.
  - intros (m & HD & HW & HE & HP).
    exists ((m, aux), x); split; [|exact HP].
    split; [reflexivity|split; [split; assumption|split; [reflexivity|exact HE]]].
Qed.
