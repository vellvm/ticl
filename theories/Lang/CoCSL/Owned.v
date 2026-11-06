(** * Source admission and coupling for CoCSL owned components. *)

From TICL Require Export CTree.Interp.CSL.Owned Lang.CoCSL.Frame.
From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Relations
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Events.Writer
  CTree.Interp.State.Mod
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.Nondeterministic
  CTree.Interp.Yield.Frame
  Logic.Simulation
  CTree.Logic.Sim
  Utils.Vectors
  Utils.Pcm.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

Definition init_owned (child parent : CProg unit) (h h' : ManagedHeap)
  (ctx : Ctx.Ctx) (base : nat) : OwnedCfg :=
  init_owned_threads (denote child) (denote parent) h h' ctx base.

Definition init_local (i : side) (p : CProg unit) (h : ManagedHeap)
  (ctx : Ctx.Ctx) (base : nat) (focused : bool) : OwnedCfg :=
  init_local_thread i (denote p) h ctx base focused.

Definition component_ok {A} (p : CProg A) : Prop := prog_ok (okE_thread component_event_ok) p.

Definition admissible (child parent : CProg unit) (h h' : ManagedHeap) (ctx : Ctx.Ctx) (base : nat)
  : Prop :=
  managed_wf h /\ managed_wf h' /\ h # h' /\
  component_ok child /\ component_ok parent /\
  confined h (project Child (init_owned child parent h h' ctx base)) /\
  confined h' (project Parent (init_owned child parent h h' ctx base)).

Definition coupled (c : OwnedCfg) : Prop :=
  exists child parent h h' ctx base d,
    admissible child parent h h' ctx base /\
    clos_refl_trans _ owned_next (init_owned child parent h h' ctx base) d /\
    owned_equ d c.

Lemma project_init_child child parent h h' ctx base :
  owned_equ (project Child (init_owned child parent h h' ctx base))
    (init_local Child child h ctx base false).
Proof. apply project_init_threads_child. Qed.

Lemma project_init_parent child parent h h' ctx base :
  owned_equ (project Parent (init_owned child parent h h' ctx base))
    (init_local Parent parent h' ctx base true).
Proof. apply project_init_threads_parent. Qed.

Lemma init_local_select i p h ctx base a d :
  owned_step (init_local i p h ctx base false) a d <->
    a = act i OASelect /\ d = init_local i p h ctx base true.
Proof. apply init_local_thread_select. Qed.

Lemma init_owned_wf child parent h h' ctx base :
  managed_wf h -> managed_wf h' -> h # h' -> owned_wf (init_owned child parent h h' ctx base).
Proof. apply init_owned_threads_wf. Qed.

Lemma coupled_init child parent h h' ctx base :
  admissible child parent h h' ctx base -> coupled (init_owned child parent h h' ctx base).
Proof.
  intros Ha; exists child, parent, h, h', ctx, base, (init_owned child parent h h' ctx base).
  split; [exact Ha|split; [apply rt_refl|reflexivity]].
Qed.

Lemma coupled_equ c d : owned_equ c d -> coupled c -> coupled d.
Proof.
  intros He (ch & pa & h & h' & ctx & base & d0 & Ha & Hr & He0).
  exists ch, pa, h, h', ctx, base, d0; split; [exact Ha|split; [exact Hr|etransitivity; eauto]].
Qed.

Lemma coupled_step c a c' : coupled c -> owned_step c a c' -> coupled c'.
Proof.
  intros (ch & pa & h & h' & ctx & base & d & Ha & Hr & He) Hs; symmetry in He.
  destruct (owned_step_equ _ _ _ _ He Hs) as (d' & Hd' & He').
  exists ch, pa, h, h', ctx, base, d'; split; [exact Ha|split].
  - eapply rt_trans; [exact Hr|apply rt_step; exists a; exact Hd'].
  - symmetry; exact He'.
Qed.

Lemma coupled_weak i c c' : coupled c -> weak_next i c c' -> coupled c'.
Proof.
  intros Hc (mid & Hstar & a & Hs & _); apply (coupled_step mid a c'); [|exact Hs].
  clear Hs; revert Hc; induction Hstar as [x y (b & Hb & _)|x|x y z _ IH1 _ IH2]; intros Hc.
  - eapply coupled_step; eauto.
  - exact Hc.
  - auto.
Qed.

Lemma coupled_wf c : coupled c -> owned_wf c.
Proof.
  intros (ch & pa & h & h' & ctx & base & d & (Hw & Hw' & Hd & _) & Hr & He).
  eapply owned_wf_equ; [exact He|]; clear He.
  apply clos_rt_rtn1 in Hr; induction Hr as [|y z (a & Ha) _ IH].
  - apply init_owned_wf; assumption.
  - eapply owned_step_wf; eauto.
Qed.

Fixpoint addr_ok (r : ManagedHeap) {A} (p : CProg A) : Prop :=
  match p with
  | CRead a => fst r a <> None
  | CWrite a _ => fst r a <> None
  | CFree b => b = 0 \/ snd r b <> None
  | CCAS (CLit a) _ _ => fst r a <> None
  | CCAS _ _ _ => False
  | CFork body => addr_ok r body
  | CBind body next => addr_ok r body /\ forall x, addr_ok r (next x)
  | CUntilNone body => addr_ok r body
  | CIf _ yes no => addr_ok r yes /\ addr_ok r no
  | CWhile _ body => addr_ok r body
  | _ => True
  end.

Local Definition okR (r : ManagedHeap) : forall Y, sE Y -> Prop := fun Y e => prim_addr_ok r e.

Local Lemma framable_equ {E B A} (okE : forall Y, E Y -> Prop) (t u : ctree E B A) :
  t ≅ u -> Framable okE t -> Framable okE u.
Proof. intros H Ht; exact (proj1 (framable_chain_equ okE (R := chain_gfp _) t u H) Ht). Qed.

Local Lemma framable_guards {E B A} (okE : forall Y, E Y -> Prop) n (u : ctree E B A) :
  Framable okE (guards n u) -> Framable okE u.
Proof.
  induction n as [|n IH]; cbn [guards]; [easy|intro H].
  apply framable_unfold in H; cbn in H; dependent destruction H; auto.
Qed.

Local Lemma headed_framable r t u :
  Framable (okE_thread (okR r)) t -> headed t u -> Framable (okE_thread (okR r)) u.
Proof. intros Ht [n Hn]; eapply framable_guards, framable_equ; eauto. Qed.

Local Lemma framable_vis_inv {E B A Y} (okE : forall Y, E Y -> Prop) (e : E Y) (k : Y -> ctree E B A) :
  Framable okE (Vis e k) -> okE Y e /\ forall x, Framable okE (k x).
Proof. intro H; apply framable_unfold in H; cbn in H; dependent destruction H; auto. Qed.

Local Lemma framable_step_inv {E B A} (okE : forall Y, E Y -> Prop) (t : ctree E B A) :
  Framable okE (Step t) -> Framable okE t.
Proof. intro H; apply framable_unfold in H; cbn in H; dependent destruction H; auto. Qed.

Local Ltac fr_trig :=
  unfold heap_read, heap_write, heap_free, heap_cas, heap_alloc, source_get, source_put,
    source_yield, source_fork, CTree.trigger;
  apply fr_vis; [cbn; first [exact I|assumption]|intro; apply fr_ret].

Local Lemma exp_framable r e : Framable (okE_thread (okR r)) (denote_exp e).
Proof.
  apply denote_exp_framable.
  induction e; cbn; repeat split; assumption.
Qed.

Local Lemma addr_ok_framable r {A} (p : CProg A) :
  addr_ok r p -> Framable (okE_thread (okR r)) (denote_flow p).
Proof.
  induction p as [a|a v|q v| |body IH|A x|A B body IH next IHnext|A body IH|size|base
    |a expected desired|e|name e|A test yes IHyes no IHno|test body IH];
    cbn [denote_flow addr_ok]; intro Hp.
  - apply framable_bind; [fr_trig|intro x; apply fr_ret].
  - apply framable_bind; [fr_trig|intros []; apply fr_ret].
  - apply framable_bind; [fr_trig|intros []; apply fr_ret].
  - apply framable_bind; [fr_trig|intros []; apply fr_ret].
  - apply framable_bind; [fr_trig|].
    intros []; cbn.
    + apply framable_bind; [exact (IH Hp)|intro flow; apply fr_ret].
    + apply fr_ret.
  - apply fr_ret.
  - destruct Hp as [Hb Hn].
    apply framable_bind; [exact (IH Hb)|].
    intros [x|]; [apply IHnext, Hn|apply fr_ret].
  - apply framable_iter; intros [].
    apply framable_bind; [exact (IH Hp)|].
    intros [[x|]|]; apply fr_ret.
  - apply framable_bind; [fr_trig|intro a; apply fr_ret].
  - apply framable_bind; [fr_trig|intros []; apply fr_ret].
  - destruct a as [|a| | |]; try contradiction; cbn [denote_exp].
    eapply framable_equ; [symmetry; apply bind_ret_l|].
    apply framable_bind; [apply exp_framable|intro old].
    apply framable_bind; [apply exp_framable|intro value].
    apply framable_bind; [fr_trig|intro b; apply fr_ret].
  - apply framable_bind; [apply exp_framable|intro v; apply fr_ret].
  - apply framable_bind; [apply exp_framable|intro v].
    apply framable_bind; [fr_trig|].
    intro ctx; apply framable_bind; [fr_trig|intros []; apply fr_ret].
  - destruct Hp as [Hy Hn].
    apply framable_bind; [apply exp_framable|intro v].
    destruct (CoCSLSyntax.is_true v); auto.
  - apply framable_iter; intros [].
    apply framable_bind; [apply exp_framable|intro v].
    destruct (CoCSLSyntax.is_true v); [|apply fr_ret].
    apply framable_bind; [exact (IH Hp)|].
    intros [[]|]; apply fr_ret.
Qed.

Local Definition confined_pool_ok r (c : OwnedCfg) : Prop := pool_framable (okR r) (tp_threads (oc_pool c)).

Local Lemma confined_pool_ok_step r c a c' : confined_pool_ok r c -> owned_step c a c' -> confined_pool_ok r c'.
Proof.
  unfold confined_pool_ok, owned_step; destruct (oc_pool c) as [n v g f]; cbn.
  destruct n as [|n]; [contradiction|].
  destruct f as [j|]; intros Hv Hs.
  2: { destruct Hs as (j & -> & ->); exact Hv. }
  pose proof (Hv j) as Hj.
  destruct Hs as [(t & Hh & -> & ->)|[(k & Hh & -> & ->)|[(k & Hh & -> & ->)
    |[(Hh & -> & ->)|(Y & e & k & kind & y & c1 & Hh & Hp & -> & ->)]]]]; cbn;
    try (apply (headed_framable r) in Hh; [|exact Hj]).
  - apply pool_framable_replace; [exact Hv|exact (framable_step_inv _ _ Hh)].
  - apply pool_framable_replace; [exact Hv|exact (proj2 (framable_vis_inv _ _ _ Hh) tt)].
  - apply framable_vis_inv in Hh as [_ Hk].
    apply pool_framable_cons; [apply Hk|apply pool_framable_replace; [exact Hv|apply Hk]].
  - apply pool_framable_remove, Hv.
  - apply pool_framable_replace; [exact Hv|exact (proj2 (framable_vis_inv _ _ _ Hh) y)].
Qed.

Local Lemma pool_ok_reach r c c' : clos_refl_trans _ owned_next c c' -> confined_pool_ok r c -> confined_pool_ok r c'.
Proof.
  induction 1 as [c c' [a Hs]| |]; auto.
  intro; eapply confined_pool_ok_step; eauto.
Qed.

Lemma addr_ok_confined r i p h ctx base focused :
  addr_ok r p -> confined r (init_local i p h ctx base focused).
Proof.
  intros Hp c Hc t j Y e k Hf Hh.
  assert (Hv : confined_pool_ok r c).
  { apply (pool_ok_reach _ _ _ Hc); intro x; dependent destruction x; [|inversion x].
    apply framable_bind; [apply addr_ok_framable, Hp|intro; apply fr_ret]. }
  unfold focused_thread in Hf; destruct (tp_focus (oc_pool c)) as [x|]; [|discriminate].
  injection Hf as <- _.
  exact (proj1 (framable_vis_inv _ _ _ (headed_framable r _ _ (Hv x) Hh))).
Qed.

Lemma admissible_intro child parent h h' ctx base :
  managed_wf h -> managed_wf h' -> h # h' ->
  component_ok child -> component_ok parent ->
  addr_ok h child -> addr_ok h' parent ->
  admissible child parent h h' ctx base.
Proof.
  intros; do 5 (split; [assumption|]); split.
  - eapply confined_equ; [symmetry; apply project_init_child|apply addr_ok_confined; assumption].
  - eapply confined_equ; [symmetry; apply project_init_parent|apply addr_ok_confined; assumption].
Qed.

Lemma admissible_head_confined child parent h h' ctx base d :
  admissible child parent h h' ctx base ->
  clos_refl_trans _ owned_next (init_owned child parent h h' ctx base) d ->
  head_confined d.
Proof.
  intros (_ & _ & _ & _ & _ & HC & HP) Hd t i Y e k Hf Hh.
  assert (Ha : oc_anchor d = oc_anchor (init_owned child parent h h' ctx base)).
  { clear - Hd; induction Hd as [c c' [a Hs]| |]; auto.
    - apply (owned_step_frozen _ _ _ Hs).
    - congruence. }
  rewrite Ha.
  pose proof (focused_project i _ _ Hf) as Hfp.
  destruct (reach_project i _ _ Hd) as (d0 & Hr0 & Heq0).
  destruct (focused_thread_equ _ _ _ _ (proj1 Heq0) Hfp) as (t' & Hf0 & Ht).
  assert (Hh' : headed t' (Vis (inr1 (inr1 e) : CEff Y) k))
    by (eapply headed_equ; [symmetry; exact Ht|exact Hh]).
  destruct i; [exact (HC d0 Hr0 _ _ _ _ _ Hf0 Hh')|exact (HP d0 Hr0 _ _ _ _ _ Hf0 Hh')].
Qed.

Local Lemma denote_thread_ok p : component_ok p -> Framable (okE_thread component_event_ok) (denote p) /\ BranchFree (denote p).
Proof.
  intro Hp; split; [|apply denote_branchfree].
  unfold denote; apply framable_bind; [apply denote_flow_framable, Hp|intro; apply fr_ret].
Qed.

Lemma admissible_erasable child parent h h' ctx base :
  admissible child parent h h' ctx base -> erasable (init_owned child parent h h' ctx base).
Proof.
  intro Ha; pose proof Ha as (Wh & Wh' & D & Oc & Op & _).
  destruct (denote_thread_ok child Oc) as [Fc Bc].
  destruct (denote_thread_ok parent Op) as [Fp Bp].
  split; [apply init_owned_wf; assumption|split].
  - apply pool_framable_cons; [exact Fc|].
    apply pool_framable_cons; [exact Fp|intro i; inversion i].
  - split.
    + apply pool_branchfree_cons; [exact Bc|].
      apply pool_branchfree_cons; [exact Bp|intro i; inversion i].
    + intros d Hd; exact (admissible_head_confined _ _ _ _ _ _ _ Ha Hd).
Qed.

Lemma coupled_erasable c : coupled c -> erasable c.
Proof.
  intros (child & parent & h & h' & ctx & base & d & Ha & Hd & E).
  exact (erasable_equ d c E (erasable_reach _ d (admissible_erasable _ _ _ _ _ _ Ha) Hd)).
Qed.

Lemma admissible_active_erasable child parent h h' ctx base :
  admissible child parent h h' ctx base ->
  active_erasable (init_owned child parent h h' ctx base).
Proof.
  intro Ha; pose proof Ha as (_ & _ & _ & _ & _ & HC & HP).
  pose proof (admissible_erasable _ _ _ _ _ _ Ha) as He.
  pose proof He as (W & F & Bf & _).
  assert (HL : forall i, erasable (project i (init_owned child parent h h' ctx base))).
  { intro i; apply (erasable_single_side i).
    - apply owned_wf_project; exact W.
    - intro r; destruct (project_index_inv i
        (oc_pool (init_owned child parent h h' ctx base)) r) as (j & _ & _ & _ & Htag).
      exact Htag.
    - intro r; destruct (project_index_inv i
        (oc_pool (init_owned child parent h h' ctx base)) r) as (j & _ & _ & Et & _).
      change (Framable (okE_thread component_event_ok)
        (tp_threads (project_pool i (oc_pool (init_owned child parent h h' ctx base))) $ r)).
      rewrite Et; apply F.
    - intro r; destruct (project_index_inv i
        (oc_pool (init_owned child parent h h' ctx base)) r) as (j & _ & _ & Et & _).
      change (BranchFree
        (tp_threads (project_pool i (oc_pool (init_owned child parent h h' ctx base))) $ r)).
      rewrite Et; apply Bf.
    - destruct i; [exact HC|exact HP]. }
  exact (conj He (conj (HL Child) (HL Parent))).
Qed.

Lemma coupled_active_erasable c : coupled c -> active_erasable c.
Proof.
  intros (child & parent & h & h' & ctx & base & d & Ha & Hd & E).
  eapply active_erasable_equ; [exact E|].
  clear E.
  pose proof (admissible_active_erasable _ _ _ _ _ _ Ha) as H0.
  revert H0; induction Hd as [x y [a Hs]|x|x y z _ IH1 _ IH2]; intro H0.
  - eapply active_erasable_step; eauto.
  - exact H0.
  - apply IH2, IH1, H0.
Qed.

From TICL Require Import Lang.CoCSL.Sequential.

Theorem owned_fork_runner (child : CProg unit) (k : unit -> CProg unit) h h' ctx base :
  owned_interp (init_owned child (k tt) h h' ctx base) ~
  run_nd (CBind (CFork child) k) (h ⊎ h', (ctx, base)).
Proof.
  rewrite run_nd_fork_bind.
  unfold owned_interp, init_owned, init_owned_threads, joined_state, joined_heap, global_count.
  cbn; rewrite !Nat.add_0_r; reflexivity.
Qed.

