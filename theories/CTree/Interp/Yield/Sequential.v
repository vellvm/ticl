(** * Sequential thread segments and the cooperative prefix equation.

    A [Sequential] raw thread has no yield, fork or hidden branch anywhere:
    only returns, [Stuck], guards, visible steps and user events.  A focused
    pool slot whose head segment is sequential runs in the scheduled pool
    exactly as its standalone erased run ([interp_thread]), then rejoins the
    pool with the residual continuation — for both schedulers. *)

From Stdlib Require Import Fin Vector Morphisms Program.Equality.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Interp.Refine
  CTree.Events.Yield
  CTree.Events.Writer
  CTree.Logic.Sim
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.Policy
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.Nondeterministic
  CTree.Interp.State.Mod
  Utils.Vectors.

Import CTreeNotations VectorNotations CoindNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** Only user events: yields and forks are rejected. *)
Definition user_only {E} : forall Y, (yieldE +' (forkE +' E)) Y -> Prop :=
  fun Y e => match e with inr1 (inr1 _) => True | _ => False end.

(** A sequential raw thread is branch-free and has no yield/fork events;
    reuse the existing coinductive predicates instead of a third tower. *)
Definition Sequential {E B X} (t : ctree (yieldE +' (forkE +' E)) B X) : Prop :=
  BranchFree t /\ Framable user_only t.

(** Node shapes of a sequential thread, for inversion only. *)
Variant sequentialF {E B X} (R : ctree (yieldE +' (forkE +' E)) B X -> Prop)
  : ctree' (yieldE +' (forkE +' E)) B X -> Prop :=
| SqRetF x : sequentialF R (RetF x)
| SqStuckF : sequentialF R StuckF
| SqGuardF t : R t -> sequentialF R (GuardF t)
| SqStepF t : R t -> sequentialF R (StepF t)
| SqVisF {Y} (e : E Y) k : (forall y, R (k y)) -> sequentialF R (VisF (inr1 (inr1 e)) k).

(** Expose the node of a branch-free, user-only thread. *)
Lemma sequential_inv {E B X} (t : ctree (yieldE +' (forkE +' E)) B X) :
  Sequential t -> sequentialF Sequential (observe t).
Proof.
  intros [HB HF]; apply branchfree_unfold in HB; apply framable_unfold in HF.
  remember (observe t) as ot; destruct HB; ddestruction HF;
    try solve [constructor; intros; split; auto].
  destruct e as [y|[f|e]]; cbn [user_only] in *; try contradiction.
  constructor; intros; split; auto.
Qed.

(** ** Erasure of a standalone thread, node by node ([interp_thread]). *)
Section ThreadNodes.
  Context {E B : Type -> Type} {X : Type}.

  (** Standalone erasure of a stuck thread is stuck. *)
  Lemma interp_thread_stuck_node :
    interp_thread (Stuck : ctree (yieldE +' (forkE +' E)) B X) ≅ Stuck.
  Proof.
    unfold interp_thread, interp_yield.
    rewrite interp_stuck, interp_stuck; reflexivity.
  Qed.

  (** Standalone erasure commutes with a leading guard. *)
  Lemma interp_thread_guard_node (t : ctree (yieldE +' (forkE +' E)) B X) :
    interp_thread (Guard t) ≅ Guard (interp_thread t).
  Proof.
    unfold interp_thread, interp_yield.
    rewrite interp_guard, interp_guard; reflexivity.
  Qed.

  (** Standalone erasure turns a visible step into a step followed by two guards. *)
  Lemma interp_thread_step_node (t : ctree (yieldE +' (forkE +' E)) B X) :
    interp_thread (Step t) ≅ Step (Guard (Guard (interp_thread t))).
  Proof.
    unfold interp_thread, interp_yield.
    rewrite interp_step, interp_step, interp_guard; reflexivity.
  Qed.
End ThreadNodes.

(** ** Guard alignment closed under a shared bind prefix.

    [align_rel Base] relates [Base] pairs under any number of leading guards,
    identical trees, and any pair with the same prefix [h] whose continuations
    are themselves related.  It is a [galigned] post-fixpoint whenever every
    [Base] pair aligns, hence is contained in [~]. *)
Section AlignBind.
  Context {F B : Type -> Type} {X : Type}.
  Variable Base : ctree F B X -> ctree F B X -> Prop.

  (** Close a base relation under leading guards, [≅], and shared bind prefixes with related continuations: exactly one scheduler turn. *)
  Inductive align_rel : ctree F B X -> ctree F B X -> Prop :=
  | align_at a b t u T U :
      Base t u -> T ≅ guards a t -> U ≅ guards b u -> align_rel T U
  | align_equ T U : T ≅ U -> align_rel T U
  | align_bind a b {Z} (h : ctree F B Z) (f g : Z -> ctree F B X) T U :
      (forall z, align_rel (f z) (g z)) ->
      T ≅ guards a (h >>= fun z => Guard (f z)) ->
      U ≅ guards b (h >>= fun z => Guard (g z)) ->
      align_rel T U.

  (** Equivalent trees have aligned nodes. *)
  Lemma align_equ_step T U : T ≅ U -> galignF align_rel T U.
  Proof.
    intro H.
    pose proof (ctree_eta T) as ET.
    assert (EU : U ≅ go (observe T)) by (rewrite <- H; exact ET).
    destruct (observe T) as [r| |s|g|Z e k|Z c k].
    - apply (galignF_ret _ T U 0 0 r); assumption.
    - apply (galignF_stuck _ T U 0 0); assumption.
    - apply (galignF_step _ T U 0 0 s s); [exact ET|exact EU|apply align_equ; reflexivity].
    - apply (galignF_guard _ T U 0 0 g g); [exact ET|exact EU|apply align_equ; reflexivity].
    - apply (galignF_vis _ T U 0 0 e k k); [exact ET|exact EU|intro; apply align_equ; reflexivity].
    - apply (galignF_br _ T U 0 0 c k k); [exact ET|exact EU|intro; apply align_equ; reflexivity].
  Qed.

  (** A common bind prefix with related continuations has aligned nodes. *)
  Lemma align_bind_step a b {Z} (h : ctree F B Z) (f g : Z -> ctree F B X) T U :
    (forall z, align_rel (f z) (g z)) ->
    T ≅ guards a (h >>= fun z => Guard (f z)) ->
    U ≅ guards b (h >>= fun z => Guard (g z)) ->
    galignF align_rel T U.
  Proof.
    intros Hfg ET EU.
    destruct (observe h) as [z| |s|g'|W e kk|W c kk] eqn:Hh;
      pose proof (observe_equ_go h _ Hh) as Eh.
    - apply (galignF_guard _ T U a b (f z) (g z)).
      + rewrite ET, Eh, bind_ret_l, guards_guard; reflexivity.
      + rewrite EU, Eh, bind_ret_l, guards_guard; reflexivity.
      + apply Hfg.
    - apply (galignF_stuck _ T U a b).
      + rewrite ET, Eh, bind_stuck; reflexivity.
      + rewrite EU, Eh, bind_stuck; reflexivity.
    - apply (galignF_step _ T U a b (s >>= fun z => Guard (f z)) (s >>= fun z => Guard (g z))).
      + rewrite ET, Eh, bind_step; reflexivity.
      + rewrite EU, Eh, bind_step; reflexivity.
      + apply (align_bind 0 0 s f g); [exact Hfg|reflexivity|reflexivity].
    - apply (galignF_guard _ T U a b (g' >>= fun z => Guard (f z)) (g' >>= fun z => Guard (g z))).
      + rewrite ET, Eh, bind_guard, guards_guard; reflexivity.
      + rewrite EU, Eh, bind_guard, guards_guard; reflexivity.
      + apply (align_bind 0 0 g' f g); [exact Hfg|reflexivity|reflexivity].
    - apply (galignF_vis _ T U a b e
        (fun w => kk w >>= fun z => Guard (f z)) (fun w => kk w >>= fun z => Guard (g z))).
      + rewrite ET, Eh, bind_vis; reflexivity.
      + rewrite EU, Eh, bind_vis; reflexivity.
      + intro w; apply (align_bind 0 0 (kk w) f g); [exact Hfg|reflexivity|reflexivity].
    - apply (galignF_br _ T U a b c
        (fun w => kk w >>= fun z => Guard (f z)) (fun w => kk w >>= fun z => Guard (g z))).
      + rewrite ET, Eh, bind_br; reflexivity.
      + rewrite EU, Eh, bind_br; reflexivity.
      + intro w; apply (align_bind 0 0 (kk w) f g); [exact Hfg|reflexivity|reflexivity].
  Qed.

  (** Leading finite guard prefixes preserve node alignment. *)
  Lemma galignF_guards a b t u T U :
    galignF align_rel t u -> T ≅ guards a t -> U ≅ guards b u -> galignF align_rel T U.
  Proof.
    intros H ET EU; destruct H as
      [t u n m t' u' El Er H|t u n m r El Er|t u n m Y c k k' El Er H
      |t u n m Y e k k' El Er H|t u n m El Er|t u n m t' u' El Er H].
    - apply (galignF_guard _ T U (a + n) (b + m) t' u');
        [rewrite ET, El, guards_shift; reflexivity|rewrite EU, Er, guards_shift; reflexivity|exact H].
    - apply (galignF_ret _ T U (a + n) (b + m) r);
        [rewrite ET, El, <- guards_add; reflexivity|rewrite EU, Er, <- guards_add; reflexivity].
    - apply (galignF_br _ T U (a + n) (b + m) c k k');
        [rewrite ET, El, <- guards_add; reflexivity|rewrite EU, Er, <- guards_add; reflexivity|exact H].
    - apply (galignF_vis _ T U (a + n) (b + m) e k k');
        [rewrite ET, El, <- guards_add; reflexivity|rewrite EU, Er, <- guards_add; reflexivity|exact H].
    - apply (galignF_stuck _ T U (a + n) (b + m));
        [rewrite ET, El, <- guards_add; reflexivity|rewrite EU, Er, <- guards_add; reflexivity].
    - apply (galignF_step _ T U (a + n) (b + m) t' u');
        [rewrite ET, El, <- guards_add; reflexivity|rewrite EU, Er, <- guards_add; reflexivity|exact H].
  Qed.

  Hypothesis Hbase : forall t u, Base t u -> galignF align_rel t u.

  (** The alignment closure is a post-fixpoint when every base pair aligns. *)
  Lemma align_rel_step T U : align_rel T U -> galignF align_rel T U.
  Proof.
    intros [a b t u T' U' Hb ET EU|T' U' H|a b Z h f g T' U' Hfg ET EU].
    - exact (galignF_guards a b t u T' U' (Hbase t u Hb) ET EU).
    - exact (align_equ_step T' U' H).
    - exact (align_bind_step a b h f g T' U' Hfg ET EU).
  Qed.

End AlignBind.

(** ** The cooperative prefix equation, generically over the scheduling policy.

    A focused sequential segment preserves the policy state until it rejoins
    the pool; the scheduled observations are projected to silent steps. *)
Section Prefix.
  Context {E F B : Type -> Type} {HB : Bn -< B} {Σ : Type}
    (handler : E ~> stateT Σ (ctree F B))
    (sch : Scheduler) (st : sched_state sch)
    (n : nat) (ts : pool E B (S n)) (i : Fin.t (S n))
    {Y : Type} (K : Y -> thread E B).

  (** Run the focused pool under the direct scheduling policy. *)
  Let run (ts' : pool E B (S n)) (σ : Σ) : ctree F B (Σ * unit) :=
    interp_state handler (project_scheduled (schedule_policy sch (S n) ts' (Some i) st)) σ.

  (** Rejoin the pool with the focused continuation and its resulting state. *)
  Let rhs_k : Σ * Y -> ctree F B (Σ * unit) :=
    fun '(σ', y) => run (ts @ i := K y) σ'.

  (** Exact [≅] congruence for one focused node. *)
  Lemma run_slot_equ t t' σ :
    t ≅ t' -> run (ts @ i := t) σ ≅ run (ts @ i := t') σ.
  Proof.
    intro H; unfold run.
    now rewrite (schedule_policy_pool_proper sch (S n) _ _ (Some i) st
      (replace_pool_equ ts ts i t t' (pool_equ_refl ts) H)).
  Qed.

  (** Exact [≅] equation for a focused stuck node. *)
  Lemma run_slot_stuck t σ : t ≅ Stuck -> run (ts @ i := t) σ ≅ Stuck.
  Proof.
    intro H; rewrite (run_slot_equ _ Stuck σ H); unfold run.
    assert (Hobs : observe ((ts @ i := Stuck) $ i) = StuckF)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite (observe_equ_go _ _ (schedule_policy_focused_stuck sch n _ i st Hobs)).
    rewrite project_scheduled_stuck, interp_state_stuck; reflexivity.
  Qed.

  (** Exact [≅] equation for a focused guard. *)
  Lemma run_slot_guard t σ :
    run (ts @ i := Guard t) σ ≅ Guard (run (ts @ i := t) σ).
  Proof.
    unfold run.
    assert (Hobs : observe ((ts @ i := Guard t) $ i) = GuardF t)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite (observe_equ_go _ _ (schedule_policy_focused_guard sch n _ i t st Hobs)).
    rewrite project_scheduled_guard, interp_state_guard, Vector.replace_replace_eq.
    reflexivity.
  Qed.

  (** Exact [≅] equation for a focused step. *)
  Lemma run_slot_step t σ :
    run (ts @ i := Step t) σ ≅ Step (Guard (Guard (run (ts @ i := t) σ))).
  Proof.
    unfold run.
    assert (Hobs : observe ((ts @ i := Step t) $ i) = StepF t)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite (observe_equ_go _ _ (schedule_policy_focused_step sch n _ i t st Hobs)).
    rewrite project_scheduled_step, interp_state_step, interp_state_guard,
      Vector.replace_replace_eq.
    reflexivity.
  Qed.

  (** Exact [≅] equation for a focused user event. *)
  Lemma run_slot_user {Z} (e : E Z) k σ :
    run (ts @ i := Vis (inr1 (inr1 e)) k) σ ≅
    (handler _ e σ >>= fun sx => Guard (Guard (run (ts @ i := k (snd sx)) (fst sx)))).
  Proof.
    unfold run.
    assert (Hobs : observe ((ts @ i := Vis (inr1 (inr1 e)) k) $ i) = VisF (inr1 (inr1 e)) k)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite (observe_equ_go _ _ (schedule_policy_focused_user_event sch n _ i e k st Hobs)).
    rewrite project_scheduled_user, interp_state_vis.
    upto_bind_eq; intro sx.
    rewrite interp_state_guard, Vector.replace_replace_eq.
    reflexivity.
  Qed.

  (** Scheduled sequential segment versus its standalone erased run followed by rejoin. *)
  Variant prefix_base : ctree F B (Σ * unit) -> ctree F B (Σ * unit) -> Prop :=
  | prefix_base_at w σ :
      Sequential w ->
      prefix_base (run (ts @ i := (w >>= K)) σ)
                  (interp_state handler (interp_thread w) σ >>= rhs_k).

  (** One node of a sequential segment aligns the scheduled and standalone runs. *)
  Lemma prefix_base_step t u : prefix_base t u -> galignF (align_rel prefix_base) t u.
  Proof.
    intros [w σ Hw].
    apply sequential_inv in Hw.
    pose proof (ctree_eta w) as Ew; revert Ew.
    destruct Hw as [y| |w' Hw'|w' Hw'|Z e k Hk]; intro Ew.
    - (* Ret: the slot is the continuation; both sides are the same pool. *)
      apply align_equ_step.
      rewrite (run_slot_equ _ (K y) σ) by (rewrite Ew, bind_ret_l; reflexivity).
      rewrite Ew, interp_state_thread_ret, bind_ret_l; reflexivity.
    - apply (galignF_stuck _ _ _ 0 0).
      + apply run_slot_stuck; rewrite Ew, bind_stuck; reflexivity.
      + rewrite Ew, interp_thread_stuck_node, interp_state_stuck, bind_stuck; reflexivity.
    - apply (galignF_guard _ _ _ 0 0
        (run (ts @ i := (w' >>= K)) σ) (interp_state handler (interp_thread w') σ >>= rhs_k)).
      + rewrite (run_slot_equ _ (Guard (w' >>= K)) σ) by (rewrite Ew, bind_guard; reflexivity).
        rewrite run_slot_guard; reflexivity.
      + rewrite Ew, interp_thread_guard_node, interp_state_guard, bind_guard; reflexivity.
      + apply (align_at _ 0 0 _ _ _ _ (prefix_base_at w' σ Hw')); reflexivity.
    - apply (galignF_step _ _ _ 0 0
        (Guard (Guard (run (ts @ i := (w' >>= K)) σ)))
        (Guard (Guard (Guard (interp_state handler (interp_thread w') σ >>= rhs_k))))).
      + rewrite (run_slot_equ _ (Step (w' >>= K)) σ) by (rewrite Ew, bind_step; reflexivity).
        rewrite run_slot_step; reflexivity.
      + rewrite Ew, interp_thread_step_node, interp_state_step, interp_state_guard,
          interp_state_guard, bind_step, bind_guard, bind_guard, bind_guard; reflexivity.
      + apply (align_at _ 2 3 _ _ _ _ (prefix_base_at w' σ Hw')); reflexivity.
    - apply (align_bind_step _ 0 0 (handler _ e σ)
        (fun sx => Guard (run (ts @ i := (k (snd sx) >>= K)) (fst sx)))
        (fun sx => Guard (Guard (interp_state handler (interp_thread (k (snd sx))) (fst sx) >>= rhs_k)))).
      + intro sx; apply (align_at _ 1 2 _ _ _ _ (prefix_base_at (k (snd sx)) (fst sx) (Hk _))); reflexivity.
      + cbn [guards].
        rewrite (run_slot_equ _ (Vis (inr1 (inr1 e)) (fun z => k z >>= K)) σ)
          by (rewrite Ew, bind_vis; reflexivity).
        rewrite run_slot_user; reflexivity.
      + cbn [guards].
        rewrite Ew, interp_thread_user_node, interp_state_vis.
        change (Monad.bind ?a ?b) with (CTree.bind a b); rewrite bind_bind.
        upto_bind_eq; intro sx.
        rewrite bind_guard, interp_state_guard, interp_state_guard, bind_guard, bind_guard.
        reflexivity.
  Qed.

  (** A focused sequential segment runs standalone and then rejoins its pool. *)
  Lemma run_prefix_bind (w : ctree (yieldE +' (forkE +' E)) B Y) σ :
    Sequential w ->
    run (ts @ i := (w >>= K)) σ ~ (interp_state handler (interp_thread w) σ >>= rhs_k).
  Proof.
    intro Hw.
    apply galigned_sbisim, (galigned_coind (align_rel prefix_base) (align_rel_step prefix_base prefix_base_step)),
      (align_at _ 0 0 _ _ _ _ (prefix_base_at w σ Hw)); reflexivity.
  Qed.
End Prefix.

(** A focused sequential interval never invokes the policy. Its observations
    are only relabelled user logs, with the same actual pool continuation. *)
Section FairPrefix.
  Context {E : Type -> Type} {W Sigma X : Type}
    (sch : Scheduler) (handler : E ~> stateT Sigma (ctreeW W Bn))
    (st : sched_state sch) (n : nat) (ts : pool E Bn (S n))
    (i : Fin.t (S n)) (K : X -> thread E Bn).

  Local Notation "'run' us sigma" :=
    (interp_schedule_fair sch handler (S n) us (Some i) st sigma)
    (at level 10, us at next level, sigma at next level).

  Local Lemma fair_prefix_slot_equ t u sigma :
    t ≅ u -> run (ts @ i := t) sigma ≅ run (ts @ i := u) sigma.
  Proof.
    intro H; apply interp_schedule_fair_equ;
      exact (replace_pool_equ ts ts i t u (pool_equ_refl ts) H).
  Qed.

  Local Lemma fair_prefix_slot_guard t sigma :
    run (ts @ i := Guard t) sigma ≅ Guard (run (ts @ i := t) sigma).
  Proof.
    assert (Hobs : observe ((ts @ i := Guard t) $ i) = GuardF t)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    unfold interp_schedule_fair.
    rewrite (observe_equ_go _ _ (schedule_policy_focused_guard sch n
      (ts @ i := Guard t) i t st Hobs)).
    rewrite interp_state_guard, Vector.replace_replace_eq; reflexivity.
  Qed.

  Local Lemma fair_prefix_slot_step t sigma :
    run (ts @ i := Step t) sigma ≅ Step (Guard (run (ts @ i := t) sigma)).
  Proof.
    assert (Hobs : observe ((ts @ i := Step t) $ i) = StepF t)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    unfold interp_schedule_fair.
    rewrite (observe_equ_go _ _ (schedule_policy_focused_step sch n
      (ts @ i := Step t) i t st Hobs)).
    rewrite interp_state_step, Vector.replace_replace_eq; reflexivity.
  Qed.

  Local Lemma fair_prefix_slot_user {Y} (e : E Y) k sigma :
    run (ts @ i := Vis (inr1 (inr1 e)) k) sigma ≅
    (translate relabel_log (handler _ e sigma) >>= fun sx =>
      Guard (run (ts @ i := k (snd sx)) (fst sx))).
  Proof.
    assert (Hobs : observe ((ts @ i := Vis (inr1 (inr1 e)) k) $ i) =
      VisF (inr1 (inr1 e)) k) by (rewrite Vector.nth_replace_eq; reflexivity).
    unfold interp_schedule_fair.
    rewrite (observe_equ_go _ _ (schedule_policy_focused_user_event sch n
      (ts @ i := Vis (inr1 (inr1 e)) k) i e k st Hobs)).
    rewrite interp_state_vis; cbn [policy_handler h_sum].
    upto_bind_eq; intros [sigma' x]; cbn.
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  Variant fair_prefix_base :
    ctreeW (W + nat) Bn (Sigma * unit) -> ctreeW (W + nat) Bn (Sigma * unit) -> Prop :=
  | fair_prefix_at t sigma : Sequential t ->
      fair_prefix_base (run (ts @ i := (t >>= K)) sigma)
        (translate relabel_log (interp_state handler (interp_thread t) sigma) >>=
          fun '(sigma',x) => run (ts @ i := K x) sigma').

  Local Lemma fair_prefix_base_step T U :
    fair_prefix_base T U -> galignF (align_rel fair_prefix_base) T U.
  Proof.
    intros [t sigma Ht]; apply sequential_inv in Ht.
    pose proof (ctree_eta t) as Et; revert Et.
    destruct Ht as [x| |t' Ht'|t' Ht'|Y e k Hk]; intro Et.
    - apply align_equ_step.
      rewrite (fair_prefix_slot_equ _ (K x) sigma) by (rewrite Et, bind_ret_l; reflexivity).
      rewrite Et, interp_state_thread_ret, translate_ret, bind_ret_l; reflexivity.
    - apply (galignF_stuck _ _ _ 0 0).
      + apply interp_schedule_fair_stuck; rewrite Vector.nth_replace_eq, Et, bind_stuck; reflexivity.
      + rewrite Et, interp_thread_stuck_node, interp_state_stuck.
        rewrite (unfold_translate (Stuck : ctreeW W Bn (Sigma * X)) relabel_log); cbn.
        rewrite bind_stuck; reflexivity.
    - apply (galignF_guard _ _ _ 0 0
        (run (ts @ i := (t' >>= K)) sigma)
        (translate relabel_log (interp_state handler (interp_thread t') sigma) >>=
          fun '(sigma',x) => run (ts @ i := K x) sigma')).
      + rewrite (fair_prefix_slot_equ _ (Guard (t' >>= K)) sigma)
          by (rewrite Et, bind_guard; reflexivity).
        rewrite fair_prefix_slot_guard; reflexivity.
      + rewrite Et, interp_thread_guard_node, interp_state_guard, translate_guard, bind_guard; reflexivity.
      + apply (align_at _ 0 0 _ _ _ _ (fair_prefix_at t' sigma Ht')); reflexivity.
    - apply (galignF_step _ _ _ 0 0
        (Guard (run (ts @ i := (t' >>= K)) sigma))
        (guards 3 (translate relabel_log (interp_state handler (interp_thread t') sigma) >>=
          fun '(sigma',x) => run (ts @ i := K x) sigma'))).
      + rewrite (fair_prefix_slot_equ _ (Step (t' >>= K)) sigma)
          by (rewrite Et, bind_step; reflexivity).
        rewrite fair_prefix_slot_step; reflexivity.
      + rewrite Et, interp_thread_step_node, interp_state_step, !interp_state_guard,
          translate_step, !translate_guard, bind_step, !bind_guard; reflexivity.
      + apply (align_at _ 1 3 _ _ _ _ (fair_prefix_at t' sigma Ht')); reflexivity.
    - apply (align_bind_step _ 0 0 (translate relabel_log (handler _ e sigma))
        (fun sx => run (ts @ i := (k (snd sx) >>= K)) (fst sx))
        (fun sx => guards 2
          (translate relabel_log (interp_state handler (interp_thread (k (snd sx))) (fst sx)) >>=
            fun '(sigma',x) => run (ts @ i := K x) sigma'))).
      + intro sx; apply (align_at _ 0 2 _ _ _ _ (fair_prefix_at (k (snd sx)) (fst sx) (Hk _))); reflexivity.
      + rewrite (fair_prefix_slot_equ _ (Vis (inr1 (inr1 e)) (fun x => k x >>= K)) sigma)
          by (rewrite Et, bind_vis; reflexivity).
        rewrite fair_prefix_slot_user; reflexivity.
      + rewrite Et, interp_thread_user_node, interp_state_vis.
        change (Monad.bind ?a ?b) with (CTree.bind a b).
        rewrite translate_bind, bind_bind.
        upto_bind_eq; intros [sigma' x]; cbn.
        rewrite !interp_state_guard, !translate_guard, !bind_guard; reflexivity.
  Qed.

  Local Lemma fair_prefix_bind t sigma :
    Sequential t -> run (ts @ i := (t >>= K)) sigma ~
    (translate relabel_log (interp_state handler (interp_thread t) sigma) >>=
      fun '(sigma',x) => run (ts @ i := K x) sigma').
  Proof.
    intro Ht; apply galigned_sbisim,
      (galigned_coind (align_rel fair_prefix_base)
        (align_rel_step fair_prefix_base fair_prefix_base_step)),
      (align_at _ 0 0 _ _ _ _ (fair_prefix_at t sigma Ht)); reflexivity.
  Qed.
End FairPrefix.

Lemma interp_schedule_fair_prefix_bind {E : Type -> Type} {W Sigma X : Type}
    (sch : Scheduler) (handler : E ~> stateT Sigma (ctreeW W Bn))
    n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    (t : ctree (yieldE +' (forkE +' E)) Bn X) (K : X -> thread E Bn)
    (st : sched_state sch) sigma :
  Sequential t ->
  interp_schedule_fair sch handler (S n) (ts @ i := (t >>= K)) (Some i) st sigma ~
  (translate relabel_log (interp_state handler (interp_thread t) sigma) >>=
    fun '(sigma',x) =>
      interp_schedule_fair sch handler (S n) (ts @ i := K x) (Some i) st sigma').
Proof. exact (fair_prefix_bind sch handler st n ts i K t sigma). Qed.

(** Round-robin join principle for a focused sequential segment. *)
Lemma interp_schedule_rr_prefix_bind {E : Type -> Type} {W Σ : Type}
  (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n)) (i : Fin.t (S n))
  {Y} (w : ctree (yieldE +' (forkE +' E)) Bn Y) (K : Y -> thread E Bn) m σ :
  Sequential w ->
  interp_schedule_rr handler (S n) (ts @ i := (w >>= K)) (Some i) m σ ~
  (translate relabel_log (interp_state handler (interp_thread w) σ) >>= fun '(σ', y) =>
     interp_schedule_rr handler (S n) (ts @ i := K y) (Some i) m σ').
Proof. apply interp_schedule_fair_prefix_bind. Qed.

(** Nondeterministic join principle for a focused sequential segment. *)
Lemma interp_schedule_nd_prefix_bind {E F B : Type -> Type} {HB : Bn -< B} {Σ : Type}
  (handler : E ~> stateT Σ (ctree F B)) n (ts : pool E B (S n)) (i : Fin.t (S n))
  {Y} (w : ctree (yieldE +' (forkE +' E)) B Y) (K : Y -> thread E B) σ :
  Sequential w ->
  interp_schedule_nd handler (S n) (ts @ i := (w >>= K)) (Some i) σ ~
  (interp_state handler (interp_thread w) σ >>= fun '(σ', y) =>
     interp_schedule_nd handler (S n) (ts @ i := K y) (Some i) σ').
Proof.
  intro Hw; unfold interp_schedule_nd.
  unfold schedule.
  exact (run_prefix_bind handler nd_scheduler tt n ts i K w σ Hw).
Qed.
