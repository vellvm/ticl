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
  CTree.Events.Yield
  CTree.Interp.Refine
  CTree.Logic.Sim
  CTree.Interp.Yield.Mod
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
    rewrite interp_stuck_node, interp_stuck_node; reflexivity.
  Qed.

  (** Standalone erasure commutes with a leading guard. *)
  Lemma interp_thread_guard_node (t : ctree (yieldE +' (forkE +' E)) B X) :
    interp_thread (Guard t) ≅ Guard (interp_thread t).
  Proof.
    unfold interp_thread, interp_yield.
    rewrite interp_guard_node, interp_guard_node; reflexivity.
  Qed.

  (** Standalone erasure turns a visible step into a step followed by two guards. *)
  Lemma interp_thread_step_node (t : ctree (yieldE +' (forkE +' E)) B X) :
    interp_thread (Step t) ≅ Step (Guard (Guard (interp_thread t))).
  Proof.
    unfold interp_thread, interp_yield.
    rewrite interp_step_node, interp_step_node, interp_guard_node; reflexivity.
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

(** ** The cooperative prefix equation, generically over the branch policy.

    [P] is what sits between [schedule] and erasure: [run_round_robin _ m]
    for the round-robin pool, the identity for the nondeterministic one.  Only
    its action on the heads a sequential slot can expose is needed. *)
Section Prefix.
  Context {E F B : Type -> Type} {HB : Bn -< B} {Σ : Type}
    (handler : E ~> stateT Σ (ctree F B))
    (P : completed E B -> completed E B)
    (n : nat) (ts : pool E B (S n)) (i : Fin.t (S n))
    {Y : Type} (K : Y -> thread E B).

  Hypothesis P_equ : Proper (equ eq ==> equ eq) P.
  #[local] Existing Instance P_equ.
  Hypothesis P_stuck : P Stuck ≅ Stuck.
  Hypothesis P_guard : forall t, P (Guard t) ≅ Guard (P t).
  Hypothesis P_step : forall t, P (Step t) ≅ Step (P t).
  Hypothesis P_vis : forall {Z} (e : (yieldE +' (spawnE +' E)) Z) k,
    P (Vis e k) ≅ Vis e (fun z => P (k z)).

  (** Run the scheduled pool under the branch policy [P]. *)
  Let run (ts' : pool E B (S n)) (σ : Σ) : ctree F B (Σ * unit) :=
    interp_state handler (interp_yield (interp_spawn (P (schedule (S n) ts' (Some i))))) σ.

  (** Rejoin the pool with the focused continuation and its resulting state. *)
  Let rhs_k : Σ * Y -> ctree F B (Σ * unit) :=
    fun '(σ', y) => run (ts @ i := K y) σ'.

  (** Exact [≅] congruence for one focused node, generic in [P]. *)
  Lemma run_slot_equ t t' σ :
    t ≅ t' -> run (ts @ i := t) σ ≅ run (ts @ i := t') σ.
  Proof.
    intro H; unfold run.
    now rewrite (schedule_pool_proper (S n) _ _ (Some i)
      (replace_pool_equ ts ts i t t' (pool_equ_refl ts) H)).
  Qed.

  (** Exact [≅] equation for a focused stuck node, generic in [P]. *)
  Lemma run_slot_stuck t σ : t ≅ Stuck -> run (ts @ i := t) σ ≅ Stuck.
  Proof.
    intro H; rewrite (run_slot_equ _ Stuck σ H); unfold run.
    rewrite (trans_schedule_focused_stuck n _ i)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite P_stuck, interp_erase_stuck, interp_state_stuck; reflexivity.
  Qed.

  (** Exact [≅] equation for a focused guard, generic in [P]. *)
  Lemma run_slot_guard t σ :
    run (ts @ i := Guard t) σ ≅ Guard (run (ts @ i := t) σ).
  Proof.
    unfold run.
    rewrite (trans_schedule_focused_guard n _ i t)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite P_guard, interp_erase_guard, interp_state_guard, Vector.replace_replace_eq.
    reflexivity.
  Qed.

  (** Exact [≅] equation for a focused step, generic in [P]. *)
  Lemma run_slot_step t σ :
    run (ts @ i := Step t) σ ≅ Step (Guard (Guard (Guard (run (ts @ i := t) σ)))).
  Proof.
    unfold run.
    rewrite (schedule_focused_step_equ n _ i t)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite P_step, interp_erase_step, interp_state_step, interp_state_guard,
      interp_state_guard, Vector.replace_replace_eq.
    reflexivity.
  Qed.

  (** Exact [≅] equation for a focused user event, generic in [P]. *)
  Lemma run_slot_user {Z} (e : E Z) k σ :
    run (ts @ i := Vis (inr1 (inr1 e)) k) σ ≅
    (handler _ e σ >>= fun sx => Guard (Guard (Guard (run (ts @ i := k (snd sx)) (fst sx))))).
  Proof.
    unfold run.
    assert (Hobs : observe ((ts @ i := Vis (inr1 (inr1 e)) k) $ i) = VisF (inr1 (inr1 e)) k)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite (observe_equ_go _ _ (schedule_focused_user_event n _ i e k Hobs)).
    rewrite P_vis, interp_erase_user, interp_state_vis.
    upto_bind_eq; intro sx.
    rewrite interp_state_guard, interp_state_guard, Vector.replace_replace_eq.
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
        (Guard (Guard (Guard (run (ts @ i := (w' >>= K)) σ))))
        (Guard (Guard (Guard (interp_state handler (interp_thread w') σ >>= rhs_k))))).
      + rewrite (run_slot_equ _ (Step (w' >>= K)) σ) by (rewrite Ew, bind_step; reflexivity).
        rewrite run_slot_step; reflexivity.
      + rewrite Ew, interp_thread_step_node, interp_state_step, interp_state_guard,
          interp_state_guard, bind_step, bind_guard, bind_guard, bind_guard; reflexivity.
      + apply (align_at _ 3 3 _ _ _ _ (prefix_base_at w' σ Hw')); reflexivity.
    - apply (align_bind_step _ 0 0 (handler _ e σ)
        (fun sx => Guard (Guard (run (ts @ i := (k (snd sx) >>= K)) (fst sx))))
        (fun sx => Guard (Guard (interp_state handler (interp_thread (k (snd sx))) (fst sx) >>= rhs_k)))).
      + intro sx; apply (align_at _ 2 2 _ _ _ _ (prefix_base_at (k (snd sx)) (fst sx) (Hk _))); reflexivity.
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

(** Round-robin join principle for a focused sequential segment. *)
Lemma interp_schedule_rr_prefix_bind {E F : Type -> Type} {Σ : Type}
  (handler : E ~> stateT Σ (ctree F Bn)) n (ts : pool E Bn (S n)) (i : Fin.t (S n))
  {Y} (w : ctree (yieldE +' (forkE +' E)) Bn Y) (K : Y -> thread E Bn) m σ :
  Sequential w ->
  interp_schedule_rr handler (S n) (ts @ i := (w >>= K)) (Some i) m σ ~
  (interp_state handler (interp_thread w) σ >>= fun '(σ', y) =>
     interp_schedule_rr handler (S n) (ts @ i := K y) (Some i) m σ').
Proof.
  intro Hw; unfold interp_schedule_rr.
  apply (run_prefix_bind handler (fun t => run_round_robin t m) n ts i K); [| | | | |exact Hw].
  { intros t u Ht; now rewrite Ht. }
  all: intros; rewrite unfold_run_round_robin; reflexivity.
Qed.

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
  apply (run_prefix_bind handler (fun t => t) n ts i K); [| | | | |exact Hw].
  { intros t u Ht; exact Ht. }
  all: intros; reflexivity.
Qed.
