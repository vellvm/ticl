From Stdlib Require Import Fin Vector.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.State.Mod
  Utils.Vectors.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** Round-robin refinement ([refine_rr]) is fixed to the finite branch
    signature [Bn], so the scheduled pools of this module live in [ctree _ Bn].
    The scheduler's pick [brS (branchn (S n)) k] is the node
    [Br (branchn (S n)) (fun i => Step (k i))], which [refine_rr] resolves
    deterministically through [rr_pick]: one visible [Step] per selection. *)

Section RoundRobinInterpretation.
  Context {E F : Type -> Type} {Σ : Type}.

  Definition interp_schedule_rr
    (handler : E ~> stateT Σ (ctree F Bn))
    (n : nat) (ts : pool E Bn n) (focus : option (Fin.t n))
    (cursor : nat) (σ : Σ) : ctree F Bn (Σ * unit) :=
    interp_state handler
      (interp_yield (interp_spawn
        (run_round_robin (schedule n ts focus) cursor))) σ.

  Lemma interp_schedule_rr_equ
    (handler : E ~> stateT Σ (ctree F Bn)) n (ts ts' : pool E Bn n) focus m σ :
    pool_equ ts ts' ->
    interp_schedule_rr handler n ts focus m σ ≅
    interp_schedule_rr handler n ts' focus m σ.
  Proof.
    intro Hts; unfold interp_schedule_rr.
    now rewrite (schedule_pool_proper n ts ts' focus Hts).
  Qed.

  Lemma interp_schedule_rr_empty
    (handler : E ~> stateT Σ (ctree F Bn)) m σ :
    interp_schedule_rr handler 0 ([] : pool E Bn 0) None m σ ~ (Ret (σ,tt) : ctree F Bn (Σ * unit)).
  Proof.
    unfold interp_schedule_rr.
    rewrite unfold_run_round_robin, schedule_empty_none.
    rewrite interp_erase_ret, interp_state_ret; reflexivity.
  Qed.

  Lemma interp_schedule_rr_ret
    (handler : E ~> stateT Σ (ctree F Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) m σ :
    observe (ts $ i) = RetF tt ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler n (ts -- i) None m σ.
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_ret n ts i Hobs).
    rewrite interp_erase_guard, interp_state_guard, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_rr_guard
    (handler : E ~> stateT Σ (ctree F Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) t m σ :
    observe (ts $ i) = GuardF t ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m σ.
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_guard n ts i t Hobs).
    rewrite interp_erase_guard, interp_state_guard, sb_guard; reflexivity.
  Qed.

  (** A visible step of the focused thread is one visible step of the pool. *)
  Lemma interp_schedule_rr_step
    (handler : E ~> stateT Σ (ctree F Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) t m σ :
    observe (ts $ i) = StepF t ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    Step (interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m σ).
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_step n ts i t Hobs).
    rewrite interp_erase_step, interp_state_step.
    apply sb_step.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.

  Lemma interp_schedule_rr_yield
    (handler : E ~> stateT Σ (ctree F Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) k m σ :
    observe (ts $ i) = VisF (inl1 Yield) k ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler (S n) (ts @ i := k tt) None m σ.
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_yield n ts i k Hobs).
    rewrite interp_erase_guard, interp_state_guard, sb_guard; reflexivity.
  Qed.

  (** The scheduling point: the round-robin pick is one visible step. *)
  Lemma interp_schedule_rr_select
    (handler : E ~> stateT Σ (ctree F Bn)) n (ts : pool E Bn (S n)) m σ :
    interp_schedule_rr handler (S n) ts None m σ ~
    Step (interp_schedule_rr handler (S n) ts (Some (rr_pick n m)) (S m) σ).
  Proof.
    unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, schedule_no_focus_nonempty.
    rewrite interp_erase_yield, interp_state_guard, sb_guard,
      interp_state_guard, sb_guard.
    rewrite (unfold_run_round_robin
      (brS (branchn (S n)) (fun i => schedule (S n) ts (Some i))) m).
    (* resolve the reflexive [Bn -< Bn] embedding of the pick without
       unfolding [rr_pick] *)
    cbn [observe _observe subevent CategoryOps.resum CategoryOps.ReSum_id
         CategoryOps.id_ Id_IFun].
    rewrite interp_erase_guard, interp_state_guard, sb_guard.
    rewrite unfold_run_round_robin; cbn [observe _observe].
    rewrite interp_erase_step, interp_state_step.
    apply sb_step.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.

  Lemma interp_schedule_rr_fork
    (handler : E ~> stateT Σ (ctree F Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) k m σ :
    observe (ts $ i) = VisF (inr1 (inl1 Fork)) k ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler (S (S n))
      (k true :: (ts @ i := k false)) (Some (Fin.FS i)) m σ.
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_fork n ts i k Hobs).
    rewrite interp_erase_spawn, interp_state_guard, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_rr_user
    (handler : E ~> stateT Σ (ctree F Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) {Y} (e : E Y) k m σ :
    observe (ts $ i) = VisF (inr1 (inr1 e)) k ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    (handler _ e σ >>= fun '(σ',x) =>
      interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m σ').
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_user_event n ts i e k Hobs).
    rewrite interp_erase_user, interp_state_vis.
    __upto_bind_sbisim_eq; intros [σ' x]; cbn.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.

  (** A focused slot that is [Stuck] makes the whole interpreted pool
      raw-equivalent to [Stuck]; no other slot ever runs. *)
  Lemma interp_schedule_rr_stuck
    (handler : E ~> stateT Σ (ctree F Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) m σ :
    (ts $ i) ≅ Stuck ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ≅ Stuck.
  Proof.
    intro Hstuck.
    rewrite (interp_schedule_rr_equ handler (S n) ts (ts @ i := Stuck) (Some i) m σ)
      by (intro j; destruct (Fin.eq_dec j i) as [->|Hne];
          [rewrite Vector.nth_replace_eq; exact Hstuck
          |rewrite Vector.nth_replace_neq by congruence; reflexivity]).
    unfold interp_schedule_rr.
    rewrite unfold_run_round_robin.
    rewrite (schedule_focused_stuck n (ts @ i := Stuck) i)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite interp_erase_stuck, interp_state_stuck; reflexivity.
  Qed.

  (** Keep one scheduler continuation fixed while interpreting a raw user event. *)
  Lemma interp_schedule_rr_user_bind
    (handler : E ~> stateT Σ (ctree F Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) (t : thread E Bn) {Y} (e : E Y) (k : Y -> thread E Bn) m σ :
    t ≅ Vis (inr1 (inr1 e)) k ->
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m σ ~
    (interp_state handler (CTree.trigger e : ctree E Bn Y) σ >>=
      fun '(σ',x) =>
        interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m σ').
  Proof.
    intro Hnode.
    rewrite (interp_schedule_rr_equ handler (S n)
      (ts @ i := t) (ts @ i := Vis (inr1 (inr1 e)) k) (Some i) m σ
      (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)).
    erewrite interp_schedule_rr_user with (e:=e) (k:=k)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite interp_state_trigger_bind.
    __upto_bind_sbisim_eq; intros [σ' x].
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

End RoundRobinInterpretation.

Arguments interp_schedule_rr {E F Σ} handler n ts focus cursor σ.

(** ** Round-robin refinement preserves guard alignment *)
Section RoundRobinAlign.
  Context {E : Type -> Type} {X : Type}.
  Local Typeclasses Transparent equ.

  Lemma run_round_robin_guards n (t : ctree E Bn X) c :
    run_round_robin (guards n t) c ≅ guards n (run_round_robin t c).
  Proof.
    induction n; cbn [guards]; [reflexivity|].
    rewrite unfold_run_round_robin; cbn [observe _observe].
    apply guard_equ_node; exact IHn.
  Qed.

  Inductive rr_rel : ctree E Bn X -> ctree E Bn X -> Prop :=
  | rr_rel_at n m (t u : ctree E Bn X) c T U :
      galigned t u -> T ≅ guards n (run_round_robin t c) ->
      U ≅ guards m (run_round_robin u c) -> rr_rel T U.

  Lemma rr_rel_step T U : rr_rel T U -> galignF rr_rel T U.
  Proof.
    intros [n m t u c T' U' A ET EU].
    destruct A as [t u a b t' u' Et Eu A|t u a b r Et Eu|t u a b Y d kk kk' Et Eu Hk
      |t u a b Y e kk kk' Et Eu Hk|t u a b Et Eu|t u a b t' u' Et Eu A].
    - apply (galignF_guard _ T' U' (n + a) (m + b)
        (run_round_robin t' c) (run_round_robin u' c)).
      + rewrite ET, Et, run_round_robin_guards, guards_shift; reflexivity.
      + rewrite EU, Eu, run_round_robin_guards, guards_shift; reflexivity.
      + apply (rr_rel_at 0 0 t' u' c); [exact A|reflexivity|reflexivity].
    - apply (galignF_ret _ T' U' (n + a) (m + b) r).
      + rewrite ET, Et, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; reflexivity.
      + rewrite EU, Eu, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; reflexivity.
    - destruct d as [[|p]].
      + apply (galignF_stuck _ T' U' (n + a) (m + b)).
        * rewrite ET, Et, run_round_robin_guards, <- guards_add,
            unfold_run_round_robin; reflexivity.
        * rewrite EU, Eu, run_round_robin_guards, <- guards_add,
            unfold_run_round_robin; reflexivity.
      + apply (galignF_guard _ T' U' (n + a) (m + b)
          (run_round_robin (kk (rr_pick p c)) (S c))
          (run_round_robin (kk' (rr_pick p c)) (S c))).
        * rewrite ET, Et, run_round_robin_guards, <- guards_add,
            unfold_run_round_robin; cbn [observe _observe].
          rewrite <- guards_guard; reflexivity.
        * rewrite EU, Eu, run_round_robin_guards, <- guards_add,
            unfold_run_round_robin; cbn [observe _observe].
          rewrite <- guards_guard; reflexivity.
        * apply (rr_rel_at 0 0 (kk (rr_pick p c)) (kk' (rr_pick p c)) (S c));
            [apply Hk|reflexivity|reflexivity].
    - apply (galignF_vis _ T' U' (n + a) (m + b) e
        (fun x => run_round_robin (kk x) c) (fun x => run_round_robin (kk' x) c)).
      + rewrite ET, Et, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; reflexivity.
      + rewrite EU, Eu, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; reflexivity.
      + intro x; apply (rr_rel_at 0 0 (kk x) (kk' x) c); [apply Hk|reflexivity|reflexivity].
    - apply (galignF_stuck _ T' U' (n + a) (m + b)).
      + rewrite ET, Et, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; reflexivity.
      + rewrite EU, Eu, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; reflexivity.
    - apply (galignF_step _ T' U' (n + a) (m + b)
        (run_round_robin t' c) (run_round_robin u' c)).
      + rewrite ET, Et, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; reflexivity.
      + rewrite EU, Eu, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; reflexivity.
      + apply (rr_rel_at 0 0 t' u' c); [exact A|reflexivity|reflexivity].
  Qed.

  Lemma run_round_robin_galigned (t u : ctree E Bn X) c :
    galigned t u -> galigned (run_round_robin t c) (run_round_robin u c).
  Proof.
    intro H; apply (galigned_coind rr_rel rr_rel_step).
    apply (rr_rel_at 0 0 t u c); [exact H|reflexivity|reflexivity].
  Qed.
End RoundRobinAlign.

(** Guard-equivalent pools are bisimilar under round-robin scheduling, for
    every focus, cursor and state. *)
Lemma interp_schedule_rr_guard_equ {E F : Type -> Type} {Σ : Type}
  (handler : E ~> stateT Σ (ctree F Bn)) n (ts us : pool E Bn n) focus m σ :
  pool_guard_equ ts us ->
  interp_schedule_rr handler n ts focus m σ ~ interp_schedule_rr handler n us focus m σ.
Proof.
  intro H; unfold interp_schedule_rr, interp_yield, interp_spawn.
  apply galigned_sbisim, interp_state_galigned, interp_galigned, interp_galigned,
    run_round_robin_galigned, schedule_galigned, H.
Qed.
