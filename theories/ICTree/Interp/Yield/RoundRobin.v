From Stdlib Require Import Fin Vector.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Events.Yield
  ICTree.Interp.Refine ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.State.Mod Utils.Vectors.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

Section RoundRobinInterpretation.
  Context {E F : Type} {HE : Encode E} {HF : Encode F} {Σ : Type}.

  Definition interp_schedule_rr
    (handler : E ~> stateT Σ (ictree F))
    (n : nat) (ts : pool E n) (focus : option (Fin.t n))
    (cursor : nat) (σ : Σ) : ictree F (unit * Σ) :=
    interp_state handler
      (interp_yield (interp_spawn
        (run_round_robin (schedule n ts focus) cursor))) σ.

  Lemma interp_schedule_rr_equ
    (handler : E ~> stateT Σ (ictree F)) n (ts ts' : pool E n) focus m σ :
    pool_equ ts ts' ->
    interp_schedule_rr handler n ts focus m σ ≅
    interp_schedule_rr handler n ts' focus m σ.
  Proof.
    intro Hts; unfold interp_schedule_rr.
    apply equ_interp_state; [|reflexivity].
    apply interp_yield_equ, interp_spawn_equ.
    apply run_round_robin_equ; [|reflexivity].
    now apply schedule_pool_proper.
  Qed.

  Lemma interp_schedule_rr_empty
    (handler : E ~> stateT Σ (ictree F)) m σ :
    interp_schedule_rr handler 0 ([] : pool E 0) None m σ ~ Ret (tt,σ).
  Proof.
    unfold interp_schedule_rr.
    rewrite unfold_run_round_robin, schedule_empty_none.
    rewrite interp_erase_ret, interp_state_ret; reflexivity.
  Qed.

  Lemma interp_schedule_rr_ret
    (handler : E ~> stateT Σ (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) m σ :
    observe (ts $ i) = RetF tt ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler n (ts -- i) None m σ.
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_ret n ts i Hobs).
    rewrite interp_erase_guard, interp_state_tau, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_rr_guard
    (handler : E ~> stateT Σ (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) t m σ :
    observe (ts $ i) = GuardF t ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m σ.
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_guard n ts i t Hobs).
    rewrite interp_erase_guard, interp_state_tau, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_rr_yield
    (handler : E ~> stateT Σ (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) k m σ :
    observe (ts $ i) = VisF (inl Yield) k ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler (S n) (ts @ i := k tt) None m σ.
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_yield n ts i k Hobs).
    rewrite interp_erase_guard, interp_state_tau, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_rr_select
    (handler : E ~> stateT Σ (ictree F)) n (ts : pool E (S n)) m σ :
    interp_schedule_rr handler (S n) ts None m σ ~
    interp_schedule_rr handler (S n) ts (Some (rr_pick n m)) (S m) σ.
  Proof.
    unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, schedule_no_focus_nonempty.
    rewrite interp_erase_yield, interp_state_tau, sb_guard,
      interp_state_tau, sb_guard.
    rewrite (unfold_run_round_robin
      (Br n (fun i => schedule (S n) ts (Some i))) m).
    change (interp_state handler
      (interp_yield (interp_spawn
        (Guard (run_round_robin (schedule (S n) ts (Some (rr_pick n m))) (S m))))) σ ~
      interp_schedule_rr handler (S n) ts (Some (rr_pick n m)) (S m) σ).
    rewrite interp_erase_guard, interp_state_tau, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_rr_fork
    (handler : E ~> stateT Σ (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) k m σ :
    observe (ts $ i) = VisF (inr (inl Fork)) k ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler (S (S n))
      (k true :: (ts @ i := k false)) (Some (Fin.FS i)) m σ.
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_fork n ts i k Hobs).
    rewrite interp_erase_spawn, interp_state_tau, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_rr_user
    (handler : E ~> stateT Σ (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) e k m σ :
    observe (ts $ i) = VisF (inr (inr e)) k ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    (runStateT (handler e) σ >>= fun '(x,σ') =>
      interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m σ').
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_user_event n ts i e k Hobs).
    rewrite interp_erase_user, interp_state_vis.
    apply sbisim_clo_bind_eq; [reflexivity|].
    intros [x σ']; rewrite sb_guard, interp_state_tau, sb_guard,
      interp_state_tau, sb_guard; reflexivity.
  Qed.

  (** Keep one scheduler continuation fixed while interpreting a raw user event. *)
  Lemma interp_schedule_rr_user_bind
    (handler : E ~> stateT Σ (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) (t : thread E) (e : E) (k : encode e -> thread E) m σ :
    t ≅ Vis (inr (inr e)) k ->
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m σ ~
    (interp_state handler
       (@ICtree.trigger E E _ _ ReSum_refl ReSumRet_refl e) σ >>=
      fun '(x,σ') =>
        interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m σ').
  Proof.
    intro Hnode.
    pose proof (interp_schedule_rr_equ handler (S n)
      (ts @ i := t) (ts @ i := Vis (inr (inr e)) k) (Some i) m σ
      (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
    rewrite Hpool.
    erewrite interp_schedule_rr_user with (e:=e) (k:=k)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite interp_state_trigger_bind.
    apply sbisim_clo_bind_eq; [reflexivity | intros [x σ']].
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

End RoundRobinInterpretation.

Arguments interp_schedule_rr {E F HE HF Σ} handler n ts focus cursor σ.
