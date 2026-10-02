From Stdlib Require Import Fin Vector.
From Coinduction Require Import coinduction lattice tactics.
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

  (** A focused slot that is [stuck] makes the whole interpreted pool
      raw-equivalent to [stuck]; no other slot ever runs. *)
  Lemma interp_schedule_rr_stuck
    (handler : E ~> stateT Σ (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) m σ :
    (ts $ i) ≅ stuck ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ≅ stuck.
  Proof.
    intro Hstuck.
    rewrite (interp_schedule_rr_equ handler (S n) ts (ts @ i := stuck) (Some i) m σ)
      by (intro j; destruct (Fin.eq_dec j i) as [->|Hne];
          [rewrite Vector.nth_replace_eq; exact Hstuck
          |rewrite Vector.nth_replace_neq by congruence; reflexivity]).
    apply equ_guard_stuck.
    unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin.
    rewrite (schedule_focused_guard n (ts @ i := stuck) i stuck)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq.
    rewrite interp_erase_guard, interp_state_tau; reflexivity.
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

(** ** Round-robin refinement preserves guard alignment *)
Section RoundRobinAlign.
  Context {E : Type} {HE : Encode E} {X : Type}.
  Local Typeclasses Transparent equ.

  Lemma run_round_robin_guards n (t : ictree E X) c :
    run_round_robin (guards n t) c ≅ guards n (run_round_robin t c).
  Proof.
    induction n; cbn [guards]; [reflexivity|].
    rewrite unfold_run_round_robin; cbn [observe _observe].
    apply guard_equ_node; exact IHn.
  Qed.

  Inductive rr_rel : ictree E X -> ictree E X -> Prop :=
  | rr_rel_at n m (t u : ictree E X) c T U :
      galigned t u -> T ≅ guards n (run_round_robin t c) ->
      U ≅ guards m (run_round_robin u c) -> rr_rel T U.

  Lemma rr_rel_step T U : rr_rel T U -> galignF rr_rel T U.
  Proof.
    intros [n m t u c T' U' A ET EU].
    destruct A as [t u a b t' u' Et Eu A|t u a b r Et Eu
      |t u a b k kk kk' Et Eu Hk|t u a b e kk kk' Et Eu Hk].
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
    - apply (galignF_guard _ T' U' (n + a) (m + b)
        (run_round_robin (kk (rr_pick k c)) (S c))
        (run_round_robin (kk' (rr_pick k c)) (S c))).
      + rewrite ET, Et, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; cbn [observe _observe].
        rewrite <- guards_guard; reflexivity.
      + rewrite EU, Eu, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; cbn [observe _observe].
        rewrite <- guards_guard; reflexivity.
      + apply (rr_rel_at 0 0 (kk (rr_pick k c)) (kk' (rr_pick k c)) (S c)); [apply Hk|reflexivity|reflexivity].
    - apply (galignF_vis _ T' U' (n + a) (m + b) e
        (fun x => run_round_robin (kk x) c) (fun x => run_round_robin (kk' x) c)).
      + rewrite ET, Et, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; reflexivity.
      + rewrite EU, Eu, run_round_robin_guards, <- guards_add,
          unfold_run_round_robin; reflexivity.
      + intro x; apply (rr_rel_at 0 0 (kk x) (kk' x) c); [apply Hk|reflexivity|reflexivity].
  Qed.

  Lemma run_round_robin_galigned (t u : ictree E X) c :
    galigned t u -> galigned (run_round_robin t c) (run_round_robin u c).
  Proof.
    intro H; apply (galigned_coind rr_rel rr_rel_step).
    apply (rr_rel_at 0 0 t u c); [exact H|reflexivity|reflexivity].
  Qed.
End RoundRobinAlign.

(** Guard-equivalent pools are bisimilar under round-robin scheduling, for
    every focus, cursor and state. *)
Lemma interp_schedule_rr_guard_equ {E F : Type} {HE : Encode E} {HF : Encode F} {Σ : Type}
  (handler : E ~> stateT Σ (ictree F)) n (ts us : pool E n) focus m σ :
  pool_guard_equ ts us ->
  interp_schedule_rr handler n ts focus m σ ~ interp_schedule_rr handler n us focus m σ.
Proof.
  intro H; unfold interp_schedule_rr, interp_yield, interp_spawn.
  apply galigned_sbisim, interp_state_galigned, interp_galigned, interp_galigned,
    run_round_robin_galigned, schedule_galigned, H.
Qed.
