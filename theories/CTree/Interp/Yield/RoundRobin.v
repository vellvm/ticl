From Stdlib Require Import Fin Vector.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Events.Writer
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.Policy
  CTree.Interp.State.Mod
  Utils.Vectors.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** Round robin is the [rr_scheduler] instance of the event-only policy
    runner: [interp_schedule_rr] abbreviates [interp_schedule_fair
    rr_scheduler], so every node equation is the generic
    [interp_schedule_fair_*] lemma of [Policy].  Only selection is
    RR-specific: a single alternative, logged as
    [Log (inr (slot_index (rr_pick n m)))], with no extra visible step. *)

Abbreviation interp_schedule_rr := (interp_schedule_fair rr_scheduler).

Section RoundRobinInterpretation.
  Context {E : Type -> Type} {W Σ : Type}.

  Lemma interp_schedule_rr_equ
    (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts ts' : pool E Bn n) focus m σ :
    pool_equ ts ts' ->
    interp_schedule_rr handler n ts focus m σ ≅
    interp_schedule_rr handler n ts' focus m σ.
  Proof. intro Hts; apply interp_schedule_fair_equ, Hts. Qed.

  Lemma interp_schedule_rr_empty
    (handler : E ~> stateT Σ (ctreeW W Bn)) m σ :
    interp_schedule_rr handler 0 ([] : pool E Bn 0) None m σ ~ (Ret (σ,tt) : ctreeW (W + nat) Bn (Σ * unit)).
  Proof. apply interp_schedule_fair_empty. Qed.

  Lemma interp_schedule_rr_ret
    (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) m σ :
    observe (ts $ i) = RetF tt ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler n (ts -- i) None m σ.
  Proof. apply interp_schedule_fair_ret. Qed.

  Lemma interp_schedule_rr_guard
    (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) t m σ :
    observe (ts $ i) = GuardF t ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m σ.
  Proof. apply interp_schedule_fair_guard. Qed.

  Lemma interp_schedule_rr_step
    (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) t m σ :
    observe (ts $ i) = StepF t ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    Step (interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m σ).
  Proof. apply interp_schedule_fair_step. Qed.

  Lemma interp_schedule_rr_br
    (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) {Y} (c : Bn Y) k m σ :
    observe (ts $ i) = BrF c k ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
      Br c (fun x => interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m σ).
  Proof. intro Hobs; rewrite (interp_schedule_fair_br rr_scheduler handler n ts i c k m σ Hobs).
    apply sb_br_id; intro x; rewrite sb_guard; reflexivity. Qed.

  Lemma interp_schedule_rr_yield
    (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) k m σ :
    observe (ts $ i) = VisF (inl1 Yield) k ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler (S n) (ts @ i := k tt) None m σ.
  Proof. apply interp_schedule_fair_yield. Qed.

  Lemma interp_schedule_rr_fork
    (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) k m σ :
    observe (ts $ i) = VisF (inr1 (inl1 Fork)) k ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    interp_schedule_rr handler (S (S n))
      (k true :: (ts @ i := k false)) (Some (Fin.FS i)) m σ.
  Proof. apply interp_schedule_fair_fork. Qed.

  Lemma interp_schedule_rr_user
    (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) {Y} (e : E Y) k m σ :
    observe (ts $ i) = VisF (inr1 (inr1 e)) k ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ~
    (translate relabel_log (handler _ e σ) >>= fun '(σ',x) =>
      interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m σ').
  Proof. apply interp_schedule_fair_user. Qed.

  Lemma interp_schedule_rr_stuck
    (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) m σ :
    (ts $ i) ≅ Stuck ->
    interp_schedule_rr handler (S n) ts (Some i) m σ ≅ Stuck.
  Proof. apply interp_schedule_fair_stuck. Qed.

  Lemma interp_schedule_rr_user_bind
    (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n))
    (i : Fin.t (S n)) (t : thread E Bn) {Y} (e : E Y) (k : Y -> thread E Bn) m σ :
    t ≅ Vis (inr1 (inr1 e)) k ->
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m σ ~
    (translate relabel_log (handler _ e σ) >>=
      fun '(σ',x) =>
        interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m σ').
  Proof. apply interp_schedule_fair_user_bind. Qed.

  (** The scheduling point: one logged pick, then the focused pool. *)
  Lemma interp_schedule_rr_select_exact (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n)) m σ :
    interp_schedule_rr handler (S n) ts None m σ ≅
    Vis (Log (inr (slot_index (rr_pick n m))))
      (fun _ => Guard (interp_schedule_rr handler (S n) ts (Some (rr_pick n m)) (S m) σ)).
  Proof.
    unfold interp_schedule_fair at 1.
    rewrite (schedule_policy_no_focus_nonempty rr_scheduler n ts m).
    cbn [sched_arity sched_pick rr_scheduler br_alts fst snd].
    rewrite interp_state_vis; cbn [policy_handler h_sum sched_handler].
    change (Monad.bind ?a ?b) with (CTree.bind a b); rewrite bind_vis.
    apply vis_equ_node; intros _.
    rewrite bind_ret_l; cbn [fst snd]; reflexivity.
  Qed.

  (** The scheduling point: the round-robin pick is one logged event. *)
  Lemma interp_schedule_rr_select (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts : pool E Bn (S n)) m σ :
    interp_schedule_rr handler (S n) ts None m σ ~
    Vis (Log (inr (slot_index (rr_pick n m))))
      (fun _ => interp_schedule_rr handler (S n) ts (Some (rr_pick n m)) (S m) σ).
  Proof.
    rewrite interp_schedule_rr_select_exact.
    apply sb_vis; intros _; rewrite sb_guard; reflexivity.
  Qed.
End RoundRobinInterpretation.

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

(** Guard-equivalent pools preserve the logged round-robin interpretation. *)
Lemma interp_schedule_rr_guard_equ {E : Type -> Type} {W Σ : Type}
  (handler : E ~> stateT Σ (ctreeW W Bn)) n (ts us : pool E Bn n) focus m σ :
  pool_guard_equ ts us ->
  interp_schedule_rr handler n ts focus m σ ~ interp_schedule_rr handler n us focus m σ.
Proof. apply interp_schedule_fair_guard_equ. Qed.
