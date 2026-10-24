(** * Nondeterministic scheduling interpretation.

    The parallel of [CTree.Interp.Yield.RoundRobin]: the same [schedule]
    pool semantics, but every scheduling choice is an actual visible branch
    ([brS]) instead of a cursor pick.  The handler, effects, branch signature
    and auxiliary state are arbitrary; no scheduler-policy record is
    introduced. *)

From Stdlib Require Import Fin Vector.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Events.State
  CTree.Events.Writer
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.State.Mod
  Utils.Vectors.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

Generalizable All Variables.

Section NondeterministicInterpretation.
  Context {E F B : Type -> Type} `{Bn -< B} {Sigma : Type}.

  Definition interp_schedule_nd
    (handler : E ~> stateT Sigma (ctree F B))
    (n : nat) (ts : pool E B n) (focus : option (Fin.t n)) (sigma : Sigma)
    : ctree F B (Sigma * unit) :=
    interp_state handler (interp_yield (interp_spawn (schedule n ts focus))) sigma.

  Lemma interp_schedule_nd_equ
    (handler : E ~> stateT Sigma (ctree F B)) n (ts ts' : pool E B n) focus sigma :
    pool_equ ts ts' ->
    interp_schedule_nd handler n ts focus sigma ≅
    interp_schedule_nd handler n ts' focus sigma.
  Proof.
    intro Hts; unfold interp_schedule_nd.
    now rewrite (schedule_pool_proper n ts ts' focus Hts).
  Qed.

  (** Any zero-length pool, not only the literal empty vector: removing the
      last slot yields an abstract [ts -- i] of length zero. *)
  Lemma interp_schedule_nd_empty
    (handler : E ~> stateT Sigma (ctree F B)) (ts : pool E B 0) sigma :
    interp_schedule_nd handler 0 ts None sigma ~ (Ret (sigma,tt) : ctree F B (Sigma * unit)).
  Proof.
    unfold interp_schedule_nd.
    assert (Hempty : schedule 0 ts None ≅ Ret tt).
    { rewrite (ctree_eta (schedule 0 ts None)), schedule_empty_none.
      reflexivity. }
    rewrite Hempty, interp_erase_ret, interp_state_ret; reflexivity.
  Qed.

  Lemma interp_schedule_nd_ret
    (handler : E ~> stateT Sigma (ctree F B)) n (ts : pool E B (S n))
    (i : Fin.t (S n)) sigma :
    observe (ts $ i) = RetF tt ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
    interp_schedule_nd handler n (ts -- i) None sigma.
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅ Guard (schedule n (ts -- i) None)).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_ret n ts i Hobs); reflexivity. }
    rewrite Hnode, interp_erase_guard, interp_state_guard, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_nd_guard
    (handler : E ~> stateT Sigma (ctree F B)) n (ts : pool E B (S n))
    (i : Fin.t (S n)) t sigma :
    observe (ts $ i) = GuardF t ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
      interp_schedule_nd handler (S n) (ts @ i := t) (Some i) sigma.
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Guard (schedule (S n) (ts @ i := t) (Some i))).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_guard n ts i t Hobs); reflexivity. }
    rewrite Hnode, interp_erase_guard, interp_state_guard, sb_guard; reflexivity.
  Qed.

  (** A visible step of the focused thread is one visible step of the pool. *)
  Lemma interp_schedule_nd_step
    (handler : E ~> stateT Sigma (ctree F B)) n (ts : pool E B (S n))
    (i : Fin.t (S n)) t sigma :
    observe (ts $ i) = StepF t ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
      Step (interp_schedule_nd handler (S n) (ts @ i := t) (Some i) sigma).
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Step (schedule (S n) (ts @ i := t) (Some i))).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_step n ts i t Hobs); reflexivity. }
    rewrite Hnode, interp_erase_step, interp_state_step.
    apply sb_step.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.

  Lemma interp_schedule_nd_yield
    (handler : E ~> stateT Sigma (ctree F B)) n (ts : pool E B (S n))
    (i : Fin.t (S n)) k sigma :
    observe (ts $ i) = VisF (inl1 Yield) k ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
      interp_schedule_nd handler (S n) (ts @ i := k tt) None sigma.
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Guard (schedule (S n) (ts @ i := k tt) None)).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_yield n ts i k Hobs); reflexivity. }
    rewrite Hnode, interp_erase_guard, interp_state_guard, sb_guard; reflexivity.
  Qed.

  (** The genuine nondeterministic choice: one visible branch per selection. *)
  Lemma interp_schedule_nd_select
    (handler : E ~> stateT Sigma (ctree F B)) n (ts : pool E B (S n)) sigma :
    interp_schedule_nd handler (S n) ts None sigma ~
      brS (branchn (S n)) (fun i => interp_schedule_nd handler (S n) ts (Some i) sigma).
  Proof.
    unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts None ≅
      Vis (inl1 Yield) (fun _ => brS (branchn (S n)) (fun i => schedule (S n) ts (Some i)))).
    { rewrite (ctree_eta (schedule (S n) ts None)), schedule_no_focus_nonempty.
      reflexivity. }
    rewrite Hnode, interp_erase_yield, interp_state_guard, sb_guard,
      interp_state_guard, sb_guard.
    rewrite interp_erase_br, interp_state_br.
    change (Monad.bind (mbr ?c) ?f) with (CTree.bind (branch c : ctree F B _) f).
    rewrite bind_branch.
    apply sb_br_id; intro i.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    rewrite interp_erase_step, interp_state_step.
    apply sb_step.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.

  Lemma interp_schedule_nd_fork
    (handler : E ~> stateT Sigma (ctree F B)) n (ts : pool E B (S n))
    (i : Fin.t (S n)) k sigma :
    observe (ts $ i) = VisF (inr1 (inl1 Fork)) k ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
      interp_schedule_nd handler (S (S n)) (k true :: (ts @ i := k false))
        (Some (Fin.FS i)) sigma.
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Vis (inr1 (inl1 Spawn)) (fun _ =>
        schedule (S (S n)) (k true :: (ts @ i := k false)) (Some (Fin.FS i)))).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_fork n ts i k Hobs); reflexivity. }
    rewrite Hnode, interp_erase_spawn, interp_state_guard, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_nd_user
    (handler : E ~> stateT Sigma (ctree F B)) n (ts : pool E B (S n))
    (i : Fin.t (S n)) {Y} (e : E Y) k sigma :
    observe (ts $ i) = VisF (inr1 (inr1 e)) k ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
      (handler _ e sigma >>= fun '(sigma',x) =>
       interp_schedule_nd handler (S n) (ts @ i := k x) (Some i) sigma').
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Vis (inr1 (inr1 e) : (yieldE +' (spawnE +' E)) Y)
        (fun x => schedule (S n) (ts @ i := k x) (Some i))).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_user_event n ts i e k Hobs); reflexivity. }
    rewrite Hnode, interp_erase_user, interp_state_vis.
    __upto_bind_sbisim_eq; intros [sigma' x]; cbn.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.

  (** A focused slot that is [Stuck] makes the whole interpreted pool
      raw-equivalent to [Stuck]; no other slot ever runs. *)
  Lemma interp_schedule_nd_stuck
    (handler : E ~> stateT Sigma (ctree F B)) n (ts : pool E B (S n))
    (i : Fin.t (S n)) sigma :
    (ts $ i) ≅ Stuck ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ≅ Stuck.
  Proof.
    intro Hstuck.
    rewrite (interp_schedule_nd_equ handler (S n) ts (ts @ i := Stuck) (Some i) sigma)
      by (intro j; destruct (Fin.eq_dec j i) as [->|Hne];
          [rewrite Vector.nth_replace_eq; exact Hstuck
          |rewrite Vector.nth_replace_neq by congruence; reflexivity]).
    unfold interp_schedule_nd.
    assert (Hnode : schedule (S n) (ts @ i := Stuck) (Some i) ≅ Stuck).
    { rewrite (ctree_eta (schedule (S n) (ts @ i := Stuck) (Some i))),
        (schedule_focused_stuck n (ts @ i := Stuck) i)
        by (rewrite Vector.nth_replace_eq; reflexivity); reflexivity. }
    rewrite Hnode, interp_erase_stuck, interp_state_stuck; reflexivity.
  Qed.

  (** Keep one scheduler continuation fixed while interpreting a raw user event. *)
  Lemma interp_schedule_nd_user_bind
    (handler : E ~> stateT Sigma (ctree F B)) n (ts : pool E B (S n))
    (i : Fin.t (S n)) (t : thread E B) {Y} (e : E Y) (k : Y -> thread E B) sigma :
    t ≅ Vis (inr1 (inr1 e)) k ->
    interp_schedule_nd handler (S n) (ts @ i := t) (Some i) sigma ~
    (interp_state handler (CTree.trigger e : ctree E B Y) sigma >>=
      fun '(sigma',x) =>
        interp_schedule_nd handler (S n) (ts @ i := k x) (Some i) sigma').
  Proof.
    intro Hnode.
    rewrite (interp_schedule_nd_equ handler (S n)
      (ts @ i := t) (ts @ i := Vis (inr1 (inr1 e)) k) (Some i) sigma
      (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)).
    erewrite interp_schedule_nd_user with (e:=e) (k:=k)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite interp_state_trigger_bind.
    __upto_bind_sbisim_eq; intros [sigma' x].
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  (** Guard-equivalent pools are bisimilar under nondeterministic
      scheduling, for every focus and state. *)
  Lemma interp_schedule_nd_guard_equ
    (handler : E ~> stateT Sigma (ctree F B)) n (ts us : pool E B n) focus sigma :
    pool_guard_equ ts us ->
    interp_schedule_nd handler n ts focus sigma ~
    interp_schedule_nd handler n us focus sigma.
  Proof.
    intro H'; unfold interp_schedule_nd.
    apply galigned_sbisim, interp_state_galigned, erased_schedule_galigned, H'.
  Qed.
End NondeterministicInterpretation.

Arguments interp_schedule_nd {E F B _ Sigma} handler n ts focus sigma.

(** The singleton state-update step under [h_stateW]: read the state, write
    [f] of it, and finish.  Exactly one [Log] of the new state is observable,
    followed by the return of the emptied pool. *)
Lemma interp_schedule_nd_singleton_update {B} `{Bn -< B} {Sigma} (f : Sigma -> Sigma)
  (ts : pool (stateE Sigma) B 1) (sigma : Sigma) :
  observe (ts $ Fin.F1) =
    VisF (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Sigma)) Sigma)
      (fun s : Sigma =>
        Vis (inr1 (inr1 (Put (f s))) : (yieldE +' (forkE +' stateE Sigma)) unit)
          (fun _ : unit => Ret tt)) ->
  interp_schedule_nd (B:=B) h_stateW 1 ts (Some Fin.F1) sigma ~
    (log (f sigma);; Ret (f sigma,tt) : ctreeW Sigma B (Sigma * unit)).
Proof.
  intro Hobs.
  rewrite (interp_schedule_nd_user h_stateW 0 ts Fin.F1 Get _ sigma Hobs).
  cbn [h_stateW]; rewrite bind_ret_l; cbv beta.
  rewrite (interp_schedule_nd_user h_stateW 0 _ Fin.F1 (Put (f sigma))
    (fun _ : unit => Ret tt) sigma)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  cbn [h_stateW]; rewrite bind_bind.
  __upto_bind_sbisim_eq; intros [].
  rewrite bind_ret_l; cbv beta.
  rewrite (interp_schedule_nd_ret h_stateW 0 _ Fin.F1 (f sigma))
    by (rewrite Vector.nth_replace_eq; reflexivity).
  apply interp_schedule_nd_empty.
Qed.
