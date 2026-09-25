(** * Nondeterministic scheduling interpretation.

    The parallel of [ICTree.Interp.Yield.RoundRobin]: the same [schedule]
    pool semantics, but every scheduling choice is an actual [Br] instead of
    a cursor pick.  The handler, effects, and auxiliary state are arbitrary;
    no scheduler-policy record is introduced. *)

From Stdlib Require Import Fin Vector.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Events.Yield
  ICTree.Events.State ICTree.Events.Writer
  ICTree.Interp.Refine ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.State.Mod Utils.Vectors.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

Section NondeterministicInterpretation.
  Context {E F : Type} {HE : Encode E} {HF : Encode F} {Sigma : Type}.

  Definition interp_schedule_nd
    (handler : E ~> stateT Sigma (ictree F))
    (n : nat) (ts : pool E n) (focus : option (Fin.t n)) (sigma : Sigma)
    : ictree F (unit * Sigma) :=
    interp_state handler (interp_yield (interp_spawn (schedule n ts focus))) sigma.

  Lemma interp_schedule_nd_equ
    (handler : E ~> stateT Sigma (ictree F)) n (ts ts' : pool E n) focus sigma :
    pool_equ ts ts' ->
    interp_schedule_nd handler n ts focus sigma ≅
    interp_schedule_nd handler n ts' focus sigma.
  Proof.
    intro Hts; unfold interp_schedule_nd.
    apply equ_interp_state; [|reflexivity].
    apply interp_yield_equ, interp_spawn_equ.
    now apply schedule_pool_proper.
  Qed.

  (** Any zero-length pool, not only the literal empty vector: removing the
      last slot yields an abstract [ts -- i] of length zero. *)
  Lemma interp_schedule_nd_empty
    (handler : E ~> stateT Sigma (ictree F)) (ts : pool E 0) sigma :
    interp_schedule_nd handler 0 ts None sigma ~ Ret (tt,sigma).
  Proof.
    unfold interp_schedule_nd.
    assert (Hempty : schedule 0 ts None ≅ Ret tt).
    { rewrite (ictree_eta (schedule 0 ts None)), schedule_empty_none.
      reflexivity. }
    rewrite Hempty, interp_erase_ret, interp_state_ret; reflexivity.
  Qed.

  Lemma interp_schedule_nd_ret
    (handler : E ~> stateT Sigma (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) sigma :
    observe (ts $ i) = RetF tt ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
    interp_schedule_nd handler n (ts -- i) None sigma.
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅ Guard (schedule n (ts -- i) None)).
    { rewrite (ictree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_ret n ts i Hobs); reflexivity. }
    rewrite Hnode, interp_erase_guard, interp_state_tau, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_nd_guard
    (handler : E ~> stateT Sigma (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) t sigma :
    observe (ts $ i) = GuardF t ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
      interp_schedule_nd handler (S n) (ts @ i := t) (Some i) sigma.
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Guard (schedule (S n) (ts @ i := t) (Some i))).
    { rewrite (ictree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_guard n ts i t Hobs); reflexivity. }
    rewrite Hnode, interp_erase_guard, interp_state_tau, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_nd_yield
    (handler : E ~> stateT Sigma (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) k sigma :
    observe (ts $ i) = VisF (inl Yield) k ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
      interp_schedule_nd handler (S n) (ts @ i := k tt) None sigma.
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Guard (schedule (S n) (ts @ i := k tt) None)).
    { rewrite (ictree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_yield n ts i k Hobs); reflexivity. }
    rewrite Hnode, interp_erase_guard, interp_state_tau, sb_guard; reflexivity.
  Qed.

  (** The genuine nondeterministic choice: one real [Br] per selection. *)
  Lemma interp_schedule_nd_select
    (handler : E ~> stateT Sigma (ictree F)) n (ts : pool E (S n)) sigma :
    interp_schedule_nd handler (S n) ts None sigma ~
      Br n (fun i => interp_schedule_nd handler (S n) ts (Some i) sigma).
  Proof.
    unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts None ≅
      Vis (inl Yield) (fun _ => Br n (fun i => schedule (S n) ts (Some i)))).
    { rewrite (ictree_eta (schedule (S n) ts None)), schedule_no_focus_nonempty.
      reflexivity. }
    rewrite Hnode, interp_erase_yield, interp_state_tau, sb_guard,
      interp_state_tau, sb_guard.
    rewrite interp_erase_br, interp_state_br.
    apply sb_br_id; intro i.
    rewrite sb_guard, interp_state_tau, sb_guard, interp_state_tau, sb_guard;
      reflexivity.
  Qed.

  Lemma interp_schedule_nd_fork
    (handler : E ~> stateT Sigma (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) k sigma :
    observe (ts $ i) = VisF (inr (inl Fork)) k ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
      interp_schedule_nd handler (S (S n)) (k true :: (ts @ i := k false))
        (Some (Fin.FS i)) sigma.
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Vis (inr (inl Spawn)) (fun _ =>
        schedule (S (S n)) (k true :: (ts @ i := k false)) (Some (Fin.FS i)))).
    { rewrite (ictree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_fork n ts i k Hobs); reflexivity. }
    rewrite Hnode, interp_erase_spawn, interp_state_tau, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_nd_user
    (handler : E ~> stateT Sigma (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) e k sigma :
    observe (ts $ i) = VisF (inr (inr e)) k ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
      (runStateT (handler e) sigma >>= fun '(x,sigma') =>
       interp_schedule_nd handler (S n) (ts @ i := k x) (Some i) sigma').
  Proof.
    intro Hobs; unfold interp_schedule_nd at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Vis (inr (inr e) : yieldE + (spawnE + E))
        (fun x => schedule (S n) (ts @ i := k x) (Some i))).
    { rewrite (ictree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_user_event n ts i e k Hobs); reflexivity. }
    rewrite Hnode, interp_erase_user, interp_state_vis.
    apply sbisim_clo_bind_eq; [reflexivity|].
    intros [x sigma']; rewrite sb_guard, interp_state_tau, sb_guard,
      interp_state_tau, sb_guard; reflexivity.
  Qed.

  (** Keep one scheduler continuation fixed while interpreting a raw user event. *)
  Lemma interp_schedule_nd_user_bind
    (handler : E ~> stateT Sigma (ictree F)) n (ts : pool E (S n))
    (i : Fin.t (S n)) (t : thread E) (e : E) (k : encode e -> thread E) sigma :
    t ≅ Vis (inr (inr e)) k ->
    interp_schedule_nd handler (S n) (ts @ i := t) (Some i) sigma ~
    (interp_state handler
       (@ICtree.trigger E E _ _ ReSum_refl ReSumRet_refl e) sigma >>=
      fun '(x,sigma') =>
        interp_schedule_nd handler (S n) (ts @ i := k x) (Some i) sigma').
  Proof.
    intro Hnode.
    pose proof (interp_schedule_nd_equ handler (S n)
      (ts @ i := t) (ts @ i := Vis (inr (inr e)) k) (Some i) sigma
      (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
    rewrite Hpool.
    erewrite interp_schedule_nd_user with (e:=e) (k:=k)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite interp_state_trigger_bind.
    apply sbisim_clo_bind_eq; [reflexivity | intros [x sigma']].
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.
End NondeterministicInterpretation.

Arguments interp_schedule_nd {E F HE HF Sigma} handler n ts focus sigma.

(** The singleton state-update step under [h_stateW]: read the state, write
    [f] of it, and finish.  Exactly one [Log] of the new state is observable,
    followed by the return of the emptied pool. *)
Lemma interp_schedule_nd_singleton_update {Sigma} (f : Sigma -> Sigma)
  (ts : pool (stateE Sigma) 1) (sigma : Sigma) :
  observe (ts $ Fin.F1) =
    VisF ((inr (inr Get)) : yieldE + (forkE + stateE Sigma))
      (fun s : Sigma =>
        Vis ((inr (inr (Put (f s)))) : yieldE + (forkE + stateE Sigma))
          (fun _ : unit => Ret tt)) ->
  interp_schedule_nd h_stateW 1 ts (Some Fin.F1) sigma ~
    (log (f sigma);; Ret (tt,f sigma)).
Proof.
  intro Hobs.
  rewrite (interp_schedule_nd_user h_stateW 0 ts Fin.F1 Get _ sigma Hobs).
  cbn [h_stateW runStateT]; rewrite bind_ret_l; cbv beta.
  rewrite (interp_schedule_nd_user h_stateW 0 _ Fin.F1 (Put (f sigma))
    (fun _ : unit => Ret tt) sigma)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  cbn [h_stateW runStateT]; rewrite bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|intros []].
  rewrite bind_ret_l; cbv beta.
  rewrite (interp_schedule_nd_ret h_stateW 0 _ Fin.F1 (f sigma))
    by (rewrite Vector.nth_replace_eq; reflexivity).
  apply interp_schedule_nd_empty.
Qed.
