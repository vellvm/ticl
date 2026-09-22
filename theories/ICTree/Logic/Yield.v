From Stdlib Require Import
  Fin
  Vector
  Program.Equality.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Events.Yield
  ICTree.Events.State
  ICTree.Events.Writer
  ICTree.Interp.Core
  ICTree.Interp.State.Mod
  ICTree.Interp.Yield.Mod
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.Bind
  ICTree.Logic.CanStep
  ICTree.Logic.State
  Logic.Core
  Utils.Vectors.

Import ICtree ICTreeNotations TiclNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

(** * TICL rules for instrumented raw threads and scheduled pools *)
(** These rules are stated over raw [ictree] values built from [yieldE],
    [forkE] and [stateE] events.  They know nothing about source syntax; a
    language lifts them by instantiating the raw trees with its denotations. *)

(** ** Singleton scheduler reductions. *)
(** A source program starts as a one-slot pool focused on its only thread.
    These local reductions normalize that pool one observable step at a time. *)

Local Lemma schedule_singleton_empty {E} `{Encode E} (v : pool E 0) :
  schedule 0 v None ≅ Ret tt.
Proof.
  rewrite (ictree_eta (schedule 0 v None)), schedule_empty_none.
  reflexivity.
Qed.

Local Lemma schedule_singleton_ret {E} `{Encode E} (v : pool E 1) :
  observe (v $ Fin.F1) = RetF tt ->
  schedule 1 v (Some Fin.F1) ≅ Guard (Ret tt).
Proof.
  intro Hobs.
  rewrite (ictree_eta (schedule 1 v (Some Fin.F1))),
    (schedule_focused_ret 0 v Fin.F1 Hobs).
  apply guard_equ_node, schedule_singleton_empty.
Qed.

Local Lemma schedule_singleton_yield {E} `{Encode E} (v : pool E 1) k :
  observe (v $ Fin.F1) = VisF (inl Yield) k ->
  schedule 1 v (Some Fin.F1)
    ≅ Guard (Vis ((inl Yield) : yieldE + (spawnE + E))
               (fun _ => Br 0 (fun i =>
                  schedule 1 (v @ Fin.F1 := (k tt)) (Some i)))).
Proof.
  intro Hobs.
  rewrite (ictree_eta (schedule 1 v (Some Fin.F1))),
    (schedule_focused_yield 0 v Fin.F1 k Hobs).
  apply guard_equ_node.
  rewrite (ictree_eta (schedule 1 (v @ Fin.F1 := (k tt)) None)),
    (schedule_no_focus_nonempty 0 (v @ Fin.F1 := (k tt))).
  reflexivity.
Qed.

Local Lemma schedule_singleton_user {E} `{Encode E} (v : pool E 1) (e : E) k :
  observe (v $ Fin.F1) = VisF (inr (inr e)) k ->
  schedule 1 v (Some Fin.F1)
    ≅ Vis ((inr (inr e)) : yieldE + (spawnE + E))
        (fun x => schedule 1 (v @ Fin.F1 := (k x)) (Some Fin.F1)).
Proof.
  intro Hobs.
  rewrite (ictree_eta (schedule 1 v (Some Fin.F1))),
    (schedule_focused_user_event 0 v Fin.F1 e k Hobs).
  reflexivity.
Qed.

Local Lemma instr_schedule_singleton_ret {Σ} (v : pool (stateE Σ) 1) (σ : Σ) :
  observe (v $ Fin.F1) = RetF tt ->
  instr_schedule 1 v (Some Fin.F1) σ ~ Ret (tt, σ).
Proof.
  intro Hobs.
  unfold instr_schedule, instr_stateE.
  rewrite (schedule_singleton_ret v Hobs), interp_erase_guard_ret.
  rewrite interp_state_tau, sb_guard, interp_state_ret.
  reflexivity.
Qed.

(** The singleton update step: read the state, write [f] of it, and finish.
    Exactly one [Log] of the new state is observable. *)
Local Lemma instr_schedule_singleton_update {Σ} (f : Σ -> Σ)
    (v : pool (stateE Σ) 1) (σ : Σ) :
  observe (v $ Fin.F1) =
    VisF ((inr (inr Get)) : yieldE + (forkE + stateE Σ))
      (fun σ0 : Σ =>
         Vis ((inr (inr (Put (f σ0)))) : yieldE + (forkE + stateE Σ))
           (fun _ : unit => Ret tt)) ->
  instr_schedule 1 v (Some Fin.F1) σ ~ (log (f σ);; Ret (tt, f σ)).
Proof with eauto.
  intro Hobs.
  assert (Hput : observe
      ((v @ Fin.F1 :=
          (Vis ((inr (inr (Put (f σ)))) : yieldE + (forkE + stateE Σ))
             (fun _ : unit => Ret tt))) $ Fin.F1)
      = VisF ((inr (inr (Put (f σ)))) : yieldE + (forkE + stateE Σ))
          (fun _ : unit => Ret tt))
    by (now rewrite Vector.nth_replace_eq).
  assert (Hend : observe
      (((v @ Fin.F1 :=
           (Vis ((inr (inr (Put (f σ)))) : yieldE + (forkE + stateE Σ))
              (fun _ : unit => Ret tt)))
          @ Fin.F1 := (Ret tt)) $ Fin.F1) = RetF tt)
    by (now rewrite Vector.nth_replace_eq).
  unfold instr_schedule, instr_stateE.
  rewrite (schedule_singleton_user v Get _ Hobs).
  rewrite interp_erase_user, interp_state_vis.
  cbn [h_stateW runStateT].
  rewrite bind_ret_l, sb_guard.
  cbv beta.
  rewrite interp_state_tau, sb_guard, interp_state_tau, sb_guard.
  rewrite (schedule_singleton_user _ (Put (f σ)) _ Hput).
  rewrite interp_erase_user, interp_state_vis.
  cbn [h_stateW runStateT].
  rewrite bind_bind.
  __upto_bind_sbisim...
  intros [].
  rewrite bind_ret_l, sb_guard.
  cbv beta.
  rewrite interp_state_tau, sb_guard, interp_state_tau, sb_guard.
  rewrite (schedule_singleton_ret _ Hend).
  rewrite interp_erase_guard_ret.
  rewrite interp_state_tau, sb_guard, interp_state_ret.
  reflexivity.
Qed.

(** ** Raw thread rules. *)

(** A finished raw thread terminates in one step with the unchanged state. *)
Lemma axr_thread_ret {Σ X} : forall (r : X) (σ : Σ) w R,
    not_done w ->
    R (r, σ) w ->
    <[ {instr_thread (Ret r) σ}, w |= AX done R ]>.
Proof with eauto with ticl.
  intros r σ w R Hnd HR.
  rewrite instr_thread_ret.
  apply axr_ret...
Qed.

(** Sequential composition of raw threads, suffix [AN]. *)
Lemma anr_thread_bind_r_eq {Σ A B} :
  forall (t : ictree (yieldE + (forkE + stateE Σ)) A)
         (k : A -> ictree (yieldE + (forkE + stateE Σ)) B)
         (σ σ' : Σ) (r : A) w w' φ ψ,
    <[ {instr_thread t σ}, w |= φ AN done= {(r, σ')} w' ]> ->
    <[ {instr_thread (k r) σ'}, w' |= φ AN ψ ]> ->
    <[ {instr_thread (x <- t ;; k x) σ}, w |= φ AN ψ ]>.
Proof.
  intros t k σ σ' r w w' φ ψ Ht Hk.
  rewrite instr_thread_bind.
  eapply anr_bind_r_eq; eauto.
Qed.

(** Sequential composition of raw threads, suffix [AU]. *)
Lemma aur_thread_bind_r_eq {Σ A B} :
  forall (t : ictree (yieldE + (forkE + stateE Σ)) A)
         (k : A -> ictree (yieldE + (forkE + stateE Σ)) B)
         (σ σ' : Σ) (r : A) w w' φ ψ,
    <[ {instr_thread t σ}, w |= φ AU AX done= {(r, σ')} w' ]> ->
    <[ {instr_thread (k r) σ'}, w' |= φ AU ψ ]> ->
    <[ {instr_thread (x <- t ;; k x) σ}, w |= φ AU ψ ]>.
Proof.
  intros t k σ σ' r w w' φ ψ Ht Hk.
  rewrite instr_thread_bind.
  eapply aur_bind_r_eq; eauto.
Qed.

(** Sequential composition of raw threads, prefix [AU]. *)
Lemma aul_thread_bind_r_eq {Σ A B} :
  forall (t : ictree (yieldE + (forkE + stateE Σ)) A)
         (k : A -> ictree (yieldE + (forkE + stateE Σ)) B)
         (σ σ' : Σ) (r : A) w w' φ ψ,
    <[ {instr_thread t σ}, w |= φ AU AX done= {(r, σ')} w' ]> ->
    <( {instr_thread (k r) σ'}, w' |= φ AU ψ )> ->
    <( {instr_thread (x <- t ;; k x) σ}, w |= φ AU ψ )>.
Proof.
  intros t k σ σ' r w w' φ ψ Ht Hk.
  rewrite instr_thread_bind.
  eapply aul_bind_r_eq; eauto.
Qed.

(** A raw state update [σ ↦ f σ] leaves exactly one [Log] observation and then
    returns [r]; suffix [AU] version. *)
Lemma aur_thread_update {Σ X} :
  forall (f : Σ -> Σ) (r : X) (σ : Σ) w ψ R,
    <( {log (f σ)}, w |= ψ )> ->
    R (r, f σ) (Obs (Log (f σ)) tt) ->
    <[ {instr_thread
          (Vis ((inr (inr Get)) : yieldE + (forkE + stateE Σ))
             (fun σ0 : Σ =>
                Vis ((inr (inr (Put (f σ0)))) : yieldE + (forkE + stateE Σ))
                  (fun _ : unit => Ret r))) σ},
       w |= ψ AU AX done R ]>.
Proof with eauto with ticl.
  intros f r σ w ψ R Hlog HR.
  pose proof (ticll_not_done unit _ _ _ Hlog) as Hnd.
  rewrite instr_thread_get; cbv beta.
  setoid_rewrite instr_thread_put; cbv beta.
  eapply aur_log.
  - cleft; apply axr_thread_ret...
  - now apply ticll_bind_l.
Qed.

(** A raw state update [σ ↦ f σ]; prefix [AU] version. *)
Lemma aul_thread_update {Σ X} :
  forall (f : Σ -> Σ) (r : X) (σ : Σ) w ψ φ,
    <( {log (f σ)}, w |= ψ )> ->
    <( {Ret (r, f σ)}, {Obs (Log (f σ)) tt} |= φ )> ->
    <( {instr_thread
          (Vis ((inr (inr Get)) : yieldE + (forkE + stateE Σ))
             (fun σ0 : Σ =>
                Vis ((inr (inr (Put (f σ0)))) : yieldE + (forkE + stateE Σ))
                  (fun _ : unit => Ret r))) σ},
       w |= ψ AU φ )>.
Proof with eauto with ticl.
  intros f r σ w ψ φ Hlog Hret.
  rewrite instr_thread_get; cbv beta.
  setoid_rewrite instr_thread_put; cbv beta.
  cright.
  apply anl_log.
  - cleft.
    rewrite instr_thread_ret.
    exact Hret.
  - now apply ticll_bind_l.
Qed.

(** ** Raw singleton scheduler rules. *)

(** A finished singleton pool terminates in one step. *)
Lemma axr_schedule_ret {Σ} : forall (σ : Σ) w R,
    not_done w ->
    R (tt, σ) w ->
    <[ {instr_schedule 1
          [(Ret tt : ictree (yieldE + (forkE + stateE Σ)) unit)]%vector
          (Some Fin.F1) σ}, w |= AX done R ]>.
Proof with eauto with ticl.
  intros σ w R Hnd HR.
  rewrite (instr_schedule_singleton_ret
             [(Ret tt : ictree (yieldE + (forkE + stateE Σ)) unit)]%vector
             σ eq_refl).
  apply axr_ret...
Qed.

(** A cooperative [Yield] in a singleton pool costs two steps: the scheduler
    emits the scheduling point and then chooses the (single) runnable slot. *)
Lemma axax_schedule_yield {Σ} : forall (σ : Σ) w R,
    not_done w ->
    R (tt, σ) w ->
    <[ {instr_schedule 1
          [Vis ((inl Yield) : yieldE + (forkE + stateE Σ))
             (fun _ : unit => Ret tt)]%vector
          (Some Fin.F1) σ}, w |= AX AX done R ]>.
Proof with eauto with ticl.
  intros σ w R Hnd HR.
  assert (Hend : observe
      (([Vis ((inl Yield) : yieldE + (forkE + stateE Σ))
            (fun _ : unit => Ret tt)]%vector
          @ Fin.F1 := (Ret tt)) $ Fin.F1) = RetF tt)
    by (now rewrite Vector.nth_replace_eq).
  unfold instr_schedule, instr_stateE.
  rewrite (schedule_singleton_yield
             [Vis ((inl Yield) : yieldE + (forkE + stateE Σ))
                (fun _ : unit => Ret tt)]%vector
             (fun _ : unit => (Ret tt : ictree (yieldE + (forkE + stateE Σ)) unit))
             eq_refl).
  rewrite interp_erase_guard_yield.
  rewrite interp_state_tau, sb_guard, interp_state_tau, sb_guard,
    interp_state_tau, sb_guard.
  rewrite interp_erase_br.
  apply anr_state_br; split.
  - csplit...
  - intro i; dependent destruction i.
    + rewrite interp_state_tau, sb_guard, interp_state_tau, sb_guard.
      rewrite (schedule_singleton_ret _ Hend).
      rewrite interp_erase_guard_ret.
      rewrite interp_state_tau, sb_guard, interp_state_ret.
      apply axr_ret...
    + inversion i.
Qed.

(** A scheduled singleton state update leaves exactly one [Log]; suffix [AU]. *)
Lemma aur_schedule_update {Σ} :
  forall (f : Σ -> Σ) (σ : Σ) w ψ R,
    <( {log (f σ)}, w |= ψ )> ->
    R (tt, f σ) (Obs (Log (f σ)) tt) ->
    <[ {instr_schedule 1
          [Vis ((inr (inr Get)) : yieldE + (forkE + stateE Σ))
             (fun σ0 : Σ =>
                Vis ((inr (inr (Put (f σ0)))) : yieldE + (forkE + stateE Σ))
                  (fun _ : unit => Ret tt))]%vector
          (Some Fin.F1) σ},
       w |= ψ AU AX done R ]>.
Proof with eauto with ticl.
  intros f σ w ψ R Hlog HR.
  pose proof (ticll_not_done unit _ _ _ Hlog) as Hnd.
  rewrite (instr_schedule_singleton_update f
             [Vis ((inr (inr Get)) : yieldE + (forkE + stateE Σ))
                (fun σ0 : Σ =>
                   Vis ((inr (inr (Put (f σ0)))) : yieldE + (forkE + stateE Σ))
                     (fun _ : unit => Ret tt))]%vector
             σ eq_refl).
  eapply aur_log.
  - cleft; apply axr_ret...
  - now apply ticll_bind_l.
Qed.

(** A scheduled singleton state update; prefix [AU]. *)
Lemma aul_schedule_update {Σ} :
  forall (f : Σ -> Σ) (σ : Σ) w ψ φ,
    <( {log (f σ)}, w |= ψ )> ->
    <( {Ret (tt, f σ)}, {Obs (Log (f σ)) tt} |= φ )> ->
    <( {instr_schedule 1
          [Vis ((inr (inr Get)) : yieldE + (forkE + stateE Σ))
             (fun σ0 : Σ =>
                Vis ((inr (inr (Put (f σ0)))) : yieldE + (forkE + stateE Σ))
                  (fun _ : unit => Ret tt))]%vector
          (Some Fin.F1) σ},
       w |= ψ AU φ )>.
Proof with eauto with ticl.
  intros f σ w ψ φ Hlog Hret.
  rewrite (instr_schedule_singleton_update f
             [Vis ((inr (inr Get)) : yieldE + (forkE + stateE Σ))
                (fun σ0 : Σ =>
                   Vis ((inr (inr (Put (f σ0)))) : yieldE + (forkE + stateE Σ))
                     (fun _ : unit => Ret tt))]%vector
             σ eq_refl).
  cright.
  apply anl_log.
  - cleft...
  - now apply ticll_bind_l.
Qed.
