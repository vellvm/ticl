From Stdlib Require Import
  List
  Arith.PeanoNat
  Classes.Morphisms
  Classes.RelationPairs
  Fin
  Vector
  Program.Equality
  Wellfounded.Inverse_Image.

From Coinduction Require Import all.

From ExtLib Require Import Data.Option.

From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Events.State
  CTree.Events.Writer
  CTree.Interp.Refine
  CTree.Interp.State.Mod
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.Nondeterministic
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.Segments
  CTree.Interp.Yield.Execution
  CTree.Trace
  CTree.Logic.Trans
  CTree.Logic.AG
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.Bind
  CTree.Logic.CanStep
  CTree.Logic.Iter
  CTree.Logic.State
  CTree.Logic.Trace
  Logic.Core
  Utils.Execution
  Utils.Vectors.

Import CTreeNotations TiclNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

Generalizable All Variables.

(** * TICL rules for instrumented raw threads and scheduled pools *)
(** These rules are stated over raw [ctree] values built from [yieldE],
    [forkE] and [stateE] events.  They know nothing about source syntax; a
    language lifts them by instantiating the raw trees with its denotations. *)

(** The singleton scheduler reductions are the operational equations of
    [CTree.Interp.Yield.Nondeterministic]: [instr_schedule] is definitionally
    [interp_schedule_nd h_stateW], so the modal rules below only combine those
    equations with the tree-level [AX]/[AN]/log rules. *)

(** ** Rules for raw threads under an arbitrary state handler. *)
Section ThreadStateRules.
  Context {E B : Type -> Type} {W S : Type} (h : E ~> stateT S (ctreeW W B)).

  Lemma axr_ithread_ret {X} : forall (r : X) (s : S) w R,
      not_done w ->
      R (s, r) w ->
      <[ {interp_state h (interp_thread (Ret r : ctree (yieldE +' (forkE +' E)) B X)) s},
         w |= ret R ]>.
  Proof.
    intros r s w R Hnd HR.
    rewrite interp_state_thread_ret.
    apply ret_ret; eauto with ticl.
  Qed.

  Lemma anr_ithread_bind_r_eq {A C} :
    forall (t : ctree (yieldE +' (forkE +' E)) B A)
           (k : A -> ctree (yieldE +' (forkE +' E)) B C)
           (s s' : S) (r : A) w w' φ ψ,
      <[ {interp_state h (interp_thread t) s}, w |= φ AN done= {(s', r)} w' ]> ->
      <[ {interp_state h (interp_thread (k r)) s'}, w' |= φ AN ψ ]> ->
      <[ {interp_state h (interp_thread (x <- t ;; k x)) s}, w |= φ AN ψ ]>.
  Proof.
    intros t k s s' r w w' φ ψ Ht Hk.
    rewrite interp_state_thread_bind.
    eapply anr_bind_r_eq; eauto.
  Qed.

  Lemma aur_ithread_bind_r_eq {A C} :
    forall (t : ctree (yieldE +' (forkE +' E)) B A)
           (k : A -> ctree (yieldE +' (forkE +' E)) B C)
           (s s' : S) (r : A) w w' φ ψ,
      <[ {interp_state h (interp_thread t) s}, w |= φ AU AX done= {(s', r)} w' ]> ->
      <[ {interp_state h (interp_thread (k r)) s'}, w' |= φ AU ψ ]> ->
      <[ {interp_state h (interp_thread (x <- t ;; k x)) s}, w |= φ AU ψ ]>.
  Proof.
    intros t k s s' r w w' φ ψ Ht Hk.
    rewrite interp_state_thread_bind.
    eapply aur_bind_r_eq; eauto.
  Qed.

  Lemma aul_ithread_bind_r_eq {A C} :
    forall (t : ctree (yieldE +' (forkE +' E)) B A)
           (k : A -> ctree (yieldE +' (forkE +' E)) B C)
           (s s' : S) (r : A) w w' φ ψ,
      <[ {interp_state h (interp_thread t) s}, w |= φ AU AX done= {(s', r)} w' ]> ->
      <( {interp_state h (interp_thread (k r)) s'}, w' |= φ AU ψ )> ->
      <( {interp_state h (interp_thread (x <- t ;; k x)) s}, w |= φ AU ψ )>.
  Proof.
    intros t k s s' r w w' φ ψ Ht Hk.
    rewrite interp_state_thread_bind.
    eapply aul_bind_r_eq; eauto.
  Qed.
End ThreadStateRules.

(** ** Singleton scheduler rules under an arbitrary state handler. *)
Section ScheduleStateRules.
  Context {E B : Type -> Type} `{Bn -< B} {W S : Type} (h : E ~> stateT S (ctreeW W B)).

  Lemma axr_schedule_nd_ret : forall (s : S) w R,
      not_done w ->
      R (s, tt) w ->
      <[ {interp_schedule_nd h 1 [(Ret tt : thread E B)]%vector (Some Fin.F1) s},
         w |= ret R ]>.
  Proof.
    intros s w R Hnd HR.
    rewrite (interp_schedule_nd_ret h 0 [(Ret tt : thread E B)]%vector Fin.F1 s eq_refl).
    rewrite interp_schedule_nd_empty.
    apply ret_ret; eauto with ticl.
  Qed.

  (** A cooperative [Yield] costs one visible step: the scheduling pick. *)
  Lemma axax_schedule_nd_yield : forall (s : S) w R,
      not_done w ->
      R (s, tt) w ->
      <[ {interp_schedule_nd h 1
            [Vis (inl1 Yield : (yieldE +' (forkE +' E)) unit) (fun _ : unit => Ret tt)]%vector
            (Some Fin.F1) s}, w |= AX ret R ]>.
  Proof.
    intros s w R Hnd HR.
    rewrite (interp_schedule_nd_yield h 0
               [Vis (inl1 Yield : (yieldE +' (forkE +' E)) unit) (fun _ : unit => Ret tt)]%vector
               Fin.F1 (fun _ : unit => (Ret tt : thread E B)) s eq_refl).
    rewrite interp_schedule_nd_select.
    apply (anr_brS _ _ Fin.F1); split.
    - csplit; eauto with ticl.
    - intro i; dependent destruction i.
      + rewrite (interp_schedule_nd_ret h 0 _ Fin.F1 s)
          by (now rewrite Vector.nth_replace_eq).
        rewrite interp_schedule_nd_empty.
        apply ret_ret; eauto with ticl.
      + inversion i.
  Qed.
End ScheduleStateRules.

(** ** Raw thread rules. *)
Section RawThreadRules.
  Context {B : Type -> Type} `{Bn -< B}.

  (** A finished raw thread terminates in one step with the unchanged state. *)
  Lemma axr_thread_ret {Σ X} : forall (r : X) (σ : Σ) w R,
      not_done w ->
      R (σ, r) w ->
      <[ {instr_thread (B:=B) (Ret r) σ}, w |= ret R ]>.
  Proof. exact (axr_ithread_ret h_stateW). Qed.

  (** Sequential composition of raw threads, suffix [AN]. *)
  Lemma anr_thread_bind_r_eq {Σ A C} :
    forall (t : ctree (yieldE +' (forkE +' stateE Σ)) B A)
           (k : A -> ctree (yieldE +' (forkE +' stateE Σ)) B C)
           (σ σ' : Σ) (r : A) w w' φ ψ,
      <[ {instr_thread t σ}, w |= φ AN done= {(σ', r)} w' ]> ->
      <[ {instr_thread (k r) σ'}, w' |= φ AN ψ ]> ->
      <[ {instr_thread (x <- t ;; k x) σ}, w |= φ AN ψ ]>.
  Proof. exact (anr_ithread_bind_r_eq h_stateW). Qed.

  (** Sequential composition of raw threads, suffix [AU]. *)
  Lemma aur_thread_bind_r_eq {Σ A C} :
    forall (t : ctree (yieldE +' (forkE +' stateE Σ)) B A)
           (k : A -> ctree (yieldE +' (forkE +' stateE Σ)) B C)
           (σ σ' : Σ) (r : A) w w' φ ψ,
      <[ {instr_thread t σ}, w |= φ AU AX done= {(σ', r)} w' ]> ->
      <[ {instr_thread (k r) σ'}, w' |= φ AU ψ ]> ->
      <[ {instr_thread (x <- t ;; k x) σ}, w |= φ AU ψ ]>.
  Proof. exact (aur_ithread_bind_r_eq h_stateW). Qed.

  (** Sequential composition of raw threads, prefix [AU]. *)
  Lemma aul_thread_bind_r_eq {Σ A C} :
    forall (t : ctree (yieldE +' (forkE +' stateE Σ)) B A)
           (k : A -> ctree (yieldE +' (forkE +' stateE Σ)) B C)
           (σ σ' : Σ) (r : A) w w' φ ψ,
      <[ {instr_thread t σ}, w |= φ AU AX done= {(σ', r)} w' ]> ->
      <( {instr_thread (k r) σ'}, w' |= φ AU ψ )> ->
      <( {instr_thread (x <- t ;; k x) σ}, w |= φ AU ψ )>.
  Proof. exact (aul_ithread_bind_r_eq h_stateW). Qed.

  (** A raw state update [σ ↦ f σ] leaves exactly one [Log] observation and then
      returns [r]; suffix [AU] version. *)
  Lemma aur_thread_update {Σ X} :
    forall (f : Σ -> Σ) (r : X) (σ : Σ) w ψ R,
      <( {log (B:=B) (f σ)}, w |= ψ )> ->
      R (f σ, r) (Obs (Log (f σ)) tt) ->
      <[ {instr_thread (B:=B)
            (Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
               (fun σ0 : Σ =>
                  Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                    (fun _ : unit => Ret r))) σ},
         w |= ψ AU ret R ]>.
  Proof.
    intros f r σ w ψ R Hlog HR.
    pose proof (ticll_not_done unit _ _ _ Hlog) as Hnd.
    rewrite instr_thread_get; cbv beta.
    setoid_rewrite instr_thread_put; cbv beta.
    eapply aur_log.
    - cleft; apply axr_thread_ret; eauto with ticl.
    - now apply ticll_bind_l.
  Qed.

  (** A raw state update [σ ↦ f σ]; prefix [AU] version. *)
  Lemma aul_thread_update {Σ X} :
    forall (f : Σ -> Σ) (r : X) (σ : Σ) w ψ φ,
      <( {log (B:=B) (f σ)}, w |= ψ )> ->
      <( {Ret (f σ, r) : ctreeW Σ B (Σ * X)}, {Obs (Log (f σ)) tt} |= φ )> ->
      <( {instr_thread (B:=B)
            (Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
               (fun σ0 : Σ =>
                  Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                    (fun _ : unit => Ret r))) σ},
         w |= ψ AU φ )>.
  Proof.
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
      R (σ, tt) w ->
      <[ {instr_schedule (B:=B) 1
            [(Ret tt : ctree (yieldE +' (forkE +' stateE Σ)) B unit)]%vector
            (Some Fin.F1) σ}, w |= ret R ]>.
  Proof. exact (axr_schedule_nd_ret (B:=B) h_stateW). Qed.

  (** A cooperative [Yield] in a singleton pool costs one visible step: the
      scheduler picks the (single) runnable slot. *)
  Lemma axax_schedule_yield {Σ} : forall (σ : Σ) w R,
      not_done w ->
      R (σ, tt) w ->
      <[ {instr_schedule (B:=B) 1
            [Vis (inl1 Yield : (yieldE +' (forkE +' stateE Σ)) unit)
               (fun _ : unit => Ret tt)]%vector
            (Some Fin.F1) σ}, w |= AX ret R ]>.
  Proof. exact (axax_schedule_nd_yield (B:=B) h_stateW). Qed.

  (** A scheduled singleton state update leaves exactly one [Log]; suffix [AU]. *)
  Lemma aur_schedule_update {Σ} :
    forall (f : Σ -> Σ) (σ : Σ) w ψ R,
      <( {log (B:=B) (f σ)}, w |= ψ )> ->
      R (f σ, tt) (Obs (Log (f σ)) tt) ->
      <[ {instr_schedule (B:=B) 1
            [Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
               (fun σ0 : Σ =>
                  Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                    (fun _ : unit => Ret tt))]%vector
            (Some Fin.F1) σ},
         w |= ψ AU ret R ]>.
  Proof.
    intros f σ w ψ R Hlog HR.
    pose proof (ticll_not_done unit _ _ _ Hlog) as Hnd.
    rewrite (interp_schedule_nd_singleton_update f
               [Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
                  (fun σ0 : Σ =>
                     Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                       (fun _ : unit => Ret tt))]%vector
               σ eq_refl
             : instr_schedule (B:=B) 1 _ (Some Fin.F1) σ ~ _).
    eapply aur_log.
    - cleft; apply ret_ret; eauto with ticl.
    - now apply ticll_bind_l.
  Qed.

  (** A scheduled singleton state update; prefix [AU]. *)
  Lemma aul_schedule_update {Σ} :
    forall (f : Σ -> Σ) (σ : Σ) w ψ φ,
      <( {log (B:=B) (f σ)}, w |= ψ )> ->
      <( {Ret (f σ, tt) : ctreeW Σ B (Σ * unit)}, {Obs (Log (f σ)) tt} |= φ )> ->
      <( {instr_schedule (B:=B) 1
            [Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
               (fun σ0 : Σ =>
                  Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                    (fun _ : unit => Ret tt))]%vector
            (Some Fin.F1) σ},
         w |= ψ AU φ )>.
  Proof.
    intros f σ w ψ φ Hlog Hret.
    rewrite (interp_schedule_nd_singleton_update f
               [Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
                  (fun σ0 : Σ =>
                     Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                       (fun _ : unit => Ret tt))]%vector
               σ eq_refl
             : instr_schedule (B:=B) 1 _ (Some Fin.F1) σ ~ _).
    cright.
    apply anl_log.
    - cleft; eauto with ticl.
    - now apply ticll_bind_l.
  Qed.
End RawThreadRules.

(** ** Recurrence for repeating turn batches.

    The turn-structured twin of [CTree.Logic.Trace.emit_batches_agaf]: every
    turn is one visible [Step] carrying at most one observation. *)
Section EmitTurnBatches.
  Context {W I X : Type} {B : Type -> Type}
    (batch : I -> list (option W)) (next : I -> I)
    (Inv : I -> Prop) (rank : I -> nat) (P : W -> Prop)
    (Hnext : forall i, Inv i -> Inv (next i))
    (Hnonempty : forall i, Inv i -> batch i <> Datatypes.nil)
    (Hprogress : forall i, Inv i ->
      (exists o, List.In (Some o) (batch i) /\ P o) \/ rank (next i) < rank i).

  Local Lemma after_logs_app (xs ys : list W) w :
    after_logs (xs ++ ys) w = after_logs ys (after_logs xs w).
  Proof.
    revert w; induction xs as [|o xs IH]; intro w; cbn [after_logs List.app];
      [reflexivity | apply IH].
  Qed.

  Local Lemma afr_emit_list {Y} xs (t : ctreeW W B Y) w (Q : Y -> World (writerE W) -> Prop) :
    not_done w ->
    <[ t, {after_logs xs w} |= AF ret {Q} ]> ->
    <[ {emit_list xs t}, w |= AF ret {Q} ]>.
  Proof.
    revert w; induction xs as [|o rest IH]; intros w Hd H; [exact H|].
    change <[ {log o ;; emit_list rest t}, w |= AF ret {Q} ]>.
    apply afr_log; [exact Hd|].
    apply IH; [constructor|exact H].
  Qed.

  Lemma af_emit_turns {Y} turns (t : ctreeW W B Y) w :
    not_done w ->
    <( t, {after_logs (List.flat_map event_obs turns) w} |= AF visW {P} )> ->
    <( {emit_turns turns t}, w |= AF visW {P} )>.
  Proof.
    revert w; induction turns as [|ev rest IH]; intros w Hd H; [exact H|].
    cbn [emit_turns List.flat_map] in *.
    rewrite after_logs_app in H.
    apply aul_step; right; split; [apply ticll_top; exact Hd|].
    apply af_emit_list; [exact Hd|].
    apply IH; [apply after_logs_not_done; exact Hd|exact H].
  Qed.

  Lemma af_emit_turns_member {Y} turns (t : ctreeW W B Y) w o :
    not_done w -> List.In (Some o) turns -> P o ->
    <( {emit_turns turns t}, w |= AF visW {P} )>.
  Proof.
    revert w; induction turns as [|ev rest IH]; intros w Hd Hin HP;
      [contradiction|].
    cbn [emit_turns].
    apply aul_step; right; split; [apply ticll_top; exact Hd|].
    destruct Hin as [Heq|Hin]; [subst ev|].
    - apply af_emit_list_member with o; [exact Hd|left; reflexivity|exact HP].
    - apply af_emit_list; [exact Hd|].
      apply IH; [apply after_logs_not_done; exact Hd|exact Hin|exact HP].
  Qed.

  Lemma af_emit_turns_ret {Y} turns (r : Y) w (Q : Y -> World (writerE W) -> Prop) :
    not_done w -> Q r (after_logs (List.flat_map event_obs turns) w) ->
    <[ {emit_turns turns (Ret r) : ctreeW W B Y}, w |= AF ret {Q} ]>.
  Proof.
    revert w; induction turns as [|ev rest IH]; intros w Hd HQ.
    - cleft; apply ret_ret; assumption.
    - cbn [emit_turns List.flat_map] in *.
      rewrite after_logs_app in HQ.
      apply aur_step; right; split; [apply ticll_top; exact Hd|].
      apply afr_emit_list; [exact Hd|].
      apply IH; [apply after_logs_not_done; exact Hd|exact HQ].
  Qed.

  Lemma emit_turn_batches_af : forall i w, Inv i -> not_done w ->
    <( {(emit_turn_batches batch next i : ctreeW W B X)}, {w} |= AF visW {P} )>.
  Proof.
    intros i w Hi Hd; unfold emit_turn_batches.
    eapply aul_iter_nat with (Ri := fun j (_ : World (writerE W)) => Inv j)
      (f := fun j (_ : World (writerE W)) => rank j).
    - exact Hd.
    - exact Hi.
    - intros j v Hv Hj.
      destruct (Hprogress j Hj) as [(o & Hin & HP) | Hlt].
      + left; eapply af_emit_turns_member; [exact Hv | exact Hin | exact HP].
      + right; apply af_emit_turns_ret; [exact Hv |].
        exists (next j); split; [reflexivity |].
        split; [apply after_logs_not_done; exact Hv |].
        split; [apply Hnext; exact Hj | exact Hlt].
  Qed.

  (** The coinductive invariant: a tree bisimilar to a remaining log prefix,
      then a remaining turn suffix of the current batch, then the loop.  Each
      step is guarded by a real log or a real turn step. *)
  Lemma emit_turn_batches_agaf : forall i w, Inv i -> not_done w ->
    <( {(emit_turn_batches batch next i : ctreeW W B X)}, {w} |= AG (AF visW {P}) )>.
  Proof.
    intros i w Hi Hd.
    assert (Hsuffix : forall (t : ctreeW W B X) v,
      (exists j logs suffix, Inv j /\ not_done v /\
        t ~ emit_list logs (emit_turns suffix (emit_turn_batches batch next j : ctreeW W B X))) ->
      <( t, v |= AG (AF visW {P}) )>).
    { coinduction R CIH; intros t v (j & logs & suffix & Hj & Hv & Ht).
      assert (Haf : <( t, v |= AF visW {P} )>).
      { rewrite Ht; apply af_emit_list; [exact Hv|].
        apply af_emit_turns; [apply after_logs_not_done; exact Hv|].
        apply emit_turn_batches_af; [exact Hj|].
        apply after_logs_not_done, after_logs_not_done; exact Hv. }
      destruct logs as [|o logs].
      - (* no pending log: the next turn is a visible step *)
        assert (Hexp : exists ev rest j', Inv j' /\
          t ~ Step (emit_list (event_obs ev)
                 (emit_turns rest (emit_turn_batches batch next j' : ctreeW W B X)))).
        { destruct suffix as [|ev rest].
          - destruct (batch j) as [|ev rest] eqn:Eb; [exfalso; exact (Hnonempty j Hj Eb)|].
            exists ev, rest, (next j); split; [apply Hnext, Hj|].
            rewrite Ht; unfold emit_list; cbn [List.fold_right emit_turns].
            rewrite emit_turn_batches_unfold_sbisim, Eb; reflexivity.
          - exists ev, rest, j; split; [exact Hj|exact Ht]. }
        destruct Hexp as (ev & rest & j' & Hj' & Ht').
        rewrite Ht'; rewrite Ht' in Haf; split; [exact Haf|]; split.
        + apply can_step_step; exact Hv.
        + intros t' w' Htr.
          apply ktrans_step in Htr as (Heq & <- & _).
          rewrite Heq; apply CIH; exists j', (event_obs ev), rest.
          split; [exact Hj'|]; split; [exact Hv|reflexivity].
      - (* a pending log is a visible observation *)
        rewrite Ht, emit_list_cons; rewrite Ht, emit_list_cons in Haf; split; [exact Haf|]; split.
        + apply can_step_vis; [exact tt|exact Hv].
        + intros t' w' Htr.
          apply ktrans_vis in Htr as ([] & -> & Heq & _).
          rewrite <- Heq; apply CIH; exists j, logs, suffix.
          split; [exact Hj|]; split; [constructor|reflexivity]. }
    apply Hsuffix; exists i, Datatypes.nil, Datatypes.nil.
    split; [exact Hi|]; split; [exact Hd|reflexivity].
  Qed.
End EmitTurnBatches.

(** ** Round-robin recurrence from executable cycle certificates.

    The top-level entry point for clients holding finite RR cycle runs
    rather than a preconstructed log loop: transport through
    [model_rr_emit_batches], then [emit_turn_batches_agaf]. *)
Section ModelRRRecurrence.
  Context {St Act W X I : Type} {B : Type -> Type}
    (n : nat) (actor : Fin.t (S n) -> Act)
    (step : Act -> St -> option (St * option W))
    (R : St -> St -> Prop)
    (Hstep : Proper (eq ==> R ==> Roption (RelProd R eq)) step)
    (boundary : I -> St) (batch : I -> list (option W)) (next : I -> I)
    (Inv : I -> Prop) (cursor period : nat)
    (Hcursor : (cursor + period) mod (S n) = cursor mod (S n))
    (Hnext : forall i, Inv i -> Inv (next i))
    (Hnonempty : forall i, Inv i -> batch i <> Datatypes.nil)
    (Hcycle : forall i, Inv i -> exists last,
      run_turns step turn_list (rr_script n actor cursor period) (boundary i) =
        Some (last,batch i) /\ R last (boundary (next i)))
    (rank : I -> nat) (P : W -> Prop)
    (Hprogress : forall i, Inv i ->
      (exists o, List.In (Some o) (batch i) /\ P o) \/ rank (next i) < rank i).

  Lemma model_rr_agaf : forall i w, Inv i -> not_done w ->
    <( {(model_rr n actor step (boundary i) cursor : ctreeW W B X)}, {w}
      |= AG (AF visW {P}) )>.
  Proof.
    intros i w Hi Hd.
    rewrite (model_rr_emit_batches n actor step R Hstep boundary batch next Inv
      cursor period Hcursor Hnext Hnonempty Hcycle i Hi).
    exact (emit_turn_batches_agaf batch next Inv rank P Hnext Hnonempty Hprogress i w Hi Hd).
  Qed.
End ModelRRRecurrence.

(** ** Structural invariance and eventuality over yielding pools.

    A pool of threads, each of which -- from every invariant state -- closes
    an exact, finite turn with exactly one observation and returns to the
    same thread, satisfies [AG] of any formula holding at all invariant
    configurations ([ClosedTurns]); if moreover every turn either emits a
    target observation or decreases a well-founded rank of ghost data
    ([RankedTurns]), then [AF] of the target holds.  The nondeterministic
    rules require this of EVERY selectable slot: no fair selection is
    assumed.  The certificates live in [Prop]; no choice function over the
    ghost witnesses is used. *)
Section PoolRules.
  Context {E B : Type -> Type} `{Bn -< B} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W B)).

  Abbreviation exactW := (fun X (t u : ctreeW W B X) => t ≅ u).

  Definition ClosedTurns {G n} (ts : pool E B (S n))
      (Inv : G -> Sigma -> Prop) : Prop :=
    forall g sigma (i : Fin.t (S n)), Inv g sigma ->
    exists g' sigma' o,
      segment_to handler exactW (ts $ i) sigma (List.cons o List.nil) (ts $ i) sigma' /\
      Inv g' sigma'.

  Definition RankedTurns {G V n} (ts : pool E B (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V)
      (ltV : V -> V -> Prop) (P : W -> Prop) : Prop :=
    forall g sigma (i : Fin.t (S n)), Inv g sigma ->
    exists g' sigma' o,
      segment_to handler exactW (ts $ i) sigma (List.cons o List.nil) (ts $ i) sigma' /\
      Inv g' sigma' /\ (P o \/ ltV (rank g') (rank g)).

  Lemma ranked_turns_closed {G V n} (ts : pool E B (S n)) Inv (rank : G -> V) ltV P :
    RankedTurns ts Inv rank ltV P -> ClosedTurns ts Inv.
  Proof.
    intros Hr g sigma i Hinv.
    destruct (Hr g sigma i Hinv) as (g' & sigma' & o & Hseg & Hinv' & _).
    exists g', sigma', o; split; assumption.
  Qed.

  Lemma ag_pool_nd_invariance {G n} (ts : pool E B (S n))
      (Inv : G -> Sigma -> Prop) (φ : ticllW W) :
    ClosedTurns ts Inv ->
    (forall g sigma focus w, Inv g sigma -> not_done w ->
       <( {interp_schedule_nd handler (S n) ts focus sigma}, {w} |= φ )>) ->
    forall g sigma focus w, Inv g sigma -> not_done w ->
      <( {interp_schedule_nd handler (S n) ts focus sigma}, {w} |= AG φ )>.
  Proof.
    intros Hclosed Hφ.
    coinduction R CIH; intros g sigma focus w Hinv Hw.
    pose proof (Hφ g sigma focus w Hinv Hw) as Hnow.
    destruct focus as [i|].
    - destruct (Hclosed g sigma i Hinv) as (g' & sigma' & o & Hseg & Hinv').
      rewrite (segment_pool_nd_loop handler n ts i sigma (List.cons o List.nil) sigma' Hseg),
        emit_list_cons in Hnow |- *.
      split; [exact Hnow|]; split.
      + apply can_step_vis; [exact tt|exact Hw].
      + intros t' w' Htr.
        apply ktrans_vis in Htr as ([] & -> & Heq & _).
        rewrite <- Heq.
        apply (CIH g' sigma' None); [exact Hinv'|constructor].
    - rewrite (interp_schedule_nd_select handler) in Hnow |- *.
      split; [exact Hnow|]; split.
      + apply (can_step_brS _ _ Fin.F1); exact Hw.
      + intros t' w' Htr.
        apply ktrans_brS in Htr as (i & Heq & <- & _).
        rewrite Heq.
        apply (CIH g sigma (Some i)); assumption.
  Qed.

  Lemma aul_pool_nd_eventually {G V n} (ts : pool E B (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V)
      (ltV : V -> V -> Prop) (P : W -> Prop) :
    well_founded ltV -> RankedTurns ts Inv rank ltV P ->
    forall g sigma focus w, Inv g sigma -> not_done w ->
      <( {interp_schedule_nd handler (S n) ts focus sigma}, {w} |= AF visW {P} )>.
  Proof.
    intros Hwf Hranked g.
    induction g as [g IH] using
      (well_founded_induction (wf_inverse_image G V ltV rank Hwf)).
    intros sigma focus w Hinv Hw.
    assert (Hsome : forall i w, not_done w ->
      <( {interp_schedule_nd handler (S n) ts (Some i) sigma}, {w} |= AF visW {P} )>).
    { intros i w0 Hw0.
      destruct (Hranked g sigma i Hinv) as (g' & sigma' & o & Hseg & Hinv' & [HP|Hlt]).
      - rewrite (segment_pool_nd_loop handler n ts i sigma (List.cons o List.nil) sigma' Hseg).
        cbn [emit_list List.fold_right].
        apply afl_log; [exact Hw0|].
        cleft; apply ticll_vis; constructor; exact HP.
      - rewrite (segment_pool_nd_loop handler n ts i sigma (List.cons o List.nil) sigma' Hseg).
        cbn [emit_list List.fold_right].
        apply afl_log; [exact Hw0|].
        apply (IH g' Hlt sigma' None); [exact Hinv'|constructor]. }
    destruct focus as [i|]; [apply Hsome, Hw|].
    rewrite (interp_schedule_nd_select handler).
    apply (aul_brS _ _ Fin.F1); right; split.
    - apply ticll_top; exact Hw.
    - intro i; apply Hsome, Hw.
  Qed.
End PoolRules.

(** The round-robin scheduler refines finite branches, so it lives at [Bn]. *)
Section PoolRulesRR.
  Context {E : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W Bn)).

  Abbreviation exactW := (fun X (t u : ctreeW W Bn X) => t ≅ u).

  Lemma ag_pool_rr_invariance {G n} (ts : pool E Bn (S n))
      (Inv : G -> Sigma -> Prop) (φ : ticllW W) :
    ClosedTurns handler ts Inv ->
    (forall g sigma focus cursor w, Inv g sigma -> not_done w ->
       <( {interp_schedule_rr handler (S n) ts focus cursor sigma}, {w} |= φ )>) ->
    forall g sigma focus cursor w, Inv g sigma -> not_done w ->
      <( {interp_schedule_rr handler (S n) ts focus cursor sigma}, {w} |= AG φ )>.
  Proof.
    intros Hclosed Hφ.
    coinduction R CIH; intros g sigma focus cursor w Hinv Hw.
    pose proof (Hφ g sigma focus cursor w Hinv Hw) as Hnow.
    destruct focus as [i|].
    - destruct (Hclosed g sigma i Hinv) as (g' & sigma' & o & Hseg & Hinv').
      rewrite (segment_pool_rr_loop handler n ts i cursor sigma (List.cons o List.nil) sigma' Hseg),
        emit_list_cons in Hnow |- *.
      split; [exact Hnow|]; split.
      + apply can_step_vis; [exact tt|exact Hw].
      + intros t' w' Htr.
        apply ktrans_vis in Htr as ([] & -> & Heq & _).
        rewrite <- Heq.
        apply (CIH g' sigma' None cursor); [exact Hinv'|constructor].
    - rewrite (interp_schedule_rr_select handler n ts cursor sigma) in Hnow |- *.
      split; [exact Hnow|]; split.
      + apply can_step_step; exact Hw.
      + intros t' w' Htr.
        apply ktrans_step in Htr as (Heq & <- & _).
        rewrite Heq.
        apply (CIH g sigma (Some (rr_pick n cursor)) (S cursor)); assumption.
  Qed.

  Lemma aul_pool_rr_eventually {G V n} (ts : pool E Bn (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V)
      (ltV : V -> V -> Prop) (P : W -> Prop) :
    well_founded ltV -> RankedTurns handler ts Inv rank ltV P ->
    forall g sigma focus cursor w, Inv g sigma -> not_done w ->
      <( {interp_schedule_rr handler (S n) ts focus cursor sigma}, {w} |= AF visW {P} )>.
  Proof.
    intros Hwf Hranked g.
    induction g as [g IH] using
      (well_founded_induction (wf_inverse_image G V ltV rank Hwf)).
    intros sigma focus cursor w Hinv Hw.
    assert (Hsome : forall i c w, not_done w ->
      <( {interp_schedule_rr handler (S n) ts (Some i) c sigma}, {w} |= AF visW {P} )>).
    { intros i c w0 Hw0.
      destruct (Hranked g sigma i Hinv) as (g' & sigma' & o & Hseg & Hinv' & [HP|Hlt]).
      - rewrite (segment_pool_rr_loop handler n ts i c sigma (List.cons o List.nil) sigma' Hseg).
        cbn [emit_list List.fold_right].
        apply afl_log; [exact Hw0|].
        cleft; apply ticll_vis; constructor; exact HP.
      - rewrite (segment_pool_rr_loop handler n ts i c sigma (List.cons o List.nil) sigma' Hseg).
        cbn [emit_list List.fold_right].
        apply afl_log; [exact Hw0|].
        apply (IH g' Hlt sigma' None c); [exact Hinv'|constructor]. }
    destruct focus as [i|]; [apply Hsome, Hw|].
    rewrite (interp_schedule_rr_select handler n ts cursor sigma).
    apply aul_step; right; split.
    - apply ticll_top; exact Hw.
    - apply Hsome, Hw.
  Qed.
End PoolRulesRR.
