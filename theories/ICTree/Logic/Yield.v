From Stdlib Require Import
  List
  Arith.PeanoNat
  Classes.Morphisms
  Classes.RelationPairs
  Fin
  Vector
  Program.Equality
  Wellfounded.Inverse_Image.

From Coinduction Require Import coinduction.

From ExtLib Require Import Data.Option.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Events.Yield
  ICTree.Events.State
  ICTree.Events.Writer
  ICTree.Interp.Core
  ICTree.Interp.Refine
  ICTree.Interp.State.Mod
  ICTree.Interp.Yield.Mod
  ICTree.Interp.Yield.Nondeterministic
  ICTree.Interp.Yield.RoundRobin
  ICTree.Interp.Yield.Segments
  ICTree.Interp.Yield.Execution
  ICTree.Trace
  ICTree.Logic.Trans
  ICTree.Logic.AG
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.Bind
  ICTree.Logic.CanStep
  ICTree.Logic.State
  ICTree.Logic.Trace
  Logic.Core
  Utils.Execution
  Utils.Vectors.

Import ICtree ICTreeNotations TiclNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

(** * TICL rules for instrumented raw threads and scheduled pools *)
(** These rules are stated over raw [ictree] values built from [yieldE],
    [forkE] and [stateE] events.  They know nothing about source syntax; a
    language lifts them by instantiating the raw trees with its denotations. *)

(** The singleton scheduler reductions are the operational equations of
    [ICTree.Interp.Yield.Nondeterministic]: [instr_schedule] is definitionally
    [interp_schedule_nd h_stateW], so the modal rules below only combine those
    equations with the tree-level [AX]/[AN]/log rules. *)

(** ** Rules for raw threads under an arbitrary state handler. *)
Section ThreadStateRules.
  Context {E W S : Type} {HE : Encode E} (h : E ~> stateT S (ictreeW W)).

  Lemma axr_ithread_ret {X} : forall (r : X) (s : S) w R,
      not_done w ->
      R (r, s) w ->
      <[ {interp_state h (interp_thread (Ret r : ictree (yieldE + (forkE + E)) X)) s},
         w |= AX done R ]>.
  Proof with eauto with ticl.
    intros r s w R Hnd HR.
    rewrite interp_state_thread_ret.
    apply axr_ret...
  Qed.

  Lemma anr_ithread_bind_r_eq {A B} :
    forall (t : ictree (yieldE + (forkE + E)) A)
           (k : A -> ictree (yieldE + (forkE + E)) B)
           (s s' : S) (r : A) w w' φ ψ,
      <[ {interp_state h (interp_thread t) s}, w |= φ AN done= {(r, s')} w' ]> ->
      <[ {interp_state h (interp_thread (k r)) s'}, w' |= φ AN ψ ]> ->
      <[ {interp_state h (interp_thread (x <- t ;; k x)) s}, w |= φ AN ψ ]>.
  Proof.
    intros t k s s' r w w' φ ψ Ht Hk.
    rewrite interp_state_thread_bind.
    eapply anr_bind_r_eq; eauto.
  Qed.

  Lemma aur_ithread_bind_r_eq {A B} :
    forall (t : ictree (yieldE + (forkE + E)) A)
           (k : A -> ictree (yieldE + (forkE + E)) B)
           (s s' : S) (r : A) w w' φ ψ,
      <[ {interp_state h (interp_thread t) s}, w |= φ AU AX done= {(r, s')} w' ]> ->
      <[ {interp_state h (interp_thread (k r)) s'}, w' |= φ AU ψ ]> ->
      <[ {interp_state h (interp_thread (x <- t ;; k x)) s}, w |= φ AU ψ ]>.
  Proof.
    intros t k s s' r w w' φ ψ Ht Hk.
    rewrite interp_state_thread_bind.
    eapply aur_bind_r_eq; eauto.
  Qed.

  Lemma aul_ithread_bind_r_eq {A B} :
    forall (t : ictree (yieldE + (forkE + E)) A)
           (k : A -> ictree (yieldE + (forkE + E)) B)
           (s s' : S) (r : A) w w' φ ψ,
      <[ {interp_state h (interp_thread t) s}, w |= φ AU AX done= {(r, s')} w' ]> ->
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
  Context {E W S : Type} {HE : Encode E} (h : E ~> stateT S (ictreeW W)).

  Lemma axr_schedule_nd_ret : forall (s : S) w R,
      not_done w ->
      R (tt, s) w ->
      <[ {interp_schedule_nd h 1 [(Ret tt : thread E)]%vector (Some Fin.F1) s},
         w |= AX done R ]>.
  Proof with eauto with ticl.
    intros s w R Hnd HR.
    rewrite (interp_schedule_nd_ret h 0 [(Ret tt : thread E)]%vector Fin.F1 s eq_refl).
    rewrite interp_schedule_nd_empty.
    apply axr_ret...
  Qed.

  Lemma axax_schedule_nd_yield : forall (s : S) w R,
      not_done w ->
      R (tt, s) w ->
      <[ {interp_schedule_nd h 1
            [Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => Ret tt)]%vector
            (Some Fin.F1) s}, w |= AX AX done R ]>.
  Proof with eauto with ticl.
    intros s w R Hnd HR.
    rewrite (interp_schedule_nd_yield h 0
               [Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => Ret tt)]%vector
               Fin.F1 (fun _ : unit => (Ret tt : thread E)) s eq_refl).
    rewrite interp_schedule_nd_select.
    apply anr_br; split.
    - csplit...
    - intro i; dependent destruction i.
      + rewrite (interp_schedule_nd_ret h 0 _ Fin.F1 s)
          by (now rewrite Vector.nth_replace_eq).
        rewrite interp_schedule_nd_empty.
        apply axr_ret...
      + inversion i.
  Qed.
End ScheduleStateRules.

(** ** Raw thread rules. *)

(** A finished raw thread terminates in one step with the unchanged state. *)
Lemma axr_thread_ret {Σ X} : forall (r : X) (σ : Σ) w R,
    not_done w ->
    R (r, σ) w ->
    <[ {instr_thread (Ret r) σ}, w |= AX done R ]>.
Proof. exact (axr_ithread_ret h_stateW). Qed.

(** Sequential composition of raw threads, suffix [AN]. *)
Lemma anr_thread_bind_r_eq {Σ A B} :
  forall (t : ictree (yieldE + (forkE + stateE Σ)) A)
         (k : A -> ictree (yieldE + (forkE + stateE Σ)) B)
         (σ σ' : Σ) (r : A) w w' φ ψ,
    <[ {instr_thread t σ}, w |= φ AN done= {(r, σ')} w' ]> ->
    <[ {instr_thread (k r) σ'}, w' |= φ AN ψ ]> ->
    <[ {instr_thread (x <- t ;; k x) σ}, w |= φ AN ψ ]>.
Proof. exact (anr_ithread_bind_r_eq h_stateW). Qed.

(** Sequential composition of raw threads, suffix [AU]. *)
Lemma aur_thread_bind_r_eq {Σ A B} :
  forall (t : ictree (yieldE + (forkE + stateE Σ)) A)
         (k : A -> ictree (yieldE + (forkE + stateE Σ)) B)
         (σ σ' : Σ) (r : A) w w' φ ψ,
    <[ {instr_thread t σ}, w |= φ AU AX done= {(r, σ')} w' ]> ->
    <[ {instr_thread (k r) σ'}, w' |= φ AU ψ ]> ->
    <[ {instr_thread (x <- t ;; k x) σ}, w |= φ AU ψ ]>.
Proof. exact (aur_ithread_bind_r_eq h_stateW). Qed.

(** Sequential composition of raw threads, prefix [AU]. *)
Lemma aul_thread_bind_r_eq {Σ A B} :
  forall (t : ictree (yieldE + (forkE + stateE Σ)) A)
         (k : A -> ictree (yieldE + (forkE + stateE Σ)) B)
         (σ σ' : Σ) (r : A) w w' φ ψ,
    <[ {instr_thread t σ}, w |= φ AU AX done= {(r, σ')} w' ]> ->
    <( {instr_thread (k r) σ'}, w' |= φ AU ψ )> ->
    <( {instr_thread (x <- t ;; k x) σ}, w |= φ AU ψ )>.
Proof. exact (aul_ithread_bind_r_eq h_stateW). Qed.

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
Proof. exact (axr_schedule_nd_ret h_stateW). Qed.

(** A cooperative [Yield] in a singleton pool costs two steps: the scheduler
    emits the scheduling point and then chooses the (single) runnable slot. *)
Lemma axax_schedule_yield {Σ} : forall (σ : Σ) w R,
    not_done w ->
    R (tt, σ) w ->
    <[ {instr_schedule 1
          [Vis ((inl Yield) : yieldE + (forkE + stateE Σ))
             (fun _ : unit => Ret tt)]%vector
          (Some Fin.F1) σ}, w |= AX AX done R ]>.
Proof. exact (axax_schedule_nd_yield h_stateW). Qed.

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
  rewrite (interp_schedule_nd_singleton_update f
             [Vis ((inr (inr Get)) : yieldE + (forkE + stateE Σ))
                (fun σ0 : Σ =>
                   Vis ((inr (inr (Put (f σ0)))) : yieldE + (forkE + stateE Σ))
                     (fun _ : unit => Ret tt))]%vector
             σ eq_refl
           : instr_schedule 1 _ (Some Fin.F1) σ ~ _).
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
  rewrite (interp_schedule_nd_singleton_update f
             [Vis ((inr (inr Get)) : yieldE + (forkE + stateE Σ))
                (fun σ0 : Σ =>
                   Vis ((inr (inr (Put (f σ0)))) : yieldE + (forkE + stateE Σ))
                     (fun _ : unit => Ret tt))]%vector
             σ eq_refl
           : instr_schedule 1 _ (Some Fin.F1) σ ~ _).
  cright.
  apply anl_log.
  - cleft...
  - now apply ticll_bind_l.
Qed.

(** ** Round-robin recurrence from executable cycle certificates.

    The top-level entry point for clients holding finite RR cycle runs
    rather than a preconstructed log loop: transport through
    [model_rr_emit_batches], then [emit_batches_agaf]. *)
Section ModelRRRecurrence.
  Context {St Act W X I : Type}
    (n : nat) (actor : Fin.t (S n) -> Act)
    (step : Act -> St -> option (St * option W))
    (R : St -> St -> Prop)
    (Hstep : Proper (eq ==> R ==> Roption (RelProd R eq)) step)
    (boundary : I -> St) (batch : I -> list W) (next : I -> I)
    (Inv : I -> Prop) (cursor period : nat)
    (Hcursor : (cursor + period) mod (S n) = cursor mod (S n))
    (Hnext : forall i, Inv i -> Inv (next i))
    (Hnonempty : forall i, Inv i -> batch i <> Datatypes.nil)
    (Hcycle : forall i, Inv i -> exists last,
      run_turns step event_obs (rr_script n actor cursor period) (boundary i) =
        Some (last,batch i) /\ R last (boundary (next i)))
    (rank : I -> nat) (P : W -> Prop)
    (Hprogress : forall i, Inv i ->
      (exists o, List.In o (batch i) /\ P o) \/ rank (next i) < rank i).

  Lemma model_rr_agaf : forall i w, Inv i -> not_done w ->
    <( {(model_rr n actor step (boundary i) cursor : ictreeW W X)}, {w}
      |= AG (AF visW {P}) )>.
  Proof.
    intros i w Hi Hd.
    rewrite (model_rr_emit_batches n actor step R Hstep boundary batch next Inv
      cursor period Hcursor Hnext Hnonempty Hcycle i Hi).
    exact (emit_batches_agaf batch next Inv rank P Hnext Hnonempty Hprogress i w Hi Hd).
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
  Context {E W Sigma : Type} {HE : Encode E}
    (handler : E ~> stateT Sigma (ictreeW W)).

  Notation exactW := (fun X (t u : ictreeW W X) => t ≅ u).

  Definition ClosedTurns {G n} (ts : pool E (S n))
      (Inv : G -> Sigma -> Prop) : Prop :=
    forall g sigma (i : Fin.t (S n)), Inv g sigma ->
    exists g' sigma' o,
      segment_to handler exactW (ts $ i) sigma (List.cons o List.nil) (ts $ i) sigma' /\
      Inv g' sigma'.

  Definition RankedTurns {G V n} (ts : pool E (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V)
      (ltV : V -> V -> Prop) (P : W -> Prop) : Prop :=
    forall g sigma (i : Fin.t (S n)), Inv g sigma ->
    exists g' sigma' o,
      segment_to handler exactW (ts $ i) sigma (List.cons o List.nil) (ts $ i) sigma' /\
      Inv g' sigma' /\ (P o \/ ltV (rank g') (rank g)).

  Lemma ranked_turns_closed {G V n} (ts : pool E (S n)) Inv (rank : G -> V) ltV P :
    RankedTurns ts Inv rank ltV P -> ClosedTurns ts Inv.
  Proof.
    intros H g sigma i Hinv.
    destruct (H g sigma i Hinv) as (g' & sigma' & o & Hseg & Hinv' & _).
    exists g', sigma', o; split; assumption.
  Qed.

  Local Lemma log_vis {X} (o : W) (k : ictreeW W X) :
    emit_list (List.cons o List.nil) k ≅ Vis (Log o) (fun _ => k).
  Proof.
    cbn [emit_list List.fold_right]; unfold log, ICtree.trigger.
    rewrite bind_vis; apply vis_equ_node; intros []; apply bind_ret_l.
  Qed.

  Lemma ag_pool_nd_invariance {G n} (ts : pool E (S n))
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
        log_vis in Hnow |- *.
      split; [exact Hnow|]; split.
      + apply can_step_vis; [exact tt|exact Hw].
      + intros t' w' Htr.
        apply ktrans_vis in Htr as ([] & -> & <- & _).
        apply (CIH g' sigma' None); [exact Hinv'|constructor].
    - rewrite (interp_schedule_nd_select handler) in Hnow |- *.
      split; [exact Hnow|]; split.
      + apply can_step_br; exact Hw.
      + intros t' w' Htr.
        apply ktrans_br in Htr as (i & -> & <- & _).
        apply (CIH g sigma (Some i)); assumption.
  Qed.

  Lemma ag_pool_rr_invariance {G n} (ts : pool E (S n))
      (Inv : G -> Sigma -> Prop) (φ : ticllW W) :
    ClosedTurns ts Inv ->
    (forall g sigma focus cursor w, Inv g sigma -> not_done w ->
       <( {interp_schedule_rr handler (S n) ts focus cursor sigma}, {w} |= φ )>) ->
    forall g sigma focus cursor w, Inv g sigma -> not_done w ->
      <( {interp_schedule_rr handler (S n) ts focus cursor sigma}, {w} |= AG φ )>.
  Proof.
    intros Hclosed Hφ.
    coinduction R CIH; intros g sigma focus cursor w Hinv Hw.
    pose proof (Hφ g sigma focus cursor w Hinv Hw) as Hnow.
    destruct focus as [i|];
      [|rewrite (interp_schedule_rr_select handler n ts cursor sigma) in Hnow |- *].
    all: lazymatch goal with
         | |- context [interp_schedule_rr _ _ _ (Some ?j) ?c ?s] =>
             destruct (Hclosed g s j Hinv) as (g' & sigma' & o & Hseg & Hinv');
             rewrite (segment_pool_rr_loop handler n ts j c s (List.cons o List.nil) sigma' Hseg),
               log_vis in Hnow |- *;
             split; [exact Hnow|]; split;
             [apply can_step_vis; [exact tt|exact Hw]
             |intros t' w' Htr;
              apply ktrans_vis in Htr as ([] & -> & <- & _);
              apply (CIH g' sigma' None c); [exact Hinv'|constructor]]
         end.
  Qed.

  Lemma aul_pool_nd_eventually {G V n} (ts : pool E (S n))
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
    apply aul_br; right; split.
    - apply ticll_top; exact Hw.
    - intro i; apply Hsome, Hw.
  Qed.

  Lemma aul_pool_rr_eventually {G V n} (ts : pool E (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V)
      (ltV : V -> V -> Prop) (P : W -> Prop) :
    well_founded ltV -> RankedTurns ts Inv rank ltV P ->
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
    apply Hsome, Hw.
  Qed.
End PoolRules.
