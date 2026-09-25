From Stdlib Require Import
  List
  Arith.PeanoNat
  Classes.Morphisms
  Classes.RelationPairs
  Fin
  Vector
  Program.Equality.

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
  ICTree.Interp.Yield.Execution
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
  rewrite (interp_schedule_nd_ret h_stateW 0
             [(Ret tt : ictree (yieldE + (forkE + stateE Σ)) unit)]%vector
             Fin.F1 σ eq_refl
           : instr_schedule 1 _ (Some Fin.F1) σ ~ _).
  rewrite interp_schedule_nd_empty.
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
  rewrite (interp_schedule_nd_yield h_stateW 0
             [Vis ((inl Yield) : yieldE + (forkE + stateE Σ))
                (fun _ : unit => Ret tt)]%vector
             Fin.F1
             (fun _ : unit => (Ret tt : ictree (yieldE + (forkE + stateE Σ)) unit))
             σ eq_refl
           : instr_schedule 1 _ (Some Fin.F1) σ ~ _).
  rewrite interp_schedule_nd_select.
  apply anr_br; split.
  - csplit...
  - intro i; dependent destruction i.
    + rewrite (interp_schedule_nd_ret h_stateW 0 _ Fin.F1 σ)
        by (now rewrite Vector.nth_replace_eq).
      rewrite interp_schedule_nd_empty.
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
