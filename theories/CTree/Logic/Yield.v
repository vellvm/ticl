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
  CTree.Interp.Yield.Policy
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
      <[ {interp_state h (interp_thread t) s}, w |= ret= {(s', r)} w' ]> ->
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
      <[ {interp_state h (interp_thread t) s}, w |= φ AU ret= {(s', r)} w' ]> ->
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
      <[ {interp_state h (interp_thread t) s}, w |= φ AU ret= {(s', r)} w' ]> ->
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
      <[ {instr_thread t σ}, w |= ret= {(σ', r)} w' ]> ->
      <[ {instr_thread (k r) σ'}, w' |= φ AN ψ ]> ->
      <[ {instr_thread (x <- t ;; k x) σ}, w |= φ AN ψ ]>.
  Proof. exact (anr_ithread_bind_r_eq h_stateW). Qed.

  (** Sequential composition of raw threads, suffix [AU]. *)
  Lemma aur_thread_bind_r_eq {Σ A C} :
    forall (t : ctree (yieldE +' (forkE +' stateE Σ)) B A)
           (k : A -> ctree (yieldE +' (forkE +' stateE Σ)) B C)
           (σ σ' : Σ) (r : A) w w' φ ψ,
      <[ {instr_thread t σ}, w |= φ AU ret= {(σ', r)} w' ]> ->
      <[ {instr_thread (k r) σ'}, w' |= φ AU ψ ]> ->
      <[ {instr_thread (x <- t ;; k x) σ}, w |= φ AU ψ ]>.
  Proof. exact (aur_ithread_bind_r_eq h_stateW). Qed.

  (** Sequential composition of raw threads, prefix [AU]. *)
  Lemma aul_thread_bind_r_eq {Σ A C} :
    forall (t : ctree (yieldE +' (forkE +' stateE Σ)) B A)
           (k : A -> ctree (yieldE +' (forkE +' stateE Σ)) B C)
           (σ σ' : Σ) (r : A) w w' φ ψ,
      <[ {instr_thread t σ}, w |= φ AU ret= {(σ', r)} w' ]> ->
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

(** ** Round-robin recurrence from executable cycle certificates.

    The top-level entry point for clients holding finite RR cycle runs
    rather than a preconstructed log loop: transport through
    [model_rr_emit_batches], then [emit_batches_agaf]. *)
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
    <( {(model_rr n actor step (boundary i) cursor : ctreeW (W + nat) B X)}, {w}
      |= AG (AF visW {fair_obs P}) )>.
  Proof.
    intros i w Hi Hd.
    rewrite (model_rr_emit_batches n actor step R Hstep boundary batch next Inv
      cursor period Hcursor Hnext Hnonempty Hcycle i Hi).
    apply (emit_batches_agaf (fun j => rr_run_obs n cursor (batch j)) next Inv rank (fair_obs P) Hnext).
    - intros j Hj Hnil; apply (Hnonempty j Hj), (proj1 (rr_run_obs_nil_iff n cursor (batch j))), Hnil.
    - intros j Hj; destruct (Hprogress j Hj) as [(o & Hin & HP)|Hlt]; [left|right; exact Hlt].
      exists (inl o); split; [apply in_rr_run_obs; exact Hin|exact HP].
    - exact Hi.
    - exact Hd.
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

(** The round-robin runner lives at [Bn]; its observations are the program's
    under [inl] and the scheduling decisions under [inr]. *)
Section PoolRulesRR.
  Context {E : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W Bn)).

  Abbreviation exactW := (fun X (t u : ctreeW W Bn X) => t ≅ u).

  Lemma ag_pool_rr_invariance {G n} (ts : pool E Bn (S n))
      (Inv : G -> Sigma -> Prop) (φ : ticllW (W + nat)) :
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
      rewrite (segment_pool_fair_loop rr_scheduler handler n ts i cursor sigma (List.cons o List.nil) sigma' Hseg) in Hnow |- *.
      cbn [List.map] in Hnow |- *; rewrite emit_list_cons in Hnow |- *.
      split; [exact Hnow|]; split.
      + apply can_step_vis; [exact tt|exact Hw].
      + intros t' w' Htr.
        apply ktrans_vis in Htr as ([] & -> & Heq & _).
        rewrite <- Heq.
        apply (CIH g' sigma' None cursor); [exact Hinv'|constructor].
    - rewrite (interp_schedule_rr_select handler n ts cursor sigma) in Hnow |- *.
      split; [exact Hnow|]; split.
      + apply can_step_vis; [exact tt|exact Hw].
      + intros t' w' Htr.
        apply ktrans_vis in Htr as ([] & -> & Heq & _).
        rewrite <- Heq.
        apply (CIH g sigma (Some (rr_pick n cursor)) (S cursor)); [exact Hinv|constructor].
  Qed.

  Lemma aul_pool_rr_eventually {G V n} (ts : pool E Bn (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V)
      (ltV : V -> V -> Prop) (P : W -> Prop) :
    well_founded ltV -> RankedTurns handler ts Inv rank ltV P ->
    forall g sigma focus cursor w, Inv g sigma -> not_done w ->
      <( {interp_schedule_rr handler (S n) ts focus cursor sigma}, {w} |= AF visW {fair_obs P} )>.
  Proof.
    intros Hwf Hranked g.
    induction g as [g IH] using
      (well_founded_induction (wf_inverse_image G V ltV rank Hwf)).
    intros sigma focus cursor w Hinv Hw.
    assert (Hsome : forall i c w, not_done w ->
      <( {interp_schedule_rr handler (S n) ts (Some i) c sigma}, {w} |= AF visW {fair_obs P} )>).
    { intros i c w0 Hw0.
      destruct (Hranked g sigma i Hinv) as (g' & sigma' & o & Hseg & Hinv' & [HP|Hlt]).
      - rewrite (segment_pool_fair_loop rr_scheduler handler n ts i c sigma (List.cons o List.nil) sigma' Hseg).
        cbn [List.map emit_list List.fold_right].
        apply afl_log; [exact Hw0|].
        cleft; apply ticll_vis; constructor; exact HP.
      - rewrite (segment_pool_fair_loop rr_scheduler handler n ts i c sigma (List.cons o List.nil) sigma' Hseg).
        cbn [List.map emit_list List.fold_right].
        apply afl_log; [exact Hw0|].
        apply (IH g' Hlt sigma' None c); [exact Hinv'|constructor]. }
    destruct focus as [i|]; [apply Hsome, Hw|].
    rewrite (interp_schedule_rr_select handler n ts cursor sigma).
    apply (aul_vis _ _ tt); right; split.
    - apply ticll_top; exact Hw.
    - intros []; apply Hsome; constructor.
  Qed.
End PoolRulesRR.
