From TICL Require Import CTree.Interp.Yield.Policy.
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
  CTree.Interp.State.Mod
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.Nondeterministic
  CTree.Interp.Yield.Policy
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.Segments
  CTree.Interp.Yield.Execution
  CTree.Trace
  CTree.Logic.Trans
  CTree.Logic.AG
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.EF
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
      <( {interp_state h (interp_thread (Ret r : ctree (yieldE +' (forkE +' E)) B X)) s},
         w |=R ret R )>.
  Proof.
    intros r s w R Hnd HR.
    ticl_normalize; rewrite interp_state_thread_ret.
    apply ret_ret; eauto with ticl.
  Qed.

  Lemma anr_ithread_bind_r_eq {A C} :
    forall (t : ctree (yieldE +' (forkE +' E)) B A)
           (k : A -> ctree (yieldE +' (forkE +' E)) B C)
           (s s' : S) (r : A) w w' (φ : ticl (writerE W) None) (ψ : ticl (writerE W) (Some ((S * C) : Type))),
      <( {interp_state h (interp_thread t) s}, w |=R ret= {(s', r)} w' )> ->
      <( {interp_state h (interp_thread (k r)) s'}, w' |=R φ AN ψ )> ->
      <( {interp_state h (interp_thread (x <- t ;; k x)) s}, w |=R φ AN ψ )>.
  Proof.
    intros t k s s' r w w' φ ψ Ht Hk.
    ticl_normalize; rewrite interp_state_thread_bind.
    eapply ticl_bind_ret_eq; eauto.
  Qed.

  Lemma au_ithread_bind_r_eq {A C} {b : bool} :
    forall (t : ctree (yieldE +' (forkE +' E)) B A)
           (k : A -> ctree (yieldE +' (forkE +' E)) B C)
           (s s' : S) (r : A) w w'
           (phi : ticl (writerE W) None) (psi : ticl_at (writerE W) (S * C) b),
      entails (S * A) true (Cu Q_A phi (CRet (fun y z => (s', r) = y /\ w' = z)))
        (interp_state h (interp_thread t) s) w ->
      entails (S * C) b (Cu Q_A phi psi) (interp_state h (interp_thread (k r)) s') w' ->
      entails (S * C) b (Cu Q_A phi psi) (interp_state h (interp_thread (CTree.bind t k)) s) w.
  Proof.
    intros * Ht Hk; rewrite interp_state_thread_bind.
    eapply (u_bind_r_eq (b:=b) Q_A); eauto.
  Qed.
End ThreadStateRules.

(** ** Singleton scheduler rules under an arbitrary state handler. *)
Section ScheduleStateRules.
  Context {E B : Type -> Type} `{Bn -< B} {W S : Type} (h : E ~> stateT S (ctreeW W B)).

  Lemma axr_schedule_nd_ret : forall (s : S) w R,
      not_done w ->
      R (s, tt) w ->
      <( {interp_schedule_nd h 1 [(Ret tt : thread E B)]%vector (Some Fin.F1) s},
         w |=R ret R )>.
  Proof.
    intros s w R Hnd HR.
    ticl_normalize; rewrite (interp_schedule_nd_ret h 0 [(Ret tt : thread E B)]%vector Fin.F1 s eq_refl).
    rewrite interp_schedule_nd_empty.
    apply ret_ret; eauto with ticl.
  Qed.

  (** A cooperative [Yield] costs one visible step: the scheduling pick. *)
  Lemma axax_schedule_nd_yield : forall (s : S) w R,
      not_done w ->
      R (s, tt) w ->
      <( {interp_schedule_nd h 1
            [Vis (inl1 Yield : (yieldE +' (forkE +' E)) unit) (fun _ : unit => Ret tt)]%vector
            (Some Fin.F1) s}, w |=R AX ret R )>.
  Proof.
    intros s w R Hnd HR.
    ticl_normalize; rewrite (interp_schedule_nd_yield h 0
               [Vis (inl1 Yield : (yieldE +' (forkE +' E)) unit) (fun _ : unit => Ret tt)]%vector
               Fin.F1 (fun _ : unit => (Ret tt : thread E B)) s eq_refl).
    rewrite interp_schedule_nd_select.
    apply (an_brS (b:=true) _ _ Fin.F1); split.
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
      <( {instr_thread (B:=B) (Ret r) σ}, w |=R ret R )>.
  Proof. exact (axr_ithread_ret h_stateW). Qed.

  (** Sequential composition of raw threads, suffix [AN]. *)
  Lemma anr_thread_bind_r_eq {Σ A C} :
    forall (t : ctree (yieldE +' (forkE +' stateE Σ)) B A)
           (k : A -> ctree (yieldE +' (forkE +' stateE Σ)) B C)
           (σ σ' : Σ) (r : A) w w' (φ : ticl (writerE Σ) None) (ψ : ticl (writerE Σ) (Some ((Σ * C) : Type))),
      <( {instr_thread t σ}, w |=R ret= {(σ', r)} w' )> ->
      <( {instr_thread (k r) σ'}, w' |=R φ AN ψ )> ->
      <( {instr_thread (x <- t ;; k x) σ}, w |=R φ AN ψ )>.
  Proof. exact (anr_ithread_bind_r_eq h_stateW). Qed.

  (** Sequential composition preserves an indexed until endpoint. *)
  Lemma au_thread_bind_r_eq {Σ A C} {b : bool} :
    forall (t : ctree (yieldE +' (forkE +' stateE Σ)) B A)
           (k : A -> ctree (yieldE +' (forkE +' stateE Σ)) B C)
           (σ σ' : Σ) (r : A) w w'
           (phi : ticl (writerE Σ) None) (psi : ticl_at (writerE Σ) (Σ * C) b),
      entails (Σ * A) true (Cu Q_A phi (CRet (fun y z => (σ', r) = y /\ w' = z))) (instr_thread t σ) w ->
      entails (Σ * C) b (Cu Q_A phi psi) (instr_thread (k r) σ') w' ->
      entails (Σ * C) b (Cu Q_A phi psi) (instr_thread (CTree.bind t k) σ) w.
  Proof. exact (au_ithread_bind_r_eq h_stateW (b:=b)). Qed.

  (** A raw update hands its logged final return to the indexed endpoint. *)
  Lemma au_thread_update {Σ X} {b : bool} :
    forall (f : Σ -> Σ) (r : X) (σ : Σ) w
      (phi : ticl (writerE Σ) None) (psi : ticl_at (writerE Σ) (Σ * X) b),
      entails unit false phi (log (B:=B) (f σ)) w ->
      entails (Σ * X) b psi (Ret (f σ, r) : ctreeW Σ B (Σ * X)) (Obs (Log (f σ)) tt) ->
      entails (Σ * X) b (Cu Q_A phi psi)
        (instr_thread (B:=B)
          (Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
            (fun σ0 : Σ =>
              Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                (fun _ : unit => Ret r))) σ) w.
  Proof.
    intros * Hlog Hret; rewrite instr_thread_get; cbv beta.
    setoid_rewrite instr_thread_put; cbv beta.
    cright; apply (an_log (b:=b)).
    - cleft; rewrite instr_thread_ret; exact Hret.
    - now apply ticll_bind_l.
  Qed.

  (** ** Raw singleton scheduler rules. *)

  (** A finished singleton pool terminates in one step. *)
  Lemma axr_schedule_ret {Σ} : forall (σ : Σ) w R,
      not_done w ->
      R (σ, tt) w ->
      <( {instr_schedule (B:=B) 1
            [(Ret tt : ctree (yieldE +' (forkE +' stateE Σ)) B unit)]%vector
            (Some Fin.F1) σ}, w |=R ret R )>.
  Proof. exact (axr_schedule_nd_ret (B:=B) h_stateW). Qed.

  (** A cooperative [Yield] in a singleton pool costs one visible step: the
      scheduler picks the (single) runnable slot. *)
  Lemma axax_schedule_yield {Σ} : forall (σ : Σ) w R,
      not_done w ->
      R (σ, tt) w ->
      <( {instr_schedule (B:=B) 1
            [Vis (inl1 Yield : (yieldE +' (forkE +' stateE Σ)) unit)
               (fun _ : unit => Ret tt)]%vector
            (Some Fin.F1) σ}, w |=R AX ret R )>.
  Proof. exact (axax_schedule_nd_yield (B:=B) h_stateW). Qed.

  (** A scheduled singleton state update leaves exactly one [Log]; suffix [AU]. *)
  Lemma aur_schedule_update {Σ} :
    forall (f : Σ -> Σ) (σ : Σ) w (ψ : ticl (writerE Σ) None) R,
      <( {log (B:=B) (f σ)}, w |=L ψ )> ->
      R (f σ, tt) (Obs (Log (f σ)) tt) ->
      <( {instr_schedule (B:=B) 1
            [Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
               (fun σ0 : Σ =>
                  Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                    (fun _ : unit => Ret tt))]%vector
            (Some Fin.F1) σ},
         w |=R ψ AU ret R )>.
  Proof.
    intros f σ w ψ R Hlog HR.
    pose proof (ticl_not_done unit false _ _ _ Hlog) as Hnd.
    ticl_normalize; rewrite (interp_schedule_nd_singleton_update f
               [Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
                  (fun σ0 : Σ =>
                     Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                       (fun _ : unit => Ret tt))]%vector
               σ eq_refl
             : instr_schedule (B:=B) 1 _ (Some Fin.F1) σ ~ _).
    eapply (au_log (b:=true)).
    - cleft; apply ret_ret; eauto with ticl.
    - now apply ticll_bind_l.
  Qed.

  (** A scheduled singleton state update; prefix [AU]. *)
  Lemma aul_schedule_update {Σ} :
    forall (f : Σ -> Σ) (σ : Σ) w (ψ φ : ticl (writerE Σ) None),
      <( {log (B:=B) (f σ)}, w |=L ψ )> ->
      <( {Ret (f σ, tt) : ctreeW Σ B (Σ * unit)}, {Obs (Log (f σ)) tt} |=L φ )> ->
      <( {instr_schedule (B:=B) 1
            [Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
               (fun σ0 : Σ =>
                  Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                    (fun _ : unit => Ret tt))]%vector
            (Some Fin.F1) σ},
         w |=L ψ AU φ )>.
  Proof.
    intros f σ w ψ φ Hlog Hret.
    ticl_normalize; rewrite (interp_schedule_nd_singleton_update f
               [Vis (inr1 (inr1 Get) : (yieldE +' (forkE +' stateE Σ)) Σ)
                  (fun σ0 : Σ =>
                     Vis (inr1 (inr1 (Put (f σ0))) : (yieldE +' (forkE +' stateE Σ)) unit)
                       (fun _ : unit => Ret tt))]%vector
               σ eq_refl
             : instr_schedule (B:=B) 1 _ (Some Fin.F1) σ ~ _).
    cright.
    apply (an_log (b:=false)).
    - cleft; eauto with ticl.
    - now apply ticll_bind_l.
  Qed.
End RawThreadRules.

Lemma f_emit_turns {W : Type} {B : Type -> Type} {X : Type} {b : bool}
  (q : ticlq) (turns : list (list W)) (t : ctreeW W B X) w
  (ψ : ticl_at (writerE W) X b) :
  not_done w ->
  entails X b (Cu q (CNow (fun _ => True)) ψ) t
    (after_logs (List.concat turns) w) ->
  entails X b (Cu q (CNow (fun _ => True)) ψ) (emit_turns turns t) w.
Proof.
  revert w; induction turns as [|ev rest IH]; intros w Hd H; [exact H|].
  cbn [emit_turns List.concat] in *.
  rewrite after_logs_app in H.
  destruct q; [apply (au_step (b:=b)) | apply (eu_step (b:=b))];
    right; split; [apply ticll_top; exact Hd |
      apply (f_emit_list (b:=b) Q_A); [exact Hd|];
      apply IH; [apply after_logs_not_done; exact Hd|exact H] |
      apply ticll_top; exact Hd |
      apply (f_emit_list (b:=b) Q_E); [exact Hd|];
      apply IH; [apply after_logs_not_done; exact Hd|exact H]].
Qed.

(** ** Recurrence for repeating turn batches.

    The turn-structured twin of [CTree.Logic.Trace.emit_batches_agaf]: every
    turn is one visible [Step] followed by its finite observation list. *)
Section EmitTurnBatches.
  Context {W I X : Type} {B : Type -> Type}
    (batch : I -> list (list W)) (next : I -> I)
    (Inv : I -> Prop) (rank : I -> nat) (P : W -> Prop)
    (Hnext : forall i, Inv i -> Inv (next i))
    (Hnonempty : forall i, Inv i -> batch i <> Datatypes.nil)
    (Hprogress : forall i, Inv i ->
      (exists o, List.In o (List.concat (batch i)) /\ P o) \/ rank (next i) < rank i).

  Lemma af_emit_turns {Y} turns (t : ctreeW W B Y) w :
    not_done w ->
    <( t, {after_logs (List.concat turns) w} |=L AF visW {P} )> ->
    <( {emit_turns turns t}, w |=L AF visW {P} )>.
  Proof.
    apply (f_emit_turns (b:=false) Q_A).
  Qed.

  Lemma af_emit_turns_member {Y} turns (t : ctreeW W B Y) w o :
    not_done w -> List.In o (List.concat turns) -> P o ->
    <( {emit_turns turns t}, w |=L AF visW {P} )>.
  Proof.
    revert w; induction turns as [|ev rest IH]; intros w Hd Hin HP;
      [contradiction|].
    cbn [emit_turns].
    apply (au_step (b:=false)); right; split; [apply ticll_top; exact Hd|].
    cbn [List.concat] in Hin; apply List.in_app_iff in Hin as [Hin|Hin].
    - apply af_emit_list_member with o; [exact Hd|exact Hin|exact HP].
    - apply af_emit_list; [exact Hd|].
      apply IH; [apply after_logs_not_done; exact Hd|exact Hin|exact HP].
  Qed.

  Lemma af_emit_turns_ret {Y} turns (r : Y) w (Q : Y -> World (writerE W) -> Prop) :
    not_done w -> Q r (after_logs (List.concat turns) w) ->
    <( {emit_turns turns (Ret r) : ctreeW W B Y}, w |=R AF ret {Q} )>.
  Proof.
    intros Hd HQ; apply (f_emit_turns (b:=true) Q_A); [exact Hd|].
    cleft; apply ret_ret; [apply after_logs_not_done; exact Hd|exact HQ].
  Qed.

  Lemma emit_turn_batches_af : forall i w, Inv i -> not_done w ->
    <( {(emit_turn_batches batch next i : ctreeW W B X)}, {w} |=L AF visW {P} )>.
  Proof.
    intros i w Hi Hd; unfold emit_turn_batches.
    eapply (u_iter_prefix_nat Q_A) with (Ri := fun j (_ : World (writerE W)) => Inv j)
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
    <( {(emit_turn_batches batch next i : ctreeW W B X)}, {w} |=L AG (AF visW {P}) )>.
  Proof.
    intros i w Hi Hd.
    assert (Hsuffix : forall (t : ctreeW W B X) v,
      (exists j logs suffix, Inv j /\ not_done v /\
        t ~ emit_list logs (emit_turns suffix (emit_turn_batches batch next j : ctreeW W B X))) ->
      <( t, v |=L AG (AF visW {P}) )>).
    { coinduction R CIH; intros t v (j & logs & suffix & Hj & Hv & Ht).
      assert (Haf : <( t, v |=L AF visW {P} )>).
      { ticl_normalize; rewrite Ht; apply af_emit_list; [exact Hv|].
        apply af_emit_turns; [apply after_logs_not_done; exact Hv|].
        apply emit_turn_batches_af; [exact Hj|].
        apply after_logs_not_done, after_logs_not_done; exact Hv. }
      ticl_normalize in Haf;
      destruct logs as [|o logs].
      - (* no pending log: the next turn is a visible step *)
        assert (Hexp : exists ev rest j', Inv j' /\
          t ~ Step (emit_list ev
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
          rewrite Heq; apply CIH; exists j', ev, rest.
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
    [model_rr_emit_batches], then [emit_batches_agaf]. *)
Section ModelRRRecurrence.
  Context {St Act W X I : Type} {B : Type -> Type}
    (n : nat) (actor : Fin.t (S n) -> Act)
    (step : Act -> St -> option (St * list W))
    (R : St -> St -> Prop)
    (Hstep : Proper (eq ==> R ==> Roption (RelProd R eq)) step)
    (boundary : I -> St) (batch : I -> list (list W)) (next : I -> I)
    (Inv : I -> Prop) (cursor period : nat)
    (Hcursor : (cursor + period) mod (S n) = cursor mod (S n))
    (Hnext : forall i, Inv i -> Inv (next i))
    (Hnonempty : forall i, Inv i -> batch i <> Datatypes.nil)
    (Hcycle : forall i, Inv i -> exists last,
      run_turns step (fun xs => List.cons xs List.nil) (rr_script n actor cursor period) (boundary i) =
        Some (last,batch i) /\ R last (boundary (next i)))
    (rank : I -> nat) (P : W -> Prop)
    (Hprogress : forall i, Inv i ->
      (exists o, List.In o (List.concat (batch i)) /\ P o) \/ rank (next i) < rank i).

  Lemma model_rr_agaf : forall i w, Inv i -> not_done w ->
    <( {(model_rr n actor step (boundary i) cursor : ctreeW (W + nat) B X)}, {w}
      |=L AG (AF visW {fair_obs P}) )>.
  Proof.
    intros i w Hi Hd.
    ticl_normalize; rewrite (model_rr_emit_batches n actor step R Hstep boundary batch next Inv
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
    exists g' sigma' logs,
      segment_to handler exactW (ts $ i) sigma logs (ts $ i) sigma' /\
      Inv g' sigma'.

  Definition RankedTurns {G V n} (ts : pool E B (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V)
      (ltV : V -> V -> Prop) (P : W -> Prop) : Prop :=
    forall g sigma (i : Fin.t (S n)), Inv g sigma ->
    exists g' sigma' logs,
      segment_to handler exactW (ts $ i) sigma logs (ts $ i) sigma' /\
      Inv g' sigma' /\ (List.Exists P logs \/ ltV (rank g') (rank g)).

  Lemma ranked_turns_closed {G V n} (ts : pool E B (S n)) Inv (rank : G -> V) ltV P :
    RankedTurns ts Inv rank ltV P -> ClosedTurns ts Inv.
  Proof.
    intros Hr g sigma i Hinv.
    destruct (Hr g sigma i Hinv) as (g' & sigma' & o & Hseg & Hinv' & _).
    exists g', sigma', o; split; assumption.
  Qed.

  Lemma ranked_turns_mono {G V n} (ts : pool E B (S n)) Inv (rank : G -> V) ltV P Q :
    (forall o, P o -> Q o) ->
    RankedTurns ts Inv rank ltV P -> RankedTurns ts Inv rank ltV Q.
  Proof.
    intros HPQ Hr g sigma i Hinv.
    destruct (Hr g sigma i Hinv) as (g' & sigma' & logs & Hseg & Hinv' & Hcase).
    exists g',sigma',logs; split; [exact Hseg|split; [exact Hinv'|]].
    destruct Hcase as [HP|Hrank]; [left; eapply List.Exists_impl; [exact HPQ|exact HP]|now right].
  Qed.

  Lemma ag_pool_nd_invariance {G n} (ts : pool E B (S n))
      (Inv : G -> Sigma -> Prop) (φ : ticl (writerE W) None) :
    ClosedTurns ts Inv ->
    (forall (o : W) (t : ctreeW W B (Sigma * unit)) w, not_done w ->
      entails (Sigma * unit) false φ t (Obs (Log o) tt) ->
      entails (Sigma * unit) false φ (Vis (Log o) (fun _ => t)) w) ->
    (forall g sigma focus w, Inv g sigma -> not_done w ->
       <( {interp_schedule_nd handler (S n) ts focus sigma}, {w} |=L φ )>) ->
    forall g sigma focus w, Inv g sigma -> not_done w ->
      <( {interp_schedule_nd handler (S n) ts focus sigma}, {w} |=L AG φ )>.
  Proof.
    intros Hclosed Hlog Hφ.
    assert (Hpref : forall xs (t : ctreeW W B (Sigma * unit)),
      (forall w, not_done w -> entails (Sigma * unit) false φ t w) ->
      forall w, not_done w -> entails (Sigma * unit) false φ (emit_list xs t) w).
    { induction xs as [|o xs IH]; intros t Ht w Hw; [apply Ht, Hw|].
      rewrite emit_list_cons; apply Hlog; [exact Hw|].
      apply IH; [exact Ht|constructor]. }
    coinduction R CIH; intros g sigma focus w Hinv Hw.
    assert (Hnone : forall g sigma w, Inv g sigma -> not_done w ->
      agcF (entails (Sigma * unit) false φ) (elem R) (interp_schedule_nd handler (S n) ts None sigma) w).
    { clear g sigma focus w Hinv Hw; intros g sigma w Hinv Hw.
      pose proof (Hφ g sigma None w Hinv Hw) as Hnow.
      ticl_normalize in Hnow.
      rewrite (interp_schedule_nd_select handler) in Hnow |- *.
      split; [exact Hnow|]; split.
      - apply (can_step_brS _ _ Fin.F1); exact Hw.
      - intros t' w' Htr; apply ktrans_brS in Htr as (i & Heq & <- & _).
        rewrite Heq; apply (CIH g sigma (Some i)); assumption. }
    destruct focus as [i|]; [|apply (Hnone g sigma w Hinv Hw)].
    destruct (Hclosed g sigma i Hinv) as (g' & sigma' & logs & Hseg & Hinv').
    rewrite (segment_pool_nd_loop handler n ts i sigma logs sigma' Hseg).
    clear Hseg; revert w Hw.
    induction logs as [|o logs IHlogs]; intros w Hw.
    - cbn [emit_list List.fold_right]; apply (Hnone g' sigma' w Hinv' Hw).
    - rewrite emit_list_cons; split; [|split].
      + apply Hlog; [exact Hw|]; apply Hpref; [|constructor].
        intros z Hz; apply (Hφ g' sigma' None z Hinv' Hz).
      + apply can_step_vis; [exact tt|exact Hw].
      + intros t' w' Htr; apply ktrans_vis in Htr as ([] & -> & Heq & _).
        rewrite <- Heq; apply (b_chain R), IHlogs; constructor.
  Qed.

  Lemma aul_pool_nd_eventually {G V n} (ts : pool E B (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V)
      (ltV : V -> V -> Prop) (P : W -> Prop) :
    well_founded ltV -> RankedTurns ts Inv rank ltV P ->
    forall g sigma focus w, Inv g sigma -> not_done w ->
      <( {interp_schedule_nd handler (S n) ts focus sigma}, {w} |=L AF visW {P} )>.
  Proof.
    intros Hwf Hranked g.
    induction g as [g IH] using
      (well_founded_induction (wf_inverse_image G V ltV rank Hwf)).
    intros sigma focus w Hinv Hw; ticl_normalize.
    assert (Hsome : forall i w, not_done w ->
      <( {interp_schedule_nd handler (S n) ts (Some i) sigma}, {w} |=L AF visW {P} )>).
    { intros i w0 Hw0; ticl_normalize.
      destruct (Hranked g sigma i Hinv) as (g' & sigma' & logs & Hseg & Hinv' & [HP|Hlt]);
        rewrite (segment_pool_nd_loop handler n ts i sigma logs sigma' Hseg).
      - apply List.Exists_exists in HP as (o & Hin & HP).
        eapply af_emit_list_member; [exact Hw0|exact Hin|exact HP].
      - apply af_emit_list; [exact Hw0|].
        apply (IH g' Hlt sigma' None); [exact Hinv'|apply after_logs_not_done; exact Hw0]. }
    destruct focus as [i|]; [apply Hsome, Hw|].
    rewrite (interp_schedule_nd_select handler).
    apply ((au_brS (b:=false)) _ _ Fin.F1); right; split.
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
      (Inv : G -> Sigma -> Prop) (φ : ticl (writerE (W + nat)) None) :
    ClosedTurns handler ts Inv ->
    (forall (o : W) (t : ctreeW (W + nat) Bn (Sigma * unit)) w, not_done w ->
      entails (Sigma * unit) false φ t (Obs (Log (inl o)) tt) ->
      entails (Sigma * unit) false φ (Vis (Log (inl o)) (fun _ => t)) w) ->
    (forall g sigma focus cursor w, Inv g sigma -> not_done w ->
       <( {interp_schedule_rr handler (S n) ts focus cursor sigma}, {w} |=L φ )>) ->
    forall g sigma focus cursor w, Inv g sigma -> not_done w ->
      <( {interp_schedule_rr handler (S n) ts focus cursor sigma}, {w} |=L AG φ )>.
  Proof.
    intros Hclosed Hlog Hφ.
    assert (Hpref : forall xs (t : ctreeW (W + nat) Bn (Sigma * unit)),
      (forall w, not_done w -> entails (Sigma * unit) false φ t w) ->
      forall w, not_done w ->
        entails (Sigma * unit) false φ (emit_list (List.map inl xs) t) w).
    { induction xs as [|o xs IH]; intros t Ht w Hw; [apply Ht, Hw|].
      cbn [List.map]; rewrite emit_list_cons; apply Hlog; [exact Hw|].
      apply IH; [exact Ht|constructor]. }
    coinduction R CIH; intros g sigma focus cursor w Hinv Hw.
    assert (Hnone : forall g sigma cursor w, Inv g sigma -> not_done w ->
      agcF (entails (Sigma * unit) false φ) (elem R)
        (interp_schedule_rr handler (S n) ts None cursor sigma) w).
    { clear g sigma focus cursor w Hinv Hw; intros g sigma cursor w Hinv Hw.
      pose proof (Hφ g sigma None cursor w Hinv Hw) as Hnow.
      ticl_normalize in Hnow.
      rewrite (interp_schedule_rr_select handler n ts cursor sigma) in Hnow |- *.
      split; [exact Hnow|]; split.
      - apply can_step_vis; [exact tt|exact Hw].
      - intros t' w' Htr; apply ktrans_vis in Htr as ([] & -> & Heq & _).
        rewrite <- Heq.
        apply (CIH g sigma (Some (rr_pick n cursor)) (S cursor)); [exact Hinv|constructor]. }
    destruct focus as [i|]; [|apply (Hnone g sigma cursor w Hinv Hw)].
    destruct (Hclosed g sigma i Hinv) as (g' & sigma' & logs & Hseg & Hinv').
    rewrite (segment_pool_rr_loop handler n ts i cursor sigma logs sigma' Hseg).
    clear Hseg; revert w Hw.
    induction logs as [|o logs IHlogs]; intros w Hw.
    - cbn [List.map emit_list List.fold_right]; apply (Hnone g' sigma' cursor w Hinv' Hw).
    - cbn [List.map]; rewrite emit_list_cons; split; [|split].
      + apply Hlog; [exact Hw|]; apply Hpref; [|constructor].
        intros z Hz; apply (Hφ g' sigma' None cursor z Hinv' Hz).
      + apply can_step_vis; [exact tt|exact Hw].
      + intros t' w' Htr; apply ktrans_vis in Htr as ([] & -> & Heq & _).
        rewrite <- Heq; apply (b_chain R), IHlogs; constructor.
  Qed.

  Lemma aul_pool_rr_eventually {G V n} (ts : pool E Bn (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V)
      (ltV : V -> V -> Prop) (P : W -> Prop) :
    well_founded ltV -> RankedTurns handler ts Inv rank ltV P ->
    forall g sigma focus cursor w, Inv g sigma -> not_done w ->
      <( {interp_schedule_rr handler (S n) ts focus cursor sigma}, {w} |=L AF visW {fair_obs P} )>.
  Proof.
    intros Hwf Hranked g.
    induction g as [g IH] using
      (well_founded_induction (wf_inverse_image G V ltV rank Hwf)).
    intros sigma focus cursor w Hinv Hw; ticl_normalize.
    assert (Hsome : forall i c w, not_done w ->
      <( {interp_schedule_rr handler (S n) ts (Some i) c sigma}, {w} |=L AF visW {fair_obs P} )>).
    { intros i c w0 Hw0; ticl_normalize.
      destruct (Hranked g sigma i Hinv) as (g' & sigma' & logs & Hseg & Hinv' & [HP|Hlt]);
        rewrite (segment_pool_rr_loop handler n ts i c sigma logs sigma' Hseg).
      - apply List.Exists_exists in HP as (o & Hin & HP).
        eapply af_emit_list_member with (o := inl o); [exact Hw0|now apply List.in_map|exact HP].
      - apply af_emit_list; [exact Hw0|].
        apply (IH g' Hlt sigma' None c); [exact Hinv'|apply after_logs_not_done; exact Hw0]. }
    destruct focus as [i|]; [apply Hsome, Hw|].
    rewrite (interp_schedule_rr_select handler n ts cursor sigma).
    apply (au_vis (b:=false) _ _ tt); right; split.
    - apply ticll_top; exact Hw.
    - intros []; apply Hsome; constructor.
  Qed.
End PoolRulesRR.

(** ** Exact native-return normal forms for finite returning pools

    Finite administrative guards do not select another actor. An unfocused
    selection costs one [Step] under ND and one logged slot under RR; an
    already-focused slot costs neither. These equations describe return of
    the whole pool and preserve handler state without invoking the handler. *)
Section ReturningPoolsND.
  Context {E B : Type -> Type} `{Bn -< B} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W B)).

  Local Lemma returning_nd_slot n (ts : pool E B (S n))
      (i : Fin.t (S n)) k sigma :
    interp_schedule_nd handler (S n)
      (ts @ i := Nat.iter k (fun t => Guard t) (Ret tt)) (Some i) sigma ~
    interp_schedule_nd handler n (ts -- i) None sigma.
  Proof.
    induction k as [|k IH].
    - cbn [Nat.iter].
      rewrite (interp_schedule_nd_ret handler n (ts @ i := Ret tt) i sigma)
        by (rewrite Vector.nth_replace_eq; reflexivity).
      rewrite (interp_schedule_nd_equ handler n
        ((ts @ i := Ret tt) -- i) (ts -- i) None sigma).
      + reflexivity.
      + apply remove_replace_pool_equ.
    - cbn [Nat.iter].
      rewrite (segment_nd_focused_guard handler n ts i
        (Nat.iter k (fun t => Guard t) (Ret tt)) sigma).
      exact IH.
  Qed.

  Lemma interp_schedule_nd_returns n (ts : pool E B n)
      (focus : option (Fin.t n)) sigma :
    (forall i, exists k, (ts $ i) ≅ Nat.iter k (fun t => Guard t) (Ret tt)) ->
    interp_schedule_nd handler n ts focus sigma ~
    Nat.iter (match focus with None => n | Some _ => Nat.pred n end)
      (fun t => Step t) (Ret (sigma,tt) : ctreeW W B (Sigma * unit)).
  Proof.
    revert ts focus sigma; induction n as [|n IH]; intros ts focus sigma Hslots.
    - destruct focus as [i|]; [inversion i|].
      cbn [Nat.iter]; apply interp_schedule_nd_empty.
    - assert (Hfocused : forall i,
        interp_schedule_nd handler (S n) ts (Some i) sigma ~
        Nat.iter n (fun t => Step t) (Ret (sigma,tt) : ctreeW W B (Sigma * unit))).
      { intro i; destruct (Hslots i) as [k Hk].
        rewrite (interp_schedule_nd_equ handler (S n) ts
          (ts @ i := Nat.iter k (fun t => Guard t) (Ret tt)) (Some i) sigma).
        2: { intro j; destruct (Fin.eq_dec j i) as [->|Hne].
             - rewrite Vector.nth_replace_eq; exact Hk.
             - rewrite Vector.nth_replace_neq by congruence; reflexivity. }
        rewrite (returning_nd_slot n ts i k sigma).
        apply IH; intro j.
        exact (vector_remove_pointwise
          (fun (t _ : thread E B) => exists k, t ≅ Nat.iter k (fun u => Guard u) (Ret tt))
          ts ts i (fun l _ => Hslots l) j). }
      destruct focus as [i|]; [exact (Hfocused i)|].
      rewrite interp_schedule_nd_select; cbn [Nat.iter].
      apply sb_br_l with (y:=Fin.F1); intro i.
      apply sb_step, Hfocused.
  Qed.
End ReturningPoolsND.

Section ReturningPoolsRR.
  Context {E : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W Bn)).

  Local Lemma returning_rr_slot n (ts : pool E Bn (S n))
      (i : Fin.t (S n)) k cursor sigma :
    interp_schedule_rr handler (S n)
      (ts @ i := Nat.iter k (fun t => Guard t) (Ret tt)) (Some i) cursor sigma ~
    interp_schedule_rr handler n (ts -- i) None cursor sigma.
  Proof.
    induction k as [|k IH].
    - cbn [Nat.iter].
      rewrite (interp_schedule_rr_ret handler n (ts @ i := Ret tt) i cursor sigma)
        by (rewrite Vector.nth_replace_eq; reflexivity).
      rewrite (interp_schedule_rr_equ handler n
        ((ts @ i := Ret tt) -- i) (ts -- i) None cursor sigma).
      + reflexivity.
      + apply remove_replace_pool_equ.
    - cbn [Nat.iter].
      rewrite (segment_rr_focused_guard handler n ts i
        (Nat.iter k (fun t => Guard t) (Ret tt)) cursor sigma).
      exact IH.
  Qed.

  Lemma interp_schedule_rr_returns n (ts : pool E Bn n)
      (focus : option (Fin.t n)) cursor sigma :
    (forall i, exists k, (ts $ i) ≅ Nat.iter k (fun t => Guard t) (Ret tt)) ->
    interp_schedule_rr handler n ts focus cursor sigma ~
    emit_list (List.map (@inr W nat)
      (rr_return_picks (match focus with None => n | Some _ => Nat.pred n end) cursor))
      (Ret (sigma,tt) : ctreeW (W + nat) Bn (Sigma * unit)).
  Proof.
    revert ts focus cursor sigma; induction n as [|n IH];
      intros ts focus cursor sigma Hslots.
    - destruct focus as [i|]; [inversion i|].
      dependent destruction ts; cbn [rr_return_picks List.map emit_list List.fold_right];
        apply interp_schedule_rr_empty.
    - assert (Hfocused : forall i cursor',
        interp_schedule_rr handler (S n) ts (Some i) cursor' sigma ~
        emit_list (List.map (@inr W nat) (rr_return_picks n cursor'))
          (Ret (sigma,tt) : ctreeW (W + nat) Bn (Sigma * unit))).
      { intros i cursor'; destruct (Hslots i) as [k Hk].
        rewrite (interp_schedule_rr_equ handler (S n) ts
          (ts @ i := Nat.iter k (fun t => Guard t) (Ret tt)) (Some i) cursor' sigma).
        2: { intro j; destruct (Fin.eq_dec j i) as [->|Hne].
             - rewrite Vector.nth_replace_eq; exact Hk.
             - rewrite Vector.nth_replace_neq by congruence; reflexivity. }
        rewrite (returning_rr_slot n ts i k cursor' sigma).
        apply IH; intro j.
        exact (vector_remove_pointwise
          (fun (t _ : thread E Bn) => exists k, t ≅ Nat.iter k (fun u => Guard u) (Ret tt))
          ts ts i (fun l _ => Hslots l) j). }
      destruct focus as [i|]; [exact (Hfocused i cursor)|].
      rewrite interp_schedule_rr_select; cbn [rr_return_picks List.map].
      rewrite emit_list_cons; apply sb_vis; intros []; apply Hfocused.
  Qed.
End ReturningPoolsRR.
