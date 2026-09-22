From Stdlib Require Import Arith.PeanoNat Lia Fin Vector Program.Equality.
From Coinduction Require Import coinduction rel tactics.
From TICL Require Import
  Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Events.Heap
  ICTree.Interp.Refine ICTree.Interp.Yield.Mod ICTree.Interp.Yield.RoundRobin
  ICTree.Logic.Trans ICTree.Logic.AX ICTree.Logic.AF ICTree.Logic.AG
  ICTree.Logic.Bind ICTree.Logic.State ICTree.Logic.CanStep
  Logic.Core Utils.Vectors.
From examples Require Import CSL.InterpTests.

Import ICtree ICTreeNotations TiclNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

Local Definition allocate_then_emit : CProg unit :=
  CBind (CAlloc 2) (fun base => CEmit 9 base).

(** Allocation is silent; its emission and final return are distinct steps. *)

Lemma rr_alloc_first_fit_ticl :
  <[ {run_rr allocate_then_emit (Pcm.hsingle 2 99) 5}, Pure |=
    AX (AX done {fun result w =>
      heq (fst (snd result)) (hunion (hblock 3 2) (Pcm.hsingle 2 99)) /\
      snd (snd result) = 6 /\ w = Obs (Log (SPop 9 3 5)) tt}) ]>.
Proof.
  assert (Free : block_free (Pcm.hsingle 2 99) 3 2)
    by (apply block_freeb_spec; reflexivity).
  assert (First : forall j, Nat.lt 0 j -> Nat.lt j 3 ->
    ~ block_free (Pcm.hsingle 2 99) j 2).
  { intros j J L F; assert (j = 1 \/ j = 2) by lia.
    destruct H; subst j;
      [specialize (F 1 ltac:(lia)) | specialize (F 0 ltac:(lia))]; discriminate F. }
  unfold run_rr.
  change [denote allocate_then_emit]%vector with
    ([Ret tt]%vector @ Fin.F1 := (denote_flow allocate_then_emit >>= fun _ => Ret tt)).
  unfold allocate_then_emit.
  rewrite anr_csl_rr_bind.
  rewrite anr_csl_rr_alloc with (base:=3) by (try lia; assumption).
  rewrite anr_csl_rr_emit.
  split.
  - apply ticll_top; constructor.
  - cbn beta iota.
    erewrite interp_schedule_rr_ret by source_observe.
    pool_simpl; rewrite vector_remove_head, interp_schedule_rr_empty.
    apply axr_ret; [constructor |].
    cbn; split; [intro address; reflexivity | split; reflexivity].
Qed.

Lemma nd_alloc_finite_observed h c : heap_finite h ->
  <( {run_nd allocate_then_emit h c}, Pure |=
    AF (visW {fun o => stag o = 9 /\ sidx o = c /\ Nat.lt 0 (sval o)}) )>.
Proof.
  intro Finite; unfold run_nd.
  change [denote allocate_then_emit]%vector with
    ([Ret tt]%vector @ Fin.F1 := (denote_flow allocate_then_emit >>= fun _ => Ret tt)).
  unfold allocate_then_emit.
  rewrite aul_csl_nd_bind.
  rewrite aul_csl_nd_alloc_finite by (try assumption; lia).
  intros base Base Free First.
  rewrite aul_csl_nd_emit.
  right; split.
  - apply ticll_top; constructor.
  - cleft; apply ticll_vis; constructor; cbn; repeat split; auto.
Qed.

Lemma rr_alloc_finite_observed h c : heap_finite h ->
  <( {run_rr allocate_then_emit h c}, Pure |=
    AF (visW {fun o => stag o = 9 /\ sidx o = c /\ Nat.lt 0 (sval o)}) )>.
Proof.
  intro Finite; unfold run_rr.
  change [denote allocate_then_emit]%vector with
    ([Ret tt]%vector @ Fin.F1 := (denote_flow allocate_then_emit >>= fun _ => Ret tt)).
  unfold allocate_then_emit.
  rewrite aul_csl_rr_bind.
  rewrite aul_csl_rr_alloc_finite by (try assumption; lia).
  intros base Base Free First.
  rewrite aul_csl_rr_emit.
  right; split.
  - apply ticll_top; constructor.
  - cleft; apply ticll_vis; constructor; cbn; repeat split; auto.
Qed.

(** Shared-state scheduling and scoped source continuations. *)

Lemma rr_shared_write_ticl :
  <[ {run_rr shared_write_program (Pcm.hsingle 4 0) 0}, Pure |=
    AF (AX done {fun result w =>
      heq (fst (snd result)) (upd (Pcm.hsingle 4 0) 4 9) /\
      snd (snd result) = 1 /\ w = Obs (Log (SPop 2 9 0)) tt}) ]>.
Proof.
  unfold run_rr.
  change [denote shared_write_program]%vector with
    ([Ret tt]%vector @ Fin.F1 := (denote_flow shared_write_program >>= fun _ => Ret tt)).
  unfold shared_write_program.
  rewrite aur_csl_rr_bind, aur_csl_rr_fork.
  lazymatch goal with |- @entailsR _ _ _ _ _ ?formula _ _ =>
  change (<[ {interp_schedule_rr sh 2
    ([denote (CBind (CRead 4) (fun v => CEmit 2 v)); Ret tt]%vector
      @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CWrite 4 9) (fun _ => CYield)) >>= fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) 0 (Pcm.hsingle 4 0,0)}, Pure |= {formula} ]>) end.
  rewrite aur_csl_rr_bind.
  rewrite aur_csl_rr_write by discriminate.
  rewrite aur_csl_rr_yield.
  lazymatch goal with |- @entailsR _ _ _ _ _ ?formula _ _ =>
  change (<[ {interp_schedule_rr sh 2
    ([Ret tt; Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CRead 4) (fun v => CEmit 2 v)) >>= fun _ => Ret tt))
    (Some Fin.F1) 1 (upd (Pcm.hsingle 4 0) 4 9,0)}, Pure |= {formula} ]>) end.
  rewrite aur_csl_rr_bind.
  rewrite aur_csl_rr_read with (value:=9) by apply upd_eq.
  rewrite aur_csl_rr_emit.
  right; split.
  - apply ticll_top; constructor.
  - cleft.
    repeat first
      [ progress pool_simpl
      | rewrite vector_remove_head
      | rewrite vector_remove_tail
      | erewrite interp_schedule_rr_ret by source_observe
      | rewrite interp_schedule_rr_select
      | rewrite interp_schedule_rr_empty ].
    apply axr_ret; [constructor |].
    cbn; split; [intro address; reflexivity | split; reflexivity].
Qed.

Lemma rr_shared_cas_ticl :
  <[ {run_rr shared_cas_program hemp 0}, Pure |=
    AX ({<( visW {fun o => o = SPop 10 1 0} )>} AN
      (AX done {fun result w =>
        heq (fst (snd result)) (upd (hunion (hblock 1 1) hemp) 1 10) /\
        snd (snd result) = 2 /\ w = Obs (Log (SPop 20 0 1)) tt})) ]>.
Proof.
  unfold run_rr.
  change [denote shared_cas_program]%vector with
    ([Ret tt]%vector @ Fin.F1 := (denote_flow shared_cas_program >>= fun _ => Ret tt)).
  unfold shared_cas_program.
  rewrite anr_csl_rr_bind.
  rewrite anr_csl_rr_alloc with (base:=1) by
    (try lia; apply block_freeb_spec; reflexivity).
  rewrite anr_csl_rr_bind, anr_csl_rr_fork.
  lazymatch goal with |- @entailsR _ _ _ _ _ ?formula _ _ =>
  change (<[ {interp_schedule_rr sh 2
    ([denote (CBind (CCAS 1 0 20) (fun won => CEmit 20 (if won then 1 else 0))); Ret tt]%vector
      @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CCAS 1 0 10) (fun won =>
        CBind (CEmit 10 (if won then 1 else 0)) (fun _ => CYield))) >>= fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) 0 (hunion (hblock 1 1) hemp,0)}, Pure |= {formula} ]>) end.
  rewrite anr_csl_rr_bind.
  rewrite anr_csl_rr_cas with (current:=0) by reflexivity.
  cbn [Nat.eqb].
  rewrite anr_csl_rr_bind, anr_csl_rr_emit.
  split.
  - apply ticll_top; constructor.
  - rewrite anr_csl_rr_yield.
    lazymatch goal with |- @entailsR _ _ _ _ _ ?formula _ _ =>
    change (<[ {interp_schedule_rr sh 2
      ([Ret tt; Ret tt]%vector @ Fin.F1 :=
        (denote_flow (CBind (CCAS 1 0 20) (fun won =>
          CEmit 20 (if won then 1 else 0))) >>= fun _ => Ret tt))
      (Some Fin.F1) 1 (upd (hunion (hblock 1 1) hemp) 1 10,1)},
      {Obs (Log (SPop 10 1 0)) tt} |= {formula} ]>) end.
    rewrite anr_csl_rr_bind.
    rewrite anr_csl_rr_cas with (current:=10) by apply upd_eq.
    cbn [Nat.eqb].
    rewrite anr_csl_rr_emit.
    split.
    + apply ticll_vis; constructor; reflexivity.
    + repeat first
        [ progress pool_simpl
        | rewrite vector_remove_head
        | rewrite vector_remove_tail
        | erewrite interp_schedule_rr_ret by source_observe
        | rewrite interp_schedule_rr_select
        | rewrite interp_schedule_rr_empty ].
      apply axr_ret; [constructor |].
      cbn; split; [intro address; reflexivity | split; reflexivity].
Qed.

Lemma rr_scoped_child_ticl :
  <[ {run_rr scoped_child_program hemp 0}, Pure |=
    AX ({<( visW {fun o => o = SPop 1 10 0} )>} AN
      ({<( visW {fun o => o = SPop 1 11 1} )>} AN
        (AX done {fun result w => heq (fst (snd result)) hemp /\
          snd (snd result) = 3 /\ w = Obs (Log (SPop 2 20 2)) tt}))) ]>.
Proof.
  set (body := CBind (CFork (CEmit 2 20))
    (fun _ => CBind (CEmit 1 10) (fun _ => CRet (None : option unit)))).
  set (haltk := fun _ : option unit => (Ret tt : thread sE)).
  set (after := fun r : option unit =>
    match r with None => haltk None | Some _ => denote_flow (CEmit 1 11) >>= haltk end).
  set (next := until_tail body after).
  unfold run_rr, scoped_child_program.
  lazymatch goal with |- @entailsR _ _ _ _ _ ?formula _ _ =>
  change (<[ {interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CUntilNone body) (fun _ => CEmit 1 11)) >>= haltk))
    (Some Fin.F1) 0 (hemp,0)}, Pure |= {formula} ]>) end.
  rewrite anr_csl_rr_bind, anr_csl_rr_until_none.
  lazymatch goal with |- @entailsR _ _ _ _ _ ?formula _ _ =>
  change (<[ {interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 := (denote_flow body >>= next))
    (Some Fin.F1) 0 (hemp,0)}, Pure |= {formula} ]>) end.
  unfold body at 1; rewrite anr_csl_rr_bind, anr_csl_rr_fork.
  lazymatch goal with |- @entailsR _ _ _ _ _ ?formula _ _ =>
  change (<[ {interp_schedule_rr sh 2
    ([denote (CEmit 2 20); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CEmit 1 10) (fun _ => CRet (None : option unit))) >>= next))
    (Some (Fin.FS Fin.F1)) 0 (hemp,0)}, Pure |= {formula} ]>) end.
  rewrite anr_csl_rr_bind, anr_csl_rr_emit.
  split.
  - apply ticll_top; constructor.
  - rewrite anr_csl_rr_ret.
    lazymatch goal with |- @entailsR _ _ _ _ _ ?formula _ _ =>
    change (<[ {interp_schedule_rr sh 2
      ([denote (CEmit 2 20); Ret tt]%vector @ Fin.FS Fin.F1 :=
        (denote_flow (CEmit 1 11) >>= haltk))
      (Some (Fin.FS Fin.F1)) 0 (hemp,1)},
      {Obs (Log (SPop 1 10 0)) tt} |= {formula} ]>) end.
    rewrite anr_csl_rr_emit.
    split.
    + apply ticll_vis; constructor; reflexivity.
    + erewrite interp_schedule_rr_ret by source_observe.
      pool_simpl; rewrite vector_remove_tail, vector_remove_head.
      rewrite anr_csl_rr_select.
      lazymatch goal with |- @entailsR _ _ _ _ _ ?formula _ _ =>
      change (<[ {interp_schedule_rr sh 1
        ([Ret tt]%vector @ Fin.F1 := (denote_flow (CEmit 2 20) >>= haltk))
        (Some Fin.F1) 1 (hemp,2)},
        {Obs (Log (SPop 1 11 1)) tt} |= {formula} ]>) end.
      rewrite anr_csl_rr_emit.
      split.
      * apply ticll_vis; constructor; reflexivity.
      * erewrite interp_schedule_rr_ret by source_observe.
        pool_simpl; rewrite vector_remove_head, interp_schedule_rr_empty.
        apply axr_ret; [constructor |].
        cbn; split; [intro address; reflexivity | split; reflexivity].
Qed.

(** Universal ND choices versus cursor-dependent round-robin choices. *)

Local Definition choice_good : CProg unit := CEmit 1 7.
Local Definition choice_bad : CProg unit :=
  CBind (CRead 99) (fun _ => CEmit 2 9).

Lemma nd_yield_bad_successor :
  ~ <( {interp_nd 2
        ([Ret tt; denote choice_bad] @ Fin.F1 :=
          (denote_flow CYield >>= fun _ => denote choice_good))
        (Some Fin.F1) (hemp,0)},
       Pure |= AX (AF (visW {fun _ => True})) )>.
Proof.
  intro H.
  apply anl_csl_nd_yield in H.
  destruct H as [_ Hnext].
  specialize (Hnext (Fin.FS Fin.F1)).
  change <( {interp_nd 2
              ([denote choice_good; Ret tt] @ Fin.FS Fin.F1 :=
                (denote_flow (CBind (CRead 99) (fun _ => CEmit 2 9)) >>=
                  fun _ => Ret tt))
              (Some (Fin.FS Fin.F1)) (hemp,0)},
             Pure |= AF (visW {fun _ => True}) )> in Hnext.
  apply (proj1 (aul_csl_nd_bind 1 [denote choice_good; Ret tt]
    (Fin.FS Fin.F1) (CRead 99) (fun _ => CEmit 2 9)
    (fun _ => Ret tt) hemp 0 Pure
    <( ⊤ )> <( visW {fun _ => True} )>)) in Hnext.
  pose proof (interp_nd_source_read_missing 1 [denote choice_good; Ret tt]
    (Fin.FS Fin.F1) 99
    (fun flow => match flow with
                 | None => Ret tt
                 | Some _ => denote_flow (CEmit 2 9);; Ret tt
                 end)
    hemp 0 eq_refl) as Hmissing.
  rewrite Hmissing in Hnext.
  apply aul_stuck in Hnext.
  apply ticll_vis in Hnext.
  inversion Hnext.
Qed.

Lemma nd_yield_all_emit :
  <( {interp_nd 2
        ([Ret tt; denote (CEmit 2 9)] @ Fin.F1 :=
          (denote_flow CYield >>= fun _ => denote choice_good))
        (Some Fin.F1) (hemp,0)},
       Pure |= AX (AF (visW {fun _ => True})) )>.
Proof.
  apply (proj2 (anl_csl_nd_yield 1 [Ret tt; denote (CEmit 2 9)] Fin.F1
    (fun _ => denote choice_good) hemp 0 Pure
    <( ⊤ )> <( AF (visW {fun _ => True}) )>)).
  split.
  - apply ticll_top; constructor.
  - intro j; dependent destruction j.
    + apply (proj2 (aul_csl_nd_emit 1 [Ret tt; denote (CEmit 2 9)] Fin.F1
        1 7 (fun _ => Ret tt) hemp 0 Pure
        <( ⊤ )> <( visW {fun _ => True} )>)).
      right; split.
      * apply ticll_top; constructor.
      * cleft. apply ticll_vis; constructor; exact I.
    + dependent destruction j.
      * apply (proj2 (aul_csl_nd_emit 1 [denote choice_good; Ret tt]
          (Fin.FS Fin.F1) 2 9 (fun _ => Ret tt) hemp 0 Pure
          <( ⊤ )> <( visW {fun _ => True} )>)).
        right; split.
        -- apply ticll_top; constructor.
        -- cleft. apply ticll_vis; constructor; exact I.
      * inversion j.
Qed.

Lemma rr_yield_cursor0_observed :
  <( {interp_schedule_rr sh 2
        ([Ret tt; denote choice_bad] @ Fin.F1 :=
          (denote_flow CYield >>= fun _ => denote choice_good))
        (Some Fin.F1) 0 (hemp,0)},
       Pure |= AX (visW {fun o => o = SPop 1 7 0}) )>.
Proof.
  apply (proj2 (anl_csl_rr_yield 1 [Ret tt; denote choice_bad] Fin.F1
    (fun _ => denote choice_good) 0 hemp 0 Pure
    <( ⊤ )> <( visW {fun o => o = SPop 1 7 0} )>)).
  apply (proj2 (anl_csl_rr_emit 1 [Ret tt; denote choice_bad] Fin.F1
    1 7 (fun _ => Ret tt) 1 hemp 0 Pure
    <( ⊤ )> <( visW {fun o => o = SPop 1 7 0} )>)).
  split.
  - apply ticll_top; constructor.
  - apply ticll_vis; constructor; reflexivity.
Qed.

Lemma rr_yield_cursor1_blocked :
  ~ <( {interp_schedule_rr sh 2
        ([Ret tt; denote choice_bad] @ Fin.F1 :=
          (denote_flow CYield >>= fun _ => denote choice_good))
        (Some Fin.F1) 1 (hemp,0)},
       Pure |= AX (visW {fun o => o = SPop 1 7 0}) )>.
Proof.
  intro H.
  apply (proj1 (anl_csl_rr_yield 1 [Ret tt; denote choice_bad] Fin.F1
    (fun _ => denote choice_good) 1 hemp 0 Pure
    <( ⊤ )> <( visW {fun o => o = SPop 1 7 0} )>)) in H.
  apply (proj1 (anl_csl_rr_bind 1 [denote choice_good; Ret tt]
    (Fin.FS Fin.F1) (CRead 99) (fun _ => CEmit 2 9)
    (fun _ => Ret tt) 2 hemp 0 Pure
    <( ⊤ )> <( visW {fun o => o = SPop 1 7 0} )>)) in H.
  pose proof (interp_rr_read_missing 1 [denote choice_good; Ret tt]
    (Fin.FS Fin.F1) 99
    (fun flow => match flow with
                 | None => Ret tt
                 | Some _ => denote_flow (CEmit 2 9);; Ret tt
                 end)
    2 hemp 0 eq_refl) as Hmissing.
  rewrite Hmissing in H.
  exact (anl_stuck H).
Qed.

(** Actual observations sustain AG; guard-only divergence does not. *)

Theorem nd_emit_loop_ag :
  <( {run_nd
       (CUntilNone
         (CBind (CEmit 7 9) (fun _ => CRet (Some tt : option unit))))
       hemp 0}, Pure |= AG ⊤ )>.
Proof.
  assert (Hproductive : forall c w, not_done w ->
    <( {run_nd
         (CUntilNone
           (CBind (CEmit 7 9) (fun _ => CRet (Some tt : option unit))))
         hemp c}, {w} |= AG ⊤ )>).
  {
    coinduction R CIH; intros c w Hw.
    unfold run_nd, denote.
    change (agcbt (entailsL (unit * SSig) <[ ⊤ ]>) R
      (interp_nd 1
        (([Ret tt] : pool sE 1) @ Fin.F1 :=
          (denote_flow
            (CUntilNone
              (CBind (CEmit 7 9) (fun _ => CRet (Some tt : option unit))))
            >>= fun _ => Ret tt))
        (Some Fin.F1) (hemp,c)) w).
    rewrite interp_nd_source_until_none, interp_nd_source_bind,
      interp_nd_source_emit_log.
    unfold log, ICtree.trigger.
    rewrite bind_vis.
    setoid_rewrite bind_ret_l.
    split; [split; [exact I | exact Hw] |].
    split.
    - apply can_step_vis; [exact tt | exact Hw].
    - intros t' w' Htr.
      apply ktrans_vis in Htr as ([] & -> & <- & Hnd).
      rewrite interp_nd_source_ret.
      erewrite interp_nd_guard by reflexivity.
      cbn [Vector.replace].
      apply CIH.
      constructor.
  }
  unfold run_nd, denote.
  change <( {interp_nd 1
    (([Ret tt] : pool sE 1) @ Fin.F1 :=
      (denote_flow
        (CUntilNone
          (CBind (CEmit 7 9) (fun _ => CRet (Some tt : option unit))))
        >>= fun _ => Ret tt))
    (Some Fin.F1) (hemp,0)}, Pure |= AG ⊤ )>.
  rewrite ag_csl_nd_until_none, ag_csl_nd_bind, ag_csl_nd_emit.
  split.
  - split; constructor.
  - rewrite ag_csl_nd_ret.
    erewrite interp_nd_guard by reflexivity.
    cbn [Vector.replace].
    apply Hproductive.
    constructor.
Qed.

Theorem rr_emit_loop_ag :
  <( {run_rr
       (CUntilNone
         (CBind (CEmit 7 9) (fun _ => CRet (Some tt : option unit))))
       hemp 0}, Pure |= AG ⊤ )>.
Proof.
  assert (Hproductive : forall c w, not_done w ->
    <( {run_rr
         (CUntilNone
           (CBind (CEmit 7 9) (fun _ => CRet (Some tt : option unit))))
         hemp c}, {w} |= AG ⊤ )>).
  {
    coinduction R CIH; intros c w Hw.
    unfold run_rr, denote.
    change (agcbt (entailsL (unit * SSig) <[ ⊤ ]>) R
      (interp_schedule_rr sh 1
        (([Ret tt] : pool sE 1) @ Fin.F1 :=
          (denote_flow
            (CUntilNone
              (CBind (CEmit 7 9) (fun _ => CRet (Some tt : option unit))))
            >>= fun _ => Ret tt))
        (Some Fin.F1) 0 (hemp,c)) w).
    rewrite interp_rr_until_none, interp_rr_bind, interp_rr_emit_log.
    unfold log, ICtree.trigger.
    rewrite bind_vis.
    setoid_rewrite bind_ret_l.
    split; [split; [exact I | exact Hw] |].
    split.
    - apply can_step_vis; [exact tt | exact Hw].
    - intros t' w' Htr.
      apply ktrans_vis in Htr as ([] & -> & <- & Hnd).
      rewrite interp_rr_ret.
      erewrite interp_schedule_rr_guard by reflexivity.
      cbn [Vector.replace].
      apply CIH.
      constructor.
  }
  unfold run_rr, denote.
  change <( {interp_schedule_rr sh 1
    (([Ret tt] : pool sE 1) @ Fin.F1 :=
      (denote_flow
        (CUntilNone
          (CBind (CEmit 7 9) (fun _ => CRet (Some tt : option unit))))
        >>= fun _ => Ret tt))
    (Some Fin.F1) 0 (hemp,0)}, Pure |= AG ⊤ )>.
  rewrite ag_csl_rr_until_none, ag_csl_rr_bind, ag_csl_rr_emit.
  split.
  - split; constructor.
  - rewrite ag_csl_rr_ret.
    erewrite interp_schedule_rr_guard by reflexivity.
    cbn [Vector.replace].
    apply Hproductive.
    constructor.
Qed.

Theorem nd_silent_loop_no_ag :
  ~ <( {run_nd (CUntilNone (CRet (Some tt : option unit))) hemp 0},
       Pure |= AG ⊤ )>.
Proof.
  set (p := CUntilNone (CRet (Some tt : option unit))).
  assert (Hraw : denote p ≅ Guard (denote p)).
  {
    unfold p, denote.
    etransitivity; [apply source_raw_until |].
    etransitivity; [apply source_raw_ret |].
    reflexivity.
  }
  assert (Hguard : run_nd p hemp 0 ≅ Guard (run_nd p hemp 0)).
  {
    unfold run_nd.
    etransitivity.
    - apply (interp_nd_equ 1 _ [Guard (denote p)]).
      apply SBisim.cons_pool_equ;
        [exact Hraw | apply SBisim.pool_equ_refl].
    - unfold interp_nd.
      rewrite (SBisim.trans_schedule_focused_guard
        0 [Guard (denote p)] Fin.F1 (denote p) eq_refl).
      rewrite interp_erase_guard, Mod.interp_state_tau.
      reflexivity.
  }
  assert (Hstuck : run_nd p hemp 0 ≅
    (stuck : ictreeW SObs (unit * SSig))).
  {
    unfold equ.
    coinduction R CIH.
    rewrite Hguard, unfold_stuck.
    constructor.
    exact CIH.
  }
  rewrite Hstuck.
  apply ag_stuck.
Qed.

Theorem rr_silent_loop_no_ag :
  ~ <( {run_rr (CUntilNone (CRet (Some tt : option unit))) hemp 0},
       Pure |= AG ⊤ )>.
Proof.
  set (p := CUntilNone (CRet (Some tt : option unit))).
  assert (Hraw : denote p ≅ Guard (denote p)).
  {
    unfold p, denote.
    etransitivity; [apply source_raw_until |].
    etransitivity; [apply source_raw_ret |].
    reflexivity.
  }
  assert (Hguard : run_rr p hemp 0 ≅ Guard (run_rr p hemp 0)).
  {
    unfold run_rr.
    etransitivity.
    - apply (interp_schedule_rr_equ sh 1 _ [Guard (denote p)]).
      apply SBisim.cons_pool_equ;
        [exact Hraw | apply SBisim.pool_equ_refl].
    - unfold interp_schedule_rr.
      rewrite unfold_run_round_robin,
        (schedule_focused_guard
          0 [Guard (denote p)] Fin.F1 (denote p) eq_refl).
      rewrite interp_erase_guard, Mod.interp_state_tau.
      reflexivity.
  }
  assert (Hstuck : run_rr p hemp 0 ≅
    (stuck : ictreeW SObs (unit * SSig))).
  {
    unfold equ.
    coinduction R CIH.
    rewrite Hguard, unfold_stuck.
    constructor.
    exact CIH.
  }
  rewrite Hstuck.
  apply ag_stuck.
Qed.

(** Termination, faults, immediate until matching, and physical deletion. *)

Lemma rr_ret_next_done :
  <[ {run_rr (CRet tt) hemp 0}, Pure |= AX done {fun _ _ => True} ]>.
Proof.
  unfold run_rr, denote.
  change (<[ {interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 :=
    (denote_flow (CRet tt) >>= fun _ => Ret tt))
    (Some Fin.F1) 0 (hemp,0)}, Pure |= AX done {fun _ _ => True} ]>).
  apply (proj2 (anr_csl_rr_ret 0 [Ret tt]%vector Fin.F1 tt
    (fun _ => Ret tt) 0 hemp 0 Pure _ _)).
  pose proof (interp_schedule_rr_ret sh 0 [Ret tt]%vector Fin.F1 0
    (hemp,0) eq_refl) as Hret.
  cbn in Hret.
  eapply (proj2 (@proper_entailsR_meq _ _ _ _ _ (sbisim eq) _
    (@KripkeSetoidSBisim _ _ _) _ _ _ Hret _ _ eq_refl)).
  eapply (proj2 (@proper_entailsR_meq _ _ _ _ _ (sbisim eq) _
    (@KripkeSetoidSBisim _ _ _) _ _ _
    (interp_schedule_rr_empty sh 0 (hemp,0)) _ _ eq_refl)).
  apply axr_ret; [constructor | exact I].
Qed.

Lemma rr_ret_no_prefix_next :
  ~ <( {run_rr (CRet tt) hemp 0}, Pure |= AX ⊤ )>.
Proof.
  unfold run_rr, denote.
  change (not <( {interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 :=
    (denote_flow (CRet tt) >>= fun _ => Ret tt))
    (Some Fin.F1) 0 (hemp,0)}, Pure |= AX ⊤ )>).
  rewrite anl_csl_rr_ret.
  intro H.
  apply (@anl_ret (writerE SObs) _ (unit * SSig) (tt,(hemp,0))
    Pure <[⊤]> <[⊤]>).
  eapply (proj1 (@proper_entailsL_meq _ _ _ _ _ (sbisim eq) _
    (@KripkeSetoidSBisim _ _ _) <(AX ⊤)> _ _
    (interp_schedule_rr_empty sh 0 (hemp,0)) _ _ eq_refl)).
  eapply (proj1 (@proper_entailsL_meq _ _ _ _ _ (sbisim eq) _
    (@KripkeSetoidSBisim _ _ _) <(AX ⊤)> _ _
    (interp_schedule_rr_ret sh 0 [Ret tt]%vector Fin.F1 0
      (hemp,0) eq_refl) _ _ eq_refl)).
  exact H.
Qed.

Lemma rr_ret_no_ag :
  ~ <( {run_rr (CRet tt) hemp 0}, Pure |= AG ⊤ )>.
Proof.
  unfold run_rr, denote.
  change (not <( {interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 :=
    (denote_flow (CRet tt) >>= fun _ => Ret tt))
    (Some Fin.F1) 0 (hemp,0)}, Pure |= AG ⊤ )>).
  rewrite ag_csl_rr_ret.
  intro H.
  apply (@ag_ret (writerE SObs) _ (unit * SSig) (tt,(hemp,0)) Pure <(⊤)>).
  eapply (proj1 (@proper_entailsL_meq _ _ _ _ _ (sbisim eq) _
    (@KripkeSetoidSBisim _ _ _) <(AG ⊤)> _ _
    (interp_schedule_rr_empty sh 0 (hemp,0)) _ _ eq_refl)).
  eapply (proj1 (@proper_entailsL_meq _ _ _ _ _ (sbisim eq) _
    (@KripkeSetoidSBisim _ _ _) <(AG ⊤)> _ _
    (interp_schedule_rr_ret sh 0 [Ret tt]%vector Fin.F1 0
      (hemp,0) eq_refl) _ _ eq_refl)).
  exact H.
Qed.


Lemma nd_fault_controls :
  (not <( {run_nd (CBind (CRead 1) (fun _ => CRet tt)) hemp 0}, Pure |= AX ⊤ )> /\
   not <( {run_nd (CBind (CRead 1) (fun _ => CRet tt)) hemp 0}, Pure |= AG ⊤ )>) /\
  (not <( {run_nd (CWrite 1 9) hemp 0}, Pure |= AX ⊤ )> /\
   not <( {run_nd (CWrite 1 9) hemp 0}, Pure |= AG ⊤ )>) /\
  (not <( {run_nd (CBind (CCAS 1 0 9) (fun _ => CRet tt)) hemp 0}, Pure |= AX ⊤ )> /\
   not <( {run_nd (CBind (CCAS 1 0 9) (fun _ => CRet tt)) hemp 0}, Pure |= AG ⊤ )>) /\
  (not <( {run_nd (CBind (CAlloc 0) (fun _ => CRet tt)) hemp 0}, Pure |= AX ⊤ )> /\
   not <( {run_nd (CBind (CAlloc 0) (fun _ => CRet tt)) hemp 0}, Pure |= AG ⊤ )>) /\
  (not <( {run_nd (CBind (CAlloc 1) (fun _ => CRet tt)) (fun _ => Some 7) 0}, Pure |= AX ⊤ )> /\
   not <( {run_nd (CBind (CAlloc 1) (fun _ => CRet tt)) (fun _ => Some 7) 0}, Pure |= AG ⊤ )>).
Proof.
  assert (Hcontrol : forall t : ictreeW SObs (unit * SSig), t ~ (stuck : ictreeW SObs (unit * SSig)) ->
    (not <( {t}, Pure |= AX ⊤ )> /\ not <( {t}, Pure |= AG ⊤ )>)).
  { intros t Hstuck; split; intro H.
    - apply (@anl_stuck (writerE SObs) _ (unit * SSig) Pure <(⊤)> <(⊤)>).
      exact (proj1 (@proper_entailsL_meq _ _ _ _ _ (sbisim eq) _
        (@KripkeSetoidSBisim _ _ _) <(AX ⊤)> _ _ Hstuck _ _ eq_refl) H).
    - apply (@ag_stuck (writerE SObs) _ (unit * SSig) Pure <(⊤)>).
      exact (proj1 (@proper_entailsL_meq _ _ _ _ _ (sbisim eq) _
        (@KripkeSetoidSBisim _ _ _) <(AG ⊤)> _ _ Hstuck _ _ eq_refl) H). }
  split; [apply Hcontrol |].
  - unfold run_nd, denote.
    change (interp_nd 1 ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CRead 1) (fun _ => CRet tt)) >>= fun _ => Ret tt))
      (Some Fin.F1) (hemp,0) ~ (stuck : ictreeW SObs (unit * SSig))).
    rewrite interp_nd_source_bind.
    apply interp_nd_source_read_missing; reflexivity.
  - split; [apply Hcontrol |].
    + unfold run_nd, denote.
      change (interp_nd 1 ([Ret tt]%vector @ Fin.F1 :=
        (denote_flow (CWrite 1 9) >>= fun _ => Ret tt))
        (Some Fin.F1) (hemp,0) ~ (stuck : ictreeW SObs (unit * SSig))).
      apply interp_nd_source_write_missing; reflexivity.
    + split; [apply Hcontrol |].
      * unfold run_nd, denote.
        change (interp_nd 1 ([Ret tt]%vector @ Fin.F1 :=
          (denote_flow (CBind (CCAS 1 0 9) (fun _ => CRet tt)) >>= fun _ => Ret tt))
          (Some Fin.F1) (hemp,0) ~ (stuck : ictreeW SObs (unit * SSig))).
        rewrite interp_nd_source_bind.
        apply interp_nd_source_cas_missing; reflexivity.
      * split; apply Hcontrol.
        -- unfold run_nd, denote.
           change (interp_nd 1 ([Ret tt]%vector @ Fin.F1 :=
             (denote_flow (CBind (CAlloc 0) (fun _ => CRet tt)) >>= fun _ => Ret tt))
             (Some Fin.F1) (hemp,0) ~ (stuck : ictreeW SObs (unit * SSig))).
           rewrite interp_nd_source_bind.
           apply interp_nd_source_alloc_zero.
        -- unfold run_nd, denote.
           change (interp_nd 1 ([Ret tt]%vector @ Fin.F1 :=
             (denote_flow (CBind (CAlloc 1) (fun _ => CRet tt)) >>= fun _ => Ret tt))
             (Some Fin.F1) ((fun _ => Some 7),0) ~ (stuck : ictreeW SObs (unit * SSig))).
           rewrite interp_nd_source_bind.
           apply interp_nd_source_alloc_no_space; [lia |].
           intros base Positive Free.
           specialize (Free 0 ltac:(lia)); discriminate.
Qed.

Lemma rr_fault_controls :
  (not <( {run_rr (CBind (CRead 1) (fun _ => CRet tt)) hemp 0}, Pure |= AX ⊤ )> /\
   not <( {run_rr (CBind (CRead 1) (fun _ => CRet tt)) hemp 0}, Pure |= AG ⊤ )>) /\
  (not <( {run_rr (CWrite 1 9) hemp 0}, Pure |= AX ⊤ )> /\
   not <( {run_rr (CWrite 1 9) hemp 0}, Pure |= AG ⊤ )>) /\
  (not <( {run_rr (CBind (CCAS 1 0 9) (fun _ => CRet tt)) hemp 0}, Pure |= AX ⊤ )> /\
   not <( {run_rr (CBind (CCAS 1 0 9) (fun _ => CRet tt)) hemp 0}, Pure |= AG ⊤ )>) /\
  (not <( {run_rr (CBind (CAlloc 0) (fun _ => CRet tt)) hemp 0}, Pure |= AX ⊤ )> /\
   not <( {run_rr (CBind (CAlloc 0) (fun _ => CRet tt)) hemp 0}, Pure |= AG ⊤ )>) /\
  (not <( {run_rr (CBind (CAlloc 1) (fun _ => CRet tt)) (fun _ => Some 7) 0}, Pure |= AX ⊤ )> /\
   not <( {run_rr (CBind (CAlloc 1) (fun _ => CRet tt)) (fun _ => Some 7) 0}, Pure |= AG ⊤ )>).
Proof.
  assert (Hcontrol : forall t : ictreeW SObs (unit * SSig), t ~ (stuck : ictreeW SObs (unit * SSig)) ->
    (not <( {t}, Pure |= AX ⊤ )> /\ not <( {t}, Pure |= AG ⊤ )>)).
  { intros t Hstuck; split; intro H.
    - apply (@anl_stuck (writerE SObs) _ (unit * SSig) Pure <(⊤)> <(⊤)>).
      exact (proj1 (@proper_entailsL_meq _ _ _ _ _ (sbisim eq) _
        (@KripkeSetoidSBisim _ _ _) <(AX ⊤)> _ _ Hstuck _ _ eq_refl) H).
    - apply (@ag_stuck (writerE SObs) _ (unit * SSig) Pure <(⊤)>).
      exact (proj1 (@proper_entailsL_meq _ _ _ _ _ (sbisim eq) _
        (@KripkeSetoidSBisim _ _ _) <(AG ⊤)> _ _ Hstuck _ _ eq_refl) H). }
  split; [apply Hcontrol |].
  - unfold run_rr, denote.
    change (interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CRead 1) (fun _ => CRet tt)) >>= fun _ => Ret tt))
      (Some Fin.F1) 0 (hemp,0) ~ (stuck : ictreeW SObs (unit * SSig))).
    rewrite interp_rr_bind.
    apply interp_rr_read_missing; reflexivity.
  - split; [apply Hcontrol |].
    + unfold run_rr, denote.
      change (interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 :=
        (denote_flow (CWrite 1 9) >>= fun _ => Ret tt))
        (Some Fin.F1) 0 (hemp,0) ~ (stuck : ictreeW SObs (unit * SSig))).
      apply interp_rr_write_missing; reflexivity.
    + split; [apply Hcontrol |].
      * unfold run_rr, denote.
        change (interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 :=
          (denote_flow (CBind (CCAS 1 0 9) (fun _ => CRet tt)) >>= fun _ => Ret tt))
          (Some Fin.F1) 0 (hemp,0) ~ (stuck : ictreeW SObs (unit * SSig))).
        rewrite interp_rr_bind.
        apply interp_rr_cas_missing; reflexivity.
      * split; apply Hcontrol.
        -- unfold run_rr, denote.
           change (interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 :=
             (denote_flow (CBind (CAlloc 0) (fun _ => CRet tt)) >>= fun _ => Ret tt))
             (Some Fin.F1) 0 (hemp,0) ~ (stuck : ictreeW SObs (unit * SSig))).
           rewrite interp_rr_bind.
           apply interp_rr_alloc_zero.
        -- unfold run_rr, denote.
           change (interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 :=
             (denote_flow (CBind (CAlloc 1) (fun _ => CRet tt)) >>= fun _ => Ret tt))
             (Some Fin.F1) 0 ((fun _ => Some 7),0) ~ (stuck : ictreeW SObs (unit * SSig))).
           rewrite interp_rr_bind.
           apply interp_rr_alloc_no_space; [lia |].
           intros base Positive Free.
           specialize (Free 0 ltac:(lia)); discriminate.
Qed.

Lemma nd_stuck_until_now :
  <( {run_nd (CBind (CRead 1) (fun _ => CRet tt)) hemp 0}, Pure |= ⊤ AU pure )>.
Proof.
  cleft. apply ticll_pure; reflexivity.
Qed.

Lemma rr_stuck_until_now :
  <( {run_rr (CBind (CRead 1) (fun _ => CRet tt)) hemp 0}, Pure |= ⊤ AU pure )>.
Proof.
  cleft. apply ticll_pure; reflexivity.
Qed.


Lemma nd_heap_free_next_done :
  <[ {interp_nd 1 [heap_free (E:=CEff) 1;; Ret tt]%vector
       (Some Fin.F1) (Pcm.hsingle 1 9,7)}, Pure |=
     AX done {fun r w => snd (snd r) = 7 /\
       heq (fst (snd r)) (Pcm.hfree 1 (Pcm.hsingle 1 9)) /\ w = Pure} ]>.
Proof.
  change (<[ {interp_nd 1 ([Ret tt]%vector @ Fin.F1 :=
    (heap_free (E:=CEff) 1 >>= fun _ => Ret tt))
    (Some Fin.F1) (Pcm.hsingle 1 9,7)}, Pure |=
    AX done {fun r w => snd (snd r) = 7 /\
      heq (fst (snd r)) (Pcm.hfree 1 (Pcm.hsingle 1 9)) /\ w = Pure} ]>).
  apply (proj2 (anr_csl_nd_heap_free 0 [Ret tt]%vector Fin.F1 1
    (fun _ => Ret tt) (Pcm.hsingle 1 9) 7 Pure _ _)).
  eapply (proj2 (@proper_entailsR_meq _ _ _ _ _ (sbisim eq) _
    (@KripkeSetoidSBisim _ _ _) _ _ _
    (interp_nd_ret 0 [Ret tt]%vector Fin.F1
      (Pcm.hfree 1 (Pcm.hsingle 1 9),7) eq_refl) _ _ eq_refl)).
  eapply (proj2 (@proper_entailsR_meq _ _ _ _ _ (sbisim eq) _
    (@KripkeSetoidSBisim _ _ _) _ _ _
    (interp_nd_empty (Pcm.hfree 1 (Pcm.hsingle 1 9),7)) _ _ eq_refl)).
  apply axr_ret; [constructor |].
  split; [reflexivity |]. split; [apply heq_refl | reflexivity].
Qed.

Lemma rr_heap_free_next_done :
  <[ {interp_schedule_rr sh 1 [heap_free (E:=CEff) 1;; Ret tt]%vector
       (Some Fin.F1) 0 (Pcm.hsingle 1 9,7)}, Pure |=
     AX done {fun r w => snd (snd r) = 7 /\
       heq (fst (snd r)) (Pcm.hfree 1 (Pcm.hsingle 1 9)) /\ w = Pure} ]>.
Proof.
  change (<[ {interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 :=
    (heap_free (E:=CEff) 1 >>= fun _ => Ret tt))
    (Some Fin.F1) 0 (Pcm.hsingle 1 9,7)}, Pure |=
    AX done {fun r w => snd (snd r) = 7 /\
      heq (fst (snd r)) (Pcm.hfree 1 (Pcm.hsingle 1 9)) /\ w = Pure} ]>).
  apply (proj2 (anr_csl_rr_heap_free 0 [Ret tt]%vector Fin.F1 1
    (fun _ => Ret tt) 0 (Pcm.hsingle 1 9) 7 Pure _ _)).
  eapply (proj2 (@proper_entailsR_meq _ _ _ _ _ (sbisim eq) _
    (@KripkeSetoidSBisim _ _ _) _ _ _
    (interp_schedule_rr_ret sh 0 [Ret tt]%vector Fin.F1 0
      (Pcm.hfree 1 (Pcm.hsingle 1 9),7) eq_refl) _ _ eq_refl)).
  eapply (proj2 (@proper_entailsR_meq _ _ _ _ _ (sbisim eq) _
    (@KripkeSetoidSBisim _ _ _) _ _ _
    (interp_schedule_rr_empty sh 0 (Pcm.hfree 1 (Pcm.hsingle 1 9),7)) _ _ eq_refl)).
  apply axr_ret; [constructor |].
  split; [reflexivity |]. split; [apply heq_refl | reflexivity].
Qed.
