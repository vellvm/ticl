(** * Scheduler-generic fairness for yielding pools.

    The policy runner [interp_schedule_fair] ([Policy.v]) logs a
    [Scheduled i] event at every pick of the [Scheduler] record driving it.
    Fairness is a property of the policy's own pick stream ([FairScheduler]);
    the pool rules at the end conclude [AG (AF _)] on the instrumented runner
    for any fair policy from an invariant, a well-founded rank and a helpful
    slot. *)

From Stdlib Require Import List Arith.PeanoNat Lia Fin Vector Morphisms
  Program.Equality Wellfounded.Inverse_Image.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Events.Writer
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.Policy
  CTree.Interp.Yield.Segments
  CTree.Interp.Yield.Sequential
  CTree.Interp.Yield.Execution
  CTree.Interp.State.Mod
  CTree.Trace
  CTree.Logic.Trans
  CTree.Logic.AG
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.Bind
  CTree.Logic.Trace
  CTree.Logic.CanStep
  CTree.Logic.State
  Logic.Core
  Utils.Vectors.

Import CTreeNotations TiclNotations CoindNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

Generalizable All Variables.

(** * Policy traces and fairness *)

(** The policy's own pick stream for a live pool of size [S n]. *)
CoFixpoint sched_trace (sch : Scheduler) (n : nat) (st : sched_state sch) : ctreeW nat Bn unit :=
  Br (branchn (S (sched_arity sch n st))) (fun a =>
    Vis (Log (slot_index (fst (sched_pick sch n st a))))
      (fun _ => sched_trace sch n (snd (sched_pick sch n st a)))).

Lemma unfold_sched_trace sch n st :
  sched_trace sch n st ≅
  Br (branchn (S (sched_arity sch n st))) (fun a =>
    Vis (Log (slot_index (fst (sched_pick sch n st a))))
      (fun _ => sched_trace sch n (snd (sched_pick sch n st a)))).
Proof. step; now cbn. Qed.

(** Fairness: from every policy state, every slot of a fixed-size pool is
    picked again and again. *)
Class FairScheduler (sch : Scheduler) : Prop :=
  fair_scheduled : forall n (i : Fin.t (S n)) (st : sched_state sch) (w : World (writerE nat)),
    not_done w ->
    <( {sched_trace sch n st}, w |= AG (AF visW {eq (slot_index i)}) )>.

(** Induction-friendly witness: along every alternative that avoids slot
    [i], slot [i] is still picked after finitely many scheduling points. *)
Inductive EventuallyPicks (sch : Scheduler) (n : nat) (i : Fin.t (S n)) : sched_state sch -> Prop :=
| ep_intro st :
    (forall a, fst (sched_pick sch n st a) <> i ->
               EventuallyPicks sch n i (snd (sched_pick sch n st a))) ->
    EventuallyPicks sch n i st.

Section FairBridge.
  Context (sch : Scheduler) (n : nat) (i : Fin.t (S n)).

  Lemma eventually_picks_af st w :
    EventuallyPicks sch n i st -> not_done w ->
    <( {sched_trace sch n st}, w |= AF visW {eq (slot_index i)} )>.
  Proof.
    intro Hep; revert w; induction Hep as [st Hst IH]; intros w Hw.
    rewrite unfold_sched_trace.
    apply aul_br; [apply ticll_top; exact Hw|exists Fin.F1; apply can_step_vis; [exact tt|exact Hw]|].
    intros a t' w' TR.
    apply ktrans_vis in TR as ([] & -> & Heq & _); rewrite <- Heq.
    destruct (Fin.eq_dec (fst (sched_pick sch n st a)) i) as [Hpick|Hne].
    - cleft; apply ticll_vis; constructor; rewrite Hpick; reflexivity.
    - apply IH; [exact Hne|constructor].
  Qed.

  Lemma af_trace_eventually_picks :
    forall (t : ctreeW nat Bn unit) w,
      <( t, w |= AF visW {eq (slot_index i)} )> ->
      forall st, t ≅ sched_trace sch n st ->
      w <> Obs (Log (slot_index i)) tt ->
      EventuallyPicks sch n i st.
  Proof.
    intros t w H.
    cinduction H; intros st Et Hw.
    - exfalso; apply Hw.
      apply ticll_vis in Hp; inversion Hp as [Y e v Hv Ew]; clear Hp.
      destruct e as [k]; destruct v; cbn in Hv; subst; reflexivity.
    - constructor; intros a Hne.
      apply ticll_not_done in Hp.
      apply (HInd (sched_trace sch n (snd (sched_pick sch n st a)))
        (Obs (Log (slot_index (fst (sched_pick sch n st a)))) tt)).
      + rewrite Et, unfold_sched_trace; apply ktrans_br; exists a.
        apply ktrans_vis; exists tt; split; [reflexivity|split; [reflexivity|exact Hp]].
      + reflexivity.
      + intro Ew; apply Hne, Fin.to_nat_inj.
        injection Ew as Ek; exact Ek.
  Qed.

  Lemma fair_eventually_picks `{FairScheduler sch} st : EventuallyPicks sch n i st.
  Proof.
    pose proof (fair_scheduled n i st Pure ltac:(constructor)) as Hag.
    cdestruct Hag.
    apply (af_trace_eventually_picks _ Pure Hp st); [reflexivity|discriminate].
  Qed.
End FairBridge.

(** Any policy whose picks are inductively fair is a [FairScheduler]. *)
Lemma eventually_picks_fair (sch : Scheduler) :
  (forall n (i : Fin.t (S n)) st, EventuallyPicks sch n i st) -> FairScheduler sch.
Proof.
  intros Hep n i.
  coinduction R CIH; intros st w Hw.
  split; [apply eventually_picks_af; [apply Hep|exact Hw]|].
  split.
  - rewrite unfold_sched_trace; apply can_step_br; exists Fin.F1.
    apply can_step_vis; [exact tt|exact Hw].
  - intros t' w' TR.
    rewrite unfold_sched_trace in TR.
    apply ktrans_br in TR as (a & TR).
    apply ktrans_vis in TR as ([] & -> & Heq & _); rewrite <- Heq.
    apply CIH; constructor.
Qed.

Lemma rr_eventually_picks n (i : Fin.t (S n)) : forall m, EventuallyPicks rr_scheduler n i m.
Proof.
  assert (Hk : forall k m, (m + k) mod S n = slot_index i -> EventuallyPicks rr_scheduler n i m).
  { induction k as [|k IH]; intros m Hm; constructor; intros a Hne;
      cbn [sched_pick rr_scheduler fst snd] in *.
    - exfalso; apply Hne, Fin.to_nat_inj; unfold rr_pick; rewrite Fin.to_nat_of_nat; cbn [proj1_sig].
      rewrite Nat.add_0_r in Hm; exact Hm.
    - apply IH; rewrite <- Hm; f_equal; lia. }
  intro m; apply (Hk (S n - m mod S n + slot_index i)).
  pose proof (Nat.div_mod m (S n) (Nat.neq_succ_0 n)) as Hdm.
  pose proof (Nat.mod_upper_bound m (S n) (Nat.neq_succ_0 n)) as Hub.
  pose proof (proj2_sig (Fin.to_nat i)) as Hi; unfold slot_index in *.
  replace (m + (S n - m mod S n + proj1_sig (Fin.to_nat i)))
    with (proj1_sig (Fin.to_nat i) + (m / S n + 1) * S n) by lia.
  rewrite Nat.Div0.mod_add, Nat.mod_small; [reflexivity|exact Hi].
Qed.

#[global] Instance rr_fair : FairScheduler rr_scheduler :=
  eventually_picks_fair rr_scheduler (fun n i => rr_eventually_picks n i).

(** * Nondeterministic selection is not fair

    With two or more slots, the alternative that picks another slot leads
    back to the same stateless scheduling point, so no finite witness that
    slot [i] is eventually picked exists. *)
Lemma nd_not_eventually_picks n (i : Fin.t (S (S n))) st :
  ~ EventuallyPicks nd_scheduler (S n) i st.
Proof.
  intro Hep; induction Hep as [st _ IH]; cbn [sched_pick nd_scheduler fst snd] in IH.
  destruct (Fin.eq_dec i Fin.F1) as [->|Hne].
  - exact (IH (Fin.FS Fin.F1) ltac:(discriminate)).
  - exact (IH Fin.F1 (fun E => Hne (eq_sym E))).
Qed.

(** Hence no [FairScheduler nd_scheduler] instance exists: fairness would
    yield the inductive witness for slot [Fin.F1] of a two-slot pool. *)
Lemma nd_not_fair : ~ FairScheduler nd_scheduler.
Proof.
  intro Hfair.
  exact (nd_not_eventually_picks 0 Fin.F1 tt (fair_eventually_picks nd_scheduler 1 Fin.F1 tt)).
Qed.

(** * Inversion rules: invariant, well-founded rank, helpful slot.

    The certificate is the Manna–Pnueli response rule under justice: a turn
    either reaches the goal, or strictly decreases the rank, or is taken by a
    non-helpful slot and changes neither rank nor helpful slot.  Fairness of
    the policy guarantees that the helpful slot is eventually picked.  The
    pool text is part of the invariant: threads may change code at turn
    boundaries (program-counter residuals as in allocator pools). *)
Section PoolRulesFair.
  Context {E : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W Bn)) (sch : Scheduler) {n : nat}.

  Abbreviation exactW := (fun X (t u : ctreeW W Bn X) => t ≅ u).
  #[local] Abbreviation fair := (interp_schedule_fair sch handler (S n)).

  Record FairCertificate {G V : Type}
      (Inv : G -> pool E Bn (S n) -> Sigma -> Prop)
      (rank : G -> V) (ltV : V -> V -> Prop)
      (target : G -> Fin.t (S n)) (P : W -> Prop) : Prop := {
    fair_wf : well_founded ltV;
    fair_turn : forall g ts sigma (j : Fin.t (S n)), Inv g ts sigma ->
      exists g' logs residual sigma',
        ThreadSegment handler exactW (ts $ j) sigma logs residual sigma' /\
        Inv g' (ts @ j := residual) sigma' /\
        (List.Exists P logs \/
         ltV (rank g') (rank g) \/
         (j <> target g /\ rank g' = rank g /\ target g' = target g))
  }.
  Arguments fair_wf {G V Inv rank ltV target P} _.
  Arguments fair_turn {G V Inv rank ltV target P} _ g ts sigma j _.

  (** Closed turns alone, for the [AG] half. *)
  Definition ClosedPool {G} (Inv : G -> pool E Bn (S n) -> Sigma -> Prop) : Prop :=
    forall g ts sigma (j : Fin.t (S n)), Inv g ts sigma ->
      exists g' logs residual sigma',
        ThreadSegment handler exactW (ts $ j) sigma logs residual sigma' /\
        Inv g' (ts @ j := residual) sigma'.

  Lemma fair_certificate_closed {G V} Inv rank ltV target P :
    @FairCertificate G V Inv rank ltV target P -> ClosedPool Inv.
  Proof.
    intros Hc g ts sigma j Hinv.
    destruct (fair_turn Hc g ts sigma j Hinv) as (g' & logs & residual & sigma' & Hseg & Hinv' & _).
    exists g', logs, residual, sigma'; split; assumption.
  Qed.

  (** ** The [AG] half: closed turns keep [φ] invariant on the fair runner. *)
  Lemma ag_pool_fair_invariance {G} (Inv : G -> pool E Bn (S n) -> Sigma -> Prop)
      (φ : ticllW (W + nat)) :
    ClosedPool Inv ->
    (forall (o : W) (t : ctreeW (W + nat) Bn (Sigma * unit)) w, not_done w ->
       <( t, {Obs (Log (inl o)) tt} |= φ )> -> <( {Vis (Log (inl o)) (fun _ => t)}, w |= φ )>) ->
    (forall g ts sigma st w, Inv g ts sigma -> not_done w ->
       <( {fair ts None st sigma}, w |= φ )>) ->
    forall g ts sigma focus st w, Inv g ts sigma -> not_done w ->
      <( {fair ts focus st sigma}, w |= AG φ )>.
  Proof.
    intros Hclosed Hlog Hφ.
    assert (Hpref : forall xs (t : ctreeW (W + nat) Bn (Sigma * unit)),
      (forall w, not_done w -> <( t, w |= φ )>) ->
      forall w, not_done w -> <( {emit_list (List.map inl xs) t}, w |= φ )>).
    { induction xs as [|o xs IH]; intros t Ht w Hw; [apply Ht, Hw|].
      cbn [List.map]; rewrite emit_list_cons.
      apply Hlog; [exact Hw|]; apply IH; [exact Ht|constructor]. }
    coinduction R CIH; intros g ts sigma focus st w Hinv Hw.
    assert (Hnone : forall g ts sigma st w, Inv g ts sigma -> not_done w ->
      agcF (entailsL (Sigma * unit) φ) (elem R) (fair ts None st sigma) w).
    { clear g ts sigma focus st w Hinv Hw; intros g ts sigma st w Hinv Hw.
      pose proof (Hφ g ts sigma st w Hinv Hw) as Hnow.
      rewrite interp_schedule_fair_select in Hnow |- *.
      split; [exact Hnow|]; split.
      - apply can_step_br_alts; exists Fin.F1; apply can_step_vis; [exact tt|exact Hw].
      - intros t' w' Htr.
        apply ktrans_br_alts in Htr as (a & Htr).
        apply ktrans_vis in Htr as ([] & -> & Heq & _); rewrite <- Heq.
        apply (CIH g ts sigma (Some _)); [exact Hinv|constructor]. }
    destruct focus as [i|]; [|apply (Hnone g ts sigma st w Hinv Hw)].
    destruct (Hclosed g ts sigma i Hinv) as (g' & logs & residual & sigma' & Hseg & Hinv').
    rewrite (segment_interp_fair sch handler exactW (fun X t u => equ_sbisim t u)
      n ts i st sigma logs residual sigma' Hseg).
    clear Hseg; revert w Hw.
    induction logs as [|o logs IH]; intros w Hw.
    { cbn [List.map emit_list List.fold_right]; apply (Hnone g' _ sigma' st w Hinv' Hw). }
    cbn [List.map]; rewrite emit_list_cons.
    split; [|split].
    - apply Hlog; [exact Hw|].
      apply Hpref; [|constructor].
      intros w'' Hw''; apply (Hφ g'); [exact Hinv'|exact Hw''].
    - apply can_step_vis; [exact tt|exact Hw].
    - intros t' w' Htr.
      apply ktrans_vis in Htr as ([] & -> & Heq & _); rewrite <- Heq.
      apply (b_chain R), IH; constructor.
  Qed.

  (** ** The [AF] half: the helpful slot is eventually picked, and every turn
      makes progress toward the goal or leaves the rank alone. *)
  Lemma aul_pool_fair_eventually `{FairScheduler sch} {G V} Inv rank ltV target P :
    @FairCertificate G V Inv rank ltV target P ->
    forall g ts sigma focus st w, Inv g ts sigma -> not_done w ->
      <( {fair ts focus st sigma}, w |= AF visW {fair_obs P} )>.
  Proof.
    intros Hcert g.
    induction g as [g IHrank] using
      (well_founded_induction (wf_inverse_image G V ltV rank (fair_wf Hcert))).
    intros ts sigma focus st w Hinv Hw.
    (* A turn of the helpful slot: a hit or a strict rank drop. *)
    assert (Htarget : forall g0 ts sigma st w,
      Inv g0 ts sigma -> rank g0 = rank g -> target g0 = target g -> not_done w ->
      <( {fair ts (Some (target g)) st sigma}, w |= AF visW {fair_obs P} )>).
    { intros g0 ts0 sigma0 st0 w0 Hinv0 Hrank Htgt Hw0.
      destruct (fair_turn Hcert g0 ts0 sigma0 (target g) Hinv0)
        as (g' & logs & residual & sigma' & Hseg & Hinv' & [HP|[Hlt|(Hne & _)]]);
        [| |exfalso; apply Hne; symmetry; exact Htgt];
        rewrite (segment_interp_fair sch handler exactW (fun X t u => equ_sbisim t u)
          n ts0 _ st0 sigma0 logs residual sigma' Hseg).
      - apply List.Exists_exists in HP as (o & Hin & HP).
        eapply af_emit_list_member with (o := inl o);
          [exact Hw0|apply List.in_map; exact Hin|exact HP].
      - apply af_emit_list with (xs := List.map inl logs); [exact Hw0|].
        apply (IHrank g'); [rewrite <- Hrank; exact Hlt|exact Hinv'|].
        apply after_logs_not_done; exact Hw0. }
    (* Until the helpful slot is picked, the rank is preserved. *)
    assert (Hinner : forall st, EventuallyPicks sch n (target g) st ->
      forall g0 ts sigma focus w,
        Inv g0 ts sigma -> rank g0 = rank g -> target g0 = target g -> not_done w ->
        <( {fair ts focus st sigma}, w |= AF visW {fair_obs P} )>).
    { intros st0 Hep; induction Hep as [st0 Hst0 IH].
      assert (Hnone : forall g0 ts sigma w,
        Inv g0 ts sigma -> rank g0 = rank g -> target g0 = target g -> not_done w ->
        <( {fair ts None st0 sigma}, w |= AF visW {fair_obs P} )>).
      { intros g0 ts0 sigma0 w0 Hinv0 Hrank Htgt Hw0.
        rewrite interp_schedule_fair_select.
        apply aul_br_alts; [apply ticll_top; exact Hw0|exists Fin.F1; apply can_step_vis; [exact tt|exact Hw0]|].
        intros a t' w' TR.
        apply ktrans_vis in TR as ([] & -> & Heq & _); rewrite <- Heq.
        destruct (Fin.eq_dec (fst (sched_pick sch n st0 a)) (target g)) as [Hj|Hj].
        - rewrite Hj; apply (Htarget g0); [exact Hinv0|exact Hrank|exact Htgt|constructor].
        - apply (IH a Hj g0); [exact Hinv0|exact Hrank|exact Htgt|constructor]. }
      intros g0 ts0 sigma0 [j|] w0 Hinv0 Hrank Htgt Hw0; [|apply (Hnone g0); assumption].
      destruct (fair_turn Hcert g0 ts0 sigma0 j Hinv0)
        as (g' & logs & residual & sigma' & Hseg & Hinv' & [HP|[Hlt|(Hne & Hrank' & Htgt')]]);
        rewrite (segment_interp_fair sch handler exactW (fun X t u => equ_sbisim t u)
          n ts0 j st0 sigma0 logs residual sigma' Hseg).
      - apply List.Exists_exists in HP as (o & Hin & HP).
        eapply af_emit_list_member with (o := inl o);
          [exact Hw0|apply List.in_map; exact Hin|exact HP].
      - apply af_emit_list with (xs := List.map inl logs); [exact Hw0|].
        apply (IHrank g'); [rewrite <- Hrank; exact Hlt|exact Hinv'|].
        apply after_logs_not_done; exact Hw0.
      - apply af_emit_list with (xs := List.map inl logs); [exact Hw0|].
        apply (Hnone g'); [exact Hinv'|congruence|congruence|].
        apply after_logs_not_done; exact Hw0. }
    apply (Hinner st (fair_eventually_picks sch n (target g) st) g);
      [exact Hinv|reflexivity|reflexivity|exact Hw].
  Qed.

  (** The fairness inversion rule: witnesses are an invariant, a well-founded
      rank and a helpful slot. *)
  Theorem agaf_pool_fair `{FairScheduler sch} {G V} Inv rank ltV target P :
    @FairCertificate G V Inv rank ltV target P ->
    forall g ts sigma focus st w, Inv g ts sigma -> not_done w ->
      <( {fair ts focus st sigma}, w |= AG (AF visW {fair_obs P}) )>.
  Proof.
    intro Hcert.
    apply ag_pool_fair_invariance.
    - exact (fair_certificate_closed _ _ _ _ _ Hcert).
    - intros o t w Hw Ht; apply (aul_vis _ _ tt); right; split;
        [apply ticll_top; exact Hw|intros []; exact Ht].
    - intros g ts sigma st w Hinv Hw.
      apply (aul_pool_fair_eventually _ _ _ _ _ Hcert g ts sigma None st w Hinv Hw).
  Qed.

  (** ** Fixed pool text, one log per turn, constant helpful slot. *)
  Definition FairTurns {G V} (ts : pool E Bn (S n)) (i : Fin.t (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V) (ltV : V -> V -> Prop) (P : W -> Prop) : Prop :=
    forall g sigma (j : Fin.t (S n)), Inv g sigma ->
    exists g' sigma' o,
      segment_to handler exactW (ts $ j) sigma (List.cons o List.nil) (ts $ j) sigma' /\
      Inv g' sigma' /\
      (P o \/ ltV (rank g') (rank g) \/ (j <> i /\ rank g' = rank g)).

  Theorem agaf_fair_turns `{FairScheduler sch} {G V} ts i Inv rank ltV P :
    well_founded ltV -> @FairTurns G V ts i Inv rank ltV P ->
    forall g sigma focus st w, Inv g sigma -> not_done w ->
      <( {fair ts focus st sigma}, w |= AG (AF visW {fair_obs P}) )>.
  Proof.
    intros Hwf Hturns g sigma focus st w Hinv Hw.
    refine (agaf_pool_fair (fun g ts' σ => Inv g σ /\ pool_guard_equ ts' ts) rank ltV (fun _ => i) P
      _ g ts sigma focus st w (conj Hinv (fun j => guard_equ_equ _ _ (reflexivity _))) Hw).
    constructor; [exact Hwf|].
    intros g0 ts' σ j (Hinv0 & Hpool).
    destruct (Hturns g0 σ j Hinv0) as (g' & σ' & o & (residual & Hseg & Htail) & Hinv' & Hcase).
    apply (proj2 (guard_equ_segment_iff handler exactW (ts' $ j) (ts $ j) (Hpool j)
      σ (List.cons o List.nil) residual σ')) in Hseg.
    exists g', (List.cons o List.nil), residual, σ'; split; [exact Hseg|]; split.
    - split; [exact Hinv'|].
      intro k; destruct (Fin.eq_dec k j) as [->|Hne].
      + rewrite Vector.nth_replace_eq; exact Htail.
      + rewrite Vector.nth_replace_neq by congruence; apply Hpool.
    - destruct Hcase as [HP|[Hlt|(Hne & Hrank)]];
        [left; constructor; exact HP|right; left; exact Hlt|right; right; auto].
  Qed.

  (** ** Abstract-model clients: ghost data projects to model states. *)
  Theorem agaf_pool_simulation_fair `{FairScheduler sch} {St Act G V}
      (actor : Fin.t (S n) -> Act) (slot : Act -> Fin.t (S n))
      (slot_actor : forall i, slot (actor i) = i)
      (step : Act -> St -> option (St * option W)) (pool_of : St -> pool E Bn (S n))
      (agree : Sigma -> St -> Prop) (Inv : St -> Prop)
      (Hsim : PoolSimulation n handler slot step pool_of agree Inv)
      (st_of : G -> St) (InvG : G -> Prop) (rank : G -> V) (ltV : V -> V -> Prop)
      (target : G -> Fin.t (S n)) (P : W -> Prop) :
    well_founded ltV ->
    (forall g, InvG g -> Inv (st_of g)) ->
    (forall g who s' event, InvG g -> step who (st_of g) = Some (s', event) ->
       exists g', st_of g' = s' /\ InvG g' /\
         ((exists o, event = Some o /\ P o) \/ ltV (rank g') (rank g) \/
          (slot who <> target g /\ rank g' = rank g /\ target g' = target g))) ->
    forall g ts sigma focus st w,
      InvG g -> agree sigma (st_of g) -> pool_guard_equ ts (pool_of (st_of g)) -> not_done w ->
      <( {fair ts focus st sigma}, w |= AG (AF visW {fair_obs P}) )>.
  Proof.
    intros Hwf HInv Hturn g ts sigma focus st w Hg Hagree Hpool Hw.
    refine (agaf_pool_fair
      (fun g ts σ => InvG g /\ agree σ (st_of g) /\ pool_guard_equ ts (pool_of (st_of g)))
      rank ltV target P _ g ts sigma focus st w (conj Hg (conj Hagree Hpool)) Hw).
    constructor; [exact Hwf|].
    intros g0 ts0 σ j (Hg0 & Hagree0 & Hpool0).
    destruct (simulation_total Hsim (actor j) (st_of g0) (HInv g0 Hg0)) as (s' & event & Hstep & _).
    destruct (Hturn g0 (actor j) s' event Hg0 Hstep) as (g' & Es' & Hg' & Hcase).
    destruct (selected_turn_segment Hsim ts0 (st_of g0) (actor j) s' event σ
      (HInv g0 Hg0) Hagree0 Hpool0 Hstep) as (residual & σ' & Hseg & Hagree' & Hpool').
    rewrite slot_actor in Hseg, Hpool', Hcase.
    exists g', (event_obs event), residual, σ'; split; [exact Hseg|]; split.
    - split; [exact Hg'|rewrite Es'; split; assumption].
    - destruct Hcase as [(o & -> & HP)|Hcase]; [left; constructor; exact HP|right; exact Hcase].
  Qed.
End PoolRulesFair.
