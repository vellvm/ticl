(** * Scheduler-generic fairness for yielding pools.

    The direct policy scheduler logs one selected-slot observation per turn.
    User logs are relabelled into the program side of [W + nat]; selections
    occupy the other side. Fairness is a property of the policy's own pick
    stream, conditional on reaching cooperative scheduling boundaries. *)

From Stdlib Require Import List Arith.PeanoNat Lia Fin Vector Morphisms
  Program.Equality Wellfounded.Inverse_Image Eqdep.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Events.Writer
  CTree.Interp.Yield.Policy
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
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


(** Raw handler equations remain valid after relabelling. *)
Lemma relabel_equ_sb {W X} (t u : ctreeW W Bn X) :
  t ≅ u -> translate relabel_log t ~ translate relabel_log u.
Proof. intro Eq; rewrite Eq; reflexivity. Qed.

(** * Policy traces and fairness *)

(** The policy's own pick stream for a live pool of size [S n]. *)
CoFixpoint sched_trace (sch : Scheduler) (n : nat) (st : sched_state sch) : ctreeW nat Bn unit :=
  match sched_arity sch n st as a return
    (Fin.t (S a) -> Fin.t (S n) * sched_state sch) -> ctreeW nat Bn unit with
  | 0 => fun pick => let '(i, st') := pick Fin.F1 in
      Vis (Log (slot_index i)) (fun _ => sched_trace sch n st')
  | S a => fun pick => Br (branchn (S (S a))) (fun x =>
      let '(i, st') := pick x in
      Vis (Log (slot_index i)) (fun _ => sched_trace sch n st'))
  end (sched_pick sch n st).

Lemma unfold_sched_trace sch n st :
  sched_trace sch n st ≅
  match sched_arity sch n st as a return
    (Fin.t (S a) -> Fin.t (S n) * sched_state sch) -> ctreeW nat Bn unit with
  | 0 => fun pick => let '(i, st') := pick Fin.F1 in
      Vis (Log (slot_index i)) (fun _ => sched_trace sch n st')
  | S a => fun pick => Br (branchn (S (S a))) (fun x =>
      let '(i, st') := pick x in
      Vis (Log (slot_index i)) (fun _ => sched_trace sch n st'))
  end (sched_pick sch n st).
Proof. step; cbn; reflexivity. Qed.

Lemma sched_trace_select sch n st :
  sched_trace sch n st ~
  Br (branchn (S (sched_arity sch n st))) (fun a =>
    Vis (Log (slot_index (fst (sched_pick sch n st a))))
      (fun _ => sched_trace sch n (snd (sched_pick sch n st a)))).
Proof.
  rewrite unfold_sched_trace.
  generalize (sched_pick sch n st); destruct (sched_arity sch n st) as [|a]; intro pick.
  - symmetry; apply sb_br_l with (y:=Fin.F1); intro i.
    assert (Hi : i = Fin.F1) by (dependent destruction i; [reflexivity|inversion i]).
    subst i; destruct (pick Fin.F1); reflexivity.
  - apply sb_br_id; intro i; destruct (pick i); reflexivity.
Qed.

(** Exact residuals matter for transition induction: the uniform selection
    bisimulation is not a replacement for these native trace transitions. *)
Lemma sched_trace_pick sch n st a w :
  not_done w ->
  |sched_trace sch n st, w| ↦
    |sched_trace sch n (snd (sched_pick sch n st a)),
      Obs (Log (slot_index (fst (sched_pick sch n st a)))) tt|.
Proof.
  rewrite unfold_sched_trace.
  revert a; generalize (sched_pick sch n st).
  destruct (sched_arity sch n st) as [|arity]; intros pick a Hw.
  - assert (Ha : a = Fin.F1) by (dependent destruction a; [reflexivity|inversion a]).
    subst a; destruct (pick Fin.F1) as [i st']; cbn.
    apply ktrans_vis; exists tt; split; [reflexivity|split; [reflexivity|exact Hw]].
  - apply ktrans_br; exists a; destruct (pick a) as [i st']; cbn.
    apply ktrans_vis; exists tt; split; [reflexivity|split; [reflexivity|exact Hw]].
Qed.

Lemma sched_trace_pick_inv sch n st w t' w' :
  |sched_trace sch n st, w| ↦ |t', w'| ->
  exists a, w' = Obs (Log (slot_index (fst (sched_pick sch n st a)))) tt /\
    sched_trace sch n (snd (sched_pick sch n st a)) ≅ t'.
Proof.
  rewrite unfold_sched_trace.
  generalize (sched_pick sch n st).
  destruct (sched_arity sch n st) as [|arity]; intros pick TR.
  - destruct (pick Fin.F1) as [i st'] eqn:Hpick; cbn in TR.
    apply ktrans_vis in TR as ([] & -> & Heq & _).
    exists Fin.F1; rewrite Hpick; cbn; split; [reflexivity|exact Heq].
  - apply ktrans_br in TR as (a & TR).
    destruct (pick a) as [i st'] eqn:Hpick; cbn in TR.
    apply ktrans_vis in TR as ([] & -> & Heq & _).
    exists a; rewrite Hpick; cbn; split; [reflexivity|exact Heq].
Qed.

(** Fairness: from every policy state, every slot of a fixed-size pool is
    picked again and again. *)
Class FairScheduler (sch : Scheduler) : Prop :=
  fair_scheduled : forall n (i : Fin.t (S n)) (st : sched_state sch) (w : World (writerE nat)),
    not_done w ->
    <( {sched_trace sch n st}, w |=L AG (AF visW {eq (slot_index i)}) )>.

(** Induction-friendly witness: along every alternative that avoids slot
    [i], slot [i] is still picked after finitely many scheduling points. *)
Inductive EventuallyPicks (sch : Scheduler) (n : nat) (i : Fin.t (S n)) : sched_state sch -> Prop :=
| ep_intro st :
    (forall a, fst (sched_pick sch n st a) <> i ->
               EventuallyPicks sch n i (snd (sched_pick sch n st a))) ->
    EventuallyPicks sch n i st.

(** A destination policy may duplicate a source scheduling point only while
    strictly decreasing its own well-founded rank. Every offered destination
    choice must match a source choice, including its selected slot. *)
Lemma eventually_picks_simulation {V} (source target: Scheduler)
  (n: nat) (i: Fin.t (S n))
  (Rel: sched_state target -> sched_state source -> Prop)
  (rank: sched_state target -> V) (ltV: relation V) :
  well_founded ltV ->
  (forall dst src offer, Rel dst src -> exists offer',
    fst (sched_pick target n dst offer) = fst (sched_pick source n src offer') /\
    (Rel (snd (sched_pick target n dst offer))
         (snd (sched_pick source n src offer')) \/
     (Rel (snd (sched_pick target n dst offer)) src /\
      ltV (rank (snd (sched_pick target n dst offer))) (rank dst)))) ->
  forall src dst, EventuallyPicks source n i src -> Rel dst src ->
    EventuallyPicks target n i dst.
Proof.
  intros Wf Hsim src dst Hep; revert dst.
  induction Hep as [src Hnext IH].
  apply (well_founded_induction
    (wf_inverse_image (sched_state target) V ltV rank Wf)
    (fun dst => Rel dst src -> EventuallyPicks target n i dst)).
  intros dst IHrank Hrel; constructor; intros offer Hmiss.
  destruct (Hsim dst src offer Hrel) as
    (offer' & Hpick & [Hadvance | [Hstay Hlt]]).
  - apply (IH offer'); [now rewrite <- Hpick | exact Hadvance].
  - apply (IHrank _ Hlt Hstay).
Qed.

Section FairBridge.
  Context (sch : Scheduler) (n : nat) (i : Fin.t (S n)).

  Lemma eventually_picks_af st w :
    EventuallyPicks sch n i st -> not_done w ->
    <( {sched_trace sch n st}, w |=L AF visW {eq (slot_index i)} )>.
  Proof.
    intro Hep; revert w; induction Hep as [st Hst IH]; intros w Hw.
    ticl_normalize; rewrite sched_trace_select.
    apply (au_br (b:=false)); [apply ticll_top; exact Hw|exists Fin.F1; apply can_step_vis; [exact tt|exact Hw]|].
    intros a t' w' TR.
    apply ktrans_vis in TR as ([] & -> & Heq & _); rewrite <- Heq.
    destruct (Fin.eq_dec (fst (sched_pick sch n st a)) i) as [Hpick|Hne].
    - cleft; apply ticl_vis; constructor; rewrite Hpick; reflexivity.
    - apply IH; [exact Hne|constructor].
  Qed.

  Lemma af_trace_eventually_picks :
    forall (t : ctreeW nat Bn unit) w,
      <( t, w |=L AF visW {eq (slot_index i)} )> ->
      forall st, t ≅ sched_trace sch n st ->
      w <> Obs (Log (slot_index i)) tt ->
      EventuallyPicks sch n i st.
  Proof.
    intros t w H.
    cinduction H; intros st Et Hw.
    - exfalso; apply Hw.
      apply ticl_vis in Hp; inversion Hp as [Y e v Hv Ew]; clear Hp.
      destruct e as [k]; destruct v; cbn in Hv; subst; reflexivity.
    - constructor; intros a Hne.
      apply ticl_not_done in Hp.
      apply (HInd (sched_trace sch n (snd (sched_pick sch n st a)))
        (Obs (Log (slot_index (fst (sched_pick sch n st a)))) tt)).
      + rewrite Et; apply sched_trace_pick; exact Hp.
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
  - rewrite sched_trace_select; apply can_step_br; exists Fin.F1.
    apply can_step_vis; [exact tt|exact Hw].
  - intros t' w' TR.
    apply sched_trace_pick_inv in TR as (a & -> & Heq); rewrite <- Heq.
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
      (φ : ticl (writerE (W + nat)) None) :
    ClosedPool Inv ->
    (forall (o : W) (t : ctreeW (W + nat) Bn (Sigma * unit)) w, not_done w ->
       <( t, {Obs (Log (inl o)) tt} |=L φ )> -> <( {Vis (Log (inl o)) (fun _ => t)}, w |=L φ )>) ->
    (forall g ts sigma st w, Inv g ts sigma -> not_done w ->
       <( {fair ts None st sigma}, w |=L φ )>) ->
    forall g ts sigma focus st w, Inv g ts sigma -> not_done w ->
      <( {fair ts focus st sigma}, w |=L AG φ )>.
  Proof.
    intros Hclosed Hlog Hφ.
    assert (Hpref : forall xs (t : ctreeW (W + nat) Bn (Sigma * unit)),
      (forall w, not_done w -> <( t, w |=L φ )>) ->
      forall w, not_done w -> <( {emit_list (List.map inl xs) t}, w |=L φ )>).
    { induction xs as [|o xs IH]; intros t Ht w Hw; [apply Ht, Hw|].
      ticl_normalize; cbn [List.map]; rewrite emit_list_cons.
      apply Hlog; [exact Hw|]; apply IH; [exact Ht|constructor]. }
    coinduction R CIH; intros g ts sigma focus st w Hinv Hw.
    assert (Hnone : forall g ts sigma st w, Inv g ts sigma -> not_done w ->
      agcF (entails (Sigma * unit) false φ) (elem R) (fair ts None st sigma) w).
    { clear g ts sigma focus st w Hinv Hw; intros g ts sigma st w Hinv Hw.
      pose proof (Hφ g ts sigma st w Hinv Hw) as Hnow.
      ticl_normalize in Hnow; rewrite interp_schedule_fair_select in Hnow |- *.
      split; [exact Hnow|]; split.
      - apply can_step_br_alts; exists Fin.F1; apply can_step_vis; [exact tt|exact Hw].
      - intros t' w' Htr.
        apply ktrans_br_alts in Htr as (a & Htr).
        apply ktrans_vis in Htr as ([] & -> & Heq & _); rewrite <- Heq.
        apply (CIH g ts sigma (Some _)); [exact Hinv|constructor]. }
    destruct focus as [i|]; [|apply (Hnone g ts sigma st w Hinv Hw)].
    destruct (Hclosed g ts sigma i Hinv) as (g' & logs & residual & sigma' & Hseg & Hinv').
    rewrite (segment_interp_fair sch handler exactW (fun X t u => relabel_equ_sb t u)
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
      <( {fair ts focus st sigma}, w |=L AF visW {fair_obs P} )>.
  Proof.
    intros Hcert g.
    induction g as [g IHrank] using
      (well_founded_induction (wf_inverse_image G V ltV rank (fair_wf Hcert))).
    intros ts sigma focus st w Hinv Hw; ticl_normalize.
    (* A turn of the helpful slot: a hit or a strict rank drop. *)
    assert (Htarget : forall g0 ts sigma st w,
      Inv g0 ts sigma -> rank g0 = rank g -> target g0 = target g -> not_done w ->
      <( {fair ts (Some (target g)) st sigma}, w |=L AF visW {fair_obs P} )>).
    { intros g0 ts0 sigma0 st0 w0 Hinv0 Hrank Htgt Hw0; ticl_normalize.
      destruct (fair_turn Hcert g0 ts0 sigma0 (target g) Hinv0)
        as (g' & logs & residual & sigma' & Hseg & Hinv' & [HP|[Hlt|(Hne & _)]]);
        [| |exfalso; apply Hne; symmetry; exact Htgt];
        rewrite (segment_interp_fair sch handler exactW (fun X t u => relabel_equ_sb t u)
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
        <( {fair ts focus st sigma}, w |=L AF visW {fair_obs P} )>).
    { intros st0 Hep; induction Hep as [st0 Hst0 IH].
      assert (Hnone : forall g0 ts sigma w,
        Inv g0 ts sigma -> rank g0 = rank g -> target g0 = target g -> not_done w ->
        <( {fair ts None st0 sigma}, w |=L AF visW {fair_obs P} )>).
      { intros g0 ts0 sigma0 w0 Hinv0 Hrank Htgt Hw0; ticl_normalize.
        rewrite interp_schedule_fair_select.
        apply (au_br_alts (b:=false)); [apply ticll_top; exact Hw0|exists Fin.F1; apply can_step_vis; [exact tt|exact Hw0]|].
        intros a t' w' TR.
        apply ktrans_vis in TR as ([] & -> & Heq & _); rewrite <- Heq.
        destruct (Fin.eq_dec (fst (sched_pick sch n st0 a)) (target g)) as [Hj|Hj].
        - rewrite Hj; apply (Htarget g0); [exact Hinv0|exact Hrank|exact Htgt|constructor].
        - apply (IH a Hj g0); [exact Hinv0|exact Hrank|exact Htgt|constructor]. }
      intros g0 ts0 sigma0 [j|] w0 Hinv0 Hrank Htgt Hw0; ticl_normalize; [|apply (Hnone g0); assumption].
      destruct (fair_turn Hcert g0 ts0 sigma0 j Hinv0)
        as (g' & logs & residual & sigma' & Hseg & Hinv' & [HP|[Hlt|(Hne & Hrank' & Htgt')]]);
        rewrite (segment_interp_fair sch handler exactW (fun X t u => relabel_equ_sb t u)
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
      <( {fair ts focus st sigma}, w |=L AG (AF visW {fair_obs P}) )>.
  Proof.
    intro Hcert.
    apply ag_pool_fair_invariance.
    - exact (fair_certificate_closed _ _ _ _ _ Hcert).
    - intros o t w Hw Ht; apply ((au_vis (b:=false)) _ _ tt); right; split;
        [apply ticll_top; exact Hw|intros []; exact Ht].
    - intros g ts sigma st w Hinv Hw.
      apply (aul_pool_fair_eventually _ _ _ _ _ Hcert g ts sigma None st w Hinv Hw).
  Qed.

  (** ** Fixed pool text, finite log lists, constant helpful slot. *)
  Definition FairTurns {G V} (ts : pool E Bn (S n)) (i : Fin.t (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V) (ltV : V -> V -> Prop) (P : W -> Prop) : Prop :=
    forall g sigma (j : Fin.t (S n)), Inv g sigma ->
    exists g' sigma' logs,
      segment_to handler exactW (ts $ j) sigma logs (ts $ j) sigma' /\
      Inv g' sigma' /\
      (List.Exists P logs \/ ltV (rank g') (rank g) \/ (j <> i /\ rank g' = rank g)).

  Lemma fair_turns_certificate {G V} ts i Inv rank ltV P :
    well_founded ltV -> @FairTurns G V ts i Inv rank ltV P ->
    FairCertificate (fun g ts' sigma => Inv g sigma /\ pool_guard_equ ts' ts)
      rank ltV (fun _ => i) P.
  Proof.
    intros Hwf Hturns; constructor; [exact Hwf|].
    intros g0 ts' sigma j (Hinv0 & Hpool).
    destruct (Hturns g0 sigma j Hinv0) as (g' & sigma' & logs & (residual & Hseg & Htail) & Hinv' & Hcase).
    apply (proj2 (guard_equ_segment_iff handler exactW (ts' $ j) (ts $ j) (Hpool j)
      sigma logs residual sigma')) in Hseg.
    exists g',logs,residual,sigma'; split; [exact Hseg|split].
    - split; [exact Hinv'|].
      intro k; destruct (Fin.eq_dec k j) as [->|Hne].
      + rewrite Vector.nth_replace_eq; exact Htail.
      + rewrite Vector.nth_replace_neq by congruence; apply Hpool.
    - destruct Hcase as [HP|[Hlt|(Hne & Hrank)]];
        [left; exact HP|right; left; exact Hlt|right; right; auto].
  Qed.

  Theorem agaf_fair_turns `{FairScheduler sch} {G V} ts i Inv rank ltV P :
    well_founded ltV -> @FairTurns G V ts i Inv rank ltV P ->
    forall g sigma focus st w, Inv g sigma -> not_done w ->
      <( {fair ts focus st sigma}, w |=L AG (AF visW {fair_obs P}) )>.
  Proof.
    intros Hwf Hturns g sigma focus st w Hinv Hw.
    exact (agaf_pool_fair (fun g ts' sigma => Inv g sigma /\ pool_guard_equ ts' ts)
      rank ltV (fun _ => i) P
      (fair_turns_certificate ts i Inv rank ltV P Hwf Hturns)
      g ts sigma focus st w (conj Hinv (fun j => guard_equ_equ _ _ (reflexivity _))) Hw).
  Qed.

  (** ** Abstract-model clients: ghost data projects to model states. *)
  Theorem agaf_pool_simulation_fair `{FairScheduler sch} {St Act G V}
      (actor : Fin.t (S n) -> Act) (slot : Act -> Fin.t (S n))
      (slot_actor : forall i, slot (actor i) = i)
      (step : Act -> St -> option (St * list W)) (pool_of : St -> pool E Bn (S n))
      (agree : Sigma -> St -> Prop) (Inv : St -> Prop)
      (Hsim : PoolSimulation n handler slot step pool_of agree Inv)
      (st_of : G -> St) (InvG : G -> Prop) (rank : G -> V) (ltV : V -> V -> Prop)
      (target : G -> Fin.t (S n)) (P : W -> Prop) :
    well_founded ltV ->
    (forall g, InvG g -> Inv (st_of g)) ->
    (forall g who s' event, InvG g -> step who (st_of g) = Some (s', event) ->
       exists g', st_of g' = s' /\ InvG g' /\
         (List.Exists P event \/ ltV (rank g') (rank g) \/
          (slot who <> target g /\ rank g' = rank g /\ target g' = target g))) ->
    forall g ts sigma focus st w,
      InvG g -> agree sigma (st_of g) -> pool_guard_equ ts (pool_of (st_of g)) -> not_done w ->
      <( {fair ts focus st sigma}, w |=L AG (AF visW {fair_obs P}) )>.
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
    exists g', event, residual, σ'; split; [exact Hseg|]; split.
    - split; [exact Hg'|rewrite Es'; split; assumption].
    - exact Hcase.
  Qed.
End PoolRulesFair.
