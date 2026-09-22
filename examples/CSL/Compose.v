(** * Compose: recurring per-queue progress for TWO ACTIVE queues.

    This is the experiment's positive result.  Both queues are running, under
    the nonpreemptive cyclic scheduler that is part of the program
    ([SLang.sbody]), and each one still satisfies the nested recurrence
    formula of the frozen single-queue theorem.

    The claim is deliberately NOT "the second queue is a frame".  A frame is a
    resource nobody touches; here the other queue is rewritten on every second
    turn.  The proof is organised to make the difference visible:

    - [step_focus] / [step_foreign] are the two resource-level turn lemmas.
      [step_foreign] is where active composition differs from framing: the
      focused queue's representation must survive a step of the OTHER
      component, and that is [Sep2.foreign_pres], not a frame rule.

    - the temporal layer reuses the frozen loop rules unchanged
      ([ICTree.Logic.State.ag_state_iter] for the outer [AG] and
      [Recurrence.owned_aul_iter_ghost] for the inner [AF]).  No fixed point
      is unfolded anywhere in this file.

    - the variant is the reused natural position rank plus ONE new component,
      the scheduler phase ([Lex.rank3]).  The phase component is what makes a
      foreign turn count as progress; without it the composition does not
      close.  It is still a [nat]: no ordinal is used or needed.

    The whole development is stated for an arbitrary FOCUS, so the two
    per-queue theorems are two instantiations of one proof rather than a
    copied proof. *)

From Stdlib Require Import
  List
  Lia
  Bool
  Arith.PeanoNat
  Arith.Wf_nat
  Relations.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Interp.State.Mod
  ICTree.Events.State
  ICTree.Events.Writer
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.State
  Logic.Core.

From examples Require Import CSL.HeapQ CSL.Trace CSL.Layout CSL.Frame CSL.Recurrence CSL.Sep2 CSL.SLang CSL.Lex.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.

(** A queue that still contains an element is non-empty.  Used to keep the
    focused queue's node list non-empty across a FOREIGN turn without
    destructing it. *)
Lemma qrep_find_nonnil: forall hdr ns vs h nl d,
    qrep hdr ns vs h -> find nl vs = Some d -> ns <> [].
Proof.
  intros hdr ns vs h nl d Hq Hf C; subst ns.
  apply qrep_len in Hq; cbn in Hq.
  destruct vs as [| x vs]; [cbn in Hf; discriminate | cbn in Hq; discriminate].
Qed.

Section Composition.
  (** [u]/[v] are the two headers the PROGRAM alternates between.  [fh] is the
      header of the queue whose progress we are proving, [gh] the other one,
      and [fturn] the (program-computed) predicate saying whose turn it is.
      The four hypotheses connect the focus to the scheduler; they are
      discharged by [Nat.even] / [negb ∘ Nat.even] at the two instantiations
      below, so no scheduling assumption survives into the theorems. *)
  Context (u v: nat) (fq fh gh: nat) (fturn: nat -> bool)
          (Hfh: forall n, fturn n = true -> hdrof u v n = fh)
          (Hgh: forall n, fturn n = false -> hdrof u v n = gh)
          (Hft: forall n, fturn n = true -> tagof n = fq)
          (Hflip: forall n, fturn (S n) = negb (fturn n)).

  Lemma fturn_t: forall n, fturn n = true -> fturn (S n) = false.
  Proof. intros n H; rewrite Hflip, H; reflexivity. Qed.

  Lemma fturn_f: forall n, fturn n = false -> fturn (S n) = true.
  Proof. intros n H; rewrite Hflip, H; reflexivity. Qed.

  (** ** The two resource-level turn lemmas *)

  (** A turn of the FOCUSED queue.  Reused: [HeapQ.rot_heap_spec].  New: the
      foreign queue must survive it ([Sep2.foreign_pres_rot]) and footprint
      disjointness must be transported ([HeapQ.qcells_rot]). *)
  Lemma step_focus: forall nsf vsf nsg vsg a pv h,
      qrep fh (a :: nsf) (pv :: vsf) h ->
      qrep gh nsg vsg h ->
      Disj fh (a :: nsf) gh nsg ->
      qrep fh (nsf ++ [a]) (vsf ++ [pv])
           (rot_heap fh a (hdf nsf 0) (zof fh nsf) h)
      /\ qrep gh nsg vsg (rot_heap fh a (hdf nsf 0) (zof fh nsf) h)
      /\ Disj fh (nsf ++ [a]) gh nsg.
  Proof.
    intros nsf vsf nsg vsg a pv h Hqf Hqg Hdj.
    split; [apply (rot_heap_spec fh a nsf pv vsf h Hqf) |].
    split.
    - exact (foreign_pres_rot fh a nsf (pv :: vsf) gh nsg vsg h Hqf Hqg Hdj).
    - intros x Hx; apply Hdj, (qcells_rot fh a nsf x), Hx.
  Qed.

  (** A turn of the FOREIGN queue.  This is the statement that has no
      counterpart in the unused-frame experiment: the focused queue's
      representation, AT THE SAME abstract queue, survives a step of a
      component that is itself active. *)
  Lemma step_foreign: forall nsf vsf nsg vsg b pw h,
      qrep fh nsf vsf h -> nsf <> [] ->
      qrep gh (b :: nsg) (pw :: vsg) h ->
      Disj fh nsf gh (b :: nsg) ->
      qrep fh nsf vsf (rot_heap gh b (hdf nsg 0) (zof gh nsg) h)
      /\ qrep gh (nsg ++ [b]) (vsg ++ [pw])
              (rot_heap gh b (hdf nsg 0) (zof gh nsg) h)
      /\ Disj fh nsf gh (nsg ++ [b]).
  Proof.
    intros nsf vsf nsg vsg b pw h Hqf Hnef Hqg Hdj.
    split.
    - exact (foreign_pres_rot gh b nsg (pw :: vsg) fh nsf vsf h Hqg Hqf
               (Disj_sym _ _ _ _ Hdj)).
    - split; [apply (rot_heap_spec gh b nsg pw vsg h Hqg) |].
      intros x Hx Hy; apply (Hdj x Hx), (qcells_rot gh b nsg x), Hy.
  Qed.

  (** ** The invariants *)

  (** The [AG] invariant: BOTH queues are represented in the shared heap, their
      footprints are disjoint, and each still contains its observed element.
      The abstract queues are existentially quantified, exactly as in the
      frozen single-queue proof. *)
  Definition Iq (nlf nlg: nat) (h: Heap) : Prop :=
    exists nsf vsf nsg vsg df dg,
      qrep fh nsf vsf h /\ qrep gh nsg vsg h /\ Disj fh nsf gh nsg
      /\ find nlf vsf = Some df /\ find nlg vsg = Some dg.

  (** The ghost invariant of the inner eventuality.  The rank is
      (occurrence bound left, position in the focused queue, scheduler phase).
      Neither the heap nor the world appears in it. *)
  Definition Ig (nlf nlg kb: nat) (m: nat * (nat * nat)) (n: nat) (s: SSig)
    : Prop :=
    exists nsf vsf nsg vsg df dg,
      qrep fh nsf vsf (fst s) /\ qrep gh nsg vsg (fst s) /\ Disj fh nsf gh nsg
      /\ find nlf vsf = Some df /\ find nlg vsg = Some dg
      /\ m = (kb - snd s, (df, if fturn n then 0 else 1)).

  (** ** The inner eventuality: the focused queue pops its element again *)

  Section Inner.
    Context (nlf nlg kb: nat) (P: SObs -> Prop)
            (HP: forall j, Nat.le kb j -> P (SPop fq nlf j)).

    Lemma inner_af: forall n h c w,
        not_done w ->
        Iq nlf nlg h ->
        <( {interp_state sh (sched u v n) (h, c)}, w |= AF visW {P} )>.
    Proof.
      intros n h c w Hd (nsf & vsf & nsg & vsg & df & dg & Hqf & Hqg & Hdj & Hff & Hfg).
      unfold sched.
      apply (owned_aul_iter_ghost sh rank3 (Ig nlf nlg kb) (sbody u v) _ _
               rank3_wf (kb - c, (df, if fturn n then 0 else 1)) n (h, c) w Hd).
      - exists nsf, vsf, nsg, vsg, df, dg; cbn.
        split; [exact Hqf |]; split; [exact Hqg |]; split; [exact Hdj |];
          split; [exact Hff |]; split; [exact Hfg | reflexivity].
      - clear n h c w Hd nsf vsf nsg vsg df dg Hqf Hqg Hdj Hff Hfg.
        intros m n s w Hd
          (nsf & vsf & nsg & vsg & df & dg & Hqf & Hqg & Hdj & Hff & Hfg & Hm).
        destruct s as (h, c); cbn in Hqf, Hqg, Hm.
        destruct (fturn n) eqn:Eph.
        + (* --- the FOCUSED queue's turn --- *)
          destruct vsf as [| pv vsf']; [cbn in Hff; discriminate |].
          destruct nsf as [| a nsf'];
            [apply qrep_len in Hqf; cbn in Hqf; discriminate |].
          pose proof (sbody_spec u v n a nsf' pv vsf' h c) as Hspec.
          rewrite (Hfh n Eph), (Hft n Eph) in Hspec.
          specialize (Hspec Hqf).
          destruct (step_focus nsf' vsf' nsg vsg a pv h Hqf Hqg Hdj)
            as (Hqf' & Hqg' & Hdj').
          assert (Hstep: forall df',
                     find nlf (vsf' ++ [pv]) = Some df' ->
                     rank3 (kb - S c, (df', 1)) m ->
                     (exists g' i' s' w',
                         not_done w'
                         /\ <[ {interp_state sh ((sbody u v) n) (h, c)}, w
                               |= ⊤ AU AX done= {(@inl nat unit i', s')} w' ]>
                         /\ Ig nlf nlg kb g' i' s'
                         /\ rank3 g' m)).
          { intros df' Hdf' Hlex.
            exists (kb - S c, (df', 1)), (S n),
              (rot_heap fh a (hdf nsf' 0) (zof fh nsf') h, S c),
              (Obs (Log (SPop fq pv c)) tt).
            split; [constructor |].
            split.
            { rewrite Hspec; apply aur_log;
                [cleft; apply axr_ret; [constructor | split; reflexivity]
                | apply ticll_top; assumption]. }
            split; [| exact Hlex].
            exists (nsf' ++ [a]), (vsf' ++ [pv]), nsg, vsg, df', dg; cbn.
            split; [exact Hqf' |]; split; [exact Hqg' |]; split; [exact Hdj' |];
              split; [exact Hdf' |]; split; [exact Hfg |].
            rewrite (fturn_t n Eph); reflexivity. }
          destruct df as [| d0].
          * (* the element is at the head of the focused queue *)
            pose proof (find_head _ _ _ Hff) as Hv; subst pv.
            destruct (Nat.le_gt_cases kb c) as [Hle | Hgt].
            -- (* and the occurrence bound is met: observe it now *)
               left.
               rewrite Hspec.
               apply afl_log; [assumption |].
               cleft; apply ticll_vis; constructor; now apply HP.
            -- (* the bound is not met yet: rotate, the bound gets closer *)
               right.
               destruct (find_last_ex nlf vsf') as (df' & Hdf').
               apply (Hstep df'); [exact Hdf' | rewrite Hm; apply rank3_bound; lia].
          * (* the element is deeper: rotate, its position falls *)
            right.
            apply (Hstep d0).
            -- rewrite <- rotl_cons; eapply find_rotl; exact Hff.
            -- rewrite Hm; destruct (Nat.le_gt_cases kb c) as [Hle | Hgt].
               ++ replace (kb - S c) with (kb - c) by lia.
                  apply rank3_pos; lia.
               ++ apply rank3_bound; lia.
        + (* --- the FOREIGN queue's turn --- *)
          assert (Hnef: nsf <> []) by (eapply qrep_find_nonnil; eassumption).
          destruct vsg as [| pw vsg']; [cbn in Hfg; discriminate |].
          destruct nsg as [| b nsg'];
            [apply qrep_len in Hqg; cbn in Hqg; discriminate |].
          pose proof (sbody_spec u v n b nsg' pw vsg' h c) as Hspec.
          rewrite (Hgh n Eph) in Hspec.
          specialize (Hspec Hqg).
          destruct (step_foreign nsf vsf nsg' vsg' b pw h Hqf Hnef Hqg Hdj)
            as (Hqf' & Hqg' & Hdj').
          destruct (find_rotl_pres _ _ _ _ Hfg) as (dg' & Hdg').
          rewrite rotl_cons in Hdg'.
          right.
          exists (kb - S c, (df, 0)), (S n),
            (rot_heap gh b (hdf nsg' 0) (zof gh nsg') h, S c),
            (Obs (Log (SPop (tagof n) pw c)) tt).
          split; [constructor |].
          split.
          { rewrite Hspec; apply aur_log;
              [cleft; apply axr_ret; [constructor | split; reflexivity]
              | apply ticll_top; assumption]. }
          split.
          { exists nsf, vsf, (nsg' ++ [b]), (vsg' ++ [pw]), df, dg'; cbn.
            split; [exact Hqf' |]; split; [exact Hqg' |]; split; [exact Hdj' |];
              split; [exact Hff |]; split; [exact Hdg' |].
            rewrite (fturn_f n Eph); reflexivity. }
          rewrite Hm; destruct (Nat.le_gt_cases kb c) as [Hle | Hgt].
          * replace (kb - S c) with (kb - c) by lia.
            apply rank3_phase; lia.
          * apply rank3_bound; lia.
    Qed.

    (** ** The recurrence theorem for the focused queue *)
    Theorem sched_agaf: forall n h c w,
        not_done w ->
        Iq nlf nlg h ->
        <( {interp_state sh (sched u v n) (h, c)}, w |= AG (AF visW {P}) )>.
    Proof.
      intros n h c w Hd HI.
      unfold sched.
      apply (ag_state_iter sh (h, c)
               (fun (_: nat) (s: SSig) (_: WorldW SObs) => Iq nlf nlg (fst s))
               n w); [assumption | exact HI |].
      clear n h c w Hd HI.
      intros n s w Hd HI.
      destruct s as (h, c); cbn in HI.
      split; [now apply inner_af |].
      destruct HI
        as (nsf & vsf & nsg & vsg & df & dg & Hqf & Hqg & Hdj & Hff & Hfg).
      destruct (fturn n) eqn:Eph.
      - (* focused turn *)
        destruct vsf as [| pv vsf']; [cbn in Hff; discriminate |].
        destruct nsf as [| a nsf'];
          [apply qrep_len in Hqf; cbn in Hqf; discriminate |].
        pose proof (sbody_spec u v n a nsf' pv vsf' h c) as Hspec.
        rewrite (Hfh n Eph), (Hft n Eph) in Hspec.
        specialize (Hspec Hqf).
        destruct (step_focus nsf' vsf' nsg vsg a pv h Hqf Hqg Hdj)
          as (Hqf' & Hqg' & Hdj').
        destruct (find_rotl_pres _ _ _ _ Hff) as (df' & Hdf').
        rewrite rotl_cons in Hdf'.
        rewrite Hspec.
        apply anr_log; [| apply ticll_top; assumption].
        cleft; apply axr_ret; [constructor |].
        exists (S n); split; [reflexivity | split; [constructor |]].
        exists (nsf' ++ [a]), (vsf' ++ [pv]), nsg, vsg, df', dg; cbn.
        split; [exact Hqf' |]; split; [exact Hqg' |]; split; [exact Hdj' |];
          split; [exact Hdf' | exact Hfg].
      - (* foreign turn *)
        assert (Hnef: nsf <> []) by (eapply qrep_find_nonnil; eassumption).
        destruct vsg as [| pw vsg']; [cbn in Hfg; discriminate |].
        destruct nsg as [| b nsg'];
          [apply qrep_len in Hqg; cbn in Hqg; discriminate |].
        pose proof (sbody_spec u v n b nsg' pw vsg' h c) as Hspec.
        rewrite (Hgh n Eph) in Hspec.
        specialize (Hspec Hqg).
        destruct (step_foreign nsf vsf nsg' vsg' b pw h Hqf Hnef Hqg Hdj)
          as (Hqf' & Hqg' & Hdj').
        destruct (find_rotl_pres _ _ _ _ Hfg) as (dg' & Hdg').
        rewrite rotl_cons in Hdg'.
        rewrite Hspec.
        apply anr_log; [| apply ticll_top; assumption].
        cleft; apply axr_ret; [constructor |].
        exists (S n); split; [reflexivity | split; [constructor |]].
        exists nsf, vsf, (nsg' ++ [b]), (vsg' ++ [pw]), df, dg'; cbn.
        split; [exact Hqf' |]; split; [exact Hqg' |]; split; [exact Hdj' |];
          split; [exact Hff | exact Hdg'].
    Qed.
  End Inner.
End Composition.

(** ** The two per-queue theorems.

    Both are instantiations of ONE proof: the focus is a parameter, and the
    scheduler hypotheses are discharged by [Nat.even] and its negation.  Note
    the quantification over the turn counter [n]: the theorems hold from
    EITHER starting scheduler phase, and from any point of the schedule. *)

Lemma even_true_hdr: forall u v n, Nat.even n = true -> hdrof u v n = u.
Proof. exact hdrof_even. Qed.

Lemma neg_even_true: forall n, negb (Nat.even n) = true -> Nat.even n = false.
Proof. intros n H; now apply negb_true_iff in H. Qed.

Lemma neg_even_false: forall n, negb (Nat.even n) = false -> Nat.even n = true.
Proof. intros n H; now apply negb_false_iff in H. Qed.

Lemma neg_even_flip: forall n, negb (Nat.even (S n)) = negb (negb (Nat.even n)).
Proof. intro n; now rewrite even_flip. Qed.

(** *** Queue 1 (the one the scheduler serves on even turns) *)

Theorem sched_agaf_q1_gen: forall u v nl1 nl2 kb (P: SObs -> Prop),
    (forall j, Nat.le kb j -> P (SPop 1 nl1 j)) ->
    forall n h c ns1 vs1 ns2 vs2 d1 d2,
      qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
      find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
      <( {srun u v n h c}, Pure |= AG (AF visW {P}) )>.
Proof.
  intros u v nl1 nl2 kb P HP n h c ns1 vs1 ns2 vs2 d1 d2 Hq1 Hq2 Hdj Hf1 Hf2.
  unfold srun.
  apply (sched_agaf u v 1 u v Nat.even
           (fun n H => hdrof_even u v n H)
           (fun n H => hdrof_odd u v n H)
           (fun n H => tagof_even n H)
           even_flip nl1 nl2 kb P HP n h c Pure);
    [constructor |].
  exists ns1, vs1, ns2, vs2, d1, d2.
  split; [exact Hq1 |]; split; [exact Hq2 |]; split; [exact Hdj |];
    split; [exact Hf1 | exact Hf2].
Qed.

Theorem sched_agaf_q1: forall u v nl1 nl2 n h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
    <( {srun u v n h c}, Pure |= AG (AF visW {spopped 1 nl1}) )>.
Proof.
  intros.
  eapply (sched_agaf_q1_gen u v nl1 nl2 0 (spopped 1 nl1));
    [intros j _; split; reflexivity | eassumption .. ].
Qed.

Theorem sched_agaf_q1_fresh: forall u v nl1 nl2 k n h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
    <( {srun u v n h c}, Pure |= AG (AF visW {spopped_after 1 nl1 k}) )>.
Proof.
  intros.
  eapply (sched_agaf_q1_gen u v nl1 nl2 k (spopped_after 1 nl1 k));
    [intros j Hj; split; [reflexivity | split; [reflexivity | exact Hj]]
    | eassumption .. ].
Qed.

(** *** Queue 2 (the one the scheduler serves on odd turns) *)

Theorem sched_agaf_q2_gen: forall u v nl1 nl2 kb (P: SObs -> Prop),
    (forall j, Nat.le kb j -> P (SPop 2 nl2 j)) ->
    forall n h c ns1 vs1 ns2 vs2 d1 d2,
      qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
      find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
      <( {srun u v n h c}, Pure |= AG (AF visW {P}) )>.
Proof.
  intros u v nl1 nl2 kb P HP n h c ns1 vs1 ns2 vs2 d1 d2 Hq1 Hq2 Hdj Hf1 Hf2.
  unfold srun.
  apply (sched_agaf u v 2 v u (fun n => negb (Nat.even n))
           (fun n H => hdrof_odd u v n (neg_even_true n H))
           (fun n H => hdrof_even u v n (neg_even_false n H))
           (fun n H => tagof_odd n (neg_even_true n H))
           neg_even_flip nl2 nl1 kb P HP n h c Pure);
    [constructor |].
  exists ns2, vs2, ns1, vs1, d2, d1.
  split; [exact Hq2 |]; split; [exact Hq1 |];
    split; [now apply Disj_sym | split; [exact Hf2 | exact Hf1]].
Qed.

Theorem sched_agaf_q2: forall u v nl1 nl2 n h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
    <( {srun u v n h c}, Pure |= AG (AF visW {spopped 2 nl2}) )>.
Proof.
  intros.
  eapply (sched_agaf_q2_gen u v nl1 nl2 0 (spopped 2 nl2));
    [intros j _; split; reflexivity | eassumption .. ].
Qed.

Theorem sched_agaf_q2_fresh: forall u v nl1 nl2 k n h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
    <( {srun u v n h c}, Pure |= AG (AF visW {spopped_after 2 nl2 k}) )>.
Proof.
  intros.
  eapply (sched_agaf_q2_gen u v nl1 nl2 k (spopped_after 2 nl2 k));
    [intros j Hj; split; [reflexivity | split; [reflexivity | exact Hj]]
    | eassumption .. ].
Qed.
