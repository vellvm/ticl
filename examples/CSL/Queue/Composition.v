(** * Recurring per-queue progress for two active queues under any fair scheduler.

    Both workers of [parallel_queues] rotate their OWN queue in the shared
    heap; the scheduler is any [FairScheduler].

    The claim is deliberately NOT "the second queue is a frame".  A frame is a
    resource nobody touches; here the other queue is rewritten on every one of
    its turns.  The proof is organised to make the difference visible:

    - [step_focus] / [step_foreign] are the two resource-level turn lemmas.
      [step_foreign] is where active composition differs from framing: the
      focused queue's representation must survive a step of the OTHER
      component, and that is [Separation.foreign_pres], not a frame rule.

    - the temporal layer is the fairness inversion rule [agaf_fair_turns]:
      the invariant is both queues represented and disjoint, the rank is
      (occurrence bound left, position of the element in the focused queue)
      under [lexnat], and the helpful slot is the focused worker.  A foreign
      turn leaves the rank alone; fairness of the policy supplies the focused
      turn.  No fixed point is unfolded anywhere in this file.

    The whole development is stated for an arbitrary FOCUS, so the two
    per-queue theorems are two instantiations of one proof rather than a
    copied proof. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat
  Fin
  Vector.
From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Events.Writer
  CTree.Interp.Yield.Fair
  Lang.CSL.Mod
  CTree.Logic.State
  Logic.Core
  Utils.Relations
  Utils.Lists.

From examples Require Import
  CSL.Queue.Representation CSL.Queue.Operations CSL.Queue.Trace CSL.Queue.Layout
  CSL.Queue.Frame CSL.Queue.Separation CSL.Queue.Program CSL.Queue.Shared.

Import CTree CTreeNotations TiclNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Section Composition.
  (** [fh] is the header of the queue whose progress we are proving, [gh] the
      other one. *)
  Context (fh gh: nat).

  (** ** The two resource-level turn lemmas *)

  (** A focused turn reuses [Representation.rot_heap_spec], preserves the
      foreign queue through [Separation.foreign_pres_rot], and transports
      disjointness through [Representation.qcells_rot]. *)
  Lemma step_focus: forall nsf vsf nsg vsg a pv h,
      qrep fh (a :: nsf) (pv :: vsf) h ->
      qrep gh nsg vsg h ->
      Disj fh (a :: nsf) gh nsg ->
      qrep fh (nsf ++ [a]) (vsf ++ [pv])
           (rot_heap fh a (List.hd 0 nsf) (zof fh nsf) h)
      /\ qrep gh nsg vsg (rot_heap fh a (List.hd 0 nsf) (zof fh nsf) h)
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
      qrep fh nsf vsf (rot_heap gh b (List.hd 0 nsg) (zof gh nsg) h)
      /\ qrep gh (nsg ++ [b]) (vsg ++ [pw])
              (rot_heap gh b (List.hd 0 nsg) (zof gh nsg) h)
      /\ Disj fh nsf gh (nsg ++ [b]).
  Proof.
    intros nsf vsf nsg vsg b pw h Hqf Hnef Hqg Hdj.
    split.
    - exact (foreign_pres_rot gh b nsg (pw :: vsg) fh nsf vsf h Hqg Hqf
               (Disj_sym _ _ _ _ Hdj)).
    - split; [apply (rot_heap_spec gh b nsg pw vsg h Hqg) |].
      intros x Hx Hy; apply (Hdj x Hx), (qcells_rot gh b nsg x), Hy.
  Qed.

  (** ** The invariant and rank

      BOTH queues are represented in the shared heap, their footprints are
      disjoint, and each still contains its observed element.  The ghost is
      the rank: (occurrence bound left, position of [nlf] in the focused
      queue).  Neither the heap nor the world appears in it. *)
  Definition Ifair (nlf nlg kb: nat) (g: nat * nat) (s: SSig) : Prop :=
    exists nsf vsf nsg vsg dg,
      qrep fh nsf vsf (fst (csl_memory s)) /\ qrep gh nsg vsg (fst (csl_memory s))
      /\ Disj fh nsf gh nsg
      /\ find_index Nat.eqb nlf vsf = Some (snd g) /\ find_index Nat.eqb nlg vsg = Some dg
      /\ fst g = kb - csl_counter s.

  (** One turn of either slot: a focused turn hits the target or drops the
      rank; a foreign turn drops the bound component or leaves the rank. *)
  Lemma worker_fair_turns (tagf tagg nlf nlg kb: nat) (fi: Fin.t 2)
      (ps: Vector.t (CProg unit) 2) (P: indexed (nat * nat) -> Prop) :
    (ps $ fi) = worker tagf fh -> (forall j, j <> fi -> (ps $ j) = worker tagg gh) ->
    (forall j, Nat.le kb j -> P (stamp (tagf, nlf) j)) ->
    FairTurns sh (csl_pool ps) fi (Ifair nlf nlg kb) (fun g => g) lexnat (csl_indexed P).
  Proof.
    intros Hfi Hother HP g s j (nsf & vsf & nsg & vsg & dg & Hqf & Hqg & Hdj & Hff & Hfg & Hg).
    destruct s as ((h, allocs), (ctx, c)); destruct g as (kc, d);
      cbn in Hqf, Hqg, Hff, Hg; subst kc.
    unfold csl_pool; rewrite (Vector.nth_map denote ps j j eq_refl).
    destruct (Fin.eq_dec j fi) as [->|Hne].
    - (* the FOCUSED queue's turn *)
      rewrite Hfi.
      destruct vsf as [| pv vsf']; [cbn in Hff; discriminate |].
      destruct nsf as [| a nsf']; [apply qrep_len in Hqf; cbn in Hqf; discriminate |].
      destruct (step_focus nsf' vsf' nsg vsg a pv h Hqf Hqg Hdj) as (Hqf' & Hqg' & Hdj').
      pose proof (exact_worker_turn tagf fh a nsf' pv vsf' h allocs ctx c Hqf) as Hturn.
      set (s' := ((rot_heap fh a (List.hd 0 nsf') (zof fh nsf') h, allocs), (ctx, S c))).
      assert (Hinv : forall d', find_index Nat.eqb nlf (vsf' ++ [pv]) = Some d' ->
        Ifair nlf nlg kb (kb - S c, d') s').
      { intros d' Hd'; exists (nsf' ++ [a]), (vsf' ++ [pv]), nsg, vsg, dg; cbn.
        split; [exact Hqf' |]; split; [exact Hqg' |]; split; [exact Hdj' |];
          split; [exact Hd' |]; split; [exact Hfg | reflexivity]. }
      destruct d as [| d0].
      + (* the element is at the head: observe it, or get closer to the bound *)
        pose proof (find_index_head Nat.eqb Nat.eqb_eq _ _ _ Hff) as Hv; subst pv.
        destruct (find_index_last_ex Nat.eqb Nat.eqb_eq nlf vsf') as (d' & Hd').
        exists (kb - S c, d'), s', (inr (stamp (tagf, nlf) c)).
        split; [exact Hturn |]; split; [now apply Hinv |].
        destruct (Nat.le_gt_cases kb c) as [Hle | Hgt].
        * left; cbn; apply HP; exact Hle.
        * right; left; left; cbn; lia.
      + (* the element is deeper: rotate, its position falls *)
        pose proof (find_index_rotl Nat.eqb nlf pv vsf' d0 Hff) as Hd0.
        rewrite rotl_cons in Hd0.
        exists (kb - S c, d0), s', (inr (stamp (tagf, pv) c)).
        split; [exact Hturn |]; split; [now apply Hinv |].
        right; left; destruct (Nat.le_gt_cases kb c) as [Hle | Hgt].
        * right; cbn; split; lia.
        * left; cbn; lia.
    - (* the FOREIGN queue's turn *)
      rewrite (Hother j Hne).
      assert (Hnef: nsf <> []).
      { intro Hnil; subst nsf.
        assert (Hlen : length vsf = 0) by (apply qrep_len in Hqf; cbn in Hqf; lia).
        pose proof (find_index_nonnil Nat.eqb nlf vsf d Hff) as Hnonempty.
        destruct vsf; [apply Hnonempty; reflexivity|discriminate]. }
      destruct vsg as [| pw vsg']; [cbn in Hfg; discriminate |].
      destruct nsg as [| b nsg']; [apply qrep_len in Hqg; cbn in Hqg; discriminate |].
      destruct (step_foreign nsf vsf nsg' vsg' b pw h Hqf Hnef Hqg Hdj) as (Hqf' & Hqg' & Hdj').
      destruct (find_index_rotl_pres Nat.eqb Nat.eqb_eq _ _ _ _ Hfg) as (dg' & Hdg').
      rewrite rotl_cons in Hdg'.
      exists (kb - S c, d),
        ((rot_heap gh b (List.hd 0 nsg') (zof gh nsg') h, allocs), (ctx, S c)),
        (inr (stamp (tagg, pw) c)).
      split; [exact (exact_worker_turn tagg gh b nsg' pw vsg' h allocs ctx c Hqg) |].
      split.
      { exists nsf, vsf, (nsg' ++ [b]), (vsg' ++ [pw]), dg'; cbn.
        split; [exact Hqf' |]; split; [exact Hqg' |]; split; [exact Hdj' |];
          split; [exact Hff |]; split; [exact Hdg' | reflexivity]. }
      destruct (Nat.le_gt_cases kb c) as [Hle | Hgt].
      + right; right; split; [exact Hne |]; f_equal; lia.
      + right; left; left; cbn; lia.
  Qed.

  (** ** The recurrence theorem for the focused queue, for any fair policy. *)
  Theorem fair_agaf_pool : forall (sch : Scheduler) `{FairScheduler sch} (tagf tagg : nat)
      (fi : Fin.t 2) (ps : Vector.t (CProg unit) 2) nlf nlg kb (P : indexed (nat * nat) -> Prop),
    (ps $ fi) = worker tagf fh -> (forall j, j <> fi -> (ps $ j) = worker tagg gh) ->
    (forall j, Nat.le kb j -> P (stamp (tagf, nlf) j)) ->
    forall focus st h allocs ctx c nsf vsf nsg vsg df dg,
      qrep fh nsf vsf h -> qrep gh nsg vsg h -> Disj fh nsf gh nsg ->
      find_index Nat.eqb nlf vsf = Some df -> find_index Nat.eqb nlg vsg = Some dg ->
      <( {run_fair_pool sch ps focus st ((h,allocs),(ctx,c))}, Pure
         |= AG (AF visW {fair_obs (csl_indexed P)}) )>.
  Proof.
    intros sch Hfair tagf tagg fi ps nlf nlg kb P Hfi Hother HP
      focus st h allocs ctx c nsf vsf nsg vsg df dg Hqf Hqg Hdj Hff Hfg.
    unfold run_fair_pool.
    apply (agaf_fair_turns sh sch (csl_pool ps) fi (Ifair nlf nlg kb) (fun g => g) lexnat
      (csl_indexed P) lexnat_wf (worker_fair_turns tagf tagg nlf nlg kb fi ps P Hfi Hother HP)
      (kb - c, df)); [|constructor].
    exists nsf, vsf, nsg, vsg, dg; cbn.
    split; [exact Hqf |]; split; [exact Hqg |]; split; [exact Hdj |];
      split; [exact Hff |]; split; [exact Hfg | reflexivity].
  Qed.
End Composition.

(** ** The two per-queue theorems.

    Both are instantiations of ONE proof: the focus is a parameter.  After the
    fork of [parallel_queues u v] the pool is [worker 2 v; worker 1 u], so
    queue 1 lives in slot [FS F1] and queue 2 in slot [F1].  The theorems hold
    from any focus and any policy state. *)

(** *** Queue 1 (slot [FS F1], tag 1) *)

Theorem fair_agaf_q1_gen (sch : Scheduler) `{FairScheduler sch} :
  forall u v nl1 nl2 kb (P: (indexed (nat * nat)) -> Prop),
    (forall j, Nat.le kb j -> P (stamp (1,nl1) j)) ->
    forall focus st h allocs ctx c ns1 vs1 ns2 vs2 d1 d2,
      qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
      find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
      <( {run_fair_pool sch [worker 2 v; worker 1 u]%vector focus st ((h, allocs), (ctx, c))}, Pure
         |= AG (AF visW {fair_obs (csl_indexed P)}) )>.
Proof.
  intros u v nl1 nl2 kb P HP focus st h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 Hq1 Hq2 Hdj Hf1 Hf2.
  assert (Hother : forall j : Fin.t 2, j <> Fin.FS Fin.F1 ->
    ([worker 2 v; worker 1 u]%vector $ j) = worker 2 v).
  { intro j; pattern j; apply Fin.caseS'; [intros _; reflexivity|].
    intro k; pattern k; apply Fin.caseS'; [intro Hc; exfalso; apply Hc; reflexivity|].
    intro z; inversion z. }
  apply (fair_agaf_pool u v sch 1 2 (Fin.FS Fin.F1) [worker 2 v; worker 1 u]%vector nl1 nl2 kb P eq_refl
    Hother
    HP focus st h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 Hq1 Hq2 Hdj Hf1 Hf2).
Qed.

(** *** Queue 2 (slot [F1], tag 2) *)

Theorem fair_agaf_q2_gen (sch : Scheduler) `{FairScheduler sch} :
  forall u v nl1 nl2 kb (P: (indexed (nat * nat)) -> Prop),
    (forall j, Nat.le kb j -> P (stamp (2,nl2) j)) ->
    forall focus st h allocs ctx c ns1 vs1 ns2 vs2 d1 d2,
      qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
      find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
      <( {run_fair_pool sch [worker 2 v; worker 1 u]%vector focus st ((h, allocs), (ctx, c))}, Pure
         |= AG (AF visW {fair_obs (csl_indexed P)}) )>.
Proof.
  intros u v nl1 nl2 kb P HP focus st h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 Hq1 Hq2 Hdj Hf1 Hf2.
  assert (Hother : forall j : Fin.t 2, j <> Fin.F1 ->
    ([worker 2 v; worker 1 u]%vector $ j) = worker 1 u).
  { intro j; pattern j; apply Fin.caseS'; [intro Hc; exfalso; apply Hc; reflexivity|].
    intro k; pattern k; apply Fin.caseS'; [intros _; reflexivity|].
    intro z; inversion z. }
  apply (fair_agaf_pool v u sch 2 1 Fin.F1 [worker 2 v; worker 1 u]%vector nl2 nl1 kb P eq_refl
    Hother
    HP focus st h allocs ctx c ns2 vs2 ns1 vs1 d2 d1 Hq2 Hq1 (Disj_sym _ _ _ _ Hdj) Hf2 Hf1).
Qed.
