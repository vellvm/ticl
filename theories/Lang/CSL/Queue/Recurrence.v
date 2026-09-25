(** * Recurrence: the heap-backed [AG AF] theorem and its freshness companion.

    The reference theorem is [examples/Queue.v], [rotate_agaf_pop]:

      find_index rel_dec nl q = Some i ->
      <( instr_prog rotate q, Pure |= AG AF visW {fun h => h = nl} )>

    over an ABSTRACT queue held in the interpretation state as a [list T].
    Here the queue is a preallocated linked structure in a heap, the pops are
    real heap reads, and the rotation is four real heap writes.

    The temporal proof uses two reusable structural iteration rules:

    - the outer [AG] needs NO adaptation.  [ICTree.Logic.State.ag_state_iter]
      takes an invariant [R i sigma w], and the abstract queue can be
      existentially quantified inside it.  There is no variant, so nothing
      has to be a function of the state.

    - the inner [AF] uses [ICTree.Logic.State.aul_state_iter_ghost].
      Its rank belongs to ghost queue data tied to the heap by the invariant;
      it need not be a function of the concrete heap or observation world. *)

From Stdlib Require Import
  List
  Lia
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

From TICL Require Import Lang.CSL.Queue.Representation Lang.CSL.Queue.Sequential
  Lang.CSL.Queue.Operations Utils.Relations.

From Coinduction Require Import coinduction.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.


(** ** The observation projection.

    [indexed_value] is the documented projection from the queue observation
    to the reference alphabet: the reference logs the (fun o => indexed_value o = payload), this
    language logs the (fun o => indexed_value o = payload) PLUS its occurrence index.  Erasing
    [indexed_index] recovers the reference formula exactly, and
    [indexed_after] adds the occurrence bound.

    A retained observation cannot masquerade as a later one: the world
    [Obs (Log (stamp v j)) tt] does NOT satisfy
    [indexed_after (fun x => x = nl) (S j)], so an [AF] of that formula
    cannot be discharged by the world already in hand.  That is
    [ICTree.Logic.Trace.indexed_excludes_retained], proved once for every
    payload and return type. *)


Section Recurrence.
  (** [hdr] is the queue header, [nl] the observed element, [kb] the occurrence
      bound, and [P] any observation predicate satisfied by every pop of [nl]
      at or after [kb].  Instantiating [kb := 0] gives the plain recurrence
      theorem; leaving [kb] free gives the freshness companion. *)
  Context (hdr nl kb: nat) (P: (indexed nat) -> Prop)
          (HP: forall j, Nat.le kb j -> P (stamp nl j)).

  (** The [AG] invariant: the state is a valid representation of SOME queue
      that still contains [nl].  The abstract queue is existentially
      quantified -- no extraction function from heaps to lists is needed. *)
  Definition Rq (_: unit) (s: Sig) (_: WorldW (indexed nat)) : Prop :=
    exists ns vs d, qrep hdr ns vs (fst s) /\ find_index Nat.eqb nl vs = Some d.

  (** *** One iteration, as a deterministic suffix formula.

      This is the only place the body is opened, and it is opened through
      [rot_body_spec] -- a bisimulation -- not by unfolding [auc]. *)
  Lemma body_det: forall ns vs a v h c w,
      qrep hdr (a :: ns) (v :: vs) h ->
      not_done w ->
      <[ {interp_state h_qE (rot_body hdr) (h, c)}, w
         |= ⊤ AU AX done= {(@inl unit unit tt,
                            (rot_heap hdr a (List.hd 0 ns) (zof hdr ns) h, S c))}
              {Obs (Log (stamp v c)) tt} ]>.
  Proof.
    intros ns vs a v h c w Hq Hd.
    rewrite (rot_body_spec hdr a ns v vs h c Hq).
    apply aur_log.
    - cleft; apply axr_ret; [constructor | split; reflexivity].
    - apply ticll_top; assumption.
  Qed.

  (** *** The inner eventuality.

      The ghost data is the rank [(kb - c, d)]: [c] is the private occurrence
      counter and [d] is the position of [nl] in the abstract queue.  Neither
      the heap nor the world appears in it.  The whole proof is ONE
      application of [aul_state_iter_ghost] plus a body case analysis. *)
  Definition InvQ (m: nat * nat) (_: unit) (s: Sig) : Prop :=
    exists ns vs d, qrep hdr ns vs (fst s)
               /\ find_index Nat.eqb nl vs = Some d
               /\ m = (kb - snd s, d).

  Lemma inner_af: forall h c ns vs d w,
      not_done w ->
      qrep hdr ns vs h ->
      find_index Nat.eqb nl vs = Some d ->
      <( {interp_state h_qE (rotate hdr) (h, c)}, w |= AF visW {P} )>.
  Proof.
    intros h c ns vs d w Hd Hq Hf.
    unfold rotate.
    apply (aul_state_iter_ghost h_qE lexnat InvQ (fun _: unit => rot_body hdr)
             _ _ lexnat_wf (kb - c, d) tt (h, c) w Hd).
    - exists ns, vs, d; split; [exact Hq | split; [exact Hf | reflexivity]].
    - clear h c ns vs d w Hd Hq Hf.
      intros m [] s w Hd (ns & vs & d & Hq & Hf & Hm).
      destruct s as (h, c); cbn in Hq, Hm.
      destruct vs as [| v vs']; [cbn in Hf; discriminate |].
      destruct ns as [| a ns']; [apply qrep_len in Hq; cbn in Hq; discriminate |].
      (* the shared "rotate once" step *)
      assert (Hstep: forall d', find_index Nat.eqb nl (vs' ++ [v]) = Some d' ->
                           lexnat (kb - S c, d') m ->
                           (exists g' i' s' w',
                               not_done w'
                               /\ <[ {interp_state h_qE
                                       ((fun _: unit => rot_body hdr) tt) (h, c)}, w
                                     |= ⊤ AU AX done= {(@inl unit unit i', s')} w' ]>
                               /\ InvQ g' i' s'
                               /\ lexnat g' m)).
      { intros d' Hd' Hlex.
        exists (kb - S c, d'), tt,
          (rot_heap hdr a (List.hd 0 ns') (zof hdr ns') h, S c),
          (Obs (Log (stamp v c)) tt).
        split; [constructor |].
        split; [eapply body_det; eassumption |].
        split; [| exact Hlex].
        exists (ns' ++ [a]), (vs' ++ [v]), d'; cbn; split;
          [apply (rot_heap_spec hdr a ns' v vs' h Hq)
          | split; [exact Hd' | reflexivity]]. }
      destruct d as [| d0].
      + (* the element is at the head *)
        pose proof (find_index_head Nat.eqb Nat.eqb_eq _ _ _ Hf) as Hv; subst v.
        destruct (Nat.le_gt_cases kb c) as [Hle | Hgt].
        * (* and the occurrence bound is already met: observe it now *)
          left.
          rewrite (rot_body_spec hdr a ns' nl vs' h c Hq).
          apply afl_log; [assumption |].
          cleft; apply ticll_vis; constructor; now apply HP.
        * (* the bound is not met yet: rotate, the bound gets closer *)
          right.
          destruct (find_index_last_ex Nat.eqb Nat.eqb_eq nl vs') as (d' & Hd').
          apply (Hstep d'); [exact Hd' | rewrite Hm; left; cbn; lia].
      + (* the element is deeper in the queue: rotate, it gets closer *)
        right.
        apply (Hstep d0).
        * rewrite <- rotl_cons; eapply find_index_rotl; exact Hf.
        * rewrite Hm; destruct (Nat.le_gt_cases kb c);
            [right; cbn; split; lia | left; cbn; lia].
  Qed.

  (** *** The recurrence theorem. *)
  Theorem rotate_agaf_core: forall h c ns vs d w,
      not_done w ->
      qrep hdr ns vs h ->
      find_index Nat.eqb nl vs = Some d ->
      <( {interp_state h_qE (rotate hdr) (h, c)}, w |= AG (AF visW {P}) )>.
  Proof.
    intros h c ns vs d w Hd Hq Hf.
    unfold rotate.
    apply (ag_state_iter h_qE (h, c) Rq tt w); [assumption | |].
    - exists ns, vs, d; split; assumption.
    - intros [] s w' Hd' (ns1 & vs1 & d1 & Hq1 & Hf1).
      destruct s as (h1, c1); cbn in Hq1.
      destruct vs1 as [| v1 vs1']; [cbn in Hf1; discriminate |].
      destruct ns1 as [| a1 ns1'];
        [apply qrep_len in Hq1; cbn in Hq1; discriminate |].
      split.
      + eapply inner_af; [exact Hd' | exact Hq1 | exact Hf1].
      + rewrite (rot_body_spec hdr a1 ns1' v1 vs1' h1 c1 Hq1).
        apply anr_log; [| apply ticll_top; assumption].
        cleft; apply axr_ret; [constructor |].
        exists tt; split; [reflexivity | split; [constructor |]].
        destruct (find_index_rotl_pres Nat.eqb Nat.eqb_eq _ _ _ _ Hf1) as (d' & Hd'').
        exists (ns1' ++ [a1]), (vs1' ++ [v1]), d'; split.
        * apply (rot_heap_spec hdr a1 ns1' v1 vs1' h1 Hq1).
        * rewrite <- rotl_cons; exact Hd''.
  Qed.
End Recurrence.

(** ** The two headline theorems.

    [rotate_agaf_pop_heap] is the heap-backed counterpart of the reference
    [rotate_agaf_pop]: same modal shape, same natural position argument, same
    pure [find_index] lemmas, but over owned heap nodes.

    [rotate_agaf_pop_fresh] is what the reference formula does NOT give: for
    every occurrence bound [k], every reachable state still eventually
    produces a pop of [nl] whose index is at least [k].  Since indices are
    strictly increasing and each observation carries its own, this cannot be
    discharged by a retained world ([fresh_excludes_retained]). *)

Theorem rotate_agaf_pop_heap: forall hdr nl h c ns vs d,
    qrep hdr ns vs h ->
    find_index Nat.eqb nl vs = Some d ->
    <( {run hdr h c}, Pure |= AG (AF visW {(fun o => indexed_value o = nl)}) )>.
Proof.
  intros hdr nl h c ns vs d Hq Hf.
  unfold run.
  eapply (rotate_agaf_core hdr nl 0 ((fun o => indexed_value o = nl)));
    [ intros j _; reflexivity | constructor | exact Hq | exact Hf ].
Qed.

Theorem rotate_agaf_pop_fresh: forall hdr nl h c ns vs d k,
    qrep hdr ns vs h ->
    find_index Nat.eqb nl vs = Some d ->
    <( {run hdr h c}, Pure |= AG (AF visW {(indexed_after (fun x => x = nl) k)}) )>.
Proof.
  intros hdr nl h c ns vs d k Hq Hf.
  unfold run.
  eapply (rotate_agaf_core hdr nl k ((indexed_after (fun x => x = nl) k)));
    [ intros j Hj; split; [reflexivity | exact Hj] | constructor | exact Hq | exact Hf ].
Qed.

(** ** Precondition controls.

    The recurrence theorem's hypotheses are not decoration.  Both controls are
    about the SAFE handler: an out-of-footprint dereference is stuck, and a
    stuck state satisfies no [AG] formula. *)

(** *** Control 1: the EMPTY queue.

    The head pointer is null, the null address is not allocated, so the first
    dereference of the body is out of footprint.  The run cannot step at all,
    hence NO [AG] formula holds of it -- in particular not the recurrence
    formula.  This is what the hypothesis [find_index Nat.eqb nl vs = Some d] (which forces
    a non-empty queue) buys. *)
Theorem empty_queue_no_ag: forall hdr h c vs w phi,
    qrep hdr [] vs h -> ~ <( {run hdr h c}, w |= AG phi )>.
Proof.
  intros hdr h c vs w phi Hq H.
  pose proof Hq as (Hwf & Hhd & _ & _ & _); cbn in Hhd.
  pose proof (qrep_null _ _ _ _ Hq) as H0.
  assert (Hns: ~ can_step (run hdr h c) w).
  { unfold run, rotate, h_qE; rewrite interp_state_unfold_iter.
    apply nostep_bind.
    unfold rot_body, queue_turn.
    rewrite (interp_heap_rd (h_indexed (A:=nat) (Sigma:=Heap))
      (S hdr) h c 0 _ Hhd).
    now apply (interp_heap_rd_nostep (h_indexed (A:=nat) (Sigma:=Heap))). }
  cdestruct H; now apply Hns.
Qed.

(** *** Control 2: an ABSENT element is never observed.

    Rotation permutes the queue, so every logged payload is a member of the
    INITIAL payload list.  Consequently, if [nl] does not occur initially, the
    atom of the recurrence formula is false at every reachable state.  The
    statement below is the [AG] invariance; deriving [~ AF] from [AG ~] is the
    standard duality and is NOT mechanised here. *)

Definition obs_sat (Q: nat -> Prop) : WorldW (indexed nat) -> Prop :=
  fun w => forall o, w = Obs (Log o) tt -> Q (indexed_value o).

Theorem rotate_ag_obs: forall hdr h c ns vs w (Q: nat -> Prop),
    (forall x, In x vs -> Q x) ->
    not_done w ->
    qrep hdr ns vs h ->
    ns <> [] ->
    obs_sat Q w ->
    <( {interp_state h_qE (rotate hdr) (h, c)}, w |= AG (now {obs_sat Q}) )>.
Proof.
  intros hdr h c ns vs w Q HQ Hd Hq Hne Hw.
  unfold rotate.
  apply (ag_state_iter h_qE (h, c)
           (fun (_: unit) (s: Sig) (w: WorldW (indexed nat)) =>
              (exists ns' vs', qrep hdr ns' vs' (fst s) /\ ns' <> []
                          /\ (forall x, In x vs' -> Q x))
              /\ obs_sat Q w)
           tt w); [assumption | |].
  - split; [exists ns, vs; split; [exact Hq | split; [exact Hne | exact HQ]]
           | exact Hw].
  - intros [] s w' Hd' ((ns1 & vs1 & Hq1 & Hne1 & Hin1) & Hw').
    destruct s as (h1, c1); cbn in Hq1.
    destruct ns1 as [| a1 ns1']; [contradiction |].
    destruct vs1 as [| v1 vs1']; [apply qrep_len in Hq1; cbn in Hq1; discriminate |].
    assert (Hv1: Q v1) by (apply Hin1, in_eq).
    split.
    + apply ticll_now; split; assumption.
    + rewrite (rot_body_spec hdr a1 ns1' v1 vs1' h1 c1 Hq1).
      apply anr_log; [| apply ticll_top; assumption].
      cleft; apply axr_ret; [constructor |].
      exists tt; split; [reflexivity | split; [constructor |]].
      split.
      * exists (ns1' ++ [a1]), (vs1' ++ [v1]); split;
          [apply (rot_heap_spec hdr a1 ns1' v1 vs1' h1 Hq1) | split].
        -- intro C; apply app_eq_nil in C as (_ & C); discriminate.
        -- intros x Hx; apply in_app_iff in Hx as [Hx | [Hx | []]];
             [apply Hin1, in_cons; exact Hx | subst; exact Hv1].
      * intros o Ho; inversion Ho; subst; cbn; exact Hv1.
Qed.

(** The control itself: an element outside the initial queue is never the
    payload of any observation. *)
Corollary absent_never_observed: forall hdr h c ns vs nl,
    qrep hdr ns vs h ->
    ns <> [] ->
    ~ In nl vs ->
    <( {run hdr h c}, Pure |= AG (now {obs_sat (fun x => x <> nl)}) )>.
Proof.
  intros hdr h c ns vs nl Hq Hne Hnin.
  unfold run.
  apply (rotate_ag_obs hdr h c ns vs Pure (fun x => x <> nl));
    [ intros x Hx C; subst; contradiction
    | constructor | exact Hq | exact Hne
    | intros o Ho; discriminate ].
Qed.
