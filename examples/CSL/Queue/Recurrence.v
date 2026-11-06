(** * Recurrence: the heap-backed [AG AF] theorem and its freshness companion.

    The reference theorem is [examples/Queue.v], [rotate_agaf_pop]:

      find_index rel_dec nl q = Some i ->
      <( instr_prog rotate q, Pure |=L AG AF visW {fun h => h = nl} )>

    over an ABSTRACT queue held in the interpretation state as a [list T].
    Here the queue is a preallocated linked structure in a heap, the pops are
    real heap reads, and the rotation is four real heap writes.

    The outer [AG] uses continuation-aware [ag_state_iter_logs]: every pending
    heap snapshot retains the actual next iteration.  The inner [AF] keeps
    [u_state_iter_prefix_ghost], whose rank belongs to ghost queue data tied to
    the heap by the invariant. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat
  Arith.Wf_nat
  Relations.
From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Interp.State.Mod
  CTree.Events.State
  CTree.Events.Writer
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.Bind
  CTree.Logic.Iter
  CTree.Logic.State
  Logic.Core
  CTree.Logic.Trace.

From examples Require Import CSL.Queue.Representation CSL.Queue.Sequential
  CSL.Queue.Operations.
From TICL Require Import Utils.Relations.


Import CTree CTreeNotations TiclNotations ListNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.


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
    [CTree.Logic.Trace.indexed_excludes_retained], proved once for every
    payload and return type. *)


Section Recurrence.
  (** [hdr] is the queue header, [nl] the observed element, [kb] the occurrence
      bound, and [P] any observation predicate satisfied by every pop of [nl]
      at or after [kb].  Instantiating [kb := 0] gives the plain recurrence
      theorem; leaving [kb] free gives the freshness companion. *)
  Context (hdr nl kb: nat) (P: (indexed nat) -> Prop)
          (HP: forall j, Nat.le kb j -> P (stamp nl j)).

  (** *** The recurrence theorem.

      [ag_state_iter_logs] keeps the exact continuation under every pending
      snapshot. At each loop boundary, [u_state_iter_prefix_ghost] proves the
      eventuality with the inline rank [(kb - counter, first-match position)].
      [find_index_rotation_progress] permits duplicate payloads; the body is
      exposed only through [rot_body_spec]. *)
  Theorem rotate_agaf_core: forall h allocs ctx c ns vs d w,
      not_done w ->
      qrep hdr ns vs h ->
      find_index Nat.eqb nl vs = Some d ->
      <( {interp_state (sh (A:=nat)) (rotate hdr) ((h, allocs), (ctx, c))}, w |=L AG (AF visW {csl_indexed P}) )>.
  Proof.
    intros h allocs ctx c ns vs d w Hd Hq Hf.
    unfold rotate.
    eapply (ag_state_iter_logs (sh (A:=nat)) (X:=unit)
      (fun (_ : unit) (s : SSig) =>
        exists ns vs d, qrep hdr ns vs (fst (fst s)) /\
          find_index Nat.eqb nl vs = Some d)
      (fun _ : unit => rot_body hdr) <( AF visW {csl_indexed P} )>).
    - intros [] ((h1,allocs1),(ctx1,c1)) (ns1 & vs1 & d1 & Hq1 & Hf1).
      cbn in Hq1.
      destruct vs1 as [|v1 vs1']; [cbn in Hf1; discriminate|].
      destruct ns1 as [|a1 ns1'];
        [apply qrep_len in Hq1; cbn in Hq1; discriminate|].
      destruct (find_index_rotl_pres Nat.eqb Nat.eqb_eq _ _ _ _ Hf1) as (d' & Hd'').
      exists tt,
        ((rot_heap hdr a1 (List.hd 0 ns1') (zof hdr ns1') h1,allocs1),(ctx1,S c1)),
        (queue_turn_logs (CSLEmit (stamp v1 c1)) hdr a1
          (List.hd 0 ns1') (last (a1 :: ns1') 0) (h1,allocs1)).
      split; [discriminate|split;
        [exact (rot_body_spec hdr a1 ns1' v1 vs1' h1 allocs1 ctx1 c1 Hq1)|]].
      exists (ns1' ++ [a1]), (vs1' ++ [v1]), d'; split.
      + exact (proj1 (rot_heap_spec hdr a1 ns1' v1 vs1' h1 Hq1)).
      + rewrite <- rotl_cons; exact Hd''.
    - intros o t w' Hw Hphi.
      pose proof (af_log (b:=false) o t w' _ Hw Hphi) as Hlog.
      rewrite log_vis in Hlog; exact Hlog.
    - intros [] ((h1,allocs1),(ctx1,c1)) w' (ns1 & vs1 & d1 & Hq1 & Hf1) Hw.
      eapply (u_state_iter_prefix_ghost (sh (A:=nat)) Q_A
        (fun m (_ : unit) (s : SSig) z =>
          not_done z /\ exists ns vs d,
            qrep hdr ns vs (fst (fst s)) /\
            find_index Nat.eqb nl vs = Some d /\
            m = (kb - csl_counter s, d))
        lexnat (fun _ : unit => rot_body hdr) _ _ lexnat_wf)
        with (g := (kb - c1, d1)).
      2: exact Hw.
      2: { split; [exact Hw|].
           exists ns1, vs1, d1; split; [exact Hq1|].
           split; [exact Hf1|reflexivity]. }
      clear h allocs ctx c ns vs d w Hd Hq Hf h1 allocs1 ctx1 c1
        ns1 vs1 d1 w' Hq1 Hf1 Hw.
      intros m [] ((h2,allocs2),(ctx2,c2)) w2 Hd2
        (Hlive & ns2 & vs2 & d2 & Hq2 & Hf2 & Hm).
      cbn in Hq2, Hm.
      destruct vs2 as [|v2 vs2']; [cbn in Hf2; discriminate|].
      destruct ns2 as [|a2 ns2'];
        [apply qrep_len in Hq2; cbn in Hq2; discriminate|].
      destruct (find_index_rotation_progress Nat.eqb Nat.eqb_eq nl v2 vs2' d2
        Hf2 kb c2) as (d' & Hf' & [[Hv Hbound]|Hrank]).
      + left; subst v2.
        ticl_normalize.
        rewrite (rot_body_spec hdr a2 ns2' nl vs2' h2 allocs2 ctx2 c2 Hq2).
        eapply af_emit_list_member with (o:=CSLEmit (stamp nl c2)).
        * exact Hd2.
        * unfold queue_turn_logs; apply in_eq.
        * cbn; now apply HP.
      + right.
        ticl_normalize.
        rewrite (rot_body_spec hdr a2 ns2' v2 vs2' h2 allocs2 ctx2 c2 Hq2).
        apply af_emit_list_ret; [exact Hd2|].
        exists (kb - S c2, d'), tt; split; [reflexivity|].
        split; [apply after_logs_not_done; exact Hd2|].
        split.
        * split; [apply after_logs_not_done; exact Hd2|].
          exists (ns2' ++ [a2]), (vs2' ++ [v2]), d'; cbn; split.
          -- apply (rot_heap_spec hdr a2 ns2' v2 vs2' h2 Hq2).
          -- split; [rewrite <- rotl_cons; exact Hf'|reflexivity].
        * rewrite Hm; exact Hrank.
    - exists ns, vs, d; split; assumption.
    - exact Hd.
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
    discharged by a retained world ([indexed_excludes_retained]). *)

Theorem rotate_agaf_pop_heap: forall hdr nl h allocs ctx c ns vs d,
    qrep hdr ns vs h ->
    find_index Nat.eqb nl vs = Some d ->
    <( {run hdr ((h, allocs), (ctx, c))}, Pure |=L AG (AF visW {csl_indexed (fun o => indexed_value o = nl)}) )>.
Proof.
  intros hdr nl h allocs ctx c ns vs d Hq Hf.
  unfold run.
  eapply (rotate_agaf_core hdr nl 0 ((fun o => indexed_value o = nl)));
    [ intros j _; reflexivity | constructor | exact Hq | exact Hf ].
Qed.

Theorem rotate_agaf_pop_fresh: forall hdr nl h allocs ctx c ns vs d k,
    qrep hdr ns vs h ->
    find_index Nat.eqb nl vs = Some d ->
    <( {run hdr ((h, allocs), (ctx, c))}, Pure |=L AG (AF visW {csl_indexed (indexed_after (fun x => x = nl) k)}) )>.
Proof.
  intros hdr nl h allocs ctx c ns vs d k Hq Hf.
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
Theorem empty_queue_no_ag: forall hdr h allocs ctx c vs w phi,
    qrep hdr [] vs h -> ~ <( {run hdr ((h, allocs), (ctx, c))}, w |=L AG phi )>.
Proof.
  intros hdr h allocs ctx c vs w phi Hq H.
  pose proof Hq as (Hwf & Hhd & _ & _ & _); cbn in Hhd.
  pose proof (qrep_null _ _ _ _ Hq) as H0.
  assert (Hns: ~ can_step (run hdr ((h, allocs), (ctx, c))) w).
  { unfold run, rotate, sh; rewrite interp_state_unfold_iter.
    apply nostep_bind.
    unfold rot_body, queue_turn.
    rewrite (interp_heapW_rd CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat)))
      (S hdr) h allocs (ctx, c) 0 _ Hhd).
    rewrite (interp_heapW_rd_missing CSLHeap
      (h_sum csl_context_handler (csl_emit_handler (A:=nat))) 0 h allocs (ctx,c) _ H0).
    apply can_step_stuck. }
  cdestruct H; now apply Hns.
Qed.

(** *** Control 2: an ABSENT element is never observed.

    Rotation permutes the queue, so every logged payload is a member of the
    INITIAL payload list.  Consequently, if [nl] does not occur initially, the
    atom of the recurrence formula is false at every reachable state.  The
    statement below is the [AG] invariance; deriving [~ AF] from [AG ~] is the
    standard duality and is NOT mechanised here. *)

Definition obs_sat (Q: nat -> Prop) : WorldW (CSLObs nat) -> Prop :=
  fun w => forall o, w = Obs (Log (CSLEmit o)) tt -> Q (indexed_value o).

Theorem rotate_ag_obs: forall hdr h allocs ctx c ns vs w (Q: nat -> Prop),
    (forall x, In x vs -> Q x) ->
    not_done w ->
    qrep hdr ns vs h ->
    ns <> [] ->
    obs_sat Q w ->
    <( {interp_state (sh (A:=nat)) (rotate hdr) ((h, allocs), (ctx, c))}, w |=L AG (now {obs_sat Q}) )>.
Proof.
  intros hdr h allocs ctx c ns vs w Q HQ Hd Hq Hne Hw.
  unfold rotate.
  apply (ag_state_iter (sh (A:=nat)) ((h, allocs), (ctx, c))
           (fun (_: unit) (s: SSig) (w: WorldW (CSLObs nat)) =>
              (exists ns' vs', qrep hdr ns' vs' (fst (fst s)) /\ ns' <> []
                          /\ (forall x, In x vs' -> Q x))
              /\ obs_sat Q w)
           tt w); [assumption | |].
  - split; [exists ns, vs; split; [exact Hq | split; [exact Hne | exact HQ]]
           | exact Hw].
  - intros [] s w' Hd' ((ns1 & vs1 & Hq1 & Hne1 & Hin1) & Hw').
    destruct s as ((h1, allocs1), (ctx1, c1)); cbn in Hq1.
    destruct ns1 as [| a1 ns1']; [contradiction |].
    destruct vs1 as [| v1 vs1']; [apply qrep_len in Hq1; cbn in Hq1; discriminate |].
    assert (Hv1: Q v1) by (apply Hin1, in_eq).
    split.
    + apply ticl_now; split; assumption.
    + ticl_normalize; rewrite (rot_body_spec hdr a1 ns1' v1 vs1' h1 allocs1 ctx1 c1 Hq1).
      unfold queue_turn_logs; cbn [fst snd emit_list List.fold_right].
      apply (an_log (b:=true)); [|apply ticll_top; exact Hd'].
      do 4 (apply (au_log (b:=true)); [|apply ticl_now; split;
        [intros o Ho; inversion Ho; subst; cbn; exact Hv1|constructor]]).
      cleft; apply ret_ret; [constructor|].
      exists tt; split; [reflexivity|split; [constructor|]].
      split.
      * exists (ns1' ++ [a1]), (vs1' ++ [v1]); split;
          [apply (rot_heap_spec hdr a1 ns1' v1 vs1' h1 Hq1)|split].
        -- intro C; apply app_eq_nil in C as (_ & C); discriminate.
        -- intros x Hx; apply in_app_iff in Hx as [Hx|[Hx|[]]];
             [apply Hin1, in_cons; exact Hx|subst; exact Hv1].
      * intros o Ho; discriminate.
Qed.

(** The control itself: an element outside the initial queue is never the
    payload of any observation. *)
Corollary absent_never_observed: forall hdr h allocs ctx c ns vs nl,
    qrep hdr ns vs h ->
    ns <> [] ->
    ~ In nl vs ->
    <( {run hdr ((h, allocs), (ctx, c))}, Pure |=L AG (now {obs_sat (fun x => x <> nl)}) )>.
Proof.
  intros hdr h allocs ctx c ns vs nl Hq Hne Hnin.
  unfold run.
  apply (rotate_ag_obs hdr h allocs ctx c ns vs Pure (fun x => x <> nl));
    [ intros x Hx C; subst; contradiction
    | constructor | exact Hq | exact Hne
    | intros o Ho; discriminate ].
Qed.
