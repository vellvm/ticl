(** * Shared: one finite heap queue rotated forever by two spawned workers.

    Both workers of [shared_queue] rotate the SAME queue.  Each scheduled turn
    of either worker is an exact first-yield source segment that logs one pop
    and rotates the queue once ([exact_worker_turn]).  The invariant/variant
    certificate [shared_worker_turn] is the queue's standard rank argument,
    stated per worker slot so that it is independent of which worker the
    scheduler selects. *)

From Stdlib Require Import List Lia Arith.PeanoNat.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.Events.Writer Events.WriterE
  ICTree.Interp.Yield.Segments Lang.CSL.Mod Utils.Lists Utils.Relations
  ICTree.Logic.Yield ICTree.Logic.AG ICTree.SBisim ICTree.Interp.Refine
  ICTree.Interp.Yield.Mod ICTree.Interp.Yield.RoundRobin ICTree.Logic.State Logic.Core.
From examples Require Import CSL.Queue.Representation CSL.Queue.Program
  CSL.Queue.Trace CSL.Queue.Layout CSL.Queue.Frame.

Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope list_scope.

(** ** One worker turn as an exact source segment. *)

Lemma exact_worker_turn : forall tag hdr a ns v vs h allocs ctx c,
  qrep hdr (a :: ns) (v :: vs) h ->
  segment_to sh csl_equ (denote (worker tag hdr))
    ((h,allocs),(ctx,c)) [inr (stamp (tag,v) c)]
    (denote (worker tag hdr))
    ((rot_heap hdr a (List.hd 0 ns) (zof hdr ns) h,allocs),(ctx,S c)).
Proof.
  intros tag hdr a ns v vs h allocs ctx c Hq.
  pose proof Hq as (Hwf & Hhd & Htl & Hch & Hdom).
  cbn in Hhd, Htl.
  apply chain_cons in Hch as (Ha & Hsa & Hch).
  pose proof (qwf_neqs _ _ _ Hwf) as (Hha & Hsha & Hhsa & Hshsa & Hhshdr).
  pose proof (qrep_zof_dom _ _ _ _ _ _ Hq) as Hzdom.
  assert (Hhdrdom : h hdr <> None) by (rewrite Htl; discriminate).
  assert (Hsadom : h (S a) <> None) by (rewrite Hsa; discriminate).
  assert (Hshdrdom : h (S hdr) <> None) by (rewrite Hhd; discriminate).
  assert (Hread_hdr : upd h (S hdr) (List.hd 0 ns) hdr = Some (last (a :: ns) 0))
    by (rewrite upd_neq by congruence; exact Htl).
  unfold denote, worker.
  apply exact_source_until.
  apply exact_source_bind.
  unfold rotate_once.
  apply exact_source_bind; eapply exact_source_read; [exact Hhd|]; cbn beta iota.
  apply exact_source_bind; eapply exact_source_read; [exact Ha|]; cbn beta iota.
  apply exact_source_bind; apply exact_source_emit; cbn beta iota.
  apply exact_source_bind; eapply exact_source_read; [exact Hsa|]; cbn beta iota.
  apply exact_source_bind; apply exact_source_write; [exact Hshdrdom|]; cbn beta iota.
  apply exact_source_bind; eapply exact_source_read; [exact Hread_hdr|]; cbn beta iota.
  rewrite (zof_compute hdr a ns Hwf).
  apply exact_source_bind; apply exact_source_write; [now apply upd_mono|];
    cbn beta iota.
  apply exact_source_bind; apply exact_source_write; [now apply upd_mono, upd_mono|];
    cbn beta iota.
  apply exact_source_write; [now apply upd_mono, upd_mono, upd_mono|]; cbn beta iota.
  apply exact_source_bind; apply exact_source_yield.
  eapply guard_equ_trans; [apply guard_equ_equ, source_raw_ret|].
  cbn [until_tail]; apply guard_equ_left, guard_equ_equ; reflexivity.
Qed.

(** ** Observation targets and the shared-queue invariant. *)

Definition shared_pop (nl : nat) : CSLObs (nat * nat) -> Prop :=
  csl_indexed (fun o => snd (indexed_value o) = nl).

Definition shared_pop_after (nl k : nat) : CSLObs (nat * nat) -> Prop :=
  csl_indexed (indexed_after (fun p => snd p = nl) k).

Definition SharedInv (hdr nl k : nat) (g : nat * nat) (s : SSig) : Prop :=
  exists ns vs d,
    qrep hdr ns vs (fst (csl_memory s)) /\
    find_index Nat.eqb nl vs = Some d /\
    g = (k - csl_counter s, d).

(** Either worker's turn preserves the invariant and either meets the target
    or strictly decreases the rank [(k - counter, position of nl)]. *)
Lemma shared_worker_turn : forall tag hdr nl k g s,
  SharedInv hdr nl k g s ->
  exists g' s' o,
    segment_to sh csl_equ (denote (worker tag hdr)) s [o]
      (denote (worker tag hdr)) s' /\
    SharedInv hdr nl k g' s' /\
    (shared_pop_after nl k o \/ lexnat g' g).
Proof.
  intros tag hdr nl k g s (ns & vs & d & Hq & Hf & Hg).
  destruct s as ((h, allocs), (ctx, c)); cbn in Hq, Hg; subst g.
  destruct vs as [| v vs']; [cbn in Hf; discriminate |].
  destruct ns as [| a ns']; [apply qrep_len in Hq; cbn in Hq; discriminate |].
  set (s' := ((rot_heap hdr a (List.hd 0 ns') (zof hdr ns') h, allocs), (ctx, S c))).
  assert (Hstep : forall d', find_index Nat.eqb nl (vs' ++ [v]) = Some d' ->
    SharedInv hdr nl k (k - S c, d') s').
  { intros d' Hd'; exists (ns' ++ [a]), (vs' ++ [v]), d'; cbn; split;
      [apply (rot_heap_spec hdr a ns' v vs' h Hq) | split; [exact Hd' | reflexivity]]. }
  pose proof (exact_worker_turn tag hdr a ns' v vs' h allocs ctx c Hq) as Hturn.
  destruct d as [| d0].
  - pose proof (find_index_head Nat.eqb Nat.eqb_eq _ _ _ Hf) as Hv; subst v.
    destruct (find_index_last_ex Nat.eqb Nat.eqb_eq nl vs') as (d' & Hd').
    exists (k - S c, d'), s', (inr (stamp (tag, nl) c)).
    split; [exact Hturn |]; split; [now apply Hstep |].
    destruct (Nat.le_gt_cases k c) as [Hle | Hgt].
    + left; cbn; split; [reflexivity | exact Hle].
    + right; left; cbn; lia.
  - pose proof (find_index_rotl Nat.eqb nl v vs' d0 Hf) as Hd0.
    rewrite rotl_cons in Hd0.
    exists (k - S c, d0), s', (inr (stamp (tag, v) c)).
    split; [exact Hturn |]; split; [now apply Hstep |].
    right; destruct (Nat.le_gt_cases k c);
      [right; cbn; split; lia | left; cbn; lia].
Qed.

(** Invariant closure alone, without the rank. *)
Corollary shared_worker_closed : forall tag hdr nl k g s,
  SharedInv hdr nl k g s ->
  exists g' s' o,
    segment_to sh csl_equ (denote (worker tag hdr)) s [o]
      (denote (worker tag hdr)) s' /\
    SharedInv hdr nl k g' s'.
Proof.
  intros tag hdr nl k g s Hinv.
  destruct (shared_worker_turn tag hdr nl k g s Hinv) as (g' & s' & o & Hseg & Hinv' & _).
  exists g', s', o; split; assumption.
Qed.

(** ** The two-worker pool and its turn certificates.

    After both forks the parent has terminated and the pool is
    [worker 2 hdr; worker 1 hdr].  Either slot closes a turn from every
    invariant state, so neither the nondeterministic nor the round-robin
    proof needs a fairness or phase argument. *)

Import Vector.VectorNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Lemma shared_ranked hdr nl k :
  RankedTurns sh (csl_pool [worker 2 hdr; worker 1 hdr]%vector)
    (SharedInv hdr nl k) (fun g => g) lexnat (shared_pop_after nl k).
Proof.
  intros g s i Hinv; pattern i; apply Fin.caseS'.
  - exact (shared_worker_turn 2 hdr nl k g s Hinv).
  - intro j; pattern j; apply Fin.caseS'.
    + exact (shared_worker_turn 1 hdr nl k g s Hinv).
    + intro z; inversion z.
Qed.

(** Plain recurrence uses the same certificate at occurrence bound [0]. *)
Lemma shared_ranked_pop hdr nl :
  RankedTurns sh (csl_pool [worker 2 hdr; worker 1 hdr]%vector)
    (SharedInv hdr nl 0) (fun g => g) lexnat (shared_pop nl).
Proof.
  intros g s i Hinv.
  destruct (shared_ranked hdr nl 0 g s i Hinv)
    as (g' & s' & o & Hseg & Hinv' & [HP|Hlt]);
    exists g', s', o; split; [exact Hseg| |exact Hseg|];
    split; try exact Hinv'.
  - left; destruct o as [ctx|o]; [destruct HP|exact (proj1 HP)].
  - right; exact Hlt.
Qed.

Lemma shared_pool_agaf_nd hdr nl k g s (P : CSLObs (nat * nat) -> Prop) :
  RankedTurns sh (csl_pool [worker 2 hdr; worker 1 hdr]%vector)
    (SharedInv hdr nl k) (fun g => g) lexnat P ->
  SharedInv hdr nl k g s ->
  <( {run_nd_pool [worker 2 hdr; worker 1 hdr]%vector None s}, Pure
     |= AG (AF visW {P}) )>.
Proof.
  intros Hranked Hinv.
  apply (ag_csl_nd_invariance _ (SharedInv hdr nl k) _
    (ranked_turns_closed sh _ _ _ _ _ Hranked)) with (g := g);
    [|exact Hinv|constructor].
  intros g0 s0 focus w Hinv0 Hw.
  exact (aul_csl_nd_eventually _ _ (fun g => g) lexnat P lexnat_wf Hranked
    g0 s0 focus w Hinv0 Hw).
Qed.

Lemma shared_pool_agaf_rr hdr nl k g s cursor (P : CSLObs (nat * nat) -> Prop) :
  RankedTurns sh (csl_pool [worker 2 hdr; worker 1 hdr]%vector)
    (SharedInv hdr nl k) (fun g => g) lexnat P ->
  SharedInv hdr nl k g s ->
  <( {run_rr_pool [worker 2 hdr; worker 1 hdr]%vector None cursor s}, Pure
     |= AG (AF visW {P}) )>.
Proof.
  intros Hranked Hinv.
  apply (ag_csl_rr_invariance _ (SharedInv hdr nl k) _
    (ranked_turns_closed sh _ _ _ _ _ Hranked)) with (g := g);
    [|exact Hinv|constructor].
  intros g0 s0 focus c0 w Hinv0 Hw.
  exact (aul_csl_rr_eventually _ _ (fun g => g) lexnat P lexnat_wf Hranked
    g0 s0 focus c0 w Hinv0 Hw).
Qed.

(** ** Recurrence of the actual shared program from a represented queue. *)

Theorem shared_rotate_agaf_pop_nd_fresh : forall hdr nl h allocs ctx c ns vs d k,
  qrep hdr ns vs h -> find_index Nat.eqb nl vs = Some d ->
  <( {run_nd (shared_queue hdr) ((h,allocs),(ctx,c))}, Pure
     |= AG (AF visW {shared_pop_after nl k}) )>.
Proof.
  intros hdr nl h allocs ctx c ns vs d k Hq Hf.
  unfold shared_queue; rewrite run_nd_two_forks.
  apply (shared_pool_agaf_nd hdr nl k (k - c, d)); [apply shared_ranked|].
  exists ns, vs, d; split; [exact Hq|split; [exact Hf|reflexivity]].
Qed.

Theorem shared_rotate_agaf_pop_rr_fresh : forall hdr nl h allocs ctx c ns vs d k,
  qrep hdr ns vs h -> find_index Nat.eqb nl vs = Some d ->
  <( {run_rr (shared_queue hdr) ((h,allocs),(ctx,c))}, Pure
     |= AG (AF visW {shared_pop_after nl k}) )>.
Proof.
  intros hdr nl h allocs ctx c ns vs d k Hq Hf.
  unfold shared_queue; rewrite run_rr_two_forks.
  apply (shared_pool_agaf_rr hdr nl k (k - c, d)); [apply shared_ranked|].
  exists ns, vs, d; split; [exact Hq|split; [exact Hf|reflexivity]].
Qed.

Theorem shared_rotate_agaf_pop_nd : forall hdr nl h allocs ctx c ns vs d,
  qrep hdr ns vs h -> find_index Nat.eqb nl vs = Some d ->
  <( {run_nd (shared_queue hdr) ((h,allocs),(ctx,c))}, Pure
     |= AG (AF visW {shared_pop nl}) )>.
Proof.
  intros hdr nl h allocs ctx c ns vs d Hq Hf.
  unfold shared_queue; rewrite run_nd_two_forks.
  apply (shared_pool_agaf_nd hdr nl 0 (0 - c, d)); [apply shared_ranked_pop|].
  exists ns, vs, d; split; [exact Hq|split; [exact Hf|reflexivity]].
Qed.

Theorem shared_rotate_agaf_pop_rr : forall hdr nl h allocs ctx c ns vs d,
  qrep hdr ns vs h -> find_index Nat.eqb nl vs = Some d ->
  <( {run_rr (shared_queue hdr) ((h,allocs),(ctx,c))}, Pure
     |= AG (AF visW {shared_pop nl}) )>.
Proof.
  intros hdr nl h allocs ctx c ns vs d Hq Hf.
  unfold shared_queue; rewrite run_rr_two_forks.
  apply (shared_pool_agaf_rr hdr nl 0 (0 - c, d)); [apply shared_ranked_pop|].
  exists ns, vs, d; split; [exact Hq|split; [exact Hf|reflexivity]].
Qed.

(** ** The allocated program. *)

Lemma allocated_shared_queue_rep values :
  qrep 1 (queue_nodes 1 (length values)) values (new_queue_heap 1 values hemp).
Proof.
  pose proof (qheap_queue_nodes_rep 1 values ltac:(lia)) as Hq.
  pose proof (new_queue_heap_agrees 1 values hemp ltac:(lia)
    ltac:(intros offset _; reflexivity)) as Hagree.
  apply (qrep_agree_fp 1 _ _ _ _ Hq).
  - intros x _; rewrite (Hagree x); unfold hunion, hemp.
    destruct (qheap 1 (queue_nodes 1 (length values)) values x); reflexivity.
  - rewrite (Hagree 0); unfold hunion; rewrite (qrep_null _ _ _ _ Hq); reflexivity.
Qed.

Theorem shared_rotate_agaf_pop_alloc_nd : forall values nl ctx c d,
  find_index Nat.eqb nl values = Some d ->
  <( {run_nd (allocated_shared_queue values) (managed_empty,(ctx,c))}, Pure
     |= AG (AF visW {shared_pop nl}) )>.
Proof.
  intros values nl ctx c d Hf; rewrite run_nd_allocated_shared_queue.
  eapply shared_rotate_agaf_pop_nd; [apply allocated_shared_queue_rep|exact Hf].
Qed.

Theorem shared_rotate_agaf_pop_alloc_rr : forall values nl ctx c d,
  find_index Nat.eqb nl values = Some d ->
  <( {run_rr (allocated_shared_queue values) (managed_empty,(ctx,c))}, Pure
     |= AG (AF visW {shared_pop nl}) )>.
Proof.
  intros values nl ctx c d Hf; rewrite run_rr_allocated_shared_queue.
  eapply shared_rotate_agaf_pop_rr; [apply allocated_shared_queue_rep|exact Hf].
Qed.

Theorem shared_rotate_agaf_pop_alloc_nd_fresh : forall values nl ctx c d k,
  find_index Nat.eqb nl values = Some d ->
  <( {run_nd (allocated_shared_queue values) (managed_empty,(ctx,c))}, Pure
     |= AG (AF visW {shared_pop_after nl k}) )>.
Proof.
  intros values nl ctx c d k Hf; rewrite run_nd_allocated_shared_queue.
  eapply shared_rotate_agaf_pop_nd_fresh; [apply allocated_shared_queue_rep|exact Hf].
Qed.

Theorem shared_rotate_agaf_pop_alloc_rr_fresh : forall values nl ctx c d k,
  find_index Nat.eqb nl values = Some d ->
  <( {run_rr (allocated_shared_queue values) (managed_empty,(ctx,c))}, Pure
     |= AG (AF visW {shared_pop_after nl k}) )>.
Proof.
  intros values nl ctx c d k Hf; rewrite run_rr_allocated_shared_queue.
  eapply shared_rotate_agaf_pop_rr_fresh; [apply allocated_shared_queue_rep|exact Hf].
Qed.

Local Open Scope ictree_scope.
Local Open Scope list_scope.

(** ** Concrete execution.

    The first three complete rotations of the allocated program under round
    robin: worker 2 runs first (the parent is gone and the cursor is still
    [0]), then worker 1, then worker 2 again, each rotating the same queue
    once and logging one pop. *)
Theorem shared_queue_rr_prefix3 :
  let h0 := new_queue_heap 1 [10;20;30] hemp in
  let h3 := qstepN 1 3 [3;5;7] h0 in
  run_rr (allocated_shared_queue [10;20;30]) (managed_empty,(List.nil,0)) ~
  emit_list [inr (stamp (2,10) 0); inr (stamp (1,20) 1);
             inr (stamp (2,30) 2)]
    (run_rr_pool [worker 2 1; worker 1 1]%vector None 3
      ((h3,upd hemp 1 8),(List.nil,3))).
Proof.
  intros h0 h3.
  rewrite run_rr_allocated_shared_queue; unfold shared_queue; rewrite run_rr_two_forks.
  set (allocs := upd hemp 1 (2 * S (length [10;20;30]))).
  pose proof (allocated_shared_queue_rep [10;20;30]) as Hq0.
  change (qrep 1 [3;5;7] [10;20;30] h0) in Hq0.
  pose proof (qstep_qrep 1 [3;5;7] [10;20;30] h0 Hq0 ltac:(discriminate)) as Hq1.
  change (qrep 1 [5;7;3] [20;30;10] (qstep 1 [3;5;7] h0)) in Hq1.
  pose proof (qstep_qrep 1 [5;7;3] [20;30;10] _ Hq1 ltac:(discriminate)) as Hq2.
  change (qrep 1 [7;3;5] [30;10;20] (qstep 1 [5;7;3] (qstep 1 [3;5;7] h0))) in Hq2.
  cbn [emit_list List.fold_right].
  (* worker 2 *)
  rewrite (run_rr_pool_select [worker 2 1; worker 1 1]%vector 0), (rr_pick_even 0 eq_refl).
  etransitivity;
    [exact (run_rr_pool_turn [worker 2 1; worker 1 1]%vector Fin.F1 1 _ _ _
      (exact_worker_turn 2 1 3 [5;7] 10 [20;30] h0 allocs List.nil 0 Hq0))|].
  cbn [emit_list List.fold_right].
  apply sbisim_clo_bind_eq; [reflexivity|intros []].
  (* worker 1 *)
  rewrite (run_rr_pool_select [worker 2 1; worker 1 1]%vector 1), (rr_pick_odd 1 eq_refl).
  etransitivity;
    [exact (run_rr_pool_turn [worker 2 1; worker 1 1]%vector (Fin.FS Fin.F1) 2 _ _ _
      (exact_worker_turn 1 1 5 [7;3] 20 [30;10] (qstep 1 [3;5;7] h0) allocs List.nil 1 Hq1))|].
  cbn [emit_list List.fold_right].
  apply sbisim_clo_bind_eq; [reflexivity|intros []].
  (* worker 2 again *)
  rewrite (run_rr_pool_select [worker 2 1; worker 1 1]%vector 2), (rr_pick_even 2 eq_refl).
  etransitivity;
    [exact (run_rr_pool_turn [worker 2 1; worker 1 1]%vector Fin.F1 3 _ _ _
      (exact_worker_turn 2 1 7 [3;5] 30 [10;20] (qstep 1 [5;7;3] (qstep 1 [3;5;7] h0))
         allocs List.nil 2 Hq2))|].
  cbn [emit_list List.fold_right].
  apply sbisim_clo_bind_eq; [reflexivity|intros []].
  reflexivity.
Qed.

Local Open Scope fin_vector_scope.

(** ** The empty queue faults.

    An allocated empty queue has a null head pointer and the null cell is
    unallocated: the first worker turn reads it and the whole run is stuck,
    so no [AG] formula holds. *)
Lemma allocated_shared_queue_empty_stuck : forall ctx c,
  run_rr (allocated_shared_queue []) (managed_empty,(ctx,c)) ~
    (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intros ctx c.
  rewrite run_rr_allocated_shared_queue; unfold shared_queue; rewrite run_rr_two_forks.
  rewrite run_rr_pool_select, (rr_pick_even 0 eq_refl).
  unfold run_rr_pool, csl_pool; cbn [Vector.map].
  change (interp_schedule_rr sh 2
    ([Ret tt; denote (worker 1 1)]%vector @ Fin.F1 :=
      (denote_flow (worker 2 1) >>= fun _ => Ret tt)) (Some Fin.F1) 1
    ((new_queue_heap 1 [] hemp, upd hemp 1 (2 * S (length (@List.nil nat)))),(ctx,c)) ~
    (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig))).
  unfold worker at 2; rewrite interp_rr_until_none, interp_rr_bind.
  unfold rotate_once at 1; rewrite interp_rr_bind.
  rewrite (interp_rr_read_value _ _ _ 2 0) by reflexivity; cbv beta iota.
  rewrite interp_rr_bind.
  apply interp_rr_read_missing; reflexivity.
Qed.

Lemma allocated_shared_queue_empty_no_ag : forall ctx c w
    (phi : ticllW (CSLObs (nat * nat))),
  ~ <( {run_rr (allocated_shared_queue []) (managed_empty,(ctx,c))}, {w}
       |= AG phi )>.
Proof.
  intros ctx c w phi; rewrite allocated_shared_queue_empty_stuck; apply ag_stuck.
Qed.
