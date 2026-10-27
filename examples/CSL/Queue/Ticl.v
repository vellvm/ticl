From Stdlib Require Import List Fin Vector.
From Coinduction Require Import all.
From TICL Require Import
  Lang.CoCSL.Mod
  CTree.Core
  CTree.Events.Writer
  CTree.Interp.Yield.Fair
  CTree.Logic.Trans
  CTree.Logic.State
  CTree.Logic.AG
  Logic.Core.
From examples Require Import CSL.Queue.Representation CSL.Queue.Layout
  CSL.Queue.Frame CSL.Queue.Separation CSL.Queue.Alternating
  CSL.Queue.Composition CSL.Queue.Program.

Import CTree CTreeNotations TiclNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.

(** [parallel_queues u v] forks [worker 2 v] and continues as [worker 1 u]:
    the fair pool is [worker 2 v; worker 1 u] focused on the parent. *)
Lemma run_fair_parallel_queues (sch : Scheduler) u v st s :
  run_fair sch (parallel_queues u v) st s ~
  run_fair_pool sch [worker 2 v; worker 1 u]%vector (Some (Fin.FS Fin.F1)) st s.
Proof. unfold parallel_queues; rewrite run_fair_fork_bind; reflexivity. Qed.

Theorem rotate_agaf_pop_fair (sch : Scheduler) `{FairScheduler sch} (st : sched_state sch) :
  forall u v nl1 nl2 h allocs ctx c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
    <( {run_fair sch (parallel_queues u v) st ((h,allocs),(ctx,c))}, Pure
        |= AG (AF visW {fair_obs (csl_indexed (fun o => indexed_value o = (1,nl1)))}) )>.
Proof.
  intros u v nl1 nl2 h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite run_fair_parallel_queues.
  eapply (fair_agaf_q1_gen sch u v nl1 nl2 0 (fun o => indexed_value o = (1,nl1)));
    [intros j _; split; reflexivity | eassumption .. ].
Qed.

Theorem rotate_agaf_pop_fair_q2 (sch : Scheduler) `{FairScheduler sch} (st : sched_state sch) :
  forall u v nl1 nl2 h allocs ctx c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
    <( {run_fair sch (parallel_queues u v) st ((h,allocs),(ctx,c))}, Pure
        |= AG (AF visW {fair_obs (csl_indexed (fun o => indexed_value o = (2,nl2)))}) )>.
Proof.
  intros u v nl1 nl2 h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite run_fair_parallel_queues.
  eapply (fair_agaf_q2_gen sch u v nl1 nl2 0 (fun o => indexed_value o = (2,nl2)));
    [intros j _; split; reflexivity | eassumption .. ].
Qed.

Theorem rotate_agaf_pop_fair_fresh (sch : Scheduler) `{FairScheduler sch} (st : sched_state sch) :
  forall u v nl1 nl2 k h allocs ctx c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
    <( {run_fair sch (parallel_queues u v) st ((h,allocs),(ctx,c))}, Pure
        |= AG (AF visW {fair_obs (csl_indexed (indexed_after (fun x => x = (1,nl1)) k))}) )>.
Proof.
  intros u v nl1 nl2 k h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite run_fair_parallel_queues.
  eapply (fair_agaf_q1_gen sch u v nl1 nl2 k (indexed_after (fun x => x = (1,nl1)) k));
    [intros j Hj; split; [reflexivity | exact Hj] | eassumption .. ].
Qed.

Theorem rotate_agaf_pop_fair_q2_fresh (sch : Scheduler) `{FairScheduler sch} (st : sched_state sch) :
  forall u v nl1 nl2 k h allocs ctx c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
    <( {run_fair sch (parallel_queues u v) st ((h,allocs),(ctx,c))}, Pure
        |= AG (AF visW {fair_obs (csl_indexed (indexed_after (fun x => x = (2,nl2)) k))}) )>.
Proof.
  intros u v nl1 nl2 k h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite run_fair_parallel_queues.
  eapply (fair_agaf_q2_gen sch u v nl1 nl2 k (indexed_after (fun x => x = (2,nl2)) k));
    [intros j Hj; split; [reflexivity | exact Hj] | eassumption .. ].
Qed.

Theorem rotate_agaf_pop_fair_owned (sch : Scheduler) `{FairScheduler sch} (st : sched_state sch) :
  forall u v nl1 nl2 h allocs ctx c ns1 vs1 ns2 vs2 d1 d2,
    owned_queues u ns1 vs1 v ns2 vs2 h ->
    find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
    <( {run_fair sch (parallel_queues u v) st ((h,allocs),(ctx,c))}, Pure
        |= AG (AF visW {fair_obs (csl_indexed (fun o => indexed_value o = (1,nl1)))}) )>.
Proof.
  intros u v nl1 nl2 h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 Hown F1 F2.
  destruct (owned_queues_sound u ns1 vs1 v ns2 vs2 h Hown) as (H1 & H2 & Hd).
  eapply rotate_agaf_pop_fair; eassumption.
Qed.

Theorem rotate_agaf_pop_alloc (sch : Scheduler) `{FairScheduler sch} (st : sched_state sch) :
  forall values1 values2 nl1 nl2 ctx c d1 d2,
    find_index Nat.eqb nl1 values1 = Some d1 -> find_index Nat.eqb nl2 values2 = Some d2 ->
    <( {run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty,(ctx,c))}, Pure
        |= AG (AF visW {fair_obs (csl_indexed (fun o => indexed_value o = (1,nl1)))}) )>.
Proof.
  intros values1 values2 nl1 nl2 ctx c d1 d2 F1 F2.
  destruct (run_fair_allocated_parallel sch values1 values2 st ctx c)
    as (u & v & h & allocs & Finite & Owned & Run).
  change (owned_queues u (queue_nodes u (List.length values1)) values1
    v (queue_nodes v (List.length values2)) values2 h) in Owned.
  rewrite Run; eapply rotate_agaf_pop_fair_owned; eassumption.
Qed.

Theorem rotate_agaf_pop_alloc_q2 (sch : Scheduler) `{FairScheduler sch} (st : sched_state sch) :
  forall values1 values2 nl1 nl2 ctx c d1 d2,
    find_index Nat.eqb nl1 values1 = Some d1 -> find_index Nat.eqb nl2 values2 = Some d2 ->
    <( {run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty,(ctx,c))}, Pure
        |= AG (AF visW {fair_obs (csl_indexed (fun o => indexed_value o = (2,nl2)))}) )>.
Proof.
  intros values1 values2 nl1 nl2 ctx c d1 d2 F1 F2.
  destruct (run_fair_allocated_parallel sch values1 values2 st ctx c)
    as (u & v & h & allocs & Finite & Owned & Run).
  change (owned_queues u (queue_nodes u (List.length values1)) values1
    v (queue_nodes v (List.length values2)) values2 h) in Owned.
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  rewrite Run; eapply rotate_agaf_pop_fair_q2; eassumption.
Qed.

Theorem rotate_agaf_pop_alloc_fresh (sch : Scheduler) `{FairScheduler sch} (st : sched_state sch) :
  forall values1 values2 nl1 nl2 k ctx c d1 d2,
    find_index Nat.eqb nl1 values1 = Some d1 -> find_index Nat.eqb nl2 values2 = Some d2 ->
    <( {run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty,(ctx,c))}, Pure
        |= AG (AF visW {fair_obs (csl_indexed (indexed_after (fun x => x = (1,nl1)) k))}) )>.
Proof.
  intros values1 values2 nl1 nl2 k ctx c d1 d2 F1 F2.
  destruct (run_fair_allocated_parallel sch values1 values2 st ctx c)
    as (u & v & h & allocs & Finite & Owned & Run).
  change (owned_queues u (queue_nodes u (List.length values1)) values1
    v (queue_nodes v (List.length values2)) values2 h) in Owned.
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  rewrite Run; eapply rotate_agaf_pop_fair_fresh; eassumption.
Qed.

Theorem rotate_agaf_pop_alloc_q2_fresh (sch : Scheduler) `{FairScheduler sch} (st : sched_state sch) :
  forall values1 values2 nl1 nl2 k ctx c d1 d2,
    find_index Nat.eqb nl1 values1 = Some d1 -> find_index Nat.eqb nl2 values2 = Some d2 ->
    <( {run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty,(ctx,c))}, Pure
        |= AG (AF visW {fair_obs (csl_indexed (indexed_after (fun x => x = (2,nl2)) k))}) )>.
Proof.
  intros values1 values2 nl1 nl2 k ctx c d1 d2 F1 F2.
  destruct (run_fair_allocated_parallel sch values1 values2 st ctx c)
    as (u & v & h & allocs & Finite & Owned & Run).
  change (owned_queues u (queue_nodes u (List.length values1)) values1
    v (queue_nodes v (List.length values2)) values2 h) in Owned.
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  rewrite Run; eapply rotate_agaf_pop_fair_q2_fresh; eassumption.
Qed.

Lemma parallel_queues_hemp_no_ag u v ctx c (phi : ticllW (CSLObs (nat * nat))) w :
  ~ <( {run_rr (parallel_queues u v) (managed_empty,(ctx,c))}, {w} |= AG phi )>.
Proof. rewrite (parallel_queues_hemp_stuck u v ctx c); apply ag_stuck. Qed.

Lemma allocated_parallel_queues_empty_no_ag values ctx c
  (phi : ticllW (CSLObs (nat * nat))) w :
  ~ <( {run_rr (allocated_parallel_queues [] values) (managed_empty,(ctx,c))}, {w} |= AG phi )>.
Proof. rewrite (allocated_parallel_queues_empty_stuck values ctx c); apply ag_stuck. Qed.
