From Stdlib Require Import List.
From TICL Require Import
  Lang.CSL ICTree.Core ICTree.Equ ICTree.Events.Writer ICTree.SBisim
  ICTree.Logic.Trans ICTree.Logic.State ICTree.Logic.AG Logic.Core.
From TICL Require Import Lang.CSL.Queue.Representation Lang.CSL.Queue.Layout
  Lang.CSL.Queue.Frame Lang.CSL.Queue.Separation Lang.CSL.Queue.Alternating
  Lang.CSL.Queue.Composition Lang.CSL.Queue.Program.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Typeclasses Transparent equ sbisim.

Theorem rotate_agaf_pop_rr :
  forall u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
    <( {run_rr (parallel_queues u v) h c}, Pure
        |= AG (AF visW {(fun o => indexed_value o = (1,nl1))}) )>.
Proof.
  intros u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite (run_rr_parallel_bisim u v h c).
  exact (Composition.sched_agaf_q1 u v nl1 nl2 0 h c
    ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2).
Qed.

Theorem rotate_agaf_pop_rr_q2 :
  forall u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
    <( {run_rr (parallel_queues u v) h c}, Pure
        |= AG (AF visW {(fun o => indexed_value o = (2,nl2))}) )>.
Proof.
  intros u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite (run_rr_parallel_bisim u v h c).
  exact (Composition.sched_agaf_q2 u v nl1 nl2 0 h c
    ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2).
Qed.

Theorem rotate_agaf_pop_rr_fresh :
  forall u v nl1 nl2 k h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
    <( {run_rr (parallel_queues u v) h c}, Pure
        |= AG (AF visW {(indexed_after (fun x => x = (1,nl1)) k)}) )>.
Proof.
  intros u v nl1 nl2 k h c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite (run_rr_parallel_bisim u v h c).
  exact (Composition.sched_agaf_q1_fresh u v nl1 nl2 k 0 h c
    ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2).
Qed.

Theorem rotate_agaf_pop_rr_q2_fresh :
  forall u v nl1 nl2 k h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
    <( {run_rr (parallel_queues u v) h c}, Pure
        |= AG (AF visW {(indexed_after (fun x => x = (2,nl2)) k)}) )>.
Proof.
  intros u v nl1 nl2 k h c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite (run_rr_parallel_bisim u v h c).

From Coinduction Require Import coinduction.
  exact (Composition.sched_agaf_q2_fresh u v nl1 nl2 k 0 h c
    ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2).
Qed.

Theorem rotate_agaf_pop_rr_owned :
  forall u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2,
    owned_queues u ns1 vs1 v ns2 vs2 h ->
    find_index Nat.eqb nl1 vs1 = Some d1 -> find_index Nat.eqb nl2 vs2 = Some d2 ->
    <( {run_rr (parallel_queues u v) h c}, Pure
        |= AG (AF visW {(fun o => indexed_value o = (1,nl1))}) )>.
Proof.
  intros u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2 Hown F1 F2.
  destruct (owned_queues_sound u ns1 vs1 v ns2 vs2 h Hown) as (H1 & H2 & Hd).
  eapply rotate_agaf_pop_rr; eassumption.
Qed.

Theorem rotate_agaf_pop_alloc :
  forall values1 values2 nl1 nl2 c d1 d2,
    find_index Nat.eqb nl1 values1 = Some d1 -> find_index Nat.eqb nl2 values2 = Some d2 ->
    <( {run_rr (allocated_parallel_queues values1 values2) hemp c}, Pure
        |= AG (AF visW {(fun o => indexed_value o = (1,nl1))}) )>.
Proof.
  intros values1 values2 nl1 nl2 c d1 d2 F1 F2.
  destruct (run_rr_allocated_parallel values1 values2 c)
    as (u & v & h & Finite & Owned & Run).
  change (owned_queues u (queue_nodes u (List.length values1)) values1
    v (queue_nodes v (List.length values2)) values2 h) in Owned.
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  rewrite Run; eapply rotate_agaf_pop_rr; eassumption.
Qed.

Theorem rotate_agaf_pop_alloc_q2 :
  forall values1 values2 nl1 nl2 c d1 d2,
    find_index Nat.eqb nl1 values1 = Some d1 -> find_index Nat.eqb nl2 values2 = Some d2 ->
    <( {run_rr (allocated_parallel_queues values1 values2) hemp c}, Pure
        |= AG (AF visW {(fun o => indexed_value o = (2,nl2))}) )>.
Proof.
  intros values1 values2 nl1 nl2 c d1 d2 F1 F2.
  destruct (run_rr_allocated_parallel values1 values2 c)
    as (u & v & h & Finite & Owned & Run).
  change (owned_queues u (queue_nodes u (List.length values1)) values1
    v (queue_nodes v (List.length values2)) values2 h) in Owned.
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  rewrite Run; eapply rotate_agaf_pop_rr_q2; eassumption.
Qed.

Theorem rotate_agaf_pop_alloc_fresh :
  forall values1 values2 nl1 nl2 k c d1 d2,
    find_index Nat.eqb nl1 values1 = Some d1 -> find_index Nat.eqb nl2 values2 = Some d2 ->
    <( {run_rr (allocated_parallel_queues values1 values2) hemp c}, Pure
        |= AG (AF visW {(indexed_after (fun x => x = (1,nl1)) k)}) )>.
Proof.
  intros values1 values2 nl1 nl2 k c d1 d2 F1 F2.
  destruct (run_rr_allocated_parallel values1 values2 c)
    as (u & v & h & Finite & Owned & Run).
  change (owned_queues u (queue_nodes u (List.length values1)) values1
    v (queue_nodes v (List.length values2)) values2 h) in Owned.
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  rewrite Run; eapply rotate_agaf_pop_rr_fresh; eassumption.
Qed.

Theorem rotate_agaf_pop_alloc_q2_fresh :
  forall values1 values2 nl1 nl2 k c d1 d2,
    find_index Nat.eqb nl1 values1 = Some d1 -> find_index Nat.eqb nl2 values2 = Some d2 ->
    <( {run_rr (allocated_parallel_queues values1 values2) hemp c}, Pure
        |= AG (AF visW {(indexed_after (fun x => x = (2,nl2)) k)}) )>.
Proof.
  intros values1 values2 nl1 nl2 k c d1 d2 F1 F2.
  destruct (run_rr_allocated_parallel values1 values2 c)
    as (u & v & h & Finite & Owned & Run).
  change (owned_queues u (queue_nodes u (List.length values1)) values1
    v (queue_nodes v (List.length values2)) values2 h) in Owned.
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  rewrite Run; eapply rotate_agaf_pop_rr_q2_fresh; eassumption.
Qed.

Lemma parallel_queues_hemp_no_ag u v c (phi : ticllW (indexed (nat * nat))) w :
  ~ <( {run_rr (parallel_queues u v) hemp c}, {w} |= AG phi )>.
Proof. rewrite (parallel_queues_hemp_stuck u v c); apply ag_stuck. Qed.

Lemma allocated_parallel_queues_empty_no_ag values c
  (phi : ticllW (indexed (nat * nat))) w :
  ~ <( {run_rr (allocated_parallel_queues [] values) hemp c}, {w} |= AG phi )>.
Proof. rewrite (allocated_parallel_queues_empty_stuck values c); apply ag_stuck. Qed.
