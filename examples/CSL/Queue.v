From TICL Require Import
  Lang.CSL ICTree.Core ICTree.Equ ICTree.Events.Writer ICTree.SBisim
  ICTree.Logic.Trans Logic.Core.
From examples Require Import
  CSL.HeapQ CSL.Layout CSL.Frame CSL.Sep2 CSL.SLang CSL.Compose CSL.Program.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Typeclasses Transparent equ sbisim.

Theorem rotate_agaf_pop_rr :
  forall u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
    <( {run_rr (parallel_queues u v) h c}, Pure
        |= AG (AF visW {spopped 1 nl1}) )>.
Proof.
  intros u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite (run_rr_parallel_bisim u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2
    H1 H2 Hd F1 F2).
  exact (Compose.sched_agaf_q1 u v nl1 nl2 0 h c
    ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2).
Qed.

Theorem rotate_agaf_pop_rr_q2 :
  forall u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
    <( {run_rr (parallel_queues u v) h c}, Pure
        |= AG (AF visW {spopped 2 nl2}) )>.
Proof.
  intros u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite (run_rr_parallel_bisim u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2
    H1 H2 Hd F1 F2).
  exact (Compose.sched_agaf_q2 u v nl1 nl2 0 h c
    ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2).
Qed.

Theorem rotate_agaf_pop_rr_fresh :
  forall u v nl1 nl2 k h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
    <( {run_rr (parallel_queues u v) h c}, Pure
        |= AG (AF visW {spopped_after 1 nl1 k}) )>.
Proof.
  intros u v nl1 nl2 k h c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite (run_rr_parallel_bisim u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2
    H1 H2 Hd F1 F2).
  exact (Compose.sched_agaf_q1_fresh u v nl1 nl2 k 0 h c
    ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2).
Qed.

Theorem rotate_agaf_pop_rr_q2_fresh :
  forall u v nl1 nl2 k h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
    <( {run_rr (parallel_queues u v) h c}, Pure
        |= AG (AF visW {spopped_after 2 nl2 k}) )>.
Proof.
  intros u v nl1 nl2 k h c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2.
  rewrite (run_rr_parallel_bisim u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2
    H1 H2 Hd F1 F2).
  exact (Compose.sched_agaf_q2_fresh u v nl1 nl2 k 0 h c
    ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2).
Qed.

Definition owned_queues u ns1 vs1 v ns2 vs2 : Heap -> Prop :=
  asep (qrepX u ns1 vs1) (qrepX v ns2 vs2).

Lemma owned_queues_sound u ns1 vs1 v ns2 vs2 h :
  owned_queues u ns1 vs1 v ns2 vs2 h ->
  qrep u ns1 vs1 h /\ qrep v ns2 vs2 h /\ Disj u ns1 v ns2.
Proof.
  intros (h1 & h2 & Hd & Heq & H1 & H2).
  change (hdisj h1 h2) in Hd.
  change (heq h (hunion h1 h2)) in Heq.
  assert (H1e : hdisj h1 hemp) by (intro x; right; reflexivity).
  assert (H2e : hdisj h2 hemp) by (intro x; right; reflexivity).
  destruct (compose3 u ns1 vs1 h1 v ns2 vs2 h2 hemp
    H1 H2 Hd H1e H2e eq_refl) as (Q1 & Q2 & Hdisj).
  assert (Hagree : forall x, hunion h1 (hunion h2 hemp) x = h x).
  { intro x; rewrite Heq; unfold hunion, hemp.
    destruct (h1 x); [reflexivity | destruct (h2 x); reflexivity]. }
  split; [| split].
  - eapply qrep_agree_fp; [exact Q1 | |].
    + intros x _; symmetry; apply Hagree.
    + rewrite <- Hagree; exact (qrep_null _ _ _ _ Q1).
  - eapply qrep_agree_fp; [exact Q2 | |].
    + intros x _; symmetry; apply Hagree.
    + rewrite <- Hagree; exact (qrep_null _ _ _ _ Q2).
  - exact Hdisj.
Qed.

Theorem rotate_agaf_pop_rr_owned :
  forall u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2,
    owned_queues u ns1 vs1 v ns2 vs2 h ->
    find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
    <( {run_rr (parallel_queues u v) h c}, Pure
        |= AG (AF visW {spopped 1 nl1}) )>.
Proof.
  intros u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2 Hown F1 F2.
  destruct (owned_queues_sound u ns1 vs1 v ns2 vs2 h Hown) as (H1 & H2 & Hd).
  eapply rotate_agaf_pop_rr; eassumption.
Qed.

Theorem rotate_agaf_pop_alloc :
  forall values1 values2 nl1 nl2 c d1 d2,
    find nl1 values1 = Some d1 -> find nl2 values2 = Some d2 ->
    <( {run_rr (allocated_parallel_queues values1 values2) hemp c}, Pure
        |= AG (AF visW {spopped 1 nl1}) )>.
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
    find nl1 values1 = Some d1 -> find nl2 values2 = Some d2 ->
    <( {run_rr (allocated_parallel_queues values1 values2) hemp c}, Pure
        |= AG (AF visW {spopped 2 nl2}) )>.
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
    find nl1 values1 = Some d1 -> find nl2 values2 = Some d2 ->
    <( {run_rr (allocated_parallel_queues values1 values2) hemp c}, Pure
        |= AG (AF visW {spopped_after 1 nl1 k}) )>.
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
    find nl1 values1 = Some d1 -> find nl2 values2 = Some d2 ->
    <( {run_rr (allocated_parallel_queues values1 values2) hemp c}, Pure
        |= AG (AF visW {spopped_after 2 nl2 k}) )>.
Proof.
  intros values1 values2 nl1 nl2 k c d1 d2 F1 F2.
  destruct (run_rr_allocated_parallel values1 values2 c)
    as (u & v & h & Finite & Owned & Run).
  change (owned_queues u (queue_nodes u (List.length values1)) values1
    v (queue_nodes v (List.length values2)) values2 h) in Owned.
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  rewrite Run; eapply rotate_agaf_pop_rr_q2_fresh; eassumption.
Qed.
