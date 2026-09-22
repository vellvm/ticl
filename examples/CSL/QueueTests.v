From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector.
From TICL Require Import
  Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Events.Writer
  ICTree.Interp.State.Mod ICTree.Logic.Trans Logic.Core
  ICTree.Events.Yield ICTree.Interp.Yield.RoundRobin Utils.Vectors.
From examples Require Import
  CSL.HeapQ CSL.Layout CSL.Frame CSL.Sep2 CSL.SLang CSL.Trace CSL.Program CSL.Queue.

Import ICtree ICTreeNotations TiclNotations VectorNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.
Local Open Scope fin_vector_scope.
Local Typeclasses Opaque equ sbisim.

Definition demo_h1 := qheap 2 [4;6] [7;9].
Definition demo_h2 := qheap 10 [12] [8].
Definition demo_heap := hunion demo_h1 demo_h2.
Definition duplicate_heap :=
  hunion (qheap 2 [4;6] [7;7]) (qheap 10 [12] [7]).

Lemma demo_queue2_aligned : qwf 10 [12].
Proof.
  apply qwf_aligned.
  - repeat (apply NoDup_cons; [cbn; intuition congruence |]); apply NoDup_nil.
  - cbn; intuition congruence.
  - repeat constructor; [exists 5 | exists 6]; reflexivity.
Qed.

Lemma demo_h1_owned : qrepX 2 [4;6] [7;9] demo_h1.
Proof. exact Frame.qrepX1. Qed.

Lemma demo_h2_owned : qrepX 10 [12] [8] demo_h2.
Proof.
  split; [apply qheap_qrep; [apply demo_queue2_aligned | reflexivity | discriminate]
         | apply qheap_qex].
Qed.

Lemma demo_disjoint xs ys : hdisj (qheap 2 [4;6] xs) (qheap 10 [12] ys).
Proof.
  intro x.
  destruct (qheap 2 [4;6] xs x) eqn:H1; [| now left].
  destruct (qheap 10 [12] ys x) eqn:H2; [| now right].
  exfalso.
  pose proof (qheap_qex 2 [4;6] xs x ltac:(congruence)) as F1.
  pose proof (qheap_qex 10 [12] ys x ltac:(congruence)) as F2.
  cbn in F1, F2; intuition congruence.
Qed.

Lemma demo_owned : owned_queues 2 [4;6] [7;9] 10 [12] [8] demo_heap.
Proof.
  exists demo_h1, demo_h2.
  split; [apply demo_disjoint |].
  split; [intro x; reflexivity |].
  split; [apply demo_h1_owned | apply demo_h2_owned].
Qed.

Lemma duplicate_owned :
  owned_queues 2 [4;6] [7;7] 10 [12] [7] duplicate_heap.
Proof.
  exists (qheap 2 [4;6] [7;7]), (qheap 10 [12] [7]).
  split; [apply demo_disjoint |].
  split; [intro x; reflexivity |].
  split; split; try apply qheap_qex.
  - apply qheap_qrep; [exact Layout.qwf1 | reflexivity | discriminate].
  - apply qheap_qrep; [apply demo_queue2_aligned | reflexivity | discriminate].
Qed.

Local Ltac reference_turn Hq :=
  lazymatch type of Hq with
  | qrep ?hdr (?a :: ?ns) (?pv :: ?vs) ?h =>
    lazymatch goal with
    | |- srun ?u ?v ?n h ?c ~ ?rhs =>
      let Hbody := constr:(sbody_spec u v n a ns pv vs h c Hq) in
      unfold srun, sched at 1;
      rewrite interp_state_unfold_iter;
      cbv beta;
      match goal with
      | |- sbisim _ (ICtree.bind _ ?k) _ =>
        eapply Transitive_sbisim;
        [ eapply sbisim_clo_bind_eq with (k2 := k);
          [ exact Hbody | intros ?; reflexivity ]
        | ]
      end;
      rewrite bind_bind;
      apply sbisim_clo_bind_eq; [reflexivity | intros []];
      rewrite bind_ret_l, sb_guard;
      lazymatch goal with
      | |- _ ~ ?tail =>
        change (srun u v (S n) (qstep hdr (a :: ns) h) (S c) ~ tail)
      end
    end
  end.

Local Lemma fixed_layout_four_pop u a b v d h x y z :
  qrep u [a;b] [x;y] h -> qrep v [d] [z] h -> Disj u [a;b] v [d] ->
  exists rest : ictreeW SObs (unit * SSig),
  run_rr (parallel_queues u v) h 0 ~
  (log (SPop 1 x 0);; log (SPop 2 z 1);;
   log (SPop 1 y 2);; log (SPop 2 z 3);; rest).
Proof.
  intros H1 H2 Hd.
  assert (F1 : find x [x;y] = Some 0) by (cbn [find]; now rewrite Nat.eqb_refl).
  assert (F2 : find z [z] = Some 0) by (cbn [find]; now rewrite Nat.eqb_refl).
  pose proof (qstep_qrep u [a;b] [x;y] h H1 ltac:(discriminate)) as H1a.
  change (qrep u [b;a] [y;x] (qstep u [a;b] h)) in H1a.
  pose proof (foreign_pres u [a;b] [x;y] v [d] [z] h
    H1 ltac:(discriminate) H2 Hd) as H2a.
  pose proof (Disj_rotl_l u [a;b] v [d] ltac:(discriminate) Hd) as Hda.
  change (Disj u [b;a] v [d]) in Hda.
  pose proof (foreign_pres v [d] [z] u [b;a] [y;x]
    (qstep u [a;b] h) H2a ltac:(discriminate) H1a
    (Disj_sym u [b;a] v [d] Hda)) as H1b.
  pose proof (qstep_qrep v [d] [z] (qstep u [a;b] h)
    H2a ltac:(discriminate)) as H2b.
  change (qrep v [d] [z] (qstep v [d] (qstep u [a;b] h))) in H2b.
  pose proof (foreign_pres u [b;a] [y;x] v [d] [z]
    (qstep v [d] (qstep u [a;b] h)) H1b ltac:(discriminate) H2b Hda) as H2c.
  exists (srun u v 4
    (qstep v [d] (qstep u [b;a]
      (qstep v [d] (qstep u [a;b] h)))) 4).
  etransitivity.
  - exact (run_rr_parallel_bisim u v x z h 0 [a;b] [x;y] [d] [z] 0 0
      H1 H2 Hd F1 F2).
  - reference_turn H1.
  reference_turn H2a.
  reference_turn H1b.
  reference_turn H2c.
  reflexivity.
Qed.

Lemma demo_four_pop_prefix : exists rest : ictreeW SObs (unit * SSig),
  run_rr (parallel_queues 2 10) demo_heap 0 ~
  (log (SPop 1 7 0);; log (SPop 2 8 1);;
   log (SPop 1 9 2);; log (SPop 2 8 3);; rest).
Proof.
  destruct (owned_queues_sound _ _ _ _ _ _ _ demo_owned) as (H1 & H2 & Hd).
  apply (fixed_layout_four_pop 2 4 6 10 12); assumption.
Qed.

Lemma duplicate_four_pop_prefix : exists rest : ictreeW SObs (unit * SSig),
  run_rr (parallel_queues 2 10) duplicate_heap 0 ~
  (log (SPop 1 7 0);; log (SPop 2 7 1);;
   log (SPop 1 7 2);; log (SPop 2 7 3);; rest).
Proof.
  destruct (owned_queues_sound _ _ _ _ _ _ _ duplicate_owned) as (H1 & H2 & Hd).
  apply (fixed_layout_four_pop 2 4 6 10 12); assumption.
Qed.

Lemma demo_queue1_recurs :
  <( {run_rr (parallel_queues 2 10) demo_heap 0}, Pure
      |= AG (AF visW {spopped 1 7}) )>.
Proof.
  destruct (owned_queues_sound _ _ _ _ _ _ _ demo_owned) as (H1 & H2 & Hd).
  exact (rotate_agaf_pop_rr 2 10 7 8 demo_heap 0
    [4;6] [7;9] [12] [8] 0 0 H1 H2 Hd eq_refl eq_refl).
Qed.

Lemma demo_queue2_recurs :
  <( {run_rr (parallel_queues 2 10) demo_heap 0}, Pure
      |= AG (AF visW {spopped 2 8}) )>.
Proof.
  destruct (owned_queues_sound _ _ _ _ _ _ _ demo_owned) as (H1 & H2 & Hd).
  exact (rotate_agaf_pop_rr_q2 2 10 7 8 demo_heap 0
    [4;6] [7;9] [12] [8] 0 0 H1 H2 Hd eq_refl eq_refl).
Qed.

Lemma demo_queue1_fresh k :
  <( {run_rr (parallel_queues 2 10) demo_heap 0}, Pure
      |= AG (AF visW {spopped_after 1 7 k}) )>.
Proof.
  destruct (owned_queues_sound _ _ _ _ _ _ _ demo_owned) as (H1 & H2 & Hd).
  exact (rotate_agaf_pop_rr_fresh 2 10 7 8 k demo_heap 0
    [4;6] [7;9] [12] [8] 0 0 H1 H2 Hd eq_refl eq_refl).
Qed.

Lemma demo_queue2_fresh k :
  <( {run_rr (parallel_queues 2 10) demo_heap 0}, Pure
      |= AG (AF visW {spopped_after 2 8 k}) )>.
Proof.
  destruct (owned_queues_sound _ _ _ _ _ _ _ demo_owned) as (H1 & H2 & Hd).
  exact (rotate_agaf_pop_rr_q2_fresh 2 10 7 8 k demo_heap 0
    [4;6] [7;9] [12] [8] 0 0 H1 H2 Hd eq_refl eq_refl).
Qed.

Lemma duplicate_queue1_recurs :
  <( {run_rr (parallel_queues 2 10) duplicate_heap 0}, Pure
      |= AG (AF visW {spopped 1 7}) )>.
Proof.
  destruct (owned_queues_sound _ _ _ _ _ _ _ duplicate_owned) as (H1 & H2 & Hd).
  exact (rotate_agaf_pop_rr 2 10 7 7 duplicate_heap 0
    [4;6] [7;7] [12] [7] 0 0 H1 H2 Hd eq_refl eq_refl).
Qed.

Lemma duplicate_queue2_recurs :
  <( {run_rr (parallel_queues 2 10) duplicate_heap 0}, Pure
      |= AG (AF visW {spopped 2 7}) )>.
Proof.
  destruct (owned_queues_sound _ _ _ _ _ _ _ duplicate_owned) as (H1 & H2 & Hd).
  exact (rotate_agaf_pop_rr_q2 2 10 7 7 duplicate_heap 0
    [4;6] [7;7] [12] [7] 0 0 H1 H2 Hd eq_refl eq_refl).
Qed.

Lemma duplicate_queue1_fresh k :
  <( {run_rr (parallel_queues 2 10) duplicate_heap 0}, Pure
      |= AG (AF visW {spopped_after 1 7 k}) )>.
Proof.
  destruct (owned_queues_sound _ _ _ _ _ _ _ duplicate_owned) as (H1 & H2 & Hd).
  exact (rotate_agaf_pop_rr_fresh 2 10 7 7 k duplicate_heap 0
    [4;6] [7;7] [12] [7] 0 0 H1 H2 Hd eq_refl eq_refl).
Qed.

Lemma duplicate_queue2_fresh k :
  <( {run_rr (parallel_queues 2 10) duplicate_heap 0}, Pure
      |= AG (AF visW {spopped_after 2 7 k}) )>.
Proof.
  destruct (owned_queues_sound _ _ _ _ _ _ _ duplicate_owned) as (H1 & H2 & Hd).
  exact (rotate_agaf_pop_rr_q2_fresh 2 10 7 7 k duplicate_heap 0
    [4;6] [7;7] [12] [7] 0 0 H1 H2 Hd eq_refl eq_refl).
Qed.

Lemma allocated_demo_four_pop_prefix :
  exists rest : ictreeW SObs (unit * SSig),
  run_rr (allocated_parallel_queues [7;9] [8]) hemp 0 ~
  (log (SPop 1 7 0);; log (SPop 2 8 1);;
   log (SPop 1 9 2);; log (SPop 2 8 3);; rest).
Proof.
  destruct (run_rr_allocated_parallel [7;9] [8] 0)
    as (u & v & h & Finite & Owned & Run).
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  destruct (fixed_layout_four_pop _ _ _ _ _ _ _ _ _ H1 H2 Hd) as (rest & Prefix).
  exists rest; etransitivity; [exact Run | exact Prefix].
Qed.

Lemma allocated_duplicate_four_pop_prefix :
  exists rest : ictreeW SObs (unit * SSig),
  run_rr (allocated_parallel_queues [7;7] [7]) hemp 0 ~
  (log (SPop 1 7 0);; log (SPop 2 7 1);;
   log (SPop 1 7 2);; log (SPop 2 7 3);; rest).
Proof.
  destruct (run_rr_allocated_parallel [7;7] [7] 0)
    as (u & v & h & Finite & Owned & Run).
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned) as (H1 & H2 & Hd).
  destruct (fixed_layout_four_pop _ _ _ _ _ _ _ _ _ H1 H2 Hd) as (rest & Prefix).
  exists rest; etransitivity; [exact Run | exact Prefix].
Qed.

Lemma allocated_demo_queue1_recurs :
  <( {run_rr (allocated_parallel_queues [7;9] [8]) hemp 0}, Pure
      |= AG (AF visW {spopped 1 7}) )>.
Proof. exact (rotate_agaf_pop_alloc [7;9] [8] 7 8 0 0 0 eq_refl eq_refl). Qed.

Lemma allocated_demo_queue2_recurs :
  <( {run_rr (allocated_parallel_queues [7;9] [8]) hemp 0}, Pure
      |= AG (AF visW {spopped 2 8}) )>.
Proof. exact (rotate_agaf_pop_alloc_q2 [7;9] [8] 7 8 0 0 0 eq_refl eq_refl). Qed.

Lemma allocated_demo_queue1_fresh k :
  <( {run_rr (allocated_parallel_queues [7;9] [8]) hemp 0}, Pure
      |= AG (AF visW {spopped_after 1 7 k}) )>.
Proof. exact (rotate_agaf_pop_alloc_fresh [7;9] [8] 7 8 k 0 0 0 eq_refl eq_refl). Qed.

Lemma allocated_demo_queue2_fresh k :
  <( {run_rr (allocated_parallel_queues [7;9] [8]) hemp 0}, Pure
      |= AG (AF visW {spopped_after 2 8 k}) )>.
Proof. exact (rotate_agaf_pop_alloc_q2_fresh [7;9] [8] 7 8 k 0 0 0 eq_refl eq_refl). Qed.

Lemma allocated_duplicate_queue1_recurs :
  <( {run_rr (allocated_parallel_queues [7;7] [7]) hemp 0}, Pure
      |= AG (AF visW {spopped 1 7}) )>.
Proof. exact (rotate_agaf_pop_alloc [7;7] [7] 7 7 0 0 0 eq_refl eq_refl). Qed.

Lemma allocated_duplicate_queue2_recurs :
  <( {run_rr (allocated_parallel_queues [7;7] [7]) hemp 0}, Pure
      |= AG (AF visW {spopped 2 7}) )>.
Proof. exact (rotate_agaf_pop_alloc_q2 [7;7] [7] 7 7 0 0 0 eq_refl eq_refl). Qed.

Lemma allocated_duplicate_queue1_fresh k :
  <( {run_rr (allocated_parallel_queues [7;7] [7]) hemp 0}, Pure
      |= AG (AF visW {spopped_after 1 7 k}) )>.
Proof. exact (rotate_agaf_pop_alloc_fresh [7;7] [7] 7 7 k 0 0 0 eq_refl eq_refl). Qed.

Lemma allocated_duplicate_queue2_fresh k :
  <( {run_rr (allocated_parallel_queues [7;7] [7]) hemp 0}, Pure
      |= AG (AF visW {spopped_after 2 7 k}) )>.
Proof. exact (rotate_agaf_pop_alloc_q2_fresh [7;7] [7] 7 7 k 0 0 0 eq_refl eq_refl). Qed.

Local Lemma interp_rr_new_queue_empty n (ts : pool sE (S n)) (i : Fin.t (S n))
  values (K : option nat -> thread sE) m c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (new_queue values) >>= K)) (Some i) m (hemp,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some 1))
    (Some i) m (new_queue_heap 1 values hemp,c).
Proof.
  assert (Free : block_free hemp 1 (2 * S (length values)))
    by (intros offset O; reflexivity).
  assert (First : forall j, Nat.lt 0 j -> Nat.lt j 1 ->
    ~ block_free hemp j (2 * S (length values))) by (intros; lia).
  pose proof (sinterp_alloc_first hemp (2 * S (length values)) 1 c
    (fun a : nat => (Ret a : ictree sE nat)) ltac:(lia) ltac:(lia) Free First) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  unfold new_queue; rewrite interp_rr_bind, interp_rr_alloc.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  eapply equ_clos_sbisim_goal; [apply bind_ret_l | reflexivity |].
  rewrite interp_rr_bind; etransitivity.
  - apply interp_rr_init_queue; intros offset O.
    unfold hunion; rewrite (hblock_in 1 (2 * S (length values)) offset O).
    discriminate.
  - rewrite interp_rr_ret; reflexivity.
Qed.

Local Ltac probe_read value :=
  lazymatch goal with
  | |- (interp_state sh (srd ?a) (?h,?c) >>= ?next) ~ _ =>
    let Hr := fresh "Hread" in
    pose proof (sinterp_rd a h c value
      (fun x : nat => (Ret x : ictree sE nat)) eq_refl) as Hr;
    rewrite bind_ret_r, interp_state_ret in Hr;
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hr | intro result; reflexivity] |];
    eapply equ_clos_sbisim_goal; [apply bind_ret_l | reflexivity |]
  end.

Local Ltac probe_emit :=
  lazymatch goal with
  | |- (interp_state sh (semit ?q ?v) (?h,?c) >>= ?next) ~ _ =>
    let He := fresh "Hemit" in
    assert (He : interp_state sh (semit q v) (h,c) ~
      (log (SPop q v c);; Ret (tt,(h,S c)))) by
    (let Hraw := fresh "Hraw" in
     pose proof (sinterp_emit q v h c
       (fun x : unit => (Ret x : ictree sE unit))) as Hraw;
     rewrite bind_ret_r in Hraw;
     etransitivity; [exact Hraw |];
     apply sbisim_clo_bind_eq; [reflexivity | intros []];
     rewrite interp_state_ret; reflexivity);
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact He | intro result; reflexivity] |];
    eapply equ_clos_sbisim_goal; [apply bind_bind | reflexivity |];
    apply sbisim_clo_bind_eq; [reflexivity | intros []];
    eapply equ_clos_sbisim_goal; [apply bind_ret_l | reflexivity |]
  end.

Local Ltac probe_finish :=
  cbv [Vector.replace Vector.caseS'];
  erewrite interp_schedule_rr_ret by reflexivity;
  rewrite vector_remove_head, interp_schedule_rr_empty; reflexivity.

Definition initialized_queue_probe : CProg unit :=
  CBind (new_queue [7;9]) (fun hdr =>
  CBind (CRead (S hdr)) (fun head =>
  CBind (CRead head) (fun value => CEmit hdr value))).

Lemma initialized_queue_probe_seen :
  run_rr initialized_queue_probe hemp 0 ~
    (log (SPop 1 7 0);; Ret (tt,(new_queue_heap 1 [7;9] hemp,1))).
Proof.
  unfold run_rr, initialized_queue_probe.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (new_queue [7;9]) (fun hdr =>
        CBind (CRead (S hdr)) (fun head =>
        CBind (CRead head) (fun value => CEmit hdr value)))) >>= fun _ => Ret tt))
    (Some Fin.F1) 0 (hemp,0) ~
    (log (SPop 1 7 0);; Ret (tt,(new_queue_heap 1 [7;9] hemp,1)))).
  rewrite interp_rr_bind, interp_rr_new_queue_empty.
  rewrite interp_rr_bind, interp_rr_read; probe_read 3.
  rewrite interp_rr_bind, interp_rr_read; probe_read 7.
  rewrite interp_rr_emit; probe_emit.
  probe_finish.
Qed.

Definition empty_queue_probe : CProg unit :=
  CBind (new_queue []) (fun hdr =>
  CBind (CRead hdr) (fun tail =>
  CBind (CRead (S hdr)) (fun head => CEmit tail head))).

Lemma empty_queue_probe_seen :
  run_rr empty_queue_probe hemp 0 ~
    (log (SPop 0 0 0);; Ret (tt,(new_queue_heap 1 [] hemp,1))).
Proof.
  unfold run_rr, empty_queue_probe.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (new_queue []) (fun hdr =>
        CBind (CRead hdr) (fun tail =>
        CBind (CRead (S hdr)) (fun head => CEmit tail head)))) >>= fun _ => Ret tt))
    (Some Fin.F1) 0 (hemp,0) ~
    (log (SPop 0 0 0);; Ret (tt,(new_queue_heap 1 [] hemp,1)))).
  rewrite interp_rr_bind, interp_rr_new_queue_empty.
  rewrite interp_rr_bind, interp_rr_read; probe_read 0.
  rewrite interp_rr_bind, interp_rr_read; probe_read 0.
  rewrite interp_rr_emit; probe_emit.
  probe_finish.
Qed.

