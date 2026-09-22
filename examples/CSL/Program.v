From Stdlib Require Import Arith.PeanoNat Fin Vector List Lia.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.Events.Yield Lang.CSL
  ICTree.Events.Writer ICTree.SBisim ICTree.Interp.State.Mod
  ICTree.Interp.Yield.RoundRobin ICTree.Interp.Yield.SBisim Utils.Vectors.
From examples Require Import CSL.SLang CSL.HeapQ CSL.Sep2 CSL.Layout CSL.Frame.

Import ICtree ICTreeNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

Definition rotate_once (q hdr : nat) : CProg unit :=
  CBind (CRead (S hdr)) (fun a =>
  CBind (CRead a) (fun v =>
  CBind (CEmit q v) (fun _ =>
  CBind (CRead (S a)) (fun n =>
  CBind (CWrite (S hdr) n) (fun _ =>
  CBind (CRead hdr) (fun z0 =>
  CBind (CWrite (S (if Nat.eqb n 0 then hdr else z0)) a) (fun _ =>
  CBind (CWrite (S a) 0) (fun _ =>
  CWrite hdr a)))))))).

Definition worker (q hdr : nat) : CProg unit :=
  CUntilNone
    (CBind (rotate_once q hdr) (fun _ =>
     CBind CYield (fun _ => CRet (Some tt)))).

Definition parallel_queues (u v : nat) : CProg unit :=
  CBind (CFork (worker 2 v)) (fun _ => worker 1 u).

Fixpoint fill_nodes (first : nat) (values : list nat) : CProg unit :=
  match values with
  | []%list => CRet tt
  | (value :: rest)%list =>
      CBind (CWrite first value) (fun _ =>
      CBind (CWrite (S first)
        (match rest with []%list => 0 | (_ :: _)%list => first + 2 end)) (fun _ =>
      fill_nodes (first + 2) rest))
  end.

Definition init_queue (hdr : nat) (values : list nat) : CProg unit :=
  let ns := queue_nodes hdr (length values) in
  CBind (CWrite hdr (last ns 0)) (fun _ =>
  CBind (CWrite (S hdr) (hdf ns 0)) (fun _ =>
  fill_nodes (hdr + 2) values)).

Definition new_queue (values : list nat) : CProg nat :=
  CBind (CAlloc (2 * S (length values))) (fun hdr =>
  CBind (init_queue hdr values) (fun _ => CRet hdr)).

Definition allocated_parallel_queues (values1 values2 : list nat) : CProg unit :=
  CBind (new_queue values1) (fun u =>
  CBind (new_queue values2) (fun v => parallel_queues u v)).

Lemma denote_rotate_once q hdr :
  denote_flow (rotate_once q hdr) ≅
  (a <- heap_event (SRd (S hdr));;
   v <- heap_event (SRd a);;
   heap_event (SEmit q v);;
   n <- heap_event (SRd (S a));;
   heap_event (SWr (S hdr) n);;
   z0 <- heap_event (SRd hdr);;
   heap_event (SWr (S (if Nat.eqb n 0 then hdr else z0)) a);;
   heap_event (SWr (S a) 0);;
   heap_event (SWr hdr a);;
   Ret (Some tt)).
Proof.
  unfold rotate_once; cbn [denote_flow].
  do 8 (etransitivity; [apply bind_bind|];
    apply equ_clo_bind_eq; intro;
    etransitivity; [apply bind_ret_l|]).
  reflexivity.
Qed.

Local Lemma denote_rotate_once_bind {X} q hdr
  (K : option unit -> ictree CEff X) :
  (denote_flow (rotate_once q hdr) >>= K) ≅
  (denote (rotate_once q hdr);; K (Some tt)).
Proof.
  pose proof (denote_rotate_once q hdr) as Hr.
  etransitivity.
  - apply equ_clo_bind with (S := eq) (k2 := K);
      [exact Hr | intros x y <-; reflexivity].
  - symmetry; unfold denote.
    etransitivity; [apply bind_bind|].
    etransitivity.
    + apply equ_clo_bind with (S := eq)
        (k2 := fun _ : option unit => Ret tt;; K (Some tt));
        [exact Hr | intros x y <-; reflexivity].
    + do 9 (etransitivity; [apply bind_bind|];
        symmetry; etransitivity; [apply bind_bind|]; symmetry;
        apply equ_clo_bind_eq; intro).
      rewrite !bind_ret_l; reflexivity.
Qed.

Lemma denote_worker q hdr :
  denote (worker q hdr) ≅
  (denote (rotate_once q hdr);; source_yield;; Guard (denote (worker q hdr))).
Proof.
  unfold denote at 1; unfold worker at 1; cbn [denote_flow].
  etransitivity.
  - apply equ_clo_bind with (S := eq) (k2 := fun _ : option unit => Ret tt);
      [apply unfold_iter | intros x y <-; reflexivity].
  - do 3 (etransitivity; [apply bind_bind|]).
    etransitivity; [apply denote_rotate_once_bind|].
    apply equ_clo_bind_eq; intro ignored.
    do 2 (etransitivity; [apply bind_bind|]).
    apply equ_clo_bind_eq; intro yielded.
    do 3 (etransitivity; [apply bind_ret_l|]).
    etransitivity; [apply bind_guard|].
    step; constructor; reflexivity.
Qed.

Lemma denote_parallel_queues u v :
  denote (parallel_queues u v) ≅
  Vis (inr (inl Fork))
    (fun child : bool => if child then denote (worker 2 v) else denote (worker 1 u)).
Proof. unfold parallel_queues; apply denote_fork_bind. Qed.

Local Ltac rotate_state_bind :=
  lazymatch goal with
  | |- _ ~ (interp_state ?handler (ICtree.bind ?t ?k) ?s >>= ?finish) =>
    let Hbind := fresh "Hbind" in
    assert (Hbind : (interp_state handler (t >>= k) s >>= finish) ≅
      (interp_state handler t s >>= fun result =>
        (let '(x,s') := result in interp_state handler (k x) s') >>= finish)) by
      (etransitivity;
        [apply equ_clo_bind with (S := eq) (k2 := finish);
          [apply interp_state_bind | intros x y <-; reflexivity]
        | apply bind_bind]);
    rewrite Hbind; clear Hbind
  end.

Local Ltac rotate_effect law :=
  try rewrite interp_rr_bind;
  etransitivity; [apply law|];
  rotate_state_bind;
  apply sbisim_clo_bind_eq; [reflexivity | intros [? [? ?]]].

Lemma interp_rr_rotate_once n (ts : pool sE (S n))
  (i : Fin.t (S n)) q hdr (K : option unit -> thread sE) m h c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (rotate_once q hdr) >>= K)) (Some i) m (h,c) ~
  (interp_state sh (turn q hdr) (h,c) >>=
    fun '(_, (h',c')) =>
      interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m (h',c')).
Proof.
  unfold rotate_once, turn, turnk.
  rotate_effect interp_rr_read.
  rotate_effect interp_rr_read.
  rotate_effect interp_rr_emit.
  rotate_effect interp_rr_read.
  rotate_effect interp_rr_write.
  rotate_effect interp_rr_read.
  rotate_effect interp_rr_write.
  rotate_effect interp_rr_write.
  rotate_effect interp_rr_write.
  lazymatch goal with
  | |- _ ~ (interp_state ?handler (Ret ?x) ?s >>= ?finish) =>
    let Hret := fresh "Hret" in
    assert (Hret : (interp_state handler (Ret x) s >>= finish) ≅ finish (x,s)) by
      (transitivity (Ret (x,s) >>= finish);
        [apply equ_clo_bind with (S := eq);
          [apply interp_state_ret | intros a b <-; reflexivity]
        | exact (bind_ret_l (x,s) finish)]);
    eapply equ_clos_sbisim_goal; [reflexivity | exact Hret | reflexivity]
  end.
Qed.

Definition queue_slot (n : nat) : Fin.t 2 :=
  if Nat.even n then Fin.FS Fin.F1 else Fin.F1.

Definition queue_workers (u v : nat) (g2 g1 : bool) : pool sE 2 :=
  [(if g2 then Guard (denote (worker 2 v)) else denote (worker 2 v));
   (if g1 then Guard (denote (worker 1 u)) else denote (worker 1 u))]%vector.

Lemma queue_pick_next n : rr_pick 1 n = queue_slot (S n).
Proof.
  unfold queue_slot; rewrite even_flip.
  destruct (Nat.even n) eqn:Hn; cbn [negb].
  - now apply rr_pick_even.
  - now apply rr_pick_odd.
Qed.

Local Lemma interp_rr_worker n (ts : pool sE (S n))
  (i : Fin.t (S n)) q hdr m h c :
  interp_schedule_rr sh (S n) (ts @ i := denote (worker q hdr)) (Some i) m (h,c) ~
  (interp_state sh (turn q hdr) (h,c) >>= fun '(_, (h',c')) =>
    interp_schedule_rr sh (S n) (ts @ i := Guard (denote (worker q hdr))) None m (h',c')).
Proof.
  set (again := fun r : option (option unit) =>
    match r with
    | None => (Ret tt : thread sE)
    | Some None => Ret tt
    | Some (Some _) => Guard (denote (worker q hdr))
    end).
  unfold denote at 1; unfold worker at 1.
  rewrite interp_rr_until_none.
  lazymatch goal with
  | |- _ ~ ?rhs =>
    change (interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow
        (CBind (rotate_once q hdr) (fun _ =>
          CBind CYield (fun _ => CRet (Some tt)))) >>= again))
      (Some i) m (h,c) ~ rhs)
  end.
  rewrite interp_rr_bind.
  etransitivity; [apply interp_rr_rotate_once|].
  apply sbisim_clo_bind_eq; [reflexivity | intros [ignored [h' c']]].
  rewrite interp_rr_bind, interp_rr_yield.
  assert (Hpark : pool_equ
    (ts @ i := (denote_flow (CRet (Some tt)) >>= again))
    (ts @ i := Guard (denote (worker q hdr)))).
  {
    apply replace_pool_equ; [apply pool_equ_refl|].
    cbn [denote_flow].
    etransitivity; [exact (bind_ret_l (Some (Some tt)) again)|].
    reflexivity.
  }
  pose proof (interp_schedule_rr_equ sh (S n) _ _ None m (h',c') Hpark) as Hdone.
  eapply equ_clos_sbisim_goal; [exact Hdone | reflexivity | reflexivity].
Qed.

Lemma queue_pool_turn u v n g2 g1 h c :
  interp_schedule_rr sh 2 (queue_workers u v g2 g1)
    (Some (queue_slot n)) n (h,c) ~
  (interp_state sh (turn (tagof n) (hdrof u v n)) (h,c) >>=
    fun '(_, (h',c')) =>
      interp_schedule_rr sh 2
        (queue_workers u v (if Nat.even n then g2 else true)
                           (if Nat.even n then true else g1))
        (Some (queue_slot (S n))) (S n) (h',c')).
Proof.
  unfold queue_slot at 1; unfold tagof, hdrof.
  destruct (Nat.even n) eqn:Hphase.
  - destruct g1;
      [etransitivity; [eapply interp_schedule_rr_guard; reflexivity|] |].
    all: lazymatch goal with
    | |- _ ~ ?rhs =>
      change (interp_schedule_rr sh 2
        (queue_workers u v g2 false @ Fin.FS Fin.F1 := denote (worker 1 u))
        (Some (Fin.FS Fin.F1)) n (h,c) ~ rhs)
    end.
    all: etransitivity; [apply interp_rr_worker|].
    all: apply sbisim_clo_bind_eq; [reflexivity | intros [ignored [h' c']]].
    all: etransitivity; [apply interp_schedule_rr_select|].
    all: rewrite queue_pick_next; reflexivity.
  - destruct g2;
      [etransitivity; [eapply interp_schedule_rr_guard; reflexivity|] |].
    all: lazymatch goal with
    | |- _ ~ ?rhs =>
      change (interp_schedule_rr sh 2
        (queue_workers u v false g1 @ Fin.F1 := denote (worker 2 v))
        (Some Fin.F1) n (h,c) ~ rhs)
    end.
    all: etransitivity; [apply interp_rr_worker|].
    all: apply sbisim_clo_bind_eq; [reflexivity | intros [ignored [h' c']]].
    all: etransitivity; [apply interp_schedule_rr_select|].
    all: rewrite queue_pick_next; reflexivity.
Qed.


Local Ltac queue_prefix R law :=
  cbv beta;
  lazymatch goal with
  | |- _ (ICtree.bind ?prefix ?left) (ICtree.bind ?other_prefix ?right) =>
    etransitivity;
    [ apply (coinduction.gfp_bt (sb eq) R);
      apply sbisim_clo_bind_eq with (k2 := left);
      [law | intro result; reflexivity]
    | ];
    etransitivity;
    [ | apply (coinduction.gfp_bt (sb eq) R); symmetry;
        apply sbisim_clo_bind_eq with (k2 := right);
        [law | intro result; reflexivity] ]
  end.

Local Ltac queue_fault Hnone :=
  cbv beta;
  lazymatch goal with
  | |- interp_state sh (ICtree.bind (srd ?a) ?next) (?h,?c) ~ _ =>
    let Hfault := fresh "Hfault" in
    assert (Hfault : interp_state sh (srd a >>= next) (h,c) ≅ stuck) by
      (etransitivity; [apply interp_state_bind|];
       etransitivity;
       [ apply equ_clo_bind with (S := eq)
           (k2 := fun '(x,s') => interp_state sh (next x) s');
         [exact (sinterp_srd_stuck a h c Hnone) | intros x y <-; reflexivity]
       | apply bind_stuck_equ ]);
    eapply equ_clos_sbisim_goal; [exact Hfault | reflexivity | reflexivity]
  end.

Lemma queue_pool_bisim : forall u v n g2 g1 h c,
  interp_schedule_rr sh 2 (queue_workers u v g2 g1)
    (Some (queue_slot n)) n (h,c) ~ srun u v n h c.
Proof.
  coinduction R CIH; intros u v n g2 g1 h c.
  etransitivity;
    [apply (coinduction.gfp_bt (sb eq) R), queue_pool_turn|].
  etransitivity;
    [|apply (coinduction.gfp_bt (sb eq) R); symmetry; apply srun_turn].
  unfold turn, turnk.
  destruct (h (S (hdrof u v n))) as [a|] eqn:Hhead.
  - queue_prefix R ltac:(eapply sinterp_rd; exact Hhead).
    destruct (h a) as [payload|] eqn:Hpayload.
    + queue_prefix R ltac:(eapply sinterp_rd; exact Hpayload).
      queue_prefix R ltac:(apply sinterp_emit).
      eapply equ_sbt_closed_goal; [apply bind_bind | apply bind_bind |].
      unfold log, ICtree.trigger.
      eapply equ_sbt_closed_goal; [apply bind_vis | apply bind_vis |].
      apply step_sb_vis.
      * intros []; exists tt; split; [|reflexivity].
        eapply equ_clos_st_goal; [apply bind_ret_l | apply bind_ret_l |].
        apply st_clo_bind_eq; [reflexivity | intros [ignored [h' c']]; apply CIH].
      * intros []; exists tt; split; [|reflexivity].
        eapply equ_clos_st_goal; [apply bind_ret_l | apply bind_ret_l |].
        apply st_clo_bind_eq; [reflexivity | intros [ignored [h' c']]; apply CIH].
    + queue_prefix R ltac:(queue_fault Hpayload).
      eapply equ_sbt_closed_goal;
        [apply bind_stuck_equ | apply bind_stuck_equ | reflexivity].
  - queue_prefix R ltac:(queue_fault Hhead).
    eapply equ_sbt_closed_goal;
      [apply bind_stuck_equ | apply bind_stuck_equ | reflexivity].
Qed.

Theorem run_rr_parallel_bisim :
  forall u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2,
    qrep u ns1 vs1 h -> qrep v ns2 vs2 h -> Disj u ns1 v ns2 ->
    find nl1 vs1 = Some d1 -> find nl2 vs2 = Some d2 ->
    run_rr (parallel_queues u v) h c ~ srun u v 0 h c.
Proof.
  intros u v nl1 nl2 h c ns1 vs1 ns2 vs2 d1 d2 _ _ _ _ _.
  unfold parallel_queues; rewrite run_rr_fork_bind.
  change (interp_schedule_rr sh 2 (queue_workers u v false false)
    (Some (queue_slot 0)) 0 (h,c) ~ srun u v 0 h c).
  apply queue_pool_bisim.
Qed.

(** Silent initialization in the real shared source scheduler. *)

Local Lemma interp_rr_write_present n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h c :
  h a <> None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m (upd h a v,c).
Proof.
  intro Present; destruct (h a) as [old|] eqn:E; [|contradiction].
  rewrite interp_rr_write.
  assert (Hwrite : interp_state sh (swr a v) (h,c) ≅
    Guard (Ret (tt,(upd h a v,c)))).
  { etransitivity; [unfold swr; apply interp_state_vis |].
    transitivity (Ret (tt,(upd h a v,c)) >>= fun result : (unit * SSig)%type =>
      let '(_,sigma') := result in Guard (interp_state sh (Ret tt) sigma')).
    - apply equ_clo_bind with (S := eq);
        [exact (sh_wr_some a h c v old E) | intros x y <-; reflexivity].
    - etransitivity; [apply bind_ret_l |].
      step; constructor; apply interp_state_ret. }
  transitivity (Ret (tt,(upd h a v,c)) >>= fun result : (unit * SSig)%type =>
    let '(_,sigma') := result in
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m sigma').
  - apply sbisim_clo_bind_eq.
    + eapply equ_clos_sbisim_goal; [exact Hwrite | reflexivity | apply sb_guard].
    + intro result; reflexivity.
  - rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_fill_nodes n (ts : pool sE (S n)) (i : Fin.t (S n))
  first values (K : option unit -> thread sE) m h c :
  (forall offset, Nat.lt offset (2 * length values) ->
     h (first + offset)%nat <> None) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (fill_nodes first values) >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
    (Some i) m (fill_nodes_heap first values h,c).
Proof.
  revert first h; induction values as [|value values IH]; intros first h Allocated.
  - cbn [fill_nodes fill_nodes_heap]; rewrite interp_rr_ret; reflexivity.
  - cbn [fill_nodes fill_nodes_heap]; rewrite interp_rr_bind.
    etransitivity.
    + apply interp_rr_write_present.
      specialize (Allocated 0 ltac:(cbn; lia)); now rewrite Nat.add_0_r in Allocated.
    + rewrite interp_rr_bind; etransitivity.
      * apply interp_rr_write_present, upd_mono.
        specialize (Allocated 1 ltac:(cbn; lia)).
        replace (first + 1)%nat with (S first) in Allocated by lia; exact Allocated.
      * apply IH; intros offset O; apply upd_mono, upd_mono.
        replace (first + 2 + offset)%nat with (first + (2 + offset))%nat by lia.
        apply Allocated; cbn; lia.
Qed.

Lemma interp_rr_init_queue n (ts : pool sE (S n)) (i : Fin.t (S n))
  hdr values (K : option unit -> thread sE) m h c :
  (forall offset, Nat.lt offset (2 * S (length values)) ->
     h (hdr + offset)%nat <> None) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (init_queue hdr values) >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
    (Some i) m (init_queue_heap hdr values h,c).
Proof.
  intro Allocated; unfold init_queue, init_queue_heap; rewrite interp_rr_bind.
  etransitivity.
  - apply interp_rr_write_present.
    specialize (Allocated 0 ltac:(lia)); now rewrite Nat.add_0_r in Allocated.
  - rewrite interp_rr_bind; etransitivity.
    + apply interp_rr_write_present, upd_mono.
      specialize (Allocated 1 ltac:(lia)).
      replace (hdr + 1)%nat with (S hdr) in Allocated by lia; exact Allocated.
    + apply interp_rr_fill_nodes; intros offset O; apply upd_mono, upd_mono.
      replace (hdr + 2 + offset)%nat with (hdr + (2 + offset))%nat by lia.
      apply Allocated; lia.
Qed.

Lemma interp_rr_new_queue n (ts : pool sE (S n)) (i : Fin.t (S n))
  values (K : option nat -> thread sE) m h c :
  heap_finite h ->
  exists hdr,
    Nat.lt 0 hdr /\ block_free h hdr (2 * S (length values)) /\
    heap_finite (new_queue_heap hdr values h) /\
    asep (qrepX hdr (queue_nodes hdr (length values)) values)
         (fun frame => heq frame h) (new_queue_heap hdr values h) /\
    interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow (new_queue values) >>= K)) (Some i) m (h,c) ~
    interp_schedule_rr sh (S n) (ts @ i := K (Some hdr))
      (Some i) m (new_queue_heap hdr values h,c).
Proof.
  intro Finite.
  destruct (sh_alloc_finite h (2 * S (length values)) c Finite ltac:(lia))
    as (hdr & Positive & Free & First & Alloc).
  exists hdr; split; [exact Positive |]; split; [exact Free |]; split.
  - now apply new_queue_heap_finite.
  - split; [now apply new_queue_heap_owned |].
    pose proof (sinterp_alloc_first h (2 * S (length values)) hdr c
      (fun a : nat => (Ret a : ictree sE nat)) ltac:(lia) Positive Free First) as Hstate.
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
    + apply interp_rr_init_queue; intros offset O.
      unfold hunion; rewrite (hblock_in hdr (2 * S (length values)) offset O).
      discriminate.
    + rewrite interp_rr_ret; reflexivity.
Qed.

Theorem run_rr_allocated_parallel : forall values1 values2 c,
  exists u v h,
    heap_finite h /\
    asep (qrepX u (queue_nodes u (length values1)) values1)
         (qrepX v (queue_nodes v (length values2)) values2) h /\
    run_rr (allocated_parallel_queues values1 values2) hemp c ~
      run_rr (parallel_queues u v) h c.
Proof.
  intros values1 values2 c.
  set (done := fun _ : option unit => (Ret tt : thread sE)).
  set (after1 := fun r : option nat =>
    match r with
    | None => done None
    | Some u => denote_flow
        (CBind (new_queue values2) (fun v => parallel_queues u v)) >>= done
    end).
  destruct (interp_rr_new_queue 0 [Ret tt]%vector Fin.F1 values1 after1 0 hemp c
    heap_finite_hemp) as (u & Upos & Ufree & Finite1 & Own1 & Run1).
  set (h1 := new_queue_heap u values1 hemp).
  set (after2 := fun r : option nat =>
    match r with
    | None => done None
    | Some v => denote_flow (parallel_queues u v) >>= done
    end).
  destruct (interp_rr_new_queue 0 [Ret tt]%vector Fin.F1 values2 after2 0 h1 c
    Finite1) as (v & Vpos & Vfree & Finite2 & Own2 & Run2).
  exists u, v, (new_queue_heap v values2 h1); split; [exact Finite2 |]; split.
  - set (q1 := qheap u (queue_nodes u (length values1)) values1).
    set (q2 := qheap v (queue_nodes v (length values2)) values2).
    assert (E1 : heq h1 q1).
    { intro x; unfold h1.
      rewrite (new_queue_heap_agrees u values1 hemp Upos Ufree x).
      change (hunion q1 hemp x = q1 x).
      unfold hunion, hemp; destruct (q1 x); reflexivity. }
    assert (D21 : hdisj q2 q1).
    { eapply hdisj_resp; [apply heq_refl | exact E1 |].
      apply new_queue_heap_disjoint; exact Vfree. }
    exists q1, q2; split; [apply hdisj_sym; exact D21 |]; split.
    + eapply heq_trans; [apply new_queue_heap_agrees; eassumption |].
      eapply heq_trans.
      * apply hunion_resp; [apply heq_refl | exact E1].
      * apply hunion_comm; exact D21.
    + split; split; try apply qheap_qex; apply qheap_queue_nodes_rep; assumption.
  - unfold allocated_parallel_queues, run_rr at 1; unfold denote at 1.
    change (interp_schedule_rr sh 1
      ([Ret tt]%vector @ Fin.F1 :=
        (denote_flow (CBind (new_queue values1) (fun u =>
          CBind (new_queue values2) (fun v => parallel_queues u v))) >>= done))
      (Some Fin.F1) 0 (hemp,c) ~
      run_rr (parallel_queues u v) (new_queue_heap v values2 h1) c).
    rewrite interp_rr_bind.
    etransitivity; [exact Run1 |].
    cbn [after1]; rewrite interp_rr_bind.
    etransitivity; [exact Run2 |].
    reflexivity.
Qed.
