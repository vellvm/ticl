From TICL Require Import CTree.Interp.Yield.Policy.
From Stdlib Require Import Arith.PeanoNat Fin Vector List Lia.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  Lang.CoCSL.Mod
  Lang.CoCSL.Sequential
  CTree.Events.Writer
  CTree.Trace
  Logic.World
  CTree.Interp.State.Mod
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.SBisim
  Utils.Vectors.
From examples Require Import CSL.Queue.Alternating CSL.Queue.Representation
  CSL.Queue.Separation CSL.Queue.Layout CSL.Queue.Frame
  CSL.Queue.Operations CSL.Queue.Trace.

Import CTree CTreeNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
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

Definition fill_nodes (first : nat) (values : list nat) : CProg unit :=
  write_list (node_writes (node_addrs first (length values)) values).

Definition init_queue (hdr : nat) (values : list nat) : CProg unit :=
  let ns := queue_nodes hdr (length values) in
  CBind (CWrite hdr (last ns 0)) (fun _ =>
  CBind (CWrite (S hdr) (List.hd 0 ns)) (fun _ =>
  fill_nodes (hdr + 2) values)).

Definition new_queue (values : list nat) : CProg nat :=
  CBind (CAlloc (2 * S (length values))) (fun hdr =>
  CBind (init_queue hdr values) (fun _ => CRet hdr)).

Definition fill_nodes_logs {A} (first : nat) (values : list nat)
  (memory : ManagedHeap) : list (CSLObs A) :=
  write_snapshots (node_writes (node_addrs first (length values)) values)
    memory.

Definition init_queue_logs {A} (hdr : nat) (values : list nat)
  (memory : ManagedHeap) : list (CSLObs A) :=
  let ns := queue_nodes hdr (length values) in
  let h1 := upd (fst memory) hdr (last ns 0) in
  let h2 := upd h1 (S hdr) (List.hd 0 ns) in
  CSLHeap (h1,snd memory) :: CSLHeap (h2,snd memory) ::
    fill_nodes_logs (hdr + 2) values (h2,snd memory).

Definition new_queue_logs {A} (hdr : nat) (values : list nat)
  (memory : ManagedHeap) : list (CSLObs A) :=
  let allocated := managed_alloc memory hdr (2 * S (length values)) in
  CSLHeap allocated :: init_queue_logs hdr values allocated.

Lemma fill_nodes_logs_after {A} first values (memory : ManagedHeap) :
  after_logs (fill_nodes_logs (A:=A) first values memory)
    (Obs (Log (CSLHeap memory)) tt) =
  Obs (Log (CSLHeap (fill_nodes_heap first values (fst memory),snd memory))) tt.
Proof.
  apply write_snapshots_after.
Qed.

Lemma init_queue_logs_after {A} hdr values (memory : ManagedHeap) w :
  after_logs (init_queue_logs (A:=A) hdr values memory) w =
  Obs (Log (CSLHeap (init_queue_heap hdr values (fst memory),snd memory))) tt.
Proof.
  unfold init_queue_logs, init_queue_heap; cbn [after_logs fst snd].
  exact (fill_nodes_logs_after (hdr + 2) values
    (upd (upd (fst memory) hdr (last (queue_nodes hdr (length values)) 0))
      (S hdr) (List.hd 0 (queue_nodes hdr (length values))),snd memory)).
Qed.

Lemma new_queue_logs_after {A} hdr values (memory : ManagedHeap) w :
  after_logs (new_queue_logs (A:=A) hdr values memory) w =
  Obs (Log (CSLHeap (new_queue_heap hdr values (fst memory),
    upd (snd memory) hdr (2 * S (length values))))) tt.
Proof.
  unfold new_queue_logs; cbn [after_logs]; rewrite init_queue_logs_after.
  reflexivity.
Qed.

(** A logged run retains the complete constructor prefix and its final
    heap snapshot on the program-observation side of the sum. *)
Lemma new_queue_logs_afterW {A} hdr values (memory : ManagedHeap)
  (w : World (writerE (CSLObs A + nat))) :
  after_logs (List.map inl (new_queue_logs (A:=A) hdr values memory)) w =
  Obs (Log (inl (CSLHeap (new_queue_heap hdr values (fst memory),
    upd (snd memory) hdr (2 * S (length values)))))) tt.
Proof.
  unfold new_queue_logs; cbn [List.map after_logs].
  apply after_logs_map, init_queue_logs_after.
Qed.

Lemma fill_nodes_logs_length {A} first values memory :
  length (fill_nodes_logs (A:=A) first values memory) = 2 * length values.
Proof.
  unfold fill_nodes_logs; rewrite write_snapshots_length.
  rewrite <- (length_map fst (node_writes (node_addrs first (length values)) values)).
  rewrite node_writes_cells by apply node_addrs_length.
  rewrite cells_length, node_addrs_length; reflexivity.
Qed.

Lemma init_queue_logs_length {A} hdr values memory :
  length (init_queue_logs (A:=A) hdr values memory) = 2 + 2 * length values.
Proof.
  unfold init_queue_logs; cbn [length]; rewrite fill_nodes_logs_length; reflexivity.
Qed.

Lemma new_queue_logs_length {A} hdr values memory :
  length (new_queue_logs (A:=A) hdr values memory) = 3 + 2 * length values.
Proof.
  unfold new_queue_logs; cbn [length]; rewrite init_queue_logs_length; reflexivity.
Qed.

Definition allocated_parallel_queues (values1 values2 : list nat) : CProg unit :=
  CBind (new_queue values1) (fun u =>
  CBind (new_queue values2) (fun v => parallel_queues u v)).

Definition shared_queue (hdr : nat) : CProg unit :=
  CBind (CFork (worker 1 hdr)) (fun _ =>
  CBind (CFork (worker 2 hdr)) (fun _ => CRet tt)).

Definition allocated_shared_queue (values : list nat) : CProg unit :=
  CBind (new_queue values) shared_queue.

Lemma denote_rotate_once q hdr :
  denote_flow (rotate_once q hdr) ≅
  (a <- heap_read (E:=CEff) (S hdr);;
   v <- heap_read (E:=CEff) a;;
   CTree.trigger (inr1 (inr1 (inr1 (inr1 (Log (q,v))))) : CEff unit);;
   n <- heap_read (E:=CEff) (S a);;
   heap_write (E:=CEff) (S hdr) n;;
   z0 <- heap_read (E:=CEff) hdr;;
   heap_write (E:=CEff) (S (if Nat.eqb n 0 then hdr else z0)) a;;
   heap_write (E:=CEff) (S a) 0;;
   heap_write (E:=CEff) hdr a;;
   Ret (Some tt)).
Proof.
  unfold rotate_once; cbn [denote_flow].
  do 8 (etransitivity; [apply bind_bind|];
    apply equ_clo_bind_eq; intro;
    etransitivity; [apply bind_ret_l|]).
  reflexivity.
Qed.

Local Lemma denote_rotate_once_bind {X} q hdr
  (K : option unit -> ctree CEff Bn X) :
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
  Vis (inr1 (inl1 Fork))
    (fun child : bool => if child then denote (worker 2 v) else denote (worker 1 u)).
Proof. unfold parallel_queues; apply denote_fork_bind. Qed.

(** Expose a source [bind] under [interp_state] and inject its observations
    into the program side of the logged scheduler signature. *)
Local Ltac rotate_state_bind :=
  lazymatch goal with
  | |- _ ~ (translate relabel_log (interp_state ?handler (CTree.bind ?t ?k) ?s) >>= ?finish) =>
    let Hbind := fresh "Hbind" in
    assert (Hbind : (translate relabel_log (interp_state handler (t >>= k) s) >>= finish) ≅
      (translate relabel_log (interp_state handler t s) >>= fun xs =>
        translate relabel_log (interp_state handler (k (snd xs)) (fst xs)) >>= finish)) by
      (rewrite interp_state_bind, translate_bind; apply bind_bind);
    rewrite Hbind; clear Hbind
  end.

Local Ltac rotate_effect law :=
  try rewrite interp_rr_bind;
  etransitivity; [apply law|];
  rotate_state_bind;
  apply sbisim_clo_bind_eq; [reflexivity | intros [? ?]; cbn [fst snd]].

Lemma interp_rr_rotate_once n (ts : pool sE Bn (S n))
  (i : Fin.t (S n)) q hdr (K : option unit -> thread sE Bn) m (s : SSig) :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (rotate_once q hdr) >>= K)) (Some i) m s ~
  (translate relabel_log (interp_state sh (turn q hdr) s) >>=
    fun '(s', _) =>
      interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m s').
Proof.
  unfold rotate_once, turn, turnk, queue_turn.
  rotate_effect interp_rr_read.
  rotate_effect interp_rr_read.
  rotate_effect interp_rr_emit.
  rotate_effect interp_rr_read.
  rotate_effect interp_rr_write.
  rotate_effect interp_rr_read.
  rotate_effect interp_rr_write.
  rotate_effect interp_rr_write.
  rotate_effect interp_rr_write.
  rewrite interp_state_ret, translate_ret, bind_ret_l.
  reflexivity.
Qed.

Definition queue_workers (u v : nat) (g2 g1 : bool) : pool sE Bn 2 :=
  [(if g2 then Guard (denote (worker 2 v)) else denote (worker 2 v));
   (if g1 then Guard (denote (worker 1 u)) else denote (worker 1 u))]%vector.

Lemma queue_pick_next n : rr_pick 1 n = queue_slot (S n).
Proof.
  unfold queue_slot; rewrite even_flip.
  destruct (Nat.even n) eqn:Hn; cbn [negb].
  - now apply rr_pick_even.
  - now apply rr_pick_odd.
Qed.

Local Lemma interp_rr_worker n (ts : pool sE Bn (S n))
  (i : Fin.t (S n)) q hdr m (s : SSig) :
  interp_schedule_rr sh (S n) (ts @ i := denote (worker q hdr)) (Some i) m s ~
  (translate relabel_log (interp_state sh (turn q hdr) s) >>= fun '(s', _) =>
    interp_schedule_rr sh (S n) (ts @ i := Guard (denote (worker q hdr))) None m s').
Proof.
  set (again := fun r : option (option unit) =>
    match r with
    | None => (Ret tt : thread sE Bn)
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
      (Some i) m s ~ rhs)
  end.
  rewrite interp_rr_bind.
  etransitivity; [apply interp_rr_rotate_once|].
  apply sbisim_clo_bind_eq; [reflexivity | intros [s' ignored]].
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
  transitivity (interp_schedule_rr sh (S n)
    (ts @ i := Guard (denote (worker q hdr))) None m s');
    [apply equ_sbisim; exact (interp_schedule_rr_equ sh (S n) _ _ None m s' Hpark)
    | reflexivity].
Qed.

(** One pool turn: the focused worker rotates, then the scheduler's logged
    pick ([interp_schedule_rr_select]) moves to the other slot. *)
Lemma queue_pool_turn u v n g2 g1 (s : SSig) :
  interp_schedule_rr sh 2 (queue_workers u v g2 g1)
    (Some (queue_slot n)) n s ~
  (translate relabel_log (interp_state sh (turn (tagof n) (hdrof u v n)) s) >>=
    fun '(s', _) =>
      Vis (Log (inr (slot_index (queue_slot (S n))))) (fun _ =>
        interp_schedule_rr sh 2
          (queue_workers u v (if Nat.even n then g2 else true)
                             (if Nat.even n then true else g1))
          (Some (queue_slot (S n))) (S n) s')).
Proof.
  unfold queue_slot at 1; unfold tagof, hdrof.
  destruct (Nat.even n) eqn:Hphase.
  - destruct g1;
      [etransitivity; [eapply interp_schedule_rr_guard; reflexivity|] |].
    all: lazymatch goal with
    | |- _ ~ ?rhs =>
      change (interp_schedule_rr sh 2
        (queue_workers u v g2 false @ Fin.FS Fin.F1 := denote (worker 1 u))
        (Some (Fin.FS Fin.F1)) n s ~ rhs)
    end.
    all: etransitivity; [apply interp_rr_worker|].
    all: apply sbisim_clo_bind_eq; [reflexivity | intros [s' ignored]].
    all: etransitivity; [apply interp_schedule_rr_select|].
    all: rewrite queue_pick_next; reflexivity.
  - destruct g2;
      [etransitivity; [eapply interp_schedule_rr_guard; reflexivity|] |].
    all: lazymatch goal with
    | |- _ ~ ?rhs =>
      change (interp_schedule_rr sh 2
        (queue_workers u v false g1 @ Fin.F1 := denote (worker 2 v))
        (Some Fin.F1) n s ~ rhs)
    end.
    all: etransitivity; [apply interp_rr_worker|].
    all: apply sbisim_clo_bind_eq; [reflexivity | intros [s' ignored]].
    all: etransitivity; [apply interp_schedule_rr_select|].
    all: rewrite queue_pick_next; reflexivity.
Qed.

(** The two-worker pool under the source round-robin scheduler IS the
    reference alternating scheduler: both factor every turn through
    the lifted [interp_state sh (turn _ _)] and end with the same logged pick. *)
Lemma queue_pool_bisim : forall u v n g2 g1 (s : SSig),
  interp_schedule_rr sh 2 (queue_workers u v g2 g1)
    (Some (queue_slot n)) n s ~ srun u v n s.
Proof.
  intros u v n g2 g1 s.
  refine (sbisim_log_family
    (fun '(n,g2,g1,s) => interp_schedule_rr sh 2 (queue_workers u v g2 g1)
      (Some (queue_slot n)) n s)
    (fun '(n,g2,g1,s) => srun u v n s)
    (fun '(n,g2,g1,s) => translate relabel_log
      (interp_state sh (turn (tagof n) (hdrof u v n)) s))
    (fun '(n,g2,g1,s) => inr (slot_index (queue_slot (S n))))
    (fun '(n,g2,g1,s) '(s',_) =>
      (S n, if Nat.even n then g2 else true,
        if Nat.even n then true else g1, s'))
    (fun _ => True) _ _ _ (n,g2,g1,s) I).
  - intros [[[n0 g20] g10] s0] _.
    etransitivity; [apply queue_pool_turn|].
    apply sbisim_clo_bind_eq; [reflexivity|intros [s' ignored]; reflexivity].
  - intros [[[n0 g20] g10] s0] _.
    etransitivity; [apply srun_turn|].
    apply sbisim_clo_bind_eq; [reflexivity|intros [s' ignored]; reflexivity].
  - intros i a _; exact I.
Qed.

Theorem run_rr_parallel_bisim u v (s : SSig) :
  run_rr (parallel_queues u v) s ~ srun u v 0 s.
Proof.
  unfold parallel_queues; rewrite run_rr_fork_bind.
  change (interp_schedule_rr sh 2 (queue_workers u v false false)
    (Some (queue_slot 0)) 0 s ~ srun u v 0 s).
  apply queue_pool_bisim.
Qed.

(** One whole rotation of the reference scheduler, read off [turnk_spec]:
    one pop and four snapshots, the logged scheduling pick, the rotated heap. *)
Lemma srun_pop u v n hdr tag a ns pv vs h allocs ctx c :
  hdrof u v n = hdr -> tagof n = tag ->
  qrep hdr (a :: ns) (pv :: vs) h ->
  srun u v n ((h, allocs), (ctx, c)) ~
  emit_list (List.map inl
    (queue_turn_logs (CSLEmit (stamp (tag,pv) c)) hdr a
      (List.hd 0 ns) (last (a :: ns) 0) (h,allocs)))
   (log (inr (slot_index (queue_slot (S n)))) ;;
    srun u v (S n) ((qstep hdr (a :: ns) h, allocs), (ctx, S c))).
Proof.
  intros <- <- Hq.
  rewrite srun_turn; unfold turn.
  rewrite (turnk_spec (tagof n) (hdrof u v n) a ns pv vs h allocs ctx c (Ret tt) Hq).
  rewrite translate_emit_list, emit_list_bind; apply emit_list_sbisim.
  rewrite interp_state_ret, translate_ret, bind_ret_l; cbn [qstep].
  rewrite log_vis; reflexivity.
Qed.

(** The first four pops of two disjoint queues under the shared source
    round-robin scheduler: queue 1 rotates [a;b], queue 2 its singleton [d],
    alternating, with the observation counter advancing once per pop and one
    logged scheduling pick between consecutive pops (slots [0;1;0;1]). *)
Lemma parallel_queues_four_pop_bisim u a b v d h allocs x y z ctx c :
  qrep u [a;b] [x;y] h -> qrep v [d] [z] h -> Disj u [a;b] v [d] ->
  let h1 := qstep u [a;b] h in
  let h2 := qstep v [d] h1 in
  let h3 := qstep u [b;a] h2 in
  let h4 := qstep v [d] h3 in
  run_rr (parallel_queues u v) ((h,allocs),(ctx,c)) ~
    emit_list (List.map inl (queue_turn_logs (CSLEmit (stamp (1,x) c)) u a b b (h,allocs)))
     (log (inr 0);;
      emit_list (List.map inl (queue_turn_logs (CSLEmit (stamp (2,z) (S c))) v d 0 d (h1,allocs)))
     (log (inr 1);;
      emit_list (List.map inl (queue_turn_logs (CSLEmit (stamp (1,y) (S (S c)))) u b a a (h2,allocs)))
     (log (inr 0);;
      emit_list (List.map inl (queue_turn_logs (CSLEmit (stamp (2,z) (S (S (S c))))) v d 0 d (h3,allocs)))
     (log (inr 1);;
      srun u v 4 ((h4,allocs),(ctx,S (S (S (S c))))))))).
Proof.
  intros H1 H2 Hd; cbv zeta.
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
  etransitivity; [exact (run_rr_parallel_bisim u v ((h,allocs),(ctx,c))) |].
  rewrite (srun_pop u v 0 u 1 a [b] x [y] h allocs ctx c eq_refl eq_refl H1).
  apply emit_list_sbisim; rewrite !log_vis; apply sb_vis; intros _.
  rewrite (srun_pop u v 1 v 2 d [] z [] _ allocs ctx (S c) eq_refl eq_refl H2a).
  apply emit_list_sbisim; rewrite !log_vis; apply sb_vis; intros _.
  rewrite (srun_pop u v 2 u 1 b [a] y [x] _ allocs ctx (S (S c)) eq_refl eq_refl H1b).
  apply emit_list_sbisim; rewrite !log_vis; apply sb_vis; intros _.
  rewrite (srun_pop u v 3 v 2 d [] z [] _ allocs ctx (S (S (S c))) eq_refl eq_refl H2c).
  apply emit_list_sbisim; rewrite !log_vis; apply sb_vis; intros _.
  reflexivity.
Qed.

(** An out-of-footprint read under [interp_state sh] is stuck, whatever
    follows it. *)
Local Ltac queue_fault Hnone :=
  cbv beta;
  lazymatch goal with
  | |- interp_state ?H (CTree.bind (heap_read ?a) ?next) ((?h,?allocs),?c) ~ _ =>
    let Hfault := fresh "Hfault" in
    assert (Hfault : interp_state H (heap_read a >>= next) ((h,allocs),c) ~ Stuck) by
      (apply (interp_heapW_rd_missing CSLHeap
        (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))); exact Hnone);
    rewrite Hfault; reflexivity
  end.

(** Queue 1 takes the first source turn; a fault there faults the whole run. *)
Local Lemma parallel_queues_first_turn_stuck u v (s : SSig) :
  interp_state sh (turn 1 u) s ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)) ->
  run_rr (parallel_queues u v) s ~
    (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intro Hfault.
  unfold parallel_queues; rewrite run_rr_fork_bind.
  change (interp_schedule_rr sh 2 (queue_workers u v false false)
    (Some (queue_slot 0)) 0 s ~
    (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))).
  rewrite queue_pool_turn.
  change (tagof 0) with 1; change (hdrof u v 0) with u.
  rewrite Hfault, translate_stuck_node, bind_stuck; reflexivity.
Qed.

Lemma parallel_queues_hemp_stuck u v ctx c :
  run_rr (parallel_queues u v) (managed_empty,(ctx,c)) ~
    (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  apply parallel_queues_first_turn_stuck.
  assert (Hhead : hemp (S u) = None) by reflexivity.
  unfold turn, turnk, queue_turn, managed_empty; queue_fault Hhead.
Qed.

Lemma interp_nd_fill_nodes n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  first values (K : option unit -> thread sE Bn) h allocs ctx c :
  (forall offset, Nat.lt offset (2 * length values) ->
     h (first + offset)%nat <> None) ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (fill_nodes first values) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  emit_list (fill_nodes_logs first values (h,allocs))
    (interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
      (Some i) ((fill_nodes_heap first values h,allocs),(ctx,c))).
Proof.
  intro Allocated; unfold fill_nodes, fill_nodes_logs, fill_nodes_heap.
  apply interp_nd_write_list.
  intros a v Hin.
  assert (Hcell : In a (cells (node_addrs first (length values)))).
  { apply (node_writes_keys_subset (node_addrs first (length values)) values a).
    exact (in_map fst _ _ Hin). }
  apply node_cells_range in Hcell as [Hlo Hhi].
  replace a with (first + (a - first))%nat by lia.
  apply Allocated; lia.
Qed.

Lemma interp_nd_init_queue n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  hdr values (K : option unit -> thread sE Bn) h allocs ctx c :
  (forall offset, Nat.lt offset (2 * S (length values)) ->
     h (hdr + offset)%nat <> None) ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (init_queue hdr values) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  emit_list (init_queue_logs hdr values (h,allocs))
    (interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
      (Some i) ((init_queue_heap hdr values h,allocs),(ctx,c))).
Proof.
  intro Allocated; unfold init_queue, init_queue_heap, init_queue_logs;
    cbn [fst snd emit_list List.fold_right]; rewrite interp_nd_source_bind.
  etransitivity.
  - apply interp_nd_source_write_present.
    specialize (Allocated 0 ltac:(lia)); now rewrite Nat.add_0_r in Allocated.
  - rewrite !log_vis; apply sb_vis; intros _.
    rewrite interp_nd_source_bind; etransitivity.
    + apply interp_nd_source_write_present, upd_mono.
      specialize (Allocated 1 ltac:(lia)).
      replace (hdr + 1)%nat with (S hdr) in Allocated by lia; exact Allocated.
    + rewrite !log_vis; apply sb_vis; intros _.
      apply interp_nd_fill_nodes; intros offset O; apply upd_mono, upd_mono.
      replace (hdr + 2 + offset)%nat with (hdr + (2 + offset))%nat by lia.
      apply Allocated; lia.
Qed.

Lemma interp_nd_new_queue_first n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  values hdr (K : option nat -> thread sE Bn) h allocs ctx c :
  Nat.lt 0 hdr -> block_free h hdr (2 * S (length values)) ->
  (forall j, Nat.lt 0 j -> Nat.lt j hdr ->
    ~ block_free h j (2 * S (length values))) ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (new_queue values) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  emit_list (new_queue_logs hdr values (h,allocs))
    (interp_schedule_nd sh (S n) (ts @ i := K (Some hdr))
      (Some i) ((new_queue_heap hdr values h,
                 upd allocs hdr (2 * S (length values))),(ctx,c))).
Proof.
  intros Positive Free First.
  unfold new_queue; rewrite interp_nd_source_bind.
  rewrite interp_nd_source_alloc_first with (base:=hdr) by (try lia; assumption).
  unfold new_queue_logs; cbn [emit_list List.fold_right].
  rewrite !log_vis; apply sb_vis; intros _.
  unfold managed_alloc; cbn [fst snd].
  rewrite interp_nd_source_bind; etransitivity.
  - apply interp_nd_init_queue; intros offset O.
    unfold hunion; rewrite (hblock_in hdr (2 * S (length values)) offset O).
    discriminate.
  - apply emit_list_sbisim; rewrite interp_nd_source_ret; reflexivity.
Qed.

Lemma interp_nd_new_queue_empty n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  values (K : option nat -> thread sE Bn) ctx c :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (new_queue values) >>= K)) (Some i) (managed_empty,(ctx,c)) ~
  emit_list (new_queue_logs 1 values managed_empty)
    (interp_schedule_nd sh (S n) (ts @ i := K (Some 1))
      (Some i) ((new_queue_heap 1 values hemp,
                 upd hemp 1 (2 * S (length values))),(ctx,c))).
Proof.
  apply interp_nd_new_queue_first;
    [lia | intros offset Hlt; reflexivity | intros j Hj Hfirst; lia].
Qed.

Lemma run_nd_allocated_shared_queue values ctx c :
  run_nd (allocated_shared_queue values) (managed_empty,(ctx,c)) ~
  emit_list (new_queue_logs 1 values managed_empty)
    (run_nd (shared_queue 1)
      ((new_queue_heap 1 values hemp, upd hemp 1 (2 * S (length values))),(ctx,c))).
Proof.
  rewrite !run_nd_unfold; unfold allocated_shared_queue, denote.
  change (interp_schedule_nd sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (new_queue values) shared_queue) >>= fun _ => Ret tt))
    (Some Fin.F1) (managed_empty,(ctx,c)) ~
    emit_list (new_queue_logs 1 values managed_empty)
      (interp_schedule_nd sh 1
        ([Ret tt]%vector @ Fin.F1 :=
          (denote_flow (shared_queue 1) >>= fun _ => Ret tt))
        (Some Fin.F1)
        ((new_queue_heap 1 values hemp, upd hemp 1 (2 * S (length values))),(ctx,c)))).
  rewrite interp_nd_source_bind.
  etransitivity; [apply interp_nd_new_queue_empty |].
  reflexivity.
Qed.

(** Exact initialization under any scheduling policy.  The outer injection
    preserves the distinction between CSL logs and scheduler observations. *)

Lemma interp_fair_fill_nodes sch n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  first values (K : option unit -> thread sE Bn) st h allocs ctx c :
  (forall offset, Nat.lt offset (2 * length values) ->
     h (first + offset)%nat <> None) ->
  interp_schedule_fair sch sh (S n)
    (ts @ i := (denote_flow (fill_nodes first values) >>= K)) (Some i) st ((h,allocs),(ctx,c)) ~
  emit_list (List.map inl (fill_nodes_logs first values (h,allocs)))
    (interp_schedule_fair sch sh (S n) (ts @ i := K (Some tt))
      (Some i) st ((fill_nodes_heap first values h,allocs),(ctx,c))).
Proof.
  intro Allocated; unfold fill_nodes, fill_nodes_logs, fill_nodes_heap.
  apply interp_fair_write_list.
  intros a v Hin.
  assert (Hcell : In a (cells (node_addrs first (length values)))).
  { apply (node_writes_keys_subset (node_addrs first (length values)) values a).
    exact (in_map fst _ _ Hin). }
  apply node_cells_range in Hcell as [Hlo Hhi].
  replace a with (first + (a - first))%nat by lia.
  apply Allocated; lia.
Qed.

Lemma interp_fair_init_queue sch n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  hdr values (K : option unit -> thread sE Bn) st h allocs ctx c :
  (forall offset, Nat.lt offset (2 * S (length values)) ->
     h (hdr + offset)%nat <> None) ->
  interp_schedule_fair sch sh (S n)
    (ts @ i := (denote_flow (init_queue hdr values) >>= K)) (Some i) st ((h,allocs),(ctx,c)) ~
  emit_list (List.map inl (init_queue_logs hdr values (h,allocs)))
    (interp_schedule_fair sch sh (S n) (ts @ i := K (Some tt))
      (Some i) st ((init_queue_heap hdr values h,allocs),(ctx,c))).
Proof.
  intro Allocated; unfold init_queue, init_queue_heap, init_queue_logs;
    cbn [fst snd List.map emit_list List.fold_right]; rewrite interp_fair_bind.
  etransitivity.
  - apply interp_fair_write_present.
    specialize (Allocated 0 ltac:(lia)); now rewrite Nat.add_0_r in Allocated.
  - rewrite !log_vis; apply sb_vis; intros _.
    rewrite interp_fair_bind; etransitivity.
    + apply interp_fair_write_present, upd_mono.
      specialize (Allocated 1 ltac:(lia)).
      replace (hdr + 1)%nat with (S hdr) in Allocated by lia; exact Allocated.
    + rewrite !log_vis; apply sb_vis; intros _.
      apply interp_fair_fill_nodes; intros offset O; apply upd_mono, upd_mono.
      replace (hdr + 2 + offset)%nat with (hdr + (2 + offset))%nat by lia.
      apply Allocated; lia.
Qed.

Lemma interp_fair_new_queue_first sch n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  values hdr (K : option nat -> thread sE Bn) st h allocs ctx c :
  Nat.lt 0 hdr -> block_free h hdr (2 * S (length values)) ->
  (forall j, Nat.lt 0 j -> Nat.lt j hdr ->
    ~ block_free h j (2 * S (length values))) ->
  interp_schedule_fair sch sh (S n)
    (ts @ i := (denote_flow (new_queue values) >>= K)) (Some i) st ((h,allocs),(ctx,c)) ~
  emit_list (List.map inl (new_queue_logs hdr values (h,allocs)))
    (interp_schedule_fair sch sh (S n) (ts @ i := K (Some hdr))
      (Some i) st ((new_queue_heap hdr values h,
                    upd allocs hdr (2 * S (length values))),(ctx,c))).
Proof.
  intros Positive Free First.
  unfold new_queue; rewrite interp_fair_bind.
  rewrite interp_fair_alloc_first with (base:=hdr) by (try lia; assumption).
  unfold new_queue_logs; cbn [List.map emit_list List.fold_right].
  rewrite !log_vis; apply sb_vis; intros _.
  unfold managed_alloc; cbn [fst snd].
  rewrite interp_fair_bind; etransitivity.
  - apply interp_fair_init_queue; intros offset O.
    unfold hunion; rewrite (hblock_in hdr (2 * S (length values)) offset O).
    discriminate.
  - apply emit_list_sbisim; rewrite interp_fair_ret; reflexivity.
Qed.

Lemma interp_fair_new_queue_empty sch n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  values (K : option nat -> thread sE Bn) st ctx c :
  interp_schedule_fair sch sh (S n)
    (ts @ i := (denote_flow (new_queue values) >>= K)) (Some i) st (managed_empty,(ctx,c)) ~
  emit_list (List.map inl (new_queue_logs 1 values managed_empty))
    (interp_schedule_fair sch sh (S n) (ts @ i := K (Some 1))
      (Some i) st ((new_queue_heap 1 values hemp,
                    upd hemp 1 (2 * S (length values))),(ctx,c))).
Proof.
  apply interp_fair_new_queue_first;
    [lia | intros offset Hlt; reflexivity | intros j Hj Hfirst; lia].
Qed.

Lemma run_fair_allocated_shared_queue sch values st ctx c :
  run_fair sch (allocated_shared_queue values) st (managed_empty,(ctx,c)) ~
  emit_list (List.map inl (new_queue_logs 1 values managed_empty))
    (run_fair sch (shared_queue 1) st
      ((new_queue_heap 1 values hemp, upd hemp 1 (2 * S (length values))),(ctx,c))).
Proof.
  rewrite !run_fair_unfold; unfold allocated_shared_queue, denote.
  change (interp_schedule_fair sch sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (new_queue values) shared_queue) >>= fun _ => Ret tt))
    (Some Fin.F1) st (managed_empty,(ctx,c)) ~
    emit_list (List.map inl (new_queue_logs 1 values managed_empty))
      (interp_schedule_fair sch sh 1
        ([Ret tt]%vector @ Fin.F1 :=
          (denote_flow (shared_queue 1) >>= fun _ => Ret tt))
        (Some Fin.F1) st
        ((new_queue_heap 1 values hemp, upd hemp 1 (2 * S (length values))),(ctx,c)))).
  rewrite interp_fair_bind.
  etransitivity; [apply interp_fair_new_queue_empty |].
  reflexivity.
Qed.

Lemma interp_fair_new_queue sch n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  values (K : option nat -> thread sE Bn) st h allocs ctx c :
  heap_finite h ->
  exists hdr,
    Nat.lt 0 hdr /\ block_free h hdr (2 * S (length values)) /\
    heap_finite (new_queue_heap hdr values h) /\
    asep (qrepX hdr (queue_nodes hdr (length values)) values)
         (fun frame => heq frame h) (new_queue_heap hdr values h) /\
    interp_schedule_fair sch sh (S n)
      (ts @ i := (denote_flow (new_queue values) >>= K)) (Some i) st ((h,allocs),(ctx,c)) ~
    emit_list (List.map inl (new_queue_logs hdr values (h,allocs)))
      (interp_schedule_fair sch sh (S n) (ts @ i := K (Some hdr))
        (Some i) st ((new_queue_heap hdr values h,
                      upd allocs hdr (2 * S (length values))),(ctx,c))).
Proof.
  intro Finite.
  destruct (first_fit_exists h (2 * S (length values)) Finite ltac:(lia))
    as (hdr & Positive & Free & First).
  exists hdr; split; [exact Positive |]; split; [exact Free |]; split.
  - now apply new_queue_heap_finite.
  - split; [now apply new_queue_heap_owned |].
    apply interp_fair_new_queue_first; assumption.
Qed.

Theorem run_fair_allocated_parallel sch : forall values1 values2 st ctx c,
  exists u v h allocs,
    heap_finite h /\
    asep (qrepX u (queue_nodes u (length values1)) values1)
         (qrepX v (queue_nodes v (length values2)) values2) h /\
    run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty,(ctx,c)) ~
      emit_list (List.map inl (new_queue_logs u values1 managed_empty ++
        new_queue_logs v values2
          (new_queue_heap u values1 hemp,upd hemp u (2 * S (length values1)))))
        (run_fair sch (parallel_queues u v) st ((h,allocs),(ctx,c))).
Proof.
  intros values1 values2 st ctx c.
  set (done := fun _ : option unit => (Ret tt : thread sE Bn)).
  set (after1 := fun r : option nat =>
    match r with
    | None => done None
    | Some u => denote_flow
        (CBind (new_queue values2) (fun v => parallel_queues u v)) >>= done
    end).
  destruct (interp_fair_new_queue sch 0 [Ret tt]%vector Fin.F1 values1 after1 st hemp hemp ctx c
    heap_finite_hemp) as (u & Upos & Ufree & Finite1 & Own1 & Run1).
  set (h1 := new_queue_heap u values1 hemp).
  set (allocs1 := upd hemp u (2 * S (length values1))).
  set (after2 := fun r : option nat =>
    match r with
    | None => done None
    | Some v => denote_flow (parallel_queues u v) >>= done
    end).
  destruct (interp_fair_new_queue sch 0 [Ret tt]%vector Fin.F1 values2 after2 st h1 allocs1 ctx c
    Finite1) as (v & Vpos & Vfree & Finite2 & Own2 & Run2).
  exists u, v, (new_queue_heap v values2 h1), (upd allocs1 v (2 * S (length values2))).
  split; [exact Finite2 |]; split.
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
  - unfold allocated_parallel_queues.
    change (interp_schedule_fair sch sh 1
      ([Ret tt]%vector @ Fin.F1 :=
        (denote_flow (CBind (new_queue values1) (fun u =>
          CBind (new_queue values2) (fun v => parallel_queues u v))) >>= done))
      (Some Fin.F1) st ((hemp,hemp),(ctx,c)) ~
      emit_list (List.map inl (new_queue_logs u values1 managed_empty ++
        new_queue_logs v values2 (h1,allocs1)))
        (run_fair sch (parallel_queues u v) st
          ((new_queue_heap v values2 h1, upd allocs1 v (2 * S (length values2))),(ctx,c)))).
    rewrite interp_fair_bind.
    etransitivity; [exact Run1 |].
    rewrite List.map_app, emit_list_app; apply emit_list_sbisim.
    cbn [after1]; rewrite interp_fair_bind.
    etransitivity; [exact Run2|].
    apply emit_list_sbisim; reflexivity.
Qed.

(** Round-robin initialization preserves every snapshot via [inl]; these
    structural rules specialize the same policy-generic proofs. *)

Lemma interp_rr_fill_nodes n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  first values (K : option unit -> thread sE Bn) m h allocs ctx c :
  (forall offset, Nat.lt offset (2 * length values) ->
     h (first + offset)%nat <> None) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (fill_nodes first values) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  emit_list (List.map inl (fill_nodes_logs first values (h,allocs)))
    (interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
      (Some i) m ((fill_nodes_heap first values h,allocs),(ctx,c))).
Proof.
  apply (interp_fair_fill_nodes rr_scheduler).
Qed.

Lemma interp_rr_init_queue n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  hdr values (K : option unit -> thread sE Bn) m h allocs ctx c :
  (forall offset, Nat.lt offset (2 * S (length values)) ->
     h (hdr + offset)%nat <> None) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (init_queue hdr values) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  emit_list (List.map inl (init_queue_logs hdr values (h,allocs)))
    (interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
      (Some i) m ((init_queue_heap hdr values h,allocs),(ctx,c))).
Proof.
  apply (interp_fair_init_queue rr_scheduler).
Qed.

Lemma interp_rr_new_queue_first n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  values hdr (K : option nat -> thread sE Bn) m h allocs ctx c :
  Nat.lt 0 hdr -> block_free h hdr (2 * S (length values)) ->
  (forall j, Nat.lt 0 j -> Nat.lt j hdr ->
    ~ block_free h j (2 * S (length values))) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (new_queue values) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  emit_list (List.map inl (new_queue_logs hdr values (h,allocs)))
    (interp_schedule_rr sh (S n) (ts @ i := K (Some hdr))
      (Some i) m ((new_queue_heap hdr values h,
                   upd allocs hdr (2 * S (length values))),(ctx,c))).
Proof.
  apply (interp_fair_new_queue_first rr_scheduler).
Qed.

Lemma interp_rr_new_queue_empty n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  values (K : option nat -> thread sE Bn) m ctx c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (new_queue values) >>= K)) (Some i) m (managed_empty,(ctx,c)) ~
  emit_list (List.map inl (new_queue_logs 1 values managed_empty))
    (interp_schedule_rr sh (S n) (ts @ i := K (Some 1))
      (Some i) m ((new_queue_heap 1 values hemp,
                   upd hemp 1 (2 * S (length values))),(ctx,c))).
Proof.
  apply (interp_fair_new_queue_empty rr_scheduler).
Qed.

Lemma run_rr_allocated_shared_queue values ctx c :
  run_rr (allocated_shared_queue values) (managed_empty,(ctx,c)) ~
  emit_list (List.map inl (new_queue_logs 1 values managed_empty))
    (run_rr (shared_queue 1)
      ((new_queue_heap 1 values hemp, upd hemp 1 (2 * S (length values))),(ctx,c))).
Proof.
  apply (run_fair_allocated_shared_queue rr_scheduler values 0 ctx c).
Qed.

Lemma interp_rr_new_queue n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  values (K : option nat -> thread sE Bn) m h allocs ctx c :
  heap_finite h ->
  exists hdr,
    Nat.lt 0 hdr /\ block_free h hdr (2 * S (length values)) /\
    heap_finite (new_queue_heap hdr values h) /\
    asep (qrepX hdr (queue_nodes hdr (length values)) values)
         (fun frame => heq frame h) (new_queue_heap hdr values h) /\
    interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow (new_queue values) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
    emit_list (List.map inl (new_queue_logs hdr values (h,allocs)))
      (interp_schedule_rr sh (S n) (ts @ i := K (Some hdr))
        (Some i) m ((new_queue_heap hdr values h,
                     upd allocs hdr (2 * S (length values))),(ctx,c))).
Proof.
  apply (interp_fair_new_queue rr_scheduler).
Qed.

Theorem run_rr_allocated_parallel : forall values1 values2 ctx c,
  exists u v h allocs,
    heap_finite h /\
    asep (qrepX u (queue_nodes u (length values1)) values1)
         (qrepX v (queue_nodes v (length values2)) values2) h /\
    run_rr (allocated_parallel_queues values1 values2) (managed_empty,(ctx,c)) ~
      emit_list (List.map inl (new_queue_logs u values1 managed_empty ++
        new_queue_logs v values2
          (new_queue_heap u values1 hemp,upd hemp u (2 * S (length values1)))))
        (run_rr (parallel_queues u v) ((h,allocs),(ctx,c))).
Proof.
  intros values1 values2 ctx c.
  exact (run_fair_allocated_parallel rr_scheduler values1 values2 0 ctx c).
Qed.

(** An allocated empty first queue has head pointer [0], and the null cell is
    unallocated: the first source turn faults, whatever the second queue is. *)
Lemma allocated_parallel_queues_empty_stuck values ctx c :
  exists u v,
    run_rr (allocated_parallel_queues [] values) (managed_empty,(ctx,c)) ~
      emit_list (List.map inl (new_queue_logs u [] managed_empty ++
        new_queue_logs v values (new_queue_heap u [] hemp,upd hemp u 2)))
        (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  destruct (run_rr_allocated_parallel [] values ctx c)
    as (u & v & h & allocs & _ & Owned & Run).
  destruct (owned_queues_sound _ _ _ _ _ _ _ Owned)
    as ((_ & Hhead & _ & _ & Hnull & _) & _ & _).
  change (h (S u) = Some 0) in Hhead.
  exists u, v; rewrite Run; apply emit_list_sbisim.
  apply parallel_queues_first_turn_stuck.
  unfold turn, turnk, queue_turn.
  etransitivity; [eapply (interp_heapW_rd CSLHeap
    (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))); exact Hhead|].
  queue_fault Hnull.
Qed.
