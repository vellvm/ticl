(** * An allocated queue client: passive framing and runner-safe source reuse.

    The source split changes neither effect order nor yield boundaries.  Its
    finite helper equation is lifted structurally before applying the actual
    round-robin runner congruence.  The recurrent proof reuses [SharedInv] and
    the existing ranked-turn certificate, then applies the generic semantic
    frame rule to the initialized owned resource. *)
From Stdlib Require Import Arith.PeanoNat Fin Vector List Lia.
From Coinduction Require Import all.
From CTree Require Import Eq.IterFacts.
From TICL Require Import CTree.Core CTree.Events.Writer Logic.Core Lang.CSL.Frame
  CTree.Interp.Yield.RoundRobin CTree.Interp.Yield.SBisim.
From examples Require Import CSL.Queue.Program CSL.Queue.Shared
  CSL.Queue.Representation CSL.Queue.Frame CSL.Queue.Layout CSL.Queue.Trace
  CSL.Queue.Operations.

Import CTree CTreeNotations TiclNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.
Local Open Scope pcm_scope.

Definition read_queue_head (hdr : nat) : CProg (nat * nat) :=
  CBind (CRead (S hdr)) (fun a =>
  CBind (CRead a) (fun v => CRet (a,v))).

Definition rotate_captured (tag hdr a v : nat) : CProg unit :=
  CBind (CEmit tag v) (fun _ =>
  CBind (CRead (S a)) (fun n =>
  CBind (CWrite (S hdr) n) (fun _ =>
  CBind (CRead hdr) (fun z0 =>
  CBind (CWrite (S (if Nat.eqb n 0 then hdr else z0)) a) (fun _ =>
  CBind (CWrite (S a) 0) (fun _ => CWrite hdr a)))))).

Definition rotate_once_split (tag hdr : nat) : CProg unit :=
  CBind (read_queue_head hdr)
    (fun av => rotate_captured tag hdr (fst av) (snd av)).

Definition worker_split (tag hdr : nat) : CProg unit :=
  CUntilNone
    (CBind (rotate_once_split tag hdr) (fun _ =>
     CBind CYield (fun _ => CRet (Some tt)))).

Definition shared_queue_split (hdr : nat) : CProg unit :=
  CBind (CFork (worker_split 1 hdr)) (fun _ =>
  CBind (CFork (worker_split 2 hdr)) (fun _ => CRet tt)).

Definition allocated_shared_queue_split values : CProg unit :=
  CBind (new_queue values) shared_queue_split.

(** Finite source unfolding and monad laws remove the captured-pair return.
    This normalization does not unfold an iteration or a scheduler. *)

Local Lemma rotate_once_split_cps_equ {X} tag hdr
  (K : option unit -> ctree CEff Bn X) :
  (denote_flow (rotate_once_split tag hdr) >>= K) ≅
  (denote_flow (rotate_once tag hdr) >>= K).
Proof.
  unfold rotate_once_split, read_queue_head, rotate_captured, rotate_once.
  cbn [denote_flow].
  repeat first [progress setoid_rewrite bind_bind | progress setoid_rewrite bind_ret_l].
  cbn [fst snd]; reflexivity.
Qed.

Lemma rotate_once_split_cps tag hdr
  (K : option unit -> thread sE Bn) :
  (denote_flow (rotate_once_split tag hdr) >>= K) ≅
  (denote_flow (rotate_once tag hdr) >>= K).
Proof. apply rotate_once_split_cps_equ. Qed.

Local Lemma rotate_once_split_equ tag hdr :
  denote_flow (rotate_once_split tag hdr) ≅ denote_flow (rotate_once tag hdr).
Proof.
  pose proof (rotate_once_split_cps_equ tag hdr
    (fun x : option unit => (Ret x : ctree CEff Bn (option unit)))) as H.
  now rewrite !bind_ret_r in H.
Qed.

Local Lemma source_bind_equ {A B} (p q : CProg A)
  (next next' : A -> CProg B) :
  denote_flow p ≅ denote_flow q ->
  (forall a, denote_flow (next a) ≅ denote_flow (next' a)) ->
  denote_flow (CBind p next) ≅ denote_flow (CBind q next').
Proof.
  intros Hp Hnext.
  cbn [denote_flow].
  apply equ_clo_bind with (S:=eq); [exact Hp|].
  intros [a|] y <-; [apply Hnext|reflexivity].
Qed.

Lemma denote_flow_worker_split tag hdr :
  denote_flow (worker_split tag hdr) ≅ denote_flow (worker tag hdr).
Proof.
  change (CTree.iter (fun _ : unit =>
    denote_flow (CBind (rotate_once_split tag hdr) (fun _ =>
      CBind CYield (fun _ => CRet (Some tt)))) >>=
      fun flow => match flow with
      | None => Ret (inr None)
      | Some None => Ret (inr (Some tt))
      | Some (Some _) => Ret (inl tt) end) tt ≅
    CTree.iter (fun _ : unit =>
    denote_flow (CBind (rotate_once tag hdr) (fun _ =>
      CBind CYield (fun _ => CRet (Some tt)))) >>=
      fun flow => match flow with
      | None => Ret (inr None)
      | Some None => Ret (inr (Some tt))
      | Some (Some _) => Ret (inl tt) end) tt).
  apply (iter_equ (R:=eq)); [|reflexivity].
  intros [] [] _.
  apply equ_clo_bind with (S:=eq).
  - apply source_bind_equ; [apply rotate_once_split_equ|intro; reflexivity].
  - intros x y <-; reflexivity.
Qed.

Lemma denote_worker_split tag hdr :
  denote (worker_split tag hdr) ≅ denote (worker tag hdr).
Proof.
  unfold denote; apply equ_clo_bind with (S:=eq);
    [apply denote_flow_worker_split|intros x y <-; reflexivity].
Qed.

Lemma worker_split_pool_rr hdr focus cursor s :
  run_rr_pool [worker_split 2 hdr; worker_split 1 hdr]%vector focus cursor s ~
  run_rr_pool [worker 2 hdr; worker 1 hdr]%vector focus cursor s.
Proof.
  unfold run_rr_pool; apply interp_schedule_rr_guard_equ.
  intros i; dependent destruction i; [|dependent destruction i; [|dependent destruction i]];
    cbn [csl_pool Vector.map]; apply guard_equ_equ, denote_worker_split.
Qed.

Lemma shared_queue_split_rr hdr s :
  run_rr (shared_queue_split hdr) s ~ run_rr (shared_queue hdr) s.
Proof.
  unfold shared_queue_split, shared_queue; rewrite !run_rr_two_forks.
  apply worker_split_pool_rr.
Qed.

Local Lemma source_fork_equ (p q : CProg unit) :
  denote_flow p ≅ denote_flow q ->
  denote_flow (CFork p) ≅ denote_flow (CFork q).
Proof.
  intro H; cbn [denote_flow].
  apply equ_clo_bind_eq; intros []; [|reflexivity].
  apply equ_clo_bind with (S:=eq); [exact H|intros x y <-; reflexivity].
Qed.

Local Lemma shared_queue_split_equ hdr :
  denote_flow (shared_queue_split hdr) ≅ denote_flow (shared_queue hdr).
Proof.
  unfold shared_queue_split, shared_queue.
  apply source_bind_equ; [apply source_fork_equ, denote_flow_worker_split|intro].
  apply source_bind_equ; [apply source_fork_equ, denote_flow_worker_split|intro; reflexivity].
Qed.

Lemma allocated_shared_queue_split_rr values s :
  run_rr (allocated_shared_queue_split values) s ~
  run_rr (allocated_shared_queue values) s.
Proof.
  unfold run_rr, run_rr_pool; apply interp_schedule_rr_guard_equ.
  intros i; dependent destruction i; [|dependent destruction i].
  cbn [csl_pool Vector.map]; apply guard_equ_equ.
  unfold denote; apply equ_clo_bind with (S:=eq); [|intros x y <-; reflexivity].
  unfold allocated_shared_queue_split, allocated_shared_queue.
  apply source_bind_equ; [reflexivity|apply shared_queue_split_equ].
Qed.

Lemma qheap_managed_wf hdr values :
  0 < hdr ->
  managed_wf
    (qheap hdr (queue_nodes hdr (length values)) values,
     upd hemp hdr (2 * S (length values))).
Proof.
  intro Positive; split; cbn [fst snd].
  - intros base size Recorded; unfold upd in Recorded.
    destruct (Nat.eqb_spec base hdr); [subst base|discriminate].
    inversion Recorded; subst size; split; [exact Positive|split; [lia|]].
    intros x Range; eapply qrep_fp; [now apply qheap_queue_nodes_rep|].
    now apply queue_cells_range.
  - intros b1 n1 b2 n2 H1 H2 Different.
    unfold upd in H1, H2.
    destruct (Nat.eqb_spec b1 hdr); [|discriminate].
    destruct (Nat.eqb_spec b2 hdr); [congruence|discriminate].
Qed.

Lemma initialized_queue_frame_rel hdr values f ctx c :
  0 < hdr -> block_free f hdr (2 * S (length values)) ->
  frame_rel (f,hemp)
    ((qheap hdr (queue_nodes hdr (length values)) values,
      upd hemp hdr (2 * S (length values))),(ctx,c))
    ((new_queue_heap hdr values f,
      upd hemp hdr (2 * S (length values))),(ctx,c)).
Proof.
  intros Positive Free; unfold frame_rel, frame_inv, csl_memory; cbn [fst snd]; split.
  - split.
    + split; [now apply new_queue_heap_disjoint|apply hdisj_sym, hdisj_hemp].
    + now apply qheap_managed_wf.
  - split; [reflexivity|].
    split; [now apply new_queue_heap_agrees|].
    change (heq (upd hemp hdr (2 * S (length values)))
      (hunion (upd hemp hdr (2 * S (length values))) hemp)).
    intro x; unfold hunion; destruct (upd hemp hdr (2 * S (length values)) x);
      reflexivity.
Qed.

Lemma allocated_shared_queue_rr_contract values f ctx c :
  heap_finite f ->
  exists hdr,
    0 < hdr /\ block_free f hdr (2 * S (length values)) /\
    asep (qrepX hdr (queue_nodes hdr (length values)) values)
         (fun frame => heq frame f) (new_queue_heap hdr values f) /\
    frame_rel (f,hemp)
      ((qheap hdr (queue_nodes hdr (length values)) values,
        upd hemp hdr (2 * S (length values))),(ctx,c))
      ((new_queue_heap hdr values f,
        upd hemp hdr (2 * S (length values))),(ctx,c)) /\
    run_rr (allocated_shared_queue values) ((f,hemp),(ctx,c)) ~
      run_rr (shared_queue hdr)
        ((new_queue_heap hdr values f,
          upd hemp hdr (2 * S (length values))),(ctx,c)).
Proof.
  intro Finite.
  destruct (interp_rr_new_queue 0 [Ret tt]%vector Fin.F1 values
    (fun flow => match flow with None => Ret tt | Some hdr => denote (shared_queue hdr) end)
    0 f hemp ctx c Finite)
    as (hdr & Positive & Free & _ & Owned & Run).
  exists hdr; split; [exact Positive|split; [exact Free|]].
  split; [exact Owned|split; [now apply initialized_queue_frame_rel|]].
  rewrite !run_rr_unfold; unfold allocated_shared_queue, denote.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (new_queue values) shared_queue) >>= fun _ => Ret tt))
    (Some Fin.F1) 0 ((f,hemp),(ctx,c)) ~
    interp_schedule_rr sh 1
      ([Ret tt]%vector @ Fin.F1 :=
        (denote_flow (shared_queue hdr) >>= fun _ => Ret tt))
      (Some Fin.F1) 0
      ((new_queue_heap hdr values f, upd hemp hdr (2 * S (length values))),(ctx,c))).
  rewrite interp_rr_bind; exact Run.
Qed.

Local Lemma shared_queue_alloc_free hdr : alloc_free (shared_queue hdr).
Proof.
  unfold alloc_free, shared_queue, worker, rotate_once.
  cbn [prog_ok okE_thread no_alloc_sE]; repeat (split || intro); try exact I.
Qed.

Theorem allocated_shared_queue_passive_fresh_rr values nl d k f ctx c :
  heap_finite f -> find_index Nat.eqb nl values = Some d ->
  <( {run_rr (allocated_shared_queue values) ((f,hemp),(ctx,c))},
     Pure |= AG (AF visW {shared_pop_after nl k}) )>.
Proof.
  intros Finite Member.
  destruct (allocated_shared_queue_rr_contract values f ctx c Finite)
    as (hdr & Positive & Free & Owned & Related & Run).
  rewrite Run.
  unfold run_rr, run_rr_pool, interp_schedule_rr.
  eapply (ticll_csl_frame (f,hemp)).
  - apply run_rr_framable, shared_queue_alloc_free.
  - exact Related.
  - change <( {run_rr (shared_queue hdr)
      ((qheap hdr (queue_nodes hdr (length values)) values,
        upd hemp hdr (2 * S (length values))),(ctx,c))},
      Pure |= AG (AF visW {shared_pop_after nl k}) )>.
    eapply shared_rotate_agaf_pop_rr_fresh;
      [now apply qheap_queue_nodes_rep|exact Member].
Qed.

Theorem allocated_shared_queue_split_passive_fresh_rr values nl d k f ctx c :
  heap_finite f -> find_index Nat.eqb nl values = Some d ->
  <( {run_rr (allocated_shared_queue_split values) ((f,hemp),(ctx,c))},
     Pure |= AG (AF visW {shared_pop_after nl k}) )>.
Proof.
  intros Finite Member; rewrite allocated_shared_queue_split_rr.
  eapply allocated_shared_queue_passive_fresh_rr; eassumption.
Qed.

Corollary client_passive_10 k :
  <( {run_rr (allocated_shared_queue [10;20;30])
       ((upd hemp 100 7,hemp),(List.nil,0))},
     Pure |= AG (AF visW {shared_pop_after 10 k}) )>.
Proof.
  eapply allocated_shared_queue_passive_fresh_rr with (d:=0).
  - apply heap_finite_upd, heap_finite_hemp.
  - reflexivity.
Qed.

Corollary client_split_passive_10 k :
  <( {run_rr (allocated_shared_queue_split [10;20;30])
       ((upd hemp 100 7,hemp),(List.nil,0))},
     Pure |= AG (AF visW {shared_pop_after 10 k}) )>.
Proof.
  rewrite allocated_shared_queue_split_rr; apply client_passive_10.
Qed.

Definition client_heap := new_queue_heap 1 [10;20;30] (upd hemp 100 7).

Local Lemma client_block_free : block_free (upd hemp 100 7) 1 8.
Proof.
  intros offset Bound; unfold upd.
  destruct (Nat.eqb_spec (1 + offset) 100); [lia|reflexivity].
Qed.

Local Lemma client_heap_rep : qrep 1 [3;5;7] [10;20;30] client_heap.
Proof.
  pose proof (qheap_queue_nodes_rep 1 [10;20;30] ltac:(lia)) as Owned.
  eapply qrep_agree_fp; [exact Owned| |].
  - intros x InFootprint; unfold client_heap.
    rewrite (new_queue_heap_agrees 1 [10;20;30] (upd hemp 100 7)
      ltac:(lia) client_block_free x).
    apply hunion_eq; eapply qrep_fp; eassumption.
  - reflexivity.
Qed.

Local Lemma client_initialization :
  run_rr (allocated_shared_queue [10;20;30])
    ((upd hemp 100 7,hemp),(List.nil,0)) ~
  run_rr (shared_queue 1) ((client_heap,upd hemp 1 8),(List.nil,0)).
Proof.
  rewrite !run_rr_unfold; unfold allocated_shared_queue, denote.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (new_queue [10;20;30]) shared_queue) >>= fun _ => Ret tt))
    (Some Fin.F1) 0 ((upd hemp 100 7,hemp),(List.nil,0)) ~
    interp_schedule_rr sh 1
      ([Ret tt]%vector @ Fin.F1 :=
        (denote_flow (shared_queue 1) >>= fun _ => Ret tt))
      (Some Fin.F1) 0 ((client_heap,upd hemp 1 8),(List.nil,0))).
  rewrite interp_rr_bind; apply interp_rr_new_queue_first.
  - lia.
  - exact client_block_free.
  - intros j Positive Earlier; lia.
Qed.

(** Three scheduler picks, each followed by a complete constructor-backed
    turn.  The suffix records the actual cursor, not a claimed state cycle. *)
Theorem client_split_prefix3 :
  run_rr (allocated_shared_queue_split [10;20;30])
    ((upd hemp 100 7,hemp),(List.nil,0)) ~
  Step (log (inr (stamp (2,10) 0) : CSLObs (nat * nat));;
   Step (log (inr (stamp (1,20) 1) : CSLObs (nat * nat));;
    Step (log (inr (stamp (2,30) 2) : CSLObs (nat * nat));;
     run_rr_pool [worker 2 1; worker 1 1]%vector None 3
       ((qstepN 1 3 [3;5;7] client_heap,upd hemp 1 8),(List.nil,3))))).
Proof.
  rewrite allocated_shared_queue_split_rr, client_initialization.
  unfold shared_queue; rewrite run_rr_two_forks.
  pose proof client_heap_rep as Hq0.
  pose proof (qstep_qrep 1 [3;5;7] [10;20;30] client_heap Hq0 ltac:(discriminate)) as Hq1.
  change (qrep 1 [5;7;3] [20;30;10] (qstep 1 [3;5;7] client_heap)) in Hq1.
  pose proof (qstep_qrep 1 [5;7;3] [20;30;10] _ Hq1 ltac:(discriminate)) as Hq2.
  change (qrep 1 [7;3;5] [30;10;20]
    (qstep 1 [5;7;3] (qstep 1 [3;5;7] client_heap))) in Hq2.
  rewrite (run_rr_pool_select [worker 2 1; worker 1 1]%vector 0), (rr_pick_even 0 eq_refl).
  apply sb_step; etransitivity;
    [exact (run_rr_pool_turn [worker 2 1; worker 1 1]%vector Fin.F1 1 _ _ _
      (exact_worker_turn 2 1 3 [5;7] 10 [20;30] client_heap
        (upd hemp 1 8) List.nil 0 Hq0))|].
  cbn [emit_list List.fold_right]; rewrite !log_vis; apply sb_vis; intros _.
  rewrite (run_rr_pool_select [worker 2 1; worker 1 1]%vector 1), (rr_pick_odd 1 eq_refl).
  apply sb_step; etransitivity;
    [exact (run_rr_pool_turn [worker 2 1; worker 1 1]%vector (Fin.FS Fin.F1) 2 _ _ _
      (exact_worker_turn 1 1 5 [7;3] 20 [30;10] (qstep 1 [3;5;7] client_heap)
        (upd hemp 1 8) List.nil 1 Hq1))|].
  cbn [emit_list List.fold_right]; rewrite !log_vis; apply sb_vis; intros _.
  rewrite (run_rr_pool_select [worker 2 1; worker 1 1]%vector 2), (rr_pick_even 2 eq_refl).
  apply sb_step; etransitivity;
    [exact (run_rr_pool_turn [worker 2 1; worker 1 1]%vector Fin.F1 3 _ _ _
      (exact_worker_turn 2 1 7 [3;5] 30 [10;20]
        (qstep 1 [5;7;3] (qstep 1 [3;5;7] client_heap))
        (upd hemp 1 8) List.nil 2 Hq2))|].
  cbn [emit_list List.fold_right]; rewrite !log_vis; apply sb_vis; intros _.
  reflexivity.
Qed.

Theorem client_frame_preserved n :
  qstepN 1 n [3;5;7] client_heap 100 = Some 7.
Proof.
  assert (Outside : ~ In 100 (qcells 1 [3;5;7])).
  { change (List.In 100 [1;2;3;4;5;6;7;8]%list -> False); cbn; intuition congruence. }
  pose proof (frame_preserved n 1 [3;5;7] [10;20;30] client_heap
    client_heap_rep ltac:(discriminate) 100) as Frame.
  rewrite !qfrm_out in Frame by exact Outside.
  rewrite <- Frame; reflexivity.
Qed.

Theorem client_heap_cycle3 :
  heq (qstepN 1 3 [3;5;7] client_heap) client_heap.
Proof.
  intro x.
  destruct (in_dec Nat.eq_dec x (qcells 1 [3;5;7])) as [Inside|Outside].
  - change (List.In x [1;2;3;4;5;6;7;8]%list) in Inside; cbn in Inside.
    repeat destruct Inside as [Inside|Inside]; try contradiction; subst x; reflexivity.
  - exact (qstepN_agree 3 1 [3;5;7] [10;20;30] client_heap
      client_heap_rep ltac:(discriminate) x Outside).
Qed.
