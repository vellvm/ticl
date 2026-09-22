From Stdlib Require Import Arith.PeanoNat Fin Vector Lia.
From ExtLib Require Import Data.Monads.StateMonad.
From TICL Require Import
  Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Interp.State.Mod
  ICTree.Interp.Yield.RoundRobin Utils.Vectors.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.


Definition shared_write_program : CProg unit :=
  CBind (CFork (CBind (CRead 4) (fun v => CEmit 2 v)))
    (fun _ => CBind (CWrite 4 9) (fun _ => CYield)).

Lemma shared_write_seen :
  run_rr shared_write_program (Pcm.hsingle 4 0) 0 ~
  (log (SPop 2 9 0);;
   Ret (tt, (upd (Pcm.hsingle 4 0) 4 9, 1))).
Proof.
  unfold shared_write_program; rewrite run_rr_fork_bind.
  change (interp_schedule_rr sh 2
    ([denote (CBind (CRead 4) (fun v => CEmit 2 v)); Ret tt]%vector
      @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CWrite 4 9) (fun _ => CYield)) >>= fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) 0 (Pcm.hsingle 4 0,0) ~
    (log (SPop 2 9 0);; Ret (tt,(upd (Pcm.hsingle 4 0) 4 9,1)))).
  rewrite interp_rr_bind.
  rewrite interp_rr_write_present by discriminate.
  rewrite interp_rr_yield, interp_schedule_rr_select.
  change (interp_schedule_rr sh 2
    ([Ret tt; Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CRead 4) (fun v => CEmit 2 v)) >>= fun _ => Ret tt))
    (Some Fin.F1) 1 (upd (Pcm.hsingle 4 0) 4 9,0) ~
    (log (SPop 2 9 0);; Ret (tt,(upd (Pcm.hsingle 4 0) 4 9,1)))).
  rewrite interp_rr_bind.
  rewrite interp_rr_read_value with (value:=9) by reflexivity.
  rewrite interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  finish_pool.
Qed.

Definition scoped_child_program : CProg unit :=
  CBind
    (CUntilNone
      (CBind (CFork (CEmit 2 20))
        (fun _ => CBind (CEmit 1 10)
          (fun _ => CRet (None : option unit)))))
    (fun _ => CEmit 1 11).

Lemma scoped_child_halts :
  run_rr scoped_child_program hemp 0 ~
  (log (SPop 1 10 0);;
   log (SPop 1 11 1);;
   log (SPop 2 20 2);;
   Ret (tt,(hemp,3))).
Proof.
  set (body := CBind (CFork (CEmit 2 20))
    (fun _ => CBind (CEmit 1 10) (fun _ => CRet (None : option unit)))).
  set (done := fun _ : option unit => (Ret tt : thread sE)).
  set (after := fun r : option unit =>
    match r with None => done None | Some _ => denote_flow (CEmit 1 11) >>= done end).
  set (next := fun r : option (option unit) =>
    match r with
    | None => after None
    | Some None => after (Some tt)
    | Some (Some _) => Guard (denote_flow (CUntilNone body) >>= after)
    end).
  unfold run_rr, scoped_child_program.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CUntilNone body) (fun _ => CEmit 1 11)) >>= done))
    (Some Fin.F1) 0 (hemp,0) ~
    (log (SPop 1 10 0);; log (SPop 1 11 1);; log (SPop 2 20 2);; Ret (tt,(hemp,3)))).
  rewrite interp_rr_bind, interp_rr_until_none.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 := (denote_flow body >>= next))
    (Some Fin.F1) 0 (hemp,0) ~
    (log (SPop 1 10 0);; log (SPop 1 11 1);; log (SPop 2 20 2);; Ret (tt,(hemp,3)))).
  unfold body at 1; rewrite interp_rr_bind, interp_rr_fork.
  change (interp_schedule_rr sh 2
    ([denote (CEmit 2 20); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CEmit 1 10) (fun _ => CRet (None : option unit))) >>= next))
    (Some (Fin.FS Fin.F1)) 0 (hemp,0) ~
    (log (SPop 1 10 0);; log (SPop 1 11 1);; log (SPop 2 20 2);; Ret (tt,(hemp,3)))).
  rewrite interp_rr_bind, interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite interp_rr_ret.
  change (interp_schedule_rr sh 2
    ([denote (CEmit 2 20); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CEmit 1 11) >>= done))
    (Some (Fin.FS Fin.F1)) 0 (hemp,1) ~
    (log (SPop 1 11 1);; log (SPop 2 20 2);; Ret (tt,(hemp,3)))).
  rewrite interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  erewrite interp_schedule_rr_ret by source_observe.
  pool_simpl; rewrite vector_remove_tail, vector_remove_head.
  rewrite interp_schedule_rr_select.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 := (denote_flow (CEmit 2 20) >>= done))
    (Some Fin.F1) 1 (hemp,2) ~
    (log (SPop 2 20 2);; Ret (tt,(hemp,3)))).
  rewrite interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  unfold done; finish_pool.
Qed.

Definition finite_tagged_program : CProg unit :=
  CBind
    (CFork (CBind (CEmit 2 9) (fun _ =>
      CBind CYield (fun _ => CEmit 2 10))))
    (fun _ => CBind (CEmit 1 7) (fun _ =>
      CBind CYield (fun _ => CEmit 1 8))).

Lemma finite_tagged_round_robin :
  run_rr finite_tagged_program hemp 0 ~
  (log (SPop 1 7 0);; log (SPop 2 9 1);;
   log (SPop 1 8 2);; log (SPop 2 10 3);;
   Ret (tt,(hemp,4))).
Proof.
  unfold finite_tagged_program; rewrite run_rr_fork_bind.
  change (interp_schedule_rr sh 2
    ([denote (CBind (CEmit 2 9) (fun _ => CBind CYield (fun _ => CEmit 2 10))); Ret tt]%vector
      @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CEmit 1 7) (fun _ => CBind CYield (fun _ => CEmit 1 8)))
        >>= fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) 0 (hemp,0) ~
    (log (SPop 1 7 0);; log (SPop 2 9 1);; log (SPop 1 8 2);;
     log (SPop 2 10 3);; Ret (tt,(hemp,4)))).
  rewrite interp_rr_bind, interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite interp_rr_bind, interp_rr_yield, interp_schedule_rr_select.
  change (interp_schedule_rr sh 2
    ([Ret tt; denote (CEmit 1 8)]%vector @ Fin.F1 :=
      (denote_flow (CBind (CEmit 2 9) (fun _ => CBind CYield (fun _ => CEmit 2 10)))
        >>= fun _ => Ret tt))
    (Some Fin.F1) 1 (hemp,1) ~
    (log (SPop 2 9 1);; log (SPop 1 8 2);; log (SPop 2 10 3);; Ret (tt,(hemp,4)))).
  rewrite interp_rr_bind, interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite interp_rr_bind, interp_rr_yield, interp_schedule_rr_select.
  change (interp_schedule_rr sh 2
    ([denote (CEmit 2 10); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CEmit 1 8) >>= fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) 2 (hemp,2) ~
    (log (SPop 1 8 2);; log (SPop 2 10 3);; Ret (tt,(hemp,4)))).
  rewrite interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  erewrite interp_schedule_rr_ret by source_observe.
  pool_simpl; rewrite vector_remove_tail, vector_remove_head.
  rewrite interp_schedule_rr_select.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 := (denote_flow (CEmit 2 10) >>= fun _ => Ret tt))
    (Some Fin.F1) 3 (hemp,3) ~
    (log (SPop 2 10 3);; Ret (tt,(hemp,4)))).
  rewrite interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  finish_pool.
Qed.

Definition allocation_zero_read : CProg unit :=
  CBind (CAlloc 2) (fun base =>
  CBind (CRead (S base)) (fun value => CEmit 9 value)).

Lemma allocation_zero_read_seen :
  run_rr allocation_zero_read hemp 0 ~
  (log (SPop 9 0 0);; Ret (tt,(hunion (hblock 1 2) hemp,1))).
Proof.
  unfold run_rr, allocation_zero_read.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CAlloc 2) (fun base =>
        CBind (CRead (S base)) (fun value => CEmit 9 value))) >>=
        fun _ => Ret tt))
    (Some Fin.F1) 0 (hemp,0) ~
    (log (SPop 9 0 0);; Ret (tt,(hunion (hblock 1 2) hemp,1)))).
  rewrite interp_rr_bind.
  rewrite interp_rr_alloc_first with (base:=1) by
    (try lia; apply block_freeb_spec; reflexivity).
  rewrite interp_rr_bind.
  rewrite interp_rr_read_value with (value:=0) by reflexivity.
  rewrite interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  finish_pool.
Qed.

Definition allocating_thread (tag : nat) : CProg unit :=
  CBind (CAlloc 2) (fun base =>
  CBind (CWrite base tag) (fun _ =>
  CBind (CEmit tag base) (fun _ => CYield))).

Definition shared_alloc_program : CProg unit :=
  CBind (CFork (allocating_thread 2)) (fun _ => allocating_thread 1).

Definition alloc_parent_heap := upd (hunion (hblock 1 2) hemp) 1 1.
Definition alloc_both_heap := upd (hunion (hblock 3 2) alloc_parent_heap) 3 2.

Lemma shared_alloc_seen :
  run_rr shared_alloc_program hemp 0 ~
  (log (SPop 1 1 0);; log (SPop 2 3 1);; Ret (tt,(alloc_both_heap,2))).
Proof.
  assert (First : forall j, Nat.lt 0 j -> Nat.lt j 3 ->
    ~ block_free alloc_parent_heap j 2).
  { intros j J L F; assert (j = 1 \/ j = 2) as Cases by lia.
    destruct Cases as [-> | ->];
      specialize (F 0 ltac:(lia)); discriminate F. }
  unfold shared_alloc_program; rewrite run_rr_fork_bind.
  change (interp_schedule_rr sh 2
    ([denote (allocating_thread 2); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CAlloc 2) (fun base =>
        CBind (CWrite base 1) (fun _ =>
        CBind (CEmit 1 base) (fun _ => CYield)))) >>= fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) 0 (hemp,0) ~
    (log (SPop 1 1 0);; log (SPop 2 3 1);; Ret (tt,(alloc_both_heap,2)))).
  rewrite interp_rr_bind.
  rewrite interp_rr_alloc_first with (base:=1) by
    (try lia; apply block_freeb_spec; reflexivity).
  rewrite interp_rr_bind.
  rewrite interp_rr_write_present by discriminate.
  rewrite interp_rr_bind, interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite interp_rr_yield, interp_schedule_rr_select.
  change (interp_schedule_rr sh 2
    ([Ret tt; Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CAlloc 2) (fun base =>
        CBind (CWrite base 2) (fun _ =>
        CBind (CEmit 2 base) (fun _ => CYield)))) >>= fun _ => Ret tt))
    (Some Fin.F1) 1 (alloc_parent_heap,1) ~
    (log (SPop 2 3 1);; Ret (tt,(alloc_both_heap,2)))).
  rewrite interp_rr_bind.
  rewrite interp_rr_alloc_first with (base:=3) by
    (try lia; first [apply block_freeb_spec; reflexivity | exact First]).
  rewrite interp_rr_bind.
  rewrite interp_rr_write_present by discriminate.
  rewrite interp_rr_bind, interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite interp_rr_yield.
  finish_pool.
Qed.

Definition shared_cas_program : CProg unit :=
  CBind (CAlloc 1) (fun cell =>
  CBind (CFork (CBind (CCAS cell 0 20) (fun won =>
    CEmit 20 (if won then 1 else 0))))
    (fun _ => CBind (CCAS cell 0 10) (fun won =>
      CBind (CEmit 10 (if won then 1 else 0)) (fun _ => CYield)))).

Lemma shared_cas_seen :
  run_rr shared_cas_program hemp 0 ~
  (log (SPop 10 1 0);; log (SPop 20 0 1);;
   Ret (tt,(upd (hunion (hblock 1 1) hemp) 1 10,2))).
Proof.
  unfold run_rr, shared_cas_program.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CAlloc 1) (fun cell =>
        CBind (CFork (CBind (CCAS cell 0 20) (fun won =>
          CEmit 20 (if won then 1 else 0))))
          (fun _ => CBind (CCAS cell 0 10) (fun won =>
            CBind (CEmit 10 (if won then 1 else 0)) (fun _ => CYield))))) >>=
        fun _ => Ret tt))
    (Some Fin.F1) 0 (hemp,0) ~
    (log (SPop 10 1 0);; log (SPop 20 0 1);;
     Ret (tt,(upd (hunion (hblock 1 1) hemp) 1 10,2)))).
  rewrite interp_rr_bind.
  rewrite interp_rr_alloc_first with (base:=1) by
    (try lia; apply block_freeb_spec; reflexivity).
  rewrite interp_rr_bind, interp_rr_fork.
  change (interp_schedule_rr sh 2
    ([denote (CBind (CCAS 1 0 20) (fun won =>
        CEmit 20 (if won then 1 else 0))); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CBind (CCAS 1 0 10) (fun won =>
        CBind (CEmit 10 (if won then 1 else 0)) (fun _ => CYield))) >>=
        fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) 0 (hunion (hblock 1 1) hemp,0) ~
    (log (SPop 10 1 0);; log (SPop 20 0 1);;
     Ret (tt,(upd (hunion (hblock 1 1) hemp) 1 10,2)))).
  rewrite interp_rr_bind.
  rewrite interp_rr_cas_value with (current:=0) by reflexivity.
  cbn [Nat.eqb].
  rewrite interp_rr_bind, interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite interp_rr_yield, interp_schedule_rr_select.
  change (interp_schedule_rr sh 2
    ([Ret tt; Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CCAS 1 0 20) (fun won =>
        CEmit 20 (if won then 1 else 0))) >>= fun _ => Ret tt))
    (Some Fin.F1) 1 (upd (hunion (hblock 1 1) hemp) 1 10,1) ~
    (log (SPop 20 0 1);; Ret (tt,(upd (hunion (hblock 1 1) hemp) 1 10,2)))).
  rewrite interp_rr_bind.
  rewrite interp_rr_cas_value with (current:=10) by apply upd_eq.
  cbn [Nat.eqb].
  rewrite interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  finish_pool.
Qed.
