From Stdlib Require Import Arith.PeanoNat Fin Vector Lia.
From ExtLib Require Import Data.Monads.StateMonad.
From TICL Require Import
  Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Interp.State.Mod
  ICTree.Interp.Yield.RoundRobin Utils.Vectors.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

Local Ltac source_observe :=
  lazy [observe _observe Vector.nth Vector.replace Vector.caseS'
    denote denote_flow ICtree.bind ICtree.subst' rr_pick
    Nat.modulo Nat.divmod Fin.of_nat_lt]; reflexivity.

Local Ltac pool_simpl :=
  cbv [Vector.replace Vector.caseS' rr_pick Nat.modulo Nat.divmod Fin.of_nat_lt].

Local Ltac finish_pool :=
  repeat first
    [ progress pool_simpl
    | rewrite vector_remove_head
    | rewrite vector_remove_tail
    | erewrite interp_schedule_rr_ret by source_observe
    | rewrite interp_schedule_rr_select
    | rewrite interp_schedule_rr_empty ];
  reflexivity.

Local Ltac read_result value :=
  lazymatch goal with
  | |- (interp_state sh (srd ?a) (?h,?c) >>= ?K) ~ ?rhs =>
      let Hp := fresh "Hread" in
      assert (Hp : interp_state sh (srd a) (h,c) ≅ Guard (Ret (value,(h,c)))) by
      (etransitivity; [unfold srd; apply interp_state_vis|];
       transitivity (Ret (value,(h,c)) >>= fun result : (nat * SSig)%type =>
         let '(x,σ') := result in Guard (interp_state sh (Ret x) σ'));
       [ apply equ_clo_bind with (S := eq);
         [ apply sh_rd_some; reflexivity | intros r r' <-; reflexivity ]
       | etransitivity; [apply bind_ret_l|];
         step; constructor; apply interp_state_ret ]);
      transitivity (Ret (value,(h,c)) >>= K);
      [ apply sbisim_clo_bind_eq;
        [ eapply equ_clos_sbisim_goal; [exact Hp|reflexivity|apply sb_guard]
        | intro result; reflexivity ]
      | eapply equ_clos_sbisim_goal; [apply bind_ret_l|reflexivity|] ]
  end.

Local Ltac write_result old :=
  lazymatch goal with
  | |- (interp_state sh (swr ?a ?v) (?h,?c) >>= ?K) ~ ?rhs =>
      let Hp := fresh "Hwrite" in
      assert (Hp : interp_state sh (swr a v) (h,c) ≅
        Guard (Ret (tt,(upd h a v,c)))) by
      (etransitivity; [unfold swr; apply interp_state_vis|];
       transitivity (Ret (tt,(upd h a v,c)) >>= fun result : (unit * SSig)%type =>
         let '(_,σ') := result in Guard (interp_state sh (Ret tt) σ'));
       [ apply equ_clo_bind with (S := eq);
         [ apply (sh_wr_some a h c v old); reflexivity
         | intros r r' <-; reflexivity ]
       | etransitivity; [apply bind_ret_l|];
         step; constructor; apply interp_state_ret ]);
      transitivity (Ret (tt,(upd h a v,c)) >>= K);
      [ apply sbisim_clo_bind_eq;
        [ eapply equ_clos_sbisim_goal; [exact Hp|reflexivity|apply sb_guard]
        | intro result; reflexivity ]
      | eapply equ_clos_sbisim_goal; [apply bind_ret_l|reflexivity|] ]
  end.

Local Ltac emit_result :=
  lazymatch goal with
  | |- (interp_state sh (semit ?q ?v) (?h,?c) >>= ?K) ~ ?rhs =>
      let Hp := fresh "Hemit" in
      assert (Hp : interp_state sh (semit q v) (h,c) ≅
        (log (SPop q v c);; Guard (Ret (tt,(h,S c))))) by
      (etransitivity; [unfold semit; apply interp_state_vis|];
       transitivity ((log (SPop q v c);; Ret (tt,(h,S c))) >>=
         fun result : (unit * SSig)%type =>
         let '(_,σ') := result in Guard (interp_state sh (Ret tt) σ'));
       [ apply equ_clo_bind with (S := eq);
         [ apply sh_emit | intros r r' <-; reflexivity ]
       | etransitivity; [apply bind_bind|];
         apply equ_clo_bind_eq; intros [];
         etransitivity; [apply bind_ret_l|];
         step; constructor; apply interp_state_ret ]);
      transitivity ((log (SPop q v c);; Ret (tt,(h,S c))) >>= K);
      [ apply sbisim_clo_bind_eq;
        [ eapply equ_clos_sbisim_goal; [exact Hp|reflexivity|];
          apply sbisim_clo_bind_eq; [reflexivity|intros []; apply sb_guard]
        | intro result; reflexivity ]
      | eapply equ_clos_sbisim_goal; [apply bind_bind|reflexivity|];
        apply sbisim_clo_bind_eq; [reflexivity|intros []];
        eapply equ_clos_sbisim_goal; [apply bind_ret_l|reflexivity|] ]
  end.

Local Ltac alloc_result base Halloc :=
  lazymatch goal with
  | |- (interp_state sh (salloc ?size) (?h,?c) >>= ?K) ~ ?rhs =>
      let Hp := fresh "Halloc_state" in
      assert (Hp : interp_state sh (salloc size) (h,c) ~
        Ret (base,(hunion (hblock base size) h,c))) by
      (eapply equ_clos_sbisim_goal;
       [ unfold salloc; apply interp_state_vis | reflexivity | ];
       transitivity (Ret (base,(hunion (hblock base size) h,c)) >>=
         fun result : (nat * SSig)%type =>
         let '(x,σ') := result in Guard (interp_state sh (Ret x) σ'));
       [ apply sbisim_clo_bind_eq;
         [ exact Halloc | intro result; reflexivity ]
       | eapply equ_clos_sbisim_goal; [apply bind_ret_l|reflexivity|];
         rewrite sb_guard, interp_state_ret; reflexivity ]);
      transitivity (Ret (base,(hunion (hblock base size) h,c)) >>= K);
      [ apply sbisim_clo_bind_eq;
        [ exact Hp | intro result; reflexivity ]
      | eapply equ_clos_sbisim_goal; [apply bind_ret_l|reflexivity|] ]
  end.

Local Ltac cas_result value next_heap Hcas :=
  lazymatch goal with
  | |- (interp_state sh (scas ?a ?expected ?desired) (?h,?c) >>= ?K) ~ ?rhs =>
      let Hp := fresh "Hcas_state" in
      assert (Hp : interp_state sh (scas a expected desired) (h,c) ≅
        Guard (Ret (value,(next_heap,c)))) by
      (etransitivity; [unfold scas; apply interp_state_vis|];
       transitivity (Ret (value,(next_heap,c)) >>= fun result : (bool * SSig)%type =>
         let '(b,σ') := result in Guard (interp_state sh (Ret b) σ'));
       [ apply equ_clo_bind with (S := eq);
         [ exact Hcas | intros r r' <-; reflexivity ]
       | etransitivity; [apply bind_ret_l|];
         step; constructor; apply interp_state_ret ]);
      transitivity (Ret (value,(next_heap,c)) >>= K);
      [ apply sbisim_clo_bind_eq;
        [ eapply equ_clos_sbisim_goal; [exact Hp|reflexivity|apply sb_guard]
        | intro result; reflexivity ]
      | eapply equ_clos_sbisim_goal; [apply bind_ret_l|reflexivity|] ]
  end.

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
  rewrite interp_rr_bind, interp_rr_write.
  write_result 0.
  rewrite interp_rr_yield, interp_schedule_rr_select.
  change (interp_schedule_rr sh 2
    ([Ret tt; Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CRead 4) (fun v => CEmit 2 v)) >>= fun _ => Ret tt))
    (Some Fin.F1) 1 (upd (Pcm.hsingle 4 0) 4 9,0) ~
    (log (SPop 2 9 0);; Ret (tt,(upd (Pcm.hsingle 4 0) 4 9,1)))).
  rewrite interp_rr_bind, interp_rr_read.
  read_result 9.
  rewrite interp_rr_emit; emit_result.
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
  rewrite interp_rr_bind, interp_rr_emit; emit_result.
  rewrite interp_rr_ret.
  change (interp_schedule_rr sh 2
    ([denote (CEmit 2 20); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CEmit 1 11) >>= done))
    (Some (Fin.FS Fin.F1)) 0 (hemp,1) ~
    (log (SPop 1 11 1);; log (SPop 2 20 2);; Ret (tt,(hemp,3)))).
  rewrite interp_rr_emit; emit_result.
  erewrite interp_schedule_rr_ret by source_observe.
  pool_simpl; rewrite vector_remove_tail, vector_remove_head.
  rewrite interp_schedule_rr_select.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 := (denote_flow (CEmit 2 20) >>= done))
    (Some Fin.F1) 1 (hemp,2) ~
    (log (SPop 2 20 2);; Ret (tt,(hemp,3)))).
  rewrite interp_rr_emit; emit_result.
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
  rewrite interp_rr_bind, interp_rr_emit; emit_result.
  rewrite interp_rr_bind, interp_rr_yield, interp_schedule_rr_select.
  change (interp_schedule_rr sh 2
    ([Ret tt; denote (CEmit 1 8)]%vector @ Fin.F1 :=
      (denote_flow (CBind (CEmit 2 9) (fun _ => CBind CYield (fun _ => CEmit 2 10)))
        >>= fun _ => Ret tt))
    (Some Fin.F1) 1 (hemp,1) ~
    (log (SPop 2 9 1);; log (SPop 1 8 2);; log (SPop 2 10 3);; Ret (tt,(hemp,4)))).
  rewrite interp_rr_bind, interp_rr_emit; emit_result.
  rewrite interp_rr_bind, interp_rr_yield, interp_schedule_rr_select.
  change (interp_schedule_rr sh 2
    ([denote (CEmit 2 10); Ret tt]%vector @ Fin.FS Fin.F1 :=
      (denote_flow (CEmit 1 8) >>= fun _ => Ret tt))
    (Some (Fin.FS Fin.F1)) 2 (hemp,2) ~
    (log (SPop 1 8 2);; log (SPop 2 10 3);; Ret (tt,(hemp,4)))).
  rewrite interp_rr_emit; emit_result.
  erewrite interp_schedule_rr_ret by source_observe.
  pool_simpl; rewrite vector_remove_tail, vector_remove_head.
  rewrite interp_schedule_rr_select.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 := (denote_flow (CEmit 2 10) >>= fun _ => Ret tt))
    (Some Fin.F1) 3 (hemp,3) ~
    (log (SPop 2 10 3);; Ret (tt,(hemp,4)))).
  rewrite interp_rr_emit; emit_result.
  finish_pool.
Qed.

Definition allocation_zero_read : CProg unit :=
  CBind (CAlloc 2) (fun base =>
  CBind (CRead (S base)) (fun value => CEmit 9 value)).

Lemma allocation_zero_read_seen :
  run_rr allocation_zero_read hemp 0 ~
  (log (SPop 9 0 0);; Ret (tt,(hunion (hblock 1 2) hemp,1))).
Proof.
  assert (Halloc : runStateT (sh (SAlloc 2)) (hemp,0) ~
    Ret (1,(hunion (hblock 1 2) hemp,0))).
  { apply sh_alloc_first; try lia.
    apply block_freeb_spec; reflexivity. }
  unfold run_rr, allocation_zero_read.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CAlloc 2) (fun base =>
        CBind (CRead (S base)) (fun value => CEmit 9 value))) >>=
        fun _ => Ret tt))
    (Some Fin.F1) 0 (hemp,0) ~
    (log (SPop 9 0 0);; Ret (tt,(hunion (hblock 1 2) hemp,1)))).
  rewrite interp_rr_bind, interp_rr_alloc; alloc_result 1 Halloc.
  rewrite interp_rr_bind, interp_rr_read; read_result 0.
  rewrite interp_rr_emit; emit_result.
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
  assert (Hparent : runStateT (sh (SAlloc 2)) (hemp,0) ~
    Ret (1,(hunion (hblock 1 2) hemp,0))).
  { apply sh_alloc_first; try lia.
    apply block_freeb_spec; reflexivity. }
  assert (Hchild : runStateT (sh (SAlloc 2)) (alloc_parent_heap,1) ~
    Ret (3,(hunion (hblock 3 2) alloc_parent_heap,1))).
  { apply sh_alloc_first; try lia.
    - apply block_freeb_spec; reflexivity.
    - intros j J L F; assert (j = 1 \/ j = 2) as Cases by lia.
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
  rewrite interp_rr_bind, interp_rr_alloc; alloc_result 1 Hparent.
  rewrite interp_rr_bind, interp_rr_write; write_result 0.
  rewrite interp_rr_bind, interp_rr_emit; emit_result.
  rewrite interp_rr_yield, interp_schedule_rr_select.
  change (interp_schedule_rr sh 2
    ([Ret tt; Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CAlloc 2) (fun base =>
        CBind (CWrite base 2) (fun _ =>
        CBind (CEmit 2 base) (fun _ => CYield)))) >>= fun _ => Ret tt))
    (Some Fin.F1) 1 (alloc_parent_heap,1) ~
    (log (SPop 2 3 1);; Ret (tt,(alloc_both_heap,2)))).
  rewrite interp_rr_bind, interp_rr_alloc; alloc_result 3 Hchild.
  rewrite interp_rr_bind, interp_rr_write; write_result 0.
  rewrite interp_rr_bind, interp_rr_emit; emit_result.
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
  assert (Halloc : runStateT (sh (SAlloc 1)) (hemp,0) ~
    Ret (1,(hunion (hblock 1 1) hemp,0))).
  { apply sh_alloc_first; try lia.
    apply block_freeb_spec; reflexivity. }
  assert (Hparent : runStateT (sh (SCAS 1 0 10))
    (hunion (hblock 1 1) hemp,0) ≅
    Ret (true,(upd (hunion (hblock 1 1) hemp) 1 10,0))).
  { apply sh_cas_success; reflexivity. }
  assert (Hchild : runStateT (sh (SCAS 1 0 20))
    (upd (hunion (hblock 1 1) hemp) 1 10,1) ≅
    Ret (false,(upd (hunion (hblock 1 1) hemp) 1 10,1))).
  { eapply sh_cas_failure; [reflexivity|discriminate]. }
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
  rewrite interp_rr_bind, interp_rr_alloc; alloc_result 1 Halloc.
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
  rewrite interp_rr_bind, interp_rr_cas.
  cas_result true (upd (hunion (hblock 1 1) hemp) 1 10) Hparent.
  rewrite interp_rr_bind, interp_rr_emit; emit_result.
  rewrite interp_rr_yield, interp_schedule_rr_select.
  change (interp_schedule_rr sh 2
    ([Ret tt; Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CCAS 1 0 20) (fun won =>
        CEmit 20 (if won then 1 else 0))) >>= fun _ => Ret tt))
    (Some Fin.F1) 1 (upd (hunion (hblock 1 1) hemp) 1 10,1) ~
    (log (SPop 20 0 1);; Ret (tt,(upd (hunion (hblock 1 1) hemp) 1 10,2)))).
  rewrite interp_rr_bind, interp_rr_cas.
  cas_result false (upd (hunion (hblock 1 1) hemp) 1 10) Hchild.
  rewrite interp_rr_emit; emit_result.
  finish_pool.
Qed.
