From TICL Require Import CTree.Interp.Yield.Policy.
(** * Control behavior of the combined Yield+CSL source language.

    Concrete programs run through the real round-robin interpreter.  They pin
    the scoped semantics of [CFork] (a child runs only its body), the single
    yield of a successful variable read together with the late context read of
    an assignment, the separation of context observations from the indexed
    counter, and faults on missing variables or CAS cells.  CAS operands also
    exercise capture-before-yield and late comparison across interleavings.
    Round-robin selections are logged as [inr slot]; context, heap snapshots,
    and indexed program emissions are logged under [inl]. *)

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Strings.String Program.Equality.
From ExtLib Require Import Structures.Maps Data.Map.FMapAList Data.String.
From TICL Require Import
  CTree.Core
  CTree.Logic.CanStep
  Logic.Core
  CTree.Trace
  CTree.Events.Writer
  CTree.Events.Yield
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Refine
  Lang.CoCSL.Mod
  Lang.CoCSL.Frame
  Lang.CoCSL.Sequential
  Utils.Vectors.

Import CTreeNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** ** Driving the round-robin run *)

(** Expose the focused slot as an explicit replacement, so that the source
    execution laws of [Lang.CoCSL.Mod] apply to it. *)
Ltac rr_focus :=
  lazymatch goal with
  | |- interp_schedule_rr ?h ?N ?P (Some ?i) ?m ?s ~ _ =>
      rewrite <- (interp_schedule_rr_equ h N (P @ i := (P $ i)) P (Some i) m s
        (pool_replace_current P i));
      let x := eval cbn [Vector.nth Vector.replace Vector.caseS Vector.caseS'] in (P $ i) in
      change (P $ i) with x; unfold denote
  end.

(** A focused finished slot is removed; the remaining pool is computed
    without unfolding any source denotation. *)
Ltac rr_finish_step :=
  rewrite interp_schedule_rr_ret by reflexivity;
  cbn [Vector.replace Vector.caseS Vector.caseS'];
  rewrite ?vector_remove_tail, ?vector_remove_head.

(** Split a shared leading observation. *)
Ltac rr_log :=
  rewrite !log_vis; apply sb_vis; intros [].

(** Round-robin selection logs the computed slot without advancing the source counter. *)
Ltac rr_select :=
  rewrite interp_schedule_rr_select at 1;
  lazymatch goal with
  | |- context [slot_index (rr_pick ?n ?m)] =>
      let k := eval vm_compute in (slot_index (rr_pick n m)) in
      change (slot_index (rr_pick n m)) with k
  end;
  lazymatch goal with
  | |- context [rr_pick ?n ?m] =>
      let p := eval vm_compute in (rr_pick n m) in change (rr_pick n m) with p
  end;
  rr_log.

Definition ctx0 : Ctx.Ctx := List.nil.
Definition state0 : SSig := (managed_empty, (ctx0, 0)).

(** ** Scoped fork

    The child runs only its own body; it never executes the parent's
    continuation.  Parent first (the focus stays on the parent after a
    fork), then one logged selection, then the child, each emitting exactly
    once. *)
Theorem scoped_fork_no_parent_replay :
  run_rr (CBind (CFork (CEmit 1 7)) (fun _ => CEmit 0 9)) state0 ~
  emit_list [inl (CSLEmit (stamp (0,9) 0)); inr 0;
             inl (CSLEmit (stamp (1,7) 1))]%list
    (Ret ((managed_empty, (ctx0, 2)), tt)
      : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_fork_bind; unfold state0.
  rr_focus.
  rewrite interp_rr_emit_log.
  unfold emit_list; cbn [List.fold_right].
  rr_log.
  rr_finish_step.
  rr_select; rr_focus.
  rewrite interp_rr_emit_log.
  rr_log.
  rr_finish_step.
  apply interp_schedule_rr_empty.
Qed.

(** ** Late context reads

    [x := 1; fork (z := 9); y := x].  The parent's read of [x] yields once,
    so the child updates the shared context first; the parent's assignment
    then reads the context again, so the child's update is preserved.  Only
    context observations are emitted, and the indexed counter stays [0]. *)
Definition context_program : CProg unit :=
  CBind (CAssign "x" (CLit 1)) (fun _ =>
  CBind (CFork (CAssign "z" (CLit 9))) (fun _ =>
    CAssign "y" (CVar "x"))).

Theorem context_resume_preserves_updates :
  let ctx1 := add "x"%string 1 ctx0 in
  let ctx2 := add "z"%string 9 ctx1 in
  let ctx3 := add "y"%string 1 ctx2 in
  run_rr context_program state0 ~
  emit_list [inl (CSLCtx ctx1); inr 0; inl (CSLCtx ctx2); inr 0;
             inl (CSLCtx ctx3)]%list
    (Ret ((managed_empty, (ctx3, 0)), tt)
      : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intros ctx1 ctx2 ctx3.
  rewrite run_rr_unfold; unfold state0, context_program.
  unfold emit_list; cbn [List.fold_right].
  (* parent: x := 1 *)
  rr_focus.
  rewrite interp_rr_bind, interp_rr_assign, interp_rr_lit; cbv beta.
  rewrite interp_rr_get_ctx; cbv beta.
  rewrite interp_rr_put_ctx.
  rr_log.
  (* parent: fork the child, keep the focus *)
  cbv beta iota.
  rewrite interp_rr_bind, interp_rr_fork.
  (* parent: y := x reads x and yields *)
  rr_focus.
  rewrite interp_rr_assign.
  rewrite (interp_rr_var _ _ _ "x"%string 1) by reflexivity.
  (* the child runs next: z := 9, then halts *)
  rr_select; rr_focus.
  rewrite interp_rr_assign, interp_rr_lit; cbv beta.
  rewrite interp_rr_get_ctx; cbv beta.
  rewrite interp_rr_put_ctx.
  rr_log.
  cbv beta iota.
  rr_finish_step.
  (* the parent resumes with the captured value and a fresh context read *)
  rr_select; rr_focus.
  rewrite interp_rr_get_ctx; cbv beta.
  rewrite interp_rr_put_ctx.
  rr_log.
  cbv beta iota.
  rr_finish_step.
  apply interp_schedule_rr_empty.
Qed.

(** A successful variable read captures its value before yielding.  The
    child overwrites the same shared variable, but the parent's resumed
    continuation emits the captured value rather than reading it again. *)
Definition captured_before_yield : CProg unit :=
  CBind (CFork (CAssign "x" (CLit 1))) (fun _ =>
  CBind (CEval (CVar "x")) (fun v => CEmit 9 v)).

Theorem captured_before_yield_rr memory c :
  let ctx0 := add "x"%string 0 List.nil in
  let ctx1 := add "x"%string 1 ctx0 in
  run_rr captured_before_yield (memory,(ctx0,c)) ~
    emit_list [inr 0; inl (CSLCtx ctx1); inr 0;
               inl (CSLEmit (stamp (9,0) c))]%list
      (Ret ((memory,(ctx1,S c)),tt)
        : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intros ctx0 ctx1.
  unfold captured_before_yield; rewrite run_rr_fork_bind.
  unfold emit_list; cbn [List.fold_right].
  (* Parent: capture x = 0, then clear the focus at the read's yield. *)
  rr_focus.
  rewrite interp_rr_bind.
  rewrite (interp_schedule_rr_equ sh 2 _ _ (Some (Fin.FS Fin.F1)) 0 _
    (replace_pool_equ _ _ (Fin.FS Fin.F1) _ _
      (pool_equ_refl _) (source_raw_eval _ _))).
  rewrite (interp_rr_var _ _ _ "x"%string 0) by reflexivity.
  (* Cursor 0 selects the child, which stores x = 1 and terminates. *)
  rr_select; rr_focus.
  rewrite interp_rr_assign, interp_rr_lit; cbv beta.
  rewrite interp_rr_get_ctx; cbv beta.
  rewrite interp_rr_put_ctx.
  rr_log.
  cbv beta iota.
  rr_finish_step.
  (* The remaining parent emits the saved 0 in the updated context. *)
  rr_select; rr_focus.
  unfold csl_set_context, csl_context, csl_memory, csl_counter; cbn [fst snd].
  rewrite interp_rr_emit_log.
  rr_log.
  rr_finish_step.
  apply interp_schedule_rr_empty.
Qed.

(** ** Missing variables fault

    There is no default value: reading an unbound variable is stuck, so the
    whole run is [Stuck] rather than an empty observation sequence. *)
Theorem missing_variable_stuck :
  run_rr (CBind (CEval (CVar "missing")) (fun _ => CRet tt)) state0 ~
    (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_unfold; unfold state0.
  rr_focus.
  rewrite interp_rr_bind.
  rewrite (interp_schedule_rr_equ sh 1 _ _ (Some Fin.F1) 0 _
    (replace_pool_equ _ _ Fin.F1 _ _ (pool_equ_refl _) (source_raw_eval _ _))).
  apply interp_rr_var_missing; reflexivity.
Qed.

(** ** Expression-valued CAS

    Pure arithmetic introduces no scheduling boundary. *)
Definition cas_arithmetic : CProg unit :=
  CBind
    (CCAS (CPlus (CLit 1) (CLit 2))
          (CMinus (CLit 9) (CLit 2))
          (CMult (CLit 2) (CLit 4)))
    (fun ok => CEmit 90 (if ok then 1 else 0)).

Theorem cas_arithmetic_rr :
  run_rr cas_arithmetic ((upd hemp 3 7, hemp), (List.nil, 0)) ~
    emit_list [inl (CSLHeap (upd (upd hemp 3 7) 3 8, hemp));
               inl (CSLEmit (stamp (90,1) 0))]%list
      (Ret (((upd (upd hemp 3 7) 3 8, hemp), (List.nil, 1)), tt)
        : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  assert (Arithmetic : forall K : option bool -> thread sE Bn,
    (denote_flow (CCAS (CPlus (CLit 1) (CLit 2))
      (CMinus (CLit 9) (CLit 2)) (CMult (CLit 2) (CLit 4))) >>= K) ≅
    (denote_flow (CCAS (CLit 3) (CLit 7) (CLit 8)) >>= K)).
  { intro K; cbn [denote_flow denote_exp]; rewrite !bind_ret_l; reflexivity. }
  rewrite run_rr_unfold; unfold cas_arithmetic.
  unfold emit_list; cbn [List.fold_right].
  rr_focus; rewrite interp_rr_bind.
  rewrite (interp_schedule_rr_equ sh 1 _ _ (Some Fin.F1) 0 _
    (replace_pool_equ _ _ Fin.F1 _ _ (pool_equ_refl _) (Arithmetic _))).
  erewrite interp_rr_cas_value by reflexivity; cbn [Nat.eqb].
  rr_log.
  cbv beta iota; rewrite interp_rr_emit_log.
  rr_log; rr_finish_step.
  apply interp_schedule_rr_empty.
Qed.

(** The child changes the context between the parent's four reads, then
    makes the heap comparison succeed only after the desired value is saved. *)
Definition cas_interleaving_child : CProg unit :=
  CBind (CAssign "x" (CLit 1)) (fun _ =>
  CBind CYield (fun _ =>
  CBind (CAssign "x" (CLit 7)) (fun _ =>
  CBind CYield (fun _ =>
  CBind (CAssign "x" (CLit 8)) (fun _ =>
  CBind CYield (fun _ =>
  CBind (CAssign "x" (CLit 9)) (fun _ =>
  CWrite 3 7))))))).

Definition cas_interleaving : CProg unit :=
  CBind (CFork cas_interleaving_child) (fun _ =>
  CBind (CCAS (CMinus (CVar "x") (CVar "x")) (CVar "x") (CVar "x"))
    (fun ok => CEmit 90 (if ok then 1 else 0))).

Theorem cas_interleaving_rr :
  let h0 := upd hemp 3 99 in
  let ctx0 := add "x"%string 4 List.nil in
  let ctx1 := add "x"%string 1 ctx0 in
  let ctx2 := add "x"%string 7 ctx1 in
  let ctx3 := add "x"%string 8 ctx2 in
  let ctx4 := add "x"%string 9 ctx3 in
  run_rr cas_interleaving ((h0, hemp), (ctx0, 0)) ~
    emit_list [inr 0; inl (CSLCtx ctx1); inr 1; inr 0;
               inl (CSLCtx ctx2); inr 1; inr 0;
               inl (CSLCtx ctx3); inr 1; inr 0;
               inl (CSLCtx ctx4); inl (CSLHeap (upd h0 3 7, hemp)); inr 0;
               inl (CSLHeap (upd (upd h0 3 7) 3 8, hemp));
               inl (CSLEmit (stamp (90,1) 0))]%list
      (Ret (((upd (upd h0 3 7) 3 8, hemp), (ctx4, 1)), tt)
        : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intros h0 ctx0 ctx1 ctx2 ctx3 ctx4.
  assert (Sub : forall K : nat -> thread sE Bn,
    (denote_exp (CMinus (CVar "x") (CVar "x")) >>= K) ≅
    (x <- denote_exp (CVar "x");; y <- denote_exp (CVar "x");; K (x - y)%nat)).
  { intro K.
    change (((x <- denote_exp (CVar "x");;
      y <- denote_exp (CVar "x");; Ret (x - y)%nat) >>= K) ≅
      (x <- denote_exp (CVar "x");; y <- denote_exp (CVar "x");; K (x - y)%nat)).
    rewrite bind_bind; apply equ_clo_bind_eq; intro x.
    rewrite bind_bind; apply equ_clo_bind_eq; intro y; apply bind_ret_l. }
  unfold cas_interleaving; rewrite run_rr_fork_bind.
  unfold emit_list; cbn [List.fold_right].
  (* Parent: the first address read captures 4, then yields. *)
  rr_focus; rewrite interp_rr_bind, interp_rr_cas_exp.
  rewrite (interp_schedule_rr_equ sh 2 _ _ (Some (Fin.FS Fin.F1)) 0 _
    (replace_pool_equ _ _ (Fin.FS Fin.F1) _ _ (pool_equ_refl _) (Sub _))).
  rewrite (interp_rr_var _ _ _ "x"%string 4) by reflexivity.
  (* Slot 0: x := 1, then yield. *)
  rr_select; rr_focus; unfold cas_interleaving_child.
  rewrite interp_rr_bind, interp_rr_assign, interp_rr_lit; cbv beta.
  rewrite interp_rr_get_ctx; cbv beta; rewrite interp_rr_put_ctx.
  rr_log; cbv beta iota; rewrite interp_rr_bind, interp_rr_yield.
  (* Slot 1: the second address read captures 1, giving address 3. *)
  rr_select; rr_focus.
  rewrite (interp_rr_var _ _ _ "x"%string 1) by reflexivity.
  (* Slot 0: x := 7, then yield. *)
  rr_select; rr_focus.
  rewrite interp_rr_bind, interp_rr_assign, interp_rr_lit; cbv beta.
  rewrite interp_rr_get_ctx; cbv beta; rewrite interp_rr_put_ctx.
  rr_log; cbv beta iota; rewrite interp_rr_bind, interp_rr_yield.
  (* Slot 1: the expected operand captures 7. *)
  rr_select; rr_focus.
  rewrite (interp_rr_var _ _ _ "x"%string 7) by reflexivity.
  (* Slot 0: x := 8, then yield. *)
  rr_select; rr_focus.
  rewrite interp_rr_bind, interp_rr_assign, interp_rr_lit; cbv beta.
  rewrite interp_rr_get_ctx; cbv beta; rewrite interp_rr_put_ctx.
  rr_log; cbv beta iota; rewrite interp_rr_bind, interp_rr_yield.
  (* Slot 1: the desired operand captures 8 while the heap still holds 99. *)
  rr_select; rr_focus.
  rewrite (interp_rr_var _ _ _ "x"%string 8) by reflexivity.
  (* Slot 0: x := 9, write 7 to the heap, then terminate. *)
  rr_select; rr_focus.
  rewrite interp_rr_bind, interp_rr_assign, interp_rr_lit; cbv beta.
  rewrite interp_rr_get_ctx; cbv beta; rewrite interp_rr_put_ctx.
  rr_log; cbv beta iota.
  unfold csl_set_context, csl_context, csl_memory, csl_counter; cbn [fst snd].
  rewrite interp_rr_write_present by (vm_compute; congruence).
  rr_log.
  rr_finish_step.
  (* The singleton parent's saved operands perform CAS 3 7 8 and report true. *)
  rr_select; rr_focus.
  erewrite interp_rr_cas_value by reflexivity; cbn [Nat.eqb].
  rr_log.
  cbv beta iota; rewrite interp_rr_emit_log.
  rr_log; rr_finish_step.
  apply interp_schedule_rr_empty.
Qed.

(** ** Operand faults precede the heap event

    No failed operand reaches the report.  In particular, the desired
    operand is evaluated even when the current heap value does not match. *)
Theorem cas_missing_address_rr :
  run_rr
    (CBind (CCAS (CVar "missing") (CVar "e") (CVar "d"))
      (fun ok => CEmit 90 (if ok then 1 else 0)))
    ((upd hemp 3 99, hemp),
      (add "d"%string 8 (add "e"%string 7 (add "a"%string 3 List.nil)), 0)) ~
    (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_unfold; rr_focus.
  rewrite interp_rr_bind, interp_rr_cas_exp.
  apply interp_rr_var_missing; reflexivity.
Qed.

Theorem cas_missing_expected_rr :
  run_rr
    (CBind (CCAS (CVar "a") (CVar "missing") (CVar "d"))
      (fun ok => CEmit 90 (if ok then 1 else 0)))
    ((upd hemp 3 99, hemp),
      (add "d"%string 8 (add "e"%string 7 (add "a"%string 3 List.nil)), 0)) ~
    (log (inr 0 : CSLObs (nat * nat) + nat);; Stuck
      : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_unfold; rr_focus.
  rewrite interp_rr_bind, interp_rr_cas_exp.
  rewrite (interp_rr_var _ _ _ "a"%string 3) by reflexivity.
  rr_select; rr_focus.
  apply interp_rr_var_missing; reflexivity.
Qed.

Theorem cas_missing_desired_rr :
  run_rr
    (CBind (CCAS (CVar "a") (CVar "e") (CVar "missing"))
      (fun ok => CEmit 90 (if ok then 1 else 0)))
    ((upd hemp 3 99, hemp),
      (add "d"%string 8 (add "e"%string 7 (add "a"%string 3 List.nil)), 0)) ~
    (log (inr 0 : CSLObs (nat * nat) + nat);; log (inr 0);; Stuck
      : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_unfold; rr_focus.
  rewrite interp_rr_bind, interp_rr_cas_exp.
  rewrite (interp_rr_var _ _ _ "a"%string 3) by reflexivity.
  rr_select; rr_focus.
  rewrite (interp_rr_var _ _ _ "e"%string 7) by reflexivity.
  rr_select; rr_focus.
  apply interp_rr_var_missing; reflexivity.
Qed.

Theorem cas_missing_cell_rr :
  run_rr
    (CBind (CCAS (CVar "a") (CVar "e") (CVar "d"))
      (fun ok => CEmit 90 (if ok then 1 else 0)))
    (managed_empty,
      (add "d"%string 8 (add "e"%string 7 (add "a"%string 3 List.nil)), 0)) ~
    (log (inr 0 : CSLObs (nat * nat) + nat);; log (inr 0);; log (inr 0);; Stuck
      : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_unfold; rr_focus.
  rewrite interp_rr_bind, interp_rr_cas_exp.
  rewrite (interp_rr_var _ _ _ "a"%string 3) by reflexivity.
  rr_select; rr_focus.
  rewrite (interp_rr_var _ _ _ "e"%string 7) by reflexivity.
  rr_select; rr_focus.
  rewrite (interp_rr_var _ _ _ "d"%string 8) by reflexivity.
  rr_select; rr_focus.
  apply interp_rr_cas_missing; reflexivity.
Qed.

(** ** The sequential-fragment boundary includes every operand *)
Theorem cas_yield_fork_free_literals :
  yield_fork_free (CCAS (CLit 3) (CLit 7) (CLit 8)).
Proof.
  cbn [yield_fork_free prog_ok exp_ok user_only]; repeat split; intros; exact I.
Qed.

Theorem cas_var_operands_not_yield_fork_free :
  ~ yield_fork_free (CCAS (CVar "x") (CLit 7) (CLit 8)) /\
  ~ yield_fork_free (CCAS (CLit 3) (CVar "x") (CLit 8)) /\
  ~ yield_fork_free (CCAS (CLit 3) (CLit 7) (CVar "x")).
Proof.
  cbn [yield_fork_free prog_ok exp_ok user_only]; tauto.
Qed.

(** A source loop may yield and grow its pool before exiting; native return
    is established only after both the parent and the spawned child finish. *)
Import TiclNotations.
Local Open Scope ticl_scope.

Definition yield_fork_body : CProg (option unit) :=
  CBind CYield (fun _ => CBind (CFork (CEmit 8 1)) (fun _ => CoCSLSyntax.CRet (None : option unit))).
Definition yield_fork_loop : CProg unit := CUntilNone yield_fork_body.

Theorem yield_fork_loop_af_return_nd : entails (SSig * unit) true
  (Cu Q_A (CNow (fun _ => True)) (Logic.Syntax.CRet (fun '(s,x) _ => s=(managed_empty,(List.nil,1)) /\ x=tt)))
  (run_nd yield_fork_loop state0) Pure.
Proof.
  unfold state0, ctx0; rewrite run_nd_unfold.
  change (entails (SSig * unit) true
    (Cu Q_A (CNow (fun _ => True)) (Logic.Syntax.CRet (fun '(s,x) _ => s=(managed_empty,(List.nil,1)) /\ x=tt)))
    (interp_schedule_nd sh 1 ([Ret tt]%vector @ Fin.F1 := (denote_flow yield_fork_loop >>= fun _ => Ret tt))
      (Some Fin.F1) (managed_empty,(List.nil,0))) Pure).
  unfold yield_fork_loop.
  eapply (af_csl_nd_until_none_wf (b:=true) yield_fork_body (fun _ => Ret tt)
    (fun (_ : unit) n (_ : pool sE Bn (S n)) (_ : Fin.t (S n)) sigma w =>
      n=0 /\ sigma=(managed_empty,(List.nil,0)) /\ w=Pure)
    (fun (_ _ : unit) => False)) with (g:=tt) (n:=0) (ts:=[Ret tt]%vector) (i:=Fin.F1).
  - intros []; constructor; intros [] H; contradiction.
  - intros [] n ts i sigma w (Hn & Hsigma & Hw); subst n sigma w.
    dependent destruction i; [|inversion i].
    dependent destruction ts.
    match goal with v : Vector.t _ 0 |- _ => dependent destruction v end.
    eapply auc_mono_r.
    + intros t z Hret; left; exact Hret.
    + apply ticl_au.
      unfold yield_fork_body; rewrite au_csl_nd_bind.
      rewrite au_csl_nd_yield; right; split; [apply ticl_now; split; [exact I|constructor]|].
      intro j; dependent destruction j; [|inversion j].
      cbn beta iota; rewrite au_csl_nd_bind.
      rewrite au_csl_nd_fork.
      cbn beta iota; unfold until_tail; cbn beta iota.
      change (entails (SSig * unit) true
        (Cu Q_A (CNow (fun _ => True)) (Logic.Syntax.CRet (fun '(s,x) _ => s=(managed_empty,(List.nil,1)) /\ x=tt)))
        (interp_schedule_nd sh 2
          ([denote_flow (CEmit 8 1) >>= fun _ => Ret tt; Ret tt]%vector @ Fin.FS Fin.F1 :=
            (denote_flow (CoCSLSyntax.CRet (None : option unit)) >>= until_tail yield_fork_body (fun _ => Ret tt)))
          (Some (Fin.FS Fin.F1)) (managed_empty,(List.nil,0))) Pure).
      rewrite au_csl_nd_ret; cbn beta iota; unfold until_tail; cbn beta iota.
      rewrite (interp_schedule_nd_ret sh) by (rewrite Vector.nth_replace_eq; reflexivity).
      cbn [Vector.replace Vector.caseS Vector.caseS']; rewrite vector_remove_tail, vector_remove_head.
      rewrite au_csl_nd_select; right; split; [apply ticl_now; split; [exact I|constructor]|].
      intro j; dependent destruction j; [|inversion j].
      change (entails (SSig * unit) true
        (Cu Q_A (CNow (fun _ => True)) (Logic.Syntax.CRet (fun '(s,x) _ => s=(managed_empty,(List.nil,1)) /\ x=tt)))
        (interp_schedule_nd sh 1 ([Ret tt]%vector @ Fin.F1 := (denote_flow (CEmit 8 1) >>= fun _ => Ret tt))
          (Some Fin.F1) (managed_empty,(List.nil,0))) Pure).
      rewrite au_csl_nd_emit; right; split; [apply ticl_now; split; [exact I|constructor]|].
      rewrite (interp_schedule_nd_ret sh) by (rewrite Vector.nth_replace_eq; reflexivity).
      rewrite (interp_schedule_nd_empty sh).
      apply ticl_au, MatchA, ret_ret; [constructor|split; reflexivity].
  - repeat split; reflexivity.
Qed.

Theorem yield_fork_loop_af_return_rr : entails (SSig * unit) true
  (Cu Q_A (CNow (fun _ => True)) (Logic.Syntax.CRet (fun '(s,x) _ => s=(managed_empty,(List.nil,1)) /\ x=tt)))
  (run_rr yield_fork_loop state0) Pure.
Proof.
  unfold state0, ctx0; rewrite run_rr_unfold.
  change (entails (SSig * unit) true
    (Cu Q_A (CNow (fun _ => True)) (Logic.Syntax.CRet (fun '(s,x) _ => s=(managed_empty,(List.nil,1)) /\ x=tt)))
    (interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 := (denote_flow yield_fork_loop >>= fun _ => Ret tt))
      (Some Fin.F1) 0 (managed_empty,(List.nil,0))) Pure).
  unfold yield_fork_loop.
  eapply (af_csl_rr_until_none_wf (b:=true) yield_fork_body (fun _ => Ret tt)
    (fun (_ : unit) n (_ : pool sE Bn (S n)) (_ : Fin.t (S n)) cursor sigma w =>
      n=0 /\ cursor=0 /\ sigma=(managed_empty,(List.nil,0)) /\ w=Pure)
    (fun (_ _ : unit) => False)) with (g:=tt) (n:=0) (ts:=[Ret tt]%vector) (i:=Fin.F1).
  - intros []; constructor; intros [] H; contradiction.
  - intros [] n ts i cursor sigma w (Hn & Hcursor & Hsigma & Hw); subst n cursor sigma w.
    dependent destruction i; [|inversion i].
    dependent destruction ts.
    match goal with v : Vector.t _ 0 |- _ => dependent destruction v end.
    eapply auc_mono_r.
    + intros t z Hret; left; exact Hret.
    + apply ticl_au.
      unfold yield_fork_body; rewrite au_csl_rr_bind.
      rewrite au_csl_rr_yield; right; split; [apply ticl_now; split; [exact I|constructor]|].
      rewrite rr_pick_0; cbn beta iota; rewrite au_csl_rr_bind.
      rewrite au_csl_rr_fork.
      cbn beta iota; unfold until_tail; cbn beta iota.
      change (entails (SSig * unit) true
        (Cu Q_A (CNow (fun _ => True)) (Logic.Syntax.CRet (fun '(s,x) _ => s=(managed_empty,(List.nil,1)) /\ x=tt)))
        (interp_schedule_rr sh 2
          ([denote_flow (CEmit 8 1) >>= fun _ => Ret tt; Ret tt]%vector @ Fin.FS Fin.F1 :=
            (denote_flow (CoCSLSyntax.CRet (None : option unit)) >>= until_tail yield_fork_body (fun _ => Ret tt)))
          (Some (Fin.FS Fin.F1)) 1 (managed_empty,(List.nil,0)))
        (Obs (Log (inr 0 : CSLObs (nat * nat) + nat)) tt)).
      rewrite au_csl_rr_ret; cbn beta iota; unfold until_tail; cbn beta iota.
      rewrite (interp_schedule_rr_ret sh) by (rewrite Vector.nth_replace_eq; reflexivity).
      cbn [Vector.replace Vector.caseS Vector.caseS']; rewrite vector_remove_tail, vector_remove_head.
      rewrite au_csl_rr_select; right; split; [apply ticl_now; split; [exact I|constructor]|].
      rewrite rr_pick_0.
      change (entails (SSig * unit) true
        (Cu Q_A (CNow (fun _ => True)) (Logic.Syntax.CRet (fun '(s,x) _ => s=(managed_empty,(List.nil,1)) /\ x=tt)))
        (interp_schedule_rr sh 1 ([Ret tt]%vector @ Fin.F1 := (denote_flow (CEmit 8 1) >>= fun _ => Ret tt))
          (Some Fin.F1) 2 (managed_empty,(List.nil,0)))
        (Obs (Log (inr 0 : CSLObs (nat * nat) + nat)) tt)).
      rewrite au_csl_rr_emit; right; split; [apply ticl_now; split; [exact I|constructor]|].
      rewrite (interp_schedule_rr_ret sh) by (rewrite Vector.nth_replace_eq; reflexivity).
      cbn [Vector.replace Vector.caseS Vector.caseS']; rewrite vector_remove_head, (interp_schedule_rr_empty sh).
      apply ticl_au, MatchA, ret_ret; [constructor|split; reflexivity].
  - repeat split; reflexivity.
Qed.

(** Nondeterminism may choose a visible successful branch or a fault.
    Round robin instead logs its cursor-dependent selection, without changing
    which branch succeeds or faults. *)
Definition fault_choice_pool : Vector.t (CProg unit) 2 :=
  [CEmit 7 9; CBind (CRead 1) (fun _ => CoCSLSyntax.CRet tt)]%vector.

Theorem fault_choice_ef_nd : entails (SSig * unit) false
  (Cu Q_E (CNow (fun _ => True)) <( visW {fun o => o = CSLEmit (stamp (7,9) 0)} )>)
  (run_nd_pool fault_choice_pool None state0) Pure.
Proof.
  unfold run_nd_pool, csl_pool, fault_choice_pool, state0, ctx0; cbn [Vector.map]; unfold denote.
  rewrite eu_csl_nd_select; right; split; [apply ticl_now; split; [exact I|constructor]|].
  exists Fin.F1.
  change (entails (SSig * unit) false
    (Cu Q_E (CNow (fun _ => True)) <( visW {fun o => o = CSLEmit (stamp (7,9) 0)} )>)
    (interp_schedule_nd sh 2
      ([Ret tt; denote_flow (CBind (CRead 1) (fun _ => CoCSLSyntax.CRet tt)) >>= fun _ => Ret tt]%vector
        @ Fin.F1 := (denote_flow (CEmit 7 9) >>= fun _ => Ret tt))
      (Some Fin.F1) (managed_empty,(List.nil,0))) Pure).
  rewrite eu_csl_nd_emit; right; split; [apply ticl_now; split; [exact I|constructor]|].
  apply ticl_eu, MatchE, ticl_vis; constructor; reflexivity.
Qed.

Theorem fault_choice_not_af_nd : ~ entails (SSig * unit) false
  (Cu Q_A (CNow (fun _ => True)) <( visW {fun o => o = CSLEmit (stamp (7,9) 0)} )>)
  (run_nd_pool fault_choice_pool None state0) Pure.
Proof.
  unfold run_nd_pool, csl_pool, fault_choice_pool, state0, ctx0; cbn [Vector.map]; unfold denote.
  rewrite au_csl_nd_select; intros [Hnow|[_ Hnext]].
  - apply ticl_vis in Hnow; inversion Hnow.
  - specialize (Hnext (Fin.FS Fin.F1)).
    change (entails (SSig * unit) false
      (Cu Q_A (CNow (fun _ => True)) <( visW {fun o => o = CSLEmit (stamp (7,9) 0)} )>)
      (interp_schedule_nd sh 2
        ([denote_flow (CEmit 7 9) >>= fun _ => Ret tt; Ret tt]%vector
          @ Fin.FS Fin.F1 := (denote_flow (CBind (CRead 1) (fun _ => CoCSLSyntax.CRet tt)) >>= fun _ => Ret tt))
        (Some (Fin.FS Fin.F1)) (managed_empty,(List.nil,0))) Pure) in Hnext.
    rewrite au_csl_nd_bind in Hnext.
    unfold managed_empty in Hnext; cbn beta iota in Hnext.
    rewrite au_csl_nd_read_missing in Hnext by reflexivity.
    apply ticl_vis in Hnext; inversion Hnext.
Qed.

Theorem fault_choice_af_rr_zero : entails (SSig * unit) false
  (Cu Q_A (CNow (fun _ => True)) <( visW {fun o => o = inl (CSLEmit (stamp (7,9) 0))} )>)
  (run_rr_pool fault_choice_pool None 0 state0) Pure.
Proof.
  unfold run_rr_pool, csl_pool, fault_choice_pool, state0, ctx0; cbn [Vector.map]; unfold denote.
  rewrite au_csl_rr_select; right; split; [apply ticl_now; split; [exact I|constructor]|].
  change (entails (SSig * unit) false
    (Cu Q_A (CNow (fun _ => True)) <( visW {fun o => o = inl (CSLEmit (stamp (7,9) 0))} )>)
    (interp_schedule_rr sh 2
      ([Ret tt; denote_flow (CBind (CRead 1) (fun _ => CoCSLSyntax.CRet tt)) >>= fun _ => Ret tt]%vector
        @ Fin.F1 := (denote_flow (CEmit 7 9) >>= fun _ => Ret tt))
      (Some Fin.F1) 1 (managed_empty,(List.nil,0)))
    (Obs (Log (inr 0 : CSLObs (nat * nat) + nat)) tt)).
  rewrite au_csl_rr_emit; right; split; [apply ticl_now; split; [exact I|constructor]|].
  apply ticl_au, MatchA, ticl_vis; constructor; reflexivity.
Qed.

Theorem fault_choice_not_ef_rr_one : ~ entails (SSig * unit) false
  (Cu Q_E (CNow (fun _ => True)) <( visW {fun o => o = inl (CSLEmit (stamp (7,9) 0))} )>)
  (run_rr_pool fault_choice_pool None 1 state0) Pure.
Proof.
  unfold run_rr_pool, csl_pool, fault_choice_pool, state0, ctx0; cbn [Vector.map]; unfold denote.
  rewrite eu_csl_rr_select; intros [Hnow|[_ Hnext]].
  - apply ticl_vis in Hnow; inversion Hnow.
  - change (entails (SSig * unit) false
      (Cu Q_E (CNow (fun _ => True)) <( visW {fun o => o = inl (CSLEmit (stamp (7,9) 0))} )>)
      (interp_schedule_rr sh 2
        ([denote_flow (CEmit 7 9) >>= fun _ => Ret tt; Ret tt]%vector
          @ Fin.FS Fin.F1 := (denote_flow (CBind (CRead 1) (fun _ => CoCSLSyntax.CRet tt)) >>= fun _ => Ret tt))
        (Some (Fin.FS Fin.F1)) 2 (managed_empty,(List.nil,0)))
      (Obs (Log (inr 1 : CSLObs (nat * nat) + nat)) tt)) in Hnext.
    rewrite eu_csl_rr_bind in Hnext.
    unfold managed_empty in Hnext; cbn beta iota in Hnext.
    rewrite eu_csl_rr_read_missing in Hnext by reflexivity.
    apply ticl_vis in Hnext; dependent destruction Hnext; discriminate.
Qed.

