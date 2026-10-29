(** * Control behavior of the combined Yield+CSL source language.

    Concrete programs run through the real round-robin interpreter.  They pin
    the scoped semantics of [CFork] (a child runs only its body), the single
    yield of a successful variable read together with the late context read of
    an assignment, the separation of context observations from the indexed
    counter, and faults on missing variables or CAS cells.  CAS operands also
    exercise capture-before-yield and late comparison across interleavings.
    Every round-robin scheduling decision is one visible [Step]. *)

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Strings.String.
From ExtLib Require Import Structures.Maps Data.Map.FMapAList Data.String.
From TICL Require Import
  CTree.Core
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

(** Round-robin selection: one visible [Step], with the picked slot computed. *)
Ltac rr_select :=
  rewrite interp_schedule_rr_select;
  lazymatch goal with
  | |- context [rr_pick ?n ?m] =>
      let p := eval vm_compute in (rr_pick n m) in change (rr_pick n m) with p
  end;
  apply sb_step.

(** Split a shared leading observation. *)
Ltac rr_log :=
  unfold log; rewrite !bind_trigger; apply sb_vis; intros [].

Definition ctx0 : Ctx.Ctx := List.nil.
Definition state0 : SSig := (managed_empty, (ctx0, 0)).

(** ** Scoped fork

    The child runs only its own body; it never executes the parent's
    continuation.  Parent first (the focus stays on the parent after a
    fork), then one scheduling step, then the child, each emitting exactly
    once. *)
Theorem scoped_fork_no_parent_replay :
  run_rr (CBind (CFork (CEmit 1 7)) (fun _ => CEmit 0 9)) state0 ~
  emit_list [inr (stamp (0,9) 0)]%list
    (Step (emit_list [inr (stamp (1,7) 1)]%list
      (Ret ((managed_empty, (ctx0, 2)), tt)
        : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)))).
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
  emit_list [inl ctx1]%list
    (Step (emit_list [inl ctx2]%list
      (Step (emit_list [inl ctx3]%list
        (Ret ((managed_empty, (ctx3, 0)), tt)
          : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)))))).
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
    Step (emit_list [inl ctx1]%list
      (Step (emit_list [inr (stamp (9,0) c)]%list
        (Ret ((memory,(ctx1,S c)),tt)
          : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))))).
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
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
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
    emit_list [inr (stamp (90,1) 0)]%list
      (Ret (((upd (upd hemp 3 7) 3 8, hemp), (List.nil, 1)), tt)
        : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
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
    Step (emit_list [inl ctx1]%list
      (Step (Step (emit_list [inl ctx2]%list
        (Step (Step (emit_list [inl ctx3]%list
          (Step (Step (emit_list [inl ctx4]%list
            (Step (emit_list [inr (stamp (90,1) 0)]%list
              (Ret (((upd (upd h0 3 7) 3 8, hemp), (ctx4, 1)), tt)
                : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)))))))))))))).
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
  rr_finish_step.
  (* The singleton parent's saved operands perform CAS 3 7 8 and report true. *)
  rr_select; rr_focus.
  erewrite interp_rr_cas_value by reflexivity; cbn [Nat.eqb].
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
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
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
    Step (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
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
    Step (Step (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))).
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
    Step (Step (Step (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)))).
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
