(** * Control behavior of the combined Yield+CSL source language.

    Concrete programs run through the real round-robin interpreter.  They pin
    the scoped semantics of [CFork] (a child runs only its body), the single
    yield of a successful variable read together with the late context read of
    an assignment, the separation of context observations from the indexed
    counter, and the fault on a missing variable. *)

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Strings.String.
From ExtLib Require Import Structures.Maps Data.Map.FMapAList Data.String.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Events.Writer ICTree.Events.Yield
  ICTree.Interp.Yield.Mod ICTree.Interp.Yield.RoundRobin ICTree.Interp.Refine
  Lang.CSL.Mod Utils.Vectors.

Import ICtree ICTreeNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

(** ** Driving the round-robin run *)

(** Expose the focused slot as an explicit replacement, so that the source
    execution laws of [Lang.CSL.Mod] apply to it. *)
Ltac rr_focus :=
  lazymatch goal with
  | |- interp_schedule_rr ?h ?N ?P (Some ?i) ?m ?s ~ _ =>
      rewrite <- (interp_schedule_rr_equ h N (P @ i := (P $ i)) P (Some i) m s
        (pool_replace_current P i));
      let x := eval cbn [Vector.nth Vector.replace Vector.caseS Vector.caseS'] in (P $ i) in
      change (P $ i) with x; unfold denote
  end.

Ltac rr_finish :=
  cbn beta iota zeta;
  rewrite interp_schedule_rr_ret by reflexivity;
  lazymatch goal with
  | |- interp_schedule_rr _ _ (?v -- _) _ _ _ ~ _ =>
      let v' := eval cbn in v in change v with v'
  end;
  rewrite vector_remove_head;
  apply interp_schedule_rr_empty.

(** A focused finished slot is removed; the remaining pool is computed
    without unfolding any source denotation. *)
Ltac rr_finish_step :=
  rewrite interp_schedule_rr_ret by reflexivity;
  cbn [Vector.replace Vector.caseS Vector.caseS'];
  rewrite ?vector_remove_tail, ?vector_remove_head.

(** Round-robin selection, with the picked slot computed. *)
Ltac rr_select :=
  rewrite interp_schedule_rr_select;
  lazymatch goal with
  | |- context [rr_pick ?n ?m] =>
      let p := eval vm_compute in (rr_pick n m) in change (rr_pick n m) with p
  end.

Definition ctx0 : Ctx.Ctx := List.nil.
Definition state0 : SSig := (managed_empty, (ctx0, 0)).

(** ** Scoped fork

    The child runs only its own body; it never executes the parent's
    continuation.  Parent first (the focus stays on the parent after a
    fork), then the child, each emitting exactly once. *)
Theorem scoped_fork_no_parent_replay :
  run_rr (CBind (CFork (CEmit 1 7)) (fun _ => CEmit 0 9)) state0 ~
  emit_list [inr (stamp (0,9) 0); inr (stamp (1,7) 1)]%list
    (Ret (tt, (managed_empty, (ctx0, 2)))).
Proof.
  rewrite run_rr_fork_bind; unfold state0.
  rr_focus.
  rewrite interp_rr_emit_log.
  unfold emit_list; cbn [List.fold_right].
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rr_finish_step.
  rr_select; rr_focus.
  rewrite interp_rr_emit_log.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
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
  emit_list [inl ctx1; inl ctx2; inl ctx3]%list
    (Ret (tt, (managed_empty, (ctx3, 0)))).
Proof.
  intros ctx1 ctx2 ctx3.
  rewrite run_rr_unfold; unfold state0, context_program.
  unfold emit_list; cbn [List.fold_right].
  (* parent: x := 1 *)
  rr_focus.
  rewrite interp_rr_bind, interp_rr_assign, interp_rr_lit; cbv beta.
  rewrite interp_rr_get_ctx; cbv beta.
  rewrite interp_rr_put_ctx.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
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
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  cbv beta iota.
  rr_finish_step.
  (* the parent resumes with the captured value and a fresh context read *)
  rr_select; rr_focus.
  rewrite interp_rr_get_ctx; cbv beta.
  rewrite interp_rr_put_ctx.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  cbv beta iota.
  rr_finish_step.
  apply interp_schedule_rr_empty.
Qed.

(** ** Missing variables fault

    There is no default value: reading an unbound variable is stuck, so the
    whole run is [stuck] rather than an empty observation sequence. *)
Theorem missing_variable_stuck :
  run_rr (CBind (CEval (CVar "missing")) (fun _ => CRet tt)) state0 ~
    (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  rewrite run_rr_unfold; unfold state0.
  rr_focus.
  rewrite interp_rr_bind.
  rewrite (interp_schedule_rr_equ sh 1 _ _ (Some Fin.F1) 0 _
    (replace_pool_equ _ _ Fin.F1 _ _ (pool_equ_refl _) (source_raw_eval _ _))).
  apply interp_rr_var_missing; reflexivity.
Qed.
