(** * Malloc/free lifecycle of the canonical CSL language.

    Concrete single-thread programs run through the real round-robin
    interpreter.  They pin the observable allocation discipline: first-fit
    zero-initialized malloc with recorded extents, whole-block free, reuse of a
    released block, the null-free no-op, and faults on interior-pointer,
    double, and use-after-free accesses. *)

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Events.Writer ICTree.Events.Yield
  ICTree.Interp.Yield.Mod ICTree.Interp.Yield.RoundRobin Lang.CSL.Mod Utils.Vectors.

Import ICtree ICTreeNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

(** ** Fixtures *)

Definition lifecycle : CProg unit :=
  CBind (CAlloc 3) (fun first =>
  CBind (CAlloc 2) (fun second =>
  CBind (CWrite first 7) (fun _ =>
  CBind (CWrite (first + 2) 9) (fun _ =>
  CBind (CWrite second 11) (fun _ =>
  CBind (CCAS first 7 8) (fun succeeded =>
  CBind (CCAS first 7 99) (fun failed =>
  CBind (CEmit 80 (if succeeded then 1 else 0)) (fun _ =>
  CBind (CEmit 81 (if failed then 1 else 0)) (fun _ =>
  CBind (CFree first) (fun _ =>
  CBind (CRead second) (fun value =>
  CBind (CEmit 82 value) (fun _ => CRet tt)))))))))))).

Definition reallocate : CProg unit :=
  CBind (CAlloc 3) (fun first =>
  CBind (CFree first) (fun _ =>
  CBind (CAlloc 3) (fun next =>
  CBind (CEmit 83 next) (fun _ => CRet tt)))).

Definition invalid_interior : CProg unit :=
  CBind (CAlloc 3) (fun base => CFree (S base)).

Definition invalid_double : CProg unit :=
  CBind (CAlloc 3) (fun base =>
  CBind (CFree base) (fun _ => CFree base)).

Definition use_after_free_read : CProg unit :=
  CBind (CAlloc 3) (fun base =>
  CBind (CFree base) (fun _ =>
  CBind (CRead (base + 2)) (fun _ => CRet tt))).

Definition use_after_free_write : CProg unit :=
  CBind (CAlloc 3) (fun base =>
  CBind (CFree base) (fun _ => CWrite (base + 2) 17)).

Definition use_after_free_cas : CProg unit :=
  CBind (CAlloc 3) (fun base =>
  CBind (CFree base) (fun _ =>
  CBind (CCAS (base + 2) 0 17) (fun _ => CRet tt))).

(** ** Driving the single-thread round-robin run

    Each step applies one source execution rule of [Lang.CSL.Mod] at the
    focused thread; concrete heap facts are discharged by computation. *)

Lemma run_rr_focus p memory c :
  run_rr p memory c ≅
  interp_schedule_rr sh 1
    (([Ret tt] : pool sE 1) @ Fin.F1 := (denote_flow p >>= fun _ => Ret tt))
    (Some Fin.F1) 0 (memory,c).
Proof. reflexivity. Qed.

Ltac first_fit :=
  let j := fresh "j" in
  let Pos := fresh "Pos" in
  let Lt := fresh "Lt" in
  let Free := fresh "Free" in
  intros j Pos Lt Free; apply block_freeb_spec in Free;
  repeat (lia || (destruct j as [|j];
    [solve [lia | vm_compute in Free; discriminate] |])).

Ltac block_is_free := apply block_freeb_spec; vm_compute; reflexivity.

Ltac rr_step :=
  cbn beta iota zeta;
  lazymatch goal with
  | |- interp_schedule_rr _ _ (_ @ _ := (denote_flow (CBind _ _) >>= _)) _ _ _ ~ _ =>
      rewrite interp_rr_bind
  | |- interp_schedule_rr _ _ (_ @ _ := (denote_flow (CRet _) >>= _)) _ _ _ ~ _ =>
      rewrite interp_rr_ret
  | |- interp_schedule_rr _ _ (_ @ _ := (denote_flow (CWrite _ _) >>= _)) _ _ _ ~ _ =>
      rewrite interp_rr_write_present by (vm_compute; congruence)
  | |- interp_schedule_rr _ _ (_ @ _ := (denote_flow (CRead _) >>= _)) _ _ _ ~ _ =>
      erewrite interp_rr_read_value by reflexivity
  | |- interp_schedule_rr _ _ (_ @ _ := (denote_flow (CCAS _ _ _) >>= _)) _ _ _ ~ _ =>
      erewrite interp_rr_cas_value by reflexivity; cbn [Nat.eqb]
  | |- interp_schedule_rr _ _ (_ @ _ := (denote_flow (CFree _) >>= _)) _ _ _ ~ _ =>
      erewrite interp_rr_free by reflexivity
  | |- interp_schedule_rr _ _ (_ @ _ := (denote_flow (CEmit _ _) >>= _)) _ _ _ ~ _ =>
      rewrite interp_rr_emit_log
  end.

(** Allocation chooses its first-fit base explicitly. *)
Ltac rr_alloc base :=
  cbn beta iota zeta; try unfold managed_empty;
  rewrite (interp_rr_alloc_first _ _ _ _ base) by
    (first [lia | block_is_free | first_fit]);
  unfold managed_alloc, managed_empty; cbn [fst snd].

Ltac rr_finish :=
  cbn beta iota zeta;
  rewrite interp_schedule_rr_ret by reflexivity;
  lazymatch goal with
  | |- interp_schedule_rr _ _ (?v -- _) _ _ _ ~ _ =>
      let v' := eval cbn in v in change v with v'
  end;
  rewrite vector_remove_head;
  apply interp_schedule_rr_empty.

(** ** Behavior *)

(** Both CAS outcomes, the adjacent allocation, release of the whole first
    extent, and the observation stamps. *)
Theorem lifecycle_scope :
  exists memory : ManagedHeap,
    run_rr lifecycle managed_empty 0 ~
      emit_list [stamp (80,1) 0; stamp (81,0) 1; stamp (82,11) 2]%list
        (Ret (tt,(memory,3))) /\
    fst memory 1 = None /\ fst memory 2 = None /\ fst memory 3 = None /\
    fst memory 4 = Some 11 /\ fst memory 5 = Some 0 /\
    snd memory 1 = None /\ snd memory 4 = Some 2.
Proof.
  eexists; split.
  - rewrite run_rr_focus; unfold lifecycle.
    rr_step; rr_alloc 1.
    rr_step; rr_alloc 4.
    (* three checked writes, then both CAS outcomes *)
    do 6 rr_step.
    do 4 rr_step.
    unfold emit_list; cbn [List.fold_right].
    rr_step; rr_step.
    apply sbisim_clo_bind_eq; [reflexivity|intros []].
    rr_step; rr_step.
    apply sbisim_clo_bind_eq; [reflexivity|intros []].
    (* free the first block, read the adjacent one, emit it *)
    do 6 rr_step.
    apply sbisim_clo_bind_eq; [reflexivity|intros []].
    rr_step.
    rr_finish.
  - repeat split; vm_compute; reflexivity.
Qed.

(** A released block is reused by the next first-fit malloc, with its whole
    extent recorded and zero-initialized again. *)
Theorem reuse_first_fit :
  exists memory : ManagedHeap,
    run_rr reallocate managed_empty 0 ~
      emit_list [stamp (83,1) 0]%list (Ret (tt,(memory,1))) /\
    snd memory 1 = Some 3 /\
    fst memory 1 = Some 0 /\ fst memory 2 = Some 0 /\ fst memory 3 = Some 0.
Proof.
  eexists; split.
  - rewrite run_rr_focus; unfold reallocate.
    rr_step; rr_alloc 1.
    rr_step; rr_step.
    rr_step; rr_alloc 1.
    unfold emit_list; cbn [List.fold_right].
    rr_step; rr_step.
    apply sbisim_clo_bind_eq; [reflexivity|intros []].
    rr_step.
    rr_finish.
  - repeat split; vm_compute; reflexivity.
Qed.

(** Freeing null leaves every component of the state unchanged. *)
Theorem free_null_unchanged (memory : ManagedHeap) c :
  run_rr (CFree 0) memory c ~ Ret (tt,(memory,c)).
Proof.
  rewrite run_rr_focus.
  rewrite (interp_rr_free _ _ _ 0 _ _ memory memory c eq_refl).
  rr_finish.
Qed.

(** ** Faults *)

Theorem invalid_interior_stuck :
  run_rr invalid_interior managed_empty 0 ~
    (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  rewrite run_rr_focus; unfold invalid_interior.
  rr_step; rr_alloc 1.
  cbn beta iota zeta.
  apply interp_rr_free_invalid; vm_compute; reflexivity.
Qed.

Theorem invalid_double_stuck :
  run_rr invalid_double managed_empty 0 ~
    (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  rewrite run_rr_focus; unfold invalid_double.
  rr_step; rr_alloc 1.
  rr_step; rr_step.
  cbn beta iota zeta.
  apply interp_rr_free_invalid; vm_compute; reflexivity.
Qed.

Theorem use_after_free_read_stuck :
  run_rr use_after_free_read managed_empty 0 ~
    (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  rewrite run_rr_focus; unfold use_after_free_read.
  rr_step; rr_alloc 1.
  rr_step; rr_step.
  rr_step; cbn beta iota zeta.
  apply interp_rr_read_missing; vm_compute; reflexivity.
Qed.

Theorem use_after_free_write_stuck :
  run_rr use_after_free_write managed_empty 0 ~
    (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  rewrite run_rr_focus; unfold use_after_free_write.
  rr_step; rr_alloc 1.
  rr_step; rr_step.
  cbn beta iota zeta.
  apply interp_rr_write_missing; vm_compute; reflexivity.
Qed.

Theorem use_after_free_cas_stuck :
  run_rr use_after_free_cas managed_empty 0 ~
    (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  rewrite run_rr_focus; unfold use_after_free_cas.
  rr_step; rr_alloc 1.
  rr_step; rr_step.
  rr_step; cbn beta iota zeta.
  apply interp_rr_cas_missing; vm_compute; reflexivity.
Qed.
