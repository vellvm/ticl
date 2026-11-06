(** * Malloc/free lifecycle of the canonical CSL language.

    Concrete single-thread programs run through the real round-robin
    interpreter.  They pin the observable allocation discipline: first-fit
    zero-initialized malloc with recorded extents, whole-block free, reuse of a
    released block, the null-free no-op, and faults on interior-pointer,
    double, and use-after-free accesses. Every heap snapshot and indexed
    program observation is logged under [inl]; selections use [inr slot]. *)

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector.
From TICL Require Import
  CTree.Core
  CTree.Trace
  CTree.Events.Writer
  CTree.Events.Yield
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.RoundRobin
  Lang.CoCSL.Mod
  Utils.Vectors.

Import CTreeNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** ** Fixtures *)

Definition lifecycle : CProg unit :=
  CBind (CAlloc 3) (fun first =>
  CBind (CAlloc 2) (fun second =>
  CBind (CWrite first 7) (fun _ =>
  CBind (CWrite (first + 2) 9) (fun _ =>
  CBind (CWrite second 11) (fun _ =>
  CBind (CCAS (CLit first) (CLit 7) (CLit 8)) (fun succeeded =>
  CBind (CCAS (CLit first) (CLit 7) (CLit 99)) (fun failed =>
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
  CBind (CCAS (CLit (base + 2)) (CLit 0) (CLit 17)) (fun _ => CRet tt))).

(** ** Driving the single-thread round-robin run

    Each step applies one source execution rule of [Lang.CoCSL.Mod] at the
    focused thread; concrete heap facts are discharged by computation. *)

Lemma run_rr_focus p (s : SSig) :
  run_rr p s ≅
  interp_schedule_rr sh 1
    (([Ret tt] : pool sE Bn 1) @ Fin.F1 := (denote_flow p >>= fun _ => Ret tt))
    (Some Fin.F1) 0 s.
Proof. reflexivity. Qed.

Ltac first_fit :=
  let j := fresh "j" in
  let Pos := fresh "Pos" in
  let Lt := fresh "Lt" in
  let Free := fresh "Free" in
  intros j Pos Lt Free; apply block_freeb_spec in Free;
  repeat (lia || (destruct j as [|j];
    [solve [lia | vm_compute in Free; discriminate] |])).

(** Split a shared leading observation. *)
Ltac rr_log :=
  unfold log; rewrite !bind_vis; setoid_rewrite bind_ret_l; apply sb_vis; intros [].

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
  | |- interp_schedule_rr _ _ (_ @ _ := (denote_flow (CCAS (CLit _) (CLit _) (CLit _)) >>= _)) _ _ _ ~ _ =>
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
  let m1 := managed_alloc managed_empty 1 3 in
  let m2 := managed_alloc m1 4 2 in
  let m3 := (upd (fst m2) 1 7, snd m2) in
  let m4 := (upd (fst m3) 3 9, snd m3) in
  let m5 := (upd (fst m4) 4 11, snd m4) in
  let m6 := (upd (fst m5) 1 8, snd m5) in
  let m7 := (hfree_block 1 3 (fst m6), hfree 1 (snd m6)) in
  exists memory : ManagedHeap,
    run_rr lifecycle (managed_empty,((List.nil : Ctx.Ctx),0)) ~
      emit_list (List.map inl
        [CSLHeap m1; CSLHeap m2; CSLHeap m3; CSLHeap m4; CSLHeap m5;
         CSLHeap m6; CSLEmit (stamp (80,1) 0); CSLEmit (stamp (81,0) 1);
         CSLHeap m7; CSLEmit (stamp (82,11) 2)]%list)
        (Ret ((memory,((List.nil : Ctx.Ctx),3)),tt)
          : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)) /\
    fst memory 1 = None /\ fst memory 2 = None /\ fst memory 3 = None /\
    fst memory 4 = Some 11 /\ fst memory 5 = Some 0 /\
    snd memory 1 = None /\ snd memory 4 = Some 2.
Proof.
  intros m1 m2 m3 m4 m5 m6 m7; eexists; split.
  - rewrite run_rr_focus; unfold lifecycle, emit_list; cbn [List.fold_right List.map].
    rr_step; rr_alloc 1; rr_log.
    rr_step; rr_alloc 4; rr_log.
    (* Three checked writes and the successful CAS each record their post-memory. *)
    do 3 (rr_step; rr_step; rr_log).
    rr_step; rr_step; rr_log.
    (* The failed CAS is silent; each explicit emission advances the counter. *)
    rr_step; rr_step.
    rr_step; rr_step; rr_log.
    rr_step; rr_step; rr_log.
    (* Release the first block, read the adjacent one, and emit the value. *)
    rr_step; rr_step; rr_log.
    rr_step; rr_step.
    rr_step; rr_step; rr_log.
    rr_step.
    rr_finish.
  - repeat split; vm_compute; reflexivity.
Qed.

(** A released block is reused by the next first-fit malloc, with its whole
    extent recorded and zero-initialized again. *)
Theorem reuse_first_fit :
  let allocated := managed_alloc managed_empty 1 3 in
  let released := (hfree_block 1 3 (fst allocated), hfree 1 (snd allocated)) in
  let allocated_again := managed_alloc released 1 3 in
  exists memory : ManagedHeap,
    run_rr reallocate (managed_empty,((List.nil : Ctx.Ctx),0)) ~
      emit_list (List.map inl
        [CSLHeap allocated; CSLHeap released; CSLHeap allocated_again;
         CSLEmit (stamp (83,1) 0)]%list) (Ret ((memory,((List.nil : Ctx.Ctx),1)),tt)
          : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)) /\
    snd memory 1 = Some 3 /\
    fst memory 1 = Some 0 /\ fst memory 2 = Some 0 /\ fst memory 3 = Some 0.
Proof.
  intros allocated released allocated_again; eexists; split.
  - rewrite run_rr_focus; unfold reallocate, emit_list; cbn [List.fold_right List.map].
    rr_step; rr_alloc 1; rr_log.
    rr_step; rr_step; rr_log.
    rr_step; rr_alloc 1; rr_log.
    rr_step; rr_step; rr_log.
    rr_step.
    rr_finish.
  - repeat split; vm_compute; reflexivity.
Qed.

(** Freeing null leaves every component of the state unchanged. *)
Theorem free_null_unchanged (memory : ManagedHeap) ctx c :
  run_rr (CFree 0) (memory,(ctx,c)) ~
    (Ret ((memory,(ctx,c)),tt) : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_focus.
  rewrite (interp_rr_free _ _ _ 0 _ _ memory memory ctx c eq_refl).
  rr_finish.
Qed.

(** ** Faults *)

Theorem invalid_interior_stuck :
  run_rr invalid_interior (managed_empty,((List.nil : Ctx.Ctx),0)) ~
    (emit_list [inl (CSLHeap (managed_alloc managed_empty 1 3))]%list Stuck
      : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_focus; unfold invalid_interior, emit_list; cbn [List.fold_right].
  rr_step; rr_alloc 1; rr_log.
  cbn beta iota zeta.
  apply interp_rr_free_invalid; vm_compute; reflexivity.
Qed.

Theorem invalid_double_stuck :
  run_rr invalid_double (managed_empty,((List.nil : Ctx.Ctx),0)) ~
    (emit_list (List.map inl [CSLHeap (managed_alloc managed_empty 1 3);
               CSLHeap (hfree_block 1 3 (fst (managed_alloc managed_empty 1 3)),
                        hfree 1 (snd (managed_alloc managed_empty 1 3)))]%list) Stuck
      : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_focus; unfold invalid_double, emit_list; cbn [List.fold_right List.map].
  rr_step; rr_alloc 1; rr_log.
  rr_step; rr_step; rr_log.
  cbn beta iota zeta.
  apply interp_rr_free_invalid; vm_compute; reflexivity.
Qed.

Theorem use_after_free_read_stuck :
  run_rr use_after_free_read (managed_empty,((List.nil : Ctx.Ctx),0)) ~
    (emit_list (List.map inl [CSLHeap (managed_alloc managed_empty 1 3);
               CSLHeap (hfree_block 1 3 (fst (managed_alloc managed_empty 1 3)),
                        hfree 1 (snd (managed_alloc managed_empty 1 3)))]%list) Stuck
      : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_focus; unfold use_after_free_read, emit_list; cbn [List.fold_right List.map].
  rr_step; rr_alloc 1; rr_log.
  rr_step; rr_step; rr_log.
  rr_step; cbn beta iota zeta.
  apply interp_rr_read_missing; vm_compute; reflexivity.
Qed.

Theorem use_after_free_write_stuck :
  run_rr use_after_free_write (managed_empty,((List.nil : Ctx.Ctx),0)) ~
    (emit_list (List.map inl [CSLHeap (managed_alloc managed_empty 1 3);
               CSLHeap (hfree_block 1 3 (fst (managed_alloc managed_empty 1 3)),
                        hfree 1 (snd (managed_alloc managed_empty 1 3)))]%list) Stuck
      : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_focus; unfold use_after_free_write, emit_list; cbn [List.fold_right List.map].
  rr_step; rr_alloc 1; rr_log.
  rr_step; rr_step; rr_log.
  cbn beta iota zeta.
  apply interp_rr_write_missing; vm_compute; reflexivity.
Qed.

Theorem use_after_free_cas_stuck :
  run_rr use_after_free_cas (managed_empty,((List.nil : Ctx.Ctx),0)) ~
    (emit_list (List.map inl [CSLHeap (managed_alloc managed_empty 1 3);
               CSLHeap (hfree_block 1 3 (fst (managed_alloc managed_empty 1 3)),
                        hfree 1 (snd (managed_alloc managed_empty 1 3)))]%list) Stuck
      : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite run_rr_focus; unfold use_after_free_cas, emit_list; cbn [List.fold_right List.map].
  rr_step; rr_alloc 1; rr_log.
  rr_step; rr_step; rr_log.
  rr_step; cbn beta iota zeta.
  apply interp_rr_cas_missing; vm_compute; reflexivity.
Qed.
