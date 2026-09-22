From Stdlib Require Import Lia Arith.PeanoNat.
From ExtLib Require Import Data.Monads.StateMonad.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Events.Writer
  ICTree.Interp.State.Mod Lang.CSL.Heap.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

Lemma allocated_read_returns a h c v :
  h a = Some v ->
  runStateT (sh (inl (HRead a))) (h,c) ≅ Ret (v,(h,c)).
Proof. apply sh_rd_some. Qed.

Lemma empty_read_faults a c :
  interp_state sh (heap_read (E:=sE) a) (hemp,c) ≅
    (stuck : ictreeW SObs (nat * SSig)).
Proof. apply sinterp_srd_stuck; reflexivity. Qed.

Lemma empty_write_faults a v c :
  interp_state sh (heap_write (E:=sE) a v) (hemp,c) ≅
    (stuck : ictreeW SObs (unit * SSig)).
Proof. apply sinterp_swr_stuck; reflexivity. Qed.

Lemma allocated_write_updates a h c v old :
  h a = Some old ->
  runStateT (sh (inl (HWrite a v))) (h,c) ≅ Ret (tt,(upd h a v,c)).
Proof. apply sh_wr_some. Qed.

Lemma emit_records_current_index q v h c :
  runStateT (sh (inr (Log (q,v)))) (h,c) ≅
    (log (SPop q v c);; Ret (tt,(h,S c))).
Proof. apply sh_emit. Qed.

Lemma alloc_empty_two :
  runStateT (sh (inl (HAlloc 2))) (hemp,5) ~
    Ret (1,(hunion (hblock 1 2) hemp,5)).
Proof.
  apply sh_alloc_first; try lia.
  - apply block_freeb_spec; reflexivity.
Qed.

Lemma alloc_skips_partial_overlap :
  runStateT (sh (inl (HAlloc 2))) (Pcm.hsingle 2 99,5) ~
    Ret (3,(hunion (hblock 3 2) (Pcm.hsingle 2 99),5)).
Proof.
  apply sh_alloc_first; try lia.
  - apply block_freeb_spec; reflexivity.
  - intros j J L F; assert (j = 1 \/ j = 2) by lia.
    destruct H; subst j.
    + specialize (F 1 ltac:(lia)); discriminate F.
    + specialize (F 0 ltac:(lia)); discriminate F.
Qed.

Lemma alloc_zero_stuck c :
  interp_state sh (heap_alloc (E:=sE) 0) (hemp,c) ≅
    (stuck : ictreeW SObs (nat * SSig)).
Proof. apply sinterp_salloc_zero. Qed.

Definition full_heap : Heap := fun _ : nat => Some 7.

Lemma alloc_full_heap_stuck size c :
  Nat.lt 0 size ->
  runStateT (sh (inl (HAlloc size))) (full_heap,c) ≅
    (stuck : ictreeW SObs (nat * SSig)).
Proof.
  intro Pos; apply (alloc_search_no_space (W:=SObs)); [exact Pos |].
  intros j J Free; specialize (Free 0 Pos); discriminate Free.
Qed.

Example cas_replacement_preserves_frame frame c :
  frame <> 2 ->
  interp_state sh
    (b <- heap_cas (E:=sE) 2 7 9 ;;
     current <- heap_read (E:=sE) 2 ;;
     framed <- heap_read (E:=sE) frame ;;
     Ret (b,current,framed)) (full_heap,c) ~
    Ret ((true,9,7),(upd full_heap 2 9,c)).
Proof.
  intro Frame.
  etransitivity; [apply sinterp_cas_success; reflexivity |].
  etransitivity; [eapply sinterp_rd with (v := 9); reflexivity |].
  etransitivity.
  - eapply sinterp_rd with (v := 7).
    unfold upd; destruct (Nat.eqb_spec frame 2); [contradiction | reflexivity].
  - rewrite interp_state_ret; reflexivity.
Qed.

Example cas_mismatch_preserves_entire_state frame c :
  interp_state sh
    (b <- heap_cas (E:=sE) 2 8 9 ;;
     current <- heap_read (E:=sE) 2 ;;
     framed <- heap_read (E:=sE) frame ;;
     Ret (b,current,framed)) (full_heap,c) ~
    Ret ((false,7,7),(full_heap,c)).
Proof.
  etransitivity.
  - eapply sinterp_cas_failure with (current := 7); [reflexivity | discriminate].
  - etransitivity; [eapply sinterp_rd with (v := 7); reflexivity |].
    etransitivity; [eapply sinterp_rd with (v := 7); reflexivity |].
    rewrite interp_state_ret; reflexivity.
Qed.

Example cas_same_value_still_succeeds frame c :
  interp_state sh
    (b <- heap_cas (E:=sE) 2 7 7 ;;
     current <- heap_read (E:=sE) 2 ;;
     framed <- heap_read (E:=sE) frame ;;
     Ret (b,current,framed)) (full_heap,c) ~
    Ret ((true,7,7),(upd full_heap 2 7,c)).
Proof.
  etransitivity; [apply sinterp_cas_success; reflexivity |].
  etransitivity; [eapply sinterp_rd with (v := 7); reflexivity |].
  etransitivity.
  - eapply sinterp_rd with (v := 7).
    unfold upd; destruct (Nat.eqb frame 2); reflexivity.
  - rewrite interp_state_ret; reflexivity.
Qed.

Example cas_missing_faults_before_continuation c :
  interp_state sh
    (b <- heap_cas (E:=sE) 1 0 9 ;;
     semit 10 (if b then 1 else 0) ;;
     Ret b) (Pcm.hsingle 2 99,c) ~
    (stuck : ictreeW SObs (bool * SSig)).
Proof. apply sinterp_cas_missing; reflexivity. Qed.
