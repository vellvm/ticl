From TICL Require Import ICTree.Events.Heap.

(* Raw command clients require no language-specific module. *)
Check (heap_read (E:=heapE)).
Check (heap_write (E:=heapE)).
Check (heap_alloc (E:=heapE)).
Check (heap_free (E:=heapE)).
Check (heap_cas (E:=heapE)).

From Stdlib Require Import Arith.PeanoNat Lia List.
From ExtLib Require Import Data.Monads.StateMonad.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Heap ICTree.Events.Writer ICTree.Interp.State.Mod
  Lang.CSL.Heap Lang.CSL.Denote Lang.HeapImp.
Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.
Module HI := TICL.Lang.HeapImp.HeapImp.

Check (heap_read (E:=(heapE + writerE nat)%type) :
  nat -> ictree (heapE + writerE nat) nat).
Check (heap_write (E:=(heapE + writerE nat)%type) :
  nat -> nat -> ictree (heapE + writerE nat) unit).
Check (heap_alloc (E:=(heapE + writerE nat)%type) :
  nat -> ictree (heapE + writerE nat) nat).
Check (heap_free (E:=(heapE + writerE nat)%type) :
  nat -> ictree (heapE + writerE nat) unit).
Check (heap_cas (E:=(heapE + writerE nat)%type) :
  nat -> nat -> nat -> ictree (heapE + writerE nat) bool).

Check (heap_read (E:=CEff) : nat -> ictree CEff nat).
Check (heap_write (E:=CEff) : nat -> nat -> ictree CEff unit).
Check (heap_alloc (E:=CEff) : nat -> ictree CEff nat).
Check (heap_free (E:=CEff) : nat -> ictree CEff unit).
Check (heap_cas (E:=CEff) : nat -> nat -> nat -> ictree CEff bool).

Local Definition heapimp_empty : HI.Mem :=
  {| HI.store := nil; HI.heap := nil |}.
Local Definition alloc_free_alloc : ictree sE (nat * nat) :=
  a <- heap_alloc 1;; heap_free a;; b <- heap_alloc 1;; Ret (a,b).
Local Definition two_cell_frame : Pcm.Heap :=
  hunion (hblock 1 2) (Pcm.hsingle 9 42).

Lemma shared_heap_alloc_free_reuses_cell :
  interp_state sh alloc_free_alloc (hemp,7) ~
    Ret ((1,1),
      (hunion (hblock 1 1) (Pcm.hfree 1 (hunion (hblock 1 1) hemp)),7)).
Proof.
  unfold alloc_free_alloc.
  etransitivity.
  - eapply sinterp_alloc_first with (base:=1); try lia.
    apply block_freeb_spec; reflexivity.
  - etransitivity; [apply sinterp_free |].
    etransitivity.
    + eapply sinterp_alloc_first with (base:=1); try lia.
      apply block_freeb_spec; reflexivity.
    + eapply equ_clos_sbisim_goal;
        [apply interp_state_ret | reflexivity | reflexivity].
Qed.

Lemma shared_heap_free_preserves_other_cells :
  (interp_state sh
     (heap_free 1;;
      other <- heap_read 2;;
      framed <- heap_read 9;;
      Ret (other,framed)) (two_cell_frame,7) ~
     Ret ((0,42),(Pcm.hfree 1 two_cell_frame,7))) /\
  Pcm.hfree 1 two_cell_frame 1 = None.
Proof.
  split.
  - etransitivity; [apply sinterp_free |].
    etransitivity; [eapply sinterp_rd with (v:=0); reflexivity |].
    etransitivity; [eapply sinterp_rd with (v:=42); reflexivity |].
    eapply equ_clos_sbisim_goal;
      [apply interp_state_ret | reflexivity | reflexivity].
  - reflexivity.
Qed.

Lemma shared_heap_free_absent_succeeds :
  (interp_state sh (heap_free (E:=sE) 42) (hemp,7) ~
     Ret (tt,(Pcm.hfree 42 hemp,7))) /\
  heq (Pcm.hfree 42 hemp) hemp.
Proof.
  split.
  - pose proof (sinterp_free 42 hemp 7
      (fun x : unit => (Ret x : ictree sE unit))) as Hfree.
    rewrite bind_ret_r, interp_state_ret in Hfree.
    exact Hfree.
  - intro a; unfold Pcm.hfree, hemp.
    destruct (Nat.eq_dec 42 a); reflexivity.
Qed.

Lemma shared_heap_read_after_free_stuck :
  interp_state sh (heap_free 1;; heap_read 1) (Pcm.hsingle 1 9,7) ~
    (stuck : ictreeW SObs (nat * SSig)).
Proof.
  etransitivity; [apply sinterp_free |].
  eapply equ_clos_sbisim_goal;
    [apply sinterp_srd_stuck; reflexivity | reflexivity | reflexivity].
Qed.

Lemma heapimp_alloc_zero_preserved :
  (instr_stateE (HI.h_heapimp (HAlloc 0)) heapimp_empty ~
     (log heapimp_empty;; Ret (0,heapimp_empty))) /\
  interp_state sh (heap_alloc (E:=sE) 0) (hemp,7) ≅
    (stuck : ictreeW SObs (nat * SSig)).
Proof.
  split.
  - unfold HI.h_heapimp, instr_stateE.
    rewrite interp_state_bind.
    lazymatch goal with |- (?t >>= ?k) ~ _ =>
      etransitivity; [apply sbisim_clo_bind_eq with (k2:=k);
        [apply interp_state_get | intro result; reflexivity] |]
    end.
    rewrite bind_ret_l.
    cbn [HI.fresh_addr HI.heap_init HI.heap HI.store heapimp_empty].
    rewrite interp_state_bind.
    lazymatch goal with |- (?t >>= ?k) ~ _ =>
      etransitivity; [apply sbisim_clo_bind_eq with (k2:=k);
        [apply interp_state_put | intro result; reflexivity] |]
    end.
    rewrite bind_bind.
    apply sbisim_clo_bind_eq; [reflexivity | intros []].
    rewrite bind_ret_l, interp_state_ret; reflexivity.
  - apply sinterp_salloc_zero.
Qed.

Lemma heapimp_free_absent_still_logs :
  instr_stateE (HI.h_heapimp (HFree 42)) heapimp_empty ~
    (log (HI.free_heap 42 heapimp_empty);;
     Ret (tt,HI.free_heap 42 heapimp_empty)).
Proof.
  unfold HI.h_heapimp, instr_stateE.
  rewrite interp_state_bind.
  lazymatch goal with |- (?t >>= ?k) ~ _ =>
    etransitivity; [apply sbisim_clo_bind_eq with (k2:=k);
      [apply interp_state_get | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l.
  apply interp_state_put.
Qed.

Lemma heapimp_write_absent_still_allocates :
  (instr_stateE (HI.h_heapimp (HWrite 1 9)) heapimp_empty ~
     (log (HI.update_heap 1 9 heapimp_empty);;
      Ret (tt,HI.update_heap 1 9 heapimp_empty))) /\
  interp_state sh (heap_write (E:=sE) 1 9) (hemp,7) ≅
    (stuck : ictreeW SObs (unit * SSig)).
Proof.
  split.
  - unfold HI.h_heapimp, instr_stateE.
    rewrite interp_state_bind.
    lazymatch goal with |- (?t >>= ?k) ~ _ =>
      etransitivity; [apply sbisim_clo_bind_eq with (k2:=k);
        [apply interp_state_get | intro result; reflexivity] |]
    end.
    rewrite bind_ret_l.
    apply interp_state_put.
  - apply sinterp_swr_stuck; reflexivity.
Qed.

Lemma heapimp_cas_same_value_logs :
  let m := HI.update_heap 1 7 heapimp_empty in
  (instr_stateE (HI.h_heapimp (HCAS 1 7 7)) m ~
     (log (HI.update_heap 1 7 m);; Ret (true,HI.update_heap 1 7 m))) /\
  (instr_stateE (HI.h_heapimp (HCAS 1 8 9)) m ~ Ret (false,m)).
Proof.
  cbn zeta.
  assert (Lookup : ExtLib.Structures.Maps.lookup 1
    (HI.heap (HI.update_heap 1 7 heapimp_empty)) = Some 7).
  { unfold HI.update_heap; cbn.
    pose proof (ExtLib.Structures.Maps.mapsto_add_eq (R:=@eq nat) (V:=nat)
      (HI.heap heapimp_empty) 1 7) as Hlookup.
    now apply ExtLib.Structures.Maps.mapsto_lookup in Hlookup. }
  split.
  - unfold HI.h_heapimp, instr_stateE.
    rewrite interp_state_bind.
    lazymatch goal with |- (?t >>= ?k) ~ _ =>
      etransitivity; [apply sbisim_clo_bind_eq with (k2:=k);
        [apply interp_state_get | intro result; reflexivity] |]
    end.
    rewrite bind_ret_l.
    rewrite Lookup; cbn [Nat.eqb].
    rewrite interp_state_bind.
    lazymatch goal with |- (?t >>= ?k) ~ _ =>
      etransitivity; [apply sbisim_clo_bind_eq with (k2:=k);
        [apply interp_state_put | intro result; reflexivity] |]
    end.
    rewrite bind_bind.
    apply sbisim_clo_bind_eq; [reflexivity | intros []].
    rewrite bind_ret_l, interp_state_ret; reflexivity.
  - unfold HI.h_heapimp, instr_stateE.
    rewrite interp_state_bind.
    lazymatch goal with |- (?t >>= ?k) ~ _ =>
      etransitivity; [apply sbisim_clo_bind_eq with (k2:=k);
        [apply interp_state_get | intro result; reflexivity] |]
    end.
    rewrite bind_ret_l.
    rewrite Lookup; cbn [Nat.eqb].
    rewrite interp_state_ret; reflexivity.
Qed.
