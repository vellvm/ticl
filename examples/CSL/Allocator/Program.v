From Stdlib Require Import Arith.PeanoNat.
From TICL Require Import Lang.CSL.Syntax.
From examples Require Import CSL.Allocator.Layout.

(* Link-first remote frees and owner collection, scoped from mimalloc v2.5.2:
   https://raw.githubusercontent.com/microsoft/mimalloc/v2.5.2/src/free.c
   https://raw.githubusercontent.com/microsoft/mimalloc/v2.5.2/src/page.c
   This model omits delayed-free flags and abandoned-page recovery. *)

Fixpoint init_links (first count : nat) {struct count} : CProg unit :=
  match count with
  | 0 => CRet tt
  | S rest =>
      CBind (CWrite first
        (match rest with 0 => 0 | S _ => first + 2 end)) (fun _ =>
      init_links (first + 2) rest)
  end.

Definition init_page (base capacity : nat) : CProg unit :=
  CBind (CWrite (remote_head base) 0) (fun _ =>
  CBind (CWrite (drain_head base) 0) (fun _ =>
  CBind (CWrite (mailbox base false) 0) (fun _ =>
  CBind (CWrite (mailbox base true) 0) (fun _ =>
  CBind (CWrite (local_head base)
    (match capacity with 0 => 0 | S _ => base + 5 end)) (fun _ =>
  init_links (base + 5) capacity))))).

Definition new_page (capacity : nat) : CProg nat :=
  CBind (CAlloc (page_size capacity)) (fun base =>
  CBind (init_page base capacity) (fun _ => CRet base)).

Definition remote_attempt (base block : nat) : CProg (option unit) :=
  CBind (CRead (remote_head base)) (fun old =>
  CBind CYield (fun _ =>
  CBind (CWrite block old) (fun _ =>
  CBind CYield (fun _ =>
  CBind (CCAS (remote_head base) old block) (fun success =>
    if success then
      CBind (CEmit tag_retire block) (fun _ =>
      CRet (None : option unit))
    else
      CBind (CEmit tag_retry block) (fun _ =>
      CBind CYield (fun _ =>
      CRet (Some tt : option unit)))))))).

Definition remote_free (base block : nat) : CProg unit :=
  CUntilNone (remote_attempt base block).

Definition detach_attempt (base : nat) : CProg (option unit) :=
  CBind (CRead (remote_head base)) (fun old =>
  CBind CYield (fun _ =>
  CBind (CCAS (remote_head base) old 0) (fun success =>
    if success then
      CBind (CWrite (drain_head base) old) (fun _ =>
      CBind CYield (fun _ =>
      CRet (None : option unit)))
    else
      CBind CYield (fun _ =>
      CRet (Some tt : option unit))))).

Definition detach_remote (base : nat) : CProg unit :=
  CUntilNone (detach_attempt base).

Definition reclaim_step (base : nat) : CProg (option unit) :=
  CBind (CRead (drain_head base)) (fun block =>
    if Nat.eqb block 0 then
      CBind CYield (fun _ => CRet (None : option unit))
    else
      CBind (CRead block) (fun next =>
      CBind (CRead (local_head base)) (fun local =>
      CBind (CWrite block local) (fun _ =>
      CBind (CWrite (local_head base) block) (fun _ =>
      CBind (CWrite (drain_head base) next) (fun _ =>
      CBind (CEmit tag_reclaim block) (fun _ =>
      CBind CYield (fun _ =>
      CRet (Some tt : option unit))))))))).

Definition collect_remote (base : nat) : CProg unit :=
  CBind (detach_remote base) (fun _ =>
  CUntilNone (reclaim_step base)).

Definition offer_block (base : nat) (client : bool) : CProg unit :=
  CBind (CRead (mailbox base client)) (fun offered =>
    if Nat.eqb offered 0 then
      CBind (CRead (local_head base)) (fun block =>
        if Nat.eqb block 0 then
          CBind CYield (fun _ => CRet tt)
        else
          CBind (CRead block) (fun next =>
          CBind (CWrite (local_head base) next) (fun _ =>
          CBind (CWrite (mailbox base client) block) (fun _ =>
          CBind (CEmit tag_alloc block) (fun _ =>
          CBind CYield (fun _ => CRet tt))))))
    else
      CBind CYield (fun _ => CRet tt)).

Definition client_round (base : nat) (client : bool) : CProg (option unit) :=
  CBind (CRead (mailbox base client)) (fun block =>
    if Nat.eqb block 0 then
      CBind CYield (fun _ => CRet (Some tt : option unit))
    else
      CBind (CWrite (mailbox base client) 0) (fun _ =>
      CBind (CWrite (S block) (if client then 2 else 1)) (fun _ =>
      CBind CYield (fun _ =>
      CBind (remote_free base block) (fun _ =>
      (* Publication has returned; the client no longer accesses block. *)
      CBind CYield (fun _ =>
      CRet (Some tt : option unit))))))).

Definition remote_client (base : nat) (client : bool) : CProg unit :=
  CUntilNone (client_round base client).

Definition owner_round (base : nat) : CProg (option unit) :=
  CBind (collect_remote base) (fun _ =>
  CBind (offer_block base false) (fun _ =>
  CBind (offer_block base true) (fun _ =>
  CRet (Some tt : option unit)))).

Definition owner (base : nat) : CProg unit :=
  CBind CYield (fun _ => CUntilNone (owner_round base)).

Definition allocator_program (capacity : nat) : CProg unit :=
  CBind (new_page capacity) (fun base =>
  CBind (CFork (remote_client base false)) (fun _ =>
  CBind (CFork (remote_client base true)) (fun _ =>
  owner base))).
