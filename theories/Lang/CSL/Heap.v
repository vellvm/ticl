(** * The CSL effect sum and its handler.

    Everything generic about checked heap access, allocation search and
    indexed observation lives one layer down, in [ICTree.Interp.Heap] and
    [ICTree.Events.Writer].  This module only fixes the CSL effect sum, its
    interpretation state, and the handler instance that pairs them. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Interp.State.Mod
  ICTree.Events.State
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.State
  Logic.Core.

From TICL Require Export
  Events.HeapModel
  ICTree.Events.Heap
  ICTree.Events.Writer
  ICTree.Interp.Heap
  ICTree.Logic.Heap.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.

(** ** Events *)

Definition sE : Type := (heapE + writerE (nat * nat))%type.

Definition semit (q v : nat) : ictree sE unit :=
  ICtree.trigger (Log (q,v)).

(** Interpretation state: the SHARED heap (which holds both queues and the
    outer frame) and one GLOBAL occurrence counter. *)
Notation SSig := (Heap * nat)%type.

(** The CSL handler is exactly the shared checked-heap handler summed with
    the shared indexing handler.  The tag travels in the payload; the

From Coinduction Require Import coinduction.
    occurrence index is supplied by [h_indexed], which owns the counter. *)
Definition sh : sE ~> stateT SSig (ictreeW (indexed (nat * nat))) :=
  h_sum heap_handler h_indexed.
