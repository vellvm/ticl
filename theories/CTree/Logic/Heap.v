(** * Logical corollaries of the checked heap interpreter.

    The only genuinely *logical* fact about the heap handler is that an
    out-of-footprint dereference cannot step.  It lives here, above the
    interpreter, rather than in the event or model module. *)

From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Interp.State.Mod
  CTree.Interp.Heap
  CTree.Events.Heap
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Core.

Import CTreeNotations.
Local Open Scope ctree_scope.

Section HeapNoStep.
  Context {F G B : Type -> Type} {Sigma : Type}
    (other : G ~> stateT (ManagedHeap * Sigma) (ctree F B)).

  (** An out-of-footprint read cannot step, regardless of its continuation. *)
  Lemma interp_heap_rd_nostep {X} : forall a h allocs (aux : Sigma)
    (k : nat -> ctree (heapE +' G) B X) w,
    h a = None ->
    ~ can_step
        (interp_state (h_sum heap_handler other) (x <- heap_read a;; k x) ((h,allocs),aux)) w.
  Proof.
    intros a h allocs aux k w H.
    rewrite interp_state_bind, (interp_heap_rd_stuck other a h allocs aux H).
    apply nostep_bind, can_step_stuck.
  Qed.
End HeapNoStep.
