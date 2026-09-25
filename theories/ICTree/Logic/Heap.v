(** * Logical corollaries of the checked heap interpreter.

    The only genuinely *logical* fact about the heap handler is that an
    out-of-footprint dereference cannot step.  It lives here, above the
    interpreter, rather than in the event or model module. *)

From Coinduction Require Import coinduction.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Interp.State.Mod
  ICTree.Interp.Heap
  ICTree.Events.Heap
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  Logic.Core.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

(** [equ] is made typeclass-transparent for setoid rewriting, and
    [coinduction] is imported so that its [#[export] Typeclasses Opaque t]
    is in scope: without it, resolution unfolds past the companion and a
    single [reflexivity] at a generic effect type costs tens of seconds. *)
Local Typeclasses Transparent equ.

Section HeapNoStep.
  Context {F G : Type} {HF : Encode F} {HG : Encode G} {Sigma : Type}
    (other : G ~> stateT (Heap * Sigma) (ictree F)).

  (** An out-of-footprint read cannot step, regardless of its continuation. *)
  Lemma interp_heap_rd_nostep {X} : forall a h (aux : Sigma)
    (k : nat -> ictree (heapE + G) X) w,
    h a = None ->
    ~ can_step
        (interp_state (h_sum heap_handler other) (x <- heap_read a;; k x) (h,aux)) w.
  Proof.
    intros a h aux k w H.
    unfold heap_read, ICtree.trigger, resum, ReSum_inl, resum_ret, ReSumRet_inl.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_rd_none (F:=F) a h aux H).
    intro Hs; apply can_step_bind in Hs as [(t' & w' & TR & _) | (y & w' & TR & _)];
      revert TR; apply ktrans_stuck.
  Qed.
End HeapNoStep.
