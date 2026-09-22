(** * Checked sequential queue rotation with occurrence-indexed observations.

    Three deliberate departures from the reference language [Lang.HeapImp],
    each of which is a research decision rather than a convenience:

    1. **The handler is safe.**  A read or a write outside the current heap's
       domain produces [ICtree.stuck].  [HeapImp]'s [Put] never checks, and its
       [Get] on an unmapped address is also stuck; here BOTH are checked, so an
       out-of-footprint access invalidates every [AG] specification rather than
       silently corrupting an unrelated cell.  The footprint discipline is
       therefore forced by the temporal proof, not assumed alongside it.

    2. **The observation is heap-free.**  [HeapImp] logs the WHOLE memory on
       every write, which puts numeric addresses into the world and makes any
       world-literal specification frame-unstable.  Here the only logged event
       is the popped payload together with an occurrence index, so the world
       never mentions an address.

    3. **The observation is occurrence-tagged.**  [Pop v k] carries the number
       of pops that preceded it.  A retained [Obs (Log (Pop v k)) tt] world
       cannot satisfy an occurrence-indexed formula for a later index, which is
       what makes "the same element is popped AGAIN" a checkable statement
       rather than a re-reading of a stale world.

    The projection back to the reference alphabet is [qval]: the reference
    [examples/Queue.v] logs the popped payload [h : T] and specifies
    [visW {fun h => h = nl}]; here the corresponding formula is
    [visW {fun o => qval o = nl}]. *)

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
  ICTree.Events.Writer
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.State
  Logic.Core
  Lang.CSL.Heap.

From TICL Require Import Lang.CSL.Queue.Representation Lang.CSL.Queue.Operations.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

(** Needed so that [equ] rewrites go through inside [sbisim] goals; the
    reference files [Lang/MeQ.v] and [examples/Queue.v] do the same. *)
Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.

(** ** The observation alphabet and its projection *)

Record QObs : Type := Pop { qval: nat ; qidx: nat }.

(** ** Events *)

Definition qE : Type := (heapE + writerE nat)%type.

(** Memory commands use the shared heap triggers; payload emission is the
    example-specific instruction in the right summand. *)
Definition emit (v: nat) : ictree qE unit :=
  @ICtree.trigger (writerE nat) qE _ _ ReSum_inr ReSumRet_inr (Log v).

(** The interpretation state: the OWNED heap and the PRIVATE occurrence
    counter.  The counter is not part of the heap and no heap operation reads
    it; it exists to index the observations. *)
Notation Sig := (Heap * nat)%type.

(** ** The safe handler *)
Definition q_emit_handler: writerE nat ~> stateT Sig (ictreeW QObs) :=
  fun e =>
    mkStateT (fun '(h, c) =>
                match e return ictreeW QObs (encode e * Sig) with
                | Log v => log (Pop v c) ;; Ret (tt, (h, S c))
                end).

Definition h_qE: qE ~> stateT Sig (ictreeW QObs) :=
  h_sum (heap_handler (W:=QObs)) q_emit_handler.

(** *** Payload emission equations *)

Lemma h_emit: forall v h c,
    runStateT (h_qE (inr (Log v))) (h, c) ≅ (log (Pop v c) ;; Ret (tt, (h, S c))).
Proof. intros; cbn; reflexivity. Qed.

(** *** Lifting the handler equations through [interp_state]. *)

Lemma interp_emit {X}: forall v h c (k: unit -> ictree qE X),
    interp_state h_qE (x <- emit v ;; k x) (h, c)
    ~ (log (Pop v c) ;; interp_state h_qE (k tt) (h, S c)).
Proof.
  intros v h c k.
  unfold emit, ICtree.trigger, resum, ReSum_inr, resum_ret, ReSumRet_inr.
  rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis, h_emit, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l; apply sb_guard.
Qed.

(** ** The rotating queue program.

    One iteration: read the head pointer, read and EMIT the head payload, read
    the head's link, detach, find the node to append after, and re-link.  No
    allocation and no free: the same four cells are rewritten forever. *)

Definition rot_body (hdr: nat) : ictree qE (unit + unit) :=
  queue_turn emit hdr (Ret (inl tt)).

Definition rotate (hdr: nat) : ictree qE unit :=
  ICtree.iter (fun _: unit => rot_body hdr) tt.

Definition run (hdr: nat) (h: Heap) (c: nat) : ictreeW QObs (unit * Sig) :=
  interp_state h_qE (rotate hdr) (h, c).

(** ** The body correspondence.

    ONE completed rotation is strongly bisimilar to a SINGLE logged step
    followed by a return.  Three things are packed into this one statement:

    - **hidden-segment termination.**  Every read and write in the body is
      silent and finite, so the whole heap segment collapses; there is no
      stuttering to reason about, and in particular no next-sensitive
      stuttering theorem is needed.  This holds ONLY because every access is
      inside the footprint: an out-of-footprint access would leave [ICtree.stuck]
      in place of a [Ret] and the collapse would fail ([interp_heap_rd_nostep]).

    - **operation correctness.**  The resulting heap is [rot_heap], which
      [Representation.rot_heap_spec] proves implements the abstract pop-and-push.

    - **the observation.**  The single event is [Pop v c] where [v] is the
      payload READ OUT OF the head node's cell and [c] is the occurrence
      counter before the pop. *)
Theorem rot_body_spec: forall hdr a ns v vs h c,
    qrep hdr (a :: ns) (v :: vs) h ->
    interp_state h_qE (rot_body hdr) (h, c)
    ~ (log (Pop v c) ;;
       Ret (@inl unit unit tt, (rot_heap hdr a (hdf ns 0) (zof hdr ns) h, S c))).
Proof.
  intros hdr a ns v vs h c Hq; unfold rot_body.
  etransitivity.
  - eapply (queue_turn_spec q_emit_handler emit Pop).
    + intros; apply interp_emit.
    + exact Hq.
  - apply sbisim_clo_bind_eq; [reflexivity | intros []].
    apply equ_sbisim, interp_state_ret.
Qed.
