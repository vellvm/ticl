(** * Checked sequential queue rotation with occurrence-indexed observations.

    Three deliberate departures from the reference language [Lang.HeapImp],
    each of which is a research decision rather than a convenience:

    1. **The handler is safe.**  A read or a write outside the current heap's
       domain produces [Stuck].  [HeapImp]'s [Put] never checks, and its
       [Get] on an unmapped address is also stuck; here BOTH are checked, so an
       out-of-footprint access invalidates every [AG] specification rather than
       silently corrupting an unrelated cell.  The footprint discipline is
       therefore forced by the temporal proof, not assumed alongside it.

    2. **The observation is heap-free.**  [HeapImp] logs the WHOLE memory on
       every write, which puts numeric addresses into the world and makes any
       world-literal specification frame-unstable.  Here the only logged event
       is the (fun o => indexed_value o = payload) together with an occurrence index, so the world
       never mentions an address.

    3. **The observation is occurrence-tagged.**  [stamp v k] carries the number
       of pops that preceded it.  A retained [Obs (Log (stamp v k)) tt] world
       cannot satisfy an occurrence-indexed formula for a later index, which is
       what makes "the same element is (fun o => indexed_value o = AGAIN)" a checkable statement
       rather than a re-reading of a stale world.

    The projection back to the reference alphabet is [indexed_value]: the reference
    [examples/Queue.v] logs the (fun o => indexed_value o = payload) [h : T] and specifies
    [visW {fun h => h = nl}]; here the corresponding formula is
    [visW {fun o => indexed_value o = nl}]. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.
From Coinduction Require Import all.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad.

From TICL Require Import
  CTree.Core
  CTree.Interp.State.Mod
  CTree.Events.State
  CTree.Events.Writer
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.Bind
  CTree.Logic.Iter
  CTree.Logic.State
  Logic.Core
  CTree.Interp.CSL.Mod.

From examples Require Import CSL.Queue.Representation CSL.Queue.Operations.


Import CTree CTreeNotations TiclNotations ListNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

(** ** The observation alphabet and its projection.

    Observations are [indexed nat]: the (fun o => indexed_value o = payload) together with the
    number of pops that preceded it.  Both the record and its indexing
    handler are owned by [Events.WriterE] / [CTree.Events.Writer]. *)

(** ** Events *)

Notation qE := (heapE +' (stateE Ctx.Ctx +' writerE nat)).

(** Memory commands use the shared heap triggers; payload emission is the
    example-specific instruction in the right summand. *)
Definition emit (v: nat) : ctree qE Bn unit :=
  CTree.trigger (inr1 (inr1 (Log v)) : qE unit).

(** ** The rotating queue program.

    One iteration: read the head pointer, read and EMIT the head payload, read
    the head's link, detach, find the node to append after, and re-link.  No
    allocation and no free: the same four cells are rewritten forever. *)

Definition rot_body (hdr: nat) : ctree qE Bn (unit + unit) :=
  queue_turn emit hdr (Ret (inl tt)).

Definition rotate (hdr: nat) : ctree qE Bn unit :=
  CTree.iter (fun _: unit => rot_body hdr) tt.

(** [run] interprets the rotation with the one CSL handler [sh] at the unary
    payload [nat].  Its state is the shared CSL state [SSig]: the managed
    memory [(h,allocs)], the (unused) variable context, and the PRIVATE
    occurrence counter.  The rotation never
    allocates or frees, so [allocs] is carried through unchanged; no heap
    operation reads the counter, which only indexes the observations. *)
Definition run (hdr: nat) (s: SSig) : ctreeW (CSLObs nat) Bn (SSig * unit) :=
  interp_state (sh (A:=nat)) (rotate hdr) s.

(** ** The body correspondence.

    ONE completed rotation is strongly bisimilar to a SINGLE logged step
    followed by a return.  Three things are packed into this one statement:

    - **hidden-segment termination.**  Every read and write in the body is
      silent and finite, so the whole heap segment collapses; there is no
      stuttering to reason about, and in particular no next-sensitive
      stuttering theorem is needed.  This holds ONLY because every access is
      inside the footprint: an out-of-footprint access would leave [Stuck]
      in place of a [Ret] and the collapse would fail ([interp_heap_rd_nostep]).

    - **operation correctness.**  The resulting heap is [rot_heap], which
      [Representation.rot_heap_spec] proves implements the abstract pop-and-push.

    - **the observation.**  The single event is [stamp v c] where [v] is the
      payload READ OUT OF the head node's cell and [c] is the occurrence
      counter before the pop. *)
Theorem rot_body_spec: forall hdr a ns v vs h allocs ctx c,
    qrep hdr (a :: ns) (v :: vs) h ->
    interp_state (sh (A:=nat)) (rot_body hdr) ((h, allocs), (ctx, c))
    ~ (log (inr (stamp v c) : CSLObs nat) ;;
       Ret (((rot_heap hdr a (List.hd 0 ns) (zof hdr ns) h, allocs), (ctx, S c)),
            @inl unit unit tt) : ctreeW (CSLObs nat) Bn (SSig * (unit + unit))).
Proof.
  intros hdr a ns v vs h allocs ctx c Hq; unfold rot_body.
  etransitivity.
  - eapply (queue_turn_spec emit (fun v c => inr (stamp v c))).
    + intros; apply interp_csl_emit.
    + exact Hq.
  - rewrite !log_vis; apply sb_vis; intros _.
    rewrite interp_state_ret; reflexivity.
Qed.
