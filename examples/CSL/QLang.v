(** * QLang: a small heap language with a SAFE handler, and the rotation body.

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
  Logic.Core.

From examples Require Import CSL.HeapQ.

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

Variant heapE : Type :=
  | Rd (a: nat)
  | Wr (a: nat) (v: nat)
  | Emit (v: nat).

Global Instance encode_heapE: Encode heapE :=
  fun e => match e with Rd _ => nat | Wr _ _ => unit | Emit _ => unit end.

(** The three instructions.  They are written as raw [Vis] nodes rather than
    [ICtree.trigger]: [trigger e] unfolds to exactly this shape through the
    identity [ReSum]/[ReSumRet] instances, and keeping the [Vis] explicit lets
    every equation below go through [interp_state_vis] without any [resum]
    bookkeeping. *)
Definition rd (a: nat) : ictree heapE nat := Vis (Rd a) (fun x: nat => Ret x).
Definition wr (a v: nat) : ictree heapE unit := Vis (Wr a v) (fun _: unit => Ret tt).
Definition emit (v: nat) : ictree heapE unit := Vis (Emit v) (fun _: unit => Ret tt).

(** The interpretation state: the OWNED heap and the PRIVATE occurrence
    counter.  The counter is not part of the heap and no heap operation reads
    it; it exists to index the observations. *)
Notation Sig := (Heap * nat)%type.

(** ** The safe handler *)
Definition h_heapE: heapE ~> stateT Sig (ictreeW QObs) :=
  fun e =>
    mkStateT (fun s =>
                match e return ictreeW QObs (encode e * Sig) with
                | Rd a => match fst s a with
                         | Some v => Ret (v, s)
                         | None => ICtree.stuck
                         end
                | Wr a v => match fst s a with
                           | Some _ => Ret (tt, (upd (fst s) a v, snd s))
                           | None => ICtree.stuck
                           end
                | Emit v => log (Pop v (snd s)) ;; Ret (tt, (fst s, S (snd s)))
                end).

(** *** Handler equations.  These are pure computation on the handler; no
    [interp_state] appears, so they are safe to reduce. *)

Lemma h_rd_some: forall a h c v,
    h a = Some v -> runStateT (h_heapE (Rd a)) (h, c) ≅ Ret (v, (h, c)).
Proof. intros a h c v H; cbn; rewrite H; reflexivity. Qed.

Lemma h_rd_none: forall a h c,
    h a = None -> runStateT (h_heapE (Rd a)) (h, c) ≅ ICtree.stuck.
Proof. intros a h c H; cbn; rewrite H; reflexivity. Qed.

Lemma h_wr_some: forall a h c v w,
    h a = Some w -> runStateT (h_heapE (Wr a v)) (h, c) ≅ Ret (tt, (upd h a v, c)).
Proof. intros a h c v w H; cbn; rewrite H; reflexivity. Qed.

Lemma h_emit: forall v h c,
    runStateT (h_heapE (Emit v)) (h, c) ≅ (log (Pop v c) ;; Ret (tt, (h, S c))).
Proof. intros; cbn; reflexivity. Qed.

(** *** Lifting the handler equations through [interp_state]. *)

Lemma interp_rd {X}: forall a h c v (k: nat -> ictree heapE X),
    h a = Some v ->
    interp_state h_heapE (x <- rd a ;; k x) (h, c) ~ interp_state h_heapE (k v) (h, c).
Proof.
  intros a h c v k H.
  unfold rd; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis.
  rewrite (h_rd_some a h c v H), bind_ret_l.
  apply sb_guard.
Qed.

Lemma interp_wr {X}: forall a h c v w (k: unit -> ictree heapE X),
    h a = Some w ->
    interp_state h_heapE (x <- wr a v ;; k x) (h, c)
    ~ interp_state h_heapE (k tt) (upd h a v, c).
Proof.
  intros a h c v w k H.
  unfold wr; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis.
  rewrite (h_wr_some a h c v w H), bind_ret_l.
  apply sb_guard.
Qed.

Lemma interp_emit {X}: forall v h c (k: unit -> ictree heapE X),
    interp_state h_heapE (x <- emit v ;; k x) (h, c)
    ~ (log (Pop v c) ;; interp_state h_heapE (k tt) (h, S c)).
Proof.
  intros v h c k.
  unfold emit; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis, h_emit, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l; apply sb_guard.
Qed.

(** A read outside the footprint cannot step: this is the whole content of
    "the handler is safe", and it is what makes an out-of-footprint access
    invalidate every [AG] specification instead of corrupting a cell. *)
Lemma interp_rd_nostep {X}: forall a h c (k: nat -> ictree heapE X) w,
    h a = None ->
    ~ can_step (interp_state h_heapE (x <- rd a ;; k x) (h, c)) w.
Proof.
  intros a h c k w H.
  unfold rd; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis, (h_rd_none a h c H).
  intro Hs; apply can_step_bind in Hs as [(t' & w' & TR & _) | (y & w' & TR & _)];
    revert TR; apply ktrans_stuck.
Qed.

(** ** The rotating queue program.

    One iteration: read the head pointer, read and EMIT the head payload, read
    the head's link, detach, find the node to append after, and re-link.  No
    allocation and no free: the same four cells are rewritten forever. *)

Definition rot_body (hdr: nat) : ictree heapE (unit + unit) :=
  a  <- rd (S hdr) ;;
  v  <- rd a ;;
  _  <- emit v ;;
  n  <- rd (S a) ;;
  _  <- wr (S hdr) n ;;
  z0 <- rd hdr ;;
  _  <- wr (S (if Nat.eqb n 0 then hdr else z0)) a ;;
  _  <- wr (S a) 0 ;;
  _  <- wr hdr a ;;
  Ret (inl tt).

Definition rotate (hdr: nat) : ictree heapE unit :=
  ICtree.iter (fun _: unit => rot_body hdr) tt.

Definition run (hdr: nat) (h: Heap) (c: nat) : ictreeW QObs (unit * Sig) :=
  interp_state h_heapE (rotate hdr) (h, c).

Lemma interp_wr' {X}: forall a h c v (k: unit -> ictree heapE X),
    h a <> None ->
    interp_state h_heapE (x <- wr a v ;; k x) (h, c)
    ~ interp_state h_heapE (k tt) (upd h a v, c).
Proof.
  intros a h c v k H; destruct (h a) as [w |] eqn:E; [| contradiction].
  eapply interp_wr; eauto.
Qed.

(** ** The body correspondence.

    ONE completed rotation is strongly bisimilar to a SINGLE logged step
    followed by a return.  Three things are packed into this one statement:

    - **hidden-segment termination.**  Every read and write in the body is
      silent and finite, so the whole heap segment collapses; there is no
      stuttering to reason about, and in particular no next-sensitive
      stuttering theorem is needed.  This holds ONLY because every access is
      inside the footprint: an out-of-footprint access would leave [ICtree.stuck]
      in place of a [Ret] and the collapse would fail ([interp_rd_nostep]).

    - **operation correctness.**  The resulting heap is [rot_heap], which
      [HeapQ.rot_heap_spec] proves implements the abstract pop-and-push.

    - **the observation.**  The single event is [Pop v c] where [v] is the
      payload READ OUT OF the head node's cell and [c] is the occurrence
      counter before the pop. *)
Theorem rot_body_spec: forall hdr a ns v vs h c,
    qrep hdr (a :: ns) (v :: vs) h ->
    interp_state h_heapE (rot_body hdr) (h, c)
    ~ (log (Pop v c) ;;
       Ret (@inl unit unit tt, (rot_heap hdr a (hdf ns 0) (zof hdr ns) h, S c))).
Proof.
  intros hdr a ns v vs h c Hq.
  pose proof Hq as (Hwf & Hhd & Htl & Hch & Hdom).
  cbn in Hhd, Htl.
  destruct Hch as (Ha & Hsa & Hch).
  pose proof (qwf_neqs _ _ _ Hwf) as (Hha & Hsha & Hhsa & Hshsa & Hhshdr).
  pose proof (qrep_zof_dom _ _ _ _ _ _ Hq) as Hzdom.
  assert (Hhdrdom: h hdr <> None) by (rewrite Htl; discriminate).
  assert (Hsadom: h (S a) <> None) by (rewrite Hsa; discriminate).
  assert (Hshdrdom: h (S hdr) <> None) by (rewrite Hhd; discriminate).
  assert (Hread_hdr: upd h (S hdr) (hdf ns 0) hdr = Some (last (a :: ns) 0))
    by (rewrite upd_neq by congruence; exact Htl).
  unfold rot_body.
  rewrite (interp_rd (S hdr) h c a _ Hhd).
  rewrite (interp_rd a h c v _ Ha).
  rewrite interp_emit.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite (interp_rd (S a) h (S c) (hdf ns 0) _ Hsa).
  rewrite (interp_wr' (S hdr) h (S c) (hdf ns 0) _ Hshdrdom).
  rewrite (interp_rd hdr (upd h (S hdr) (hdf ns 0)) (S c) (last (a :: ns) 0) _ Hread_hdr).
  rewrite (zof_compute hdr a ns Hwf).
  rewrite (interp_wr' (S (zof hdr ns)) _ (S c) a _ (upd_mono _ _ _ _ Hzdom)).
  rewrite (interp_wr' (S a) _ (S c) 0 _
             (upd_mono _ _ _ _ (upd_mono _ _ _ _ Hsadom))).
  rewrite (interp_wr' hdr _ (S c) a _
             (upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _ Hhdrdom)))).
  rewrite interp_state_ret.
  reflexivity.
Qed.
