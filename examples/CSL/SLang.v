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

From TICL Require Export Lang.CSL.Heap.
From examples Require Import CSL.HeapQ.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.

(** ** A turn: one complete rotation of the queue at [hdr], tagged [q].

    The tail [kt] is a parameter so that the same nine instructions serve both
    the standalone turn and the scheduler body without any
    bind-associativity reasoning. *)
Definition turnk {X} (q hdr: nat) (kt: ictree sE X) : ictree sE X :=
  a  <- srd (S hdr) ;;
  v  <- srd a ;;
  _  <- semit q v ;;
  n  <- srd (S a) ;;
  _  <- swr (S hdr) n ;;
  z0 <- srd hdr ;;
  _  <- swr (S (if Nat.eqb n 0 then hdr else z0)) a ;;
  _  <- swr (S a) 0 ;;
  _  <- swr hdr a ;;
  kt.

Definition turn (q hdr: nat) : ictree sE unit := turnk q hdr (Ret tt).

(** *** The turn correspondence.

    Same three-in-one content as the frozen [QLang.rot_body_spec]: hidden
    segment termination, operation correctness ([HeapQ.rot_heap_spec]) and the
    observation, now queue-tagged.  The proof script is the frozen one with
    the final [interp_state_ret] dropped, because the tail is a parameter. *)
Theorem turnk_spec {X}: forall q hdr a ns pv vs h c (kt: ictree sE X),
    qrep hdr (a :: ns) (pv :: vs) h ->
    interp_state sh (turnk q hdr kt) (h, c)
    ~ (log (SPop q pv c) ;;
       interp_state sh kt (rot_heap hdr a (hdf ns 0) (zof hdr ns) h, S c)).
Proof.
  intros q hdr a ns pv vs h c kt Hq.
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
  unfold turnk.
  rewrite (sinterp_rd (S hdr) h c a _ Hhd).
  rewrite (sinterp_rd a h c pv _ Ha).
  rewrite sinterp_emit.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite (sinterp_rd (S a) h (S c) (hdf ns 0) _ Hsa).
  rewrite (sinterp_wr' (S hdr) h (S c) (hdf ns 0) _ Hshdrdom).
  rewrite (sinterp_rd hdr (upd h (S hdr) (hdf ns 0)) (S c) (last (a :: ns) 0) _
             Hread_hdr).
  rewrite (zof_compute hdr a ns Hwf).
  rewrite (sinterp_wr' (S (zof hdr ns)) _ (S c) a _ (upd_mono _ _ _ _ Hzdom)).
  rewrite (sinterp_wr' (S a) _ (S c) 0 _
             (upd_mono _ _ _ _ (upd_mono _ _ _ _ Hsadom))).
  rewrite (sinterp_wr' hdr _ (S c) a _
             (upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _ Hhdrdom)))).
  reflexivity.
Qed.

(** ** The nonpreemptive cyclic scheduler.

    [n] is the turn counter and the loop index.  A turn is a whole rotation;
    the counter advances only after it completes. *)

Definition hdrof (u v n: nat) : nat := if Nat.even n then u else v.
Definition tagof (n: nat) : nat := if Nat.even n then 1 else 2.

Definition sbody (u v: nat) (n: nat) : ictree sE (nat + unit) :=
  if Nat.even n
  then turnk 1 u (Ret (inl (S n)))
  else turnk 2 v (Ret (inl (S n))).

Definition sched (u v n: nat) : ictree sE unit := ICtree.iter (sbody u v) n.

Definition srun (u v n: nat) (h: Heap) (c: nat) : ictreeW SObs (unit * SSig) :=
  interp_state sh (sched u v n) (h, c).

(** One scheduler turn, for EITHER phase, in one statement.  [hdrof]/[tagof]
    are what let the phase case analysis happen once, in the temporal proof,
    rather than twice in the language layer. *)
Theorem sbody_spec: forall u v n a ns pv vs h c,
    qrep (hdrof u v n) (a :: ns) (pv :: vs) h ->
    interp_state sh (sbody u v n) (h, c)
    ~ (log (SPop (tagof n) pv c) ;;
       Ret (@inl nat unit (S n),
            (rot_heap (hdrof u v n) a (hdf ns 0) (zof (hdrof u v n) ns) h, S c))).
Proof.
  intros u v n a ns pv vs h c Hq.
  unfold sbody, hdrof, tagof in *.
  destruct (Nat.even n).
  - rewrite (turnk_spec 1 u a ns pv vs h c
               (Ret (@inl nat unit (S n)): ictree sE (nat + unit)) Hq).
    apply sbisim_clo_bind_eq; [reflexivity | intros []].
    rewrite interp_state_ret; reflexivity.
  - rewrite (turnk_spec 2 v a ns pv vs h c
               (Ret (@inl nat unit (S n)): ictree sE (nat + unit)) Hq).
    apply sbisim_clo_bind_eq; [reflexivity | intros []].
    rewrite interp_state_ret; reflexivity.
Qed.

(** The parity flip: one turn of the scheduler changes whose turn it is.
    This is the entire scheduling discipline, and the composition proof uses
    exactly this. *)
Lemma even_flip: forall n, Nat.even (S n) = negb (Nat.even n).
Proof.
  intro n; rewrite Nat.even_succ, <- Nat.negb_even; reflexivity.
Qed.

Lemma hdrof_even: forall u v n, Nat.even n = true -> hdrof u v n = u.
Proof. intros u v n H; unfold hdrof; now rewrite H. Qed.

Lemma hdrof_odd: forall u v n, Nat.even n = false -> hdrof u v n = v.
Proof. intros u v n H; unfold hdrof; now rewrite H. Qed.

Lemma tagof_even: forall n, Nat.even n = true -> tagof n = 1.
Proof. intros n H; unfold tagof; now rewrite H. Qed.

Lemma tagof_odd: forall n, Nat.even n = false -> tagof n = 2.
Proof. intros n H; unfold tagof; now rewrite H. Qed.

(** ** Observation predicates *)

Definition spopped (q nl: nat) : SObs -> Prop :=
  fun o => stag o = q /\ sval o = nl.

Definition spopped_after (q nl kb: nat) : SObs -> Prop :=
  fun o => stag o = q /\ sval o = nl /\ Nat.le kb (sidx o).

(** A retained observation cannot masquerade as a later one: the frozen
    freshness argument, restated at the tagged alphabet. *)
Lemma sfresh_excludes_retained {X}: forall (t: ictreeW SObs X) q nl p pv j,
    ~ <( t, {Obs (Log (SPop p pv j)) tt} |= visW {spopped_after q nl (S j)} )>.
Proof.
  intros t q nl p pv j H.
  apply ticll_vis in H.
  inversion H as [e0 v0 Hphi Heq]; subst.
  destruct v0; destruct Hphi as (_ & _ & Hle); cbn in Hle; lia.
Qed.


Lemma turnk_bind {X} q hdr (kt : ictree sE X) :
  turnk q hdr kt ≅ (turn q hdr;; kt).
Proof.
  unfold turn, turnk.
  do 9 (rewrite bind_bind; apply equ_clo_bind_eq; intro).
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma srun_turn u v n h c :
  srun u v n h c ~
  (interp_state sh (turn (tagof n) (hdrof u v n)) (h,c) >>=
    fun '(_, (h',c')) => srun u v (S n) h' c').
Proof.
  unfold srun, sched.
  rewrite interp_state_unfold_iter.
  cbv beta.
  unfold sbody, tagof, hdrof.
  destruct (Nat.even n).
  all: rewrite turnk_bind, interp_state_bind, bind_bind.
  all: apply sbisim_clo_bind_eq; [reflexivity | intros [x [h' c']]].
  all: rewrite interp_state_ret, bind_ret_l.
  all: apply sb_guard.
Qed.
