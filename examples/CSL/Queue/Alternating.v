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
  Logic.Core.

From TICL Require Export CTree.Interp.CSL.Mod.
From examples Require Import CSL.Queue.Representation CSL.Queue.Operations.

Import CTree CTreeNotations TiclNotations ListNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

(** ** A turn: one complete rotation of the queue at [hdr], tagged [q].

    The tail [kt] is a parameter so that the same nine instructions serve both
    the standalone turn and the scheduler body without any
    bind-associativity reasoning. *)
Definition turnk {X} (q hdr: nat) (kt: ctree sE Bn X) : ctree sE Bn X :=
  queue_turn (semit q) hdr kt.

Definition turn (q hdr: nat) : ctree sE Bn unit := turnk q hdr (Ret tt).

(** *** The turn correspondence.

    Instantiate [Operations.queue_turn_spec] with tagged observations. The
    arbitrary tail reuses the same heap operation proof as sequential rotation. *)
Theorem turnk_spec {X}: forall q hdr a ns pv vs h allocs ctx c (kt: ctree sE Bn X),
    qrep hdr (a :: ns) (pv :: vs) h ->
    interp_state sh (turnk q hdr kt) ((h, allocs), (ctx, c))
    ~ (log (inr (stamp (q,pv) c) : CSLObs (nat * nat)) ;;
       interp_state sh kt ((rot_heap hdr a (List.hd 0 ns) (zof hdr ns) h, allocs), (ctx, S c))).
Proof.
  intros q hdr a ns pv vs h allocs ctx c kt Hq; unfold turnk.
  eapply (queue_turn_spec (semit q) (fun value index => inr (stamp (q,value) index))).
  - intros; unfold semit; apply interp_csl_emit.
  - exact Hq.
Qed.

(** ** The nonpreemptive cyclic scheduler.

    [n] is the turn counter and the loop index.  A turn is a whole rotation;
    the counter advances only after it completes.  Each completed turn ends
    with one visible [Step]: the scheduling decision of the source
    round-robin scheduler ([interp_schedule_rr_select]) is a visible step
    under [ctrees]' hidden branching, so the reference scheduler must take
    the same step for [Program.queue_pool_bisim] to be a bisimulation. *)

Definition hdrof (u v n: nat) : nat := if Nat.even n then u else v.
Definition tagof (n: nat) : nat := if Nat.even n then 1 else 2.

Definition sbody (u v: nat) (n: nat) : ctree sE Bn (nat + unit) :=
  if Nat.even n
  then turnk 1 u (Step (Ret (inl (S n))))
  else turnk 2 v (Step (Ret (inl (S n)))).

Definition sched (u v n: nat) : ctree sE Bn unit := CTree.iter (sbody u v) n.

Definition srun (u v n: nat) (s: SSig)
  : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) :=
  interp_state sh (sched u v n) s.

(** One scheduler turn, for EITHER phase, in one statement.  [hdrof]/[tagof]
    are what let the phase case analysis happen once, in the temporal proof,
    rather than twice in the language layer. *)
Theorem sbody_spec: forall u v n a ns pv vs h allocs ctx c,
    qrep (hdrof u v n) (a :: ns) (pv :: vs) h ->
    interp_state sh (sbody u v n) ((h, allocs), (ctx, c))
    ~ (log (inr (stamp ((tagof n),pv) c) : CSLObs (nat * nat)) ;;
       Step (Ret (((rot_heap (hdrof u v n) a (List.hd 0 ns) (zof (hdrof u v n) ns) h, allocs),
                   (ctx, S c)),
                  @inl nat unit (S n)))
       : ctreeW (CSLObs (nat * nat)) Bn (SSig * (nat + unit))).
Proof.
  intros u v n a ns pv vs h allocs ctx c Hq.
  unfold sbody, hdrof, tagof in *.
  destruct (Nat.even n).
  - rewrite (turnk_spec 1 u a ns pv vs h allocs ctx c
               (Step (Ret (@inl nat unit (S n))): ctree sE Bn (nat + unit)) Hq).
    rewrite !log_vis; apply sb_vis; intros _.
    rewrite interp_state_step; apply sb_step.
    rewrite sb_guard, interp_state_ret; reflexivity.
  - rewrite (turnk_spec 2 v a ns pv vs h allocs ctx c
               (Step (Ret (@inl nat unit (S n))): ctree sE Bn (nat + unit)) Hq).
    rewrite !log_vis; apply sb_vis; intros _.
    rewrite interp_state_step; apply sb_step.
    rewrite sb_guard, interp_state_ret; reflexivity.
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

(** ** Observation predicates

    Tagged observations are [inr] of [indexed (nat * nat)]: the payload pairs the
    queue tag with the (fun o => indexed_value o = value), and the occurrence index is the record's
    own field.  A plain predicate is therefore
    [fun o => indexed_value o = (q,nl)] and its freshness companion is
    [indexed_after (fun x => x = (q,nl)) kb].

    A retained observation cannot masquerade as a later one; that is
    [CTree.Logic.Trace.indexed_excludes_retained]. *)


Lemma turnk_bind {X} q hdr (kt : ctree sE Bn X) :
  turnk q hdr kt ≅ (turn q hdr;; kt).
Proof.
  unfold turn, turnk.
  rewrite queue_turn_bind.
  apply queue_turn_equ; symmetry; apply bind_ret_l.
Qed.

Lemma srun_turn u v n (s : SSig) :
  srun u v n s ~
  (interp_state sh (turn (tagof n) (hdrof u v n)) s >>=
    fun '(s', _) => Step (srun u v (S n) s')).
Proof.
  unfold srun, sched.
  rewrite interp_state_unfold_iter.
  cbv beta.
  unfold sbody, tagof, hdrof.
  destruct (Nat.even n).
  all: rewrite turnk_bind, interp_state_bind, bind_bind.
  all: apply sbisim_clo_bind_eq; [reflexivity | intros [s' x]].
  all: rewrite interp_state_step, bind_step; apply sb_step.
  all: rewrite bind_guard, sb_guard, interp_state_ret, bind_ret_l.
  all: apply sb_guard.
Qed.
