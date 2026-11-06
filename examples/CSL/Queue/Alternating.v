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
  CTree.Interp.Yield.Policy
  CTree.Interp.Yield.Fair
  CTree.Events.State
  CTree.Events.Writer
  CTree.Events.Yield
  Utils.Vectors
  CTree.Trace
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
    ~ emit_list (queue_turn_logs (CSLEmit (stamp (q,pv) c)) hdr a
        (List.hd 0 ns) (last (a :: ns) 0) (h,allocs))
       (interp_state sh kt ((rot_heap hdr a (List.hd 0 ns) (zof hdr ns) h, allocs), (ctx, S c))).
Proof.
  intros q hdr a ns pv vs h allocs ctx c kt Hq; unfold turnk.
  eapply (queue_turn_spec (semit q) (fun value index => CSLEmit (stamp (q,value) index))).
  - intros; unfold semit; apply interp_csl_emit.
  - exact Hq.
Qed.

(** ** The nonpreemptive cyclic scheduler.

    [n] is the turn counter and the loop index.  A turn is a whole rotation;
    the counter advances only after it completes.  Each completed turn ends
    with one logged scheduling decision: the source round-robin scheduler
    ([interp_schedule_rr_select]) logs the slot it picks next.  The reference
    scheduler triggers the same [Scheduled] event in [sE +' schedE] for
    [Program.queue_pool_bisim] to be a bisimulation. *)

Definition hdrof (u v n: nat) : nat := if Nat.even n then u else v.
Definition tagof (n: nat) : nat := if Nat.even n then 1 else 2.

(** Queue 2 occupies slot [0], and queue 1 occupies slot [1]. *)
Definition queue_slot (n : nat) : Fin.t 2 :=
  if Nat.even n then Fin.FS Fin.F1 else Fin.F1.

Definition sbody (u v: nat) (n: nat) : ctree (sE +' schedE) Bn (nat + unit) :=
  translate inl1 (turn (tagof n) (hdrof u v n)) ;;
  CTree.trigger (inr1 (Scheduled (slot_index (queue_slot (S n)))) : (sE +' schedE) unit) ;;
  Ret (inl (S n)).

Definition sched (u v n: nat) : ctree (sE +' schedE) Bn unit := CTree.iter (sbody u v) n.

Definition srun (u v n: nat) (s: SSig)
  : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) :=
  interp_state (policy_handler sh) (sched u v n) s.

(** One scheduler turn, for EITHER phase, in one statement.  [hdrof]/[tagof]
    are what let the phase case analysis happen once, in the temporal proof,
    rather than twice in the language layer. *)
Theorem sbody_spec: forall u v n a ns pv vs h allocs ctx c,
    qrep (hdrof u v n) (a :: ns) (pv :: vs) h ->
    interp_state (policy_handler sh) (sbody u v n) ((h, allocs), (ctx, c))
    ~ (emit_list (List.map inl
         (queue_turn_logs (CSLEmit (stamp (tagof n,pv) c))
           (hdrof u v n) a (List.hd 0 ns) (last (a :: ns) 0) (h,allocs)))
       (log (inr (slot_index (queue_slot (S n)))) ;;
        Ret (((rot_heap (hdrof u v n) a (List.hd 0 ns) (zof (hdrof u v n) ns) h, allocs),
              (ctx, S c)), @inl nat unit (S n)))
       : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * (nat + unit))).
Proof.
  intros u v n a ns pv vs h allocs ctx c Hq.
  unfold sbody.
  rewrite interp_state_bind, interp_state_policy_translate.
  unfold turn.
  rewrite (turnk_spec (tagof n) (hdrof u v n) a ns pv vs h allocs ctx c (Ret tt) Hq).
  rewrite translate_emit_list, emit_list_bind; apply emit_list_sbisim.
  rewrite interp_state_ret, translate_ret, bind_ret_l.
  rewrite interp_state_bind, interp_state_trigger_bind.
  cbn [policy_handler h_sum sched_handler].
  change (Monad.bind ?a ?b) with (CTree.bind a b); rewrite bind_vis.
  rewrite !log_vis; apply sb_vis; intros _.
  rewrite bind_ret_l, interp_state_ret; reflexivity.
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

    Tagged observations are [CSLEmit] of [indexed (nat * nat)]: the payload pairs the
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
  (translate relabel_log (interp_state sh (turn (tagof n) (hdrof u v n)) s) >>=
    fun '(s', _) =>
      Vis (Log (inr (slot_index (queue_slot (S n))))) (fun _ => srun u v (S n) s')).
Proof.
  unfold srun, sched.
  rewrite interp_state_unfold_iter.
  cbv beta.
  unfold sbody.
  rewrite interp_state_bind, interp_state_policy_translate, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros [s' x]].
  rewrite interp_state_bind, interp_state_trigger_bind.
  cbn [policy_handler h_sum sched_handler].
  change (Monad.bind ?a ?b) with (CTree.bind a b); rewrite !bind_bind, bind_vis.
  apply sb_vis; intros _.
  rewrite !bind_ret_l; cbn [fst].
  rewrite interp_state_ret, bind_ret_l.
  apply sb_guard.
Qed.
