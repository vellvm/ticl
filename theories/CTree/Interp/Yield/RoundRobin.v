From Stdlib Require Import Fin Vector.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Events.Writer
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.Policy
  CTree.Interp.State.Mod
  Utils.Vectors.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** Round robin is the [rr_scheduler] instance of the event-only policy
    runner: [interp_schedule_rr] abbreviates [interp_schedule_fair
    rr_scheduler], so every node equation is the generic
    [interp_schedule_fair_*] lemma of [Policy].  Only selection is
    RR-specific: a single alternative, logged as
    [Log (inr (slot_index (rr_pick n m)))], with no extra visible step. *)

Abbreviation interp_schedule_rr := (interp_schedule_fair rr_scheduler).

Section RoundRobinInterpretation.
  Context {E : Type -> Type} {W Σ : Type} (handler : E ~> stateT Σ (ctreeW W Bn)).

  (** The scheduling point: one logged pick, then the focused pool. *)
  Lemma interp_schedule_rr_select_exact n (ts : pool E Bn (S n)) m σ :
    interp_schedule_rr handler (S n) ts None m σ ≅
    Vis (Log (inr (slot_index (rr_pick n m))))
      (fun _ => Guard (interp_schedule_rr handler (S n) ts (Some (rr_pick n m)) (S m) σ)).
  Proof.
    unfold interp_schedule_fair at 1.
    rewrite (schedule_with_no_focus_nonempty rr_scheduler n ts m).
    cbn [sched_arity sched_pick rr_scheduler br_alts fst snd].
    rewrite interp_state_vis; cbn [policy_handler h_sum sched_handler].
    change (Monad.bind ?a ?b) with (CTree.bind a b); rewrite bind_vis.
    apply vis_equ_node; intros _.
    rewrite bind_ret_l; cbn [fst snd]; reflexivity.
  Qed.

  (** The scheduling point: the round-robin pick is one logged event. *)
  Lemma interp_schedule_rr_select n (ts : pool E Bn (S n)) m σ :
    interp_schedule_rr handler (S n) ts None m σ ~
    Vis (Log (inr (slot_index (rr_pick n m))))
      (fun _ => interp_schedule_rr handler (S n) ts (Some (rr_pick n m)) (S m) σ).
  Proof.
    rewrite interp_schedule_rr_select_exact.
    apply sb_vis; intros _; rewrite sb_guard; reflexivity.
  Qed.
End RoundRobinInterpretation.
