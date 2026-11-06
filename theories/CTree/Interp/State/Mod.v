From ExtLib Require Export
  Structures.MonadState
  Structures.Monad.

From TICL Require Import
  CTree.Core
  CTree.Events.Writer
  CTree.Events.State.

From Coinduction Require Import all.
From Stdlib Require Import Morphisms.

Import CTreeNotations.
Local Open Scope ctree_scope.

Set Implicit Arguments.
Generalizable All Variables.

(** * Interpreting state events *)
(** [interp_state h t s : ctree F B (S * X)] is the [ctrees] state interpreter
    ([CTree.Interp.FoldStateT]); its structural equations ([unfold_interp_state],
    [interp_state_ret/stuck/guard/step/vis/br/trigger/bind], [equ_eq_interp_state])
    come from there. Note the pair order: state first, [Ret (s, x)].

    This module adds the TICL-specific equations: the instrumented state handler
    [h_stateW], iteration under [interp_state], and indexed emissions. *)

(** Interpret [stateE Σ] events into the writer monad with ghost-state [Σ].
    The explicit universes keep the event codomain universe [v] separate from
    the state universe [u]: minimization would otherwise collapse them, and
    [get]/[put] (typed through ITree's monomorphic [-<]) could not be passed. *)
Definition instr_stateE@{u v +|+} {Σ : Type@{u} } {B : Type -> Type} {X : Type}
  (t: @ctree@{u _ v _ _ _} (stateE Σ) B X) (σ: Σ): ctreeW Σ B (Σ * X) :=
  interp_state (h_stateW (B:=B)) t σ.

Section InterpStateTicl.
  Context {E F B: Type -> Type} {W: Type} (h: E ~> stateT W (ctree F B)).

  (** A trigger's administrative guard disappears under strong bisimulation. *)
  Lemma interp_state_trigger_bind {X Y} (e : E Y)
    (k : (W * Y)%type -> ctree F B X) (s : W) :
    (interp_state h (CTree.trigger e : ctree E B Y) s >>= k) ~
    (h e s >>= k).
  Proof.
    rewrite interp_state_trigger.
    change (Monad.bind ?a ?b) with (CTree.bind a b).
    rewrite bind_bind.
    apply sbisim_clo_bind_eq; [reflexivity | intro result].
    rewrite bind_guard, sb_guard, bind_ret_l; reflexivity.
  Qed.

  (** [interp_state] applied on iteration, unfolds the iteration structure and commutes the interpretation inside the loop body. *)
  Lemma interp_state_unfold_iter {I R}
    (k : I -> ctree E B (I + R)) (i: I) (s: W) :
    interp_state h (CTree.iter k i) s ≅ interp_state h (k i) s >>= fun '(s, x) =>
        match x with
        | inl l => Guard (interp_state h (CTree.iter k l) s)
        | inr r => Ret (s, r)
        end.
  Proof.
    rewrite unfold_iter, interp_state_bind.
    upto_bind_eq; intros [s' [l | r]]; cbn.
    - rewrite interp_state_guard; reflexivity.
    - rewrite interp_state_ret; reflexivity.
  Qed.

  (** A visible branch interprets to a visible branch, up to administrative guards. *)
  Lemma interp_state_brS {X Y} (c: B Y) (k: Y -> ctree E B X) (s: W) :
    interp_state h (BrS c k) s ~ BrS c (fun y => interp_state h (k y) s).
  Proof.
    rewrite interp_state_br.
    change (Monad.bind (mbr c) ?f) with (CTree.bind (branch c : ctree F B Y) f).
    rewrite bind_branch.
    apply sbisim_br_id; intros y.
    rewrite sb_guard, interp_state_step.
    apply sbisim_step; auto; apply sb_guard.
  Qed.

End InterpStateTicl.

(** [interp_state] applied on get, returns the state. *)
Lemma interp_state_get {S B}: forall (s: S),
  interp_state (h_stateW (B:=B)) (get : ctree (stateE S) B S) s ~ (Ret (s, s) : ctreeW S B (S * S)).
Proof.
  intros.
  unfold get; rewrite interp_state_trigger; cbn.
  rewrite bind_ret_l, sb_guard.
  reflexivity.
Qed.

(** [interp_state] applied on put, interprets the event and the state leaving behind a log event. *)
Lemma interp_state_put {S B}: forall (s s': S),
  interp_state (h_stateW (B:=B)) (put s' : ctree (stateE S) B unit) s ~ (log s' ;; Ret (s', tt) : ctreeW S B (S * unit)).
Proof.
  intros.
  unfold put; rewrite interp_state_trigger; cbn.
  rewrite bind_bind.
  unfold log, CTree.trigger; rewrite ?bind_vis.
  apply sbisim_vis_id; intros []; split; auto.
  rewrite ?bind_ret_l, sb_guard.
  reflexivity.
Qed.

(** [instr_state] applied on iteration, unfolds the iteration structure and interprets the loop body. *)
Lemma instr_state_unfold_iter{S B I R}
  (k : I -> ctree (stateE S) B (I + R)) (i: I) (s: S) :
  instr_stateE (CTree.iter k i) s ≅ instr_stateE (k i) s >>= fun '(s, x) =>
      match x with
      | inl l => Guard (instr_stateE (CTree.iter k l) s)
      | inr r => Ret (s, r)
      end.
Proof.
  unfold instr_stateE.
  apply interp_state_unfold_iter.
Qed.

(** * Interpreting one indexed emission.

    [h_indexed] leaves exactly one observation and advances the shared
    occurrence counter once; the untouched auxiliary state and the other
    handler are arbitrary.  This is the interpretation-level companion of the
    raw equation [h_indexed_log]. *)
Lemma interp_indexed_emit {A Sigma E B X}
  (other : E ~> stateT (Sigma * nat) (ctreeW (indexed A) B))
  (a : A) (s : Sigma) (c : nat)
  (k : unit -> ctree (E +' writerE A) B X) :
  interp_state (h_sum other h_indexed)
    ((CTree.trigger (inr1 (Log a)) : ctree (E +' writerE A) B unit) >>= k) (s,c) ~
  (log (stamp a c);; interp_state (h_sum other h_indexed) (k tt) (s,S c)).
Proof.
  rewrite interp_state_bind, interp_state_trigger; cbn.
  rewrite ?bind_bind.
  unfold log, CTree.trigger; rewrite ?bind_vis.
  apply sbisim_vis_id; intros []; split; auto.
  rewrite ?bind_ret_l, bind_guard, sb_guard, bind_ret_l; cbn.
  reflexivity.
Qed.
