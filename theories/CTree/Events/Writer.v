(*| Useful instructions: Instrumentation |*)

From Stdlib Require Import
  Relations.

From TICL Require Import
  Logic.World
  CTree.Events.State
  CTree.Core.

From TICL Require Export Events.WriterE.

Generalizable All Variables.

(** * Instrumentation event *)
(** In program instrumentation, we leave behind a [Log] event after each semantic interpretation.
    This is useful for remembering the temporal information of the program post interpretation,
    while also being general enough to accomodate arbitrary ghost-state [W]. *)
Definition log {S B}: S -> ctree (writerE S) B unit := fun s => CTree.trigger (Log s).

Abbreviation ctreeW Φ B := (ctree (writerE Φ) B).
Abbreviation InstrM Φ B Σ := (stateT Σ (ctreeW Φ B)).

Import CTreeNotations.
Local Open Scope ctree_scope.

(** This handler makes it easier to define event instrumentation, by a semantic handler [h]
and an observation function [obs] that returns a [W] value for each event. *)
Definition h_instr {E B W Σ} (h: E ~> stateT Σ (ctree void1 B))
  (obs: forall Y (e: E Y), Y -> Σ -> option W): E ~> InstrM W B Σ :=
  fun _ e s =>
    '(σ, x) <- translate (fun _ (e: void1 _) => match e with end) (h _ e s) ;;
    match obs _ e x σ with
    | Some w => Vis (Log w) (fun 'tt => Ret (σ, x))
    | None => Ret (σ, x)
    end.

(** An instrumentation handler for [stateE S] events, leaving behind a [Log] event after each [Put] but not on [Get].
Intuitively this means that we are only interested in the changes to the state, but not accesses to the state. *)
Definition h_stateW{S B}: stateE S ~> InstrM S B S :=
  fun _ e s =>
    match e in stateE _ X return ctreeW S B (S * X) with
    | Get => Ret (s, s)
    | Put s' => log s' ;; Ret (s', tt)
    end.

(** The one shared indexing handler: every [Log a] emits exactly one indexed
    observation and increments the shared counter once.  The untouched
    auxiliary state [Sigma] is passed through unchanged, so the same handler
    serves a heap-and-counter signature and a bare counter. *)
Definition h_indexed {B : Type -> Type} {A Sigma : Type} :
  writerE A ~> stateT (Sigma * nat) (ctreeW (indexed A) B) :=
  fun _ '(Log a) '(s,c) =>
    log (stamp a c);; Ret ((s,S c), tt).

(** The canonical RAW response certificate of an emitting segment.  It is a
    handler equation, not an interpreter equation. *)
Lemma h_indexed_log {A Sigma B} (a : A) (s : Sigma) (c : nat) :
  h_indexed (B:=B) (Sigma:=Sigma) _ (Log a) (s,c)
    ≅ (log (stamp a c);; Ret ((s,S c), tt)).
Proof. reflexivity. Qed.
