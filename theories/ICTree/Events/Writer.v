(*| Useful instructions: Instrumentation |*)

From Stdlib Require Import
  Relations.

From TICL Require Import
  Classes
  Logic.World
  Events.Core
  ICTree.Events.State
  ICTree.Core.

From TICL Require Export
  Events.WriterE.

From ExtLib Require Export
  Data.Monads.StateMonad.

Generalizable All Variables.

(** * Instrumentation event *)
(** In program instrumentation, we leave behind a [Log] event after each semantic interpretation.
    This is useful for remembering the temporal information of the program post interpretation,
    while also being general enough to accomodate arbitrary ghost-state [W]. *)
Definition log {S}: S -> ictree (writerE S) unit := fun s => ICtree.trigger (Log s).

Notation ictreeW Φ := (ictree (writerE Φ)).
Notation InstrM Φ Σ := (stateT Σ (ictreeW Φ)).

Import ICTreeNotations.
Local Open Scope ictree_scope.

(** This handler makes it easier to define event instrumentation, by a semantic handler [h]
and an observation function [obs] that returns a [W] value for each event. *)
Definition h_instr `{Encode E} {W Σ} (h:E ~> stateT Σ (ictree void))
  (obs: forall (e: E), encode e -> Σ -> option W): E ~> InstrM W Σ :=
  fun e => mkStateT
          (fun s =>
             '(x, σ) <- resumICtree (runStateT (h e) s) ;;
             match obs e x σ with
             | Some w => Vis (Log w) (fun 'tt => Ret (x, σ))
             | None => Ret (x, σ)
             end).

(** An instrumentation handler for [stateE S] events, leaving behind a [Log] event after each [Put] but not on [Get].
Intuitively this means that we are only interested in the changes to the state, but not accesses to the state. *)
Definition h_stateW{S}: stateE S ~> InstrM S S :=
  fun e => mkStateT (fun s =>
                    match e return ictreeW S (encode e * S) with
                    | Get => Ret (s, s)
                    | Put s' => log s' ;; Ret (tt, s')
                    end).

#[global] Instance ReSum_inlW {A B} : ReSum (writerE A) (writerE (A + B)) :=
  fun '(Log a) => Log (inl a).

#[global] Instance ReSum_inrW {A B} : ReSum (writerE B) (writerE (A + B)) :=
  fun '(Log b) => Log (inr b).

#[global] Instance ReSumRet_inlW {A B} : ReSumRet (writerE A) (writerE (A + B)) :=
  fun _ 'tt => tt.

#[global] Instance ReSumRet_inrW {A B} : ReSumRet (writerE B) (writerE (A + B)) :=
  fun _ 'tt => tt.
