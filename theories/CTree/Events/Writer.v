(*| Useful instructions: Instrumentation |*)

From Coq Require Import
  Relations.

From CTree Require Import
  Classes
  Logic.World
  Events.Core
  CTree.Events.State
  CTree.Core.

From CTree Require Export
  Events.WriterE.

From ExtLib Require Export
  Data.Monads.StateMonad.

Generalizable All Variables.

Definition log {S}: S -> ctree (writerE S) unit := fun s => Ctree.trigger (Log s).

Notation ctreeW Φ := (ctree (writerE Φ)).
Notation InstrM Φ Σ := (stateT Σ (ctreeW Φ)).

Import CTreeNotations.
Local Open Scope ctree_scope.

Definition h_instr `{Encode E} {W Σ} (h:E ~> stateT Σ (ctree void))
  (obs: forall (e: E), encode e -> Σ -> option W): E ~> InstrM W Σ :=
  fun e => mkStateT
          (fun s =>
             '(x, σ) <- resumCtree (runStateT (h e) s) ;;
             match obs e x σ with
             | Some w => Vis (Log w) (fun 'tt => Ret (x, σ))
             | None => Ret (x, σ)
             end).

(*| Only log on changes |*)
Definition h_stateW{S}: stateE S ~> InstrM S S :=
  fun e => mkStateT (fun s =>
                    match e return ctreeW S (encode e * S) with
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
