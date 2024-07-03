(*| Useful instructions: Instrumentation |*)

From Coq Require Import
  Relations.

From CTree Require Import
  Classes
  Logic.World
  CTree.Core.

From CTree Require Export
  Events.WriterE.

Definition log {S}: S -> ctree (writerE S) unit := fun s => Ctree.trigger (Log s).

Notation ctreeW Φ := (ctree (writerE Φ)).

#[global] Instance ReSum_inlW {A B} : ReSum (writerE A) (writerE (A + B)) :=
  fun '(Log a) => Log (inl a).

#[global] Instance ReSum_inrW {A B} : ReSum (writerE B) (writerE (A + B)) :=
  fun '(Log b) => Log (inr b).

#[global] Instance ReSumRet_inlW {A B} : ReSumRet (writerE A) (writerE (A + B)) :=
  fun _ 'tt => tt.

#[global] Instance ReSumRet_inrW {A B} : ReSumRet (writerE B) (writerE (A + B)) :=
  fun _ 'tt => tt.
