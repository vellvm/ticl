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
