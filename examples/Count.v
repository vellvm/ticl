From CTree Require Import
  CTree.Core
  Logic.Ctl
  Utils.Vectors
  Events.WriterE
  CTree.Logic.Trans
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Equ
  CTree.Events.Writer
  CTree.Events.Net.

From Coq Require Import
  Fin
  Vector
  List
  Classes.SetoidClass.

Set Implicit Arguments.

Import Ctree VectorNotations CTreeNotations CtlNotations.
Local Open Scope vector_scope.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ctl_scope.

(* We all count to find how many there we are *)
Section Count.
  Context {n: nat}.
  Notation netE := (netE nat).

  (* Runs forever and counts to infinity *)
  Definition count(id: fin' n): ctree netE void :=
    forever void
      (fun _ =>
         m <- recv ;;
         match m with
         | Some cnt => send (S cnt)
         | None => Ret tt
         end) tt.

  (* TODO: Instrumentation of [send] *)
  Definition instr(i: fin' n): nat -> option nat := Some.
  
  Definition count_sched : ctree (writerE nat) _ :=
    schedule instr (Some 0) (Vector.map count (fin_all_v n)).

  Lemma count_always: forall (max: nat),
      <( count_sched, Pure |= AG AF visW \x, x = max )>.
  Proof.
    intros.
    unfold count_sched, schedule, branch, instr.
    rewrite bind_br.
    (* NEED [agaf_br] lemma or equally general *)
  Admitted.
End Count.
