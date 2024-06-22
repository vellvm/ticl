From CTree Require Import
  CTree.Core
  Logic.Ctl
  Utils.Vectors
  CTree.Equ
  CTree.SBisim
  CTree.Logic.AG
  CTree.Logic.AF
  CTree.Logic.AX
  CTree.Logic.State
  CTree.Logic.Bind
  CTree.Events.Writer
  CTree.Events.Net.Uniring.

From Coq Require Import
  Fin
  Vector
  List
  Classes.SetoidClass.

Set Implicit Arguments.

Import ListNotations CTreeNotations CtlNotations.
Local Close Scope list_scope.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ctl_scope.

Section Election.
  Context {n: nat}.
  Variant message :=
    | Candidate (u: fin' n)
    | Elected (u: fin' n).

  Notation netE := (netE message).

  Definition msg_id(m: message): fin' n :=
    match m with
    | Candidate u => u
    | Elected u => u
    end.

  Definition eqb_message(a b: message): bool :=
    match a, b with
    | Candidate a, Candidate b => Fin.eqb a b
    | Elected a, Elected b => Fin.eqb a b
    | _, _ => false
    end.

  Notation continue := (Ret (inl tt)).
  Notation stop := (Ret (inr tt)).
  
  (* Always terminates, conditional on receiving either:
     1. (Candidate candidate), where candidate = id -- I received my own [id] back 
     2. (Elected leader) -- Someone else was elected [leader]
   *)
  Definition elect(id: fin' n): ctree netE unit :=
    send (Candidate id) ;;
    (* Recv loop *)
    Ctree.iter
      (fun _ =>
         m <- recv ;;
         match m with
         | Some (Candidate candidate) =>
             match Fin_compare candidate id with (* candidate < id *)
             (* [left] neighbor proposed candidate, support her to [right]. *)
             | Gt => send (Candidate candidate) ;; continue
             (* [left] neighbor proposed a candidate, do not support her. *)
             | Lt => continue
             (* I am the leader, but only I know. Tell my [right] and return. *)
             | Eq => send (Elected id) ;; stop
             end
         | Some (Elected leader) =>
             (* I am a follower and know the [leader] *)
             send (Elected leader) ;; stop
         | None =>  stop (* Recv loop *)
         end) tt.

  Definition election_proto : ctree (writerE NetObs) void :=
    uring_sched (Vector.map (fun id => {| mbox := None; proc := elect id |}) (fin_all_v n)).

  Lemma election_fair: forall (i: fin' n),
      <( election_proto, Pure |= AF visW {fun obs => obs.(id) = i} )>.
  Proof with auto with ctl.
    intros.
    unfold election_proto, uring_sched. 
    unfold Ctree.branch.
    rewrite bind_br.
    cright.
    apply axl_br; split; [csplit; split; auto with ctl|].
    intro c. (* Nondeterministic pick *)
    rewrite bind_ret_l.
  Admitted.    
End Election.
