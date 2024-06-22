From CTree Require Import
  Utils.Vectors
  CTree.Core.

From CTree Require Export
  CTree.Core
  Events.Core
  Events.WriterE.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad.

From Equations Require Import Equations.

Import CTreeNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(*| Message passing in unidirectional ring |*)
Variant netE(T: Type): Type :=
  | Recv
  | Send (msg: T).

Arguments Recv {T}.
Arguments Send {T}.

#[global] Instance encode_netE{T}: Encode (netE T) :=
  fun e => match e with
        | Recv => option T
        | Send _ => unit
        end.

Arguments encode_netE {T} /.

Definition send {T}: T -> ctree (netE T) unit :=
  fun p => Ctree.trigger (Send p).

Definition recv {T}: ctree (netE T) (option T) :=
  Ctree.trigger (@Recv T).

Definition option_dec{A}(o: option A): {o = None} + {exists v, o = Some v} :=
  match o with
  | Some x => right (ex_intro (fun v : A => Some x = Some v) x eq_refl)
  | None => left eq_refl
  end.
                                         
(* Unidirectional ring scheduler for ctrees, based on message passing.
   1. Pick non-deterministically an [i: fin n], schedule process [i].
   2. When [i] sends a message to [j], deliver message and schedule [j] next.
   3. Repeat (2) forever.
 *)
Section UniringMsg.
  Context {n: nat} {T: Type}.

  Notation netE := (netE T).
  Record Worker := {
      mbox: option T;
      proc: ctree netE unit;
    }.

  Definition observe_worker (w: Worker): option T * ctree' netE unit :=
    (w.(mbox), observe w.(proc)).

  (* The Type of network observations *)
  Record NetObs := {
      id : fin' n;
      sent : option T;
      recd: option T;
      term: bool;
    }.

  Definition send_obs (id: fin' n) (msg: T) :=
    Log {| id := id; sent := Some msg; recd := None; term := false |}.

  Definition recv_obs (id: fin' n) (msg: T) :=
    Log {| id := id; sent := None; recd := Some msg; term := false |}.

  Definition empty_obs (id: fin' n) :=
    Log {| id := id; sent := None; recd := None; term := false |}.

  Definition term_obs (id: fin' n) :=
    Log {| id := id; sent := None; recd := None; term := true |}.

  (* A distributed system is a vector of workers *)
  Notation Sys := (vec' n Worker).
  
  Definition upd_mbox(sys: Sys)(id: fin' n)(m: option T) :=
    sys @ id := {| mbox := m; proc := proc (sys $ id) |}.

  Definition upd_proc(sys: Sys)(id: fin' n)(p: ctree netE unit) :=
    sys @ id := {| mbox := mbox (sys $ id); proc := p |}.

  Equations uring_sched_one' (id: fin' n)(sys: Sys): ctree (writerE NetObs) (fin' n * Sys) :=
    uring_sched_one' id sys with observe_worker (sys $ id) => {
        (** A non-deterministic choice, traverse it *)
        uring_sched_one' _ _ (mbox, BrF n' k) :=
          Br n' (fun i => Ret (id, upd_proc sys id (k i)));
        
        (** A guard, traverse it *)
        uring_sched_one' _ _ (mbox, GuardF t') :=
          Guard (Ret (id, upd_proc sys id t'));
        
        (** A network `send` effect, interpet it and context-switch right*)
        uring_sched_one' _ _ (mbox, VisF (Send m) k) :=
          Vis (send_obs id m)
            (fun _ => Ret (cycle id,                       
                       (upd_mbox
                          (upd_proc sys id (k tt))
                          (cycle id) (Some m))));
          
        (** Receive a message, full mailbox *)
        uring_sched_one' _ _ (Some m, VisF Recv k) :=
          Vis (recv_obs id m)
            (fun _ => Ret (id,
                       (upd_mbox
                          (upd_proc sys id (k None))
                          id None)));

        (** Receive a message, empty mailbox *)
        uring_sched_one' _ _ (None, VisF Recv k) :=
          Vis (empty_obs id) (fun _ => Ret (id, upd_proc sys id (k None)));

        (** A process returns, mark it as complete *)
        uring_sched_one' _ _ (_, RetF tt) :=
          Vis (term_obs id) (fun _ => Ret (cycle id, upd_proc sys id Ctree.stuck));
      }.

  (* Nondeterministic pick which process to start first,
     then schedule processes in a unidirectional ring *)
  Definition uring_sched (sys: Sys): ctree (writerE NetObs) void :=
    id <- Ctree.branch n;;
    Ctree.forever void
      (fun '(id, sys) =>  uring_sched_one' id sys) (id, sys).

End UniringMsg.
