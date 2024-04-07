From CTree Require Import
  Utils.Vectors
  CTree.Core.

From CTree Require Export
  CTree.Core
  Events.Core
  Events.WriterE.

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
                                         
(* Round-robbin scheduler for ctrees, based on message passing.
   1. Pick non-deterministically an [i: fin n], schedule process [i].
   2. When [i] sends a message to [j], deliver message and schedule [j] next.
   3. Repeat (2).
 *)


(* n: Number of processes
     T: Message payload type
     X: Return type of processes
     W: Observation domain *)
Section ScheduleMsg.
  Context {n: nat} {T X W: Type} (fobs: fin' n -> T -> option W).
  Notation logE := (writerE W).

  Record System := {
      id: fin' n;
      mail: option T;
      processes: vec' n (ctree (netE T) X);
      complete: vec' n (option X)
    }.

  Equations schedule_one' (sys: System): ctree logE (System + vec' n X) :=            
    schedule_one' sys with observe (sys.(processes) $ sys.(id)) => {
        (** A non-deterministic choice, traverse it *)
        schedule_one' _ (BrF n' k) :=
          Br n' (fun i => Ret (inl
                              {|
                                id := sys.(id);
                                mail := sys.(mail);
                                processes := sys.(processes) @ sys.(id) := k i;
                                complete := sys.(complete)
                              |}));
        
        (** A guard, traverse it *)
        schedule_one' _ (GuardF t') :=
          Guard (Ret (inl
                        {|
                          id := sys.(id);
                          mail := sys.(mail);
                          processes := sys.(processes) @ sys.(id) := t';
                          complete := sys.(complete)
                        |}));

        
        (** A network `send` effect, interpet it and context-switch right*)
        schedule_one' _ (VisF (Send m) k) with (fobs sys.(id) m) => {
          
          (** Instrument with [obs] *)
          schedule_one' _ _ (Some obs) := 
            Vis (Log obs) (fun _ =>
                             Ret (inl
                                    {|
                                      id := cycle sys.(id);
                                      mail := Some m;
                                      processes := sys.(processes) @ sys.(id) := k tt;
                                      complete := sys.(complete)
                                    |}));
          
          (** No instrumentation *)
          schedule_one' _ _ None :=
            Ret (inl
                   {|
                     id := cycle sys.(id);
                     mail := Some m;
                     processes := sys.(processes) @ sys.(id) := k tt;
                     complete := sys.(complete)
                   |});
        };
        
        (** Receive a message, empty mailbox *)
        schedule_one' _ (VisF Recv k) :=
          Ret (inl
                 {|
                   id := sys.(id);
                   mail := None;
                   processes := sys.(processes) @ sys.(id) := k sys.(mail);
                   complete := sys.(complete)
                 |});

        (** A process returns, mark it as complete *)
        schedule_one' _ (RetF x) :=
          let complete' := sys.(complete) @ sys.(id) := Some x in            
          match seq_opt complete' with
          | None =>
              (** Pick any [i] not complete and switch to it. *)
              i <- Ctree.when (fun r => option_dec (complete' $ r)) ;; 
              Ret (inl
                     {|
                       id := i;
                       mail := None;
                       processes := sys.(processes) @ sys.(id) := Ctree.stuck;
                       complete := complete'
                     |})
          | Some v =>
              (** All processes [complete] *)
              Ret (inr v)
          end
      }.

  (* Nondeterministic pick which process to start first *)
  Definition schedule (mail: option T) (prs: vec' n (ctree (netE T) X)): ctree logE (vec' n X) :=
    r <- Ctree.branch n;;
    Ctree.iter schedule_one'
               {|
                 id := r;
                 mail := mail;
                 processes := prs;
                 complete := vector_repeat n None;
               |}.

End ScheduleMsg.
