From Stdlib Require Import Fin.
From TICL Require Import ICTree.Core Events.Core Lang.Yield.Events Lang.Yield.Vec.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

Section Scheduler.
  Context {E : Type} `{Encode E}.

  (** Cooperative scheduler for a finite pool.

      [None] focus means the scheduler chooses a runnable thread after emitting
      a scheduling [Yield].  [Some i] observes one step of thread [i], removing
      finished threads, clearing focus on source yields, and turning source forks
      into scheduler-visible [Spawn] events. *)
  CoFixpoint schedule (n : nat) (v : pool E n) (focus : option (Fin.t n)) : completed E :=
    match focus with
    | None =>
        match n return pool E n -> completed E with
        | 0 => fun _ => Ret tt
        | S n' => fun v => Vis (inl Yield) (fun _ => Br n' (fun i => schedule (S n') v (Some i)))
        end v
    | Some i =>
        match n return pool E n -> Fin.t n -> completed E with
        | 0 => fun _ i => match i with end
        | S n' => fun v i =>
            match observe (v i) with
            | RetF _ => Guard (schedule n' (remove_pool v i) None)
            | BrF b k => Br b (fun j => schedule (S n') (replace_pool v i (k j)) (Some i))
            | GuardF t => Guard (schedule (S n') (replace_pool v i t) (Some i))
            | VisF e k =>
                match e as e0 return (encode e0 -> thread E) -> completed E with
                | inl Yield => fun k => Guard (schedule (S n') (replace_pool v i (k tt)) None)
                | inr (inl Fork) => fun k =>
                    @go (yieldE + (spawnE + E)) _ unit
                      (VisF ((inr (inl Spawn)) : yieldE + (spawnE + E))
                         (fun _ => schedule (S (S n'))
                                     (cons_pool (k true) (replace_pool v i (k false)))
                                     (Some (FS i))))
                | inr (inr e') => fun k =>
                    @go (yieldE + (spawnE + E)) _ unit
                      (VisF ((inr (inr e')) : yieldE + (spawnE + E))
                         (fun x => schedule (S n') (replace_pool v i (k x)) (Some i)))
                end k
            end
        end v i
    end.
End Scheduler.
