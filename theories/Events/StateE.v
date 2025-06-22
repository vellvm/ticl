From TICL Require Import
  Utils.Utils
  Classes
  Events.Core.

From ExtLib Require Import
  Structures.Monads
  Structures.MonadState
  Data.Monads.StateMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.
Generalizable All Variables.

(** * State events over state [S] *)
Section State.
  (** State type [S] *)
  Variable (S : Type).
  (** The state event type is [stateE] *)
  Variant stateE : Type :=
    | Get : stateE
    | Put : S -> stateE.

  (** The state event has return type given by [Encode stateE] *)
  #[global] Instance encode_stateE: Encode stateE :=
    fun e => match e with
          | Get => S
          | Put _ => unit
          end.

  (** The state handler interprets events into a state monad [state S] *)
  Definition h_stateE: stateE ~> state S :=
    fun e => mkState
            (fun s =>
               match e return (encode e * S) with
               | Get => (s, s)
               | Put s' => (tt, s')
               end).

   
End State.

Arguments Get {S}.
Arguments Put {S}.

#[global] Existing Instance Monad_stateT.

(** ** Iteration monad for state events *)
#[global] Instance MonadIter_stateT {M S} {MM : Monad M} {AM : MonadIter M}
  : MonadIter (stateT S M) :=
  fun _ _ step i => mkStateT (fun s =>
    iter (fun is =>
      let i := fst is in
      let s := snd is in
      is' <- runStateT (step i) s ;;
      ret match fst is' with
          | inl i' => inl (i', snd is')
          | inr r => inr (r, snd is')
        end) (i, s)).

(** ** Monad branching for state events *)
#[global] Instance MonadBr_stateT {S M} {MM : Monad M} {AM : MonadBr M}: MonadBr (stateT S M) :=
  fun n => mkStateT (fun s => f <- mbr n;; ret (f,s)).