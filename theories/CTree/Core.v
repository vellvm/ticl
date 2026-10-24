(** * TICL-side facade over the [ctrees] library.

    TICL's model is [ctree E B X] from the vendored [ctrees] library (git submodule
    [ctrees/]).  This module re-exports everything a TICL development needs
    (the datatype and its combinators, [equ]/[sbisim]/[ssim] and the LTS
    [trans], the [fold]/[interp]/[interp_state] interpreters, ITree's
    subevent machinery) and adds the few TICL-only notations. *)
#[global] Set Warnings "-intuition-auto-with-star".
(** [ctrees] is universe polymorphic throughout; every TICL definition over
    [ctree] must be too, otherwise monomorphic universe instances fail to
    unify with the polymorphic lemmas (e.g. [sbisim_bind_eq]). *)
#[global] Set Universe Polymorphism.
(** Without this, a definition of type [ctree E B nat] gets its value universe
    minimised to [Set], which then cannot unify with the (monomorphic) [Kripke]
    class universe when the tree is used in a TICL formula. *)
#[global] Unset Universe Minimization ToSet.
From Stdlib Require Import Fin.

From ExtLib Require Import
  Structures.Functor
  Structures.Monad.

From CTree Require Export
  CTree
  Eq
  Interp.Fold
  Interp.FoldCTree
  Interp.FoldStateT.

From ITree Require Export
  Basics.Basics
  Core.Subevent
  Indexed.Sum
  Indexed.Function.

From TICL Require Export Utils.Utils.

(** ITree's state transformer [stateT S M A := S -> M (S * A)], used by the ctrees interpreters. *)
Export Basics.Monads.
Export CTreeNotations EquNotations SBisimNotations SSimNotations.

Generalizable All Variables.

(** ctrees' [stateE S]: make [S] implicit on [Get] as it is on [Put]. *)
Arguments Get {S}.

(** [get]/[put] triggers for [stateE S]. These shadow ctrees' definitions of
    the same name (identical unfolding) but leave the result universe of the
    tree free: ctrees' [put] pins it to [Set], which rejects the dependent
    handler matches [fun _ e => match e in heapE X return ctree E B X with ...]
    whose index universe lies above [Set]. *)
Definition put {S E B} `{stateE S -< E} (s: S) : ctree E B unit :=
  CTree.trigger (subevent _ (Put s)).
Definition get {S E B} `{stateE S -< E} : ctree E B S :=
  CTree.trigger (subevent _ (@Get S)).

Abbreviation fin' n := (Fin.t (S n)).

Create HintDb ctree.

Local Open Scope ctree_scope.

(** TICL-only loop notations, kept from the previous TICL core. *)
Notation "'continue'" :=
  (Ret (inl tt))
    (at level 60): ctree_scope.

Notation "'break'" :=
  (Ret (inr tt))
    (at level 60): ctree_scope.

Notation "'for' i 'to' '∞' b" :=
  (CTree.forever
     (fun (x: nat) =>
        b%ctree x ;;
        Ret (S x)) i%nat) (at level 64, right associativity): ctree_scope.

Notation "'loop' b" :=
  (@CTree.iter _ _ unit unit
     (fun 'tt => b) tt) (at level 64): ctree_scope.

Ltac desobs t :=
  let H := fresh "Heqt" in destruct (observe t) eqn:H.

(** Case analysis on an event sum: handler for [E1 +' E2] from handlers for each. *)
Definition h_sum {E1 E2: Type -> Type} {M: Type -> Type}
  (h1: E1 ~> M) (h2: E2 ~> M): E1 +' E2 ~> M :=
  fun _ e => match e with
          | inl1 e => h1 _ e
          | inr1 e => h2 _ e
          end.
