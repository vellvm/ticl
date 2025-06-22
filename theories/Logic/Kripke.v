From Stdlib Require Import
  Relations
  Program.Basics
  Classes.Morphisms.

From TICL Require Export
  Logic.World.

From TICL Require Import
  Utils.Utils
  Events.Core.

Generalizable All Variables.

(** * Ticl Kripke model *)
(** We define Ticl abstractly over a family of models [M] parametrized by an event type [E].
    The models are equipped with a transition relation [ktrans], a notion of world [World E] and a notion of done [not_done]. 
    
    The abstract model is extensible, for example if we want to define Ticl in terms of a new coinductive tree (e.g. ITrees, CTrees, etc.)
    we can simply give an instance of the Kripke class for the new coinductive tree and obtain a new Ticl logic.
*)
Class Kripke (M: forall E, Encode E -> Type -> Type) (E: Type) `{HE: Encode E} := {

    (* - [ktrans] the transition relation over [M X * W] *)
    ktrans {X}: M E HE X -> World E -> M E HE X -> World E -> Prop;

    (* - [ktrans] only if [not_done] *)
    ktrans_not_done {X}: forall (t t': M E HE X) (w w': World E),
      ktrans t w t' w' ->
      not_done w;
  }.

Declare Scope ticl_scope.
Local Open Scope ticl_scope.
Delimit Scope ticl_scope with ticl.

(** * Transition relation notation *)
Notation "| t , w | ↦ | t' , w' | " :=
  (ktrans t w t' w')
    (at level 48,
      right associativity): ticl_scope.

(** * [can_step] relation *)
(** [can_step] is the relation that says that a model [m] can step from world [w],
if there exists a model [m'] and a world [w'] such that [m] can step to [m'] from [w] to [w']. *)
Definition can_step `{Kripke M W} {X} (m: M W _ X) (w: World W): Prop :=
  exists m' w', | m,w |  ↦ | m',w' |.

Lemma can_step_not_done `{Kripke M W} {X}: forall (t: M W _ X) w,
    can_step t w ->
    not_done w.
Proof.
  intros.
  destruct H0 as (t' & w' & TR).
  now apply ktrans_not_done in TR.
Qed.
Global Hint Resolve can_step_not_done: ticl.

Ltac world_inv :=
  match goal with
  | [H: @Obs ?E ?HE ?e ?x = ?w |- _] =>
      dependent destruction H
  | [H: @Pure ?E ?HE = ?w |- _] =>
      dependent destruction H
  | [H: @Done ?E ?HE ?X ?x = ?w |- _] =>
      dependent destruction H
  | [H: @Finish ?E ?HE ?X ?e ?v ?x = ?w |- _] =>
      dependent destruction H
  | [H: ?w = @Obs ?E ?HE ?e ?x |- _] =>
      dependent destruction H
  | [H: ?w = @Pure ?E ?HE |- _] =>
      dependent destruction H
  | [H: ?w = @Done ?E ?HE ?X ?x |- _] =>
      dependent destruction H
  | [H: ?w = @Finish ?E ?HE ?X ?e ?v ?x |- _] =>
      dependent destruction H
  end.
Global Hint Extern 2 => world_inv: ticl.

Ltac ktrans_inv :=
  match goal with
  | [H: | ?t, ?w | ↦ | ?t', ?w' | |- can_step ?t ?w] =>
      exists t', w'; apply H
  | [H: | ?t, ?w | ↦ | ?t', ?w' | |- not_done ?w] =>
      apply ktrans_not_done with t t' w'; apply H
  end.
Global Hint Extern 2 => ktrans_inv: ticl.
