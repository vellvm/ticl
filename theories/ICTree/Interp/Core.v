From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Monad.

From TICL Require Import
  Classes
  ICTree.Core
  Events.Core
  ICTree.Events.Writer
  ICTree.Events.State
  ICTree.Equ.

From Stdlib Require Import Morphisms.

Import ICTreeNotations.
Local Open Scope ictree_scope.

Set Implicit Arguments.
Generalizable All Variables.

(** * Event interpretation *)
(** An event handler [E ~> M] defines a monad morphism
    [ictree E ~> M] for any monad [M] with a loop operator. *)
Definition interp `{Encode E} {M : Type -> Type}
  {MM : Monad M} {MI : MonadIter M} {MB: MonadBr M} (h: E ~> M) : forall X, ictree E X -> M X :=
  fun R => iter (fun t =>
                match observe t with
                | RetF r => ret (inr r)
                | BrF n k => bind (mbr n) (fun x => ret (inl (k x)))
                | GuardF t => ret (inl t)
                | VisF e k => bind (h e) (fun x => ret (inl (k x)))
                end).

Arguments interp {E H M MM MI MB} h [X].

(** Unfolding of [interp]. *)
Notation _interp h t :=
  (match observe t with
   | RetF r => Ret r
   | GuardF t => Guard (interp h%ictree t)
   | BrF n k => Br n (fun x => Guard (interp h%ictree (k x)))
   | VisF e k => h e >>= (fun x => Guard (interp h%ictree (k x)))
  end).

Local Typeclasses Transparent equ.
Lemma unfold_interp `{Encode E} `{Encode F} {R} `{f : E ~> ictree F} (t : ictree E R) :
  interp f t ≅ _interp f t.
Proof.
  unfold interp, iter, MonadIter_ictree.
  rewrite unfold_iter.
  desobs t; cbn;
    rewrite ?bind_ret_l, ?bind_map, ?bind_bind.
  - reflexivity.
  - unfold mbr, MonadBr_ictree, ICtree.branch.
    rewrite bind_br.
    apply br_equ; intros.
    rewrite ?bind_ret_l.
    reflexivity.
  - reflexivity.
  - setoid_rewrite bind_ret_l.
    reflexivity.
Qed.

(** Interpretation preserves equality [equ] *)
#[global] Instance interp_equ `{HE: Encode E} {X} {h: E ~> ictree E} :
  Proper (equ eq ==> equ eq) (@interp E _ _ _ _ _ h X).
Proof.
  unfold Proper, respectful.
  coinduction R CH.
  intros. setoid_rewrite unfold_iter.
  step in H. inv H. 
  - setoid_rewrite bind_ret_l; reflexivity.
  - setoid_rewrite bind_bind; setoid_rewrite bind_ret_l.
    upto_bind_equ. 
    constructor. intros.
    apply CH. apply H2.
  - setoid_rewrite bind_ret_l.
    constructor.
    apply CH. apply H2.
  - setoid_rewrite bind_bind.
    upto_bind_equ.
    setoid_rewrite bind_ret_l.
    constructor. 
    apply CH. apply H2.
Qed.
