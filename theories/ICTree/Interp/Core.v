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

(** Interpretation preserves equality [equ].  The handler is heterogeneous:
    events of [E] are interpreted into trees over an arbitrary [F]. *)
#[global] Instance interp_equ
    {E F : Type} {HE : Encode E} {HF : Encode F} {X}
    {h : E ~> ictree F} :
  Proper (@equ E HE X X eq ==> @equ F HF X X eq)
         (@interp E HE _ _ _ _ h X).
Proof.
  unfold Proper, respectful.
  change (forall x y : ictree E X,
             @equ E HE X X eq x y ->
             @equ F HF X X eq (interp h x) (interp h y)).
  __coinduction_equ RR IH; intros * EQ1.
  setoid_rewrite unfold_iter.
  step in EQ1; inv EQ1.
  - setoid_rewrite bind_ret_l; reflexivity.
  - setoid_rewrite bind_bind; setoid_rewrite bind_ret_l.
    upto_bind_equ.
    constructor. intros.
    apply IH. apply H1.
  - setoid_rewrite bind_ret_l.
    constructor.
    apply IH. apply H1.
  - setoid_rewrite bind_bind.
    upto_bind_equ.
    setoid_rewrite bind_ret_l.
    constructor.
    apply IH. apply H1.
Qed.

(** [interp] commutes with [bind], for a heterogeneous handler. *)
Lemma interp_bind_hetero
    {E F : Type} `{Encode E} `{Encode F} {A B}
    (h : E ~> ictree F) (t : ictree E A) (k : A -> ictree E B) :
  interp h (x <- t;; k x) ≅ (x <- interp h t;; interp h (k x)).
Proof.
  revert t.
  __coinduction_equ RR IH; intros.
  rewrite (ictree_eta t).
  rewrite unfold_bind, unfold_interp.
  destruct (observe t) eqn:Hobs; cbn.
  - rewrite unfold_interp.
    cbn.
    rewrite bind_ret_l.
    rewrite unfold_interp.
    reflexivity.
  - rewrite unfold_interp.
    cbn.
    rewrite bind_br.
    setoid_rewrite bind_guard.
    constructor; intro i.
    step; econstructor; intros.
    apply IH.
  - rewrite (@unfold_interp _ _ _ _ _ h (Guard t0)).
    cbn.
    rewrite bind_guard.
    constructor.
    apply IH.
  - rewrite unfold_interp.
    cbn.
    rewrite bind_bind.
    upto_bind_equ.
    rewrite bind_guard.
    constructor.
    apply IH.
Qed.
