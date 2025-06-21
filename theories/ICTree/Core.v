#[global] Set Warnings "-intuition-auto-with-star".
From Stdlib Require Import
     Fin.

From ExtLib Require Import
  Structures.Functor
  Structures.Applicative
  Structures.Monad.

From Coinduction Require Import
     coinduction.

From TICL Require Export
  Classes
  Events.Core.

Generalizable All Variables.

Notation fin' n := (Fin.t (S n)).

Create HintDb ictree.

Section ICtree.
  Context {E: Type} `{Encode E} {X: Type}.
  Variant ictreeF(ictree: Type): Type :=
    | RetF (x: X)
    | BrF {n} (k: fin' n -> ictree)
    | GuardF (t: ictree)
    | VisF (e: E)(k: encode e -> ictree).

  #[projections(primitive)] CoInductive ictree: Type :=
    go { _observe: ictreeF ictree }.
  
End ICtree.

Declare Scope ictree_scope.
Bind Scope ictree_scope with ictree.
Delimit Scope ictree_scope with ictree.
Local Open Scope ictree_scope.

Arguments ictree E {H} X. 
Arguments ictreeF E {H} X.
Arguments BrF {E H X} [ictree] n k.
Arguments GuardF {E H X} [ictree] t.
Arguments RetF {E H X} [ictree] x.
Arguments VisF {E H X} [ictree] e k.

Notation ictree' E X := (ictreeF E X (ictree E X)).

(*| We wrap the primitive projection [_observe] in a function [observe]. |*)
Definition observe `{HE: Encode E} `(t : ictree E X) : ictree' E X := @_observe E HE X t.

Notation Ret x        := (go (RetF x)).
Notation Vis e k      := (go (VisF e k)).
Notation Br n k     := (go (BrF n k)).
Notation Guard t     := (go (GuardF t)).
Notation step t     := (Br 0 (fun _ => t)).

(* Use resum and resum_ret to map the events in an entree to another type *)
CoFixpoint resumICtree' {E1 E2 : Type} `{ReSumRet E1 E2}
           {A} (ot : ictree' E1 A) : ictree E2 A :=
  match ot with
  | RetF r => Ret r
  | BrF n k => Br n (fun i => resumICtree' (observe (k i)))
  | GuardF t =>  Guard (resumICtree' (observe t))
  | VisF e k => Vis (resum e) (fun x => resumICtree' (observe (k (resum_ret e x))))
  end.

Definition resumICtree {E1 E2 : Type} `{ReSumRet E1 E2}
           {A} (t : ictree E1 A) : ictree E2 A :=
  resumICtree' (observe t).

Module ICtree.

  Definition subst' {E : Type@{eff}} {HE: Encode E} {R S : Type@{eff}}
    (k : R -> ictree E S) : ictree' E R -> ictree E S  :=
    cofix _subst (ot : ictree' E R) :=
      match ot with
      | RetF r => k r
      | BrF n h => Br n (fun x => _subst (observe (h x)))
      | GuardF t => Guard (_subst (observe t))
      | VisF e k => Vis e (fun x => _subst (observe (k x)))
    end.

  (*| Monadic composition [bind] |*)
  Definition bind `{HE: Encode E} {X Y} (t : ictree E X) (k : X -> ictree E Y) :=
    subst' k (observe t).

  (*| Monadic composition of continuations (i.e., Kleisli composition). |*)
  Definition cat `{HE: Encode E} `(k : X -> ictree E Y) `(h : Y -> ictree E Z) :
    X -> ictree E Z := fun t => bind (k t) h.

  (*| Functorial map ([fmap] in Haskell) |*)
  Definition map `{HE: Encode E} `(f : X -> Y) (t : ictree E X) : ictree E Y :=
      bind t (fun x => Ret (f x)).

  Definition trigger {E1 E2 : Type@{eff}} `{ReSumRet E1 E2}
    (e : E1) : ictree E2 (encode e) :=
    Vis (resum e) (fun x : encode (resum e) => Ret (resum_ret e x)).
  
  (*| Atomic ictrees with choice. |*)
  Definition branch `{HE: Encode E} n: ictree E (fin' n) :=
    Br n (fun x => Ret x).

  (*| Binary non-deterministic branch |*)
  Definition br2 `{HE: Encode E}{X} (a b: ictree E X): ictree E X :=
    Br 1 (fun x: fin' 1 =>
            match x in Fin.t n return n = 2 -> ictree E X with
            | Fin.F1 => fun _: _ = 2 => a
            | _ => fun _: _ = 2 => b
            end eq_refl).

  (*| Ternary non-deterministic branch |*)
  Definition br3 `{HE: Encode E}{X} (a b c: ictree E X): ictree E X :=
    Br 2 (fun x: fin' 2 =>
            match x in Fin.t n return n = 3 -> ictree E X with
            | Fin.F1 => fun _: _ = 3 => a
            | Fin.FS Fin.F1 => fun _: _ = 3 => b
            | _ => fun _: _ = 3 => c
            end eq_refl).

  (*| Ignore the result of a ictree. |*)
  Definition ignore `{HE: Encode E} {R} : ictree E R -> ictree E unit :=
    map (fun _ => tt).

  (*| Run forever, do nothing |*)
  CoFixpoint stuck `{HE: Encode E} {R} : ictree E R := Guard stuck.
  
  (*| Run forever, do tau steps |*)
  CoFixpoint spin `{HE: Encode E} {R} : ictree E R := step spin.

  (*| [iter] |*)
  Definition iter `{HE: Encode E} {R I: Type}
    (step : I -> ictree E (I + R)) : I -> ictree E R :=
    cofix iter_ i := bind (step i)
                       (fun lr =>
                          match lr with
                          | inl l => (Guard (iter_ l))
                          | inr r => Ret r
                          end).

  Definition forever `{HE: Encode E} {R: Type} (X: Type) (k: R -> ictree E R) (x: R) :=
    iter (R:=X) (fun x => map inl (k x)) x.
  
End ICtree.


Ltac fold_bind :=
  repeat match goal with
    | h: context [ICtree.subst' ?k ?t] |- _ => fold (ICtree.bind (go t) k) in h
    | |- context [ICtree.subst' ?k ?t] => fold (ICtree.bind (go t) k)
    end.

#[global] Hint Extern 0 => fold_bind: core.

(*|
[on_left lr l t]: run a computation [t] if the first argument is an [inl l].
[l] must be a variable (used as a pattern), free in the expression [t]:

   - [on_left (inl x) l t = t{l := x}]
   - [on_left (inr y) l t = Ret y]
|*)

Notation on_left lr l t :=
  (match lr with
   | inl l => t
   | inr r => Ret r
   end) (only parsing).

Ltac desobs t :=
  let H := fresh "Heqt" in destruct (observe t) eqn:H.

Module ICTreeNotations.
  Declare Scope ictree_scope.
  Bind Scope ictree_scope with ictree.
  Delimit Scope ictree_scope with ictree.
  Local Open Scope ictree_scope.

  Notation "t1 >>= k2" := (ICtree.bind t1 k2)
                            (at level 58, left associativity) : ictree_scope.
  Notation "x <- t1 ;; t2" := (ICtree.bind t1 (fun x => t2))
                               (at level 62, t1 at next level, right associativity) : ictree_scope.
  Notation "t1 ;; t2" := (ICtree.bind t1 (fun _ => t2))
                           (at level 62, right associativity) : ictree_scope.
  Notation "' p <- t1 ;; t2" :=
    (ICtree.bind t1 (fun x_ => match x_ with p => t2 end))
      (at level 62, t1 at next level, p pattern, right associativity) : ictree_scope.

  Notation "'continue'" :=
    (Ret (inl tt))
      (at level 60): ictree_scope.

  Notation "'break'" :=
    (Ret (inr tt))
      (at level 60): ictree_scope.
  
  Notation "'for' i 'to' '∞' b" :=
    (ICtree.forever void
       (fun (x: nat) =>
         b%ictree x ;;
         Ret (S x)) i%nat) (at level 64, right associativity): ictree_scope.
  
  Notation "'loop' b" :=
    (@ICtree.iter _ _ unit unit
       (fun 'tt => b) tt) (at level 64): ictree_scope.
  
End ICTreeNotations.

(*| Common instances for [ictree] |*)
#[global] Instance Functor_ictree `{Encode E} : Functor (ictree E) :=
  { fmap := @ICtree.map E _ }.

#[global] Instance Applicative_ictree `{Encode E} : Applicative (ictree E) :=
  {
    pure := fun _ x => Ret x;
    ap := fun _ _ f x =>
            ICtree.bind f (fun f => ICtree.bind x (fun x => Ret (f x)) );
  }.

#[global] Instance Monad_ictree `{HE: Encode E} : Monad (ictree E) :=
  {
    ret := fun _ x => Ret x;
    bind := @ICtree.bind E HE;
  }.

#[global] Instance MonadIter_ictree `{HE: Encode E} : MonadIter (ictree E) :=
  fun _ _ => ICtree.iter.

#[global] Instance MonadBr_ictree `{HE: Encode E} : MonadBr (ictree E) :=
  fun n => ICtree.branch n.

(*| Export various useful Utils |*)
From TICL Require Export Utils.Utils.
