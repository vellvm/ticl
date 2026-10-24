#[global] Set Warnings "-intuition-auto-with-star".
From Stdlib Require Import Fin.
From Stdlib Require Import
  Classes.DecidableClass
  RelationPairs.
From Stdlib Require Export Program.Equality.
From Stdlib Require Import Program.Tactics.

From Coinduction Require Import all.

(** [rel], [step], [step in], [MonadBr], [inhabited], [sum_rel], [invert], [break]
    are provided by the [ctrees] library. *)
From CTree Require Export Core.Utils.

Generalizable All Variables.

Ltac ddestruction H := cbn in H; dependent destruction H.
Ltac split2 := split; [|split].

Lemma option_map_none {X Y}: forall (f: X -> Y) m,
    option_map f m = None <-> m = None.
Proof.
  intros.
  destruct m; cbn.
  - split; intros Hcontra; inversion Hcontra.
  - split; intros Hcontra; inversion Hcontra; auto.
Qed.

Lemma option_map_some {X Y}: forall (f: X -> Y) m v,
    option_map f m = Some v <-> (exists x, m = Some x /\ v = f x).
Proof.
  intros; destruct m; cbn.
  - split; intros.
    + inversion H; subst.
      exists x; auto.
    + destruct H as (? & ? & ->).
      inversion H; subst; reflexivity.
  - split; intros; inversion H.
    destruct H0; inversion H0.
Qed.

Global Coercion is_true(b: bool): Prop :=
  if b then True else False.

Lemma pull2_iff: forall {A B C} (P : A -> B -> Prop) (R : A -> B -> C -> Prop),
    (forall a b, (exists c, R a b c)-> P a b) <-> (forall a b c, R a b c -> P a b).
  split; intros; eauto.
  destruct H0.
  now apply H with x.
Qed.

Definition Disjoint(A B: Prop) :=
  (A /\ ~ B) \/ (~ A /\ B).

Fixpoint Fin_compare {m n} (p : fin m) (q : fin n) :=
  match p, q with
  | @Fin.F1 m', @Fin.F1 n' => Nat.compare m' n'
  | Fin.FS _, Fin.F1 => Gt
  | Fin.F1, Fin.FS _ => Lt
  | Fin.FS p', Fin.FS q' => Fin_compare p' q'
  end.

Definition RelDecidable {X Y} (R: rel X Y) :=
  forall x y, Decidable (R x y).

Definition EqDecidable(X: Type) :=
  forall (x y: X), Decidable (x = y).

Ltac inv H := inversion H; clear H; subst.

Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.
