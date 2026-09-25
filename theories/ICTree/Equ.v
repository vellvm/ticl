From TICL Require Export
  ICTree.Eq.Core
  ICTree.Eq.Bind.

From TICL Require Import
  ICTree.Core.

From Stdlib Require Import
  Relations
  Classes.RelationClasses
  Classes.Morphisms.

Import ICTreeNotations.
Local Open Scope ictree_scope.

Global Typeclasses Opaque equ.

(** * Tactics for equ *)
Ltac observe_equ H :=
  lazymatch type of H with
  | observe ?t = RetF ?x =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Ret x) by (step; cbn; rewrite H; reflexivity)
  | observe ?t = BrF ?n ?k =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Br n k) by (step; cbn; rewrite H; reflexivity)
  | observe ?t = GuardF ?t' =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Guard t') by (step; cbn; rewrite H; reflexivity)
  | observe ?t = VisF ?e ?k =>
      let Heq := fresh "Eqt" in
      assert (Heq: t ≅ Vis e k) by (step; cbn; rewrite H; reflexivity)
  | RetF ?x = observe ?t => symmetry in H; observe_equ H
  | VisF ?e ?k = observe ?t => symmetry in H; observe_equ H
  | GuardF ?t' = observe ?t => symmetry in H; observe_equ H
  | BrF ?n ?k = observe ?t => symmetry in H; observe_equ H
  | observe ?t = observe ?t' =>
      let Heq := fresh "Eqt" in        
      assert (Heq: t ≅ t') by (step; cbn; rewrite H; reflexivity)
  end.

Ltac observe_equ_all :=
  match goal with
  | H: _ = _ |- _ => (* Do something with hypothesis H *)
      observe_equ H;            
      clear H;
      observe_equ_all
  | _ => idtac
  end.

(** * Forgetting finitely many leading guards.

    [guard_equ] is the equivalence closure of "raw-equivalent, or one leading
    guard away".  It forgets ONLY finitely many leading guards and raw
    equivalence: it never erases a [Br] node, and it never equates a
    divergent prefix with a productive one.  The closure is Stdlib's
    [clos_refl_sym_trans], not a second hand-written equivalence closure; the
    five constructor-shaped facts below are derived so that source-alignment
    tactics remain usable. *)

Definition guard_step {E} {HE : Encode E} {X} (t u : ictree E X) : Prop :=
  t ≅ u \/ t ≅ Guard u.

Definition guard_equ {E} {HE : Encode E} {X} : ictree E X -> ictree E X -> Prop :=
  clos_refl_sym_trans _ guard_step.

Section GuardEqu.
  Context {E : Type} {HE : Encode E} {X : Type}.

  Lemma guard_equ_equ (t u : ictree E X) : t ≅ u -> guard_equ t u.
  Proof. intro H; apply rst_step; now left. Qed.

  Lemma guard_equ_left (t u : ictree E X) :
    guard_equ t u -> guard_equ (Guard t) u.
  Proof.
    intro H; eapply rst_trans; [| exact H].
    apply rst_step; right; reflexivity.
  Qed.

  Lemma guard_equ_right (t u : ictree E X) :
    guard_equ t u -> guard_equ t (Guard u).
  Proof.
    intro H; eapply rst_trans; [exact H |].
    apply rst_sym, rst_step; right; reflexivity.
  Qed.

  Lemma guard_equ_sym (t u : ictree E X) : guard_equ t u -> guard_equ u t.
  Proof. apply rst_sym. Qed.

  Lemma guard_equ_trans (t u v : ictree E X) :
    guard_equ t u -> guard_equ u v -> guard_equ t v.
  Proof. apply rst_trans. Qed.

  #[global] Instance guard_equ_Equivalence : Equivalence (@guard_equ E HE X).
  Proof.
    split.
    - intro t; apply rst_refl.
    - intros t u; apply rst_sym.
    - intros t u v; apply rst_trans.
  Qed.

  #[global] Instance guard_equ_proper :
    Proper (equ eq ==> equ eq ==> iff) (@guard_equ E HE X).
  Proof.
    intros t t' Ht u u' Hu; split; intro H.
    - eapply guard_equ_trans; [apply guard_equ_equ; symmetry; exact Ht|].
      eapply guard_equ_trans; [exact H|apply guard_equ_equ; exact Hu].
    - eapply guard_equ_trans; [apply guard_equ_equ; exact Ht|].
      eapply guard_equ_trans; [exact H|apply guard_equ_equ; symmetry; exact Hu].
  Qed.
End GuardEqu.
