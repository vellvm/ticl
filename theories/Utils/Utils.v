#[global] Set Warnings "-intuition-auto-with-star".
From Stdlib Require Import Fin.
From Stdlib Require Import
  Classes.DecidableClass
  RelationPairs.  
From Stdlib Require Export Program.Equality.
From Stdlib Require Import Program.Tactics.

From Coinduction Require Import coinduction.

Generalizable All Variables.

Notation fin := Fin.t.

#[global] Arguments bt : simpl never.
Tactic Notation "cbn*" := unfold bt; cbn.

Notation rel X Y := (X -> Y -> Prop).

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

(*| Heterogeneous [pair], todo move to coinduction library |*)
Definition pointwise {X X' Y Y'} (SS : rel X X')
  : rel Y Y' -> rel (X -> Y) (X' -> Y') :=
  fun R k k' => forall x x', SS x x' -> R (k x) (k' x').

Definition pairH {A B : Type} (x : A) (y : B) : A -> B -> Prop :=
  fun x' y' => x = x' /\ y = y'.

Lemma leq_pairH : forall {A B : Type} (x : A) (y : B) (R : rel A B),
    R x y <-> pairH x y <= R.
Proof.
  firstorder congruence.
Qed.

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

Definition Deterministic {X} `{Equivalence Y eqY} (R: rel X Y) :=
  forall x y z, R x y -> R x z -> eqY y z.

Lemma t_gfp_bt : forall {X} `{CompleteLattice X} (b : mon X),
  t b (gfp (bt b)) == gfp b.
Proof.
  intros. cbn.
  rewrite <- enhanced_gfp. rewrite t_gfp.
  reflexivity.
Qed.

#[global] Instance t_weq : forall {X Y},
  Proper (weq ==> weq) (@t (rel X Y) _).
Proof.
  split; repeat red; intros.
  - destruct H0. exists x0; auto.
    repeat red. intros.
    apply H. apply H0.
    eapply (Hbody x0). { cbn. red. intros. apply H. apply H3. }
    apply H2.
  - destruct H0. exists x0; auto.
    repeat red. intros.
    apply H. apply H0.
    eapply (Hbody x0). { cbn. red. intros. apply H. apply H3. }
    apply H2.
Qed.

#[global] Instance gfp_weq : forall {X Y},
  Proper (weq ==> weq) (@gfp (rel X Y) _).
Proof.
  intros. intros ? ? ?. now apply t_weq.
Qed.
Ltac _apply f :=
  match goal with
    |- context [@body ?x ?l ?y] => apply (f _ l)
  end.

(* A smarter version of this should be part of the [coinduction] library *)
Ltac step_ :=
  match goal with
  | |- gfp ?b ?x ?y ?z ?v => apply (proj2 (gfp_fp b x y z v)); cbn
  | |- body (t ?b) ?R ?x ?y ?z ?v => apply (bt_t b R x y z v)
  | |- body (body (T ?b) ?f) ?R ?x ?y ?z ?v => apply (bT_T b f R x y z v)
  | |- gfp ?b ?x ?y ?z => apply (proj2 (gfp_fp b x y z)); cbn
  | |- body (t ?b) ?R ?x ?y ?z => apply (bt_t b R x y z)
  | |- body (body (T ?b) ?f) ?R ?x ?y ?z => apply (bT_T b f R x y z)
  | |- gfp ?b ?x ?y => apply (proj2 (gfp_fp b x y))
  | |- body (t ?b) ?R ?x ?y => apply (bt_t b R x y)
  | |- body (body (T ?b) ?f) ?R ?x ?y => apply (bT_T b f R x y)
  | |- gfp ?b ?x => apply (proj2 (gfp_fp b x))
  | |- body (t ?b) ?R ?x => apply (bt_t b R x)
  | |- body (body (T ?b) ?f) ?R ?x => apply (bT_T b f R x)
  | |- context[@body ?x ?l (bt ?f)] => apply (@gfp_bt _ l)
  end.

Ltac step := first [step_ | red; step_].

Ltac step_in H :=
  match type of H with
  | gfp ?b ?x ?y ?z ?v => apply (gfp_fp b x y z v) in H
  | body (t ?b) ?R ?x ?y ?z ?v => apply (bt_t b R x y z v) in H
  | gfp ?b ?x ?y ?z => apply (gfp_fp b x y z) in H
  | body (t ?b) ?R ?x ?y ?z => apply (bt_t b R x y z) in H
  | gfp ?b ?x ?y => apply (gfp_fp b x y) in H
  | body (t ?b) ?R ?x ?y => apply (bt_t b R x y) in H
  | gfp ?b ?x => apply (gfp_fp b x) in H
  | body (t ?b) ?R ?x => apply (bt_t b R x) in H
  | _ => red in H; step_in H
  end.
Tactic Notation "step" "in" ident(H) := step_in H.

#[global] Notation inhabited X := { x: X | True}.

Definition sum_rel {A B1 B2} Ra Rb : rel (A + B1) (A + B2) :=
  fun ab ab' =>
    match ab, ab' with
    | inl a, inl a' => Ra a a'
    | inr b, inr b' => Rb b b'
    | _, _ => False
    end.

Ltac inv H := inversion H; clear H; subst.

Ltac invert :=
  match goal with
  | h : existT _ _ _ = existT _ _ _ |- _ => dependent induction h
  | h : existT _ _ = existT _ _ |- _ => dependent induction h
  end.

Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.

Lemma wf3_proj1{X Y Z: Type} (R: relation X):
  well_founded R -> well_founded (fun (p: X * Y * Z) p' => R (fst (fst p)) (fst (fst p'))).
Proof.
  unfold well_founded.
  intros Hind [[x a] b].
  generalize dependent a.
  generalize dependent b.
  induction (Hind x) as [x Hx IH].
  constructor.
  intros [[x' a'] b'] H.
  apply IH.
  assumption.
Defined.

Lemma wf3_proj2{X Y Z: Type} (R: relation Y):
  well_founded R -> well_founded (fun (p: X * Y * Z) p' => R (snd (fst p)) (snd (fst p'))).
Proof.
  unfold well_founded.
  intros Hind [[a x] b].
  generalize dependent a.
  generalize dependent b.
  induction (Hind x) as [x Hx IH].
  constructor.
  intros [[a' x'] b'] H.
  apply IH.
  assumption.
Defined.

Lemma wf3_proj3{X Y Z: Type} (R: relation Z):
  well_founded R -> well_founded (fun (p: X * Y * Z) p' => R (snd p) (snd p')).
Proof.
  unfold well_founded.
  intros Hind [[a b] x].
  generalize dependent a.
  generalize dependent b.
  induction (Hind x) as [x Hx IH].
  constructor.
  intros [[a' b'] x'] H.
  apply IH.
  assumption.
Defined.

Lemma wf3_proj12{X Y Z: Type} (R: relation (X*Y)):
  well_founded R -> well_founded (fun (p: X * Y * Z) p' => R (fst p) (fst p')).
Proof.
  unfold well_founded.
  intros Hind [x b].
  generalize dependent b.
  induction (Hind x) as [x Hx IH].
  constructor.
  intros [x' b'] H.
  apply IH.
  assumption.
Defined.
