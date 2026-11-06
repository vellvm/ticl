From Coinduction Require Import all.

From TICL Require Import
  Utils.Utils
  Logic.Syntax
  Logic.Semantics
  Logic.Congruence.

Import TiclNotations.
Local Open Scope ticl_scope.

Generalizable All Variables.

(** * Ltac tactics for working with TICL formulas *)
(** For example splitting conjunctions and disjunctions, unfolding inductive and coinductive modalities [AU, AG, EU, EG].
    The [csplit] tactic is used to split conjunctions and disjunctions under a ticl entailment in the goal
    the [cleft] tactic is used to take the left branch of a disjunction under a ticl entailment in the goal,
    the [cright] tactic is used to take the right branch of a disjunction under a ticl entailment in the goal,
    the [cdestruct] tactic is used to destruct conjunctions and disjunctions under a ticl entailment in a hypothesis.
    *)
#[global] Ltac csplit :=
  ticl_normalize;
  lazymatch goal with
  | |- @entails ?M ?E ?B ?KMS ?X ?b (CAnd ?p ?q) ?t ?w =>
      rewrite ticl_and; split
  | |- @entails ?M ?E ?B ?KMS ?X ?b (Cx Q_A ?p ?q) ?t ?w =>
      rewrite ticl_an; split2
  | |- @entails ?M ?E ?B ?KMS ?X ?b (Cx Q_E ?p ?q) ?t ?w =>
      rewrite ticl_en; split
  (* Quantifier is a variable, destruct it. *)
  | |- @entails ?M ?E ?B ?KMS ?X ?b (Cx ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; csplit
  | |- @entails ?M ?E ?B ?KMS ?X false (Cg Q_A ?p) ?t ?w =>
      rewrite (@equivl_ag_an M E B KMS X p), ticl_an; split2
  | |- @entails ?M ?E ?B ?KMS ?X false (Cg Q_E ?p) ?t ?w =>
      rewrite (@equivl_eg_en M E B KMS X p), ticl_en; split
  | |- @entails ?M ?E ?B ?KMS ?X false (Cg ?c ?p) ?t ?w =>
      is_var c; destruct c; csplit
  | |- @entails ?M ?E ?B ?KMS ?X false <( pure )> ?t ?w =>
      change <( t, w |=L pure )>; rewrite ticl_pure
  | |- @entails ?M ?E ?B ?KMS ?X false <( vis ?φ )> ?t ?w =>
      change <( t, w |=L vis φ )>; rewrite ticl_vis; econstructor
  | |- @entails ?M ?E ?B ?KMS ?X false (CNow ?φ) ?t ?w =>
      rewrite ticl_now
  | |- @entails ?M ?E ?B ?KMS ?X true (CRet ?φ) ?t ?w =>
      rewrite ticl_ret; eexists; split; [| split; [| split]]
  end.

#[global] Ltac cleft :=
  ticl_normalize;
  match goal with
  | |- @entails ?M ?E ?B ?KMS ?X ?b (COr ?p ?q) ?t ?w =>
      rewrite ticl_or; left
  | |- @entails ?M ?E ?B ?KMS ?X ?b (Cu Q_A ?p ?q) ?t ?w =>
      rewrite (@equiv_au_an M E B KMS X b p q), ticl_or; left
  | |- @entails ?M ?E ?B ?KMS ?X ?b (Cu Q_E ?p ?q) ?t ?w =>
      rewrite (@equiv_eu_en M E B KMS X b p q), ticl_or; left
  (* Quantifier is a variable, destruct it. *)
  | |- @entails ?M ?E ?B ?KMS ?X ?b (Cu ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cleft
  end.

#[global] Ltac cright :=
  ticl_normalize;
  match goal with
  | |- @entails ?M ?E ?B ?KMS ?X ?b (COr ?p ?q) ?t ?w =>
      rewrite ticl_or; right
  | |- @entails ?M ?E ?B ?KMS ?X ?b (Cu Q_A ?p ?q) ?t ?w =>
      rewrite (@equiv_au_an M E B KMS X b p q), ticl_or; right
  | |- @entails ?M ?E ?B ?KMS ?X ?b (Cu Q_E ?p ?q) ?t ?w =>
      rewrite (@equiv_eu_en M E B KMS X b p q), ticl_or; right
  (* Quantifier is a variable, destruct it. *)
  | |- @entails ?M ?E ?B ?KMS ?X ?b (Cu ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cright
  end.

#[global] Ltac cdestruct H :=
  ticl_normalize in H;
  match type of H with
  | @entails ?M ?E ?B ?KMS ?X false <( pure )> ?t ?w =>
      change <( t, w |=L pure )> in H; rewrite ticl_pure in H; destruct H; subst
  | @entails ?M ?E ?B ?KMS ?X false <( vis ?φ )> ?t ?w =>
      change <( t, w |=L vis φ )> in H; rewrite ticl_vis in H; ddestruction H
  | @entails ?M ?E ?B ?KMS ?X false (CNow ?φ) ?t ?w =>
      rewrite ticl_now in H; destruct H
  | @entails ?M ?E ?B ?KMS ?X true (CRet ?φ) ?t ?w =>
      let x := fresh "x" in
      let HR := fresh "HR" in
      let Hd := fresh "Hd" in
      let Hs := fresh "Hs" in
      rewrite ticl_ret in H; destruct H as (x & HR & Hd & Hs & H)
  (* AND *)
  | @entails ?M ?E ?B ?KMS ?X ?b (CAnd ?p ?q) ?t ?w =>
      let Hp := fresh "H"p in
      let Hq := fresh "H"q in
      rewrite ticl_and in H; destruct H as [Hp Hq]
  (* OR *)
  | @entails ?M ?E ?B ?KMS ?X ?b (COr ?p ?q) ?t ?w =>
      rewrite ticl_or in H; destruct H as [H | H]
  (* X *)
  | @entails ?M ?E ?B ?KMS ?X ?b (Cx Q_A ?p ?q) ?t ?w =>
      let Hs := fresh "Hs" in
      let Hp := fresh "Hp" in
      rewrite ticl_an in H; destruct H as (Hp & Hs & H)
  | @entails ?M ?E ?B ?KMS ?X ?b (Cx Q_E ?p ?q) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR := fresh "TR" in
      let Hp := fresh "Hp" in
      rewrite ticl_en in H; destruct H as (Hp & t' & w' & TR & H)
  (* Quantifier is a variable, destruct it. *)
  | @entails ?M ?E ?B ?KMS ?X ?b (Cx ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  (* U *)
  | @entails ?M ?E ?B ?KMS ?X ?b (Cu Q_A ?p ?q) ?t ?w =>
      rewrite (@equiv_au_an M E B KMS X b p q), ticl_or in H; destruct H
  | @entails ?M ?E ?B ?KMS ?X ?b (Cu Q_E ?p ?q) ?t ?w =>
      rewrite (@equiv_eu_en M E B KMS X b p q), ticl_or in H; destruct H
  (* Quantifier is a variable, destruct it. *)
  | @entails ?M ?E ?B ?KMS ?X ?b (Cu ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  (* G *)
  | @entails ?M ?E ?B ?KMS ?X false (Cg Q_A ?φ) ?t ?w =>
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      rewrite (@equivl_ag_an M E B KMS X φ), ticl_an in H; destruct H as (Hp & Hs & H)
  | @entails ?M ?E ?B ?KMS ?X false (Cg Q_E ?φ) ?t ?w =>
      let Hp := fresh "Hp" in
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR := fresh "TR" in
      rewrite (@equivl_eg_en M E B KMS X φ), ticl_en in H;
      destruct H as (Hp & t' & w' & TR & H)
  | @entails ?M ?E ?B ?KMS ?X false (Cg ?c ?p) ?t ?w =>
      is_var c; destruct c; cdestruct H
  end.
