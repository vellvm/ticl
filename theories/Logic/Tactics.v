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
  lazymatch goal with
  | |- @entailsL ?M ?E ?B ?KMS ?X (CAndL ?p ?q) ?t ?w =>
      rewrite ticll_and; split
  | |- @entailsR ?M ?E ?B ?KMS ?X (CAndR ?p ?q) ?t ?w =>
      rewrite ticlr_and; split
                                 
  | |- @entailsL ?M ?E ?B ?KMS ?X (CxL Q_A ?p ?q) ?t ?w =>      
      rewrite ticll_an; split2
  | |- @entailsR ?M ?E ?B ?KMS ?X (CxR Q_A ?p ?q) ?t ?w =>
      rewrite ticlr_an; split2
  | |- @entailsL ?M ?E ?B ?KMS ?X (CxL Q_E ?p ?q) ?t ?w =>
      rewrite ticll_en; split
  | |- @entailsR ?M ?E ?B ?KMS ?X (CxR Q_E ?p ?q) ?t ?w =>
      rewrite ticlr_en; split
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?E ?B ?KMS ?X (CxL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; csplit
  | |- @entailsR ?M ?E ?B ?KMS ?X (CxR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; csplit
                              
  | |- @entailsL ?M ?E ?B ?KMS ?X (Cg Q_A ?p) ?t ?w =>
      rewrite equivl_ag_an, ticll_an; split2
  | |- @entailsL ?M ?E ?B ?KMS ?X (Cg Q_E ?p) ?t ?w =>
      rewrite equivl_eg_en, ticll_en; split
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?E ?B ?KMS ?X (Cg ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; csplit
                              
  | |- @entailsL ?M ?E ?B ?KMS ?X <( pure )> ?t ?w =>
      rewrite ticll_pure
  | |- @entailsL ?M ?E ?B ?KMS ?X <( vis ?φ )> ?t ?w =>
      rewrite ticll_vis; econstructor
  | |- @entailsL ?M ?E ?B ?KMS ?X <( now ?φ )> ?t ?w =>
      rewrite ticll_now
  | |- @entailsR ?M ?E ?B ?KMS ?X <[ finish ?φ ]> ?t ?w =>
      rewrite ticlr_finish; econstructor
  | |- @entailsR ?M ?E ?B ?KMS ?X <[ done ?φ ]> ?t ?w =>
      rewrite ticlr_done; econstructor
  | |- @entailsR ?M ?E ?B ?KMS ?X <[ ret ?φ ]> ?t ?w =>
      rewrite ticlr_ret; eexists; split; [| split; [| split]]
  end.

#[global] Ltac cleft :=
  match goal with
  | |- @entailsL ?M ?E ?B ?KMS ?X (COrL ?p ?q) ?t ?w =>
      rewrite ticll_or; left
  | |- @entailsR ?M ?E ?B ?KMS ?X (COrR ?p ?q) ?t ?w =>
      rewrite ticlr_or; left                          
  | |- @entailsL ?M ?E ?B ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      rewrite equivl_au_an, ticll_or; left
  | |- @entailsR ?M ?E ?B ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      rewrite equivr_au_an, ticlr_or; left
  | |- @entailsL ?M ?E ?B ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      rewrite equivl_eu_en, ticll_or; left
  | |- @entailsR ?M ?E ?B ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      rewrite equivr_eu_en, ticlr_or; left
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?E ?B ?KMS ?X (CuL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cleft
  | |- @entailsR ?M ?E ?B ?KMS ?X (CuR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cleft
end.

#[global] Ltac cright :=
  match goal with
  | |- @entailsL ?M ?E ?B ?KMS ?X (COrL ?p ?q) ?t ?w =>
      rewrite ticll_or; right
  | |- @entailsR ?M ?E ?B ?KMS ?X (COrR ?p ?q) ?t ?w =>
      rewrite ticlr_or; right
  | |- @entailsL ?M ?E ?B ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      rewrite equivl_au_an, ticll_or; right
  | |- @entailsR ?M ?E ?B ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      rewrite equivr_au_an, ticlr_or; right
  | |- @entailsL ?M ?E ?B ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      rewrite equivl_eu_en, ticll_or; right
  | |- @entailsR ?M ?E ?B ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      rewrite equivr_eu_en, ticlr_or; right
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?E ?B ?KMS ?X (CuL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cright
  | |- @entailsR ?M ?E ?B ?KMS ?X (CuR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cright                              
  end.

#[global] Ltac cdestruct H :=
  match type of H with
  | <( ?t, ?w |= pure )> => rewrite ticll_pure in H; destruct H; subst
  | <( ?t, ?w |= vis ?φ )> =>
      rewrite ticll_vis in H; ddestruction H
  | <( ?t, ?w |= now ?φ )> => rewrite ticll_now in H; destruct H
  | <[ ?t, ?w |= finish ?φ ]> =>
      rewrite ticlr_finish in H; ddestruction H
  | <[ ?t, ?w |= done ?φ ]> => rewrite ticlr_done in H; ddestruction H
  | <[ ?t, ?w |= ret ?φ ]> =>
      let x := fresh "x" in
      let HR := fresh "HR" in
      let Hd := fresh "Hd" in
      let Hs := fresh "Hs" in
      rewrite ticlr_ret in H; destruct H as (x & HR & Hd & Hs & H)
  (* AND *)
  | <( ?t, ?w |= ?p /\ ?q )> =>
      let Hp := fresh "H"p in
      let Hq := fresh "H"q in
      rewrite ticll_and in H; destruct H as [Hp Hq]            
  | <[ ?t, ?w |= ?p /\ ?q ]> =>
      let Hp := fresh "H"p in
      let Hq := fresh "H"q in
      rewrite ticlr_and in H; destruct H as [Hp Hq]
  (* OR *)                                         
  | <( ?t, ?w |= ?p \/ ?q )> =>
      rewrite ticll_or in H; destruct H as [H | H]
  | <[ ?t, ?w |= ?p \/ ?q ]> =>
      rewrite ticlr_or in H; destruct H as [H | H]
  (* X *)
  | @entailsL ?M ?E ?B ?KMS ?X (CxL Q_A ?p ?q) ?t ?w =>
      let Hs' := fresh "Hs" in
      let Hp' := fresh "Hp" in
      rewrite ticll_an in H; destruct H as (Hp' & Hs' & H)
  | @entailsL ?M ?E ?B ?KMS ?X (CxL Q_E ?p ?q) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      let Hp := fresh "Hp" in
      rewrite ticll_en in H; destruct H as (Hp & t' & w' & TR' & H)
  | @entailsR ?M ?E ?B ?KMS ?X (CxR Q_A ?p ?q) ?t ?w =>
      let Hs' := fresh "Hs" in
      let Hp := fresh "Hp" in
      rewrite ticlr_an in H; destruct H as (Hp & Hs' & H)
  | @entailsR ?M ?E ?B ?KMS ?X (CxR Q_E ?p ?q) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      let Hp := fresh "Hp" in
      rewrite ticlr_en in H; destruct H as (Hp & t' & w' & TR' & H)
  (* Quantifier is a variable, destruct it *)
  | @entailsL ?M ?E ?B ?KMS ?X (CxL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  | @entailsR ?M ?E ?B ?KMS ?X (CxR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  (* U *)
  | @entailsL ?M ?E ?B ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      rewrite equivl_au_an, ticll_or in H; destruct H
  | @entailsR ?M ?E ?B ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      rewrite equivr_au_an, ticlr_or in H; destruct H
  | @entailsL ?M ?E ?B ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      rewrite equivl_eu_en, ticll_or in H; destruct H
  | @entailsR ?M ?E ?B ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      rewrite equivr_eu_en, ticlr_or in H; destruct H
  (* Quantifier is a variable, destruct it *)
  | @entailsL ?M ?E ?B ?KMS ?X (CuL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  | @entailsR ?M ?E ?B ?KMS ?X (CuR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H

  (* G *)          
  | @entailsL ?M ?E ?B ?KMS ?X (Cg Q_A ?φ) ?t ?w =>
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      rewrite equivl_ag_an, unfold_entailsL in H; destruct H as (Hp & Hs & H)
  | @entailsL ?M ?E ?B ?KMS ?X (Cg Q_E ?φ) ?t ?w =>
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite equivl_eg_en, unfold_entailsL in H; destruct H as (Hp & t' & w' & TR' & H)
  | @entailsL ?M ?E ?B ?KMS ?X (Cg ?c ?p) ?t ?w =>
      is_var c; destruct c; cdestruct H
  end.
