From Coinduction Require Import
  coinduction tactics.

From TICL Require Import
  Utils.Utils
  Events.Core
  Logic.Syntax
  Logic.Semantics
  Logic.Congruence.

Import TiclNotations.
Local Open Scope ticl_scope.

Generalizable All Variables.

#[global] Ltac csplit :=
  lazymatch goal with
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CAndL ?p ?q) ?t ?w =>
      rewrite ticll_and; split
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CAndR ?p ?q) ?t ?w =>
      rewrite ticlr_and; split
                                 
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_A ?p ?q) ?t ?w =>      
      rewrite ticll_an; split2
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_A ?p ?q) ?t ?w =>
      rewrite ticlr_an; split2
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_E ?p ?q) ?t ?w =>
      rewrite ticll_en; split
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_E ?p ?q) ?t ?w =>
      rewrite ticlr_en; split
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CxL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; csplit
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CxR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; csplit
                              
  | |- @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_A ?p) ?t ?w =>
      rewrite equivl_ag_an, ticll_an; split2
  | |- @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_E ?p) ?t ?w =>
      rewrite equivl_eg_en, ticll_en; split
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?W ?HE ?KMS ?X (Cg ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; csplit
                              
  | |- @entailsL ?M ?W ?HE ?KMS ?X <( pure )> ?t ?w =>
      rewrite ticll_pure
  | |- @entailsL ?M ?W ?HE ?KMS ?X <( vis ?φ )> ?t ?w =>
      rewrite ticll_vis; econstructor
  | |- @entailsL ?M ?W ?HE ?KMS ?X <( now ?φ )> ?t ?w =>
      rewrite ticll_now
  | |- @entailsR ?M ?W ?HE ?KMS ?X <[ finish ?φ ]> ?t ?w =>
      rewrite ticlr_finish; econstructor
  | |- @entailsR ?M ?W ?HE ?KMS ?X <[ done ?φ ]> ?t ?w =>
      rewrite ticlr_done; econstructor
  end.

#[global] Ltac cleft :=
  match goal with
  | |- @entailsL ?M ?W ?HE ?KMS ?X (COrL ?p ?q) ?t ?w =>
      rewrite ticll_or; left
  | |- @entailsR ?M ?W ?HE ?KMS ?X (COrR ?p ?q) ?t ?w =>
      rewrite ticlr_or; left                          
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      rewrite equivl_au_an, ticll_or; left
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      rewrite equivr_au_an, ticlr_or; left
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      rewrite equivl_eu_en, ticll_or; left
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      rewrite equivr_eu_en, ticlr_or; left
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cleft
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cleft
end.

#[global] Ltac cright :=
  match goal with
  | |- @entailsL ?M ?W ?HE ?KMS ?X (COrL ?p ?q) ?t ?w =>
      rewrite ticll_or; right
  | |- @entailsR ?M ?W ?HE ?KMS ?X (COrR ?p ?q) ?t ?w =>
      rewrite ticlr_or; right
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      rewrite equivl_au_an, ticll_or; right
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      rewrite equivr_au_an, ticlr_or; right
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      rewrite equivl_eu_en, ticll_or; right
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      rewrite equivr_eu_en, ticlr_or; right
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cright
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR ?c ?p ?q) ?t ?w =>
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
  (* IMPL *)
  | <[ ?t, ?w |= ?p -> ?q ]> =>
      rewrite ticlr_impll in H
  (* X *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_A ?p ?q) ?t ?w =>
      let Hs' := fresh "Hs" in
      let Hp' := fresh "Hp" in
      rewrite ticll_an in H; destruct H as (Hp' & Hs' & H)
  | @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_E ?p ?q) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      let Hp := fresh "Hp" in
      rewrite ticll_en in H; destruct H as (Hp & t' & w' & TR' & H)
  | @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_A ?p ?q) ?t ?w =>
      let Hs' := fresh "Hs" in
      let Hp := fresh "Hp" in
      rewrite ticlr_an in H; destruct H as (Hp & Hs' & H)
  | @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_E ?p ?q) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      let Hp := fresh "Hp" in
      rewrite ticlr_en in H; destruct H as (Hp & t' & w' & TR' & H)
  (* Quantifier is a variable, destruct it *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CxL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  | @entailsR ?M ?W ?HE ?KMS ?X (CxR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  (* U *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      rewrite equivl_au_an, ticll_or in H; destruct H
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      rewrite equivr_au_an, ticlr_or in H; destruct H
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      rewrite equivl_eu_en, ticll_or in H; destruct H
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      rewrite equivr_eu_en, ticlr_or in H; destruct H
  (* Quantifier is a variable, destruct it *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H

  (* G *)          
  | @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_A ?φ) ?t ?w =>
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      rewrite equivl_ag_an, unfold_entailsL in H; destruct H as (Hp & Hs & H)
  | @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_E ?φ) ?t ?w =>
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite equivl_eg_en, unfold_entailsL in H; destruct H as (Hp & t' & w' & TR' & H)
  | @entailsL ?M ?W ?HE ?KMS ?X (Cg ?c ?p) ?t ?w =>
      is_var c; destruct c; cdestruct H
  end.
