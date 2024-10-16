From Coinduction Require Import
  coinduction tactics.

From ICTL Require Import
  Utils.Utils
  Events.Core
  Logic.Syntax
  Logic.Semantics
  Logic.Congruence.

Import CtlNotations.
Local Open Scope ctl_scope.

Generalizable All Variables.

#[global] Ltac csplit :=
  lazymatch goal with
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CAndL ?p ?q) ?t ?w =>
      rewrite ctll_and; split
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CAndR ?p ?q) ?t ?w =>
      rewrite ctlr_and; split
                                 
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_A ?p ?q) ?t ?w =>      
      rewrite ctll_an; split2
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_A ?p ?q) ?t ?w =>
      rewrite ctlr_an; split2
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_E ?p ?q) ?t ?w =>
      rewrite ctll_en; split
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_E ?p ?q) ?t ?w =>
      rewrite ctlr_en; split
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CxL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; csplit
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CxR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; csplit
                              
  | |- @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_A ?p) ?t ?w =>
      rewrite ctll_ag_an, ctll_an; split2
  | |- @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_E ?p) ?t ?w =>
      rewrite ctll_eg_en, ctll_en; split
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?W ?HE ?KMS ?X (Cg ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; csplit
                              
  | |- @entailsL ?M ?W ?HE ?KMS ?X <( pure )> ?t ?w =>
      rewrite ctll_pure
  | |- @entailsL ?M ?W ?HE ?KMS ?X <( vis ?φ )> ?t ?w =>
      rewrite ctll_vis; econstructor
  | |- @entailsL ?M ?W ?HE ?KMS ?X <( now ?φ )> ?t ?w =>
      rewrite ctll_now
  | |- @entailsR ?M ?W ?HE ?KMS ?X <[ finish ?φ ]> ?t ?w =>
      rewrite ctlr_finish; econstructor
  | |- @entailsR ?M ?W ?HE ?KMS ?X <[ done ?φ ]> ?t ?w =>
      rewrite ctlr_done; econstructor
  end.

#[global] Ltac cleft :=
  match goal with
  | |- @entailsL ?M ?W ?HE ?KMS ?X (COrL ?p ?q) ?t ?w =>
      rewrite ctll_or; left
  | |- @entailsR ?M ?W ?HE ?KMS ?X (COrR ?p ?q) ?t ?w =>
      rewrite ctlr_or; left                          
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      rewrite ctll_au_an, ctll_or; left
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      rewrite ctlr_au_an, ctlr_or; left
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      rewrite ctll_eu_en, ctll_or; left
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      rewrite ctlr_eu_en, ctlr_or; left
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cleft
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cleft
end.

#[global] Ltac cright :=
  match goal with
  | |- @entailsL ?M ?W ?HE ?KMS ?X (COrL ?p ?q) ?t ?w =>
      rewrite ctll_or; right
  | |- @entailsR ?M ?W ?HE ?KMS ?X (COrR ?p ?q) ?t ?w =>
      rewrite ctlr_or; right
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      rewrite ctll_au_an, ctll_or; right
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      rewrite ctlr_au_an, ctlr_or; right
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      rewrite ctll_eu_en, ctll_or; right
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      rewrite ctlr_eu_en, ctlr_or; right
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cright
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cright                              
  end.

#[global] Ltac cdestruct H :=
  match type of H with
  | <( ?t, ?w |= pure )> => rewrite ctll_pure in H; destruct H; subst
  | <( ?t, ?w |= vis ?φ )> =>
      rewrite ctll_vis in H; ddestruction H
  | <( ?t, ?w |= now ?φ )> => rewrite ctll_now in H; destruct H
  | <[ ?t, ?w |= finish ?φ ]> =>
      rewrite ctlr_finish in H; ddestruction H
  | <[ ?t, ?w |= done ?φ ]> => rewrite ctlr_done in H; ddestruction H
  (* AND *)
  | <( ?t, ?w |= ?p /\ ?q )> =>
      let Hp := fresh "H"p in
      let Hq := fresh "H"q in
      rewrite ctll_and in H; destruct H as [Hp Hq]            
  | <[ ?t, ?w |= ?p /\ ?q ]> =>
      let Hp := fresh "H"p in
      let Hq := fresh "H"q in
      rewrite ctlr_and in H; destruct H as [Hp Hq]
  (* OR *)                                         
  | <( ?t, ?w |= ?p \/ ?q )> =>
      rewrite ctll_or in H; destruct H as [H | H]
  | <[ ?t, ?w |= ?p \/ ?q ]> =>
      rewrite ctlr_or in H; destruct H as [H | H]
  (* IMPL *)
  | <[ ?t, ?w |= ?p -> ?q ]> =>
      rewrite ctlr_impll in H
  (* X *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_A ?p ?q) ?t ?w =>
      let Hs' := fresh "Hs" in
      let Hp' := fresh "Hp" in
      rewrite ctll_an in H; destruct H as (Hp' & Hs' & H)
  | @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_E ?p ?q) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      let Hp := fresh "Hp" in
      rewrite ctll_en in H; destruct H as (Hp & t' & w' & TR' & H)
  | @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_A ?p ?q) ?t ?w =>
      let Hs' := fresh "Hs" in
      let Hp := fresh "Hp" in
      rewrite ctlr_an in H; destruct H as (Hp & Hs' & H)
  | @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_E ?p ?q) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      let Hp := fresh "Hp" in
      rewrite ctlr_en in H; destruct H as (Hp & t' & w' & TR' & H)
  (* Quantifier is a variable, destruct it *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CxL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  | @entailsR ?M ?W ?HE ?KMS ?X (CxR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  (* U *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      rewrite ctll_au_an, ctll_or in H; destruct H
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      rewrite ctlr_au_an, ctlr_or in H; destruct H
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      rewrite ctll_eu_en, ctll_or in H; destruct H
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      rewrite ctlr_eu_en, ctlr_or in H; destruct H
  (* Quantifier is a variable, destruct it *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H

  (* G *)          
  | @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_A ?φ) ?t ?w =>
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      rewrite ctll_ag_an, unfold_entailsL in H; destruct H as (Hp & Hs & H)
  | @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_E ?φ) ?t ?w =>
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite ctll_eg_en, unfold_entailsL in H; destruct H as (Hp & t' & w' & TR' & H)
  | @entailsL ?M ?W ?HE ?KMS ?X (Cg ?c ?p) ?t ?w =>
      is_var c; destruct c; cdestruct H
  end.
