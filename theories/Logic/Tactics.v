From Coinduction Require Import
  coinduction tactics.

From CTree Require Import
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
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CAndLR ?p ?q) ?t ?w =>
      rewrite ctlr_andl; split
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CAndRR ?p ?q) ?t ?w =>
      rewrite ctlr_andr; split
                                 
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_A ?p) ?t ?w =>      
      rewrite ctll_ax; split
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_A ?p) ?t ?w =>
      rewrite ctlr_ax; split
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_E ?p) ?t ?w =>
      rewrite ctll_ex
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_E ?p) ?t ?w =>
      rewrite ctlr_ex
  (* Quantifier is a variable, destruct it *)
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CxL ?c ?p) ?t ?w =>
      is_var c; destruct c; csplit
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CxR ?c ?p) ?t ?w =>
      is_var c; destruct c; csplit
                              
  | |- @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_A ?p) ?t ?w =>
      rewrite ctll_ag_ax; rewrite unfold_entailsL
  | |- @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_E ?p) ?t ?w =>
      rewrite ctll_eg_ex; rewrite unfold_entailsL
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
  | |- @entailsR ?M ?W ?HE ?KMS ?X (COrLR ?p ?q) ?t ?w =>
      rewrite ctlr_orl; left
  | |- @entailsR ?M ?W ?HE ?KMS ?X (COrRR ?p ?q) ?t ?w =>
      rewrite ctlr_orr; left
                          
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctll_af_ax
      | _ => rewrite ctll_au_ax
      end; rewrite unfold_entailsL; left
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctlr_af_ax
      | _ => rewrite ctlr_au_ax
      end; rewrite unfold_entailsR; left
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctll_ef_ex
      | _ => rewrite ctll_eu_ex
      end; rewrite unfold_entailsL; left
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctlr_ef_ex
      | _ => rewrite ctlr_eu_ex
      end; rewrite unfold_entailsR; left
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
  | |- @entailsR ?M ?W ?HE ?KMS ?X (COrLR ?p ?q) ?t ?w =>
      rewrite ctlr_orl; right
  | |- @entailsR ?M ?W ?HE ?KMS ?X (COrRR ?p ?q) ?t ?w =>
      rewrite ctlr_orr; right

  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctll_af_ax
      | _ => rewrite ctll_au_ax
      end; rewrite unfold_entailsL; right
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctlr_af_ax
      | _ => rewrite ctlr_au_ax
      end; rewrite unfold_entailsR; right
  | |- @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctll_ef_ex
      | _ => rewrite ctll_eu_ex
      end; rewrite unfold_entailsL; right
  | |- @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctlr_ef_ex
      | _ => rewrite ctlr_eu_ex
      end; rewrite unfold_entailsR; right
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
      rewrite ctlr_andr in H; destruct H as [Hp Hq]
  | <[ ?t, ?w |= ?p ∩ ?q ]> =>
      let Hp := fresh "H"p in
      let Hq := fresh "H"q in
      rewrite ctlr_andl in H; destruct H as [Hp Hq]
  (* OR *)                                         
  | <( ?t, ?w |= ?p \/ ?q )> =>
      rewrite ctll_or in H; destruct H as [H | H]
  | <[ ?t, ?w |= ?p \/ ?q ]> =>
      rewrite ctlr_orr in H; destruct H as [H | H]
  | <[ ?t, ?w |= ?p ∪ ?q ]> =>
      rewrite ctlr_orl in H; destruct H as [H | H]
  (* IMPL *)
  | <[ ?t, ?w |= ?p -> ?q ]> =>
      rewrite ctlr_impll in H
  (* X *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_A ?φ) ?t ?w =>
      let Hs' := fresh "Hs" in
      rewrite ctll_ax in H; destruct H as (Hs' & H)
  | @entailsL ?M ?W ?HE ?KMS ?X (CxL Q_E ?φ) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite ctll_ex in H; destruct H as (t' & w' & TR' & H)
  | @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_A ?φ) ?t ?w =>
      let Hs' := fresh "Hs" in
      rewrite ctlr_ax in H; destruct H as (Hs' & H)
  | @entailsR ?M ?W ?HE ?KMS ?X (CxR Q_E ?φ) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite ctlr_ex in H; destruct H as (t' & w' & TR' & H)
  (* Quantifier is a variable, destruct it *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CxL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  | @entailsR ?M ?W ?HE ?KMS ?X (CxR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  (* U *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_A ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctll_af_ax in H
      | _ => rewrite ctll_au_ax in H; rewrite unfold_entailsL in H; destruct H
      end
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_A ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctlr_af_ax in H
      | _ => rewrite ctlr_au_ax in H; rewrite unfold_entailsR in H; destruct H
      end
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_E ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctll_ef_ex
      | _ => rewrite ctll_eu_ex; rewrite unfold_entailsL; destruct H
      end
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_E ?p ?q) ?t ?w =>
      match p with
      | <( ⊤ )> => rewrite ctlr_ef_ex
      | _ => rewrite ctlr_eu_ex; rewrite unfold_entailsR; right
      end
  (* Quantifier is a variable, destruct it *)
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR ?c ?p ?q) ?t ?w =>
      is_var c; destruct c; cdestruct H

  (* G *)          
  | @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_A ?φ) ?t ?w =>
      let Hp := fresh "H"φ in
      rewrite ctll_ag_ax, unfold_entailsL in H; destruct H as [Hp H]
  | @entailsL ?M ?W ?HE ?KMS ?X (Cg Q_E ?φ) ?t ?w =>
      let Hp := fresh "H"φ in
      rewrite ctll_eg_ex, unfold_entailsL in H; destruct H as [Hp H]
  | @entailsL ?M ?W ?HE ?KMS ?X (Cg ?c ?p) ?t ?w =>
      is_var c; destruct c; cdestruct H
  end.
