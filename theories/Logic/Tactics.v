From Coinduction Require Import
  coinduction tactics.

From CTree Require Import
  Utils.Utils
  Events.Core
  Logic.Semantics.

Import CtlNotations.
Local Open Scope ctl_scope.

Generalizable All Variables.

#[global] Tactic Notation "step" "in" ident(H) :=
  (lazymatch type of H with
   | @entailsF ?M ?W ?HE ?KMS ?X (CAR ?φ ?ψ) ?t ?w =>
       rewrite unfold_entailsF in H; step_in H
   | @entailsF ?M ?W ?HE ?KMS ?X (CER ?φ ?ψ) ?t ?w =>
       rewrite unfold_entailsF in H; step_in H
   end || step_in H).

#[global] Ltac step :=
  first [
      lazymatch goal with
      | |- @entailsF ?M ?W ?HE ?KMS ?X (CAR ?φ ?ψ) ?t ?w =>
          rewrite unfold_entailsF; red; step_
      | |- @entailsF ?M ?W ?HE ?KMS ?X (CER ?φ ?ψ) ?t ?w =>
          rewrite unfold_entailsF; red; step_
      end | red; step_ ].

#[global] Ltac csplit :=
  lazymatch goal with
  | |- <( ?t, ?w |= ?φ /\ ?ψ )> => rewrite unfold_entailsF; split
  | |- <( ?t, ?w |= AX ?φ )> => rewrite unfold_ax; split
  | |- <( ?t, ?w |= AX ?φ )> => rewrite unfold_ex                                      
  end.

#[global] Ltac cleft :=
  match goal with
  | |- <( ?t, ?w |= ?φ \/ ?ψ )> => rewrite unfold_entailsF; left
  | |- <( ?t, ?w |= ?φ AU ?ψ )> => rewrite unfold_entailsF; apply StepA
  | |- <( ?t, ?w |= ?φ EU ?ψ )> => rewrite unfold_entailsF; apply StepE
  | |- <( ?t, ?w |= ?φ AR ?ψ )> => step; cbn; apply RStepA
  | |- <( ?t, ?w |= ?φ ER ?ψ )> => step; cbn; apply RStepE
  end.

#[global] Ltac cright :=
  match goal with
  | |- <( ?t, ?w |= ?φ \/ ?ψ )> => rewrite unfold_entailsF; right
  | |- <( ?t, ?w |= ?φ AU ?ψ )> => rewrite unfold_entailsF; apply MatchA
  | |- <( ?t, ?w |= ?φ EU ?ψ )> => rewrite unfold_entailsF; apply MatchE
  | |- <( ?t, ?w |= ?φ AR ?ψ )> => step; cbn; apply RMatchA
  | |- <( ?t, ?w |= ?φ ER ?ψ )> => step; cbn; apply RMatchE
  end.

#[global] Ltac cdestruct H0 :=
  match type of H0 with
  | @entailsF ?M ?W ?HE ?KMS ?X (CAnd ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; destruct H0      
  | @entailsF ?M ?W ?HE ?KMS ?X (COr ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; destruct H0
  | @entailsF ?M ?W ?HE ?KMS ?X (CAX ?φ) ?t ?w =>
      let Hs' := fresh "Hs" in
      rewrite unfold_ax in H0; destruct H0 as (Hs' & H0)
  | @entailsF ?M ?W ?HE ?KMS ?X (CEX ?φ) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite unfold_ex in H0; destruct H0 as (t' & w' & TR' & H0)
  | @entailsF ?M ?W ?HE ?KMS ?X (CAU ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; destruct H0
  | @entailsF ?M ?W ?HE ?KMS ?X (CEU ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; destruct H0
  | @entailsF ?M ?W ?HE ?KMS ?X (CAR ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; step in H0; cbn in H0; destruct H0
  | @entailsF ?M ?W ?HE ?KMS ?X (CER ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; step in H0; cbn in H0; destruct H0
  end.

#[global] Ltac cinduction H0 :=
  match type of H0 with
  | @entailsF ?M ?W ?HE ?KMS ?X (CAU ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; induction H0
  | @entailsF ?M ?W ?HE ?KMS ?X (CEU ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; induction H0
  end.

#[global] Ltac coinduction_g R CIH :=
  let R' := fresh R in
  try change (<( ?t, ?w |= ?p AR ?q )>) with (car (entailsF p) (entailsF q) t w);
  try change (<( ?t, ?w |= ?p ER ?q )>) with (cer (entailsF p) (entailsF q) t w);
  coinduction R' CIH;
  try change (car (entailsF ?p) (entailsF ?q) ?t ?w) with <( t, w |= p AR q )> in *;
  try change (cer (entailsF ?p) (entailsF ?q) ?t ?w) with <( t, w |= p ER q )> in *.

#[global] Tactic Notation "destruct" ident_list(H) :=
  (cdestruct H || destruct H).

#[global] Tactic Notation "left" := (cleft || left).
#[global] Tactic Notation "right" := (cright || right).
#[global] Tactic Notation "split" := (csplit || split).
#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  (coinduction_g R H || coinduction R H).
