From Coinduction Require Import
  coinduction tactics.

From CTree Require Import
  Utils.Utils
  Events.Core
  Logic.Syntax
  Logic.Semantics.

Import CtlNotations.
Local Open Scope ctl_scope.

Generalizable All Variables.


#[global] Tactic Notation "step" "in" ident(H) :=
  (lazymatch type of H with
   | @entailsF ?M ?W ?HE ?KMS ?X (Cg ?q ?φ) ?t ?w =>
       rewrite unfold_entailsF in H; step_in H
   end || step_in H).

#[global] Ltac step :=
  first [
      lazymatch goal with
      | |- @entailsF ?M ?W ?HE ?KMS ?X (Cg ?q ?φ) ?t ?w =>
          rewrite unfold_entailsF; red; step_
      end | red; step_ ].

#[global] Ltac csplit :=
  lazymatch goal with
  | |- <( ?t, ?w |= ?φ /\ ?ψ )> => rewrite unfold_entailsF; split
  | |- <( ?t, ?w |= AX ?φ )> => rewrite ctl_ax; split
  | |- <( ?t, ?w |= EX ?φ )> => rewrite ctl_ex
  | |- <( ?t, ?w |= prop ?φ )> => rewrite unfold_entailsF
  | |- <( ?t, ?w |= pure )> => rewrite ctl_pure                                     
  | |- <( ?t, ?w |= vis ?φ )> => rewrite ctl_vis
  | |- <( ?t, ?w |= now ?φ )> => rewrite ctl_now
  | |- <( ?t, ?w |= finish ?φ )> => rewrite ctl_finish
  | |- <( ?t, ?w |= done ?φ )> => rewrite ctl_done                                          
  end.

#[global] Ltac cleft :=
  match goal with
  | |- <( ?t, ?w |= ?φ \/ ?ψ )> => rewrite unfold_entailsF; left
  | |- <( ?t, ?w |= ?φ AU ?ψ )> => rewrite unfold_entailsF; apply StepA
  | |- <( ?t, ?w |= ?φ EU ?ψ )> => rewrite unfold_entailsF; apply StepE
  | |- <( ?t, ?w |= AG ?φ )> => step; cbn
  | |- <( ?t, ?w |= EG ?φ )> => step; cbn
  end.

#[global] Ltac cright :=
  match goal with
  | |- <( ?t, ?w |= ?φ \/ ?ψ )> => rewrite unfold_entailsF; right
  | |- <( ?t, ?w |= ?φ AU ?ψ )> => rewrite unfold_entailsF; apply MatchA
  | |- <( ?t, ?w |= ?φ EU ?ψ )> => rewrite unfold_entailsF; apply MatchE
  | |- <( ?t, ?w |= AG ?φ )> => step; cbn
  | |- <( ?t, ?w |= EG ?φ )> => step; cbn
  end.

#[global] Ltac cdestruct H0 :=
  match type of H0 with
  | <( ?t, ?w |= prop ?φ )> => rewrite unfold_entailsF in H0
  | <( ?t, ?w |= pure )> => rewrite ctl_pure in H0; subst
  | <( ?t, ?w |= vis ?φ )> =>
      let e := fresh "e" in
      let v := fresh "v" in
      rewrite ctl_vis in H0; destruct H0 as (e & v & ?)
  | <( ?t, ?w |= now ?φ )> => rewrite ctl_now in H0
  | <( ?t, ?w |= finish ?φ )> =>
      let e := fresh "e" in
      let v := fresh "v" in
      let x := fresh "x" in
      rewrite ctl_finish in H0; destruct H0 as (e & v & x & ?)
  | <( ?t, ?w |= done ?φ )> => rewrite ctl_done in H0
  | @entailsF ?M ?W ?HE ?KMS ?X (CProp ?φ) ?t ?w =>
      rewrite unfold_entailsF in H0
  | @entailsF ?M ?W ?HE ?KMS ?X (CNow ?φ) ?t ?w =>
      rewrite ctl_now in H0
  | @entailsF ?M ?W ?HE ?KMS ?X (CDone ?φ) ?t ?w =>
      rewrite ctl_done in H0
  | @entailsF ?M ?W ?HE ?KMS ?X (CAnd ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; destruct H0      
  | @entailsF ?M ?W ?HE ?KMS ?X (COr ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; destruct H0
  | @entailsF ?M ?W ?HE ?KMS ?X (Cx Q_A ?φ) ?t ?w =>
      let Hs' := fresh "Hs" in
      rewrite ctl_ax in H0; destruct H0 as (Hs' & H0)
  | @entailsF ?M ?W ?HE ?KMS ?X (Cx Q_E ?φ) ?t ?w =>
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite ctl_ex in H0; destruct H0 as (t' & w' & TR' & H0)
  | @entailsF ?M ?W ?HE ?KMS ?X (Cu ?q ?φ ?ψ) ?t ?w =>
      let t' := fresh "t" in
      remember t as t';
      rewrite unfold_entailsF in H0; destruct H0; subst      
  | @entailsF ?M ?W ?HE ?KMS ?X (Cg ?q ?φ) ?t ?w =>
      let t' := fresh "t" in
      remember t as t';
      rewrite unfold_entailsF in H0; step in H0; cbn in H0; subst
  end.

#[global] Ltac cinduction H0 :=
  match type of H0 with
  | @entailsF ?M ?W ?HE ?KMS ?X (Cu ?q ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsF in H0; induction H0
  end.

#[global] Ltac coinduction_g R CIH :=
  let R' := fresh R in
  try change (<( ?t, ?w |= AG ?p )>) with (cag (entailsF p) t w);
  try change (<( ?t, ?w |= EG ?p )>) with (ceg (entailsF p) t w);
  coinduction R' CIH;
  try change (cag (entailsF ?p) ?t ?w) with <( t, w |= AG p )> in *;
  try change (ceg (entailsF ?p) ?t ?w) with <( t, w |= EG p )> in *.

#[global] Tactic Notation "destruct" ident_list(H) :=
  (cdestruct H || destruct H).

#[global] Tactic Notation "left" := (cleft || left).
#[global] Tactic Notation "right" := (cright || right).
#[global] Tactic Notation "split" := (csplit || split).
#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  (coinduction_g R H || coinduction R H).
