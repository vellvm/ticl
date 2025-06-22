From TICL Require Import
  ICTree.Core
  ICTree.Trans
  ICTree.Equ.

From TICL Require Export
  ICTree.SBisim.Core
  ICTree.SBisim.SSim.

From Stdlib Require Import
  Classes.Morphisms
  Basics
  Program.Equality
  Classes.SetoidClass
  Classes.RelationPairs
  Vectors.Fin.

Local Open Scope ictree_scope.
Generalizable All Variables.

Global Typeclasses Opaque sbisim.
Global Typeclasses Opaque ssim.

(** * Re-export tactics from Equ/SBisim/SSim *)
#[global] Tactic Notation "step" :=
  __step_equ || __step_sbisim || __step_ssim || step.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  __coinduction_equ R H || __coinduction_sbisim R H || __coinduction_ssim R H || coinduction R H.

#[global] Tactic Notation "step" "in" ident(H) :=
  __step_equ_in H || __step_in_sbisim H || __step_in_ssim H || step in H.

(** Lemma relating [trans] and strong bisimulation [sbisim]*)
Lemma sbisim_trans `{HE: Encode E} {X}:
  forall (s t s': ictree E X) l (L: rel _ _),
    s (~ L) t ->
    trans l s s' ->
    exists l' t', trans l' t t' /\ L l l' /\ s' (~ L) t'.
Proof.
  intros * EQ TR.
  step in EQ; cbn in EQ; destruct EQ.
  destruct (H _ _ TR) as (l' & t' & TR' & Hsb & Hl).
  exists l', t'; auto.
Qed.

(** Lemma relating [trans] and strong simulation [ssim]*)
Lemma ssim_trans `{HE: Encode E} {X}:
  forall (s t s': ictree E X) l (L: rel _ _),
    s (≲ L) t ->
    trans l s s' ->
    exists l' t', trans l' t t' /\ L l l' /\ s' (≲ L) t'.
Proof.
  intros * H TR.
  step in H; cbn in H.
  destruct (H _ _ TR) as (l' & t' & TR' & Hsb & Hl).
  exists l', t'; auto.
Qed.
