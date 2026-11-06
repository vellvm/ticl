From Stdlib Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Interp.Yield.Mod
  CTree.Logic.CanStep
  CTree.Logic.EX
  CTree.Events.Writer
  Logic.Core
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.
  
(** * TICL logic lemmas on ctrees and the next [AN] operator *)
Section BasicLemmas.
  Context {E B: Type -> Type} {X: Type}.

  (** Stuck has no next step, independently of the target formula's mode. *)
  Lemma an_stuck: forall {b: bool} w (phi: ticll E) (psi: ticl_at E X b),
      ~ entails X b (Cx Q_A phi psi) (Stuck: ctree E B X) w.
  Proof.
    intros * H; cdestruct H.
    now apply can_step_stuck in Hs.
  Qed.

  (** Hidden branching requires an actual transition from at least one branch. *)
  Lemma an_br: forall {b: bool} {Y} (c: B Y) (k: Y -> ctree E B X)
      w (phi: ticll E) (psi: ticl_at E X b),
      entails X false phi (Br c k) w ->
      (exists y, can_step (k y) w) ->
      (forall y t' w', |k y, w| ↦ |t', w'| -> entails X b psi t' w') ->
      entails X b (Cx Q_A phi psi) (Br c k) w.
  Proof.
    intros * Hphi Hs Hk; csplit; eauto with ticl.
    - now apply can_step_br.
    - intros t' w' TR.
      apply ktrans_br in TR as (y & TR); eauto with ticl.
  Qed.

  (** Policy alternatives crawl through an actual transition of a branch. *)
  Lemma an_br_alts `{Bn -< B}: forall {b : bool} m
      (k : Fin.t (S m) -> ctree E B X) w (phi : ticll E) (psi : ticl_at E X b),
      entails X false phi (br_alts m k) w ->
      (exists a, can_step (k a) w) ->
      (forall a t' w', |k a, w| ↦ |t', w'| -> entails X b psi t' w') ->
      entails X b (Cx Q_A phi psi) (br_alts m k) w.
  Proof.
    intros * Hphi Hs Hk; csplit; eauto with ticl.
    - now apply can_step_br_alts.
    - intros t' w' TR.
      apply ktrans_br_alts in TR as (a & TR); eauto with ticl.
  Qed.

  (** Visible branching retains an explicit inhabitant to witness progress. *)
  Lemma an_brS: forall {b: bool} {Y} (c: B Y) (k: Y -> ctree E B X)
      (y: Y) w (phi: ticll E) (psi: ticl_at E X b),
      entails X b (Cx Q_A phi psi) (BrS c k) w <->
        entails X false phi (BrS c k) w
        /\ (forall (y: Y), entails X b psi (k y) w).
  Proof.
    split; intros.
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_not_done in Hs.
      split; eauto with ticl.
      intros y'.
      apply H, ktrans_brS; exists y'; eauto with ticl.
    - destruct H; csplit; eauto with ticl.
      + apply (can_step_brS c k y); apply ticl_not_done in H; eauto with ticl.
      + intros t' w' TR.
        apply ktrans_brS in TR as (y' & Heq & -> & Hd).
        rewrite Heq; apply H0.
  Qed.

  (** Visible step iff lemma for indexed next [AN]. *)
  Lemma an_step: forall {b: bool} (t: ctree E B X)
      w (phi: ticll E) (psi: ticl_at E X b),
      entails X b (Cx Q_A phi psi) (Step t) w <->
        entails X false phi (Step t) w /\ entails X b psi t w.
  Proof.
    split; intros.
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_not_done in Hs.
      split; eauto with ticl.
      apply H, ktrans_step; eauto with ticl.
    - destruct H; csplit; eauto with ticl.
      + apply can_step_step; apply ticl_not_done in H; eauto with ticl.
      + intros t' w' TR.
        apply ktrans_step in TR as (Heq & -> & Hd).
        now rewrite Heq.
  Qed.

  (** Visible events retain an explicit result inhabitant to witness progress. *)
  Lemma an_vis: forall {b: bool} {Y} (e: E Y) (k: Y -> ctree E B X)
      (v: Y) w (phi: ticll E) (psi: ticl_at E X b),
      entails X b (Cx Q_A phi psi) (Vis e k) w <->
        entails X false phi (Vis e k) w /\ (forall (v: Y), entails X b psi (k v) (Obs e v)).
  Proof.
    split; intros.
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_not_done in Hs.
      split; eauto with ticl.
      intros v'.
      apply H, ktrans_vis; exists v'; eauto with ticl.
    - destruct H; csplit; eauto with ticl.
      + apply (can_step_vis e k v); eauto with ticl.
        now apply ticl_not_done in H.
      + intros t' w' TR.
        apply ktrans_vis in TR as (v' & -> & Heq & Hd).
        rewrite <- Heq; apply H0.
  Qed.

  (** Completion successors cannot satisfy a formula in either mode. *)
  Lemma an_ret: forall {b: bool} (r: X) w (phi: ticll E) (psi: ticl_at E X b),
      ~ entails X b (Cx Q_A phi psi) (Ret r: ctree E B X) w.
  Proof.
    intros * H.
    cdestruct H.
    destruct Hs as (t' & w' & TR).
    specialize (H _ _ TR).
    assert (Hd: not_done w) by now apply ktrans_not_done in TR.
    inv Hd.
    - apply ktrans_done in TR as (-> & Heqt); rewrite Heqt in H.
      apply ticl_not_done in H; inv H.
    - apply ktrans_finish in TR as (-> & Heqt); rewrite Heqt in H.
      apply ticl_not_done in H; inv H.
  Qed.

End BasicLemmas.
