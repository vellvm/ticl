From Stdlib Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Events.Writer
  Logic.Core
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.
  
(** * TICL logic lemmas on ctrees and the exists-next [EX] operator *)
Section BasicLemmas.
  Context {E B: Type -> Type} {X: Type}.

  (** A stuck tree does not satisfy [φ EN ψ], at either formula mode. *)
  Lemma en_stuck: forall {b: bool} w (φ: ticll E) (ψ: ticl_at E X b),
      ~ entails X b (Cx Q_E φ ψ) (Stuck: ctree E B X) w.
  Proof.
    intros * H; cdestruct H.
    now apply ktrans_stuck in TR.
  Qed.

  (** Hidden branching retains a transition from the selected branch. *)
  Lemma en_br: forall {b: bool} {Y} (c: B Y) (k: Y -> ctree E B X)
      w (φ: ticll E) (ψ: ticl_at E X b),
      entails X b (Cx Q_E φ ψ) (Br c k) w <->
        entails X false φ (Br c k) w
        /\ (exists (y: Y) t' w', |k y, w| ↦ |t', w'| /\ entails X b ψ t' w').
  Proof.
    split; intros.
    - cdestruct H; split; eauto with ticl.
      apply ktrans_br in TR as (y & TR); eauto with ticl.
    - destruct H as (Hφ & y & t' & w' & TR & H).
      csplit; eauto with ticl.
      exists t', w'; split; eauto with ticl.
      apply ktrans_br; eauto with ticl.
  Qed.

  (** Visible branching exposes a successor satisfying the indexed target. *)
  Lemma en_brS: forall {b: bool} {Y} (c: B Y) (k: Y -> ctree E B X)
      w (φ: ticll E) (ψ: ticl_at E X b),
      entails X b (Cx Q_E φ ψ) (BrS c k) w <->
        entails X false φ (BrS c k) w
        /\ (exists (y: Y), entails X b ψ (k y) w).
  Proof.
    split; intros.
    - cdestruct H.
      apply ktrans_brS in TR as (y & Heq & -> & Hd).
      rewrite Heq in H; split; eauto with ticl.
    - destruct H as (Hφ & y & H).
      csplit; eauto with ticl.
      exists (k y), w; split; eauto with ticl.
      apply ktrans_brS; exists y; split2; eauto with ticl.
      now apply ticl_not_done in Hφ.
  Qed.

  (** A visible step exposes its continuation at the same world. *)
  Lemma en_step: forall {b: bool} (t: ctree E B X)
      w (φ: ticll E) (ψ: ticl_at E X b),
      entails X b (Cx Q_E φ ψ) (Step t) w <->
        entails X false φ (Step t) w /\ entails X b ψ t w.
  Proof.
    split; intros.
    - cdestruct H.
      apply ktrans_step in TR as (Heq & -> & Hd).
      rewrite Heq in H; split; eauto with ticl.
    - destruct H as (Hφ & H).
      csplit; eauto with ticl.
      exists t, w; split; eauto with ticl.
      apply ktrans_step; split2; eauto with ticl.
      now apply ticl_not_done in Hφ.
  Qed.

  (** Visible events expose the selected response and its observation world. *)
  Lemma en_vis: forall {b: bool} {Y} (e: E Y) (k: Y -> ctree E B X)
      w (φ: ticll E) (ψ: ticl_at E X b),
      entails X b (Cx Q_E φ ψ) (Vis e k) w <->
        entails X false φ (Vis e k) w /\ (exists (v: Y), entails X b ψ (k v) (Obs e v)).
  Proof.
    split; intros.
    - cdestruct H.
      apply ktrans_vis in TR as (v & -> & Heq & Hd).
      rewrite <- Heq in H; split; eauto with ticl.
    - destruct H as (Hφ & v & H).
      csplit; eauto with ticl.
      exists (k v), (Obs e v); split; eauto with ticl.
      apply ktrans_vis; exists v; split2; eauto with ticl.
      now apply ticl_not_done in Hφ.
  Qed.

  (** Return completion cannot satisfy an indexed next target. *)
  Lemma en_ret: forall {b: bool} (r: X) w (φ: ticll E) (ψ: ticl_at E X b),
      ~ entails X b (Cx Q_E φ ψ) (Ret r: ctree E B X) w.
  Proof.
    intros * H.
    cdestruct H.
    assert (Hd: not_done w) by now apply ktrans_not_done in TR.
    inv Hd.
    - apply ktrans_done in TR as (-> & Heqt); rewrite Heqt in H.
      apply ticl_not_done in H; inv H.
    - apply ktrans_finish in TR as (-> & Heqt); rewrite Heqt in H.
      apply ticl_not_done in H; inv H.
  Qed.

End BasicLemmas.

Section WriterLemmas.
  Context {B: Type -> Type}.

  (** Convenience lemma for the [EX] operator and the [log] event. *)
  Lemma exr_log{S}: forall (x: S) w,
      not_done w ->
      <( {log x: ctreeW S B unit}, w |=R EX ret=tt {Obs (Log x) tt} )>.
  Proof.
    intros; ticl_normalize.
    unfold log, CTree.trigger.
    apply (en_vis (b:=true)); split.
    - csplit; eauto with ticl.
    - exists tt.
      apply ret_ret; eauto with ticl.
  Qed.

End WriterLemmas.
