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

  (** A stuck tree satisfies prefix [φ EN ψ] if and only if it satisfies [ψ]. *)
  Lemma enl_stuck: forall w φ ψ,
      <( {Stuck: ctree E B X}, w |= φ EN ψ )> ->
      <( {Stuck: ctree E B X}, w |= ψ )>.
  Proof.
    intros * H; cdestruct H.
    now apply ktrans_stuck in TR.
  Qed.

  (** Hidden branch: [φ EN ψ] holds at [Br c k] iff [φ] holds there and some
      branch has a successor satisfying [ψ]. *)
  Lemma enl_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      <( {Br c k}, w |= φ EN ψ )> <->
        <( {Br c k}, w |= φ )>
        /\ (exists (y: Y) t' w', |k y, w| ↦ |t', w'| /\ <( t', w' |= ψ )>).
  Proof.
    split; intros.
    - cdestruct H; split; eauto with ticl.
      apply ktrans_br in TR as (y & TR); eauto with ticl.
    - destruct H as (Hφ & y & t' & w' & TR & H).
      csplit; eauto with ticl.
      exists t', w'; split; eauto with ticl.
      apply ktrans_br; eauto with ticl.
  Qed.

  (** Visible branch: [φ EN ψ] holds at [BrS c k] iff [φ] holds and some branch satisfies [ψ]. *)
  Lemma enl_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      <( {BrS c k}, w |= φ EN ψ )> <->
        <( {BrS c k}, w |= φ )>
        /\ (exists (y: Y), <( {k y}, w |= ψ )>).
  Proof.
    split; intros.
    - cdestruct H.
      apply ktrans_brS in TR as (y & Heq & -> & Hd).
      rewrite Heq in H; split; eauto with ticl.
    - destruct H as (Hφ & y & H).
      csplit; eauto with ticl.
      exists (k y), w; split; eauto with ticl.
      apply ktrans_brS; exists y; split2; eauto with ticl.
      now apply ticll_not_done in Hφ.
  Qed.

  (** Visible step: [φ EN ψ] holds at [Step t] iff [φ] holds and [t] satisfies [ψ]. *)
  Lemma enl_step: forall (t: ctree E B X) w φ ψ,
      <( {Step t}, w |= φ EN ψ )> <->
        <( {Step t}, w |= φ )> /\ <( t, w |= ψ )>.
  Proof.
    split; intros.
    - cdestruct H.
      apply ktrans_step in TR as (Heq & -> & Hd).
      rewrite Heq in H; split; eauto with ticl.
    - destruct H as (Hφ & H).
      csplit; eauto with ticl.
      exists t, w; split; eauto with ticl.
      apply ktrans_step; split2; eauto with ticl.
      now apply ticll_not_done in Hφ.
  Qed.

  (** Vis iff lemma for prefix next [EN] *)
  Lemma enl_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) w φ ψ,
      <( {Vis e k}, w |= φ EN ψ )> <->
        <( {Vis e k}, w |= φ )> /\ (exists (v: Y), <( {k v}, {Obs e v} |= ψ )>).
  Proof.
    split; intros.
    - cdestruct H.
      apply ktrans_vis in TR as (v & -> & Heq & Hd).
      rewrite <- Heq in H; split; eauto with ticl.
    - destruct H as (Hφ & v & H).
      csplit; eauto with ticl.
      exists (k v), (Obs e v); split; eauto with ticl.
      apply ktrans_vis; exists v; split2; eauto with ticl.
      now apply ticll_not_done in Hφ.
  Qed.

  (** A stuck tree does not satisfy suffix [φ EN ψ]. *)
  Lemma enr_stuck: forall w φ ψ,
      ~ <[ {Stuck: ctree E B X}, w |= φ EN ψ ]>.
  Proof.
    intros * H; cdestruct H.
    now apply ktrans_stuck in TR.
  Qed.

  Lemma enr_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      <[ {Br c k}, w |= φ EN ψ ]> <->
        <( {Br c k}, w |= φ )>
        /\ (exists (y: Y) t' w', |k y, w| ↦ |t', w'| /\ <[ t', w' |= ψ ]>).
  Proof.
    split; intros.
    - cdestruct H; split; eauto with ticl.
      apply ktrans_br in TR as (y & TR); eauto with ticl.
    - destruct H as (Hφ & y & t' & w' & TR & H).
      csplit; eauto with ticl.
      exists t', w'; split; eauto with ticl.
      apply ktrans_br; eauto with ticl.
  Qed.

  Lemma enr_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      <[ {BrS c k}, w |= φ EN ψ ]> <->
        <( {BrS c k}, w |= φ )>
        /\ (exists (y: Y), <[ {k y}, w |= ψ ]>).
  Proof.
    split; intros.
    - cdestruct H.
      apply ktrans_brS in TR as (y & Heq & -> & Hd).
      rewrite Heq in H; split; eauto with ticl.
    - destruct H as (Hφ & y & H).
      csplit; eauto with ticl.
      exists (k y), w; split; eauto with ticl.
      apply ktrans_brS; exists y; split2; eauto with ticl.
      now apply ticll_not_done in Hφ.
  Qed.

  Lemma enr_step: forall (t: ctree E B X) w φ ψ,
      <[ {Step t}, w |= φ EN ψ ]> <->
        <( {Step t}, w |= φ )> /\ <[ t, w |= ψ ]>.
  Proof.
    split; intros.
    - cdestruct H.
      apply ktrans_step in TR as (Heq & -> & Hd).
      rewrite Heq in H; split; eauto with ticl.
    - destruct H as (Hφ & H).
      csplit; eauto with ticl.
      exists t, w; split; eauto with ticl.
      apply ktrans_step; split2; eauto with ticl.
      now apply ticll_not_done in Hφ.
  Qed.

  (** Vis iff lemma for suffix next [EN] *)
  Lemma enr_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) w φ ψ,
      <[ {Vis e k}, w |= φ EN ψ ]> <->
        <( {Vis e k}, w |= φ )> /\ (exists (v: Y), <[ {k v}, {Obs e v} |= ψ ]>).
  Proof.
    split; intros.
    - cdestruct H.
      apply ktrans_vis in TR as (v & -> & Heq & Hd).
      rewrite <- Heq in H; split; eauto with ticl.
    - destruct H as (Hφ & v & H).
      csplit; eauto with ticl.
      exists (k v), (Obs e v); split; eauto with ticl.
      apply ktrans_vis; exists v; split2; eauto with ticl.
      now apply ticll_not_done in Hφ.
  Qed.


  (** A return tree does not satisfy prefix [φ EN ψ]; it does not step. *)
  Lemma enl_ret: forall (r: X) w φ ψ,
      ~ <( {Ret r: ctree E B X}, w |= φ EN ψ )>.
  Proof.
    intros * H.
    cdestruct H.
    assert (Hd: not_done w) by now apply ktrans_not_done in TR.
    inv Hd.
    - apply ktrans_done in TR as (-> & Heqt); rewrite Heqt in H.
      apply ticll_not_done in H; inv H.
    - apply ktrans_finish in TR as (-> & Heqt); rewrite Heqt in H.
      apply ticll_not_done in H; inv H.
  Qed.

End BasicLemmas.

Section WriterLemmas.
  Context {B: Type -> Type}.

  (** Convenience lemma for the [EX] operator and the [log] event. *)
  Lemma exr_log{S}: forall (x: S) w,
      not_done w ->
      <[ {log x: ctreeW S B unit}, w |= EX ret=tt {Obs (Log x) tt} ]>.
  Proof.
    intros.
    unfold log, CTree.trigger.
    apply enr_vis; split.
    - csplit; eauto with ticl.
    - exists tt.
      apply ret_ret; eauto with ticl.
  Qed.

End WriterLemmas.
