From Stdlib Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Setoid
  CTree.Logic.EX
  Logic.Core.

Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** * TICL logic lemmas on ctrees and the exists-always [EG] operator *)
Section BasicLemmas.
  Context {E B: Type -> Type} {X: Type}.

  (** A visible event satisfies [EG φ] if and only if it satisfies [φ] and its continuation [k v] satisfies [EG φ] for some [v]. *)
  Lemma eg_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) w φ,
      (<( {Vis e k}, w |= φ )> /\ exists v, <( {k v}, {Obs e v} |= EG φ )>) <->
         <( {Vis e k}, w |= EG φ )>.
  Proof.
    split; intros.
    - destruct H as (Hφ & v & H).
      csplit; eauto with ticl.
      exists (k v), (Obs e v); split; eauto with ticl.
      apply ticll_not_done in Hφ.
      apply ktrans_vis.
      exists v; split2; eauto with ticl.
    - cdestruct H.
      split; eauto with ticl.
      apply ktrans_vis in TR as (v & -> & Heqt & ?).
      rewrite <- Heqt in H.
      exists v.
      apply H.
  Qed.

  (** A visible branch satisfies [EG φ] if and only if it satisfies [φ] and its continuation [k y] satisfies [EG φ] for some [y]. *)
  Lemma eg_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ,
      (<( {BrS c k}, w |= φ )> /\ exists (y: Y), <( {k y}, w |= EG φ )>) <->
        <( {BrS c k}, w |= EG φ )>.
  Proof.
    split; intros.
    - destruct H as (Hφ & y & H).
      csplit; eauto with ticl.
      exists (k y), w; split; eauto with ticl.
      apply ticll_not_done in Hφ.
      apply ktrans_brS.
      exists y; eauto with ticl.
    - cdestruct H.
      apply ktrans_brS in TR as (y & Heqt & -> & ?).
      split; eauto with ticl.
      rewrite Heqt in H.
      exists y.
      apply H.
  Qed.

  (** A visible step satisfies [EG φ] if and only if it satisfies [φ] and its continuation satisfies [EG φ]. *)
  Lemma eg_step: forall (t: ctree E B X) w φ,
      (<( {Step t}, w |= φ )> /\ <( t, w |= EG φ )>) <->
        <( {Step t}, w |= EG φ )>.
  Proof.
    split; intros.
    - destruct H as (Hφ & H).
      csplit; eauto with ticl.
      exists t, w; split; eauto with ticl.
      apply ticll_not_done in Hφ.
      apply ktrans_step; eauto with ticl.
    - cdestruct H.
      apply ktrans_step in TR as (Heqt & -> & ?).
      split; eauto with ticl.
      now rewrite Heqt in H.
  Qed.

  (** A hidden branch satisfies [EG φ] if it satisfies [φ] and some branch has
      a successor satisfying [EG φ]. *)
  Lemma eg_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ,
      <( {Br c k}, w |= φ )> ->
      (exists y t' w', |k y, w| ↦ |t', w'| /\ <( t', w' |= EG φ )>) ->
      <( {Br c k}, w |= EG φ )>.
  Proof.
    intros * Hφ (y & t' & w' & TR & H).
    csplit; eauto with ticl.
    exists t', w'; split; eauto with ticl.
    apply ktrans_br; eauto with ticl.
  Qed.

  (** Inversion of [EG φ] at a hidden branch: some branch has a successor satisfying [EG φ]. *)
  Lemma eg_br_inv: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ,
      <( {Br c k}, w |= EG φ )> ->
      <( {Br c k}, w |= φ )> /\
      (exists y t' w', |k y, w| ↦ |t', w'| /\ <( t', w' |= EG φ )>).
  Proof.
    intros * H.
    cdestruct H; split; eauto with ticl.
    apply ktrans_br in TR as (y & TR); eauto with ticl.
  Qed.

  (** A stuck tree does not satisfy [EG φ]; it does not step. *)
  Lemma eg_stuck: forall w φ,
      ~ <( {Stuck: ctree E B X}, w |= EG φ )>.
  Proof.
    intros * H.
    cdestruct H; subst.
    now apply ktrans_stuck in TR.
  Qed.

  (** A return tree does not satisfy [EG φ]; it does not infinitely step. *)
  Lemma eg_ret: forall (x: X) w φ,
      ~ <( {Ret x: ctree E B X}, w |= EG φ )>.
  Proof.
    intros * H.
    cdestruct H.
    assert(Hd: not_done w) by now apply ticll_not_done in Hp.
    inv Hd.
    - apply ktrans_done in TR as (-> & Heqt).
      rewrite Heqt in H.
      now apply eg_stuck in H.
    - apply ktrans_finish in TR as (-> & Heqt).
      rewrite Heqt in H.
      now apply eg_stuck in H.
  Qed.

End BasicLemmas.
