From Stdlib Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  Logic.Core.

Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** * Lemmas on the structure of ctrees and the always [AG] operator *)
Section BasicLemmas.
  Context {E B: Type -> Type} {X: Type}.

  (** Vis iff lemma for always [AG] *)
  Lemma ag_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) (v: Y) w φ,
      (<( {Vis e k}, w |= φ )> /\ forall v, <( {k v}, {Obs e v} |= AG φ )>) <->
         <( {Vis e k}, w |= AG φ )>.
  Proof with eauto with ticl.
    split; intros.
    - destruct H as (Hφ & H).
      csplit...
      + apply ticll_not_done in Hφ.
        apply (can_step_vis e k v)...
      + intros t' w' TR.
        apply ktrans_vis in TR as (v' & -> & <- & ?)...
    - cdestruct H.
      split...
      intro v'.
      apply H, ktrans_vis...
  Qed.

  (** Visible branch iff lemma for always [AG] *)
  Lemma ag_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) w φ,
      (<( {BrS c k}, w |= φ )> /\ forall (y: Y), <( {k y}, w |= AG φ )>) <->
        <( {BrS c k}, w |= AG φ )>.
  Proof with eauto with ticl.
    split; intros.
    - destruct H as (Hφ & H).
      csplit...
      + apply ticll_not_done in Hφ.
        apply (can_step_brS c k y)...
      + intros t' w' TR.
        apply ktrans_brS in TR as (y' & Heq & -> & Hd).
        rewrite Heq; apply H.
    - cdestruct H.
      split...
      intro y'.
      apply H, ktrans_brS; exists y'...
  Qed.

  (** Visible step iff lemma for always [AG] *)
  Lemma ag_step: forall (t: ctree E B X) w φ,
      (<( {Step t}, w |= φ )> /\ <( t, w |= AG φ )>) <->
        <( {Step t}, w |= AG φ )>.
  Proof with eauto with ticl.
    split; intros.
    - destruct H as (Hφ & H).
      csplit...
      + apply ticll_not_done in Hφ.
        apply can_step_step...
      + intros t' w' TR.
        apply ktrans_step in TR as (Heq & -> & Hd).
        now rewrite Heq.
    - cdestruct H.
      split...
      apply H, ktrans_step...
  Qed.

  (** Hidden branch lemma for always [AG]: all successors of all branches
      satisfy [AG φ] and at least one branch can step. *)
  Lemma ag_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ,
      <( {Br c k}, w |= φ )> ->
      (exists y, can_step (k y) w) ->
      (forall y t' w', |k y, w| ↦ |t', w'| -> <( t', w' |= AG φ )>) ->
      <( {Br c k}, w |= AG φ )>.
  Proof with eauto with ticl.
    intros * Hφ Hs Hk; csplit...
    - now apply can_step_br.
    - intros t' w' TR.
      apply ktrans_br in TR as (y & TR)...
  Qed.

  (** Stuckness lemma for always [AG]: no AG formula for stuck as it doesn't step *)
  Lemma ag_stuck: forall w φ,
      ~ <( {Stuck: ctree E B X}, w |= AG φ )>.
  Proof.
    intros * H.
    cdestruct H; subst.
    now apply can_step_stuck in Hs.
  Qed.

  (** Return lemma for always [AG]: no AG formula for return as it doesn't step always *)
  Lemma ag_ret: forall (x: X) w φ,
      ~ <( {Ret x: ctree E B X}, w |= AG φ )>.
  Proof.
    intros * H.
    cdestruct H.
    destruct Hs as (t' & w' & TR).
    specialize (H _ _ TR).
    apply ticll_not_done in Hp.
    inv Hp.
    + apply ktrans_done in TR as (-> & ?).
      rewrite H0 in H.
      now apply ag_stuck in H.
    + apply ktrans_finish in TR as (-> & ?).
      rewrite H0 in H.
      now apply ag_stuck in H.
  Qed.

End BasicLemmas.
