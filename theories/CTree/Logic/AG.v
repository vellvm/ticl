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
  Lemma ag_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) (v: Y) w (φ : ticll E),
      (<( {Vis e k}, w |=L φ )> /\ forall v, <( {k v}, {Obs e v} |=L AG φ )>) <->
         <( {Vis e k}, w |=L AG φ )>.
  Proof.
    ticl_normalize.
    split; intros.
    - destruct H as (Hφ & H).
      csplit; eauto with ticl.
      + apply ticl_not_done in Hφ.
        apply (can_step_vis e k v); eauto with ticl.
      + intros t' w' TR.
        apply ktrans_vis in TR as (v' & -> & <- & ?); eauto with ticl.
    - cdestruct H.
      split; eauto with ticl.
      intro v'.
      apply H, ktrans_vis; eauto with ticl.
  Qed.

  (** Visible branch iff lemma for always [AG] *)
  Lemma ag_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) w (φ : ticll E),
      (<( {BrS c k}, w |=L φ )> /\ forall (y: Y), <( {k y}, w |=L AG φ )>) <->
        <( {BrS c k}, w |=L AG φ )>.
  Proof.
    ticl_normalize.
    split; intros.
    - destruct H as (Hφ & H).
      csplit; eauto with ticl.
      + apply ticl_not_done in Hφ.
        apply (can_step_brS c k y); eauto with ticl.
      + intros t' w' TR.
        apply ktrans_brS in TR as (y' & Heq & -> & Hd).
        rewrite Heq; apply H.
    - cdestruct H.
      split; eauto with ticl.
      intro y'.
      apply H, ktrans_brS; exists y'; eauto with ticl.
  Qed.

  (** Visible step iff lemma for always [AG] *)
  Lemma ag_step: forall (t: ctree E B X) w (φ : ticll E),
      (<( {Step t}, w |=L φ )> /\ <( t, w |=L AG φ )>) <->
        <( {Step t}, w |=L AG φ )>.
  Proof.
    ticl_normalize.
    split; intros.
    - destruct H as (Hφ & H).
      csplit; eauto with ticl.
      + apply ticl_not_done in Hφ.
        apply can_step_step; eauto with ticl.
      + intros t' w' TR.
        apply ktrans_step in TR as (Heq & -> & Hd).
        now rewrite Heq.
    - cdestruct H.
      split; eauto with ticl.
      apply H, ktrans_step; eauto with ticl.
  Qed.

  (** Hidden branch lemma for always [AG]: all successors of all branches
      satisfy [AG φ] and at least one branch can step. *)
  Lemma ag_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w (φ : ticll E),
      <( {Br c k}, w |=L φ )> ->
      (exists y, can_step (k y) w) ->
      (forall y t' w', |k y, w| ↦ |t', w'| -> <( t', w' |=L AG φ )>) ->
      <( {Br c k}, w |=L AG φ )>.
  Proof.
    ticl_normalize.
    intros * Hφ Hs Hk; csplit; eauto with ticl.
    - now apply can_step_br.
    - intros t' w' TR.
      apply ktrans_br in TR as (y & TR); eauto with ticl.
  Qed.

  (** Stuckness lemma for always [AG]: no AG formula for stuck as it doesn't step *)
  Lemma ag_stuck: forall w (φ : ticll E),
      ~ <( {Stuck: ctree E B X}, w |=L AG φ )>.
  Proof.
    intros * H.
    cdestruct H; subst.
    now apply can_step_stuck in Hs.
  Qed.

  (** Return lemma for always [AG]: no AG formula for return as it doesn't step always *)
  Lemma ag_ret: forall (x: X) w (φ : ticll E),
      ~ <( {Ret x: ctree E B X}, w |=L AG φ )>.
  Proof.
    intros * H.
    cdestruct H.
    destruct Hs as (t' & w' & TR).
    specialize (H _ _ TR).
    apply ticl_not_done in Hp.
    inv Hp.
    + apply ktrans_done in TR as (-> & ?).
      rewrite H0 in H.
      now apply ag_stuck in H.
    + apply ktrans_finish in TR as (-> & ?).
      rewrite H0 in H.
      now apply ag_stuck in H.
  Qed.

End BasicLemmas.

(** Silent divergence has no productive global derivation. *)
Lemma guard_fixed_no_ag {E B : Type -> Type} {X : Type} (t : ctree E B X) w φ :
  t ≅ Guard t -> ~ <( t, w |=L AG φ )>.
Proof.
  intros Ht H; cdestruct H.
  destruct Hs as (t' & w' & TR).
  apply ktrans_trans in TR as (l & TR & _).
  rewrite (guard_fixed_spin t Ht) in TR.
  eapply spin_is_stuck; exact TR.
Qed.
