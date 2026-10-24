From Stdlib Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
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

  (** Stuckness lemma for prefix next [AN], there is no next step from stuck *)
  Lemma anl_stuck: forall w φ ψ,
      ~ <( {Stuck: ctree E B X}, w |= φ AN ψ )>.
  Proof.
    intros * H; cdestruct H.
    now apply can_step_stuck in Hs.
  Qed.

  (** Stuckness lemma for suffix next [AN], there is no next step from stuck *)
  Lemma anr_stuck: forall w φ ψ,
      ~ <[ {Stuck: ctree E B X}, w |= φ AN ψ ]>.
  Proof.
    intros * H; cdestruct H.
    now apply can_step_stuck in Hs.
  Qed.

  (** Hidden branch, prefix next [AN]: all successors of all branches satisfy [ψ],
      and at least one branch can step. *)
  Lemma anl_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      <( {Br c k}, w |= φ )> ->
      (exists y, can_step (k y) w) ->
      (forall y t' w', |k y, w| ↦ |t', w'| -> <( t', w' |= ψ )>) ->
      <( {Br c k}, w |= φ AN ψ )>.
  Proof.
    intros * Hφ Hs Hk; csplit; eauto with ticl.
    - now apply can_step_br.
    - intros t' w' TR.
      apply ktrans_br in TR as (y & TR); eauto with ticl.
  Qed.

  Lemma anr_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      <( {Br c k}, w |= φ )> ->
      (exists y, can_step (k y) w) ->
      (forall y t' w', |k y, w| ↦ |t', w'| -> <[ t', w' |= ψ ]>) ->
      <[ {Br c k}, w |= φ AN ψ ]>.
  Proof.
    intros * Hφ Hs Hk; csplit; eauto with ticl.
    - now apply can_step_br.
    - intros t' w' TR.
      apply ktrans_br in TR as (y & TR); eauto with ticl.
  Qed.

  (** Visible branch iff lemma for prefix next [AN] *)
  Lemma anl_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) w φ ψ,
      <( {BrS c k}, w |= φ AN ψ )> <->
        <( {BrS c k}, w |= φ)>
        /\ (forall (y: Y), <( {k y}, w |= ψ )>).
  Proof.
    split; intros.    
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_not_done in Hs.
      split; eauto with ticl.
      intros y'.
      apply H, ktrans_brS; exists y'; eauto with ticl.
    - destruct H; csplit; eauto with ticl.
      + apply (can_step_brS c k y); apply ticll_not_done in H; eauto with ticl.
      + intros t' w' TR.
        apply ktrans_brS in TR as (y' & Heq & -> & Hd).
        rewrite Heq; apply H0.
  Qed.

  (** Visible branch iff lemma for suffix next [AN] *)
  Lemma anr_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) w φ ψ,
      <[ {BrS c k}, w |= φ AN ψ ]> <->
        <( {BrS c k}, w |= φ)>
        /\ (forall (y: Y), <[ {k y}, w |= ψ ]>).
  Proof.
    split; intros.    
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_not_done in Hs.
      split; eauto with ticl.
      intros y'.
      apply H, ktrans_brS; exists y'; eauto with ticl.
    - destruct H; csplit; eauto with ticl.
      + apply (can_step_brS c k y); apply ticll_not_done in H; eauto with ticl.
      + intros t' w' TR.
        apply ktrans_brS in TR as (y' & Heq & -> & Hd).
        rewrite Heq; apply H0.
  Qed.

  (** Visible step iff lemma for prefix next [AN] *)
  Lemma anl_step: forall (t: ctree E B X) w φ ψ,
      <( {Step t}, w |= φ AN ψ )> <->
        <( {Step t}, w |= φ)> /\ <( t, w |= ψ )>.
  Proof.
    split; intros.    
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_not_done in Hs.
      split; eauto with ticl.
      apply H, ktrans_step; eauto with ticl.
    - destruct H; csplit; eauto with ticl.
      + apply can_step_step; apply ticll_not_done in H; eauto with ticl.
      + intros t' w' TR.
        apply ktrans_step in TR as (Heq & -> & Hd).
        now rewrite Heq.
  Qed.

  (** Visible step iff lemma for suffix next [AN] *)
  Lemma anr_step: forall (t: ctree E B X) w φ ψ,
      <[ {Step t}, w |= φ AN ψ ]> <->
        <( {Step t}, w |= φ)> /\ <[ t, w |= ψ ]>.
  Proof.
    split; intros.    
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_not_done in Hs.
      split; eauto with ticl.
      apply H, ktrans_step; eauto with ticl.
    - destruct H; csplit; eauto with ticl.
      + apply can_step_step; apply ticll_not_done in H; eauto with ticl.
      + intros t' w' TR.
        apply ktrans_step in TR as (Heq & -> & Hd).
        now rewrite Heq.
  Qed.

  (** Vis iff lemma for prefix next [AN] *)
  Lemma anl_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) (v: Y) w φ ψ,
      <( {Vis e k}, w |= φ AN ψ )> <->
        <( {Vis e k}, w |= φ )> /\ (forall (v: Y), <( {k v}, {Obs e v} |= ψ )>).
  Proof.
    split; intros.
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_not_done in Hs.
      split; eauto with ticl.
      intros v'.
      apply H, ktrans_vis; exists v'; eauto with ticl.
    - destruct H; csplit; eauto with ticl.
      + apply (can_step_vis e k v); eauto with ticl.
        now apply ticll_not_done in H.
      + intros t' w' TR.
        apply ktrans_vis in TR as (v' & -> & Heq & Hd).
        rewrite <- Heq; apply H0.
  Qed.

  (** Vis iff lemma for suffix next [AN] *)
  Lemma anr_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) (v: Y) w φ ψ,
      <[ {Vis e k}, w |= φ AN ψ ]> <->
        <( {Vis e k}, w |= φ )> /\ (forall (v: Y), <[ {k v}, {Obs e v} |= ψ ]>).
  Proof.
    split; intros.
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_not_done in Hs.
      split; eauto with ticl.
      intros v'.
      apply H, ktrans_vis; exists v'; eauto with ticl.
    - destruct H; csplit; eauto with ticl.
      + apply (can_step_vis e k v); eauto with ticl.
        now apply ticll_not_done in H.
      + intros t' w' TR.
        apply ktrans_vis in TR as (v' & -> & Heq & Hd).
        rewrite <- Heq; apply H0.
  Qed.

  (** [φ AN done= r w'] pins down the tree: it is strongly bisimilar to [Ret r]. *)
  Lemma anr_done_eq: forall (t: ctree E B X) φ (r: X) w w',
      <[ t, w |= φ AN done= r w' ]> ->
      <( t, w |= φ )> /\ w' = w /\ t ~ (Ret r: ctree E B X).
  Proof.
    intros * H.
    cdestruct H.
    assert (Hw: w' = w).
    { destruct Hs as (t' & w_ & TR); specialize (H _ _ TR); cdestruct H.
      - destruct H as (_ & ->); now apply ktrans_to_done_inv in TR as (_ & ->).
      - destruct H as (_ & ->); now apply ktrans_to_finish_inv in TR as (_ & ->). }
    subst.
    assert (Hret: <[ t, w |= ret= r w ]>).
    { apply ret_unfold; exists r; split; auto with ticl.
      csplit; auto with ticl.
      now apply can_step_not_done in Hs. }
    apply ret_sbisim in Hret as (x & (-> & _) & Heq).
    split2; auto with ticl.
  Qed.

  (** Any tree bisimilar to [Ret r] satisfies [φ AN done= r w]. *)
  Lemma anr_ret: forall (t: ctree E B X) (r: X) φ w,
      <( t, w |= φ )> ->
      t ~ (Ret r: ctree E B X) ->
      <[ t, w |= φ AN done= r w ]>.
  Proof.
    intros * Hφ Heq.
    pose proof (ticll_not_done _ _ _ _ Hφ) as Hd.
    rewrite Heq in Hφ |- *.
    csplit; auto with ticl.
    intros t' w' TR.
    inv Hd.
    - apply ktrans_done in TR as (-> & _); csplit; auto with ticl.
    - apply ktrans_finish in TR as (-> & _); csplit; auto with ticl.
  Qed.

  (** Helper for the suffix [AN done R] formula on a [Ret r] tree. *)
  Lemma anr_ret_done: forall (r: X) (R: rel X (World E)) φ w,
      <( {Ret r: ctree E B X}, w |= φ )> ->
      R r w ->
      <[ {Ret r: ctree E B X}, w |= φ AN done R ]>.
  Proof.
    intros * Hφ HR.
    pose proof (ticll_not_done _ _ _ _ Hφ) as Hd.
    csplit; auto with ticl.
    intros t' w' TR.
    inv Hd.
    - apply ktrans_done in TR as (-> & _); csplit; auto with ticl.
    - apply ktrans_finish in TR as (-> & _); csplit; auto with ticl.
  Qed.

  (** Return lemma for prefix next [AN], there is no prefix formula [ψ] for return *)
  Lemma anl_ret: forall (r: X) w φ ψ,
      ~ <( {Ret r: ctree E B X}, w |= φ AN ψ )>.
  Proof.
    intros * H.
    cdestruct H.
    destruct Hs as (t' & w' & TR).
    specialize (H _ _ TR).
    assert (Hd: not_done w) by now apply ktrans_not_done in TR.
    inv Hd.
    - apply ktrans_done in TR as (-> & Heqt); rewrite Heqt in H.
      apply ticll_not_done in H; inv H.
    - apply ktrans_finish in TR as (-> & Heqt); rewrite Heqt in H.
      apply ticll_not_done in H; inv H.
  Qed.

  (** Helper more succinct version of the [anr_ret_done] lemma for [AX] = [⊤ AN] *)
  Lemma axr_ret: forall (r: X) (R: rel X (World E)) w,
      not_done w ->
      R r w ->
      <[ {Ret r: ctree E B X}, w |= AX done R ]>.
  Proof.
    intros.
    apply anr_ret_done; auto with ticl.
    csplit; auto with ticl.
  Qed.
  
  (** Inversion lemma for the next [AN] operator on a [Ret r] tree. *)
  Lemma anr_ret_inv: forall (r: X) w φ ψ,
      <[ {Ret r: ctree E B X}, w |= φ AN ψ ]> ->
        <( {Ret r: ctree E B X}, w |= φ )>
        /\ exists (w': World E), done_with (fun x w' => x = r /\ w = w') w'
        /\ <[ {Stuck: ctree E B X}, w' |= ψ ]>.
  Proof.
    intros.
    cdestruct H.
    assert (Hd: not_done w) by now apply can_step_not_done in Hs.
    destruct Hs as (t' & w' & TR).
    specialize (H _ _ TR).
    inv Hd.
    + apply ktrans_done in TR as (-> & Heqt).
      rewrite Heqt in H.
      split; auto with ticl.
      exists (Done r); auto with ticl.
    + apply ktrans_finish in TR as (-> & Heqt).
      rewrite Heqt in H.
      split; auto with ticl.
      exists (Finish e v r); auto with ticl.
  Qed.
End BasicLemmas.
