From Coq Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
  
(*| CTL logic lemmas on c/itrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma done_ax: forall (t: ctree E X) φ ψ w,
      is_done X w ->
      ~ <( t, w |= φ AX ψ )>.
  Proof.
    intros * Hret Hcontra.
    cdestruct Hcontra.
    apply can_step_not_done in Hs.
    inv Hret; inv Hs.
  Qed.

  Lemma ax_stuck: forall w φ,
      <( {Ctree.stuck: ctree E X}, w |= AX φ )> ->
      <( {Ctree.stuck: ctree E X}, w |= φ )>.
  Proof.
    intros.
    cdestruct H.
    now apply can_step_stuck in Hs.
  Qed.

  Lemma ax_guard: forall (t: ctree E X) w φ,
      <( {Guard t}, w |= AX φ )> <->
      <( t, w |= AX φ )>.
  Proof.
    intros.
    now rewrite sb_guard.
  Qed.
  
  Lemma ax_br: forall n (k: fin' n -> ctree E X) w φ,
      <( {Br n k}, w |= AX φ )> <->
        not_done w /\ (forall (i: fin' n), <( {k i}, w |= φ )>).
  Proof with auto with ctl.
    split; intros.
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_br in Hs.
      split...
      intros i.
      apply H.
      apply ktrans_br.
      exists i...
    - destruct H; csplit.
      + apply can_step_br...
      + intros t' w' TR.
        apply ktrans_br in TR as (i & -> & -> & TR).
        apply H0.
  Qed.

  Lemma ax_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      <( {Vis e k}, w |= AX φ )> <->
        not_done w /\ (forall (v: encode e), <( {k v}, {Obs e v} |= φ )>).
  Proof with auto with ctl.
    split; intros.
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_vis in Hs.
      split...
      intros v.
      apply H.
      apply ktrans_vis.
      exists v...
    - destruct H; csplit.
      + apply can_step_vis...
      + intros t' w' TR.
        apply ktrans_vis in TR as (i & -> & <- & TR); subst.
        apply H0.
  Qed.

  Lemma ax_done_ret: forall (x: X) φ w,
      <[ {Ret x}, w |= AX done φ ]> <-> not_done w /\ φ x w. 
  Proof.
    split; intros.
    - cdestruct H.
      destruct Hs as (t' & w' & TR).
      specialize (H _ _ TR).
      split.
      + now apply ktrans_not_done with (Ret x) t' w'.
      + cbn in TR.
        dependent destruction TR; observe_equ x;
          rewrite <- Eqt in H0; now cdestruct H0.
    - destruct H; csplit.
      + now apply can_step_ret.
      + intros t' w' TR.
        inv H.
        * apply ktrans_done in TR as (-> & ->).
          now csplit.
        * apply ktrans_finish in TR as (-> & ->).
          now csplit.
  Qed.
  
  Lemma ax_done: forall (t: ctree E X) φ w,
      <[ t, w |= AX done φ ]> <-> not_done w /\ (exists (x: X), t ~ Ret x /\ φ x w).
  Proof.
    split; intros.
    - cdestruct H; destruct Hs as (t' & w' & TR).
      cbn in *.
      setoid_rewrite (ctree_eta t).
      remember (observe t) as T.
      specialize (H _ _ TR).
      rewrite (ctree_eta t') in H.
      remember (observe t') as T'.
      clear HeqT t HeqT' t'.
      dependent induction TR; intros.
      + setoid_rewrite <- (ctree_eta t) in IHTR.
        split.
        * now apply ktrans_not_done with t t' w'.
        * destruct (IHTR H).
          destruct H1 as (x & ? & ?).
          exists x; split; auto.
          now apply sb_guard_l.
      + inv H1; inv H.
      + inv H1.
      + split; auto with ctl.
        exists x; intuition.
        now cdestruct H0.
      + split; auto with ctl.
        exists x; intuition.
        now cdestruct H0.
    - destruct H as (Hw & x & Heq & H).
      rewrite Heq.
      apply ax_done_ret; intuition.
  Qed.
  
End BasicLemmas.

Section BindLemmas.
  Context {E: Type} {HE: Encode E}.

  Opaque Ctree.stuck.
  Theorem axl_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ R,
      <[ t, w |= AX done R ]> ->
      (forall x w, R x w -> <( {k x}, w |= AX φ )>) ->
      <( {x <- t ;; k x}, w |= AX φ )>.
  Proof with auto with ctl.
    intros.
    cdestruct H; csplit.
    - apply can_step_bind_r with R.
      + cleft; csplit...
      + intros t' w' HR.
        specialize (H0 _ _ HR).
        now cdestruct H0.
    - intros t' w' TR'. 
      apply ktrans_bind_inv in TR' as
          [(t_ & TR_ & Hd & ->) |
            (x & w_ & TR_ & Hr & TRk)].
      + specialize (H _ _ TR_).
        cdestruct H; inv Hd.
      + specialize (H _ _ TR_); inv Hr.

        (* HERE *)
        * apply ktrans_to_done_inv in TR_ as (_ & ->).
          
        specialize (H1 _ _ TR_).
        apply ctl_done in H1; inv H1; inv Hd.
      + next in H; destruct H.
        specialize (H1 _ _ TR_).
        apply ctl_done in H1.       
        dependent destruction H1; dependent destruction Hr.
        * specialize (H1 _ _ H0).
          next in H1.
          destruct H1 as (Hs & Ht').
          apply Ht'.
          now apply ktrans_to_done_inv in TR_ as (_ & ->). 
        * specialize (H1 _ _ H0).
          next in H1.
          destruct H1 as (Hs & Ht').
          apply Ht'.
          now apply ktrans_to_finish_inv in TR_ as (_ & ->). 
  Qed.
End BindLemmas.

