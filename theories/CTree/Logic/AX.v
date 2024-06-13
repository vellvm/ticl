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

  Lemma axl_stuck: forall w φ ψ,
      ~ <( {Ctree.stuck: ctree E X}, w |= φ AX ψ )>.
  Proof.
    intros * H; cdestruct H.
    now apply can_step_stuck in Hs.
  Qed.

  Lemma axr_stuck: forall w φ ψ,
      ~ <[ {Ctree.stuck: ctree E X}, w |= φ AX ψ ]>.
  Proof.
    intros * H; cdestruct H.
    now apply can_step_stuck in Hs.
  Qed.

  Lemma axl_br: forall n (k: fin' n -> ctree E X) w φ ψ,
      <( {Br n k}, w |= φ AX ψ )> <->
        <( {Br n k}, w |= φ)>
        /\ (forall (i: fin' n), <( {k i}, w |= ψ )>).
  Proof with auto with ctl.
    split; intros.    
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_br in Hs.
      split...
      intros i.
      apply H, ktrans_br.
      exists i...
    - destruct H; csplit...
      + apply can_step_br; apply ctll_not_done in H...
      + intros t' w' TR.
        apply ktrans_br in TR as (i & -> & -> & TR).
        apply H0.
  Qed.

  Lemma axr_br: forall n (k: fin' n -> ctree E X) w φ ψ,
      <[ {Br n k}, w |= φ AX ψ ]> <->
        <( {Br n k}, w |= φ)>
        /\ (forall (i: fin' n), <[ {k i}, w |= ψ ]>).
  Proof with auto with ctl.
    split; intros.    
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_br in Hs.
      split...
      intros i.
      apply H, ktrans_br.
      exists i...
    - destruct H; csplit...
      + apply can_step_br; apply ctll_not_done in H...
      + intros t' w' TR.
        apply ktrans_br in TR as (i & -> & -> & TR).
        apply H0.
  Qed.

  Lemma axl_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ ψ,
      <( {Vis e k}, w |= φ AX ψ )> <->
        <( {Vis e k}, w |= φ )> /\ (forall (v: encode e), <( {k v}, {Obs e v} |= ψ )>).
  Proof with auto with ctl.
    split; intros.
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_vis in Hs.
      split...
      intros v.
      apply H.
      apply ktrans_vis.
      exists v...
    - destruct H; csplit...
      + apply can_step_vis...
        now apply ctll_not_done in H.
      + intros t' w' TR.
        apply ktrans_vis in TR as (i & -> & <- & TR); subst.
        apply H0.
  Qed.

  Lemma axr_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ ψ,
      <[ {Vis e k}, w |= φ AX ψ ]> <->
        <( {Vis e k}, w |= φ )> /\ (forall (v: encode e), <[ {k v}, {Obs e v} |= ψ ]>).
  Proof with auto with ctl.
    split; intros.
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_vis in Hs.
      split...
      intros v.
      apply H.
      apply ktrans_vis.
      exists v...
    - destruct H; csplit...
      + apply can_step_vis...
        now apply ctll_not_done in H.
      + intros t' w' TR.
        apply ktrans_vis in TR as (i & -> & <- & TR); subst.
        apply H0.
  Qed.

  Lemma an_done: forall (t: ctree E X) φ w,
      <[ t, w |= AN done φ ]> <-> not_done w /\ (exists (x: X), t ~ Ret x /\ φ x w).
  Proof with auto with ctl.
    split; intros.
    - cdestruct H; destruct Hs as (t' & w' & TR).
      cbn in *.
      setoid_rewrite (ctree_eta t).
      remember (observe t) as T.
      specialize (H _ _ TR).
      apply ctll_not_done in Hp.
      rewrite (ctree_eta t') in H.
      remember (observe t') as T'.
      clear HeqT t HeqT' t'.
      dependent induction TR; intros.
      + setoid_rewrite <- (ctree_eta t) in IHTR.
        split.
        * now apply ktrans_not_done with t t' w'.
        * destruct (IHTR Hp H) as (_ & x & ? & ?).
          exists x; split...
          now apply sb_guard_l.
      + inv H1; inv H.
      + inv H1.
      + split...
        exists x; intuition.
        now cdestruct H0.
      + split... 
        exists x; intuition.
        now cdestruct H0.
    - destruct H as (Hw & x & Heq & H).
      rewrite Heq, ctlr_ax; split...
      + apply ctll_now...
      + split.
        * apply can_step_ret...
        * intros t' w' TR.
          inv Hw.
          -- apply ktrans_done in TR as (-> & ->).
             apply ctlr_done...
          -- apply ktrans_finish in TR as (-> & ->).
             apply ctlr_done...
  Qed.
  
End BasicLemmas.
