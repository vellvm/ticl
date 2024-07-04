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
      ~ <( {Ctree.stuck: ctree E X}, w |= φ AN ψ )>.
  Proof.
    intros * H; cdestruct H.
    now apply can_step_stuck in Hs.
  Qed.

  Lemma axr_stuck: forall w φ ψ,
      ~ <[ {Ctree.stuck: ctree E X}, w |= φ AN ψ ]>.
  Proof.
    intros * H; cdestruct H.
    now apply can_step_stuck in Hs.
  Qed.

  Lemma axl_br: forall n (k: fin' n -> ctree E X) w φ ψ,
      <( {Br n k}, w |= φ AN ψ )> <->
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
      <[ {Br n k}, w |= φ AN ψ ]> <->
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
      <( {Vis e k}, w |= φ AN ψ )> <->
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
      <[ {Vis e k}, w |= φ AN ψ ]> <->
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

  Typeclasses Transparent equ.
  Lemma ax_done: forall (t: ctree E X) φ ψ w,
      <[ t, w |= φ AN done ψ ]> <-> <( t, w |= φ )> /\ (exists (x: X), t ~ Ret x /\ ψ x w).
  Proof with auto with ctl.
    split; intros.
    - cdestruct H; destruct Hs as (t' & w' & TR).
      cbn in *.
      assert(Hd: not_done w) by now apply ctll_not_done in Hp.
      setoid_rewrite (ctree_eta t).
      rewrite (ctree_eta t) in Hp.
      remember (observe t) as T.
      specialize (H _ _ TR).
      rewrite (ctree_eta t') in H; [|exact (equ eq)].
      remember (observe t') as T'.
      clear HeqT t HeqT' t'.
      dependent induction TR; intros.
      + setoid_rewrite <- (ctree_eta t) in IHTR.
        split.
        * rewrite sb_guard in Hp |- *.
          edestruct IHTR...
        * rewrite sb_guard in Hp.
          destruct (IHTR Hp H) as (_ & x & ? & ?)...
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
    - destruct H as (Hφ & x & Heq & H).
      rewrite Heq in Hφ |- *.
      rewrite ctlr_ax; split2...
      + apply ctll_not_done in Hφ.
        apply can_step_ret...
      + intros t' w' TR.
        apply ctll_not_done in Hφ.
        inv Hφ.
        -- apply ktrans_done in TR as (-> & ->); [|exact (equ eq)].
           apply ctlr_done...
        -- apply ktrans_finish in TR as (-> & ->); [|exact (equ eq)].
           apply ctlr_done...
  Qed.

  Lemma axl_ret: forall (r: X) w φ ψ,
      ~ <( {Ret r}, w |= φ AN ψ )>.
  Proof.
    intros * H.
    cdestruct H.
    destruct Hs as (t' & w' & TR).
    specialize (H _ _ TR).
    assert (Hd: not_done w) by now apply ktrans_not_done in TR.
    inv Hd.
    - apply ktrans_done in TR as (-> & Heqt); rewrite Heqt in H.
      apply ctll_not_done in H; inv H.
    - apply ktrans_finish in TR as (-> & Heqt); rewrite Heqt in H.
      apply ctll_not_done in H; inv H.
  Qed.

  Lemma axr_ret: forall (r: X) (R: rel X (World E)) φ w,
      <( {Ret r}, w |= φ )> ->
      R r w ->
      <[ {Ret r}, w |= φ AN done R ]>.
  Proof with auto with ctl.
    intros.
    apply ax_done; split...
    exists r...
  Qed.
  
  Lemma anr_ret: forall (r: X) (R: rel X (World E)) w,
      not_done w ->
      R r w ->
      <[ {Ret r}, w |= AX done R ]>.
  Proof with auto with ctl.
    intros.
    apply axr_ret...
    csplit...
  Qed.
  
  Lemma axr_ret_inv: forall (r: X) w φ ψ,
      <[ {Ret r}, w |= φ AN ψ ]> ->
        <( {Ret r}, w |= φ )>
        /\ exists (w': World E), done_with (fun x w' => x = r /\ w = w') w'
        /\ <[ Ctree.stuck, w' |= ψ ]>.
  Proof with auto with ctl.
    intros.
    cdestruct H.
    assert (Hd: not_done w) by now apply can_step_not_done in Hs.
    destruct Hs as (t' & w' & TR).
    specialize (H _ _ TR).
    inv Hd.
    + apply ktrans_done in TR as (-> & Heqt).
      rewrite Heqt in H.
      split...
      exists (Done r)...
    + apply ktrans_finish in TR as (-> & Heqt).
      rewrite Heqt in H.
      split...
      exists (Finish e v r)...
  Qed.
End BasicLemmas.
