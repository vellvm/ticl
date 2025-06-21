From Stdlib Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

From TICL Require Import
  Events.Core
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Events.Writer
  Logic.Core
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.
  
(*| TICL logic lemmas on c/itrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma anl_stuck: forall w φ ψ,
      ~ <( {ICtree.stuck: ictree E X}, w |= φ AN ψ )>.
  Proof.
    intros * H; cdestruct H.
    now apply can_step_stuck in Hs.
  Qed.

  Lemma anr_stuck: forall w φ ψ,
      ~ <[ {ICtree.stuck: ictree E X}, w |= φ AN ψ ]>.
  Proof.
    intros * H; cdestruct H.
    now apply can_step_stuck in Hs.
  Qed.

  Lemma anl_br: forall n (k: fin' n -> ictree E X) w φ ψ,
      <( {Br n k}, w |= φ AN ψ )> <->
        <( {Br n k}, w |= φ)>
        /\ (forall (i: fin' n), <( {k i}, w |= ψ )>).
  Proof with auto with ticl.
    split; intros.    
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_br in Hs.
      split...
      intros i.
      apply H, ktrans_br.
      exists i...
    - destruct H; csplit...
      + apply can_step_br; apply ticll_not_done in H...
      + intros t' w' TR.
        apply ktrans_br in TR as (i & -> & -> & TR).
        apply H0.
  Qed.

  Lemma anr_br: forall n (k: fin' n -> ictree E X) w φ ψ,
      <[ {Br n k}, w |= φ AN ψ ]> <->
        <( {Br n k}, w |= φ)>
        /\ (forall (i: fin' n), <[ {k i}, w |= ψ ]>).
  Proof with auto with ticl.
    split; intros.    
    - cdestruct H.
      assert(Hd: not_done w) by now apply can_step_br in Hs.
      split...
      intros i.
      apply H, ktrans_br.
      exists i...
    - destruct H; csplit...
      + apply can_step_br; apply ticll_not_done in H...
      + intros t' w' TR.
        apply ktrans_br in TR as (i & -> & -> & TR).
        apply H0.
  Qed.

  Lemma anl_vis: forall (e: E) (k: encode e -> ictree E X) (_: encode e) w φ ψ,
      <( {Vis e k}, w |= φ AN ψ )> <->
        <( {Vis e k}, w |= φ )> /\ (forall (v: encode e), <( {k v}, {Obs e v} |= ψ )>).
  Proof with auto with ticl.
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
        now apply ticll_not_done in H.
      + intros t' w' TR.
        apply ktrans_vis in TR as (i & -> & <- & TR); subst.
        apply H0.
  Qed.

  Lemma anr_vis: forall (e: E) (k: encode e -> ictree E X) (_: encode e) w φ ψ,
      <[ {Vis e k}, w |= φ AN ψ ]> <->
        <( {Vis e k}, w |= φ )> /\ (forall (v: encode e), <[ {k v}, {Obs e v} |= ψ ]>).
  Proof with auto with ticl.
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
        now apply ticll_not_done in H.
      + intros t' w' TR.
        apply ktrans_vis in TR as (i & -> & <- & TR); subst.
        apply H0.
  Qed.

  Typeclasses Transparent equ.
  Lemma anr_done: forall (t: ictree E X) φ ψ w,
      <[ t, w |= φ AN done ψ ]> <-> <( t, w |= φ )> /\ (exists (x: X), t ~ Ret x /\ ψ x w).
  Proof with auto with ticl.
    split; intros.
    - cdestruct H; destruct Hs as (t' & w' & TR).
      cbn in *.
      assert(Hd: not_done w) by now apply ticll_not_done in Hp.
      setoid_rewrite (ictree_eta t).
      rewrite (ictree_eta t) in Hp.
      remember (observe t) as T.
      specialize (H _ _ TR).
      rewrite (ictree_eta t') in H; [|exact (equ eq)].
      remember (observe t') as T'.
      clear HeqT t HeqT' t'.
      dependent induction TR; intros.
      + setoid_rewrite <- (ictree_eta t) in IHTR.
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
      rewrite ticlr_an; split2...
      + apply ticll_not_done in Hφ.
        apply can_step_ret...
      + intros t' w' TR.
        apply ticll_not_done in Hφ.
        inv Hφ.
        -- apply ktrans_done in TR as (-> & ->); [|exact (equ eq)].
           apply ticlr_done...
        -- apply ktrans_finish in TR as (-> & ->); [|exact (equ eq)].
           apply ticlr_done...
  Qed.

  Lemma anl_ret: forall (r: X) w φ ψ,
      ~ <( {Ret r}, w |= φ AN ψ )>.
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

  Lemma anr_ret: forall (r: X) (R: rel X (World E)) φ w,
      <( {Ret r}, w |= φ )> ->
      R r w ->
      <[ {Ret r}, w |= φ AN done R ]>.
  Proof with auto with ticl.
    intros.
    apply anr_done; split...
    exists r...
  Qed.
  
  Lemma axr_ret: forall (r: X) (R: rel X (World E)) w,
      not_done w ->
      R r w ->
      <[ {Ret r}, w |= AX done R ]>.
  Proof with auto with ticl.
    intros.
    apply anr_ret...
    csplit...
  Qed.
  
  Lemma anr_ret_inv: forall (r: X) w φ ψ,
      <[ {Ret r}, w |= φ AN ψ ]> ->
        <( {Ret r}, w |= φ )>
        /\ exists (w': World E), done_with (fun x w' => x = r /\ w = w') w'
        /\ <[ ICtree.stuck, w' |= ψ ]>.
  Proof with auto with ticl.
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
