From Stdlib Require Import
  Basics
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
  
(*| TICL EN lemmas on ictrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma enl_stuck: forall w φ ψ,
      <( {ICtree.stuck: ictree E X}, w |= φ EN ψ )> ->
      <( {ICtree.stuck: ictree E X}, w |= ψ )>.
  Proof.
    intros.
    cdestruct H. 
    now apply ktrans_stuck in TR.
  Qed.

  Lemma enl_br: forall n (k: fin' n -> ictree E X) w φ ψ,
      (<( {Br n k}, w |= φ )> /\ (exists (i: fin' n), <( {k i}, w |= ψ )>)) <->
    <( {Br n k}, w |= φ EN ψ )>.
  Proof with auto with ticl.
    split; intros.
    - destruct H as (Hφ & i & H).
      csplit...
      exists (k i), w; split...
      apply ktrans_br; exists i. 
      split2...
      now apply ticll_not_done in Hφ.
    - cdestruct H.
      apply ktrans_br in TR as (i & Heq & -> & Hd).
      rewrite Heq in H.
      split...
      exists i...
  Qed.

  Lemma enl_vis: forall (e: E) (k: encode e -> ictree E X) (_: encode e) w φ ψ,
      <( {Vis e k}, w |= φ EN ψ )> <->        
        <( {Vis e k}, w |= φ )> /\ (exists (v: encode e), <( {k v}, {Obs e v} |= ψ )>).
  Proof with eauto with ticl.
    split; intros.
    - cdestruct H. 
      apply ktrans_vis in TR as (v & -> & ? & ?).
      rewrite <- H0 in H.
      split... 
    - destruct H as (Hd & v & ?).
      csplit...
      exists (k v), (Obs e v); split...
      apply ktrans_vis.
      exists v; split2...
      now apply ticll_not_done in Hd.
  Qed.

  Lemma enr_stuck: forall w φ ψ,
      <[ {ICtree.stuck: ictree E X}, w |= φ EN ψ ]> ->
      <[ {ICtree.stuck: ictree E X}, w |= ψ ]>.
  Proof.
    intros.
    cdestruct H. 
    now apply ktrans_stuck in TR.
  Qed.

  Lemma enr_br: forall n (k: fin' n -> ictree E X) w φ ψ,
      (<( {Br n k}, w |= φ )> /\ (exists (i: fin' n), <[ {k i}, w |= ψ ]>)) <->
        <[ {Br n k}, w |= φ EN ψ ]>.
  Proof with auto with ticl.
    split; intros.
    - destruct H as (Hφ & i & H).
      csplit...
      exists (k i), w; split...
      apply ktrans_br; exists i. 
      split2...
      now apply ticll_not_done in Hφ.
    - cdestruct H.
      apply ktrans_br in TR as (i & Heq & -> & Hd).
      rewrite Heq in H.
      split...
      exists i...
  Qed.

  Lemma enr_vis: forall (e: E) (k: encode e -> ictree E X) (_: encode e) w φ ψ,
      <[ {Vis e k}, w |= φ EN ψ ]> <->        
        <( {Vis e k}, w |= φ )> /\ (exists (v: encode e), <[ {k v}, {Obs e v} |= ψ ]>).
  Proof with eauto with ticl.
    split; intros.
    - cdestruct H. 
      apply ktrans_vis in TR as (v & -> & ? & ?).
      rewrite <- H0 in H.
      split... 
    - destruct H as (Hd & v & ?).
      csplit...
      exists (k v), (Obs e v); split...
      apply ktrans_vis.
      exists v; split2...
      now apply ticll_not_done in Hd.
  Qed.

  Lemma enr_done: forall (t: ictree E X) φ ψ w,
      <[ t, w |= φ EN done ψ ]> <-> <( t, w |= φ )> /\ (exists (x: X), t ~ Ret x /\ ψ x w).
  Proof with eauto with ticl.
    split; intros.
    - cdestruct H.
      split...
      cbn in *.
      setoid_rewrite (ictree_eta t).
      setoid_rewrite (ictree_eta t) in Hp.
      setoid_rewrite (ictree_eta t0) in H.
      remember (observe t) as T.
      remember (observe t0) as T'.
      clear HeqT t HeqT' t0.
      dependent induction TR; intros.
      + rewrite sb_guard in Hp.
        setoid_rewrite <- (ictree_eta t) in IHTR.
        destruct (IHTR Hp) as (x & Heq & Hφ)...
        exists x; split; auto.
        now apply sb_guard_l.
      + cdestruct H1; inv H.
      + cdestruct H1. 
      + exists x; intuition.
        now cdestruct H0.
      + exists x; intuition.
        now cdestruct H0.
    - destruct H as (Hφ & x & Heq & H).
      rewrite Heq in Hφ |- *.
      csplit...
      pose proof (ticll_not_done _ _ _ _ Hφ) as Hd.
      inv Hd.
      + exists (ICtree.stuck), (Done x); split.
        * now apply ktrans_done.
        * now csplit.
      + exists (ICtree.stuck), (Finish e v x); split.
        * now apply ktrans_finish.
        * now csplit.
  Qed.

  Lemma enl_ret: forall (r: X) w φ ψ,
      ~ <( {Ret r}, w |= φ EN ψ )>.
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

  Lemma enr_ret: forall (r: X) (R: rel X (World E)) φ w,
      <( {Ret r}, w |= φ )> ->
      R r w ->
      <[ {Ret r}, w |= φ EN done R ]>.
  Proof with auto with ticl.
    intros.
    apply enr_done; split...
    exists r...
  Qed.
  
  Lemma exr_ret: forall (r: X) (R: rel X (World E)) w,
      not_done w ->
      R r w ->
      <[ {Ret r}, w |= EX done R ]>.
  Proof with auto with ticl.
    intros.
    apply enr_ret...
    csplit...
  Qed.
  
  Lemma enr_ret_inv: forall (r: X) w φ ψ,
      <[ {Ret r}, w |= φ EN ψ ]> ->
        <( {Ret r}, w |= φ )>
        /\ exists (w': World E), done_with (fun x w' => x = r /\ w = w') w'
        /\ <[ ICtree.stuck, w' |= ψ ]>.
  Proof with auto with ticl.
    intros.
    cdestruct H.
    assert (Hd: not_done w) by now apply ktrans_not_done in TR. 
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

Section WriterLemmas.
              
  Lemma exr_log{S}: forall (x: S) w,
      not_done w ->
      <[ {log x}, w |= EX EX done=tt {Obs (Log x) tt} ]>.
  Proof with eauto with ticl.
    intros.
    unfold log, ICtree.trigger.
    apply enr_vis...
    intuition.
    - csplit...
    - exists tt.
      apply enr_done; intuition.
      + csplit...
      + exists tt.
        unfold resum_ret, resum, ReSum_refl, ReSumRet_refl.
        intuition.
  Qed.

End WriterLemmas.
