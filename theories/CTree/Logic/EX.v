From Coq Require Import
  Basics
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
  
(*| CTL EX lemmas on ctrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma done_ex: forall (t: ctree E X) φ w,
      is_done X w ->
      ~ <( t, w |= EX φ )>.
  Proof.
    intros * Hret Hcontra.
    destruct Hcontra as (t' & w' & TR & H).
    apply ktrans_not_done in TR.
    inv TR; inv Hret.
  Qed.

  Lemma ex_stuck: forall w φ,
      <( {Ctree.stuck: ctree E X}, w |= EX φ )> ->
      <( {Ctree.stuck: ctree E X}, w |= φ )>.
  Proof.
    intros.
    destruct H as (t' & w' & TR' & H).
    now apply ktrans_stuck in TR'.
  Qed.

  Lemma ex_guard: forall (t: ctree E X) w φ,
      <( {Guard t}, w |= EX φ )> <->
      <( t, w |= EX φ )>.
  Proof.
    intros.
    now rewrite sb_guard.
  Qed.
  
  Lemma ex_br: forall n (k: fin' n -> ctree E X) w φ,
      <( {Br n k}, w |= EX φ )> <->
        not_done w /\ (exists (i: fin' n), <( {k i}, w |= φ )>).
  Proof with auto with ctl.
    split; intros.
    - cdestruct H. 
      apply ktrans_br in TR as (i & H' & -> & Hd').
      split...
      exists i.
      now rewrite H' in H.
    - destruct H as (Hd & i & H).
      + exists (k i), w; split...
        apply ktrans_br.
        exists i...
  Qed.

  Lemma ex_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      <( {Vis e k}, w |= EX φ )> <->
        not_done w /\ (exists (v: encode e), <( {k v}, {Obs e v} |= φ )>).
  Proof with auto with ctl.
    split; intros.
    - cdestruct H. 
      apply ktrans_vis in TR as (v & -> & ? & ?).
      rewrite <- H0 in H.
      split; [|exists v]...
    - destruct H as (Hd & v & ?).
      exists (k v), (Obs e v); split...
      apply ktrans_vis.
      exists v...
  Qed.

  Lemma ex_done_ret: forall (x: X) φ w,
      <[ {Ret x}, w |= EX done φ ]> <->
        not_done w /\ φ x w. 
  Proof with eauto with ctl.
    split; intros.
    - cdestruct H. 
      split.
      + now apply ktrans_not_done with (Ret x) t w0.
      + cdestruct H; now ddestruction TR.
    - destruct H as ([] & ?); exists (Ctree.stuck).
      + exists (Done x); split.
        * apply ktrans_done...
        * now constructor.
      + exists (Finish e v x); split.
        * apply ktrans_finish...
        * now constructor.
  Qed.

  Lemma ex_done: forall (t: ctree E X) φ w,
      <[ t, w |= EX done φ ]> <-> not_done w /\ (exists (x: X), t ~ Ret x /\ φ x w).
  Proof.
    split; intros.
    - cdestruct H.
      split; [now apply ktrans_not_done with t t0 w0|].
      cbn in *.
      setoid_rewrite (ctree_eta t).
      setoid_rewrite (ctree_eta t0) in H.
      remember (observe t) as T.
      remember (observe t0) as T'.
      clear HeqT t HeqT' t0.
      dependent induction TR; intros.
      + setoid_rewrite <- (ctree_eta t) in IHTR.
        destruct (IHTR H) as (x & Heq & Hφ).
        exists x; split; auto.
        now apply sb_guard_l.
      + inv H1; inv H.
      + inv H1.
      + exists x; intuition.
        now cdestruct H0.
      + exists x; intuition.
        now cdestruct H0.
    - destruct H as (Hw & x & Heq & H).
      rewrite Heq.
      apply ex_done_ret; intuition.
  Qed.
End BasicLemmas.

Section BindLemmas.
  Context {E: Type} {HE: Encode E}.

  Opaque Ctree.stuck.
  Typeclasses Transparent equ.
  Theorem ex_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ r,
      <[ t, w |= EX done= r w' ]> ->
      <( {k r}, w' |= EX φ )> ->
      <( {x <- t ;; k x}, w |= EX φ )>.
  Proof with eauto with ctl.
    intros.
    cdestruct H.
    cbn in TR.
    rewrite (ctree_eta t).
    rewrite (ctree_eta t0) in H; [|exact (equ eq)].
    remember (observe t) as T; clear t HeqT.
    remember (observe t0) as T'; clear t0 HeqT'.
    hinduction TR before Y; intros; subst.
    - rewrite bind_guard.
      apply ex_guard.
      eapply IHTR with w'0 r...
    - rewrite bind_br.
      inv H; inv H1.
    - inv H1.
    - cdestruct H0; ddestruction H0; destruct H0; subst.
      rewrite bind_ret_l...
    - cdestruct H0; ddestruction H0; destruct H0; subst.
      rewrite bind_ret_l...
  Qed.
End BindLemmas.
