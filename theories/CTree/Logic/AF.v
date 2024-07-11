From Coq Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From CTree Require Import
  Events.Core
  Events.WriterE
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Interp.Core
  CTree.Interp.State
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.AX
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

  Lemma aul_stuck: forall w φ ψ,
      <( {Ctree.stuck: ctree E X}, w |= ψ )> <->
      <( {Ctree.stuck: ctree E X}, w |= φ AU ψ )>.
  Proof.
    split; intros * H.
    - now cleft.
    - remember (Ctree.stuck) as S.
      cinduction H; subst.
      + apply Hp.
      + now apply can_step_stuck in Hs.
  Qed.

  Lemma aur_stuck: forall w φ ψ,
      <[ {Ctree.stuck: ctree E X}, w |= ψ ]> <->
      <[ {Ctree.stuck: ctree E X}, w |= φ AU ψ ]>.
  Proof.
    split; intros * H.
    - now cleft.
    - remember (Ctree.stuck) as S.
      cinduction H; subst.
      + apply Hp.
      + now apply can_step_stuck in Hs.
  Qed.

  Lemma aul_ret: forall (r: X) w φ ψ,
      <( {Ret r}, w |= ψ \/ φ AN ψ )> <->
      <( {Ret r}, w |= φ AU ψ )>.
  Proof with auto with ctl.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H...
      intros t' w' TR.
      apply ctll_not_done in Hp.
      specialize (H _ _ TR).
      inv Hp.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H |- *.
        now cleft.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H |- *.
        now cleft.
    - now cleft.
    - cdestruct H.
      cright; csplit...
      intros t' w' TR.
      apply ctll_not_done in Hp.
      specialize (H _ _ TR).
      inv Hp.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H |- *.
        now apply aul_stuck in H.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H |- *.
        now apply aul_stuck in H.
  Qed.

  Lemma aur_ret: forall (r: X) w φ ψ,
      <[ {Ret r}, w |= ψ \/ φ AN ψ ]> <->
      <[ {Ret r}, w |= φ AU ψ ]>.
  Proof with auto with ctl.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H...
      intros t' w' TR.
      apply ctll_not_done in Hp.
      specialize (H _ _ TR).
      inv Hp.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H |- *.
        now cleft.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H |- *.
        now cleft.
    - now cleft.
    - cdestruct H.
      cright; csplit...
      intros t' w' TR.
      apply ctll_not_done in Hp.
      specialize (H _ _ TR).
      inv Hp.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H |- *.
        now apply aur_stuck in H.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H |- *.
        now apply aur_stuck in H.
  Qed.

  Lemma aul_br: forall n (k: fin' n -> ctree E X) w ψ φ,
      (<( {Br n k}, w |= φ )> \/
         <( {Br n k}, w |= ψ )> /\
           forall (i: fin' n), <( {k i}, w |= ψ AU φ )>) <->
      <( {Br n k}, w |= ψ AU φ )>.
  Proof with auto with ctl.
    split; intros.
    - destruct H as [Hφ | (Hψ & H)].
      + now cleft.
      + cright; csplit...
        * apply ctll_not_done in Hψ.
          now apply can_step_br.
        * intros t' w' TR'.
          apply ktrans_br in TR' as (? & -> & -> & ?).
          apply H.
    - cdestruct H.
      + now left.
      + right; split...
        * now cdestruct H.
        * cdestruct H...
          intro i.
          apply H.
          apply ktrans_br.
          exists i; split2...
          now apply ctll_not_done in Hp.
  Qed.


  Lemma aul_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w ψ φ,
      (<( {Vis e k}, w |= φ )> \/
         <( {Vis e k}, w |= ψ )> /\
           forall (v: encode e), <( {k v}, {Obs e v} |= ψ AU φ )>) <->
      <( {Vis e k}, w |= ψ AU φ )>.
  Proof with auto with ctl.
    split; intros.
    - destruct H as [Hφ | (Hψ & H)].
      + now cleft.
      + cright; csplit...
        * apply ctll_not_done in Hψ.
          now apply can_step_vis.
        * intros t' w' TR'.
          apply ktrans_vis in TR' as (? & -> & <- & ?).
          apply H.
    - cdestruct H.
      + now left.
      + right; split...
        * now cdestruct H.
        * cdestruct H...
          intro i.
          apply H.
          apply ktrans_vis.
          exists i; split2...
          now apply ctll_not_done in Hp.
  Qed.

  Lemma afl_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      <( {Vis e k}, w |= φ )> \/
         (not_done w /\ forall (v: encode e), <( {k v}, {Obs e v} |= AF φ )>) <->
      <( {Vis e k}, w |= AF φ )>.
  Proof with auto with ctl.
    split; intros.
    - destruct H.
      + apply aul_vis...
      + apply aul_vis...
        destruct H as (Hd & H).
        right; split.
        * csplit; split...
        * apply H.
    - apply aul_vis in H...
      destruct H.
      + now left.
      + destruct H; cdestruct H.
        right...
  Qed.

  Lemma aur_br: forall n (k: fin' n -> ctree E X) w ψ φ,
      (<[ {Br n k}, w |= φ ]> \/
         <( {Br n k}, w |= ψ )> /\
           forall (i: fin' n), <[ {k i}, w |= ψ AU φ ]>) <->
      <[ {Br n k}, w |= ψ AU φ ]>.
  Proof with auto with ctl.
    split; intros.
    - destruct H as [Hφ | (Hψ & H)].
      + now cleft.
      + cright; csplit...
        * apply ctll_not_done in Hψ.
          now apply can_step_br.
        * intros t' w' TR'.
          apply ktrans_br in TR' as (? & -> & -> & ?).
          apply H.
    - cdestruct H.
      + now left.
      + right; split...
        * now cdestruct H.
        * cdestruct H...
          intro i.
          apply H.
          apply ktrans_br.
          exists i; split2...
          now apply ctll_not_done in Hp.
  Qed.

  Lemma aur_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w ψ φ,
      (<[ {Vis e k}, w |= φ ]> \/
         <( {Vis e k}, w |= ψ )> /\
           forall (v: encode e), <[ {k v}, {Obs e v} |= ψ AU φ ]>) <->
      <[ {Vis e k}, w |= ψ AU φ ]>.
  Proof with auto with ctl.
    split; intros.
    - destruct H as [Hφ | (Hψ & H)].
      + now cleft.
      + cright; csplit...
        * apply ctll_not_done in Hψ.
          now apply can_step_vis.
        * intros t' w' TR'.
          apply ktrans_vis in TR' as (? & -> & <- & ?).
          apply H.
    - cdestruct H.
      + now left.
      + right; split...
        * now cdestruct H.
        * cdestruct H...
          intro i.
          apply H.
          apply ktrans_vis.
          exists i; split2...
          now apply ctll_not_done in Hp.
  Qed.

  Lemma afr_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      <[ {Vis e k}, w |= φ ]> \/
         (not_done w /\ forall (v: encode e), <[ {k v}, {Obs e v} |= AF φ ]>) <->
      <[ {Vis e k}, w |= AF φ ]>.
  Proof with auto with ctl.
    split; intros.
    - destruct H.
      + apply aur_vis...
      + apply aur_vis...
        destruct H as (Hd & H).
        right; split.
        * csplit; split...
        * apply H.
    - apply aur_vis in H...
      destruct H.
      + now left.
      + destruct H; cdestruct H.
        right...
  Qed.

  Lemma aur_not_done: forall φ ψ ξ (t: ctree E X) (w: World E),
      <[ t, w |= φ AU (ψ AN ξ) ]> ->
      not_done w.
  Proof.
    intros.
    cdestruct H; cdestruct H;
      now apply can_step_not_done with t.
  Qed.
End BasicLemmas.
