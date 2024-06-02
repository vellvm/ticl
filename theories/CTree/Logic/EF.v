From Coq Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

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
  Logic.EX
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

  Lemma ef_done: forall (t: ctree E X) φ w,
      is_done w ->
      <( t, w |= EF now φ )> ->
      φ w.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra; auto.
    destruct H; auto.
    destruct H0 as (? & ? & ? & ?).
    exfalso.
    eapply done_not_ktrans with (t:=t); eauto.
  Qed.

  Lemma ef_stuck: forall w φ,
      <( {Ctree.stuck: ctree E X}, w |= EF φ )> <->
      <( {Ctree.stuck: ctree E X}, w |= φ )>.
  Proof.
    split; intros.
    - cbn in H; rewrite unfold_stuck.
      remember Ctree.stuck in H; cdestruct H; subst.
      + now rewrite unfold_stuck in H.
      + destruct H0 as (? & ? & ? & ?).
        now apply ktrans_stuck in H0.
    - now next; left.
  Qed.

  Lemma ef_ret: forall r w (Rr: rel X (World E)),      
      Rr r w ->
      not_done w ->
      <( {Ret r}, w |= EF done Rr )>.
  Proof.
    intros * Hr Hd.
    next; right.
    next; inv Hd.
    - exists (Ctree.stuck), (Done r); split.
      + apply ktrans_done; auto.
      + apply ef_stuck. now constructor.
    - exists (Ctree.stuck), (Finish e v r); split.
      + apply ktrans_finish; auto.
      + apply ef_stuck; now constructor.
  Qed.

  Lemma not_done_vis_ef: forall (t: ctree E X) φ w,
      <( t, w |= EF vis φ )> ->
      not_done w.
  Proof with eauto with ctl.
    intros * Hf.
    next in Hf ; destruct Hf.
    - destruct H; inv H; constructor.
    - destruct H as (? & ? & ? & ?).
      now apply ktrans_not_done with t x x0.
  Qed.

  Lemma not_done_pure_ef: forall (t: ctree E X) w,
      <( t, w |= EF pure )> ->
      not_done w.
  Proof with eauto with ctl.
    intros * Hf.
    next in Hf ; destruct Hf.
    - destruct H; subst; constructor.
    - destruct H as (? & ? & ? & ?).
      now apply ktrans_not_done with t x x0.
  Qed.

  Lemma ef_guard: forall (t: ctree E X) w φ,
      <( {Guard t}, w |= EF φ )> <->
      <( t, w |= EF φ )>.
  Proof.
    intros.
    now rewrite sb_guard.
  Qed.

  Lemma ef_br: forall n (k: fin' n -> ctree E X) w φ,
      <( {Br n k}, w |= EF now φ )> <->
        (exists (i: fin' n), <( {k i}, w |= EF now φ )>).
  Proof.
    split; intros.
    - next in H; destruct H.
      + exists Fin.F1.
        next; left.
        now rewrite ctl_now in *.
      + destruct H as (? & ? & ? & ?).
        apply ktrans_br in H as (i & ? & -> & ?).
        rewrite H in H0.
        now (exists i).
    - destruct H as (i & ?).
      next in H; destruct H.
      + next; left.
        now rewrite ctl_now in *.
      + next; right; next.
        destruct H as (? & ? & ? & ?).
        exists (k i), w; split; auto with ctl.
        * apply ktrans_br.
          exists i; intuition.
        * next; right; next.
          exists x, x0; intuition.
  Qed.

  Lemma ef_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      (φ w \/ (not_done w /\ exists (x: encode e),
                 <( {k x}, {Obs e x} |= EF now φ )>)) ->
      <( {Vis e k}, w |= EF now φ )>.        
  Proof.
    intros.
    destruct H as [H | [Hd (v & ?)]].
    - now next; left.
    - next; right; next.
      + exists (k v), (Obs e v); split; auto.
        apply ktrans_vis.
        exists v; intuition.
  Qed.

  Lemma ef_ret_inv: forall (x: X) w R,
      <( {Ret x}, w |= EF (EX done R) )> ->
      R x w.
  Proof.
    intros.
    next in H; destruct H.
    - destruct H as (? & ? & ? & ?).
      ddestruction H; now ddestruction H0.
    - destruct H as (? & ? & ? & ?).
      ddestruction H; observe_equ x; destruct H0.
      + rewrite <- Eqt, H in H0.
        destruct H0 as (? & ? & ? & ?); now apply ktrans_stuck in H0.
      + rewrite <- Eqt, H in H1.
        destruct H1 as (? & ? & ? & ?); now apply ktrans_stuck in H1.
      + rewrite <- Eqt, H in H0.
        destruct H0 as (? & ? & ? & ?); now apply ktrans_stuck in H0.
      + rewrite <- Eqt, H in H1.
        destruct H1 as (? & ? & ? & ?); now apply ktrans_stuck in H1.
  Qed.

End BasicLemmas.

(* TODO: WIP here copied from AF.v *)
Section CtlEfBind.
  Context {E: Type} {HE: Encode E}.

  Typeclasses Transparent equ.
  Theorem ef_bind_vis{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
      <( t, w |= EF vis φ )> ->
      <( {x <- t ;; k x}, w |= EF vis φ )>.
  Proof.
    intros * Haf.
    revert X k.
    induction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn.
      inv H; now constructor.
    - (* StepA *)
      destruct H0 as (t' & w' & TR' & H0).
      destruct H1 as (t_ & w_ & TR_ & H1).
      clear H.
      next; right; next. 
      exists (x <- t_;; k x), w_.
      split.
      + apply ktrans_bind_l; auto.          
        eapply not_done_vis_ef with (t:=x <- t_ ;; k x).
        now apply H1.
      + apply H1.
  Qed.

  Theorem ef_bind_pure{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      <( t, w |= EF pure )> ->
      <( {x <- t ;; k x}, w |= EF pure )>.
  Proof.
    intros * Haf.
    revert X k.
    induction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn.
      now apply ctl_pure. 
    - (* StepA *)
      destruct H0 as (t' & w' & TR' & H0).
      destruct H1 as (t_ & w_ & TR_ & H1).
      clear H.
      next; right; next. 
      exists (x <- t_;; k x), w_.
      split.
      + apply ktrans_bind_l; auto.          
        eapply not_done_pure_ef with (t:=x <- t_ ;; k x).
        now apply H1.
      + apply H1.
  Qed.

  Theorem ef_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ r,
      <( t, w |= EF EX done= r w' )> ->
      not_done w' ->
      <( {k r}, w' |= EF now φ )> ->
      <( {x <- t ;; k x}, w |= EF now φ )>.
  Proof.
    intros.
    revert H0 H1.
    cinduction H; intros.
    - apply ex_done in H as (Hd & y & Heqy & -> & ->).
      assert (Hk: x <- t ;; k x ~  x <- Ret y ;; k x) by (__upto_bind_sbisim; auto).
      rewrite Hk, bind_ret_l.
      apply H1.
    - destruct H0 as (t0 & w0 & TR0 & H0).
      destruct H1 as (t1 & w1 & TR1 & H1).
      specialize (H1 H2 H3).
      clear H.
      next; right; next.
      (* Here, whatever I chose is wrong :( *)
  Admitted.

End CtlEfBind.
