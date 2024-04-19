From Coq Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import
  coinduction rel tactics.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Setoid
  CTree.Logic.AX
  Logic.Ctl
  Logic.Kripke.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

(* Lemmas on the structure of ctree [t] and AG proofs *)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma ag_vis: forall e (k: encode e -> ctree E X)
                  (v : encode e) w φ,
      (vis_with φ w /\
         forall v, <( {k v}, {Obs e v} |= AG vis φ )>) <->
        <( {Vis e k}, w |= AG vis φ )>.
  Proof with eauto with ctl.
    split; intros.
    - destruct H as (Hd & H).
      next; split.
      + inv Hd...
        now apply ctl_now.
      + next; split; inv Hd.
        * apply can_step_vis... 
        * intros.
          apply ktrans_vis in H0 as (i & -> & <- & ?)...
    - next in H.
      destruct H.      
      next in H0.
      destruct H0.
      apply can_step_not_done in H0. 
      split...
      intro v'.
      apply H1, ktrans_vis...
  Qed.
  
  Lemma ag_br: forall n (k: fin' n -> ctree E X) w φ,
      (not_done w /\
         forall (i: fin' n), <( {k i}, w |= AG now φ )>) <->
        <( {Br n k}, w |= AG now φ )>.
  Proof.
    split; intros.
    - destruct H as (Hd & H).
      next; split.
      + specialize (H Fin.F1).
        next in H.
        destruct H.
        now cbn in *.
      + next; split.
        * now apply can_step_br.
        * intros.
          apply ktrans_br in H0 as (i & ? & <- & ?).        
          now rewrite H0.
    - next in H.
      destruct H.      
      next in H0.
      destruct H0.
      apply can_step_not_done in H0.
      split; auto.
      intro i.
      apply H1.
      apply ktrans_br.
      exists i; auto.
  Qed.

  Lemma ag_ret: forall (x: X) w φ,      
      <( {Ret x}, w |= AG φ )> -> False.
  Proof.
    intros. 
    next in H.
    destruct H.
    next in H0; destruct H0.
    destruct H0 as (t' & w' & TR).
    cbn in TR, H1.
    specialize (H1 _ _ TR).
    dependent destruction TR; observe_equ x;
      rewrite <- Eqt, H0 in H1; step in H1; inv H1; try contradiction;
      destruct H3; apply can_step_not_done in H1; inv H1.
  Qed.

  Lemma ag_stuck: forall w φ,
      <( {stuck: ctree E X}, w |= AG now φ )> -> False.
  Proof.
    intros.
    next in H; destruct H.
    next in H0; destruct H0.
    now apply can_step_stuck in H0.
  Qed.

  Lemma ag_guard: forall w φ (t: ctree E X),
      <( {Guard t}, w |= AG φ )> <-> <( t, w |= AG φ )>.
  Proof.
    intros.
    now rewrite sb_guard.
  Qed.
End BasicLemmas.

Section BindLemmas.
  Context {E: Type} {HE: Encode E}.

  (* [t] will loop forever. *)
  Lemma ag_bind_l{X Y}: forall (t: ctree E X) w (k: X -> ctree E Y) φ,
      <( t, w |= AG now φ )> ->
      <( {x <- t ;; k x} , w |= AG now φ )>.
  Proof.    
    intros.
    generalize dependent t.
    revert k w.
    coinduction R CIH; intros; apply RStepA;
      step in H; cbn in H; destruct H; intuition.
    destruct H0 as ((t' & w' & TR) & ?).
    split.
    - apply can_step_bind.
      left.      
      exists t', w'; intuition.
      specialize (H0 t' w' TR).
      step in H0; ddestruction H0; intuition.
      destruct H1.
      now apply can_step_not_done with t0.
    - intros k_ w_ TR_.
      apply ktrans_bind_inv in TR_ as
          [(t_ & TRt & Hd & ->) |
            (x & wx & TR' & Hr & TRk)].
      + apply CIH; auto.
      + specialize (H0 _ _ TR').
        step in H0; ddestruction H0; intuition.
        destruct H1.
        now apply can_step_stuck in H1.
  Qed.

  Typeclasses Transparent sbisim.
  Typeclasses Transparent equ.
  (* [t] satisfies [φ] until it terminates with post-condition [R],
     then forall x w, R x w -> k x, w satisfies [φ] forever. *)
  Lemma ag_bind_r{X Y}: forall (t: ctree E X)
                          w (k: X -> ctree E Y) φ R,
      <( t, w |= (vis φ) AU (AX done R) )> ->
      (forall (x: X) w, R x w -> <( {k x}, w |= AG vis φ )>) ->
      <( {x <- t ;; k x} , w |= AG vis φ )>.
  Proof.
    intros.
    induction H.
    - (* AX done R *)
      apply ax_done in H as (Hw & x & Heq & H).
      intros.
      rewrite Heq, bind_ret_l.
      specialize (H0 _ _ H);
        step in H0; remember (k x) as K; destruct H0;
        try contradiction.
      destruct H1; subst.
      next; split; auto; next; split; auto.
    - destruct H1, H2; clear H2.
      destruct H1 as (t' & w' & TR).
      cbn in TR, H3, H4.
      cbn in H.
      rewrite (ctree_eta t).
      remember (observe t) as T.
      remember (observe t') as T'.
      clear HeqT t HeqT' t'.
      induction TR.
      + rewrite bind_guard.
        apply ag_guard.
        rewrite (ctree_eta t).
        apply IHTR; eauto.
        * intros t_ w_ TR_.
          setoid_rewrite ktrans_guard in H3.
          setoid_rewrite ktrans_guard in H4.
          now apply H3.
        * intros t_ w_ TR_.
          setoid_rewrite ktrans_guard in H3.
          setoid_rewrite ktrans_guard in H4.
          now apply H4.
      + rewrite bind_br.
        rewrite <- ag_br.
        split; [auto|intro j].
        apply H4.
        apply ktrans_br.
        exists j; intuition.
      + rewrite bind_vis.
        rewrite <- ag_vis with (v:=v).
        split; auto. 
        intro x.
        apply H4.
        apply ktrans_vis.
        exists x; intuition.
      + inv H.
      + ddestruction H.
        rewrite bind_ret_l.
        assert(TR_:[Ret x, Obs e v] ↦ [stuck, Finish e v x])
          by now apply ktrans_finish.
        specialize (H4 Ctree.stuck (Finish e v x) TR_).
        specialize (H3 Ctree.stuck (Finish e v x) TR_).
        clear TR_.
        inv H3; inv H.
        now apply can_step_stuck in H2.
  Qed.

  (* [iter k x, w] *)
  (* [k] will terminate with postcondition [RR] and invariant [φ] *)
  (* [x: I] *)
  (* AG <--> AF *)
  (* vis φ <--> done Rr *)
  Lemma ag_iter{X I}: forall (k: I -> ctree E (I + X)) w (x: I) φ R,
      vis_with φ w -> (* Worlds invariant [w = Obs e v /\ φ e v] *)
      R x ->          (* Iterator [x] in [R] *)
      (forall (i: I) w,
          R i ->
          vis_with φ w ->
          <( {k i}, w |= (vis φ) AU (AX done
               {fun (lr: I+X) _ => exists i', lr = inl i' /\ R i'}) )>) ->
      <( {iter k x}, w |= AG vis φ )>.
  Proof.
    intros.
    rewrite unfold_iter.
    apply ag_bind_r with (R:=fun (lr : I + X) (_ : World E) =>
                               exists i' : I, lr = inl i' /\ R i'); auto.
    pose proof (H1 _ _ H0 H) as H1'.
    remember (k x) as K.
    hinduction H1' before k; intros; destruct x0 as [l | r]; subst.
    - destruct H3 as (i' & Hinv & ?); inv Hinv.
      apply ax_done in H as (Hd & ? & Heqk & (j & -> & ?)).
  Admitted.

End BindLemmas.
