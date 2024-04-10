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

Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma ag_vis: forall e (k: encode e -> ctree E X)
                  (_ : encode e) w φ,
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
      intro v.
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

Section BindCtxUnary.
  Context {E: Type} {HE: Encode E} {X Y: Type}.
  Notation MP X := (ctree E X * World E -> Prop).
  
  Definition bind_ctx_unary
    (R: ctree E X -> Prop) (S: (X -> ctree E Y) -> Prop):
    ctree E Y -> Prop :=
    fun t => sup R
      (fun x => sup S
               (fun k => t = bind x k)).
  
  Lemma leq_bind_ctx_unary:
    forall R S S', bind_ctx_unary R S <= S' <->
                (forall x, R x -> forall k, S k -> S' (bind x k)).
  Proof.
    intros.
    unfold bind_ctx_unary.
    split; intros; repeat red in H; repeat red.
    - apply H.
      exists x; auto.
      exists k; auto.
    - intro t.
      intros [x Hs].
      destruct H0; subst.
      apply H; auto.
  Qed.

  Lemma in_bind_ctx_unary (R S : _ -> Prop) x y:
    R x -> S y -> bind_ctx_unary R S (bind x y).
  Proof. intros. apply ->leq_bind_ctx_unary; eauto. Qed.
  #[global] Opaque bind_ctx_unary.

  (* 
  Program Definition bind_clos_ar: mon (MP X -> MP X -> MP X) :=
    {| body R '(t, w) :=
        bind_ctx_unary (fun t => R (t, w)) 
          (fun k => _) (bind t |}.
   *)
End BindCtxUnary.

Section BindLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.
  
  Lemma ag_bind_l{Y}: forall (t: ctree E X) w (k: X -> ctree E Y) φ,
      <( t, w |= AG now φ )> -> (* [t] will loop forever. *)
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
  Lemma ag_bind_r{Y}: forall (t: ctree E Y) w (k: Y -> ctree E X) φ R,
      <( t, w |= φ AU (AX done R) )> ->
      (forall w (y: Y), R y w -> <( {k y}, w |= AG φ )>) ->
      <( {x <- t ;; k x} , w |= AG φ )>.
  Proof.
    coinduction R CIH.
    intros.
    generalize dependent k.
    induction H.
    - apply ax_done in H as (Hw & x & Heq & H).
      intros.
      assert (x <- t ;; k x ~ y <- Ret x;; k y).  
      { __upto_bind_sbisim. apply Heq. reflexivity. }.
      apply RStepA.
      + rewrite H1.
        rewrite bind_ret_l.
        fold (@entailsF (ctree E) E HE ctree_kripke X φ (k x) w) in *.
        fold (@entailsF (ctree E) E HE ctree_kripke Y <(AF φ)> _ w) in *.
        clear H1.
        
        specialize (H0 _ _ H).
        step in H0.
        apply H0.
      +
      apply H0.      
    - ddestruction H.

      
  Admitted.
End BindLemmas.
