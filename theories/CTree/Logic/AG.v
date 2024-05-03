From Coq Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice tactics.

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
      destruct H, H0.    
      apply can_step_not_done in H0. 
      split...
      intro v'.
      rewrite unfold_entailsF.
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
      destruct H, H0.     
      apply can_step_not_done in H0.
      split; auto.
      intro i.
      rewrite unfold_entailsF.
      apply H1.
      apply ktrans_br.
      exists i; auto.
  Qed.

  Lemma ag_ret: forall (x: X) w φ,      
      <( {Ret x}, w |= AG φ )> -> False.
  Proof.
    intros. 
    next in H.
    cdestruct H.
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
    next in H; destruct H, H0.
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
      + apply CIH.
        rewrite unfold_entailsF.
        now apply H0.
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
    cinduction H.
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
      rewrite ctl_vis in H.
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

  Lemma ag_iter_l{X I}: forall (k: I -> ctree E (I + X)) i w (x: I) φ,
      <( {k i}, w |= AG now φ )> ->
      <( {iter k i}, w |= AG now φ )>.
  Proof.
    intros.
    rewrite sb_unfold_iter.
    now apply ag_bind_l.
  Qed.

  (* vis φ <--> done Rr *)
  Lemma ag_iter_step{X I}: forall (k: I -> ctree E (I + X)) w w' (x x': I) φ,
      <( {k x}, w |= vis φ AU AX done
                  {fun (lr: I+X) w => lr = inl x' /\ w = w'} )> ->
      <( {iter k x'}, w' |= AG vis φ )> ->
      <( {iter k x}, w |= AG vis φ )>.
  Proof.
    intros.
    rewrite sb_unfold_iter.
    apply ag_bind_r with (R:=fun (lr : I + X) (w : World E) => lr = inl x' /\ w = w'); auto.
    now intros [l | r] w_ (Hinv & ->); inv Hinv.
  Qed.

  Notation MP X := (rel (ctree E X) (World E)).
  
  Program Definition ag_bind_clos{X Y} φ Post : mon (rel (ctree E Y) (World E)) :=
    {| body R t w :=
        bind_ctx1
          (fun (t: ctree E X) => <( t, w |= vis φ AU (AX done Post) )>)
          (fun (k: X -> ctree E Y) => forall (x: X) w, Post x w -> R (k x) w)
          t
    |}.
  Next Obligation.
    revert H0.
    apply leq_bind_ctx1; intros. 
    apply in_bind_ctx1; eauto.
  Qed.

  (* Here, I have to define a different monotone relation than [car_]
     to specialize the formulas to [p, q]. Very annoying. *)
  Program Definition car_'{X} p q : mon (rel (ctree E X) (World E)) :=
    {| body R := carF R p q |}.
  Next Obligation.
    inv H0.
    - apply RMatchA; auto.
    - destruct H2.
      apply RStepA; auto.
      split; auto.
  Qed.

  Notation cart' p q := (t (car_' p q)).

  Lemma ag_bind_ag{X Y} φ Post:
      ag_bind_clos (X:=X) (Y:=Y) φ Post <= cart' <( |- vis φ )> <( |- ⊥ )>.
  Proof.
    apply Coinduction.
    intros R t w; cbn.
    apply (leq_bind_ctx1 _ _
             (fun t => carF (T (car_' (entailsF <( vis {φ} )>) (entailsF <( ⊥ )>)) (ag_bind_clos φ Post) R)
    (entailsF <( vis {φ} )>) (entailsF <( ⊥ )>) t w)). 
    intros x Hx k Hk.
    cinduction Hx.
    - (* AX done R *)
      apply ax_done in H as (Hw & x & Heq & H).
      intros.
      specialize (Hk _ _ H); remember (k x) as K;
        destruct Hk; try contradiction; subst.
      apply RStepA.
      + rewrite Heq, bind_ret_l; try (exact (equ eq)).
        apply H0.
      + split.
        * rewrite Heq, bind_ret_l.
          now destruct H1.
        * intros t' w' TR.
          apply (id_T (car_' (entailsF <( vis {φ} )>) (entailsF <( ⊥ )>))).          
          cbn.
          destruct H1.
          apply H2.
          eapply ktrans_sbisim_ret with (t:=t0); auto.
    - (* vis φ *)
      destruct H0, H1; clear H0.
      destruct H1 as (t' & w' & TR).

      (* HERE *)
      cbn in TR, H3, H4.
      cbn in H.
      rewrite (ctree_eta t).      
      remember (observe t) as T.
      remember (observe t') as T'.
      rewrite ctl_vis in H.
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
      
      apply H2.
          cright.
          apply H0.

          apply RStepA.
          -- rewrite ctl_vis in H0 |- *.
             destruct H1.
             specialize (H2 _ _ TR').
             (* WHYYYYY cannot be proved from context *)
             admit.
          -- split.
          assert (H: carF <( |- vis φ )> <( |- ⊥ )> 

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
      rewrite ctl_vis in H.
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

        
    step in xx'.
    cbn; unfold observe; cbn.
    destruct xx'.
    - cbn in *.
      generalize (kk' _ _ H).
      apply (fequ RR).
      apply id_T.
    - constructor; intros ?. apply (fTf_Tf (fequ _)).
      apply in_bind_ctx2. apply H.
      red; intros. apply (b_T (fequ _)), kk'; auto.
    - constructor. apply (fTf_Tf (fequ _)).
      apply in_bind_ctx2. apply H.
      red; intros. apply (b_T (fequ _)), kk'; auto.
    - constructor. intro a. apply (fTf_Tf (fequ _)).
      apply in_bind_ctx2. apply H.
      red; intros. apply (b_T (fequ _)), kk'; auto.
    
  (* [iter k x, w] *)
  (* [k] will terminate with postcondition [RR] and invariant [φ] *)
  (* [x: I] *)
  (* AG <--> AF *)
  (* vis φ <--> done Rr *)
  Lemma ag_iter{X I}: forall (k: I -> ctree E (I + X)) w (x: I) φ R,
      vis_with φ w -> (* Worlds invariant: [w = Obs e v /\ φ e v] *)
      R x ->          (* Iterator invariant: [x] in [R] *)
      (forall (i: I) w,
          R i ->
          vis_with φ w ->
          <( {k i}, w |= (vis φ) AU (AX done
               {fun (lr: I+X) w => exists i', lr = inl i' /\ vis_with φ w /\ R i'}) )>) ->
      <( {iter k x}, w |= AG vis φ )>.
  Proof.
    intros.
    rewrite sb_unfold_iter.
    apply ag_bind_r with (R:=fun (lr : I + X) (w : World E) =>
                               exists i' : I, lr = inl i' /\ vis_with φ w /\ R i'); auto.
    intros [? | r] w' (l & Hinv & ? & ?); inv Hinv.    
    pose proof (H1 _ _ H3 H2) as H1'.
    remember (k l) as K.
    cinduction H1'; intros; subst.
    - apply ax_done in H4 as (Hd & ? & Heqk & (j & -> & ? & ?)).
      rewrite sb_unfold_iter.
      rewrite Heqk, bind_ret_l.
      rewrite sb_unfold_iter.
      apply ag_bind_r with (R:=fun (lr : I + X) (w : World E) =>
                                 exists i' : I, lr = inl i' /\ vis_with φ w /\ R i'); auto.
      intros [? | r] w' (l' & Hinv & ? & ?); inv Hinv.    
  Abort.

  Lemma ag_iter{X I}: forall (k: I -> ctree E (I + X)) w (x: I) φ R,
      vis_with φ w -> (* Worlds invariant: [w = Obs e v /\ φ e v] *)
      R x ->          (* Iterator invariant: [x] in [R] *)
      (forall (i: I) w,
          R i ->
          vis_with φ w ->
          <( {k i}, w |= (vis φ) AU (AX done
               {fun (lr: I+X) w => exists i', lr = inl i' /\ vis_with φ w /\ R i'}) )>) ->
      <( {iter k x}, w |= AG vis φ )>.
  Proof.
    (* Coinduction steps *)
    coinduction RR CIH.
    intros.
    apply RStepA; auto.
    split.
    - (* Not true, counter-example [k = fun x => Ret (inl x)] *)
  Admitted.

End BindLemmas.
