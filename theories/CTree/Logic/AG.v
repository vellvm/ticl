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
  CTree.Interp.State
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Setoid
  CTree.Logic.AX
  CTree.Logic.AF
  Logic.Ctl
  Logic.Tactics
  Logic.Kripke
  Events.WriterE.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

(* Lemmas on the structure of ctree [t] and AG proofs *)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma ag_now: forall e (k: encode e -> ctree E X)
                  (v : encode e) w φ,
      (φ w /\ not_done w /\
         forall v, <( {k v}, {Obs e v} |= AG now φ )>) <->
        <( {Vis e k}, w |= AG now φ )>.
  Proof with eauto with ctl.
    split; intros.
    - destruct H as (Hφ & Hd & H).
      next; split.
      + inv Hd.
        * apply ctl_now...
        * apply ctl_now...          
      + apply ax_vis... 
    - cdestruct H; try contradiction.
      destruct H0 as (Hs & Ht').
      apply ctl_now in H as (? & ?).
      split; [|split]...
      intro v'.
      rewrite unfold_entailsF.
      apply Ht', ktrans_vis...
  Qed.
  
  Lemma ag_br: forall n (k: fin' n -> ctree E X) w φ,
      (not_done w /\
         forall (i: fin' n), <( {k i}, w |= AG now φ )>) <->
        <( {Br n k}, w |= AG now φ )>.
  Proof with auto with ctl.
    split; intros.
    - destruct H as (Hd & H).
      next; split.
      + specialize (H Fin.F1).
        next in H.
        destruct H.
        now cbn in *.
      + apply ax_br... 
    - cdestruct H; try contradiction.
      destruct H0 as (Hs & Ht').
      apply ctl_now in H as (? & ?).
      split...
      intro i.
      rewrite unfold_entailsF.
      apply Ht', ktrans_br.
      exists i...
  Qed.

  Lemma ag_stuck: forall w φ,
      <( {stuck: ctree E X}, w |= AG φ )> -> False.
  Proof.
    intros.
    cdestruct H; try contradiction; subst.
    destruct H0.
    now apply can_step_stuck in H0.
  Qed.

  Lemma ag_ret: forall (x: X) w φ,      
      <( {Ret x}, w |= AG φ )> -> False.
  Proof.
    intros. 
    cdestruct H; try contradiction.
    destruct H0 as ((S & w' & TR) & H0).
    specialize (H0 _ _ TR).
    cbn in TR.
    dependent destruction TR; observe_equ x;
      rewrite <- Eqt, H in H0; eapply ag_stuck;
      rewrite unfold_entailsF; apply H0.
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
  Lemma ag_iter_l{X I}: forall (k: I -> ctree E (I + X)) i w (x: I) φ,
      <( {k i}, w |= AG now φ )> ->
      <( {iter k i}, w |= AG now φ )>.
  Proof.
    intros.
    rewrite sb_unfold_iter.
    now apply ag_bind_l.
  Qed.

  Notation MP X := (rel (ctree E X) (World E)).
  Program Definition ag_bind_now_clos{X Y} φ Post : mon (MP Y) :=
    {| body R t w :=
        bind_ctx1
          (fun (t: ctree E X) => <( t, w |= now φ AU (AX done Post) )>)
          (fun (k: X -> ctree E Y) =>
             forall (x: X) (w: World E), Post x w -> R (k x) w)
          t
    |}.
  Next Obligation.
    revert H0.
    apply leq_bind_ctx1; intros.
    apply in_bind_ctx1; eauto.
  Qed.

  Lemma ag_bind_now_ag{X Y} φ Post:
      ag_bind_now_clos (X:=X) (Y:=Y) φ Post <= cart <( |- now φ )> <( |- ⊥ )>.
  Proof.    
    apply Coinduction.
    intros R t w; cbn.
    apply (leq_bind_ctx1 _ _
             (fun t => carF (entailsF <( now φ )>) (entailsF <( ⊥ )>)
                      (carT (entailsF <( now φ )>) (entailsF <( ⊥ )>)
                         (ag_bind_now_clos φ Post) R) t w)). 
    intros x Hx k Hk.
    cinduction Hx.
    - (* AX done R *)
      apply ax_done in H as (Hw & x & Heq & HPost).
      specialize (Hk _ _ HPost); remember (k x) as K;
        destruct Hk; try contradiction; subst.
      apply RStepA.
      + rewrite Heq, bind_ret_l; try (exact (equ eq)); auto.
      + split.
        * rewrite Heq, bind_ret_l.
          now destruct H0.
        * intros t' w' TR.
          apply (id_T (car_ (entailsF <( now φ )>) (entailsF <( ⊥ )>))); cbn.
          destruct H0.
          apply H1.
          eapply ktrans_sbisim_ret with (t:=t0); auto.
    - (* vis φ *)
      destruct H0, H1; clear H0.
      destruct H1 as (t' & w' & TR).
      apply RStepA; auto.
      split.
      + apply can_step_bind_l with t' w'; auto.
        destruct (H3 _ _ TR); try contradiction.
        destruct H1.
        now apply ctl_now in H0.
      + intros k_ w_ TRk.
        apply ktrans_bind_inv in TRk as
            [(t0' & TR0 & Hd_ & Heq) | (x & w0 & TRt0 & Hd & TRk)].
        * (* [t0] steps and is not [Ret] *)
          apply (fT_T (mequ_clos_car (KS:=KripkeSetoidEqu))).
          cbn; eapply mequ_clos_ctor with (t1:=x <- t0';; k x) (w1:=w_); auto.
          clear Heq k_.            
          eapply (fTf_Tf (car_ <( |- now φ )> <( |- ⊥ )>)).
          apply in_bind_ctx1.
          -- rewrite unfold_entailsF; auto.             
          -- intros.
             apply (b_T (car_ <( |- now φ )> <( |- ⊥ )>)); cbn; auto.
        * (* [t0] steps and is [Ret], contradiction *)
          ddestruction Hd; subst;
            specialize (H3 _ _ TRt0); ddestruction H3;
            try contradiction;
            destruct H1, H0;
            rewrite can_step_bind in H1;
            destruct H1 as [(? & ? & TRinv & ?) | (? & ? & TRinv & ?)];
            now apply ktrans_stuck in TRinv.
  Qed.

  (* [t] satisfies [φ] until it terminates with post-condition [R],
     then forall x w, R x w -> k x, w satisfies [φ] forever. *)
  Lemma ag_bind_r{X Y}: forall (t: ctree E X)
                          w (k: X -> ctree E Y) φ R,
      <( t, w |= now φ AU AX done R )> ->
      (forall (x: X) (w: World E), R x w -> <( {k x}, w |= AG now φ )>) ->
      <( {x <- t ;; k x} , w |= AG now φ )>.
  Proof.
    intros.
    rewrite unfold_entailsF.
    apply (ft_t (ag_bind_now_ag φ R)).
    cbn.
    apply in_bind_ctx1; auto.
  Qed.

  Lemma ag_iter{X I}: forall (k: I -> ctree E (I + X)) w (x: I) φ R,
      R x ->          (* Iterator invariant: [x] in [R] *)
      φ w ->          (* Worlds invariant: [φ w] *)
      not_done w ->
      (forall (i: I) (w: World E),
          R i ->
          not_done w ->
          φ w ->
          <( {k i}, w |= AX (now φ AU AX done
                 {fun (lr: I+X) (w: World E) =>
                    exists i' : I, lr = inl i' /\ φ w /\ not_done w /\ R i'}))>) ->
      <( {iter k x}, w |= AG now φ )>.
  Proof with auto with ctl.
    (* Coinduction steps *)
    intros.
    generalize dependent x.
    generalize dependent w.    
    coinduction RR CIH; intros.
    apply RStepA.
    - apply ctl_now; auto.
    - split. 
      + (* can_step (iter k x) w *)
        specialize (H2 _ _ H H1 H0) as HAX.
        cdestruct HAX.
        destruct Hs as (k' & w' & TR).
        rewrite sb_unfold_iter.
        specialize (HAX _ _ TR); cdestruct HAX.
        * apply ax_done in H3 as (Hd & y & Hy & i & -> & ? & _ & ?).
          apply can_step_bind_l with k' w0... 
        * destruct H4.
          apply can_step_bind_l with k' w0...
          apply ctl_now in H3 as (? & ?)...
      + (* coinductive step *)
        intros t' w' TR.
        rewrite unfold_iter in TR.
        apply ktrans_bind_inv in TR as
            [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
        * (* [k x] steps *)
          rewrite Heq; clear Heq t'.
          apply (ft_t (ag_bind_now_ag φ
             (fun (lr: I+X) (w0: World E) =>
                exists i' : I, lr = inl i' /\ φ w0 /\ not_done w0 /\ R i'))); cbn.
          apply in_bind_ctx1.
          -- specialize (H2 _ _ H H1 H0) as HAX.
             cdestruct HAX...
          -- intros [l | r] w_ (i & Hinv & Hφ & Hd & HR); inv Hinv.
             rewrite sb_guard.
             apply CIH...
        * (* [k x] returns *)        
          specialize (H2 _ _ H H1 H0) as HAX.        
          cdestruct HAX.
          specialize (HAX _ _ TRt0).
          apply au_stuck in HAX.
          cdestruct HAX.
          now apply can_step_stuck in Hs0.
  Qed.
  
End BindLemmas.

(*| Combinators for [interp_state] |*)
Section CtlAgState.
  Context {E F S: Type} {HE: Encode E} {HF: Encode F}
    (h: E ~> stateT S (ctree F)).

  Theorem ag_state_bind_l{X Y}: forall s w (t: ctree E Y) (k: Y -> ctree E X) φ,
      <( {interp_state h t s}, w |= AG now φ )> ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AG now φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    now apply ag_bind_l.
  Qed.

  Theorem ag_state_bind_r{X Y}: forall s (t: ctree E Y) (k: Y -> ctree E X) w φ
                                  (R: Y -> S -> World F -> Prop),
      <( {interp_state h t s}, w |= now φ AU (AX done {fun '(x, s) w => R x s w}) )> ->
      (forall (y: Y) (s: S) (w: World F),
          R y s w ->
          <( {interp_state h (k y) s}, w |= AG now φ )>) ->
      <( {interp_state h (x <- t ;; k x) s} , w |= AG now φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply ag_bind_r with (R:=fun '(x, s) w => R x s w); auto.
    intros [y s'] w' Hr; auto.
  Qed.

  Theorem ag_state_iter{X I}: forall s (k: I -> ctree E (I + X)) w (x: I) φ R,
      R x s ->        (* Iterator invariant: [x] in [R] *)
      φ w ->          (* Worlds invariant: [φ w] *)
      not_done w ->
      (forall (x: I) (s: S) (w: World F),
          R x s ->
          φ w ->
          not_done w ->
          <( {interp_state h (k x) s}, w |= AX (now φ AU AX done
             {fun (lr: (I+X) * S) (w: World F) =>
                exists (i' : I) (s': S), lr = (inl i', s') /\ φ w /\
                                      not_done w /\ R i' s'}))>) ->
      <( {interp_state h (iter k x) s}, w |= AG now φ )>.
  Proof with auto with ctl.
    intros.
    rewrite interp_state_unfold_iter.
    generalize dependent x.
    generalize dependent s.
    generalize dependent w.
    coinduction RR CIH; intros.
    apply RStepA; [apply ctl_now; now constructor|].
    split.
    - (* can_step *)
      specialize (H2 _ _ _ H H0 H1).
      cdestruct H2.
      destruct Hs as (t' & w' & TR).
      specialize (H2 _ _ TR).
      apply can_step_bind_l with t' w'; auto.
      cdestruct H2.
      + now apply ax_done in H2 as (? & ?).
      + now apply ctl_now in H2 as (? & ?). 
    - intros t' w' TR.
      apply ktrans_bind_inv in TR as
          [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ft_t (ag_bind_now_ag φ
                       (fun (lr: (I+X) * S) (w: World F) =>
                          exists (i': I) (s': S), lr = (inl i', s') /\
                                               φ w /\ not_done w /\ R i' s'))); cbn.
        apply in_bind_ctx1.
        * specialize (H2 _ _ _ H H0 H1) as HAX.
          cdestruct HAX.
          specialize (HAX _ _ TR0).
          apply HAX.
        * intros (lr' & s_) w_ (i & s' & Hinv & Hφ & Hd' & HR'); inv Hinv.
          rewrite sb_guard.
          setoid_rewrite interp_state_unfold_iter.
          apply CIH...
      + (* [k x] returns *)        
        specialize (H2 _ _ _ H H0 H1) as HAX.        
        cdestruct HAX.
        specialize (HAX _ _ TRt0).
        apply au_stuck in HAX.
        cdestruct HAX.
        now apply can_step_stuck in Hs0.
  Qed.        
End CtlAgState.

Section CtlAgW.
  Context {E Σ W: Type} {HE: Encode E} (h:E ~> stateT Σ (ctree void)). 

  Theorem ag_iterW{X I}: forall (σ: Σ) (k: I -> ctree E (I + X)) (i: I) (φ: Σ -> Prop) R,
      R i ->          (* Iterator invariant [R] *)
      φ σ ->          (* Initial state precondition [φ] *)
      (forall (x: I) (σ: Σ),
          R x ->
          φ σ ->
          <( {interp_state (h_writerΣ h) (k x) σ}, {Obs (Log σ) tt} |=
              AX (visW φ AU AX
                    (finishW {fun (lr: I + X) (σ _: Σ) => 
                                exists (i: I), lr = inl i /\ R i /\ φ σ})))>) ->
      <( {interp_state (h_writerΣ h) (iter k i) σ}, {Obs (Log σ) tt} |= AG visW φ )>.
  Proof with eauto with ctl.
    setoid_rewrite ctl_vis_now.
    setoid_rewrite ctl_finish_done.
    intros.
    rewrite interp_state_unfold_iter.
    generalize dependent i.
    generalize dependent σ.
    coinduction RR CIH; intros.
    apply RStepA; [apply ctl_now; eauto with ctl |].
    split.
    - (* can_step *)
      specialize (H1 _ _ H H0).
      cdestruct H1.
      destruct Hs as (t' & w' & TR).
      specialize (H1 _ _ TR).
      apply can_step_bind_l with t' w'...
      cdestruct H1.
      + apply ax_done in H1 as (? & ?)...
      + apply ctl_now in H1; destruct H1...
    - intros t' w' TR.
      apply ktrans_bind_inv in TR as
          [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ft_t (ag_bind_now_ag
                       (fun w => (exists (e : writerE Σ) (v : encode e),
                                  w = Obs e v /\
                                    (let 'Log v0 as x := e return (encode x -> Prop) in
                                     fun 'tt => φ v0) v))
                       (fun (lr: (I+X) * Σ) (w: World (writerE Σ)) =>
                          exists (i: I) (σ: Σ), lr = (inl i, σ) /\
                                             φ σ /\ not_done w /\ R i))); cbn.
        apply in_bind_ctx1.
        * specialize (H1 _ _ H H0) as HAX.
          cdestruct HAX.
          specialize (HAX _ _ TR0).
          apply HAX.
        * intros (lr' & s_) w_ (i & s' & Hinv & Hφ & Hd' & HR'); inv Hinv.
          rewrite sb_guard.
          setoid_rewrite interp_state_unfold_iter.
          apply CIH...
      + (* [k x] returns *)        
        specialize (H2 _ _ _ H H0 H1) as HAX.        
        cdestruct HAX.
        specialize (HAX _ _ TRt0).
        apply au_stuck in HAX.
        cdestruct HAX.
        now apply can_step_stuck in Hs0.
  Qed.        
  Proof.
    intros.
    rewrite ctl_vis_now.
    eapply ag_state_iter with (R:=fun i σ => R i /\ φ σ); auto with ctl.
    - eexists (Log σ), tt; auto.
    - intros j σ' w [HR Hφ] ([] & [] & -> & ?) _.
      setoid_rewrite ctl_vis_base in H1.
      setoid_rewrite ctl_finish_done in H1.
      apply H1.
    - now split.
    - now econstructor.
    - intros i σ' [] [] [? ?] ?.
      assert(Hf: equiv_ctl (X:=I+X)
                   <(finishW \ σ0 lr, exists (i : I), lr = @inl _ X i /\ R i /\ φ σ0)>
                   <(finish {fun (e : writerE Σ) (v : encode e) (lr : (I + X) * Σ) =>
                              exists (i' : I) (s' : Σ),
                                lr = (@inl _ X i', s') /\
                                  (let 'Log σ1 as x0 := e return (encode x0 -> Prop) in fun 'tt => φ σ1) v /\ R i' /\ φ s'})>).
      {
        split; intros Hinv; inv Hinv.
        - destruct H5 as ([] & [] & Hcontra & ?).
          inv Hcontra.
        - destruct x0 as ([] & lr), H5 as ([] & [] & Hinv & i' & -> & HR & Hσ1).
          ddestruction Hinv.
          rewrite unfold_entailsF.
          unfold finish_with.
          constructor.
          apply H1.
    
    
