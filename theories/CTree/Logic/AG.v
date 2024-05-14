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
          apply ktrans_vis in H1 as (i & -> & <- & ?)...
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
  Lemma ag_iter_l{X I}: forall (k: I -> ctree E (I + X)) i w (x: I) φ,
      <( {k i}, w |= AG now φ )> ->
      <( {iter k i}, w |= AG now φ )>.
  Proof.
    intros.
    rewrite sb_unfold_iter.
    now apply ag_bind_l.
  Qed.

  Notation MP X := (rel (ctree E X) (World E)).
  Program Definition ag_bind_vis_clos{X Y} φ Post : mon (MP Y) :=
    {| body R t w :=
        bind_ctx1
          (fun (t: ctree E X) => <( t, w |= vis φ AU (AX finish Post) )>)
          (fun (k: X -> ctree E Y) =>
             forall (x: X) (e: E) (v: encode e), Post e v x -> R (k x) (Obs e v))
          t
    |}.
  Next Obligation.
    revert H0.
    apply leq_bind_ctx1; intros.
    apply in_bind_ctx1; eauto.
  Qed.

  Lemma ag_bind_vis_ag{X Y} φ Post:
      ag_bind_vis_clos (X:=X) (Y:=Y) φ Post <= cart <( |- vis φ )> <( |- ⊥ )>.
  Proof.    
    apply Coinduction.
    intros R t w; cbn.
    apply (leq_bind_ctx1 _ _
             (fun t => carF (entailsF <( vis {φ} )>) (entailsF <( ⊥ )>)
                      (carT (entailsF <( vis {φ} )>) (entailsF <( ⊥ )>)
                         (ag_bind_vis_clos φ Post) R) t w)). 
    intros x Hx k Hk.
    cinduction Hx.
    - (* AX done R *)
      apply ax_done in H as (Hw & x & Heq & e & v & -> & HPost).
      specialize (Hk _ _ _ HPost); remember (k x) as K;
        destruct Hk; try contradiction; subst.
      apply RStepA.
      + rewrite Heq, bind_ret_l; try (exact (equ eq)); auto.
      + split.
        * rewrite Heq, bind_ret_l.
          now destruct H0.
        * intros t' w' TR.
          apply (id_T (car_ (entailsF <( vis {φ} )>) (entailsF <( ⊥ )>))); cbn.
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
        inv H0; constructor.
      + intros k_ w_ TRk.
        apply ktrans_bind_inv in TRk as
            [(t0' & TR0 & Hd_ & Heq) | (x & w0 & TRt0 & Hd & TRk)].
        * (* [t0] steps and is not [Ret] *)
          apply (fT_T (mequ_clos_car (KS:=KripkeSetoidEqu))).
          cbn; eapply mequ_clos_ctor with (t1:=x <- t0';; k x) (w1:=w_); auto.
          clear Heq k_.            
          eapply (fTf_Tf (car_ <( |- vis φ )> <( |- ⊥ )>)).
          apply in_bind_ctx1.
          -- rewrite unfold_entailsF; auto.             
          -- intros.
             apply (b_T (car_ <( |- vis φ )> <( |- ⊥ )>)); cbn; auto.
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
  Lemma ag_bind_vis{X Y}: forall (t: ctree E X)
                          w (k: X -> ctree E Y) φ R,
      <( t, w |= (vis φ) AU (AX finish R) )> ->
      (forall (x: X) (e: E) (v: encode e), R e v x -> <( {k x}, {Obs e v} |= AG vis φ )>) ->
      <( {x <- t ;; k x} , w |= AG vis φ )>.
  Proof.
    intros.
    rewrite unfold_entailsF.
    apply (ft_t (ag_bind_vis_ag φ R)).
    cbn.
    apply in_bind_ctx1; auto.
  Qed.

  Lemma ag_iter_vis{X I}: forall (k: I -> ctree E (I + X)) w (x: I) φ R,
      R x ->          (* Iterator invariant: [x] in [R] *)
      vis_with φ w -> (* Worlds invariant: [w = Obs e v /\ φ e v] *)
      (forall (i: I) (e: E) (v: encode e),
          R i ->
          φ e v ->
          <( {k i}, {Obs e v} |= AX (vis φ AU AX finish
                               {fun (e: E) (v: encode e) (lr: I+X) =>
                                  exists i' : I, lr = inl i' /\ φ e v /\ R i'}))>) ->
      <( {iter k x}, w |= AG vis φ )>.
  Proof with auto with ctl.
    (* Coinduction steps *)
    intros.
    generalize dependent x.
    generalize dependent w.    
    coinduction RR CIH; intros.
    apply RStepA...
    split; inv H0.
    - (* can_step (iter k x) w *)
      specialize (H1 _ _ _ H H2) as HAX.
      cdestruct HAX.
      destruct Hs as (k' & w' & TR).
      rewrite sb_unfold_iter.
      specialize (HAX _ _ TR); cdestruct HAX.
      + apply ax_done in H0 as (_ & ? & Heqt & e' & v' & -> & ? & -> & Hφ & HR).                
        apply can_step_bind_l with t (Obs e' v')...
      + destruct H3.
        apply can_step_bind_l with t w...
        inv H0...
    - (* coinductive step *)
      intros t' w' TR.
      rewrite unfold_iter in TR.
      apply ktrans_bind_inv in TR as [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ft_t (ag_bind_vis_ag φ
                       (fun (e: E) (v: encode e) (lr: I+X) =>
                          exists i' : I, lr = inl i' /\ φ e v /\ R i'))); cbn.
        apply in_bind_ctx1.
        * specialize (H1 _ _ _ H H2) as HAX.
          cdestruct HAX...
        * intros [l | r] e' v' (i & Hinv & Hφ & HR); inv Hinv.
          rewrite sb_guard.
          apply CIH...
      + (* [k x] returns *)        
        specialize (H1 _ _ _ H H2) as HAX.        
        cdestruct HAX.
        specialize (HAX _ _ TRt0).
        apply au_stuck in HAX.
        cdestruct HAX.
        now apply can_step_stuck in Hs0.
  Qed.
  
  Program Definition ag_bind_pure_clos{X Y} Post : mon (MP Y) :=
    {| body R t w :=
        bind_ctx1
          (fun (t: ctree E X) => <( t, w |= pure AU AX done {fun x w => Post x /\ w = Pure })>)
          (fun (k: X -> ctree E Y) => forall (x: X), Post x -> R (k x) Pure)
          t
    |}.
  Next Obligation.
    revert H0.
    apply leq_bind_ctx1; intros.
    apply in_bind_ctx1; eauto.
  Qed.

  Lemma ag_bind_pure_ag{X Y} Post:
      ag_bind_pure_clos (X:=X) (Y:=Y) Post <= cart <( |- pure )> <( |- ⊥ )>.
  Proof.
    apply Coinduction.
    intros R t w; cbn.
    apply (leq_bind_ctx1 _ _
             (fun t => carF (entailsF <( pure )>) (entailsF <( ⊥ )>)
                      (carT (entailsF <( pure )>) (entailsF <( ⊥ )>)
                         (ag_bind_pure_clos Post) R) t w)). 
    intros x Hx k Hk.
    cinduction Hx.
    - (* AX done R *)
      apply ax_done in H as (Hw & x & Heq & HPost & ->). 
      specialize (Hk _ HPost); remember (k x) as K;
        destruct Hk; try contradiction; subst.
      apply RStepA.
      + rewrite Heq, bind_ret_l; try (exact (equ eq)); auto.
      + split.
        * rewrite Heq, bind_ret_l.
          now destruct H0.
        * intros t' w' TR.
          apply (id_T (car_
                         (entailsF <( now {fun w0 : World E => w0 = w} )>)
                         (entailsF <( ⊥ )>))); cbn.
          destruct H0.
          apply H1.
          eapply ktrans_sbisim_ret with (t:=t0); auto.
    - (* pure *)
      destruct H0, H1; clear H0.
      destruct H1 as (t' & w' & TR).
      apply RStepA; auto.
      split.
      + apply can_step_bind_l with t' w'; auto.
        destruct (H3 _ _ TR); try contradiction.
        destruct H1.
        inv H0; constructor.
      + intros k_ w_ TRk.
        apply ktrans_bind_inv in TRk as
            [(t0' & TR0 & Hd_ & Heq) | (x & w0 & TRt0 & Hd & TRk)].
        * (* [t0] steps and is not [Ret] *)
          apply (fT_T (mequ_clos_car (KS:=KripkeSetoidEqu))).
          cbn; eapply mequ_clos_ctor with (t1:=x <- t0';; k x) (w1:=w_); auto.
          clear Heq k_.            
          eapply (fTf_Tf (car_ <( |- pure )> <( |- ⊥ )>)).
          apply in_bind_ctx1.
          -- rewrite unfold_entailsF; auto.             
          -- intros.
             apply (b_T (car_ <( |- pure )> <( |- ⊥ )>)); cbn; auto.
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
  Lemma ag_bind_pure{X Y}: forall (t: ctree E X)
                          w (k: X -> ctree E Y) R,
      <( t, w |= pure AU AX done {fun x w => R x /\ w = Pure })> ->
      (forall (x: X), R x -> <( {k x}, {Pure} |= AG pure )>) ->
      <( {x <- t ;; k x} , w |= AG pure )>.
  Proof.
    intros.
    rewrite unfold_entailsF.
    apply (ft_t (ag_bind_pure_ag R)).
    cbn.
    apply in_bind_ctx1; auto.
  Qed.
  
  Lemma ag_iter_pure{X I}: forall (k: I -> ctree E (I + X)) (x: I) (R: I -> Prop),
      R x ->          (* Iterator invariant: [x] in [R] *)
      (forall (i: I),
          R i ->
          <( {k i}, Pure |= AX (pure AU AX done
                               {fun (lr: I+X) (w: World E) =>
                                  exists i' : I, lr = inl i' /\ R i' /\ w = Pure}))>) ->
      <( {iter k x}, Pure |= AG pure )>.
  Proof with auto with ctl.
    (* Coinduction steps *)
    intros * HR H.
    generalize dependent x.
    coinduction RR CIH; intros.
    apply RStepA...
    split.
    - (* can_step (iter k x) w *)
      specialize (H _ HR) as HAX.
      cdestruct HAX.
      destruct Hs as (k' & w' & TR).
      rewrite sb_unfold_iter.
      specialize (HAX _ _ TR); cdestruct HAX.
      + apply ax_done in H0 as (_ & ? & Heqt & i & -> & HR' & ->). 
        apply can_step_bind_l with t Pure...
      + destruct H1.
        inv H0.
        apply can_step_bind_l with t Pure...
    - (* coinductive step *)
      intros t' w' TR.
      rewrite unfold_iter in TR.
      apply ktrans_bind_inv in TR as [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ft_t (ag_bind_pure_ag
                       (fun (lr: I+X) => exists i' : I, lr = inl i' /\ R i'))); cbn.
        apply in_bind_ctx1.
        * specialize (H _ HR) as HAX.
          cdestruct HAX.
          specialize (HAX _ _ TR0).
          assert(Hdeq:
                  equiv_ctl (X:= I+X)
                  <(done {fun (x0 : I + X) (w : World E) =>
                            (exists i' : I, x0 = inl i' /\ R i') /\ w = Pure})>
                  <(done {fun (x0 : I + X) (w : World E) =>
                            exists i' : I, x0 = inl i' /\ R i' /\ w = Pure})>);
            [|rewrite Hdeq]...
          split; intros H'; inv H'; destruct H0 as [? Hb].
          -- destruct H0 as (i & -> & ?); constructor; eauto.
          -- inv Hb.
          -- destruct Hb as (-> & ? & ?); constructor; eauto.
          -- destruct Hb as (-> & ? & Hinv); inv Hinv.
        * intros ? (i & -> & HR').
          rewrite sb_guard.
          apply CIH...
      + (* [k x] returns *)        
        specialize (H _ HR) as HAX.        
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

  Theorem ag_bind_state_l{X Y}: forall s w (t: ctree E Y) (k: Y -> ctree E X) φ,
      <( {interp_state h t s}, w |= AG now φ )> ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AG now φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    now apply ag_bind_l.
  Qed.

  Theorem ag_bind_state_vis{X Y}: forall s (t: ctree E Y) (k: Y -> ctree E X) w φ R,
      <( {interp_state h t s}, w |= (vis φ) AU (AX finish R) )> ->
      (forall (e: F) (v: encode e) (y: Y) (s: S),
          R e v (y, s) ->
          <( {interp_state h (k y) s}, {Obs e v} |= AG vis φ )>) ->
      <( {interp_state h (x <- t ;; k x) s} , w |= AG vis φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply ag_bind_vis with (R:=R); auto.
    intros [y s'] w' Hr; auto.
  Qed.

  Theorem ag_bind_state_pure{X Y}: forall s (t: ctree E Y) w (k: Y -> ctree E X) R,
      <( {interp_state h t s}, w |= pure AU (AX done {fun x w => R x /\ w = Pure}) )> ->
      (forall (y: Y) (s: S), R (y, s) -> <( {interp_state h (k y) s}, Pure |= AG pure )>) ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AG pure )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply ag_bind_pure with (R:=R); auto.
    intros [y s'] Hr; auto.
  Qed.
  
  Theorem ag_iter_state_vis{X I}: forall s (k: I -> ctree E (I + X)) w (x: I) φ R,
      R (x, s) ->     (* Iterator invariant: [x] in [R] *)
      vis_with φ w -> (* Worlds invariant: [w = Obs e v /\ φ e v] *)
      (forall (x: I) (s: S) (e: F) (v: encode e),
          R (x, s) ->
          φ e v ->
          <( {interp_state h (k x) s}, {Obs e v} |= AX (vis φ AU AX finish
             {fun (e: F) (v: encode e) (lr: (I+X) * S) =>
                exists (i' : I) (s': S), lr = (inl i', s') /\ φ e v /\ R (i', s')}))>) ->
      <( {interp_state h (iter k x) s}, w |= AG vis φ )>.
  Proof with auto with ctl.
    intros.
    rewrite interp_state_unfold_iter.
    inv H0.
    generalize dependent x.
    generalize dependent e.
    generalize dependent s.
    coinduction RR CIH; intros.
    apply RStepA; [apply ctl_vis; now constructor|].
    split.
    - specialize (H1 _ _ _ _ H H2).
      cdestruct H1.
      destruct Hs as (t' & w' & TR).
      specialize (H1 _ _ TR).
      apply can_step_bind_l with t' w'; auto.
      cdestruct H1.
      + now apply ax_done in H0 as (? & ?).
      + inv H0; constructor.
    - intros t' w' TR.
      apply ktrans_bind_inv in TR as [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ft_t (ag_bind_vis_ag φ
                       (fun (e: F) (v: encode e) (lr: (I+X) * S) =>
                          exists (i': I) (s': S), lr = (inl i', s') /\ φ e v /\ R (i', s')))); cbn.
        apply in_bind_ctx1.
        * specialize (H1 _ _ _ _ H H2) as HAX.
          cdestruct HAX.
          specialize (HAX _ _ TR0).
          apply HAX.
        * intros (lr' & s_) e' v' (i & s' & Hinv & Hφ & HR'); inv Hinv.
          rewrite sb_guard.
          setoid_rewrite interp_state_unfold_iter.
          apply CIH...
      + (* [k x] returns *)        
        specialize (H1 _ _ _ _ H H2) as HAX.        
        cdestruct HAX.
        specialize (HAX _ _ TRt0).
        apply au_stuck in HAX.
        cdestruct HAX.
        now apply can_step_stuck in Hs0.
  Qed.        
    
End CtlAgState.
