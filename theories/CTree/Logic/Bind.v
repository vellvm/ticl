From Coinduction Require Import
  coinduction lattice.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.EX
  Logic.Ctl.

Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

Section BindLemmas.
  Context {E: Type} {HE: Encode E}.

  (*| Prove by induction on formulas [φ], very useful! |*)
  Theorem ctll_bind_l{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
      <( t, w |= φ )> ->
      <( {x <- t ;; k x}, w |= φ )>.
  Proof with auto with ctl.
    intros.
    generalize dependent t.
    revert X Y w k.
    induction φ; intros; try destruct q; intros. 
    - (* NOW *) cdestruct H; now csplit.
    - (* AU *)
      cinduction H; intros; subst.
      + (* MatchA *) cleft...
      + (* StepA *)
        cright; csplit... 
        * (* can_step *)          
          destruct Hs as (t' & w' & TR').
          eapply can_step_bind_l with t' w'; auto.
          specialize (Hau _ _ TR').
          change (cau (entailsL Y φ1) (entailsL Y φ2) ?t ?w)
            with <( t, w |= φ1 AU φ2 )> in Hau.
          now eapply ctll_not_done in Hau. 
        * (* AX AF *)
          intros t_ w' TR_.
          apply ktrans_bind_inv in TR_ as
              [(t' & TR' & Hd & ->) |
                (x & ? & TR' & Hr & TRk)].
          -- specialize (Hau _ _ TR').
             apply HInd...
          -- specialize (HInd _ _ TR').
             apply ctll_not_done in HInd; inv Hr; inv HInd.
    - (* EU *)      
      cinduction H; intros; subst.
      + (* MatchE *) cleft...
      + (* StepE *)
        cright; csplit...
        exists (x <- t0 ;; k x), w0; split.
        * apply ktrans_bind_l...
          now apply ctll_not_done in HInd. 
        * apply HInd.
    - (* AX *)
      cdestruct H; csplit...
      + (* can_step *) destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'...
        eapply ctll_not_done, (H _ _ TR).
      + (* forall *) intros t' w' TR.
        apply ktrans_bind_inv in TR as
            [(t_ & TR' & Hd & ->) |
              (x & w_ & TR' & Hr & TRk)].
        * apply IHφ2, H...
        * specialize (H _ _ TR').
          inv Hr; apply ctll_not_done in H; inv H.
    - (* EX *)
      cdestruct H; csplit...
      exists (x <- t0;; k x), w0; split...
      apply ktrans_bind_l...
      now apply ctll_not_done in H.
    - (* AG *)
      generalize dependent t.
      revert w.
      coinduction R CIH; intros; constructor.
      + apply IHφ.
        now cdestruct H.
      + split.
        * cdestruct H.
          destruct Hs as (t' & w' & TR).
          apply can_step_bind_l with t' w'...
          eapply ctll_not_done, (H _ _ TR).
        * intros t' w' TR.
          cdestruct H.
          apply ktrans_bind_inv in TR as
              [(t_ & TR' & Hd & ->) |
                (x & w_ & TR' & Hr & TRk)].
          -- apply CIH...
          -- specialize (H _ _ TR').
             inv Hr; apply ctll_not_done in H; inv H.
    - (* EG *)
      generalize dependent t.
      revert w.
      coinduction R CIH; intros; constructor.
      + apply IHφ.
        now cdestruct H.
      + cdestruct H.
        * exists (x <- t0;; k x), w0.
          split...
          apply ktrans_bind_l...
          eapply ctll_not_done, H.
    - (* AND *)
      cdestruct H; csplit...
    - (* OR *)
      cdestruct H; [cleft | cright]...
  Qed.

  (*| Bind lemmas for [AX] |*)
  Theorem axl_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ t, w |= φ AX done R ]> ->
      (forall x w, R x w -> <( {k x}, w |= φ AX ψ )>) ->
      <( {x <- t ;; k x}, w |= φ AX ψ )>.  
  Proof with eauto with ctl.
    intros.
    cdestruct H; csplit...
    - now apply ctll_bind_l.
    - (* can_step *)
      destruct Hs as (t' & w' & TR).
      eapply can_step_bind_r.
      + cleft.
        csplit...
        csplit...
      + intros y wr HR.
        specialize (H0 _ _ HR) as Hax.   
        now cdestruct Hax.
    - intros t' w' TR'. 
      apply ktrans_bind_inv in TR' as
          [(t_ & TR_ & Hd & ->) |
            (x & w_ & TR_ & Hr & TRk)].
      + specialize (H _ _ TR_).
        cdestruct H; inv Hd.
      + specialize (H _ _ TR_); inv Hr; cdestruct H.
        * eapply ktrans_to_done in TR_ as (? & ->).
          specialize (H0 _ _ H) as Hax.
          cdestruct Hax...
        * eapply ktrans_to_finish in TR_ as (? & ->).
          specialize (H0 _ _ H) as Hax.
          cdestruct Hax...
  Qed.
  
  Theorem axr_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ t, w |= φ AX done R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ AX ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ AX ψ ]>.  
  Proof with eauto with ctl.
    intros.
    cdestruct H; csplit...
    - now apply ctll_bind_l.
    - (* can_step *)
      destruct Hs as (t' & w' & TR).
      eapply can_step_bind_r.
      + cleft.
        csplit...
        csplit...
      + intros y wr HR.
        specialize (H0 _ _ HR) as Hax.   
        now cdestruct Hax.
    - intros t' w' TR'. 
      apply ktrans_bind_inv in TR' as
          [(t_ & TR_ & Hd & ->) |
            (x & w_ & TR_ & Hr & TRk)].
      + specialize (H _ _ TR_).
        cdestruct H; inv Hd.
      + specialize (H _ _ TR_); inv Hr; cdestruct H.
        * eapply ktrans_to_done in TR_ as (? & ->).
          specialize (H0 _ _ H) as Hax.
          cdestruct Hax...
        * eapply ktrans_to_finish in TR_ as (? & ->).
          specialize (H0 _ _ H) as Hax.
          cdestruct Hax...
  Qed.

  (*| Bind lemmas for [EX] |*)
  Typeclasses Transparent sbisim.
  Theorem exl_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ ψ r,
      <[ t, w |= φ EX done= r w' ]> ->
      <( {k r}, w' |= φ EX ψ )> ->
      <( {x <- t ;; k x}, w |= φ EX ψ )>.
  Proof with eauto with ctl.
    intros.
    assert(Hd: <( t, w |= φ )> /\ (exists x : Y, t ~ Ret x /\ r = x /\ w' = w)) by
      (apply ex_done in H as (? & ?); split; auto).
    destruct Hd as (? & y & Heqt & -> & ->).
    now rewrite Heqt, bind_ret_l.
  Qed.

  Theorem exr_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ ψ r,
      <[ t, w |= φ EX done= r w' ]> ->
      <[ {k r}, w' |= φ EX ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ EX ψ ]>.
  Proof with eauto with ctl.
    intros.
    assert(Hd: <( t, w |= φ )> /\ (exists x : Y, t ~ Ret x /\ r = x /\ w' = w)) by
      (apply ex_done in H as (? & ?); split; auto).
    destruct Hd as (? & y & Heqt & -> & ->).
    now rewrite Heqt, bind_ret_l.
  Qed.
  
  (*| Bind lemmas for [AU] |*)
  Typeclasses Transparent sbisim.
  Theorem aul_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ t, w |= φ AU AN done R ]> ->
      (forall x w, R x w -> <( {k x}, w |= φ AU ψ )>) ->
      <( {x <- t ;; k x}, w |= φ AU ψ )>.  
  Proof with eauto with ctl.
    intros.
    cinduction H. 
    - apply ax_done in Hp as (Hp & y & Heqt & HR).
      rewrite Heqt, bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ctll_bind_l.
      + destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'...
        specialize (HInd _ _ TR).
        now apply ctll_not_done in HInd.
      + intros t' w' TR'.
        apply ktrans_bind_inv in TR' as
            [(t_ & TR_ & Hd & ->) |
              (x & w_ & TR_ & Hr & TRk)].
        * apply HInd...
        * specialize (Hau _ _ TR_).
          change (cau  (entailsL _ ?φ) (entailsR ?ψ) ?t ?w)
            with <[ t, w |= φ AU ψ ]> in Hau.
          now apply aur_stuck, axr_stuck in Hau.
  Qed.
  
  Theorem aul_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ r w',
      <[ t, w |= φ AU AN done= r w' ]> ->
      <( {k r}, w' |= φ AU ψ )> ->
      <( {x <- t ;; k x}, w |= φ AU ψ )>.
  Proof with eauto with ctl.
    intros.
    apply aul_bind_r with (R:=fun x w => r = x /\ w' = w)...
    intros ? ? [<- <-]...
  Qed.
  
  Theorem aur_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ t, w |= φ AU AN done R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ AU ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ AU ψ ]>.  
  Proof with eauto with ctl.
    intros.
    cinduction H. 
    - apply ax_done in Hp as (Hp & y & Heqt & HR).
      rewrite Heqt, bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ctll_bind_l.
      + destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'...
        specialize (Hau _ _ TR) as Hau.        
        destruct Hau.
        -- cdestruct H.
           now apply can_step_not_done in Hs.
        -- destruct H as (Hp' & Hs & H).
           now apply can_step_not_done in Hs.
      + intros t' w' TR'.
        apply ktrans_bind_inv in TR' as
            [(t_ & TR_ & Hd & ->) |
              (x & w_ & TR_ & Hr & TRk)].
        * apply HInd...
        * specialize (Hau _ _ TR_).
          change (cau  (entailsL _ ?φ) (entailsR ?ψ) ?t ?w)
            with <[ t, w |= φ AU ψ ]> in Hau.
          now apply aur_stuck, axr_stuck in Hau.
  Qed.

  Theorem aur_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ r w',
      <[ t, w |= φ AU AN done= r w' ]> ->
      <[ {k r}, w' |= φ AU ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ AU ψ ]>.
  Proof with eauto with ctl.
    intros.
    apply aur_bind_r with (R:=fun x w => r = x /\ w' = w)...
    intros ? ? [<- <-]...
  Qed.
  
  (* EU *)
  Theorem eul_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ t, w |= φ EU EN done R ]> ->
      (forall r w', R r w' -> <( {k r}, w' |= φ EU ψ )>) ->
      <( {x <- t ;; k x}, w |= φ EU ψ )>.
  Proof with eauto with ctl.
    intros.
    cinduction H; intros.
    - apply ex_done in Hp as (Hw & ? & Heqt & Hp). 
      rewrite Heqt in Hw |- *.
      rewrite bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ctll_bind_l.
      + exists (x <- t0;; k x), w0; split...
        assert(Hd: not_done w0) by now apply ctll_not_done in HInd.
        apply ktrans_bind_r...
  Qed.

  Theorem eul_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ r w',
      <[ t, w |= φ EU EN done= r w' ]> ->
      <( {k r}, w' |= φ EU ψ )> ->
      <( {x <- t ;; k x}, w |= φ EU ψ )>.
  Proof with eauto with ctl.
    intros.
    apply eul_bind_r with (R:=fun x w => r = x /\ w' = w)...
    intros ? ? [<- <-]...
  Qed.
  
  Theorem eur_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ t, w |= φ EU EN done R ]> ->
      (forall r w', R r w' -> <[ {k r}, w' |= φ EU ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ EU ψ ]>.
  Proof with eauto with ctl.
    intros.
    cinduction H; intros.
    - apply ex_done in Hp as (Hw & ? & Heqt & Hp).
      rewrite Heqt in Hw |- *.
      rewrite bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ctll_bind_l.
      + exists (x <- t0;; k x), w0; split...
        destruct Heu.
        * cdestruct H.
          cdestruct Hp0.
          apply ktrans_bind_r...
        * destruct H.
          apply ctll_not_done in H.
          apply ktrans_bind_r...
  Qed.

  Theorem eur_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ r w',
      <[ t, w |= φ EU EN done= r w' ]> ->
      <[ {k r}, w' |= φ EU ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ EU ψ ]>.
  Proof with eauto with ctl.
    intros.
    apply eur_bind_r with (R:=fun x w => r = x /\ w' = w)...
    intros ? ? [<- <-]...
  Qed.
  
  (*| Bind lemma for [AG] |*)
  Notation MP X := (rel (ctree E X) (World E)).
  Program Definition ag_bind_clos{X Y} φ Post : mon (MP Y) :=
    {| body R t w :=
        bind_ctx1
          (fun (t: ctree E X) => <[ t, w |= φ AU (AN done Post) ]>)
          (fun (k: X -> ctree E Y) =>
             forall (x: X) (w: World E), Post x w -> R (k x) w)
          t
    |}.
  Next Obligation.
    revert H0.
    apply leq_bind_ctx1; intros.
    apply in_bind_ctx1; eauto.
  Qed.

  Lemma ag_bind_ag{X Y} (φ: ctll E) (Post: rel X (World E)):
      ag_bind_clos (Y:=Y) φ Post <= cagt (entailsL Y φ).
  Proof with auto with ctl.  
    apply Coinduction.
    intros R t w; cbn.
    apply (leq_bind_ctx1 _ _
             (fun t => cax (entailsL Y φ)
                      (cagT (entailsL Y φ)
                         (ag_bind_clos φ Post) R) t w)).
    clear t.
    intros t Hau k Hk.    
    cinduction Hau.
    - (* AN done R *)
      apply ax_done in Hp as (Hp & x & Heq & HPost).
      specialize (Hk _ _ HPost); remember (k x) as K;
        destruct Hk; subst; split2.      
      + rewrite Heq, bind_ret_l; auto. 
      + rewrite Heq, bind_ret_l.
        now destruct H0.
      + intros t' w' TR.
        apply (id_T (cagF (entailsL Y φ))); cbn.
        destruct H0.
        apply H1.
        eapply ktrans_sbisim_ret with (t:=t); auto.
    - (* φ AX (φ AU AN done R) *)
      split2.
      + now apply ctll_bind_l.
      + destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'; auto.
        specialize (Hau0 _ _ TR) as Hinv; destruct Hinv as [t' w' Hinv | t' w' Hinv].
        * cdestruct Hinv; cdestruct Hp0...
        * destruct Hinv as (? & Hs & ?).
          now apply can_step_not_done in Hs.
      + intros k_ w_ TRk.
        apply ktrans_bind_inv in TRk as
            [(t0' & TR0 & Hd_ & Heq) | (x & w0 & TRt0 & Hd & TRk)].
        * (* [t0] steps and is not [Ret] *)
          apply (fT_T (mequ_clos_cag (KS:=KripkeSetoidEqu))).
          cbn; eapply mequ_clos_ctor with (t1:=x <- t0';; k x) (w1:=w_); auto.
          clear Heq k_.            
          eapply (fTf_Tf (cagF (entailsL Y φ))).
          apply in_bind_ctx1.
          -- rewrite unfold_entailsR... 
          -- intros.
             apply (b_T (cagF (entailsL Y φ))); cbn... 
        * (* [t0] steps and is [Ret], contradiction *)
          specialize (HInd _ _ TRt0).
          destruct HInd as (Hp' & ? & ?).
          inv Hd.
          -- apply ktrans_to_done in TRt0 as (? & ->).
             apply ctll_not_done in Hp'; inv Hp'.
          -- apply ktrans_to_finish in TRt0 as (? & ->).
             apply ctll_not_done in Hp'; inv Hp'.
  Qed.

  (* [t] satisfies [φ] until it terminates with post-condition [R],
     then forall x w, R x w -> k x, w satisfies [φ] forever. *)
  Lemma ag_bind_r{X Y}: forall (t: ctree E X)
                          w (k: X -> ctree E Y) φ R,
      <[ t, w |= φ AU AN done R ]> ->
      (forall (x: X) (w: World E), R x w -> <( {k x}, w |= AG φ )>) ->
      <( {x <- t ;; k x} , w |= AG φ )>.
  Proof.
    intros.
    rewrite unfold_entailsL.
    apply (ft_t (ag_bind_ag φ R)).
    cbn.
    apply in_bind_ctx1; auto.
  Qed.

  (*| Bind lemma for [EG] |*)
  Program Definition eg_bind_clos{X Y} φ Post: mon (MP Y) :=
    {| body R t w :=
        bind_ctx1
          (fun (t: ctree E X) => <[ t, w |= φ EU (EN done Post) ]>)
          (fun (k: X -> ctree E Y) => forall r wr, Post r wr -> R (k r) wr)
          t
    |}.
  Next Obligation.
    revert H0.
    apply leq_bind_ctx1; intros.
    apply in_bind_ctx1; auto.
  Qed.

  Lemma eg_bind_eg{X Y} (φ: ctll E) R:
      eg_bind_clos (X:=X) (Y:=Y) φ R <= cegt (entailsL Y φ).
  Proof with auto with ctl.  
    apply Coinduction.
    intros p t w; cbn.
    apply (leq_bind_ctx1 _ _
             (fun t => cex (entailsL Y φ)
                      (cegT (entailsL Y φ)
                         (eg_bind_clos φ R) p) t w)).
    clear t.
    intros t Heu k Hk.
    cinduction Heu; intros.
    - (* EN done R *)
      apply ex_done in Hp as (Hd & y & Heqt & HPosty). 
      cdestruct Hd; clear H.
      rewrite Heqt, bind_ret_l.
      destruct (Hk _ _ HPosty) as (Hφ & k' & w' & TR & HR).
      split...
      exists k', w'; split...
      now apply (id_T (cegF (entailsL Y φ))). 
    - (* EX *)
      destruct HInd as (Hφ' & t_ & w_ & TR_ & Hg).
      split.
      + now apply ctll_bind_l.
      + apply ktrans_bind_inv in TR_ as
            [(t0' & TR1 & Hd_ & Heq) | (x' & w1 & TRt0 & Hd & TRk)].
        * exists (x <- t0 ;; k x), w0.
          split...
          eapply ktrans_bind_r...
          apply (bT_T (cegF (entailsL Y φ))).
          split...
          exists t_, w_; split...
          rewrite Heq.
          apply ktrans_bind_r...
        * exists (x <- t0;; k x), w0; split.
          -- apply ktrans_bind_r...
          -- inv Hd.
             ++ apply ktrans_to_done in TRt0 as (Heqt & ->).
                rewrite Heqt, bind_ret_l.
                apply (bT_T (cegF (entailsL Y φ))).
                rewrite Heqt, bind_ret_l in Hφ'.
                split...
                exists t_, w_; split...
             ++ apply ktrans_to_finish in TRt0 as (Heqt & ->).
                rewrite Heqt, bind_ret_l.
                apply (bT_T (cegF (entailsL Y φ))).
                rewrite Heqt, bind_ret_l in Hφ'.
                split...
                exists t_, w_; split...
  Qed.

  Lemma eg_bind_r{X Y}: forall (t: ctree E X) w (k: X -> ctree E Y) R φ,
      <[ t, w |= φ EU EN done R ]> ->
      (forall r w', R r w' -> <( {k r}, w' |= EG φ )>) ->
      <( {x <- t ;; k x} , w |= EG φ )>.
  Proof.
    intros.
    rewrite unfold_entailsL.
    apply (ft_t (eg_bind_eg φ R)); cbn.    
    apply in_bind_ctx1; eauto.
  Qed.
  
  Lemma eg_bind_r_eq{X Y}: forall (t: ctree E X) r
                          w wr (k: X -> ctree E Y) φ,
      <[ t, w |= φ EU EN done= r wr ]> ->
      <( {k r}, wr |= EG φ )> ->
      <( {x <- t ;; k x} , w |= EG φ )>.
  Proof.
    intros.
    apply eg_bind_r with (R:=fun r_ w_ => r = r_ /\ wr = w_); auto.
    now intros * (-> & ->).
  Qed.
  
End BindLemmas.
