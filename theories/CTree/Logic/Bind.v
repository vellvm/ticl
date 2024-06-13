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
  Logic.Ctl.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

Section BindLemmas.
  Context {E: Type} {HE: Encode E}.

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
        exists (x <- t_ ;; k x), w_; split.
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

  Typeclasses Transparent sbisim.
  Theorem aul_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ t, w |= φ AU AN done R ]> ->
      (forall x w, R x w -> <( {k x}, w |= φ AU ψ )>) ->
      <( {x <- t ;; k x}, w |= φ AU ψ )>.  
  Proof with eauto with ctl.
    intros.
    cinduction H. 
    - apply an_done in Hp as (Hd & y & Heqt & HR).
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

  Theorem aur_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ t, w |= φ AU AN done R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ AU ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ AU ψ ]>.  
  Proof with eauto with ctl.
    intros.
    cinduction H. 
    - apply an_done in Hp as (Hd & y & Heqt & HR).
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
  

End BindLemmas.
