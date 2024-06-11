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
  Logic.AX
  Logic.Kripke
  Logic.Setoid.

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
        destruct H0, H1; clear H1.
        cright; csplit; [|csplit]...
        * (* can_step *)          
          destruct H0 as (t' & w' & TR').
          eapply can_step_bind_l with t' w'; auto.
          specialize (H2 _ _ TR').
          change (cau (entailsL Y φ1) (entailsL Y φ2) ?t ?w) with <( t, w |= φ1 AU φ2 )> in H2.
          eapply ctll_not_done, H2.
        * (* AX AF *)
          intros t_ w' TR_.
          apply ktrans_bind_inv in TR_ as
              [(t' & TR' & Hd & ->) |
                (x & ? & TR' & Hr & TRk)].
          -- specialize (H2 _ _ TR').
             apply H3...
          -- specialize (H2 _ _ TR').
             inv H2; inv Hr; apply ctll_not_done in H1; inv H1.
    - (* EU *)      
      cinduction H; intros; subst.
      + (* MatchE *) cleft...
      + (* StepE *)
        destruct H0 as (t' & w' & TR' & H0).
        destruct H1 as (t_ & w_ & TR_ & H1).
        cright; csplit; [|csplit]...
        exists (x <- t_ ;; k x), w_; split.
        * apply ktrans_bind_l...
          eapply ctll_not_done, H1.
        * apply H1.
    - (* AX *)
      cdestruct H; csplit.
      + destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'...
        eapply ctll_not_done, (H _ _ TR).
      + intros t' w' TR.
        apply ktrans_bind_inv in TR as
            [(t_ & TR' & Hd & ->) |
              (x & w_ & TR' & Hr & TRk)].
        * apply IHφ, H...
        * specialize (H _ _ TR').
          inv Hr; apply ctll_not_done in H; inv H.
    - (* EX *)
      cdestruct H; csplit.
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
        * cdestruct H; cdestruct H.
          destruct Hs as (t' & w' & TR).
          apply can_step_bind_l with t' w'...
          eapply ctll_not_done, (H _ _ TR).
        * intros t' w' TR.
          cdestruct H; cdestruct H.
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
      + cdestruct H; cdestruct H.
        * exists (x <- t0;; k x), w0.
          split...
          apply ktrans_bind_l...
          eapply ctll_not_done, H.
    - (* AND *)
      cdestruct H; csplit...
    - (* OR *)
      cdestruct H; [cleft | cright]...
  Qed.

  Theorem ctll_bind_au{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) (φ ψ: ctll E) w R,
      <[ t, w |= φ AU AX done R ]> ->
      (forall (y: Y) w, R y w -> <( {k y}, w |= φ AU ψ )>) ->
      <( {x <- t ;; k x}, w |= φ AU ψ )>.
  Proof.
    intros.
    generalize dependent t.
    generalize dependent k.
    revert R w ψ.
    induction φ; intros.
    - (* NOW *)
      cinduction H.
      + apply ax_done in H as (? & ? & ? & HR).
      rewrite H1, bind_ret_l.
      now apply H0.
    - destruct H1, H2; clear H2.
      next; right; split; [|split].
      + apply H.
      + destruct H1 as (t_ & w_ & TR).
        apply can_step_bind_l with t_ w_; auto.
        destruct (H3 _ _ TR).
        * now apply ax_done in H1 as (? & ?).
        * destruct H2.
          now apply can_step_not_done with t0.
      + intros t_ w_ TR.
        apply ktrans_bind_inv in TR as
            [(t' & TR' & Hd & ->) | (x & w' & TR' & Hr & TRk)].
        * now apply H4.
        * specialize (H3 _ _ TR').
          assert(H3': <( {Ctree.stuck: ctree E Y}, w' |= base ψ AU AX done R)>) by
            now rewrite unfold_entailsF.
          apply au_stuck in H3'.
          destruct H3'.
          now apply can_step_stuck in H2.
End BindLemmas.
