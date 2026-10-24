From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.EG
  CTree.Events.Writer
  Logic.Core.

Generalizable All Variables.

Import CTreeNotations TiclNotations CoindNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** * TICL sequential composition ([bind]) lemmas for ctrees. *)
(** These are the most useful lemmas for modular, temporal verification.

    Two regimes of sequencing lemmas live here:
    - regime A ([ret]-premised): the prefix [t] terminates in a *single* value
      ([φ AU ret R], i.e. [t ~ Ret x] at the leaves); the continuation gets the
      full [φ AU ψ] obligation.
    - regime B ([done]-premised, [_done] suffix): the prefix may terminate in
      several values at once through hidden branching ([φ AU done R]); the
      continuation obligation is stated one step later ([φ AN (φ AU ψ)]) so the
      union state of [t >>= k] is always a [StepA] state. *)
Section BindLemmas.
  Context {E B: Type -> Type}.

  (** Prove by induction on formulas [φ]; if [t] satisfies prefix formula [φ] then so do all its extensions ([x <- t ;; k x]) *)
  Theorem ticll_bind_l{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) φ w,
      <( t, w |= φ )> ->
      <( {x <- t ;; k x}, w |= φ )>.
  Proof with auto with ticl.
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
          change (auc (entailsL Y φ1) (entailsL Y φ2) ?t ?w)
            with <( t, w |= φ1 AU φ2 )> in Hau.
          now eapply ticll_not_done in Hau. 
        * (* AN AF *)
          intros t_ w' TR_.
          apply ktrans_bind_inv in TR_ as
              [(t' & TR' & Hd & ->) |
                (x & ? & TR' & Hr & TRk)].
          -- specialize (Hau _ _ TR').
             apply HInd...
          -- specialize (HInd _ _ TR').
             apply ticll_not_done in HInd; inv Hr; inv HInd.
    - (* EU *)      
      cinduction H; intros; subst.
      + (* MatchE *) cleft...
      + (* StepE *)
        cright; csplit...
        exists (x <- t0 ;; k x), w0; split.
        * apply ktrans_bind_l...
          now apply ticll_not_done in HInd. 
        * apply HInd.
    - (* AN *)
      cdestruct H; csplit...
      + (* can_step *) destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'...
        eapply ticll_not_done, (H _ _ TR).
      + (* forall *) intros t' w' TR.
        apply ktrans_bind_inv in TR as
            [(t_ & TR' & Hd & ->) |
              (x & w_ & TR' & Hr & TRk)].
        * apply IHφ2, H...
        * specialize (H _ _ TR').
          inv Hr; apply ticll_not_done in H; inv H.
    - (* EN *)
      cdestruct H; csplit...
      exists (x <- t0;; k x), w0; split...
      apply ktrans_bind_l...
      now apply ticll_not_done in H.
    - (* AG *)
      generalize dependent t.
      revert w.
      coinduction_g R CIH; intros w t H; split2.
      + apply IHφ.
        now cdestruct H.
      + cdestruct H.
        destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'...
        eapply ticll_not_done, (H _ _ TR).
      + intros t' w' TR.
        cdestruct H.
        apply ktrans_bind_inv in TR as
            [(t_ & TR' & Hd & ->) |
              (x & w_ & TR' & Hr & TRk)].
        * apply CIH...
        * specialize (H _ _ TR').
          inv Hr; apply ticll_not_done in H; inv H.
    - (* EG *)
      generalize dependent t.
      revert w.
      coinduction_g R CIH; intros w t H; split.
      + apply IHφ.
        now cdestruct H.
      + cdestruct H.
        exists (x <- t0;; k x), w0.
        split...
        apply ktrans_bind_l...
        eapply ticll_not_done, H.
    - (* AND *)
      cdestruct H; csplit...
    - (* OR *)
      cdestruct H; [cleft | cright]...
  Qed.

  (** Bind lemmas for prefix [AN]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ AN ψ] with prefix formula [ψ]. *)
  Theorem anl_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ AN done R ]> ->
      (forall x w, R x w -> <( {k x}, w |= φ AN ψ )>) ->
      <( {x <- t ;; k x}, w |= φ AN ψ )>.  
  Proof with eauto with ticl.
    intros.
    cdestruct H; csplit...
    - now apply ticll_bind_l.
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
        * eapply ktrans_to_done_inv in TR_ as (? & ->).
          specialize (H0 _ _ H) as Hax.
          cdestruct Hax...
        * eapply ktrans_to_finish_inv in TR_ as (? & ->).
          specialize (H0 _ _ H) as Hax.
          cdestruct Hax...
  Qed.
 
  (** Bind lemmas for suffix [AN]; requires specifying a postcondition [R] for the return values of [t].
  If [t] takes a step, then the continuation [k x] must satisfy postcondition [ψ] without the need to step *)
  Theorem anr_bind_l{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ AN ret R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ AN ψ ]>.  
  Proof with eauto with ticl.
    intros.
    cdestruct H; csplit...
    - now apply ticll_bind_l.
    - (* can_step *)
      destruct Hs as (t_ & w_ & TR_).
      eapply can_step_bind_l...
      specialize (H _ _ TR_).
      cdestruct H...
    - intros y wr TR.
      apply ktrans_bind_inv in TR as
          [(t_ & TR_ & Hd & ->) |
            (x & w_ & TR_ & Hr & TRk)].
      + specialize (H _ _ TR_).
        apply ret_sbisim in H as (x & HR & Heqt).
        rewrite Heqt, bind_ret_l...
      + specialize (H _ _ TR_) as Hax.
        cdestruct Hax; inv Hr; inv Hd.
  Qed.
  
  (** Bind lemma for suffix [AN]; requires specifying a postcondition [R] for the return values of [t].
  If [t] immediately terminates with post-condition [R], then the continuation [k x] must take a step to satisfy postcondition [ψ]. *)
  Theorem anr_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ AN done R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ AN ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ AN ψ ]>.  
  Proof with eauto with ticl.
    intros.
    cdestruct H; csplit...
    - now apply ticll_bind_l.
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
        * eapply ktrans_to_done_inv in TR_ as (? & ->).
          specialize (H0 _ _ H) as Hax.
          cdestruct Hax...
        * eapply ktrans_to_finish_inv in TR_ as (? & ->).
          specialize (H0 _ _ H) as Hax.
          cdestruct Hax...
  Qed.

  (** Helper version of [anr_bind_r] for deterministic [t], it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem anr_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ r w',
      <[ t, w |= φ AN done= r w' ]> ->
      <[ {k r}, w' |= φ AN ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ AN ψ ]>.  
  Proof with eauto with ticl.
    intros.
    eapply anr_bind_r...
    now intros * [-> ->].
  Qed.
  
  (** Bind lemmas for prefix [EN]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ EN ψ] with prefix formula [ψ]. *)
  Theorem enl_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ EN done R ]> ->
      (forall r w', R r w' -> <( {k r}, w' |= φ EN ψ )>) ->
      <( {x <- t ;; k x}, w |= φ EN ψ )>.
  Proof with eauto with ticl.
    intros.
    apply enr_done in H as (Hφ & r & w' & Hd & HR & TR).
    specialize (H0 _ _ HR).
    cdestruct H0; csplit.
    - now apply ticll_bind_l.
    - exists t0, w0; split...
      eapply ktrans_bind_r...
      inv Hd; now constructor.
  Qed.

  (** Helper version of [enl_bind_r] for deterministic [t], it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem enl_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' φ ψ r,
      <[ t, w |= φ EN done= r w' ]> ->
      <( {k r}, w' |= φ EN ψ )> ->
      <( {x <- t ;; k x}, w |= φ EN ψ )>.
  Proof with eauto with ticl.
    intros.
    apply enl_bind_r with (R:=fun x w => r = x /\ w' = w)...
    intros r_ w_ (-> & ->)...
  Qed.
  
  (** Bind lemmas for suffix [EN]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ EN ψ] with post-condition [ψ]. *)
  Theorem enr_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ EN done R ]> ->
      (forall r w', R r w' -> <[ {k r}, w' |= φ EN ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ EN ψ ]>.
  Proof with eauto with ticl.
    intros.
    apply enr_done in H as (Hφ & r & w' & Hd & HR & TR).
    specialize (H0 _ _ HR).
    cdestruct H0; csplit.
    - now apply ticll_bind_l.
    - exists t0, w0; split...
      eapply ktrans_bind_r...
      inv Hd; now constructor.
  Qed.
  
  (** Helper version of [enr_bind_r] for deterministic [t], it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem enr_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' φ ψ r,
      <[ t, w |= φ EN done= r w' ]> ->
      <[ {k r}, w' |= φ EN ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ EN ψ ]>.
  Proof with eauto with ticl.
    intros.
    apply enr_bind_r with (R:=fun x w => r = x /\ w' = w)...
    intros r_ w_ (-> & ->)...
  Qed.
  
  (** Bind lemmas for prefix until [AU]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ AU ψ] with prefix formula [ψ]. *)
  Theorem aul_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ AU ret R ]> ->
      (forall x w, R x w -> <( {k x}, w |= φ AU ψ )>) ->
      <( {x <- t ;; k x}, w |= φ AU ψ )>.  
  Proof with eauto with ticl.
    intros.
    cinduction H. 
    - apply ret_sbisim in Hp as (y & HR & Heqt).
      rewrite Heqt, bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ticll_bind_l.
      + destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'...
        specialize (HInd _ _ TR).
        now apply ticll_not_done in HInd.
      + intros t' w' TR'.
        apply ktrans_bind_inv in TR' as
            [(t_ & TR_ & Hd & ->) |
              (x & w_ & TR_ & Hr & TRk)].
        * apply HInd...
        * specialize (Hau _ _ TR_).
          change (auc  (entailsL _ ?φ) (entailsR ?ψ) ?t ?w)
            with <[ t, w |= φ AU ψ ]> in Hau.
          apply aur_stuck in Hau.
          cdestruct Hau; inv Hr; inv Hd.
  Qed.
  
  (** [AX done= r w'] is a deterministic return: every transition returns [r]
      from world [w'] (which is the current world). *)
  Lemma axr_done_eq_ret{X}: forall (t: ctree E B X) w r w',
      <[ t, w |= AX done= r w' ]> ->
      <[ t, w |= ret= r w' ]>.
  Proof with eauto with ticl.
    intros * H.
    cdestruct H.
    assert (Hw: w' = w).
    { destruct Hs as (t' & w_ & TR); specialize (H _ _ TR); cdestruct H.
      - destruct H as (_ & ->); now apply ktrans_to_done_inv in TR as (_ & ->).
      - destruct H as (_ & ->); now apply ktrans_to_finish_inv in TR as (_ & ->). }
    subst.
    apply ret_unfold; exists r; split...
    csplit...
  Qed.

  Lemma aur_axr_done_eq_ret{X}: forall (t: ctree E B X) w φ r w',
      <[ t, w |= φ AU AX done= r w' ]> ->
      <[ t, w |= φ AU ret= r w' ]>.
  Proof with eauto with ticl.
    intros * H.
    cinduction H.
    - cleft; now apply axr_done_eq_ret.
    - cright; csplit...
  Qed.

  (** Helper version of [aul_bind_r] for deterministic [t], it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem aul_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ r w',
      <[ t, w |= φ AU AX done= r w' ]> ->
      <( {k r}, w' |= φ AU ψ )> ->
      <( {x <- t ;; k x}, w |= φ AU ψ )>.
  Proof with eauto with ticl.
    intros.
    apply aul_bind_r with (R:=fun x w => r = x /\ w' = w)...
    - now apply aur_axr_done_eq_ret.
    - intros ? ? [<- <-]...
  Qed.

  (** Bind lemmas for suffix until [AU]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ AU ψ] with post-condition [ψ]. *)
  Theorem aur_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ AU ret R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ AU ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ AU ψ ]>.  
  Proof with eauto with ticl.
    intros.
    cinduction H. 
    - apply ret_sbisim in Hp as (y & HR & Heqt).
      rewrite Heqt, bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ticll_bind_l.
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
          change (auc  (entailsL _ ?φ) (entailsR ?ψ) ?t ?w)
            with <[ t, w |= φ AU ψ ]> in Hau.
          apply aur_stuck in Hau.
          cdestruct Hau; inv Hr; inv Hd.
  Qed.

  (** A [φ AU ret R] obligation is only satisfiable in a not-done world. *)
  Lemma aur_ret_not_done{X}: forall φ R (t: ctree E B X) (w: World E),
      <[ t, w |= φ AU ret R ]> ->
      not_done w.
  Proof.
    intros * H.
    cinduction H.
    - cdestruct Hp; auto.
    - now apply can_step_not_done in Hs.
  Qed.

  (** Bind lemma for a first step [AX] followed by suffix until [AU]. *)
  Theorem axr_aur_bind_r {X Y} :
    forall (t : ctree E B Y) (k : Y -> ctree E B X) w phi psi R,
    <[ t, w |= AX (phi AU ret R) ]> ->
    (forall x w, R x w -> <[ {k x}, w |= phi AU psi ]>) ->
    <[ {x <- t ;; k x}, w |= AX (phi AU psi) ]>.
  Proof with eauto with ticl.
    intros t k w phi psi R Ht Hk.
    cdestruct Ht; csplit...
    - destruct Hs as (t' & w' & Hstep).
      eapply can_step_bind_l; [exact Hstep |].
      eapply aur_ret_not_done, Ht, Hstep.
    - intros t' w' Hstep.
      apply ktrans_bind_inv in Hstep as
        [(u & Htu & Hd & ->) | (x & wr & Hret & Hr & Hstep)].
      + eapply aur_bind_r; [eapply Ht; exact Htu | exact Hk].
      + specialize (Ht _ _ Hret).
        apply aur_stuck in Ht.
        cdestruct Ht; inv Hr; inv Hd.
  Qed.

  (** Helper version of [aur_bind_r] for deterministic [t], it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem aur_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ r w',
      <[ t, w |= φ AU AX done= r w' ]> ->
      <[ {k r}, w' |= φ AU ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ AU ψ ]>.
  Proof with eauto with ticl.
    intros.
    apply aur_bind_r with (R:=fun x w => r = x /\ w' = w)...
    - now apply aur_axr_done_eq_ret.
    - intros ? ? [<- <-]...
  Qed.
  
  (** Bind lemmas for prefix [EU]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ EU ψ] with prefix formula [ψ]. *)
  Theorem eul_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ EU ret R ]> ->
      (forall r w', R r w' -> <( {k r}, w' |= φ EU ψ )>) ->
      <( {x <- t ;; k x}, w |= φ EU ψ )>.
  Proof with eauto with ticl.
    intros.
    cinduction H; intros.
    - apply ret_sbisim in Hp as (y & HR & Heqt).
      rewrite Heqt, bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ticll_bind_l.
      + exists (x <- t0;; k x), w0; split...
        assert(Hd: not_done w0) by now apply ticll_not_done in HInd.
        apply ktrans_bind_l...
  Qed.

  (** Helper version of [eul_bind_r] for deterministic [t] ([ret= r w']), it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. Note: with hidden branching, [EX done= r w']
  is not enough (another branch may return a different value), hence the [ret=] premise. *)
  Theorem eul_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ r w',
      <[ t, w |= φ EU ret= r w' ]> ->
      <( {k r}, w' |= φ EU ψ )> ->
      <( {x <- t ;; k x}, w |= φ EU ψ )>.
  Proof with eauto with ticl.
    intros.
    apply eul_bind_r with (R:=fun x w => r = x /\ w' = w)...
    intros ? ? [<- <-]...
  Qed.
  
  (** Bind lemmas for suffix [EU]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ EU ψ] with post-condition [ψ]. *)
  Theorem eur_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ EU ret R ]> ->
      (forall r w', R r w' -> <[ {k r}, w' |= φ EU ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ EU ψ ]>.
  Proof with eauto with ticl.
    intros.
    cinduction H; intros.
    - apply ret_sbisim in Hp as (y & HR & Heqt).
      rewrite Heqt, bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ticll_bind_l.
      + exists (x <- t0;; k x), w0; split...
        destruct Heu.
        * cdestruct H.
          apply ktrans_bind_l...
        * destruct H.
          apply ticll_not_done in H.
          apply ktrans_bind_l...
  Qed.

  (** Helper version of [eur_bind_r] for deterministic [t] ([ret= r w']), it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem eur_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ r w',
      <[ t, w |= φ EU ret= r w' ]> ->
      <[ {k r}, w' |= φ EU ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ EU ψ ]>.
  Proof with eauto with ticl.
    intros.
    apply eur_bind_r with (R:=fun x w => r = x /\ w' = w)...
    intros ? ? [<- <-]...
  Qed.

  (** ** Up-to bind principles for [AG] and [EG] (tower form) *)
  (** Every element [`R] of the final chain of [agcF (entailsL Y φ)] is closed under
      sequencing a prefix [t] that satisfies [φ] until it returns a single value
      with post-condition [Post], provided the continuation lands in [`R]. The
      [gfp] itself is the last chain element ([chain_gfp]). *)
  Lemma ag_bind_chain {X Y} (φ: ticll E) (Post: rel X (World E))
    {R: Chain (agcF (entailsL Y φ))} :
    forall (t: ctree E B X) (k: X -> ctree E B Y) w,
      <[ t, w |= φ AU ret Post ]> ->
      (forall x w, Post x w -> `R (k x) w) ->
      `R (x <- t ;; k x) w.
  Proof with auto with ticl.
    apply tower.
    - (* inf-closed *)
      intros ? INC t k w Hau Hk ? ?.
      apply INC; auto.
      intros x w' HP.
      apply leq_infx in H.
      apply H; now apply Hk.
    - (* step *)
      intros R' IH t k w Hau Hk.
      cinduction Hau.
      + (* MatchA: ret Post *)
        apply ret_sbisim in Hp as (x & HPost & Heq).
        specialize (Hk _ _ HPost).
        rewrite Heq, bind_ret_l.
        apply Hk.
      + (* StepA *)
        split2.
        * now apply ticll_bind_l.
        * destruct Hs as (t' & w' & TR).
          apply can_step_bind_l with t' w'...
          specialize (Hau0 _ _ TR) as Hinv.
          change (auc (entailsL ?X ?φ) (entailsR ?ψ) ?t ?w)
            with (@entailsR _ _ _ _ X (CuR Q_A φ ψ) t w) in Hinv.
          now apply aur_ret_not_done in Hinv.
        * intros k_ w_ TRk.
          apply ktrans_bind_inv in TRk as
              [(t0' & TR0 & Hd_ & Heq) | (x & w0 & TRt0 & Hd & TRk)].
          -- rewrite Heq.
             apply IH; [rewrite unfold_entailsR; now apply Hau0 |].
             intros; apply (b_chain R'); now apply Hk.
          -- (* [t0] returned: contradiction with [ret] in a done world *)
             specialize (Hau0 _ _ TRt0) as Hinv.
             change (auc (entailsL ?X ?φ) (entailsR ?ψ) ?t ?w)
               with (@entailsR _ _ _ _ X (CuR Q_A φ ψ) t w) in Hinv.
             apply aur_ret_not_done in Hinv; inv Hd; inv Hinv.
  Qed.

  (** ** Structural rule for the up-to bind principle for [AG]. *)
  (** [t] satisfies [φ] until it terminates with post-condition [R],
     then forall x w, R x w -> k x, w satisfies [φ] forever. *)
  Lemma ag_bind_r{X Y}: forall (t: ctree E B X)
                          w (k: X -> ctree E B Y) φ R,
      <[ t, w |= φ AU ret R ]> ->
      (forall (x: X) (w: World E), R x w -> <( {k x}, w |= AG φ )>) ->
      <( {x <- t ;; k x} , w |= AG φ )>.
  Proof.
    intros.
    rewrite unfold_entailsL.
    apply (ag_bind_chain φ R (R:=chain_gfp _)); auto.
  Qed.

  Lemma eg_bind_chain {X Y} (φ: ticll E) (Post: rel X (World E))
    {R: Chain (egcF (entailsL Y φ))} :
    forall (t: ctree E B X) (k: X -> ctree E B Y) w,
      <[ t, w |= φ EU ret Post ]> ->
      (forall x w, Post x w -> `R (k x) w) ->
      `R (x <- t ;; k x) w.
  Proof with auto with ticl.
    apply tower.
    - (* inf-closed *)
      intros ? INC t k w Heu Hk ? ?.
      apply INC; auto.
      intros x w' HP.
      apply leq_infx in H.
      apply H; now apply Hk.
    - (* step *)
      intros R' IH t k w Heu Hk.
      cinduction Heu.
      + (* MatchE: ret Post *)
        apply ret_sbisim in Hp as (x & HPost & Heq).
        specialize (Hk _ _ HPost).
        rewrite Heq, bind_ret_l.
        apply Hk.
      + (* StepE *)
        split.
        * now apply ticll_bind_l.
        * exists (x <- t0 ;; k x), w0; split.
          -- apply ktrans_bind_l...
             destruct Heu as [? ? Hret | ? ? (Hφ & _)].
             ++ cdestruct Hret...
             ++ now apply ticll_not_done in Hφ.
          -- apply IH; [rewrite unfold_entailsR; apply Heu |].
             intros; apply (b_chain R'); now apply Hk.
  Qed.

  (** ** Structural rule for the up-to bind principle for [EG]. *)
  Lemma eg_bind_r{X Y}: forall (t: ctree E B X) w (k: X -> ctree E B Y) R φ,
      <[ t, w |= φ EU ret R ]> ->
      (forall r w', R r w' -> <( {k r}, w' |= EG φ )>) ->
      <( {x <- t ;; k x} , w |= EG φ )>.
  Proof.
    intros.
    rewrite unfold_entailsL.
    apply (eg_bind_chain φ R (R:=chain_gfp _)); auto.
  Qed.
  
  (** Helper version of [eg_bind_r] for deterministic [t] ([ret= r wr]). *)
  Lemma eg_bind_r_eq{X Y}: forall (t: ctree E B X) r
                          w wr (k: X -> ctree E B Y) φ,
      <[ t, w |= φ EU ret= r wr ]> ->
      <( {k r}, wr |= EG φ )> ->
      <( {x <- t ;; k x} , w |= EG φ )>.
  Proof.
    intros.
    apply eg_bind_r with (R:=fun r_ w_ => r = r_ /\ wr = w_); auto.
    now intros * (-> & ->).
  Qed.


  (** ** Regime B: sequencing through hidden value choice *)
  (** At a state whose transitions return several values at once ([brn 2 Ret]),
      [t >>= k] has the union of the successors of all the [k x]; [φ AU ψ] is
      not closed under such unions (one [k x] may be a leaf, another a step).
      Stating the continuation obligation one step later ([φ AN (φ AU ψ)])
      makes the union state always a [StepA] state. The termination premise is
      world-only ([done R]); [not_done w] is required because [φ AU done R] is
      trivially a leaf in a done world. *)

  (** A [ktrans] out of a not-done world either stays not-done or returns a
      value of the right type ([Done x] / [Finish e v x] with [x : X]). *)
  Local Lemma ktrans_succ_cases{X}: forall (t t': ctree E B X) w w',
      |t, w| ↦ |t', w'| ->
      not_done w'
      \/ (exists (x: X), w' = Done x /\ w = Pure /\ t' ≅ Stuck)
      \/ (exists Y (e: E Y) (v: Y) (x: X), w' = Finish e v x /\ w = Obs e v /\ t' ≅ Stuck).
  Proof.
    intros * TR; cbn in TR; ddestruction TR; auto with ticl.
    - right; left; exists x; split2; auto; now apply trans_val_inv in H.
    - right; right; exists Y, e, v, x; split2; auto; now apply trans_val_inv in H.
  Qed.

  (** In a not-done world, the [can_step] obligation of [t >>= k] given [φ AU done R] on [t]
      and stepping continuations. *)
  Local Lemma can_step_bind_done{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ R,
      can_step t w ->
      (forall t' w', |t, w| ↦ |t', w'| -> <[ t', w' |= φ AU done R ]>) ->
      (forall x w, R x w -> can_step (k x) w) ->
      can_step (x <- t ;; k x) w.
  Proof with eauto with ticl.
    intros * (t' & w' & TR) Hau Hk.
    specialize (Hau _ _ TR) as Hleaf.
    apply ktrans_succ_cases in TR as Hc;
      destruct Hc as [Hd' | [(x & -> & -> & Heq) | (Z & e & v & x & -> & -> & Heq)]].
    - eapply can_step_bind_l...
    - rewrite Heq in TR, Hleaf.
      apply aur_stuck in Hleaf; cdestruct Hleaf.
      destruct (Hk _ _ H) as (k' & w' & TRk).
      exists k', w'; eapply ktrans_bind_r; eauto; now constructor.
    - rewrite Heq in TR, Hleaf.
      apply aur_stuck in Hleaf; cdestruct Hleaf.
      destruct (Hk _ _ H) as (k' & w' & TRk).
      exists k', w'; eapply ktrans_bind_r; eauto; now constructor.
  Qed.

  (** The leaf of [φ AU done R] reached by a returning transition gives [R x w]. *)
  Local Lemma aur_done_leaf{X}: forall (t t': ctree E B X) w (x: X) w_ φ R,
      |t, w| ↦ |t', w_| ->
      done_eq x w_ ->
      <[ t', w_ |= φ AU done R ]> ->
      R x w.
  Proof.
    intros * TR Hd Hleaf.
    apply ktrans_succ_cases in TR as Hc;
      destruct Hc as [Hd' | [(x' & -> & -> & Heq) | (Z & e & v & x' & -> & -> & Heq)]].
    - inv Hd; inv Hd'.
    - rewrite Heq in Hleaf; apply aur_stuck in Hleaf; cdestruct Hleaf.
      inv Hd; match goal with [HH: existT _ _ _ = existT _ _ _ |- _] => now dependent destruction HH end.
    - rewrite Heq in Hleaf; apply aur_stuck in Hleaf; cdestruct Hleaf.
      inv Hd; match goal with [HH: existT _ _ _ = existT _ _ _ |- _] => now dependent destruction HH end.
  Qed.

  Theorem aur_bind_r_done{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      not_done w ->
      <[ t, w |= φ AU done R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ AN (φ AU ψ) ]>) ->
      <[ {x <- t ;; k x}, w |= φ AN (φ AU ψ) ]>.
  Proof with eauto with ticl.
    intros * Hd Hau Hk.
    cinduction Hau.
    - (* MatchA: done R in a not-done world, impossible *)
      cdestruct Hp; inv Hd.
    - (* StepA *)
      csplit.
      + now apply ticll_bind_l.
      + eapply can_step_bind_done; eauto.
        * intros t' w' TR; rewrite unfold_entailsR; now apply Hau0.
        * intros x w' HR; specialize (Hk _ _ HR) as Hkx; now cdestruct Hkx.
      + intros k_ w_ TRk.
        apply ktrans_bind_inv in TRk as
            [(t0' & TR0 & Hd_ & Heq) | (x & w0 & TRt0 & Hr & TRk)].
        * rewrite Heq.
          cright; apply HInd...
        * assert (HR: R x w).
          { eapply aur_done_leaf; eauto; rewrite unfold_entailsR; now apply Hau0. }
          specialize (Hk _ _ HR) as Hkx; cdestruct Hkx...
  Qed.

  Corollary aur_bind_r_done_au{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      not_done w ->
      <[ t, w |= φ AU done R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ AN (φ AU ψ) ]>) ->
      <[ {x <- t ;; k x}, w |= φ AU ψ ]>.
  Proof.
    intros; cright; eapply aur_bind_r_done; eauto.
  Qed.

  (** The leaf world of a [done R] post-condition is never done. *)
  Lemma aur_done_not_done{X}: forall (t: ctree E B X) w φ R,
      <[ t, w |= φ AU done R ]> ->
      <[ t, w |= φ AU done {fun x w => R x w /\ not_done w} ]>.
  Proof with auto with ticl.
    intros * H.
    cinduction H.
    - cleft; cdestruct Hp; csplit...
    - cright; csplit...
  Qed.

  Lemma eur_done_not_done{X}: forall (t: ctree E B X) w φ R,
      <[ t, w |= φ EU done R ]> ->
      <[ t, w |= φ EU done {fun x w => R x w /\ not_done w} ]>.
  Proof with auto with ticl.
    intros * H.
    cinduction H.
    - cleft; cdestruct Hp; csplit...
    - cright; csplit...
      exists t0, w0...
  Qed.

  (** In a not-done world, [φ AU done R'] is a [StepA] state, i.e. [φ AN (φ AU done R')]. *)
  Lemma aur_done_an{X}: forall (t: ctree E B X) w φ R',
      not_done w ->
      <[ t, w |= φ AU done R' ]> ->
      <[ t, w |= φ AN (φ AU done R') ]>.
  Proof.
    intros * Hd H.
    cdestruct H; auto.
    cdestruct H; inv Hd.
  Qed.

  Corollary aur_bind_r_done_post{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ R R',
      not_done w ->
      <[ t, w |= φ AU done R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ AU done R' ]>) ->
      <[ {x <- t ;; k x}, w |= φ AU done R' ]>.
  Proof.
    intros * Hd Hau Hk.
    apply aur_bind_r_done_au with (fun x w => R x w /\ not_done w); auto.
    - now apply aur_done_not_done.
    - intros x w' (HR & Hd').
      apply aur_done_an; auto.
  Qed.

  Theorem aul_bind_r_done{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ (ψ: ticll E) R,
      not_done w ->
      <[ t, w |= φ AU done R ]> ->
      (forall x w, R x w -> <( {k x}, w |= φ AN (φ AU ψ) )>) ->
      <( {x <- t ;; k x}, w |= φ AN (φ AU ψ) )>.
  Proof with eauto with ticl.
    intros * Hd Hau Hk.
    cinduction Hau.
    - cdestruct Hp; inv Hd.
    - csplit.
      + now apply ticll_bind_l.
      + eapply can_step_bind_done; eauto.
        * intros t' w' TR; rewrite unfold_entailsR; now apply Hau0.
        * intros x w' HR; specialize (Hk _ _ HR) as Hkx; now cdestruct Hkx.
      + intros k_ w_ TRk.
        apply ktrans_bind_inv in TRk as
            [(t0' & TR0 & Hd_ & Heq) | (x & w0 & TRt0 & Hr & TRk)].
        * rewrite Heq.
          cright; apply HInd...
        * assert (HR: R x w).
          { eapply aur_done_leaf; eauto; rewrite unfold_entailsR; now apply Hau0. }
          specialize (Hk _ _ HR) as Hkx; cdestruct Hkx...
  Qed.

  (** The witnessed successor of [φ EU done R] in a done world is a leaf giving [R x w]. *)
  Local Lemma eur_done_leaf{X}: forall (t t': ctree E B X) w (x: X) w_ φ R,
      |t, w| ↦ |t', w_| ->
      done_eq x w_ ->
      <[ t', w_ |= φ EU done R ]> ->
      R x w.
  Proof.
    intros * TR Hd Hleaf.
    apply ktrans_succ_cases in TR as Hc;
      destruct Hc as [Hd' | [(x' & -> & -> & Heq) | (Z & e & v & x' & -> & -> & Heq)]].
    - inv Hd; inv Hd'.
    - rewrite Heq in Hleaf; apply eur_stuck in Hleaf; cdestruct Hleaf.
      inv Hd; match goal with [HH: existT _ _ _ = existT _ _ _ |- _] => now dependent destruction HH end.
    - rewrite Heq in Hleaf; apply eur_stuck in Hleaf; cdestruct Hleaf.
      inv Hd; match goal with [HH: existT _ _ _ = existT _ _ _ |- _] => now dependent destruction HH end.
  Qed.

  Theorem eur_bind_r_done{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      not_done w ->
      <[ t, w |= φ EU done R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ EN (φ EU ψ) ]>) ->
      <[ {x <- t ;; k x}, w |= φ EN (φ EU ψ) ]>.
  Proof with eauto with ticl.
    intros * Hd Heu Hk.
    cinduction Heu.
    - cdestruct Hp; inv Hd.
    - csplit.
      + now apply ticll_bind_l.
      + apply ktrans_succ_cases in TR as Hc;
          destruct Hc as [Hd' | [(x & -> & Hw & Heq) | (Z & e & v & x & -> & Hw & Heq)]].
        * exists (x <- t0 ;; k x), w0; split.
          -- apply ktrans_bind_l...
          -- cright; apply HInd...
        * assert (HR: R x w).
          { eapply (eur_done_leaf _ _ _ x (Done x)); eauto; [now constructor | rewrite unfold_entailsR; apply Heu]. }
          specialize (Hk _ _ HR) as Hkx; cdestruct Hkx.
          exists t1, w0; split...
          rewrite Heq in TR.
          eapply (ktrans_bind_r _ _ _ x _ (Done x)); eauto; now constructor.
        * assert (HR: R x w).
          { eapply (eur_done_leaf _ _ _ x (Finish e v x)); eauto; [now constructor | rewrite unfold_entailsR; apply Heu]. }
          specialize (Hk _ _ HR) as Hkx; cdestruct Hkx.
          exists t1, w0; split...
          rewrite Heq in TR.
          eapply (ktrans_bind_r _ _ _ x _ (Finish e v x)); eauto; now constructor.
  Qed.

  Corollary eur_bind_r_done_eu{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      not_done w ->
      <[ t, w |= φ EU done R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ EN (φ EU ψ) ]>) ->
      <[ {x <- t ;; k x}, w |= φ EU ψ ]>.
  Proof.
    intros; cright; eapply eur_bind_r_done; eauto.
  Qed.

  Lemma eur_done_en{X}: forall (t: ctree E B X) w φ R',
      not_done w ->
      <[ t, w |= φ EU done R' ]> ->
      <[ t, w |= φ EN (φ EU done R') ]>.
  Proof.
    intros * Hd H.
    cdestruct H; auto.
    cdestruct H; inv Hd.
  Qed.

  Corollary eur_bind_r_done_post{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ R R',
      not_done w ->
      <[ t, w |= φ EU done R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ EU done R' ]>) ->
      <[ {x <- t ;; k x}, w |= φ EU done R' ]>.
  Proof.
    intros * Hd Heu Hk.
    apply eur_bind_r_done_eu with (fun x w => R x w /\ not_done w); auto.
    - now apply eur_done_not_done.
    - intros x w' (HR & Hd').
      apply eur_done_en; auto.
  Qed.

  Theorem eul_bind_r_done{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ (ψ: ticll E) R,
      not_done w ->
      <[ t, w |= φ EU done R ]> ->
      (forall x w, R x w -> <( {k x}, w |= φ EN (φ EU ψ) )>) ->
      <( {x <- t ;; k x}, w |= φ EN (φ EU ψ) )>.
  Proof with eauto with ticl.
    intros * Hd Heu Hk.
    cinduction Heu.
    - cdestruct Hp; inv Hd.
    - csplit.
      + now apply ticll_bind_l.
      + apply ktrans_succ_cases in TR as Hc;
          destruct Hc as [Hd' | [(x & -> & Hw & Heq) | (Z & e & v & x & -> & Hw & Heq)]].
        * exists (x <- t0 ;; k x), w0; split.
          -- apply ktrans_bind_l...
          -- cright; apply HInd...
        * assert (HR: R x w).
          { eapply (eur_done_leaf _ _ _ x (Done x)); eauto; [now constructor | rewrite unfold_entailsR; apply Heu]. }
          specialize (Hk _ _ HR) as Hkx; cdestruct Hkx.
          exists t1, w0; split...
          rewrite Heq in TR.
          eapply (ktrans_bind_r _ _ _ x _ (Done x)); eauto; now constructor.
        * assert (HR: R x w).
          { eapply (eur_done_leaf _ _ _ x (Finish e v x)); eauto; [now constructor | rewrite unfold_entailsR; apply Heu]. }
          specialize (Hk _ _ HR) as Hkx; cdestruct Hkx.
          exists t1, w0; split...
          rewrite Heq in TR.
          eapply (ktrans_bind_r _ _ _ x _ (Finish e v x)); eauto; now constructor.
  Qed.

  (** Chain lemmas for [AG]/[EG] through a world-only termination premise. *)
  Lemma ag_bind_done_chain {X Y} (φ: ticll E) (Post: rel X (World E))
    {R: Chain (agcF (entailsL Y φ))} :
    forall (t: ctree E B X) (k: X -> ctree E B Y) w,
      not_done w ->
      <[ t, w |= φ AU done Post ]> ->
      (forall x w, Post x w -> `R (k x) w) ->
      `R (x <- t ;; k x) w.
  Proof with auto with ticl.
    apply tower.
    - intros ? INC t k w Hd Hau Hk ? ?.
      apply INC; auto.
      intros x w' HP.
      apply leq_infx in H.
      apply H; now apply Hk.
    - intros R' IH t k w Hd Hau Hk.
      cinduction Hau.
      + cdestruct Hp; inv Hd.
      + split2.
        * now apply ticll_bind_l.
        * eapply can_step_bind_done; eauto.
          -- intros t' w' TR; rewrite unfold_entailsR; now apply Hau0.
          -- intros x w' HR; specialize (Hk _ _ HR) as (_ & ? & _); auto.
        * intros k_ w_ TRk.
          apply ktrans_bind_inv in TRk as
              [(t0' & TR0 & Hd_ & Heq) | (x & w0 & TRt0 & Hr & TRk)].
          -- rewrite Heq.
             apply IH; auto.
             ++ rewrite unfold_entailsR; now apply Hau0.
             ++ intros; apply (b_chain R'); now apply Hk.
          -- assert (HR: Post x w).
             { eapply aur_done_leaf; eauto; rewrite unfold_entailsR; now apply Hau0. }
             specialize (Hk _ _ HR) as (_ & _ & HR'); now apply HR'.
  Qed.

  Lemma ag_bind_r_done{X Y}: forall (t: ctree E B X) w (k: X -> ctree E B Y) φ R,
      not_done w ->
      <[ t, w |= φ AU done R ]> ->
      (forall x w, R x w -> <( {k x}, w |= AG φ )>) ->
      <( {x <- t ;; k x}, w |= AG φ )>.
  Proof.
    intros.
    rewrite unfold_entailsL.
    apply (ag_bind_done_chain φ R (R:=chain_gfp _)); auto.
  Qed.

  Lemma eg_bind_done_chain {X Y} (φ: ticll E) (Post: rel X (World E))
    {R: Chain (egcF (entailsL Y φ))} :
    forall (t: ctree E B X) (k: X -> ctree E B Y) w,
      not_done w ->
      <[ t, w |= φ EU done Post ]> ->
      (forall x w, Post x w -> `R (k x) w) ->
      `R (x <- t ;; k x) w.
  Proof with auto with ticl.
    apply tower.
    - intros ? INC t k w Hd Heu Hk ? ?.
      apply INC; auto.
      intros x w' HP.
      apply leq_infx in H.
      apply H; now apply Hk.
    - intros R' IH t k w Hd Heu Hk.
      cinduction Heu.
      + cdestruct Hp; inv Hd.
      + split.
        * now apply ticll_bind_l.
        * apply ktrans_succ_cases in TR as Hc;
            destruct Hc as [Hd' | [(x & -> & Hw & Heq) | (Z & e & v & x & -> & Hw & Heq)]].
          -- exists (x <- t0 ;; k x), w0; split.
             ++ apply ktrans_bind_l...
             ++ apply (IH _ _ _ Hd').
                ** rewrite unfold_entailsR; exact Heu.
                ** intros; apply (b_chain R'); now apply Hk.
          -- assert (HR: Post x w).
             { eapply (eur_done_leaf _ _ _ x (Done x)); eauto; [now constructor | rewrite unfold_entailsR; apply Heu]. }
             specialize (Hk _ _ HR) as (_ & k' & w' & TRk & HR').
             exists k', w'; split; auto.
             rewrite Heq in TR.
             eapply (ktrans_bind_r _ _ _ x _ (Done x)); eauto; now constructor.
          -- assert (HR: Post x w).
             { eapply (eur_done_leaf _ _ _ x (Finish e v x)); eauto; [now constructor | rewrite unfold_entailsR; apply Heu]. }
             specialize (Hk _ _ HR) as (_ & k' & w' & TRk & HR').
             exists k', w'; split; auto.
             rewrite Heq in TR.
             eapply (ktrans_bind_r _ _ _ x _ (Finish e v x)); eauto; now constructor.
  Qed.

  Lemma eg_bind_r_done{X Y}: forall (t: ctree E B X) w (k: X -> ctree E B Y) φ R,
      not_done w ->
      <[ t, w |= φ EU done R ]> ->
      (forall x w, R x w -> <( {k x}, w |= EG φ )>) ->
      <( {x <- t ;; k x}, w |= EG φ )>.
  Proof.
    intros.
    rewrite unfold_entailsL.
    apply (eg_bind_done_chain φ R (R:=chain_gfp _)); auto.
  Qed.

End BindLemmas.

(** ** Convenience lemmas for [bind] and instrumentation events [log s]. *)
Section LogLemmas.
  Context {B: Type -> Type}.

  (** A log retains the current world for its prefix obligation and has
      exactly one successor, at the world recording that log. *)
  Lemma anl_log_iff {X W} (s : W) (k : ctreeW W B X) w (φ ψ : ticll (writerE W)) :
    <( {log s;; k}, w |= φ AN ψ )> <->
    <( {log s;; k}, w |= φ )> /\ <( k, {Obs (Log s) tt} |= ψ )>.
  Proof.
    unfold log, CTree.trigger.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite (anl_vis (Log s) _ tt).
    split.
    - intros [Hφ Hnext]; split; [exact Hφ | exact (Hnext tt)].
    - intros [Hφ Hnext]; split; [exact Hφ | intros []; exact Hnext].
  Qed.

  Lemma anr_log_iff {X W} (s : W) (k : ctreeW W B X) w
    (φ : ticll (writerE W)) (ψ : ticlr (writerE W) X) :
    <[ {log s;; k}, w |= φ AN ψ ]> <->
    <( {log s;; k}, w |= φ )> /\ <[ k, {Obs (Log s) tt} |= ψ ]>.
  Proof.
    unfold log, CTree.trigger.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite (anr_vis (Log s) _ tt).
    split.
    - intros [Hφ Hnext]; split; [exact Hφ | exact (Hnext tt)].
    - intros [Hφ Hnext]; split; [exact Hφ | intros []; exact Hnext].
  Qed.

  Lemma aul_log_iff {X W} (s : W) (k : ctreeW W B X) w (φ ψ : ticll (writerE W)) :
    <( {log s;; k}, w |= φ AU ψ )> <->
    <( {log s;; k}, w |= ψ )> \/
    (<( {log s;; k}, w |= φ )> /\ <( k, {Obs (Log s) tt} |= φ AU ψ )>).
  Proof.
    unfold log, CTree.trigger.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite <- (aul_vis (Log s) _ tt).
    split.
    - intros [Hψ | [Hφ Hnext]];
        [left; exact Hψ | right; split; [exact Hφ | exact (Hnext tt)]].
    - intros [Hψ | [Hφ Hnext]];
        [left; exact Hψ | right; split; [exact Hφ | intros []; exact Hnext]].
  Qed.

  Lemma aur_log_iff {X W} (s : W) (k : ctreeW W B X) w
    (φ : ticll (writerE W)) (ψ : ticlr (writerE W) X) :
    <[ {log s;; k}, w |= φ AU ψ ]> <->
    <[ {log s;; k}, w |= ψ ]> \/
    (<( {log s;; k}, w |= φ )> /\ <[ k, {Obs (Log s) tt} |= φ AU ψ ]>).
  Proof.
    unfold log, CTree.trigger.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite <- (aur_vis (Log s) _ tt).
    split.
    - intros [Hψ | [Hφ Hnext]];
        [left; exact Hψ | right; split; [exact Hφ | exact (Hnext tt)]].
    - intros [Hψ | [Hφ Hnext]];
        [left; exact Hψ | right; split; [exact Hφ | intros []; exact Hnext]].
  Qed.

  Lemma ag_log_iff {X W} (s : W) (k : ctreeW W B X) w (φ : ticll (writerE W)) :
    <( {log s;; k}, w |= AG φ )> <->
    <( {log s;; k}, w |= φ )> /\ <( k, {Obs (Log s) tt} |= AG φ )>.
  Proof.
    unfold log, CTree.trigger.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite <- (ag_vis (Log s) _ tt).
    split.
    - intros [Hφ Hnext]; split; [exact Hφ | exact (Hnext tt)].
    - intros [Hφ Hnext]; split; [exact Hφ | intros []; exact Hnext].
  Qed.

  Lemma anl_log{X S}: forall (s: S) (k: ctreeW S B X) w ψ φ,
      <( k, {Obs (Log s) tt} |= ψ )> ->
      <( {log s;; k }, w |= φ )> ->
      <( {log s;; k }, w |= φ AN ψ )>.
  Proof.
    intros; apply anl_log_iff; auto.
  Qed.
  
  Lemma axl_log{X S}: forall (s: S) (k: ctreeW S B X) w φ,
      not_done w ->
      <( k, {Obs (Log s) tt} |= φ )> ->
      <( {log s;; k }, w |= AX φ )>.
  Proof with eauto with ticl.
    intros.
    apply anl_log...
    csplit...
  Qed.
  
  Lemma anr_log{X S}: forall (s: S) (k: ctreeW S B X) w ψ φ,
      <[ k, {Obs (Log s) tt} |= ψ ]> ->
      <( {log s;; k }, w |= φ )> ->
      <[ {log s;; k }, w |= φ AN ψ ]>.
  Proof.
    intros; apply anr_log_iff; auto.
  Qed.
  
  Lemma axr_log{X S}: forall (s: S) (k: ctreeW S B X) w φ,
      not_done w ->
      <[ k, {Obs (Log s) tt} |= φ ]> ->
      <[ {log s;; k }, w |= AX φ ]>.
  Proof with eauto with ticl.
    intros.
    apply anr_log...
    csplit...
  Qed.
  
  Lemma afl_log{X S}: forall (s: S) (k: ctreeW S B X) w φ,
      not_done w ->
      <( k, {Obs (Log s) tt} |= AF φ )> ->
      <( {log s;; k }, w |= AF φ )>.
  Proof with eauto with ticl.
    intros.
    apply aul_log_iff; right; split...
    csplit...
  Qed.

  Lemma aur_log{X S}: forall (s: S) (k: ctreeW S B X) w ψ φ,
      <[ k, {Obs (Log s) tt} |= ψ AU φ ]> ->
      <( {log s;; k }, w |= ψ )> ->
      <[ {log s;; k }, w |= ψ AU φ ]>.  
  Proof.
    intros; apply aur_log_iff; right; auto.
  Qed.
  
  Lemma afr_log{X S}: forall (s: S) (k: ctreeW S B X) w φ,
      not_done w ->
      <[ k, {Obs (Log s) tt} |= AF φ ]> ->
      <[ {log s;; k }, w |= AF φ ]>.
  Proof with eauto with ticl.
    intros.
    eapply aur_log...
    csplit...
  Qed.

  Lemma enr_log{X S}: forall (s: S) (k: ctreeW S B X) w ψ φ,
      <[ k, {Obs (Log s) tt} |= EX ψ ]> ->
      <( {log s;; k }, w |= φ )> ->
      <[ {log s;; k }, w |= φ EN EX ψ ]>.
  Proof with eauto with ticl.
    intros.
    csplit...
    exists k, (Obs (Log s) tt); split...
    unfold log, CTree.trigger; rewrite bind_vis.
    apply ktrans_vis; exists tt; split2...
    - now rewrite bind_ret_l.
    - now apply ticll_not_done in H0.
  Qed.
  
  Lemma eur_log{X S}: forall (s: S) (k: ctreeW S B X) w ψ φ,
      <[ k, {Obs (Log s) tt} |= ψ EU φ ]> ->
      <( {log s;; k }, w |= ψ )> ->
      <[ {log s;; k }, w |= ψ EU φ ]>. 
  Proof with eauto with ticl.
    intros.
    cright.
    csplit...    
    exists k, (Obs (Log s) tt); split...
    unfold log, CTree.trigger; rewrite bind_vis.
    apply ktrans_vis; exists tt; split2...
    - now rewrite bind_ret_l.
    - now apply ticll_not_done in H0.
  Qed.

  Lemma efr_log{X S}: forall (s: S) (k: ctreeW S B X) w φ,
      not_done w ->
      <[ k, {Obs (Log s) tt} |= EF φ ]> ->
      <[ {log s;; k }, w |= EF φ ]>.
  Proof with eauto with ticl.
    intros.
    eapply eur_log...
    csplit; intuition.
  Qed.

End LogLemmas.
