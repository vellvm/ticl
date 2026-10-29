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
(** Immediate-return premises use [ret]; until premises reach [ret] leaves,
    where the continuation takes over the complete temporal obligation. *)
Section BindLemmas.
  Context {E B: Type -> Type}.

  (** Prove by induction on formulas [φ]; if [t] satisfies prefix formula [φ] then so do all its extensions ([x <- t ;; k x]) *)
  Theorem ticll_bind_l{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) φ w,
      <( t, w |= φ )> ->
      <( {x <- t ;; k x}, w |= φ )>.
  Proof.
    intros.
    generalize dependent t.
    revert X Y w k.
    induction φ; intros; try destruct q; intros. 
    - (* NOW *) cdestruct H; now csplit.
    - (* AU *)
      cinduction H; intros; subst.
      + (* MatchA *) cleft; auto with ticl.
      + (* StepA *)
        cright; csplit; auto with ticl. 
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
             apply HInd; auto with ticl.
          -- specialize (HInd _ _ TR').
             apply ticll_not_done in HInd; inv Hr; inv HInd.
    - (* EU *)      
      cinduction H; intros; subst.
      + (* MatchE *) cleft; auto with ticl.
      + (* StepE *)
        cright; csplit; auto with ticl.
        exists (x <- t0 ;; k x), w0; split.
        * apply ktrans_bind_l; auto with ticl.
          now apply ticll_not_done in HInd. 
        * apply HInd.
    - (* AN *)
      cdestruct H; csplit; auto with ticl.
      + (* can_step *) destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'; auto with ticl.
        eapply ticll_not_done, (H _ _ TR).
      + (* forall *) intros t' w' TR.
        apply ktrans_bind_inv in TR as
            [(t_ & TR' & Hd & ->) |
              (x & w_ & TR' & Hr & TRk)].
        * apply IHφ2, H; auto with ticl.
        * specialize (H _ _ TR').
          inv Hr; apply ticll_not_done in H; inv H.
    - (* EN *)
      cdestruct H; csplit; auto with ticl.
      exists (x <- t0;; k x), w0; split; auto with ticl.
      apply ktrans_bind_l; auto with ticl.
      now apply ticll_not_done in H.
    - (* AG *)
      generalize dependent t.
      revert w.
      coinduction_g R CIH; intros w t H; split2.
      + apply IHφ.
        now cdestruct H.
      + cdestruct H.
        destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'; auto with ticl.
        eapply ticll_not_done, (H _ _ TR).
      + intros t' w' TR.
        cdestruct H.
        apply ktrans_bind_inv in TR as
            [(t_ & TR' & Hd & ->) |
              (x & w_ & TR' & Hr & TRk)].
        * apply CIH; auto with ticl.
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
        split; auto with ticl.
        apply ktrans_bind_l; auto with ticl.
        eapply ticll_not_done, H.
    - (* AND *)
      cdestruct H; csplit; auto with ticl.
    - (* OR *)
      cdestruct H; [cleft | cright]; auto with ticl.
  Qed.

  (** Bind lemmas for prefix [AN]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ AN ψ] with prefix formula [ψ]. *)
  Theorem anl_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= ret R ]> ->
      (forall x w, R x w -> <( {k x}, w |= φ AN ψ )>) ->
      <( {x <- t ;; k x}, w |= φ AN ψ )>.  
  Proof.
    intros * Hret Hk.
    apply ret_sbisim in Hret as (x & HR & Heq).
    rewrite Heq, bind_ret_l.
    now apply Hk.
  Qed.
 
  (** Bind lemmas for suffix [AN]; requires specifying a postcondition [R] for the return values of [t].
  If [t] takes a step, then the continuation [k x] must satisfy postcondition [ψ] without the need to step *)
  Theorem anr_bind_l{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ AN ret R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ AN ψ ]>.  
  Proof.
    intros.
    cdestruct H; csplit; eauto with ticl.
    - now apply ticll_bind_l.
    - (* can_step *)
      destruct Hs as (t_ & w_ & TR_).
      eapply can_step_bind_l; eauto with ticl.
      specialize (H _ _ TR_).
      cdestruct H; eauto with ticl.
    - intros y wr TR.
      apply ktrans_bind_inv in TR as
          [(t_ & TR_ & Hd & ->) |
            (x & w_ & TR_ & Hr & TRk)].
      + specialize (H _ _ TR_).
        apply ret_sbisim in H as (x & HR & Heqt).
        rewrite Heqt, bind_ret_l; eauto with ticl.
      + specialize (H _ _ TR_) as Hax.
        cdestruct Hax; inv Hr; inv Hd.
  Qed.
  
  (** Bind lemma for suffix [AN]; requires specifying a postcondition [R] for the return values of [t].
  If [t] immediately terminates with post-condition [R], then the continuation [k x] must take a step to satisfy postcondition [ψ]. *)
  Theorem anr_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= ret R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ AN ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ AN ψ ]>.  
  Proof.
    intros * Hret Hk.
    apply ret_sbisim in Hret as (x & HR & Heq).
    rewrite Heq, bind_ret_l.
    now apply Hk.
  Qed.

  (** Helper version of [anr_bind_r] for deterministic [t], it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem anr_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ r w',
      <[ t, w |= ret= r w' ]> ->
      <[ {k r}, w' |= φ AN ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ AN ψ ]>.  
  Proof.
    intros.
    eapply anr_bind_r; eauto with ticl.
    now intros * [-> ->].
  Qed.
  
  (** Bind lemmas for prefix [EN]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ EN ψ] with prefix formula [ψ]. *)
  Theorem enl_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= ret R ]> ->
      (forall r w', R r w' -> <( {k r}, w' |= φ EN ψ )>) ->
      <( {x <- t ;; k x}, w |= φ EN ψ )>.
  Proof.
    intros * Hret Hk.
    apply ret_sbisim in Hret as (x & HR & Heq).
    rewrite Heq, bind_ret_l.
    now apply Hk.
  Qed.

  (** Helper version of [enl_bind_r] for deterministic [t], it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem enl_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' φ ψ r,
      <[ t, w |= ret= r w' ]> ->
      <( {k r}, w' |= φ EN ψ )> ->
      <( {x <- t ;; k x}, w |= φ EN ψ )>.
  Proof.
    intros.
    apply enl_bind_r with (R:=fun x w => r = x /\ w' = w); eauto with ticl.
    intros r_ w_ (-> & ->); eauto with ticl.
  Qed.
  
  (** Bind lemmas for suffix [EN]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ EN ψ] with post-condition [ψ]. *)
  Theorem enr_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= ret R ]> ->
      (forall r w', R r w' -> <[ {k r}, w' |= φ EN ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ EN ψ ]>.
  Proof.
    intros * Hret Hk.
    apply ret_sbisim in Hret as (x & HR & Heq).
    rewrite Heq, bind_ret_l.
    now apply Hk.
  Qed.
  
  (** Helper version of [enr_bind_r] for deterministic [t], it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem enr_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' φ ψ r,
      <[ t, w |= ret= r w' ]> ->
      <[ {k r}, w' |= φ EN ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ EN ψ ]>.
  Proof.
    intros.
    apply enr_bind_r with (R:=fun x w => r = x /\ w' = w); eauto with ticl.
    intros r_ w_ (-> & ->); eauto with ticl.
  Qed.
  
  (** Bind lemmas for prefix until [AU]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ AU ψ] with prefix formula [ψ]. *)
  Theorem aul_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ AU ret R ]> ->
      (forall x w, R x w -> <( {k x}, w |= φ AU ψ )>) ->
      <( {x <- t ;; k x}, w |= φ AU ψ )>.  
  Proof.
    intros.
    cinduction H. 
    - apply ret_sbisim in Hp as (y & HR & Heqt).
      rewrite Heqt, bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ticll_bind_l.
      + destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'; eauto with ticl.
        specialize (HInd _ _ TR).
        now apply ticll_not_done in HInd.
      + intros t' w' TR'.
        apply ktrans_bind_inv in TR' as
            [(t_ & TR_ & Hd & ->) |
              (x & w_ & TR_ & Hr & TRk)].
        * apply HInd; eauto with ticl.
        * specialize (Hau _ _ TR_).
          change (auc  (entailsL _ ?φ) (entailsR ?ψ) ?t ?w)
            with <[ t, w |= φ AU ψ ]> in Hau.
          apply aur_stuck in Hau.
          cdestruct Hau; inv Hr; inv Hd.
  Qed.
  
  (** A fixed terminal result on every successor is exactly native return. *)
  Lemma ret_done_eq_iff {X} (t : ctree E B X) w r wr :
    anc (entailsL X (CNow (fun _ => True)))
      (fun _ wd => done_with (fun x z => r = x /\ wr = z) wd) t w <->
    entailsR (CRet (fun x z => r = x /\ wr = z)) t w.
  Proof.
    split.
    - intros (Htop & Hs & Htr).
      assert (Hw : wr = w).
      { destruct Hs as (t' & wd & TR).
        specialize (Htr _ _ TR).
        destruct Htr as [x Hpost | Y e v x Hpost].
        - destruct Hpost as (_ & ->).
          now apply ktrans_to_done_inv in TR as (_ & ->).
        - destruct Hpost as (_ & ->).
          now apply ktrans_to_finish_inv in TR as (_ & ->). }
      subst wr.
      apply ticlr_ret; exists r; split; [split; reflexivity |].
      split; [now apply ticll_not_done in Htop |].
      split; [exact Hs |].
      intros t' wd TR; apply done_of_eq; now apply (Htr t' wd).
    - apply ret_done_next.
  Qed.

  (** Helper version of [aul_bind_r] for deterministic [t], it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem aul_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ r w',
      <[ t, w |= φ AU ret= r w' ]> ->
      <( {k r}, w' |= φ AU ψ )> ->
      <( {x <- t ;; k x}, w |= φ AU ψ )>.
  Proof.
    intros.
    apply aul_bind_r with (R:=fun x w => r = x /\ w' = w); eauto with ticl.
    intros ? ? [<- <-]; eauto with ticl.
  Qed.

  (** Bind lemmas for suffix until [AU]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ AU ψ] with post-condition [ψ]. *)
  Theorem aur_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ AU ret R ]> ->
      (forall x w, R x w -> <[ {k x}, w |= φ AU ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ AU ψ ]>.  
  Proof.
    intros.
    cinduction H. 
    - apply ret_sbisim in Hp as (y & HR & Heqt).
      rewrite Heqt, bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ticll_bind_l.
      + destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'; eauto with ticl.
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
        * apply HInd; eauto with ticl.
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
  Proof.
    intros t k w phi psi R Ht Hk.
    cdestruct Ht; csplit; eauto with ticl.
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
      <[ t, w |= φ AU ret= r w' ]> ->
      <[ {k r}, w' |= φ AU ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ AU ψ ]>.
  Proof.
    intros.
    apply aur_bind_r with (R:=fun x w => r = x /\ w' = w); eauto with ticl.
    intros ? ? [<- <-]; eauto with ticl.
  Qed.
  
  (** Bind lemmas for prefix [EU]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ EU ψ] with prefix formula [ψ]. *)
  Theorem eul_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ EU ret R ]> ->
      (forall r w', R r w' -> <( {k r}, w' |= φ EU ψ )>) ->
      <( {x <- t ;; k x}, w |= φ EU ψ )>.
  Proof.
    intros.
    cinduction H; intros.
    - apply ret_sbisim in Hp as (y & HR & Heqt).
      rewrite Heqt, bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ticll_bind_l.
      + exists (x <- t0;; k x), w0; split; eauto with ticl.
        assert(Hd: not_done w0) by now apply ticll_not_done in HInd.
        apply ktrans_bind_l; eauto with ticl.
  Qed.

  (** Helper version of [eul_bind_r] for deterministic [t] ([ret= r w']), it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. With hidden branching, one terminal
  successor returning [r] is not enough: another branch may return a different value. *)
  Theorem eul_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ r w',
      <[ t, w |= φ EU ret= r w' ]> ->
      <( {k r}, w' |= φ EU ψ )> ->
      <( {x <- t ;; k x}, w |= φ EU ψ )>.
  Proof.
    intros.
    apply eul_bind_r with (R:=fun x w => r = x /\ w' = w); eauto with ticl.
    intros ? ? [<- <-]; eauto with ticl.
  Qed.
  
  (** Bind lemmas for suffix [EU]; requires specifying a postcondition [R] for the return values of [t],
  then showing the continuation [k x] will always step [φ EU ψ] with post-condition [ψ]. *)
  Theorem eur_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ t, w |= φ EU ret R ]> ->
      (forall r w', R r w' -> <[ {k r}, w' |= φ EU ψ ]>) ->
      <[ {x <- t ;; k x}, w |= φ EU ψ ]>.
  Proof.
    intros.
    cinduction H; intros.
    - apply ret_sbisim in Hp as (y & HR & Heqt).
      rewrite Heqt, bind_ret_l.
      now apply H0.
    - cright; csplit.
      + now apply ticll_bind_l.
      + exists (x <- t0;; k x), w0; split; eauto with ticl.
        destruct Heu.
        * cdestruct H.
          apply ktrans_bind_l; eauto with ticl.
        * destruct H.
          apply ticll_not_done in H.
          apply ktrans_bind_l; eauto with ticl.
  Qed.

  (** Helper version of [eur_bind_r] for deterministic [t] ([ret= r w']), it allows us to
  replace the return value [r] with an existential quantifier, then simply compute it. 
  This does not require a postcondition [R]. *)
  Theorem eur_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ r w',
      <[ t, w |= φ EU ret= r w' ]> ->
      <[ {k r}, w' |= φ EU ψ ]> ->
      <[ {x <- t ;; k x}, w |= φ EU ψ ]>.
  Proof.
    intros.
    apply eur_bind_r with (R:=fun x w => r = x /\ w' = w); eauto with ticl.
    intros ? ? [<- <-]; eauto with ticl.
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
  Proof.
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
          apply can_step_bind_l with t' w'; auto with ticl.
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
  Proof.
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
          -- apply ktrans_bind_l; auto with ticl.
             destruct Heu as [? ? Hret | ? ? (Hφ & _)].
             ++ cdestruct Hret; auto with ticl.
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
  Proof.
    intros.
    apply anl_log; eauto with ticl.
    csplit; eauto with ticl.
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
  Proof.
    intros.
    apply anr_log; eauto with ticl.
    csplit; eauto with ticl.
  Qed.
  
  Lemma afl_log{X S}: forall (s: S) (k: ctreeW S B X) w φ,
      not_done w ->
      <( k, {Obs (Log s) tt} |= AF φ )> ->
      <( {log s;; k }, w |= AF φ )>.
  Proof.
    intros.
    apply aul_log_iff; right; split; eauto with ticl.
    csplit; eauto with ticl.
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
  Proof.
    intros.
    eapply aur_log; eauto with ticl.
    csplit; eauto with ticl.
  Qed.

  Lemma enr_log{X S}: forall (s: S) (k: ctreeW S B X) w ψ φ,
      <[ k, {Obs (Log s) tt} |= EX ψ ]> ->
      <( {log s;; k }, w |= φ )> ->
      <[ {log s;; k }, w |= φ EN EX ψ ]>.
  Proof.
    intros.
    csplit; eauto with ticl.
    exists k, (Obs (Log s) tt); split; eauto with ticl.
    unfold log, CTree.trigger; rewrite bind_vis.
    apply ktrans_vis; exists tt; split2; eauto with ticl.
    - now rewrite bind_ret_l.
    - now apply ticll_not_done in H0.
  Qed.
  
  Lemma eur_log{X S}: forall (s: S) (k: ctreeW S B X) w ψ φ,
      <[ k, {Obs (Log s) tt} |= ψ EU φ ]> ->
      <( {log s;; k }, w |= ψ )> ->
      <[ {log s;; k }, w |= ψ EU φ ]>. 
  Proof.
    intros.
    cright.
    csplit; eauto with ticl.    
    exists k, (Obs (Log s) tt); split; eauto with ticl.
    unfold log, CTree.trigger; rewrite bind_vis.
    apply ktrans_vis; exists tt; split2; eauto with ticl.
    - now rewrite bind_ret_l.
    - now apply ticll_not_done in H0.
  Qed.

  Lemma efr_log{X S}: forall (s: S) (k: ctreeW S B X) w φ,
      not_done w ->
      <[ k, {Obs (Log s) tt} |= EF φ ]> ->
      <[ {log s;; k }, w |= EF φ ]>.
  Proof.
    intros.
    eapply eur_log; eauto with ticl.
    csplit; intuition.
  Qed.

End LogLemmas.
