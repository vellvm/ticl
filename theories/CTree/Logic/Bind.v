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

(** Shallow kernels expose one real transition, with predicates evaluated on
    the continuing normal form.  A live guard is necessary at next steps. *)
Lemma quntil_unfold {E B X} q
    (P Q : ctree E B X -> World E -> Prop) t w :
  quntil q P Q t w <-> Q t w \/ qnext q P (quntil q P Q) t w.
Proof.
  destruct q; cbn [quntil qnext]; split; intro H.
  - inversion H; subst; [now left|now right].
  - destruct H; [now apply MatchA|now apply StepA].
  - inversion H; subst; [now left|now right].
  - destruct H; [now apply MatchE|now apply StepE].
Qed.

Lemma qnext_vis_iff {E B X Y} q (e : E Y)
    (k : Y -> ctree E B X) (y0 : Y)
    (P Q : ctree E B X -> World E -> Prop)
    (HP : Proper (sbisim eq ==> eq ==> iff) P)
    (HP_live : forall t w, P t w -> not_done w)
    (HQ : Proper (sbisim eq ==> eq ==> iff) Q) w :
  qnext q P Q (Vis e k) w <->
  P (Vis e k) w /\
    match q with
    | Q_A => forall y, Q (k y) (Obs e y)
    | Q_E => exists y, Q (k y) (Obs e y)
    end.
Proof.
  destruct q; cbn [qnext]; unfold anc, enc; split.
  - intros (Hp & Hs & Hnext); split; [exact Hp|].
    intro y; apply Hnext, ktrans_vis; exists y; split2;
      eauto using HP_live with ticl.
  - intros (Hp & Hnext); split; [exact Hp|]; split.
    + apply (can_step_vis e k y0); now apply HP_live in Hp.
    + intros t' w' TR; apply ktrans_vis in TR as (y & -> & Heq & Hd).
      rewrite <- Heq; apply Hnext.
  - intros (Hp & t' & w' & TR & Hnext); split; [exact Hp|].
    apply ktrans_vis in TR as (y & -> & Heq & Hd).
    exists y; now rewrite <- Heq in Hnext.
  - intros (Hp & y & Hnext); split; [exact Hp|].
    exists (k y), (Obs e y); split; [|exact Hnext].
    apply ktrans_vis; exists y; split2; eauto using HP_live with ticl.
Qed.

Lemma qnext_brS_iff {E B X Y} q (c : B Y)
    (k : Y -> ctree E B X) (y0 : Y)
    (P Q : ctree E B X -> World E -> Prop)
    (HP : Proper (sbisim eq ==> eq ==> iff) P)
    (HP_live : forall t w, P t w -> not_done w)
    (HQ : Proper (sbisim eq ==> eq ==> iff) Q) w :
  qnext q P Q (BrS c k) w <->
  P (BrS c k) w /\
    match q with
    | Q_A => forall y, Q (k y) w
    | Q_E => exists y, Q (k y) w
    end.
Proof.
  destruct q; cbn [qnext]; unfold anc, enc; split.
  - intros (Hp & Hs & Hnext); split; [exact Hp|].
    intro y; apply Hnext, ktrans_brS; exists y; split2;
      eauto using HP_live with ticl.
  - intros (Hp & Hnext); split; [exact Hp|]; split.
    + apply (can_step_brS c k y0); now apply HP_live in Hp.
    + intros t' w' TR; apply ktrans_brS in TR as (y & Heq & -> & Hd).
      rewrite Heq; apply Hnext.
  - intros (Hp & t' & w' & TR & Hnext); split; [exact Hp|].
    apply ktrans_brS in TR as (y & Heq & -> & Hd).
    exists y; now rewrite Heq in Hnext.
  - intros (Hp & y & Hnext); split; [exact Hp|].
    exists (k y), w; split; [|exact Hnext].
    apply ktrans_brS; exists y; split2; eauto using HP_live with ticl.
Qed.

Lemma qnext_log_iff {W B X} q (o : W) (t : ctreeW W B X)
    (P Q : ctreeW W B X -> World (writerE W) -> Prop)
    (HP : Proper (sbisim eq ==> eq ==> iff) P)
    (HP_live : forall t w, P t w -> not_done w)
    (HQ : Proper (sbisim eq ==> eq ==> iff) Q) w :
  qnext q P Q (log o;; t) w <->
  P (log o;; t) w /\ Q t (Obs (Log o) tt).
Proof.
  unfold log, CTree.trigger; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite (qnext_vis_iff q (Log o) (fun _ => t) tt P Q HP HP_live HQ).
  destruct q; cbn.
  - split.
    + intros (Hp & Hnext); split; [exact Hp|apply Hnext].
    + intros (Hp & Hnext); split; [exact Hp|intros []; exact Hnext].
  - split.
    + intros (Hp & Hnext); split; [exact Hp|].
      destruct Hnext as ([] & Hnext); exact Hnext.
    + intros (Hp & Hnext); split; [exact Hp|exists tt; exact Hnext].
Qed.

Lemma qnext_step_iff {E B X} q (t : ctree E B X)
    (P Q : ctree E B X -> World E -> Prop)
    (HP : Proper (sbisim eq ==> eq ==> iff) P)
    (HP_live : forall t w, P t w -> not_done w)
    (HQ : Proper (sbisim eq ==> eq ==> iff) Q) w :
  qnext q P Q (Step t) w <-> P (Step t) w /\ Q t w.
Proof.
  destruct q; cbn [qnext]; unfold anc, enc; split.
  - intros (Hp & Hs & Hnext); split; [exact Hp|].
    apply Hnext, ktrans_step; split2; eauto using HP_live with ticl.
  - intros (Hp & Hnext); split; [exact Hp|]; split.
    + apply can_step_step; now apply HP_live in Hp.
    + intros t' w' TR; apply ktrans_step in TR as (Heq & -> & Hd).
      now rewrite Heq.
  - intros (Hp & t' & w' & TR & Hnext); split; [exact Hp|].
    apply ktrans_step in TR as (Heq & -> & Hd); now rewrite Heq in Hnext.
  - intros (Hp & Hnext); split; [exact Hp|].
    exists t, w; split; [|exact Hnext].
    apply ktrans_step; split2; eauto using HP_live with ticl.
Qed.

Lemma qnext_dead_iff {E B X} q (t : ctree E B X)
    (P Q : ctree E B X -> World E -> Prop) w :
  (forall u z, ~ ktrans t w u z) -> (qnext q P Q t w <-> False).
Proof.
  intro Dead; destruct q; cbn [qnext]; unfold anc, enc;
    split; [intros (_ & (u & z & TR) & _)|contradiction|
            intros (_ & u & z & TR & _)|contradiction];
    exact (Dead u z TR).
Qed.

Lemma quntil_dead_iff {E B X} q (t : ctree E B X)
    (P Q : ctree E B X -> World E -> Prop) w :
  (forall u z, ~ ktrans t w u z) -> (quntil q P Q t w <-> Q t w).
Proof. intro Dead; rewrite quntil_unfold, qnext_dead_iff by exact Dead; tauto. Qed.

Lemma spin_no_ktrans {E B X} w :
  forall (u : ctree E B X) z, ~ ktrans CTree.spin w u z.
Proof.
  intros u z TR; apply ktrans_trans in TR as (l & TR & _).
  now apply spin_is_stuck in TR.
Qed.

(** * TICL sequential composition ([bind]) lemmas for ctrees. *)
(** Immediate-return premises use [ret]; until premises reach [ret] leaves,
    where the continuation takes over the complete temporal obligation. *)
Section BindLemmas.
  Context {E B: Type -> Type}.

  (** Prove by induction on formulas [φ]; if [t] satisfies prefix formula [φ] then so do all its extensions ([x <- t ;; k x]) *)
  Theorem ticll_bind_l{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) (φ : ticll E) w,
      <( t, w |=L φ )> ->
      <( {x <- t ;; k x}, w |=L φ )>.
  Proof.
    ticl_normalize.
    intros.
    generalize dependent t.
    revert X Y w k.
    induction φ as [p | q φ1 IHφ1 φ2 IHφ2 | q φ1 IHφ1 φ2 IHφ2 | q φ IHφ | φ1 IHφ1 φ2 IHφ2 | φ1 IHφ1 φ2 IHφ2] using ticll_ind; intros; try destruct q; intros.
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
          change (auc (entails Y false φ1) (entails Y false φ2) ?t ?w)
            with <( t, w |=L φ1 AU φ2 )> in Hau.
          now eapply ticl_not_done in Hau. 
        * (* AN AF *)
          intros t_ w' TR_.
          apply ktrans_bind_inv in TR_ as
              [(t' & TR' & Hd & ->) |
                (x & ? & TR' & Hr & TRk)].
          -- specialize (Hau _ _ TR').
             apply HInd; auto with ticl.
          -- specialize (HInd _ _ TR').
             apply ticl_not_done in HInd; inv Hr; inv HInd.
    - (* EU *)      
      cinduction H; intros; subst.
      + (* MatchE *) cleft; auto with ticl.
      + (* StepE *)
        cright; csplit; auto with ticl.
        exists (x <- t0 ;; k x), w0; split.
        * apply ktrans_bind_l; auto with ticl.
          now apply ticl_not_done in HInd. 
        * apply HInd.
    - (* AN *)
      cdestruct H; csplit; auto with ticl.
      + (* can_step *) destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'; auto with ticl.
        eapply ticl_not_done, (H _ _ TR).
      + (* forall *) intros t' w' TR.
        apply ktrans_bind_inv in TR as
            [(t_ & TR' & Hd & ->) |
              (x & w_ & TR' & Hr & TRk)].
        * apply IHφ2, H; auto with ticl.
        * specialize (H _ _ TR').
          inv Hr; apply ticl_not_done in H; inv H.
    - (* EN *)
      cdestruct H; csplit; auto with ticl.
      exists (x <- t0;; k x), w0; split; auto with ticl.
      apply ktrans_bind_l; auto with ticl.
      now apply ticl_not_done in H.
    - (* AG *)
      generalize dependent t.
      revert w.
      coinduction_g R CIH; intros w t H; split2.
      + apply IHφ.
        now cdestruct H.
      + cdestruct H.
        destruct Hs as (t' & w' & TR).
        apply can_step_bind_l with t' w'; auto with ticl.
        eapply ticl_not_done, (H _ _ TR).
      + intros t' w' TR.
        cdestruct H.
        apply ktrans_bind_inv in TR as
            [(t_ & TR' & Hd & ->) |
              (x & w_ & TR' & Hr & TRk)].
        * apply CIH; auto with ticl.
        * specialize (H _ _ TR').
          inv Hr; apply ticl_not_done in H; inv H.
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
        eapply ticl_not_done, H.
    - (* AND *)
      cdestruct H; csplit; auto with ticl.
    - (* OR *)
      cdestruct H; [cleft | cright]; auto with ticl.
  Qed.

  (** Native return hands the complete indexed obligation to the continuation. *)
  Theorem ticl_bind_ret {X Y} {b : bool} :
    forall (t : ctree E B Y) (k : Y -> ctree E B X) w (p : ticl_at E X b) R,
      entails Y true (CRet R) t w ->
      (forall y w', R y w' -> entails X b p (k y) w') ->
      entails X b p (CTree.bind t k) w.
  Proof.
    intros * Hret Hk; apply ret_sbisim in Hret as (x & HR & Heq).
    rewrite Heq, bind_ret_l; now apply Hk.
  Qed.

  Theorem ticl_bind_ret_eq {X Y} {b : bool} :
    forall (t : ctree E B Y) (k : Y -> ctree E B X) w (p : ticl_at E X b) r wr,
      entails Y true (CRet (fun y z => r = y /\ wr = z)) t w ->
      entails X b p (k r) wr -> entails X b p (CTree.bind t k) w.
  Proof.
    intros * Hret Hk; eapply ticl_bind_ret; [exact Hret |].
    now intros y z [<- <-].
  Qed.

  Theorem an_bind_l {X Y} {b : bool} :
    forall (t : ctree E B Y) (k : Y -> ctree E B X) w
      (phi : ticll E) (psi : ticl_at E X b) R,
      entails Y true (Cx Q_A phi (CRet R)) t w ->
      (forall y w', R y w' -> entails X b psi (k y) w') ->
      entails X b (Cx Q_A phi psi) (CTree.bind t k) w.
  Proof.
    intros * H Hk; apply ticl_an in H as (Hp & Hs & Hnext); apply ticl_an.
    split; [now apply ticll_bind_l | split].
    - destruct Hs as (u & z & TR); eapply can_step_bind_l; [exact TR |].
      eapply ticl_not_done; apply Hnext; exact TR.
    - intros u z TR; apply ktrans_bind_inv in TR as
        [(v & TR & Hd & ->) | (x & wr & TR & Hd & TRk)].
      + specialize (Hnext _ _ TR); apply ret_sbisim in Hnext as (x & HR & Heq).
        rewrite Heq, bind_ret_l; now apply Hk.
      + specialize (Hnext _ _ TR); apply ticl_not_done in Hnext; inv Hd; inv Hnext.
  Qed.

  Theorem u_bind_r {X Y} {b : bool} (q : ticlq) :
    forall (t : ctree E B Y) (k : Y -> ctree E B X) w
      (phi : ticll E) (psi : ticl_at E X b) R,
      entails Y true (Cu q phi (CRet R)) t w ->
      (forall y w', R y w' -> entails X b (Cu q phi psi) (k y) w') ->
      entails X b (Cu q phi psi) (CTree.bind t k) w.
  Proof.
    intros * H Hk; destruct q.
    - assert (ND : forall (u : ctree E B Y) z,
        auc (entails Y false phi) (entails Y true (CRet R)) u z -> not_done z).
      { intros u z Hu; eapply (ticl_not_done Y true u z (Cu Q_A phi (CRet R))).
        now apply ticl_au. }
      apply ticl_au in H; apply ticl_au; induction H.
      + apply ret_sbisim in H as (x & HR & Heq).
        rewrite Heq, bind_ret_l; apply ticl_au; now apply Hk.
      + destruct H as (Hp & Hs & Hnext); destruct H0 as (_ & _ & IH).
        apply StepA; split; [now apply ticll_bind_l | split].
        * destruct Hs as (u & z & TR); eapply can_step_bind_l; [exact TR |].
          eapply ND; now apply (Hnext _ _ TR).
        * intros u z TR; apply ktrans_bind_inv in TR as
            [(v & TR & Hd & ->) | (x & wr & TR & Hd & TRk)].
          -- apply IH; exact TR.
          -- pose proof (ND _ _ (Hnext _ _ TR)) as Hnd; inv Hd; inv Hnd.
    - assert (ND : forall (u : ctree E B Y) z,
        euc (entails Y false phi) (entails Y true (CRet R)) u z -> not_done z).
      { intros u z Hu; eapply (ticl_not_done Y true u z (Cu Q_E phi (CRet R))).
        now apply ticl_eu. }
      apply ticl_eu in H; apply ticl_eu; induction H.
      + apply ret_sbisim in H as (x & HR & Heq).
        rewrite Heq, bind_ret_l; apply ticl_eu; now apply Hk.
      + destruct H as (Hp & u & z & TR & Hsource & IH).
        apply StepE; split; [now apply ticll_bind_l |].
        exists (CTree.bind u k), z; split; [|exact IH].
        apply ktrans_bind_l; [exact TR | now apply ND in Hsource].
  Qed.

  Theorem u_bind_r_eq {X Y} {b : bool} (q : ticlq) :
    forall (t : ctree E B Y) (k : Y -> ctree E B X) w
      (phi : ticll E) (psi : ticl_at E X b) r wr,
      entails Y true (Cu q phi (CRet (fun y z => r = y /\ wr = z))) t w ->
      entails X b (Cu q phi psi) (k r) wr ->
      entails X b (Cu q phi psi) (CTree.bind t k) w.
  Proof.
    intros * H Hk; eapply (u_bind_r q); [exact H |]; now intros y z [<- <-].
  Qed.

  Theorem ax_au_bind_r {X Y} {b : bool} :
    forall (t : ctree E B Y) (k : Y -> ctree E B X) w
      (phi : ticll E) (psi : ticl_at E X b) R,
      entails Y true (Cx Q_A (CNow (fun _ => True)) (Cu Q_A phi (CRet R))) t w ->
      (forall y w', R y w' -> entails X b (Cu Q_A phi psi) (k y) w') ->
      entails X b (Cx Q_A (CNow (fun _ => True)) (Cu Q_A phi psi)) (CTree.bind t k) w.
  Proof.
    intros * H Hk; apply ticl_an in H as (Hp & Hs & Hnext); apply ticl_an.
    split; [now apply ticll_bind_l | split].
    - destruct Hs as (u & z & TR); eapply can_step_bind_l; [exact TR |].
      eapply ticl_not_done; apply Hnext; exact TR.
    - intros u z TR; apply ktrans_bind_inv in TR as
        [(v & TR & Hd & ->) | (x & wr & TR & Hd & TRk)].
      + eapply (u_bind_r Q_A); [apply Hnext; exact TR | exact Hk].
      + specialize (Hnext _ _ TR); apply ticl_not_done in Hnext; inv Hd; inv Hnext.
  Qed.

  (** A fixed terminal result on every successor is exactly native return. *)
  Lemma ret_done_eq_iff {X} (t : ctree E B X) w r wr :
    anc (entails X false (CNow (fun _ => True)))
      (fun _ wd => done_with (fun x z => r = x /\ wr = z) wd) t w <->
    entails X true (CRet (fun x z => r = x /\ wr = z)) t w.
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
      apply ticl_ret; exists r; split; [split; reflexivity |].
      split; [now apply ticl_not_done in Htop |].
      split; [exact Hs |].
      intros t' wd TR; apply done_of_eq; now apply (Htr t' wd).
    - apply ret_done_next.
  Qed.


  (** ** Up-to bind principles for [AG] and [EG] (tower form) *)
  (** Every element [`R] of the final chain of [agcF (entails Y false φ)] is closed under
      sequencing a prefix [t] that satisfies [φ] until it returns a single value
      with post-condition [Post], provided the continuation lands in [`R]. The
      [gfp] itself is the last chain element ([chain_gfp]). *)
  Lemma ag_bind_chain {X Y} (φ: ticll E) (Post: rel X (World E))
    {R: Chain (agcF (entails Y false φ))} :
    forall (t: ctree E B X) (k: X -> ctree E B Y) w,
      <( t, w |=R φ AU ret Post )> ->
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
          apply (proj2 (ticl_au X true _ _ φ (CRet Post))) in Hinv.
          now apply ticl_not_done in Hinv.
        * intros k_ w_ TRk.
          apply ktrans_bind_inv in TRk as
              [(t0' & TR0 & Hd_ & Heq) | (x & w0 & TRt0 & Hd & TRk)].
          -- rewrite Heq.
             apply IH; [apply ticl_au; now apply Hau0 |].
             intros; apply (b_chain R'); now apply Hk.
          -- (* [t0] returned: contradiction with [ret] in a done world *)
             specialize (Hau0 _ _ TRt0) as Hinv.
             apply (proj2 (ticl_au X true _ _ φ (CRet Post))) in Hinv.
             apply ticl_not_done in Hinv; inv Hd; inv Hinv.
  Qed.

  (** ** Structural rule for the up-to bind principle for [AG]. *)
  (** [t] satisfies [φ] until it terminates with post-condition [R],
     then forall x w, R x w -> k x, w satisfies [φ] forever. *)
  Lemma ag_bind_r{X Y}: forall (t: ctree E B X)
                          w (k: X -> ctree E B Y) (φ : ticll E) R,
      <( t, w |=R φ AU ret R )> ->
      (forall (x: X) (w: World E), R x w -> <( {k x}, w |=L AG φ )>) ->
      <( {x <- t ;; k x} , w |=L AG φ )>.
  Proof.
    intros.
    ticl_normalize; rewrite unfold_entails_ag.
    apply (ag_bind_chain φ R (R:=chain_gfp _)); auto.
  Qed.

  Lemma eg_bind_chain {X Y} (φ: ticll E) (Post: rel X (World E))
    {R: Chain (egcF (entails Y false φ))} :
    forall (t: ctree E B X) (k: X -> ctree E B Y) w,
      <( t, w |=R φ EU ret Post )> ->
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
             destruct Heu0 as [? ? Hret | ? ? (Hφ & _)].
             ++ cdestruct Hret; auto with ticl.
             ++ now apply ticl_not_done in Hφ.
          -- apply IH; [apply ticl_eu; apply Heu0 |].
             intros; apply (b_chain R'); now apply Hk.
  Qed.

  (** ** Structural rule for the up-to bind principle for [EG]. *)
  Lemma eg_bind_r{X Y}: forall (t: ctree E B X) w (k: X -> ctree E B Y) R (φ : ticll E),
      <( t, w |=R φ EU ret R )> ->
      (forall r w', R r w' -> <( {k r}, w' |=L EG φ )>) ->
      <( {x <- t ;; k x} , w |=L EG φ )>.
  Proof.
    intros.
    ticl_normalize; rewrite unfold_entails_eg.
    apply (eg_bind_chain φ R (R:=chain_gfp _)); auto.
  Qed.
  
  (** Helper version of [eg_bind_r] for deterministic [t] ([ret= r wr]). *)
  Lemma eg_bind_r_eq{X Y}: forall (t: ctree E B X) r
                          w wr (k: X -> ctree E B Y) (φ : ticll E),
      <( t, w |=R φ EU ret= r wr )> ->
      <( {k r}, wr |=L EG φ )> ->
      <( {x <- t ;; k x} , w |=L EG φ )>.
  Proof.
    intros.
    apply eg_bind_r with (R:=fun r_ w_ => r = r_ /\ wr = w_); auto.
    now intros * (-> & ->).
  Qed.

End BindLemmas.

(** ** Convenience lemmas for [bind] and instrumentation events [log s]. *)
Section LogLemmas.
  Context {B: Type -> Type}.

  (** A log has one successor at its recorded observation world. *)
  Lemma an_log_iff {X W} {b : bool} (s : W) (k : ctreeW W B X) w
      (phi : ticll (writerE W)) (psi : ticl_at (writerE W) X b) :
    entails X b (Cx Q_A phi psi) (log s;; k) w <->
    entails X false phi (log s;; k) w /\ entails X b psi k (Obs (Log s) tt).
  Proof.
    unfold log, CTree.trigger; rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite (an_vis (b:=b) (Log s) _ tt); split.
    - intros [Hp Hnext]; split; [exact Hp | exact (Hnext tt)].
    - intros [Hp Hnext]; split; [exact Hp | intros []; exact Hnext].
  Qed.
  Lemma au_log_iff {X W} {b : bool} (s : W) (k : ctreeW W B X) w
      (phi : ticll (writerE W)) (psi : ticl_at (writerE W) X b) :
    entails X b (Cu Q_A phi psi) (log s;; k) w <->
    entails X b psi (log s;; k) w \/
    (entails X false phi (log s;; k) w /\ entails X b (Cu Q_A phi psi) k (Obs (Log s) tt)).
  Proof.
    unfold log, CTree.trigger; rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite <- (au_vis (b:=b) (Log s) _ tt); split.
    - intros [Hp | [Hg Hnext]]; [now left | right; split; [exact Hg | exact (Hnext tt)]].
    - intros [Hp | [Hg Hnext]]; [now left | right; split; [exact Hg | intros []; exact Hnext]].
  Qed.
  Lemma ag_log_iff {X W} (s : W) (k : ctreeW W B X) w (phi : ticll (writerE W)) :
    entails X false (Cg Q_A phi) (log s;; k) w <->
    entails X false phi (log s;; k) w /\ entails X false (Cg Q_A phi) k (Obs (Log s) tt).
  Proof.
    unfold log, CTree.trigger; rewrite bind_vis; setoid_rewrite bind_ret_l.
    pose proof (ag_vis (Log s) (fun _ : unit => k) tt w phi) as Hag.
    ticl_normalize in Hag; rewrite <- Hag; split.
    - intros [Hp Hnext]; split; [exact Hp | exact (Hnext tt)].
    - intros [Hp Hnext]; split; [exact Hp | intros []; exact Hnext].
  Qed.
  Lemma en_log_iff {X W} {b : bool} (s : W) (k : ctreeW W B X) w
      (phi : ticll (writerE W)) (psi : ticl_at (writerE W) X b) :
    entails X b (Cx Q_E phi psi) (log s;; k) w <->
    entails X false phi (log s;; k) w /\ entails X b psi k (Obs (Log s) tt).
  Proof.
    unfold log, CTree.trigger; rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite (en_vis (b:=b) (Log s) _); split.
    - intros [Hp [[] Hnext]]; now split.
    - intros [Hp Hnext]; split; [exact Hp | exists tt; exact Hnext].
  Qed.
  Lemma eu_log_iff {X W} {b : bool} (s : W) (k : ctreeW W B X) w
      (phi : ticll (writerE W)) (psi : ticl_at (writerE W) X b) :
    entails X b (Cu Q_E phi psi) (log s;; k) w <->
    entails X b psi (log s;; k) w \/
    (entails X false phi (log s;; k) w /\ entails X b (Cu Q_E phi psi) k (Obs (Log s) tt)).
  Proof.
    unfold log, CTree.trigger; rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite <- (eu_vis (b:=b) (Log s) _); split.
    - intros [Hp | [Hg [[] Hnext]]]; [now left | right; now split].
    - intros [Hp | [Hg Hnext]]; [now left | right; split; [exact Hg | exists tt; exact Hnext]].
  Qed.
  Lemma eg_log_iff {X W} (s : W) (k : ctreeW W B X) w (phi : ticll (writerE W)) :
    entails X false (Cg Q_E phi) (log s;; k) w <->
    entails X false phi (log s;; k) w /\ entails X false (Cg Q_E phi) k (Obs (Log s) tt).
  Proof.
    unfold log, CTree.trigger; rewrite bind_vis; setoid_rewrite bind_ret_l.
    pose proof (eg_vis (Log s) (fun _ : unit => k) w phi) as Heg.
    ticl_normalize in Heg; rewrite <- Heg; split.
    - intros [Hp [[] Hnext]]; now split.
    - intros [Hp Hnext]; split; [exact Hp | exists tt; exact Hnext].
  Qed.

  Lemma an_log {X S} {b : bool} : forall (s : S) (k : ctreeW S B X) w
      (psi : ticl_at (writerE S) X b) (phi : ticll (writerE S)),
    entails X b psi k (Obs (Log s) tt) -> entails X false phi (log s;; k) w ->
    entails X b (Cx Q_A phi psi) (log s;; k) w.
  Proof. intros; apply an_log_iff; auto. Qed.
  Lemma ax_log {X S} {b : bool} : forall (s : S) (k : ctreeW S B X) w
      (psi : ticl_at (writerE S) X b),
    not_done w -> entails X b psi k (Obs (Log s) tt) ->
    entails X b (Cx Q_A (CNow (fun _ => True)) psi) (log s;; k) w.
  Proof. intros; apply an_log; [assumption | apply ticl_now; auto]. Qed.
  Lemma au_log {X S} {b : bool} : forall (s : S) (k : ctreeW S B X) w
      (phi : ticll (writerE S)) (psi : ticl_at (writerE S) X b),
    entails X b (Cu Q_A phi psi) k (Obs (Log s) tt) ->
    entails X false phi (log s;; k) w -> entails X b (Cu Q_A phi psi) (log s;; k) w.
  Proof. intros; apply au_log_iff; right; auto. Qed.
  Lemma af_log {X S} {b : bool} : forall (s : S) (k : ctreeW S B X) w
      (psi : ticl_at (writerE S) X b),
    not_done w -> entails X b (Cu Q_A (CNow (fun _ => True)) psi) k (Obs (Log s) tt) ->
    entails X b (Cu Q_A (CNow (fun _ => True)) psi) (log s;; k) w.
  Proof. intros; apply au_log; [assumption | apply ticl_now; auto]. Qed.
  Lemma en_log {X S} {b : bool} : forall (s : S) (k : ctreeW S B X) w
      (psi : ticl_at (writerE S) X b) (phi : ticll (writerE S)),
    entails X b psi k (Obs (Log s) tt) -> entails X false phi (log s;; k) w ->
    entails X b (Cx Q_E phi psi) (log s;; k) w.
  Proof.
    intros * Hpsi Hphi; apply ticl_en; split; [exact Hphi |].
    exists k, (Obs (Log s) tt); split; [|exact Hpsi].
    unfold log, CTree.trigger; rewrite bind_vis.
    apply ktrans_vis; exists tt; split2; eauto with ticl.
    - now rewrite bind_ret_l.
    - now apply ticl_not_done in Hphi.
  Qed.
  Lemma eu_log {X S} {b : bool} : forall (s : S) (k : ctreeW S B X) w
      (phi : ticll (writerE S)) (psi : ticl_at (writerE S) X b),
    entails X b (Cu Q_E phi psi) k (Obs (Log s) tt) ->
    entails X false phi (log s;; k) w -> entails X b (Cu Q_E phi psi) (log s;; k) w.
  Proof. intros; cright; eapply en_log; eauto. Qed.
  Lemma ef_log {X S} {b : bool} : forall (s : S) (k : ctreeW S B X) w
      (psi : ticl_at (writerE S) X b),
    not_done w -> entails X b (Cu Q_E (CNow (fun _ => True)) psi) k (Obs (Log s) tt) ->
    entails X b (Cu Q_E (CNow (fun _ => True)) psi) (log s;; k) w.
  Proof. intros; apply eu_log; [assumption | apply ticl_now; auto]. Qed.
End LogLemmas.
