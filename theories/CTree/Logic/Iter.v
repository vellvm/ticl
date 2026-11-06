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
  CTree.Logic.Bind
  CTree.Logic.Ret
  Logic.Core.

From Stdlib Require Import Arith.Wf_nat.

Generalizable All Variables.

Import CTreeNotations TiclNotations CoindNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** * TICL logic iteration lemmas for ctrees and different Ticl operators.*)
(** This section introduces the structural loop lemmas for the iteration of ctrees. 
    Those are the main structural lemmas and the big contribution of this work.
    Examples of the lemmas are: a termination lemma, a loop invariant lemma, a loop invariant lemma with a well-founded relation,
    a loop invariant lemma with a well-founded relation and a post-condition etc.

    The lemmas in this section internalize complex inductive and coinductive proof techniques to simple lemma application.

    The [ret]-premised lemmas require the loop body to return a single value at
    each leaf; immediate exits establish the suffix postcondition at that leaf.
*)
Section IterLemmas.
  Context {E B: Type -> Type}.


  (** Actual-run cutpoints: finite body segments either establish the target or
      reach a bisimilar family member at a strictly smaller configuration. *)
  Lemma au_family_wf {X I b} (T Body: I -> ctree E B X)
    (Inv: I -> World E -> Prop) (Rv: relation (I * World E))
    (phi: ticll E) (psi: ticl_at E X b) :
    (forall i, T i ~ Body i) -> well_founded Rv ->
    (forall i w, Inv i w ->
      auc (entails X false phi)
        (fun t z => entails X b psi t z \/
          exists j, Inv j z /\ Rv (j,z) (i,w) /\ t ~ T j)
        (Body i) w) ->
    forall i w, Inv i w -> entails X b (Cu Q_A phi psi) (T i) w.
  Proof.
    intros Hshape WfR Hbody i w.
    remember (i,w) as iw eqn:Heq.
    revert i w Heq.
    induction iw as [[s z] IH] using (well_founded_induction WfR).
    intros i w Heq Hinv; inversion Heq; subst i w.
    rewrite (Hshape s); apply ticl_au; apply auc_join.
    eapply auc_mono_r; [|exact (Hbody s z Hinv)].
    intros t w [Hpsi | (j & Hj & Hv & Ht)].
    - now apply MatchA.
    - pose proof (IH (j,w) Hv j w eq_refl Hj) as Hnext.
      rewrite <- Ht in Hnext; now apply ticl_au in Hnext.
  Qed.

  Lemma eu_family_wf {X I b} (T Body: I -> ctree E B X)
    (Inv: I -> World E -> Prop) (Rv: relation (I * World E))
    (phi: ticll E) (psi: ticl_at E X b) :
    (forall i, T i ~ Body i) -> well_founded Rv ->
    (forall i w, Inv i w ->
      euc (entails X false phi)
        (fun t z => entails X b psi t z \/
          exists j, Inv j z /\ Rv (j,z) (i,w) /\ t ~ T j)
        (Body i) w) ->
    forall i w, Inv i w -> entails X b (Cu Q_E phi psi) (T i) w.
  Proof.
    intros Hshape WfR Hbody i w.
    remember (i,w) as iw eqn:Heq.
    revert i w Heq.
    induction iw as [[s z] IH] using (well_founded_induction WfR).
    intros i w Heq Hinv; inversion Heq; subst i w.
    rewrite (Hshape s); apply ticl_eu; apply euc_join.
    eapply euc_mono_r; [|exact (Hbody s z Hinv)].
    intros t w [Hpsi | (j & Hj & Hv & Ht)].
    - now apply MatchE.
    - pose proof (IH (j,w) Hv j w eq_refl Hj) as Hnext.
      rewrite <- Ht in Hnext; now apply ticl_eu in Hnext.
  Qed.

  (** Finite until is closed at every stage of the global final chain. These
      local tower facts let cutpoint rules use finite bodies during coinduction. *)
  Local Lemma auc_family_chain {X} (P: ctree E B X -> World E -> Prop)
    {R: Chain (agcF P)} :
    forall t w, auc P (`R) t w -> `R t w.
  Proof.
    apply tower.
    - intros ? INC t w Hau ? ?.
      apply INC; auto.
      eapply auc_mono_r; [|exact Hau].
      intros u z Hu; apply leq_infx in H; now apply H.
    - intros R' IH t w Hau.
      destruct Hau as [t w HR | t w Hstep]; [exact HR |].
      eapply anc_mono_r; [|exact Hstep].
      intros u z Hu; apply IH.
      eapply auc_mono_r; [|exact Hu].
      intros v y Hv; now apply (b_chain R').
  Qed.

  Local Lemma euc_family_chain {X} (P: ctree E B X -> World E -> Prop)
    {R: Chain (egcF P)} :
    forall t w, euc P (`R) t w -> `R t w.
  Proof.
    apply tower.
    - intros ? INC t w Heu ? ?.
      apply INC; auto.
      eapply euc_mono_r; [|exact Heu].
      intros u z Hu; apply leq_infx in H; now apply H.
    - intros R' IH t w Heu.
      destruct Heu as [t w HR | t w Hstep]; [exact HR |].
      eapply enc_mono_r; [|exact Hstep].
      intros u z Hu; apply IH.
      eapply euc_mono_r; [|exact Hu].
      intros v y Hv; now apply (b_chain R').
  Qed.

  (** The leading next judgment requires actual progress before another loop
      cutpoint; a silent guard-only or fork-only cycle is not sufficient. *)
  Lemma ag_family {X I} (T Body: I -> ctree E B X)
    (Inv: I -> World E -> Prop) (phi: ticll E) :
    (forall i, T i ~ Body i) ->
    (forall i w, Inv i w ->
      anc (entails X false phi)
        (auc (entails X false phi)
          (fun t z => (exists j, Inv j z /\ t ~ T j) \/
            agc (entails X false phi) t z)) (Body i) w) ->
    forall i w, Inv i w -> entails X false (Cg Q_A phi) (T i) w.
  Proof.
    intros Hshape Hbody.
    setoid_rewrite unfold_entails_ag.
    pattern (agc (entails (M:=ctree) (B:=B) X false phi)); apply gfp_prop; intro R.
    apply_ptower R O; intros CIH i w Hinv.
    rewrite (Hshape i).
    eapply anc_mono_r; [|exact (Hbody i w Hinv)].
    intros t z Hcut; eapply auc_family_chain.
    eapply auc_mono_r; [|exact Hcut].
    intros u y [(j & Hj & Ht) | HG].
    - rewrite Ht; now apply CIH.
    - apply (gfp_chain R); exact HG.
  Qed.

  Lemma eg_family {X I} (T Body: I -> ctree E B X)
    (Inv: I -> World E -> Prop) (phi: ticll E) :
    (forall i, T i ~ Body i) ->
    (forall i w, Inv i w ->
      enc (entails X false phi)
        (euc (entails X false phi)
          (fun t z => (exists j, Inv j z /\ t ~ T j) \/
            egc (entails X false phi) t z)) (Body i) w) ->
    forall i w, Inv i w -> entails X false (Cg Q_E phi) (T i) w.
  Proof.
    intros Hshape Hbody.
    setoid_rewrite unfold_entails_eg.
    pattern (egc (entails (M:=ctree) (B:=B) X false phi)); apply gfp_prop; intro R.
    apply_ptower R O; intros CIH i w Hinv.
    rewrite (Hshape i).
    eapply enc_mono_r; [|exact (Hbody i w Hinv)].
    intros t z Hcut; eapply euc_family_chain.
    eapply euc_mono_r; [|exact Hcut].
    intros u y [(j & Hj & Ht) | HG].
    - rewrite Ht; now apply CIH.
    - apply (gfp_chain R); exact HG.
  Qed.
  (** Continuation-parametric rules let different decreasing body leaves
      converge to one native result without requiring one immediate return. *)
  Lemma ret_iter_wf {X I}
    (Ri: I -> World E -> Prop) (Rv: relation (I * World E))
    (body: I -> ctree E B (I + X)) (P: X -> World E -> Prop) :
    well_founded Rv ->
    (forall i w, Ri i w -> forall cont: I -> ctree E B X,
      (forall j z, Ri j z -> Rv (j,z) (i,w) ->
        entails X true (CRet P) (cont j) z) ->
      entails X true (CRet P)
        (body i >>= fun lr => match lr with
          | inl j => Guard (cont j) | inr x => Ret x end) w) ->
    forall i w, Ri i w -> entails X true (CRet P) (CTree.iter body i) w.
  Proof.
    intros WfR Hbody i w.
    remember (i,w) as iw eqn:Heq; revert i w Heq.
    induction iw as [[s z] IH] using (well_founded_induction WfR).
    intros i w Heq Hinv; inversion Heq; subst i w.
    rewrite unfold_iter; apply Hbody; [exact Hinv |].
    intros j y Hj Hv; exact (IH (j,y) Hv j y eq_refl Hj).
  Qed.

  (** Visible iteration retains the real [Step] at every continuing leaf;
      both path quantifiers and both endpoint modes share this rule. *)
  Lemma u_iterS_wf {X I b} (q: ticlq)
    (Ri: I -> World E -> Prop) (Rv: relation (I * World E))
    (body: I -> ctree E B (I + X))
    (phi: ticll E) (psi: ticl_at E X b) :
    well_founded Rv ->
    (forall i w, Ri i w -> forall cont: I -> ctree E B X,
      (forall j z, Ri j z -> Rv (j,z) (i,w) ->
        entails X b (Cu q phi psi) (cont j) z) ->
      entails X b (Cu q phi psi)
        (body i >>= fun lr => match lr with
          | inl j => Step (cont j) | inr x => Ret x end) w) ->
    forall i w, Ri i w -> entails X b (Cu q phi psi) (CTree.iterS body i) w.
  Proof.
    intros WfR Hbody i w.
    remember (i,w) as iw eqn:Heq; revert i w Heq.
    induction iw as [[s z] IH] using (well_founded_induction WfR).
    intros i w Heq Hinv; inversion Heq; subst i w.
    assert (Hunf: CTree.iterS body s ≅
      (body s >>= fun lr => match lr with
        | inl j => Step (CTree.iterS body j) | inr x => Ret x end)) by (now step).
    rewrite Hunf; apply Hbody; [exact Hinv |].
    intros j y Hj Hv; exact (IH (j,y) Hv j y eq_refl Hj).
  Qed.

  (** ** Prefix iteration for either next quantifier *)
  (** The body either already satisfies the next formula or returns an [inl]
      state along a finite decreasing chain in the well-founded relation [Rv]. *)
  Lemma n_iter_prefix {X I} (q: ticlq) Ri (Rv: relation I) (i: I) w
    (k: I -> ctree E B (I + X)) (phi psi: ticll E):
    well_founded Rv ->
    Ri i w ->
    (forall (i: I) w,
        Ri i w ->
        entails (I + X) false (Cx q phi psi) (k i) w \/
        entails (I + X) true
          (CRet (fun lr w' => exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i))
          (k i) w) ->
    entails X false (Cx q phi psi) (iter k i) w.
  Proof.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (H _ _ Hi) as [Hnext | Hret].
    - now eapply ticll_bind_l.
    - eapply (ticl_bind_ret (b:=false)) with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ Ri i' w' /\ Rv i' i).
      + exact Hret.
      + intros lr w' (j & -> & Hi' & Hv).
        rewrite sb_guard.
        apply HindWf; auto with ticl.
  Qed.

  (** One unfolding of an until proof whose body returns a continuing state. *)
  Lemma u_iter_next{X I b} (q: ticlq) R (i: I) w
      (k: I -> ctree E B (I + X)) (phi: ticll E) (psi: ticl_at E X b):
    entails (I + X) true
      (Cu q phi (CRet (fun lr w => exists i', lr = inl i' /\ R i' w))) (k i) w ->
    (forall i w, R i w -> entails X b (Cu q phi psi) (iter k i) w) ->
    entails X b (Cu q phi psi) (iter k i) w.
  Proof.
    unfold iter, MonadIter_ctree.
    intros Hbody Hnext.
    rewrite unfold_iter.
    eapply (u_bind_r (b:=b) q) with
      (R:=fun lr w => exists i', lr = inl i' /\ R i' w).
    - exact Hbody.
    - intros ? ? (i' & -> & HR).
      rewrite sb_guard; now apply Hnext.
  Qed.

  (** Split liveness between an established region and a decreasing continuation. *)
  Lemma u_iter_split{X I b} (q: ticlq) R Ri
      (Rv: relation (I * World E)) (i: I) w
      (k: I -> ctree E B (I + X)) (phi: ticll E) (psi: ticl_at E X b):
    well_founded Rv ->
    not_done w ->
    R i w ->
    (forall i w, not_done w -> Ri i w ->
      entails X b (Cu q phi psi) (iter k i) w) ->
    (forall i w, not_done w -> R i w ->
      entails (I + X) true
        (Cu q phi (CRet (fun lr w' => exists i', lr = inl i' /\
          not_done w' /\ Ri i' w'))) (k i) w \/
      entails (I + X) true
        (Cu q phi (CRet (fun lr w' => exists i', lr = inl i' /\
          not_done w' /\ R i' w' /\ Rv (i', w') (i, w)))) (k i) w) ->
    entails X b (Cu q phi psi) (iter k i) w.
  Proof.
    intros WfR.
    revert i w.
    intros i w.
    remember (i, w) as iw eqn:Heq.
    revert i w Heq.
    induction iw as [[s z] IH] using (well_founded_induction WfR).
    intros i w Heq Hd HR Hregion Hbody.
    inversion Heq; subst i w.
    destruct (Hbody s z Hd HR) as [Htransfer | Hrecur].
    - eapply (u_iter_next (b:=b) q) with (R:=fun i w => not_done w /\ Ri i w).
      + exact Htransfer.
      + intros j w' [Hd' Hj]; now apply Hregion.
    - eapply (u_iter_next (b:=b) q) with
        (R:=fun j w' => not_done w' /\ R j w' /\ Rv (j, w') (s, z)).
      + exact Hrecur.
      + intros j w' (Hd' & Hj & Hv).
        eapply (IH (j, w') Hv j w' eq_refl); eauto.
  Qed.
      
  (** ** Direct-body prefix iteration for either until quantifier *)
  (** The body either already satisfies the prefix until formula, without having
      to return, or returns an [inl] state preserving the invariant and decreasing
      the well-founded rank. This is distinct from return-driven iteration. *)
  Lemma u_iter_prefix {X I} (q: ticlq) R (Rv: relation (I * World E))
    (i: I) w (k: I -> ctree E B (I + X)) (phi psi: ticll E):
    well_founded Rv ->
    not_done w ->
    R i w ->
    (forall (i: I) w,
        not_done w ->
        R i w ->
        entails (I + X) false (Cu q phi psi) (k i) w \/
        entails (I + X) true
          (Cu q phi (CRet (fun lr w' =>
            exists i', lr = inl i' /\ not_done w' /\ R i' w' /\
              Rv (i', w') (i, w)))) (k i) w) ->
    entails X false (Cu q phi psi) (iter k i) w.
  Proof.
    intros WfR.
    revert i w.
    intros i w.
    remember (i, w) as iw eqn:Heq.
    revert i w Heq.
    induction iw as [[s z] IH] using (well_founded_induction WfR).
    intros i w Heq Hd Hi Hbody.
    inversion Heq; subst i w.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (Hbody s z Hd Hi) as [Hprefix | Hret].
    - now eapply ticll_bind_l.
    - eapply (u_bind_r (b:=false) q) with
        (R:=fun lr w' =>
          exists j, lr = inl j /\ not_done w' /\ R j w' /\
            Rv (j, w') (s, z)).
      + exact Hret.
      + intros lr w' (j & -> & Hd' & Hj & Hv).
        rewrite sb_guard.
        eapply (IH (j, w') Hv j w' eq_refl); eauto.
  Qed.

  (** Natural-number ranks instantiate the same direct-body prefix algorithm. *)
  Lemma u_iter_prefix_nat {X I} (q: ticlq) Ri (f: I -> World E -> nat)
    (i: I) w (k: I -> ctree E B (I + X)) (phi psi: ticll E):
    not_done w ->
    Ri i w ->
    (forall (i: I) w,
        not_done w ->
        Ri i w ->
        entails (I + X) false (Cu q phi psi) (k i) w \/
        entails (I + X) true
          (Cu q phi (CRet (fun lr w' =>
            exists i', lr = inl i' /\ not_done w' /\ Ri i' w' /\
              f i' w' < f i w))) (k i) w) ->
    entails X false (Cu q phi psi) (iter k i) w.
  Proof.
    intros.
    eapply (u_iter_prefix q Ri (ltof _ (fun '(i, w) => f i w))); auto.
    apply well_founded_ltof.
  Qed.

  (** Return-driven iteration: continuing returns decrease the rank, while exiting
      returns establish the indexed target at the output tree's result type. *)
  Lemma u_iter{X I b} (q: ticlq) Inv (Rv: relation (I * World E))
      (i: I) w (k: I -> ctree E B (I + X))
      (phi: ticll E) (psi: ticl_at E X b):
    well_founded Rv ->
    Inv i w ->
    (forall s w, Inv s w ->
      entails (I + X) true
        (Cu q phi (CRet (fun lr w' =>
          match lr with
          | inl s' => Inv s' w' /\ Rv (s', w') (s, w)
          | inr r => entails X b psi (Ret r : ctree E B X) w'
          end))) (k s) w) ->
    entails X b (Cu q phi psi) (iter k i) w.
  Proof.
    intros WfR.
    revert i w.
    intros i w.
    remember (i, w) as iw eqn:Heq.
    revert i w Heq.
    induction iw as [[s z] IH] using (well_founded_induction WfR).
    intros i w Heq Hinv Hbody.
    inversion Heq; subst i w.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    eapply (u_bind_r (b:=b) q) with
      (R:=fun lr w' =>
        match lr with
        | inl s' => Inv s' w' /\ Rv (s', w') (s, z)
        | inr r => entails X b psi (Ret r : ctree E B X) w'
        end).
    - now apply Hbody.
    - intros [s' | r] w' Hret.
      + destruct Hret as [Hinv' Hv].
        rewrite sb_guard.
        eapply (IH (s', w') Hv s' w' eq_refl); eauto.
      + destruct q; cleft; exact Hret.
  Qed.

  (** Natural-valued ranks for the return-driven algorithm. *)
  Lemma u_iter_nat{X I b} (q: ticlq) Inv (f: I -> World E -> nat)
      (i: I) w (k: I -> ctree E B (I + X))
      (phi: ticll E) (psi: ticl_at E X b):
    Inv i w ->
    (forall s w, Inv s w ->
      entails (I + X) true
        (Cu q phi (CRet (fun lr w' =>
          match lr with
          | inl s' => Inv s' w' /\ f s' w' < f s w
          | inr r => entails X b psi (Ret r : ctree E B X) w'
          end))) (k s) w) ->
    entails X b (Cu q phi psi) (iter k i) w.
  Proof.
    intros Hinv Hbody.
    eapply (u_iter (b:=b) q Inv (ltof _ (fun '(s, w) => f s w))).
    - apply well_founded_ltof.
    - exact Hinv.
    - exact Hbody.
  Qed.
  
  
  (** ** Iteration lemmas for the coinductive [AG] operator *)

  (** A loop [iter k i] satisfies [AG φ] if [k i] always terminates with loop invariant [R],
      while the return value of the iteration is always the left-injection [lr = inl i'].
      This lemma internalizes powerful coinductive proof techniques to simple lemma application. *)
  Lemma ag_iter{X I} (R: rel I (World E)) (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E):
    R i w ->
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |=L φ)> /\
          <( {k i}, w |=R AX (φ AU ret
                      {fun (lr: I + X) (w': World E) =>
                         exists (i': I), lr = inl i' /\ R i' w'}) )>) ->
    <( {iter k i}, w |=L AG φ )>.
  Proof.
    intros HR H.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    unfold iter, MonadIter_ctree.
    coinduction RR CIH; intros.
    specialize (H _ _ HR) as (Hφ & H').
    cdestruct H'.
    split2.
    - apply Hφ. 
    - destruct Hs as (k' & wk & TR).
      rewrite unfold_iter.
      apply can_step_bind_l with k' wk; auto with ticl.
      specialize (H' _ _ TR).
      now apply ticl_not_done in H'.
    - intros t' w' TR.
      rewrite unfold_iter in TR.
      apply ktrans_bind_inv in TR as
          [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ag_bind_chain φ
                 (fun (lr: I+X) (w0: World E) => exists i' : I, lr = inl i' /\ R i' w0)).
        * now apply H'. 
        * intros [l | r] w_ (? & Hinv & HR'); inv Hinv.
          rewrite sb_guard. 
          apply CIH; auto with ticl.
      + (* [k x] returns *)        
        specialize (H' _ _ TRt0) as HAN.
        apply (au_stuck (b:=true)) in HAN; cdestruct HAN; exfalso; eapply can_step_stuck; eauto.
  Qed.

  (** A loop [iter k i] satisfies [EG φ] if [k i] always terminates with loop invariant [R],
      while the return value of the iteration is always the left-injection [lr = inl i'].
      This lemma internalizes powerful coinductive proof techniques to simple lemma application. *)
  Lemma eg_iter{X I} R (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E):
    R i w ->    
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |=L φ)> /\
        <( {k i}, w |=R EX (φ EU ret
                    {fun (lr: I + X) (w': World E) =>
                       exists (i': I), lr = inl i' /\ R i' w'}) )>) ->
    <( {iter k i}, w |=L EG φ )>.
  Proof.
    intros.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    unfold iter, MonadIter_ctree.
    coinduction RR CIH; intros.
    specialize (H0 _ _ H) as (Hφ & H0').
    cdestruct H0'.
    split.
    - apply Hφ. 
    - exists (lr <- t;; match lr with
                 | inl l => Guard (CTree.iter k l)
                 | inr r => Ret r
                  end), w0; split.
      + rewrite unfold_iter.
        apply ktrans_bind_l; auto with ticl.
        now apply ticl_not_done in H0'.
      + apply (eg_bind_chain φ
                 (fun (lr: I+X) (w0: World E) => exists i' : I, lr = inl i' /\ R i' w0)).
        * now apply H0'. 
        * intros [l | r] w_ (? & Hinv & HR); inv Hinv.          
          rewrite sb_guard.
          apply CIH; auto with ticl.
  Qed.

End IterLemmas.
