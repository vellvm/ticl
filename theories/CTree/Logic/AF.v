From Coq Require Import
  Basics
  Classes.Morphisms
  FunctionalExtensionality.

From Coinduction Require Import
  coinduction lattice.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.SBisim
  CTree.Equ
  CTree.Trans
  CTree.Logic.AX
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.Kripke.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
  
(*| CTL logic lemmas on c/itrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma done_af: forall (t: ctree E X) φ w,
      is_done w ->
      <( t, w |= AF now φ )> ->
      φ w.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra.
    - now rewrite ctl_now in H.
    - destruct H0 as ((? & ? & ?) & ?).
      exfalso.
      eapply done_not_ktrans with (t:=t); eauto.
  Qed.

  Lemma not_done_vis_af: forall (t: ctree E X) φ w,
      <( t, w |= AF vis φ )> ->
      not_done w.
  Proof.
    intros * Hf.
    next in Hf ; destruct Hf.
    - rewrite ctl_vis in H.
      destruct H as (? & ? & -> & ?).
      constructor.
    - destruct H.
      now apply can_step_not_done with t.
  Qed.

  Lemma not_done_pure_af: forall (t: ctree E X) w,
      <( t, w |= AF pure )> ->
      not_done w.
  Proof.
    intros * Hf.
    next in Hf ; destruct Hf.
    - rewrite ctl_pure in H.
      subst.
      constructor.
    - destruct H.
      now apply can_step_not_done with t.
  Qed.
  
  (* This lemma forces us to have finite branches.
     Alternatively, a classical φ would also allow
     us to work without induction on branch arity. *)
  Lemma af_brD_aux: forall n (k: fin' n -> ctree E X) w φ,
      (forall (i: fin' n), <( {k i}, w |= AF now φ )>) -> 
      φ w \/ (forall i, can_step (k i) w /\
                    (forall (t': ctree E X) w', [k i, w] ↦ [t', w'] ->
                                           <( t', w' |= AF now φ )>)).
  Proof.
    induction n; intros.
    - specialize (H Fin.F1).
      next in H; destruct H.
      + now left.
      + right.
        intro i.
        dependent destruction i; try solve [inv i].
        next in H.
        destruct H; intuition.
    - (* Need to construct [k, i] *)
      pose proof (H Fin.F1).
      edestruct IHn with (k:=fun (i: fin (S n)) => k (Fin.FS i)) (φ:=φ) (w:=w).
      + intro i.
        apply H.
      + now left.
      + next in H0; destruct H0.
        * now left.
        * right.
          intros.
          dependent destruction i.
          -- now next in H0; destruct H0.
          -- now apply H1.
  Qed.

  Lemma af_brD: forall n (k: fin' n -> ctree E X) w φ,      
      (forall (i: fin' n), <( {k i}, w |= AF φ )> \/ can_step (k i) w -> <( {k i}, w |= AF φ )>) ->
      <( {BrD n k}, w |= AF φ )>.
  Proof.
    induction n; intros.

(*    apply af_brD_aux in H.
    destruct H.
    + next; now left.
    + next; right.
      next; split. 
      * apply can_step_brD.
        exists (Fin.F1).
        now destruct (H Fin.F1).
      * intros.
        apply ktrans_brD in H0 as (i & TR).
        destruct (H i); eauto.
  Qed. *)
  Admitted.

  Lemma af_brD_inv: forall n (k: fin' n -> ctree E X) w φ,
      <( {BrD n k}, w |= AF now φ )> ->
      (forall (i: fin' n), can_step (k i) w ->
                      <( {k i}, w |= AF now φ )>).
  Proof.
    intros.
    next in H.
    destruct H; intros; subst.
    - now next; left.
    - next in H; destruct H.
      setoid_rewrite ktrans_brD in H1.
      rewrite pull2_iff in H1.
      next; right; next; split; auto.
      + intros t' w' TR.
        now eapply H1 with i.
  Qed.
  
  Lemma af_stuck: forall w φ,
      <( {Ctree.stuck: ctree E X}, w |= AF φ )> <->
      <( {Ctree.stuck: ctree E X}, w |= φ )>.
  Proof.
    split; intros.
    - cbn in H; dependent induction H; auto.
      destruct H0, H1.
      apply can_step_stuck in H1.
      contradiction.
    - now next; left.
  Qed.
  
  Lemma af_brS: forall n (k: fin' n -> ctree E X) w φ,
      <( {BrS n k}, w |= AF now φ )> <->
        (forall (i: fin' n), <( {k i}, w |= AF now φ )>).
  Proof.
    split; intros.
    - next in H; destruct H.
      + next; left.
        now rewrite ctl_now in *.
      + destruct H.
        apply H0.
        apply ktrans_brS.
        apply can_step_not_done in H.
        exists i; eauto.
    - destruct (not_done_dec w).
      + next; right.
        next; split; auto.
        * now apply can_step_brS.
        * intros t' w' TR'.
          apply ktrans_brS in TR' as (? & -> & -> & ?).
          apply H.
      + apply done_af with (φ:=φ) (t:= k Fin.F1) in i; auto.
        next; left.
        now apply ctl_now.
  Qed.
  
  Lemma af_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      (φ w \/ (not_done w /\ forall (x: encode e),
                 <( {k x}, {Obs e x} |= AF now φ )>)) ->
      <( {Vis e k}, w |= AF now φ )>.        
  Proof.
    intros.
    destruct H as [H | [Hd H]].
    - now next; left.
    - next; right; next; split.
      + now apply can_step_vis.
      + intros t' w' TR'.
        apply ktrans_vis in TR' as (? & -> & ? & ?).
        now rewrite <- H0.
  Qed.

  Lemma af_ret_inv: forall (x: X) w R,
      <( {Ret x}, w |= AF (AX done R) )> ->
      R x w.
  Proof.
    intros.
    next in H; destruct H.
    - destruct H.
      destruct H as (tstuck & w' & TR).
      specialize (H0 _ _ TR).
      inv TR; cbn in H0; now dependent destruction H0.
    - next in H; destruct H.
      destruct H as (tstuck & w' & TR).
      specialize (H0 _ _ TR).
      inv TR; observe_equ H1; rewrite <- Eqt, H3 in H0.
      + rewrite af_stuck in H0.
        apply ax_stuck in H0.
        rewrite ctl_done in H0.
        now dependent destruction H0.
      + rewrite af_stuck in H0.
        apply ax_stuck in H0.
        cbn in H0.
        now dependent destruction H0.
  Qed.

End BasicLemmas.

Section AfDoneIndLemma.
  Context {E: Type} {HE: Encode E} {X: Type}
    (φ: X -> World E -> Prop).

  (* t |= AF AX done R *)
  Inductive AFDoneInd: ctree E X -> World E -> Prop :=
  | AFDoneIndPure: forall t (x: X),
      observe t = RetF x ->
      φ x Pure ->
      AFDoneInd t Pure
  | AFDoneIndObs: forall t (e: E) (v: encode e) (x: X),
      observe t = RetF x ->
      φ x (Obs e v) ->
      AFDoneInd t (Obs e v)
  | AFDoneIndBrD: forall n t (k: fin' n -> _) w,
      observe t = BrF false n k ->
      (forall i, can_step (k i) w -> AFDoneInd (k i) w) ->
      AFDoneInd t w
  | AFDoneIndBrS: forall n t (k: fin' n -> _) w,
      observe t = BrF true n k ->
      (forall i, AFDoneInd (k i) w) ->
      AFDoneInd t w
  |AFDoneIndVis: forall (t: ctree E X) w e k (_: encode e),
      observe t = VisF e k ->
      not_done w ->
      (forall (v: encode e), AFDoneInd (k v) (Obs e v)) ->
      AFDoneInd t w.

  Global Instance proper_equ_afdoneind:
    Proper (equ eq ==> eq ==> iff) AFDoneInd.
  Proof.
    unfold Proper, respectful.
    intros; subst; split; intros Hind.
    - generalize dependent y.
      induction Hind; intros.
      + apply AFDoneIndPure with x; auto.
        rewrite <- H.
        unfold equ in H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + apply AFDoneIndObs with x; auto.
        rewrite <- H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + step in H2; cbn in H2; rewrite H in H2.
        dependent destruction H2.
        apply AFDoneIndBrD with n k2; eauto.
        intros i Hs.
        apply H1 with i, H2.
        fold_equ_in H2.
        now rewrite <- H2 in Hs.
      + unfold equ; step in H2; cbn in H2; rewrite H in H2.
        dependent destruction H2.
        eapply AFDoneIndBrS with n k2; auto.
        intro i.
        apply H1 with i, H2.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFDoneIndVis with e k2; eauto.
        intros v. apply H2, H3.
    - generalize dependent x.
      induction Hind; intros.
      + apply AFDoneIndPure with x; auto.
        rewrite <- H.
        unfold equ in H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + apply AFDoneIndObs with x; auto.
        rewrite <- H.
        step in H1; cbn in H1; dependent destruction H1;
          congruence.
      + step in H2; cbn in H2; rewrite H in H2.
        dependent destruction H2.
        apply AFDoneIndBrD with n k1; eauto.
        intros i Hs.
        apply H1 with i, H2.
        fold_equ_in H2.
        now rewrite H2 in Hs.
      + unfold equ; step in H2; cbn in H2; rewrite H in H2.
        dependent destruction H2.
        eapply AFDoneIndBrS with n k1; auto.
        intro i.
        apply H1 with i, H2.
      + unfold equ; step in H3; cbn in H3; rewrite H in H3.
        dependent destruction H3.
        eapply AFDoneIndVis with e k1; eauto.
        intros v. apply H2, H3.
  Qed.
  
  Lemma reorder_forall{A B C} P: 
    (forall (a: A) (b : B) (c : C),
      P a b c) <->
    (forall c a b, P a b c).
  Proof.
    intros; split; eauto.
  Qed.
  
  Lemma afdone_ind {HP: Productive E}: forall (t: ctree E X) w,
      <( t, w |= AF AX done φ )> ->
      AFDoneInd t w.
  Proof.
    intros; induction H.
    - (* Match *)
      apply axdone_ind in H; auto.
      rewrite ctree_eta.
      remember (observe t) as T.
      clear HeqT t.
      induction H.
      + apply AFDoneIndPure with x; auto.
      + apply AFDoneIndObs with x; auto.
      + apply AFDoneIndBrD with n k; auto.
        intros i Hs.
        rewrite ctree_eta.
        apply H0.
    - (* Step *)      
      destruct H0, H1.
      clear H H1.
      cbn in H2, H3.
      rewrite ctree_eta in H0.
      rewrite ctree_eta.
      desobs t; [| destruct b |].
      + destruct H0 as (t' & w' & TR).
        specialize (H2 _ _ TR).
        specialize (H3 _ _ TR).
        inv TR; observe_equ H0;
          rewrite <- Eqt, H4 in H2.
        * pose proof (af_stuck (Done x) (X:=X) <( AX done φ )>) as Hstuck.          
          unfold entailsF in Hstuck.
          rewrite Hstuck in H2.
          inv H2; now apply can_step_stuck in H.
        * pose proof (af_stuck (Finish e v x) (X:=X) <( AX done φ )>) as Hstuck.          
          unfold entailsF in Hstuck.
          rewrite Hstuck in H2.
          inv H2; now apply can_step_stuck in H.
      + apply AFDoneIndBrS with n k; auto.
        intros i.
        apply H3; apply ktrans_brS.
        exists i; intuition.
        apply can_step_not_done with (BrS n k);
          auto with ctl.
      + (* BrD *)
        clear Heqt t.
        apply can_step_brD in H0.
        setoid_rewrite ktrans_brD in H2.
        setoid_rewrite ktrans_brD in H3.
        rewrite pull2_iff in H2, H3.
        apply AFDoneIndBrD with n k; auto.
        admit.
      + apply AFDoneIndVis with e k; auto.
        apply can_step_not_done with (Vis e k);
          auto with ctl.
        intro v.
        apply H3; apply ktrans_vis.
        exists v; intuition.
        apply can_step_not_done with (Vis e k); auto.
  Admitted.

End AfDoneIndLemma.

Section CtlAfBind.
  Context {E: Type} {HE: Encode E}.
  
  Opaque Ctree.stuck.
  Typeclasses Transparent equ.
  Theorem af_bind_pure{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      <( t, w |= AF pure )> ->
      <( {x <- t ;; k x}, w |= AF pure )>.
  Proof.
    intros * Haf.
    revert X k.
    induction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn.
      now apply ctl_pure in H. 
    - (* StepA *)
      destruct H0, H1; clear H H0.      
      next; right; next; split.
      + (* can_step *)
        destruct H1 as (t' & w' & TR').
        eapply can_step_bind_l with t' w'; auto.
        eapply not_done_pure_af with (t:=t').
        now apply H2.
      + (* AX AF *)
        intros t_ w_ TR_.
        apply ktrans_bind_inv in TR_.
        destruct TR_ as [(t' & TR' & Hd & ->) | (x & w' & TR' & Hr & TRk)].
        * now apply H3.
        * specialize (H2 _ _ TR').
          inv H2.
          apply ctl_pure in H; subst.
          -- inv Hr.
          -- destruct H0.
             now apply can_step_stuck in H0.
  Qed.
  
  Theorem af_bind_vis{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
      <( t, w |= AF vis φ )> ->
      <( {x <- t ;; k x}, w |= AF vis φ )>.
  Proof.
    intros * Haf.
    revert X k.
    induction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn.
      apply ctl_vis in H as (e_ & x_ & ? & ?).
      subst.
      now (exists e_, x_).
    - (* StepA *)
      destruct H0, H1; clear H H0.      
      next; right; next; split.
      + (* can_step *)
        destruct H1 as (t' & w' & TR').
        eapply can_step_bind_l with t' w'; auto.
        eapply not_done_vis_af with (t:=t').
        now apply H2.
      + (* AX AF *)
        intros t_ w_ TR_.
        apply ktrans_bind_inv in TR_ as
            [(t' & TR' & Hd & ->) |
              (x & w' & TR' & Hr & TRk)].
        * now apply H3.
        * specialize (H2 _ _ TR').
          inv H2.
          apply ctl_vis in H as (? & ? & -> & ?).
          -- inv Hr.
          -- destruct H0.
             now apply can_step_stuck in H0.
  Qed.

  Theorem af_bind_r{X Y} {HP: Productive E}: forall (t: ctree E Y)
                            (k: Y -> ctree E X) w φ R,
      <( t, w |= AF AX done R )> ->
      (forall (y: Y) w, R y w -> not_done w ->
                   <( {k y}, w |= AF now φ )>) ->
      <( {x <- t ;; k x}, w |= AF now φ )>.
  Proof.
    intros * Haf Hk.
    induction Haf; intros; subst.
    - (* MatchA *)      
      apply axdone_ind in H; auto.
      rewrite (ctree_eta t) in *.
      remember (observe t) as T.
      clear HeqT t.
      induction H. 
      + rewrite bind_ret_l; eauto with ctl.
      + rewrite bind_ret_l; eauto with ctl.
      + rewrite bind_br.
        apply af_brD; intros.
        setoid_rewrite <- ctree_eta in H0.
        apply H0.
    - (* StepA *)
      destruct H0, H1; clear H H0.      
      rewrite (ctree_eta t) in *.
      cbn in H2, H3.
      desobs t; [| destruct b |].
      + destruct H1 as (t' & w' & TR).
        specialize (H2 _ _ TR).
        specialize (H3 _ _ TR).
        inv TR; observe_equ H0;
          rewrite <- Eqt, H4 in H2.
        * pose proof (af_stuck (Done x) (X:=Y) <( AX done R )>) as Hstuck.          
          unfold entailsF in Hstuck.
          apply Hstuck in H2.
          inv H2; now apply can_step_stuck in H.
        * pose proof (af_stuck (Finish e v x) (X:=Y) <( AX done R )>) as Hstuck.          
          unfold entailsF in Hstuck.
          rewrite Hstuck in H2.
          inv H2; now apply can_step_stuck in H.
      + rewrite bind_br.
        apply af_brS.
        intro i.
        apply H3.
        apply ktrans_brS.
        exists i; intuition.
        destruct H1 as (t' & w' & TR).
        now apply ktrans_not_done with (BrS n k0) t' w'.
      + (* BrD *)
        rewrite bind_br.
        apply can_step_brD in H1.
        setoid_rewrite ktrans_brD in H3.
        setoid_rewrite ktrans_brD in H2.
        rewrite pull2_iff in H2, H3.
        clear Heqt t.        
        apply af_brD.
        intros i Hs.
        apply can_step_bind in Hs as [(t' & w' & TR & Hd) | (? & ? & ? & ?)].
        * next; right. next; split.
          -- now apply can_step_bind_l with t' w'.
          -- intros t_ w_ TR_.
             apply ktrans_bind_inv in TR_ as 
                 [(t1 & TR1 & Hd_ & ->) |
                   (x & w1 & TR1 & Hr & TRk)].
             ++ now apply H3 with i.
             ++ specialize (H2 _ _ _ TR1).
                apply (af_stuck (X:=Y) w1 (<( AX done R )>)) in H2.
                apply ax_stuck in H2.                
                inv H2; dependent destruction Hr.
                ** specialize (H3 _ _ _ TR1).
                   inv H3.
                apply Hst in H2.
             apply H3.
        apply can_step_brD in H1.
        setoid_rewrite ktrans_brD in H3.
        setoid_rewrite ktrans_brD in H2.
        rewrite pull2_iff in H2, H3.

        
        admit.
      + rewrite bind_vis.
        apply af_vis.
        apply HP.
        right; split.
        now apply can_step_not_done with (Vis e k0).
        intro x.
        apply H3.
        apply ktrans_vis.
        exists x; intuition.
        now apply can_step_not_done with (Vis e k0).
  Admitted.
  Qed. 
End CtlAfBind.

Section CtlAfIter.
  Context {E: Type} {HE: Encode E}.

  (* Total correctness lemma for [iter] *)
  (* [Ri: I -> World E -> Prop] loop invariant (left).
     [Rr: X -> World E -> Prop] loop postcondition (right).
     [Rv: (I * World E) -> (I * World E) -> Prop)] loop variant (left). *)
  Lemma af_iter{X I} Ri Rr (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E (I + X)):
      (forall (i: I) w, Ri i w ->
                   <( {k i}, w |= AF AX done {fun (x: I + X) w' =>
                                                match x with
                                                | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                                                | inr r' => Rr r' w'
                                                end})>) ->
      well_founded Rv ->
      Ri i w ->
      <( {Ctree.iter k i}, w |= AF done Rr )>.
  Proof.      
    intros H WfR Hi.
    generalize dependent k.
    revert Hi.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    Opaque entailsF.
    induction P using (well_founded_induction WfR); (* wf_ind *)
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    rewrite unfold_iter.
    eapply af_bind_r
      with (R:=fun (x : I + X) (w' : World E) =>
                 match x with
                 | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                 | inr r' => Rr r' w'
                 end); auto.
    intros [i' | r] w'.
    - intros (Hi' & Hv) Hd.
      apply af_brD.
      intros _.
      remember (i', w') as y.
      replace i' with (fst y) by now subst.
      replace w' with (snd y) by now subst.      
      apply HindWf; inv Heqy; auto.
    - intros Hr Hd.
      next; right; next; split.
      + now apply can_step_ret.
      + intros t_ w_ TR_.
        inv Hd.
        * apply ktrans_done in TR_ as (-> & ->).
          next; left.
          rewrite ctl_done.
          now constructor.
        * apply ktrans_finish in TR_ as (-> & ->).
          next; left.
          rewrite ctl_done.
          now constructor.          
  Qed.
End CtlAfIter.
