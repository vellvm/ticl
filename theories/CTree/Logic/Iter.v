From Coinduction Require Import
  coinduction lattice tactics.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Eq.Bind
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.Bind
  CTree.Logic.Ret
  Logic.Ctl.

From Coq Require Import Arith.Wf_nat.

Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

Section IterLemmas.
  Context {E: Type} {HE: Encode E}.

  (* AX *)
  Lemma axl_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E (I + X)) (φ ψ: ctll E):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= φ AX ψ )> \/
          <[ {k i}, w |= φ AX done
                      {fun (lr: I + X) (w': World E) => 
                         exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i}]>) ->
    <( {iter k i}, w |= φ AX ψ )>.
  Proof with auto with ctl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (H _ _ Hi).
    - now eapply ctll_bind_l.
    - eapply axl_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ Ri i' w' /\ Rv i' i)... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Lemma axr_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E (I + X)) (φ: ctll E) (ψ: ctlr E X):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ AX done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => Ri i' w' /\ Rv i' i
                       | inr r => <[ {Ret r}, w' |= φ AX ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AX ψ ]>.
  Proof with auto with ctl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (H _ _ Hi).
    - eapply axr_bind_r with
        (R:=(fun (lr : I + X) (w' : World E) =>
               match lr with
               | inl i' => Ri i' w' /\ Rv i' i
               | inr r => <[ {Ret r}, w' |= φ AX ψ ]>
               end))...
      intros [i' | r] w'...
      intros (Hi' & Hv). 
      rewrite sb_guard.
      apply HindWf...
  Qed.

  (* EX *)
  Typeclasses Transparent sbisim.
  Lemma exl_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E (I + X)) (φ ψ: ctll E):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= φ EX ψ )> \/
          <[ {k i}, w |= φ EX done {fun (lr: I + X) w' =>
            exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i} ]>) ->
    <( {iter k i}, w |= φ EX ψ )>.
  Proof with auto with ctl.    
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    cbn in *.
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (H _ _ Hi).
    - now eapply ctll_bind_l.
    - apply ex_done in H0 as (Hφ & [l | r] & Heqt & i' & Hinv & HRi & HRv); inv Hinv.
      rewrite Heqt, bind_ret_l, sb_guard.
      apply HindWf...
  Qed.

  Lemma exr_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E (I + X))
    (φ: ctll E) (ψ: ctlr E X):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ EX done {fun (lr: I + X) w' =>
                                    match lr with
                                    | inl i' => Ri i' w' /\ Rv i' i
                                    | inr r => <[ {Ret r}, w' |= φ EX ψ ]>
                                    end}]>) ->
    <[ {iter k i}, w |= φ EX ψ ]>.
  Proof with auto with ctl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    cbn in *.
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.    
    pose proof (H _ _ Hi) as H'.
    apply ex_done in H' as (Hφ & [l | r] & Heqt & Hi'). 
    - destruct Hi' as (HRi & HRv).
      rewrite Heqt, bind_ret_l, sb_guard.
      apply HindWf...
    - cdestruct Hi'.
      rewrite Heqt in Hφ |- *.
      rewrite bind_ret_l.
      csplit...
      exists t, w0...
  Qed.  

  (* AU *)
  Lemma aul_iter{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E (I + X)) (φ ψ: ctll E):
    well_founded Rv ->
    not_done w ->
    Ri i w ->    
    (forall (i: I) w,
        not_done w ->
        Ri i w ->
        <( {k i}, w |= φ AU ψ )> \/
          <[ {k i}, w |= φ AU AN done
                      {fun (lr: I + X) (w': World E) =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' w'
                               /\ Rv (i', w') (i, w)}]>) ->
    <( {iter k i}, w |= φ AU ψ )>.
  Proof with auto with ctl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hd Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    destruct (H _ _ Hd Hi).
    - rewrite unfold_iter.
      apply ctll_bind_l... 
    - rewrite unfold_iter.
      eapply aul_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ not_done w'/\ Ri i' w' /\ Rv (i', w') (i, w))... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, w') as y.
        replace j with (fst y) in Hi' |- * by now subst.
        replace w' with (snd y) in Hd', Hi' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Lemma aul_iter_nat{X I} Ri (f: I -> World E -> nat) (i: I) w (k: I -> ctree E (I + X))
    (φ ψ: ctll E):
    not_done w ->
    Ri i w ->    
    (forall (i: I) w,
        not_done w ->
        Ri i w ->
        <( {k i}, w |= φ AU ψ )> \/
          <[ {k i}, w |= φ AU AN done
                      {fun (lr: I + X) (w': World E) =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' w'
                               /\ f i'  w' < f i w}]>) ->
    <( {iter k i}, w |= φ AU ψ )>.
  Proof.
    intros.
    eapply aul_iter with Ri
                         (ltof _ (fun '(i, w) => f i w)); auto.
    apply well_founded_ltof.
  Qed.
  
  Lemma aur_iter{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E (I + X)) (φ: ctll E) (ψ: ctlr E X):
    well_founded Rv ->    
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ AU AN done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                       | inr r => <[ {Ret r}, w' |= ψ \/ φ AX ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AU ψ ]>.
  Proof with auto with ctl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    eapply aur_bind_r with
      (R:=(fun (lr : I + X) (w' : World E) =>
             match lr with
             | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
             | inr r => <[ {Ret r}, w' |= ψ \/ φ AX ψ ]>
             end))...
    intros [i' | r] w'...
    - intros (Hi' & Hv). 
      rewrite sb_guard.
      remember (i', w') as y.
      replace i' with (fst y) in Hi' |- * by now subst.
      replace w' with (snd y) in Hi' |- * by now subst.
      apply HindWf...
    - apply aur_ret.
  Qed.

  Lemma aur_iter_nat{X I} Ri (f: I -> World E -> nat) (i: I) w (k: I -> ctree E (I + X)) (φ: ctll E) (ψ: ctlr E X):
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ AU AN done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => Ri i' w' /\ f i' w' < f i w
                       | inr r => <[ {Ret r}, w' |= ψ \/ φ AX ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AU ψ ]>.
  Proof.
    intros.
    eapply aur_iter with Ri (ltof _ (fun '(i, w) => f i w)); auto.
    apply well_founded_ltof.
  Qed.
  
  (* EU *)
  Lemma eul_iter{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E (I + X)) (φ ψ: ctll E):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= φ EU ψ )> \/
          <[ {k i}, w |= φ EU EN done
                      {fun (lr: I + X) (w': World E) =>
                         exists i', lr = inl i' /\ Ri i' w' /\ Rv (i', w') (i, w)}]>) ->
    <( {iter k i}, w |= φ EU ψ )>.
  Proof with auto with ctl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (H _ _ Hi).
    - now eapply ctll_bind_l.
    - eapply eul_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ Ri i' w' /\ Rv (i', w') (i, w))... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, w') as y.
        replace j with (fst y) in Hi' |- * by now subst.
        replace w' with (snd y) in Hi' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Lemma eur_iter{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E (I + X)) (φ: ctll E) (ψ: ctlr E X):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ EU EN done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                       | inr r => <[ {Ret r}, w' |= ψ \/ φ EX ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ EU ψ ]>.
  Proof with auto with ctl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    eapply eur_bind_r with
      (R:=(fun (lr : I + X) (w' : World E) =>
             match lr with
             | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
             | inr r => <[ {Ret r}, w' |= ψ \/ φ EX ψ ]>
             end))...
    intros [i' | r] w'...
    intros (Hi' & Hv). 
    rewrite sb_guard.
    remember (i', w') as y.
    replace i' with (fst y) in Hi' |- * by now subst.
    replace w' with (snd y) in Hi' |- * by now subst.
    apply HindWf...
    apply eur_ret.
  Qed.
  
  (* AG *)
  Typeclasses Transparent sbisim.
  Lemma ag_iter{X I} (R: rel I (World E)) (i: I) w (k: I -> ctree E (I + X)) φ:
    R i w ->
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |= φ)> /\
          <[ {k i}, w |= AN (φ AU AN done
                      {fun (lr: I + X) (w': World E) =>
                         exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
    <( {iter k i}, w |= AG φ )>.
  Proof with auto with ctl.
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
      apply can_step_bind_l with k' wk...
      specialize (H' _ _ TR).
      now apply aur_not_done in H'.
    - intros t' w' TR.
      rewrite unfold_iter in TR.
      apply ktrans_bind_inv in TR as
          [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ft_t (ag_bind_ag φ
                       (fun (lr: I+X) (w0: World E) => exists i' : I, lr = inl i' /\ R i' w0))).
        apply in_bind_ctx1.
        * now apply H'. 
        * intros [l | r] w_ (? & Hinv & HR'); inv Hinv.
          rewrite sb_guard. 
          apply CIH...
      + (* [k x] returns *)        
        specialize (H' _ _ TRt0) as HAX.
        now apply aur_stuck, axr_stuck in HAX.
  Qed.        

  (* EG *)
  Lemma eg_iter{X I} R (i: I) w (k: I -> ctree E (I + X)) (φ: ctll E):
    R i w ->    
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |= φ)> /\
        <[ {k i}, w |= EN (φ EU EN done
                    {fun (lr: I + X) (w': World E) =>
                       exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
    <( {iter k i}, w |= EG φ )>.
  Proof with auto with ctl.
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
                 | inl l => Guard (Ctree.iter k l)
                 | inr r => Ret r
                  end), w0; split.
      + rewrite unfold_iter.
        apply ktrans_bind_r...
        now apply eur_not_done in H0'.
      + apply (ft_t (eg_bind_eg φ
                       (fun (lr: I+X) (w0: World E) => exists i' : I, lr = inl i' /\ R i' w0))).
        apply in_bind_ctx1.
        * now apply H0'. 
        * intros [l | r] w_ (? & Hinv & HR); inv Hinv.          
          rewrite sb_guard.
          apply CIH...
  Qed.

End IterLemmas.
