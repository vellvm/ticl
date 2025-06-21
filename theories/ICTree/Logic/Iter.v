From Coinduction Require Import
  coinduction lattice tactics.

From TICL Require Import
  Events.Core
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Eq.Bind
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.EX
  ICTree.Logic.EF
  ICTree.Logic.Bind
  ICTree.Logic.Ret
  Logic.Core.

From Stdlib Require Import Arith.Wf_nat.

Generalizable All Variables.

Import ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.

Section IterLemmas.
  Context {E: Type} {HE: Encode E}.

  (* AN *)
  Lemma anl_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ictree E (I + X)) (φ ψ: ticll E):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= φ AN ψ )> \/
          <[ {k i}, w |= φ AN done
                      {fun (lr: I + X) (w': World E) => 
                         exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i}]>) ->
    <( {iter k i}, w |= φ AN ψ )>.
  Proof with auto with ticl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ictree.
    rewrite unfold_iter.
    destruct (H _ _ Hi).
    - now eapply ticll_bind_l.
    - eapply anl_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ Ri i' w' /\ Rv i' i)... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Lemma anr_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ictree E (I + X)) (φ: ticll E) (ψ: ticlr E X):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ AN done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => Ri i' w' /\ Rv i' i
                       | inr r => <[ {Ret r}, w' |= φ AN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AN ψ ]>.
  Proof with auto with ticl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ictree.
    rewrite unfold_iter.
    destruct (H _ _ Hi).
    - eapply anr_bind_r with
        (R:=(fun (lr : I + X) (w' : World E) =>
               match lr with
               | inl i' => Ri i' w' /\ Rv i' i
               | inr r => <[ {Ret r}, w' |= φ AN ψ ]>
               end))...
      intros [i' | r] w'...
      intros (Hi' & Hv). 
      rewrite sb_guard.
      apply HindWf...
  Qed.

  (* EN *)
  Typeclasses Transparent sbisim.
  Lemma enl_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ictree E (I + X)) (φ ψ: ticll E):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= φ EN ψ )> \/
          <[ {k i}, w |= φ EN done {fun (lr: I + X) w' =>
            exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i} ]>) ->
    <( {iter k i}, w |= φ EN ψ )>.
  Proof with auto with ticl.    
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    cbn in *.
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ictree.
    rewrite unfold_iter.
    destruct (H _ _ Hi).
    - now eapply ticll_bind_l.
    - apply enr_done in H0 as (Hφ & [l | r] & Heqt & i' & Hinv & HRi & HRv); inv Hinv.
      rewrite Heqt, bind_ret_l, sb_guard.
      apply HindWf...
  Qed.

  Lemma enr_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ictree E (I + X))
    (φ: ticll E) (ψ: ticlr E X):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ EN done {fun (lr: I + X) w' =>
                                    match lr with
                                    | inl i' => Ri i' w' /\ Rv i' i
                                    | inr r => <[ {Ret r}, w' |= φ EN ψ ]>
                                    end}]>) ->
    <[ {iter k i}, w |= φ EN ψ ]>.
  Proof with auto with ticl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    cbn in *.
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ictree.
    rewrite unfold_iter.    
    pose proof (H _ _ Hi) as H'.
    apply enr_done in H' as (Hφ & [l | r] & Heqt & Hi'). 
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
  Lemma aul_iter_next{X I} R (i: I) w (k: I -> ictree E (I + X)) (φ ψ: ticll E):
    <[ {k i}, w |= φ AU AX done {fun lr w => exists i', lr = inl i' /\ R i' w} ]> ->
    (forall i w, R i w -> <( {iter k i}, w |= φ AU ψ )>) ->
    <( {iter k i}, w |= φ AU ψ )>.
  Proof with auto with ticl.
    unfold iter, MonadIter_ictree.
    intros.
    rewrite unfold_iter.
    apply aul_bind_r with (R:=(fun lr w => exists i', lr = inl i' /\ R i' w))...
    intros ? ? (i' & -> & HR).
    rewrite sb_guard...
  Qed.

  Lemma aul_iter_split{X I} R Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ictree E (I + X)) (φ ψ: ticll E):
    well_founded Rv ->
    not_done w ->
    R i w ->
    (forall i w, not_done w -> Ri i w -> <( {iter k i}, w |= φ AU ψ )>) ->    
    (forall (i: I) w,
        not_done w ->
        R i w ->
        <[ {k i}, w |= φ AU AX done
                    {fun (lr: I + X) (w': World E) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ Ri i' w'} ]> \/ 
        <[ {k i}, w |= φ AU AX done
                    {fun (lr: I + X) (w': World E) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ R i' w'
                             /\ Rv (i', w') (i, w) }]>) ->
    <( {iter k i}, w |= φ AU ψ )>.
  Proof with auto with ticl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hd HR Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ictree.
    destruct (H _ _ Hd HR).
    - rewrite sb_unfold_iter.
      eapply aul_bind_r with (R:=fun (lr : I + X) (w' : World E) => exists i' : I, lr = inl i' /\ not_done w' /\ Ri i' w')...
      intros [i' | r] w' (i_ & His & Hd' & HRi); inv His.
      apply Hi...
    - rewrite sb_unfold_iter.
      eapply aul_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ not_done w'/\ R i' w' /\ Rv (i', w') (i, w))... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        remember (j, w') as y.
        replace j with (fst y) in Hi' |- * by now subst.
        replace w' with (snd y) in Hd', Hi' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.
      
  Lemma aul_iter{X I} R (Rv: relation (I * World E)) (i: I) w (k: I -> ictree E (I + X)) (φ ψ: ticll E):
    well_founded Rv ->
    not_done w ->
    R i w ->    
    (forall (i: I) w,
        not_done w ->
        R i w ->
        <( {k i}, w |= φ AU ψ )> \/
          <[ {k i}, w |= φ AU AX done
                      {fun (lr: I + X) (w': World E) =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ R i' w'
                               /\ Rv (i', w') (i, w)}]>) ->
    <( {iter k i}, w |= φ AU ψ )>.
  Proof with auto with ticl.
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
    unfold iter, MonadIter_ictree.
    destruct (H _ _ Hd Hi).
    - rewrite unfold_iter.
      apply ticll_bind_l... 
    - rewrite unfold_iter.
      eapply aul_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ not_done w'/\ R i' w' /\ Rv (i', w') (i, w))... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, w') as y.
        replace j with (fst y) in Hi' |- * by now subst.
        replace w' with (snd y) in Hd', Hi' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Lemma aul_iter_nat{X I} Ri (f: I -> World E -> nat) (i: I) w (k: I -> ictree E (I + X))
    (φ ψ: ticll E):
    not_done w ->
    Ri i w ->    
    (forall (i: I) w,
        not_done w ->
        Ri i w ->
        <( {k i}, w |= φ AU ψ )> \/
          <[ {k i}, w |= φ AU AX done
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

  Lemma aur_iter_next{X I} R (i: I) w (k: I -> ictree E (I + X)) (φ: ticll E) ψ:
    <[ {k i}, w |= φ AU AX done {fun lr w => exists i', lr = inl i' /\ R i' w} ]> ->
    (forall i w, R i w -> <[ {iter k i}, w |= φ AU ψ ]>) ->
    <[ {iter k i}, w |= φ AU ψ ]>.
  Proof with auto with ticl.
    unfold iter, MonadIter_ictree.
    intros.
    rewrite unfold_iter.
    apply aur_bind_r with (R:=(fun lr w => exists i', lr = inl i' /\ R i' w))...
    intros ? ? (i' & -> & HR).
    rewrite sb_guard...
  Qed.
  
  Lemma aur_iter{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ictree E (I + X)) (φ: ticll E) (ψ: ticlr E X):
    well_founded Rv ->    
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ AU AX done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                       | inr r => <[ {Ret r}, w' |= φ AN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AU ψ ]>.
  Proof with auto with ticl.
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
    unfold iter, MonadIter_ictree.
    rewrite unfold_iter.
    eapply aur_bind_r with
      (R:=(fun (lr : I + X) (w' : World E) =>
             match lr with
             | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
             | inr r => <[ {Ret r}, w' |= φ AN ψ ]>
             end))...
    intros [i' | r] w'...
    - intros (Hi' & Hv). 
      rewrite sb_guard.
      remember (i', w') as y.
      replace i' with (fst y) in Hi' |- * by now subst.
      replace w' with (snd y) in Hi' |- * by now subst.
      apply HindWf...
    - apply ticlr_an_au. 
  Qed.

  Lemma aur_iter_nat{X I} Ri (f: I -> World E -> nat) (i: I) w (k: I -> ictree E (I + X)) (φ: ticll E) (ψ: ticlr E X):
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ AU AX done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => Ri i' w' /\ f i' w' < f i w
                       | inr r => <[ {Ret r}, w' |= φ AN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AU ψ ]>.
  Proof.
    intros.
    eapply aur_iter with Ri (ltof _ (fun '(i, w) => f i w)); auto.
    apply well_founded_ltof.
  Qed.
  
  (* EU *)
  Lemma eul_iter{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ictree E (I + X)) (φ ψ: ticll E):
    well_founded Rv ->
    Ri i w ->
    not_done w ->
    (forall (i: I) w,
        Ri i w ->
        not_done w ->
        <( {k i}, w |= φ EU ψ )> \/
          <[ {k i}, w |= φ EU EX done
                      {fun (lr: I + X) (w': World E) =>
                         exists i', lr = inl i' /\ not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)}]>) ->
    <( {iter k i}, w |= φ EU ψ )>.
  Proof with auto with ticl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hi Hd H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ictree.
    rewrite unfold_iter.
    destruct (H _ _ Hi)...
    - now eapply ticll_bind_l.
    - eapply eul_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w))... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, w') as y.
        replace j with (fst y) in Hi' |- * by now subst.
        replace w' with (snd y) in Hi',Hd' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Lemma eur_iter{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ictree E (I + X)) (φ: ticll E) (ψ: ticlr E X):
    well_founded Rv ->
    Ri i w ->
    not_done w ->
    (forall (i: I) w,
        Ri i w ->
        not_done w ->
        <[ {k i}, w |= φ EU EX done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)
                       | inr r => <[ {Ret r}, w' |= φ EN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ EU ψ ]>.
  Proof with auto with ticl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hi Hd H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ictree.
    rewrite unfold_iter.
    eapply eur_bind_r with
      (R:=(fun (lr : I + X) (w' : World E) =>
             match lr with
             | inl i' => not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)
             | inr r => <[ {Ret r}, w' |= φ EN ψ ]>
             end))...
    intros [i' | r] w'...
    intros (Hd' & Hi' & Hv). 
    rewrite sb_guard.
    remember (i', w') as y.
    replace i' with (fst y) in Hi' |- * by now subst.
    replace w' with (snd y) in Hi',Hd' |- * by now subst.
    apply HindWf...
    apply ticlr_en_eu.
  Qed.
  
  (* AG *)
  Typeclasses Transparent sbisim.
  Lemma ag_iter{X I} (R: rel I (World E)) (i: I) w (k: I -> ictree E (I + X)) φ:
    R i w ->
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |= φ)> /\
          <[ {k i}, w |= AX (φ AU AX done
                      {fun (lr: I + X) (w': World E) =>
                         exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
    <( {iter k i}, w |= AG φ )>.
  Proof with auto with ticl.
    intros HR H.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    unfold iter, MonadIter_ictree.
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
        specialize (H' _ _ TRt0) as HAN.
        now apply aur_stuck, anr_stuck in HAN.
  Qed.        

  (* EG *)
  Lemma eg_iter{X I} R (i: I) w (k: I -> ictree E (I + X)) (φ: ticll E):
    R i w ->    
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |= φ)> /\
        <[ {k i}, w |= EX (φ EU EX done
                    {fun (lr: I + X) (w': World E) =>
                       exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
    <( {iter k i}, w |= EG φ )>.
  Proof with auto with ticl.
    intros.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    unfold iter, MonadIter_ictree.
    coinduction RR CIH; intros.
    specialize (H0 _ _ H) as (Hφ & H0').
    cdestruct H0'.
    split.
    - apply Hφ. 
    - exists (lr <- t;; match lr with
                 | inl l => Guard (ICtree.iter k l)
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
