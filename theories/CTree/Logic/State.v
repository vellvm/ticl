From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Interp.State
  CTree.Events.Writer
  CTree.Logic.Trans
  CTree.Logic.Bind
  CTree.Logic.Iter
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.EF
  CTree.Logic.AG
  CTree.Logic.EX
  Logic.Ctl.

From Coq Require Import Arith.Wf_nat.
From Coq Require Import Program.Tactics.

Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

(*| Instrumented ctree formulas |*)
Notation ctllW W := (ctll (writerE W)).
Notation ctlrW W := (ctlr (writerE W)).
Notation WorldW W := (World (writerE W)).

Section StateLemmas.
  (* E: Uniterpreted effect (to interpret)
     F: New uniterpreted effect (remainder)
     Σ: Interpretation state (concrete domain)
     W: Observation state (ghost domain)
  *)
  Context {E Σ W: Type} {HE: Encode E}
    (* Semantic handler with instrumentation *)
    (h: E ~> stateT Σ (ctreeW W))
    (* Initial state *)
    (σ: Σ).
  
  (*| Prove by induction on formulas [φ], very useful! |*)
  Theorem ctll_state_bind_l{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) (φ: ctllW W) w,
      <( {interp_state h t σ}, w |= φ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ )>.
  Proof with auto with ctl.
    intros.
    rewrite interp_state_bind.
    now apply ctll_bind_l.
  Qed.

  (*| Bind lemmas for [AX] |*)
  Theorem axl_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AX done {fun '(x, σ) => R x σ} ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ AX ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AX ψ )>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    apply axl_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] w' HR...
  Qed.    
  
  Theorem axr_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AX done {fun '(x, σ) => R x σ} ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ AX ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AX ψ ]>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    apply axr_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] w' HR...
  Qed.

  Theorem axr_state_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ AX done= {(r, σ')} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= φ AX ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AX ψ ]>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply axr_bind_r... 
    intros [y σ_] w_ (Hinv & HR); inv Hinv; subst...
  Qed.
  
  (*| Bind lemmas for [EX] |*)
  Typeclasses Transparent sbisim.
  Theorem exl_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ EX done= {(r,σ')} w' ]> ->
      <( {interp_state h (k r) σ'}, w' |= φ EX ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EX ψ )>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply exl_bind_r...
  Qed.

  Theorem exr_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ EX done= {(r,σ')} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= φ EX ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EX ψ ]>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply exr_bind_r...
  Qed.
  
  (*| Bind lemmas for [AU] |*)
  Theorem aul_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AU AN done {fun '(r,σ) => R r σ} ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ AU ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ )>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply aul_bind_r...
    intros [y σ'] * HR...
  Qed.

  Theorem aul_state_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ AU AN done= {(x',σ')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= φ AU ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ )>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply aul_bind_r...
    intros [y σ''] * [Heq ->]; inv Heq...
  Qed.
  
  Theorem aur_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AU AN done {fun '(r,σ) => R r σ} ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ AU ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ ]>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply aur_bind_r...
    intros [y σ'] * HR...
  Qed.

  Theorem aur_state_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ AU AN done= {(x',σ')} w' ]> ->
      <[ {interp_state h (k x') σ'}, w' |= φ AU ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ ]>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply aur_bind_r...
    intros [y σ''] * [Heq ->]; inv Heq...
  Qed.
  
  (*| Bind lemmas for [EU] |*)
  Theorem eul_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EU EN done {fun '(r,σ) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <( {interp_state h (k r) σ}, w |= φ EU ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ )>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    apply eul_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] * HR...
  Qed.

  Theorem eur_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EU EN done {fun '(r,σ) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <[ {interp_state h (k r) σ}, w |= φ EU ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ ]>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    apply eur_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] * HR...
  Qed.

  (*| Bind lemma for [AG] |*)
  Theorem ag_state_bind_r{X Y}: forall (t: ctree E X) w (k: X -> ctree E Y) φ R,
      <[ {interp_state h t σ}, w |= φ AU AN done {fun '(r, σ) => R r σ} ]> ->
      (forall (x: X) σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= AG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= AG φ )>.
  Proof with auto with ctl.
    intros.
    rewrite interp_state_bind.
    apply ag_bind_r with (R:=fun '(r, σ) => R r σ)...
    intros [y σ'] * HR...
  Qed.

  (*| Bind lemma for [EG] |*)
  Theorem eg_state_bind_r{X Y}: forall (t: ctree E X) w (k: X -> ctree E Y) R φ,
      <[ {interp_state h t σ}, w |= φ EU EN done {fun '(r, σ) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <( {interp_state h (k r) σ}, w |= EG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= EG φ )>.
  Proof with auto with ctl.
    intros.
    rewrite interp_state_bind.
    apply eg_bind_r with (R:=fun '(r, σ) => R r σ)...
    intros [y σ'] * HR...
  Qed.

  (*| Iter lemmas for [AX] |*)
  Theorem axl_state_iter{X I} Ri (Rv: relation I) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AX ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AX done
                      {fun '(lr, σ') w' => 
                         exists (i': I), lr = inl i' /\ Ri i' σ' w' /\ Rv i' i}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ AX ψ )>.
  Proof with auto with ctl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    generalize dependent σ.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    rewrite interp_state_unfold_iter.
    destruct (H _ _ _ Hi).
    - now eapply ctll_bind_l.
    - eapply axl_bind_r with
        (R:=fun '(lr, σ') w' =>
              exists i' : I, lr = inl i' /\ Ri i' σ' w' /\ Rv i' i)... 
      intros [[i' | r] σ'] w'.            
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.        
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Theorem axr_state_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E (I + X))
    (φ: ctllW W) (ψ: ctlrW W (X * Σ)):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ AX done
                                       {fun '(lr, σ') (w': WorldW W) =>
                                          match lr with
                                          | inl i' => Ri i' σ' w' /\ Rv i' i
                                          | inr r => <[ {Ret (r, σ')}, w' |= φ AX ψ ]>
                                          end} ]>) ->
    <[ {interp_state h (Ctree.iter k i) σ}, w |= φ AX ψ ]>.
  Proof with auto with ctl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    generalize dependent σ.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    rewrite interp_state_unfold_iter.
    destruct (H _ _ _ Hi) as (Hφ & Hs & H').
    eapply axr_bind_r with
        (R:=fun '(lr, σ') w' =>
               match lr with
               | inl i' => Ri i' σ' w' /\ Rv i' i
               | inr r => <[ {Ret (r, σ')}, w' |= φ AX ψ ]>
               end)...
    intros [[i' | r] σ'] w'.            
    - intros (Hi' & Hv). 
      rewrite sb_guard.        
      apply HindWf...
    - auto.
  Qed.

  (*| Iter lemmas for [EX] |*)
  Theorem exl_state_iter{X I} Ri (Rv: relation I) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ EX ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ EX done
                      {fun '(lr, σ') w' => 
                         exists (i': I), lr = inl i' /\ Ri i' σ' w' /\ Rv i' i}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ EX ψ )>.
  Proof with auto with ctl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    generalize dependent σ.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    rewrite interp_state_unfold_iter.
    destruct (H _ _ _ Hi).
    - now eapply ctll_bind_l.
    - apply ex_done in H0 as (Hφ & [[l | r] σ'] & Heqt & i' & Hinv & HRi & HRv); inv Hinv.
      rewrite Heqt, bind_ret_l, sb_guard.
      apply HindWf...
  Qed.

  Theorem exr_state_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E (I + X)) φ ψ:
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ EX done
                                       {fun '(lr, σ') (w': WorldW W) =>
                                          match lr with
                                          | inl i' => Ri i' σ' w' /\ Rv i' i
                                          | inr r => <[ {Ret (r, σ')}, w' |= φ EX ψ ]>
                                          end} ]>) ->
    <[ {interp_state h (Ctree.iter k i) σ}, w |= φ EX ψ ]>.
  Proof with auto with ctl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    generalize dependent σ.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    rewrite interp_state_unfold_iter.
    pose proof (H _ _ _ Hi) as H'.
    apply ex_done in H' as (Hφ & [[l | r] σ'] & Heqt & H').
    - destruct H'.
      rewrite Heqt, bind_ret_l, sb_guard.
      apply HindWf...
    - rewrite Heqt, bind_ret_l...
  Qed.


  (*| Iter lemmas for [AU] |*)
  Theorem aul_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AU AN done
                      {fun '(lr, σ') (w': WorldW W) =>
                         exists i', lr = inl i' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ AU ψ )>.
  Proof with auto with ctl.
    remember (i, σ, w) as P.
    replace i with (fst (fst P)) by now subst.
    replace σ with (snd (fst P)) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w σ.
    intros WfR Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as ((i, σ), w); cbn in *. 
    rename H into HindWf.
    intros.
    rewrite interp_state_unfold_iter.
    destruct (H _ _ _ Hi).
    - now apply ctll_bind_l.
    - eapply aul_bind_r with
        (R:=fun '(lr, σ') w' =>
              exists i' : I, lr = inl i' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w))... 
      intros [[i' | r] σ'] w'.            
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, σ', w') as y.
        replace j with (fst (fst y)) in Hi' |- * by now subst.
        replace σ' with (snd (fst y)) in Hi' |- * by now subst.
        replace w' with (snd  y) in Hi' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Theorem aul_state_iter_acc{X I} Ri (Rv: relation I) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AU AN done
                      {fun '(lr, σ') (w': WorldW W) =>
                         exists i', lr = inl i' /\ Ri i' σ' w' /\ Rv i' i}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ AU ψ )>.
  Proof with auto.
    intros.
    apply aul_state_iter with (Ri:=Ri) (Rv:=fun p p' => Rv (fst (fst p)) (fst (fst p')))...
    apply wf3_proj1...
  Qed.

  Theorem aul_state_iter_state{X I} Ri (Rv: relation Σ) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AU AN done
                      {fun '(lr, σ') (w': WorldW W) =>
                         exists i', lr = inl i' /\ Ri i' σ' w' /\ Rv σ' σ}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ AU ψ )>.
  Proof with auto.
    intros.
    apply aul_state_iter with (Ri:=Ri) (Rv:=fun p p' => Rv (snd (fst p)) (snd (fst p')))...
    apply wf3_proj2...
  Qed.

  Theorem aul_state_iter_world{X I} Ri (Rv: relation (WorldW W)) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AU AN done
                      {fun '(lr, σ') (w': WorldW W) =>
                         exists i', lr = inl i' /\ Ri i' σ' w' /\ Rv w' w}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ AU ψ )>.
  Proof with auto.
    intros.
    apply aul_state_iter with (Ri:=Ri) (Rv:=fun p p' => Rv (snd p) (snd p'))...
    apply wf3_proj3...
  Qed.
  
  Theorem aur_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E (I + X)) (φ: ctllW W) (ψ: ctlrW W (X * Σ)):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ AU AN done
                    {fun '(lr, σ') (w': WorldW W) =>
                       match lr with
                       | inl i' => Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
                       | inr r => <[ {Ret (r, σ')}, w' |= ψ \/ φ AX ψ ]>
                       end} ]>) ->
    <[ {interp_state h (Ctree.iter k i) σ}, w |= φ AU ψ ]>.
  Proof with auto with ctl.
    remember (i, σ, w) as P.
    replace i with (fst (fst P)) by now subst.
    replace σ with (snd (fst P)) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w σ.
    intros WfR Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as ((i, σ), w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite interp_state_unfold_iter.
    eapply aur_bind_r with
      (R:=fun '(lr, σ') w' =>
             match lr with
             | inl i' => Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
             | inr r => <[ {Ret (r, σ')}, w' |= ψ \/ φ AX ψ ]>
             end)...
    intros [[i' | r] σ'] w'...
    - intros (Hi' & Hv). 
      rewrite sb_guard.
      remember (i', σ', w') as y.
      replace i' with (fst (fst y)) in Hi' |- * by now subst.
      replace σ' with (snd (fst y)) in Hi' |- * by now subst.
      replace w' with (snd y) in Hi' |- * by now subst.
      apply HindWf...
    - apply aur_ret.
  Qed.
  
  (*| Iter lemmas for [EU] |*)
  Lemma eul_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ EU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ EU EN done
                      {fun '(lr, σ') w' =>
                         exists i', lr = inl i' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ EU ψ )>.
  Proof with auto with ctl.
    remember (i, σ, w) as P.
    replace i with (fst (fst P)) by now subst.
    replace σ with (snd (fst P)) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w σ.
    intros WfR Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as ((i, σ), w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite interp_state_unfold_iter.
    destruct (H _ _ _ Hi).
    - now eapply ctll_bind_l.
    - eapply eul_bind_r with
        (R:=fun '(lr, σ') w' =>
              exists i' : I, lr = inl i' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w))... 
      intros [[i' | r] σ'] w'.            
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, σ', w') as y.
        replace j with (fst (fst y)) in Hi' |- * by now subst.
        replace σ' with (snd (fst y)) in Hi' |- * by now subst.
        replace w' with (snd y) in Hi' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Theorem eur_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w (k: I -> ctree E (I + X)) (φ: ctllW W) (ψ: ctlrW W (X * Σ)):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ EU EN done
                    {fun '(lr, σ') w' =>
                       match lr with
                       | inl i' => Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
                       | inr r => <[ {Ret (r, σ')}, w' |= ψ \/ φ EX ψ ]>
                       end} ]>) ->
    <[ {interp_state h (iter k i) σ}, w |= φ EU ψ ]>.
  Proof with auto with ctl.
    remember (i, σ, w) as P.
    replace i with (fst (fst P)) by now subst.
    replace σ with (snd (fst P)) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i σ w.
    intros WfR Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as ((i, σ), w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite interp_state_unfold_iter.
    eapply eur_bind_r with
      (R:=fun '(lr, σ') w' =>
            match lr with
            | inl i' => Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
            | inr r => <[ {Ret (r, σ')}, w' |= ψ \/ φ EX ψ ]>
             end)...
    intros [[i' | r] σ'] w'...
    - intros (Hi' & Hv). 
      rewrite sb_guard.
      remember (i', σ', w') as y.
      replace i' with (fst (fst y)) in Hi' |- * by now subst.
      replace σ' with (snd (fst y)) in Hi' |- * by now subst.
      replace w' with (snd y) in Hi' |- * by now subst.
      apply HindWf...
    - apply eur_ret.
  Qed.

  (*| Iter lemma for [AG] |*)
  Typeclasses Transparent sbisim.
  Lemma ag_state_iter{X I} R i w (k: I -> ctree E (I + X)) φ:
    R i σ w ->
    not_done w ->
    (forall (i: I) σ w,
        R i σ w ->
        not_done w ->
        <[ {interp_state h (k i) σ}, w |= φ AX (φ AU AN done
                    {fun '(lr, σ') w' =>
                       exists (i': I), lr = inl i' /\ not_done w' /\ R i' σ' w'}) ]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= AG φ )>.
  Proof with auto with ctl.
    intros.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    generalize dependent σ.
    coinduction RR CIH; intros.
    rewrite interp_state_unfold_iter.
    specialize (H1 _ _ _ H H0) as H1'.
    cdestruct H1'.
    split2.
    - now apply ctll_bind_l.
    - destruct Hs as (k' & wk & TRk).
      apply can_step_bind_l with k' wk...
      specialize (H1' _ _ TRk).
      now apply aur_not_done in H1'.
    - intros t' w' TR.
      apply ktrans_bind_inv in TR as
          [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ft_t (ag_bind_ag φ
                       (fun '(lr, σ') w' =>
                          exists i' : I, lr = inl X i' /\ not_done w' /\ R i' σ' w'))).
        apply in_bind_ctx1.
        * now apply H1'. 
        * intros [[l | r] σ'] w_ (? & Hinv & Hd & HR); inv Hinv.
          rewrite sb_guard.
          apply CIH...
      + (* [k x] returns *)        
        specialize (H1' _ _ TRt0) as HAX.
        now apply aur_stuck, axr_stuck in HAX.
  Qed.

  (*| Iter lemma for [EG] |*)
  Lemma eg_state_iter{X I} R (i: I) w (k: I -> ctree E (I + X)) φ:
    R i σ w ->
    not_done w ->
    (forall (i: I) σ w,
        R i σ w ->
        not_done w ->
        <[ {interp_state h (k i) σ}, w |= φ EX (φ EU EN done
                    {fun '(lr, σ') w' =>
                       exists (i': I), lr = inl X i' /\ not_done w' /\ R i' σ' w'}) ]>) ->
    <( {interp_state h (iter k i) σ}, w |= EG φ )>.
  Proof with auto with ctl.
    intros.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    generalize dependent σ.
    coinduction RR CIH; intros.
    setoid_rewrite interp_state_unfold_iter.
    specialize (H1 _ _ _ H H0) as H1'.
    cdestruct H1'.
    split.
    - now apply ctll_bind_l.
    - exists (pat <- t;; match pat with
                 | (inl l, s) => Guard (interp_state h (iter k l) s)
                 | (inr r, s) => Ret (r, s)
                  end), w0; split.
      + apply ktrans_bind_r...
        now apply eur_not_done in H1'.
      + apply (ft_t (eg_bind_eg φ
                       (fun '(lr, σ') w' =>
                          exists i' : I, lr = inl X i' /\ not_done w' /\ R i' σ' w'))).
        apply in_bind_ctx1.
        * now apply H1'. 
        * intros [[l | r] σ'] w_ (? & Hinv & Hd & HR); inv Hinv.
          rewrite sb_guard.
          apply CIH...
  Qed.

  (*| Iter with ranking function [f] for AU |*)
  Theorem aul_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AU AN done
                      {fun '(lr, σ') (w': WorldW W) =>
                         exists i', lr = inl i' /\ Ri i' σ' w' /\ f i' σ' w' < f i σ w}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ AU ψ )>.
  Proof.
    intros.
    eapply aul_state_iter with Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.

  Theorem aur_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E (I + X)) (φ: ctllW W) (ψ: ctlrW W (X * Σ)):
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ AU AN done
                                       {fun '(lr, σ') (w': WorldW W) =>
                                          match lr with
                                          | inl i' => Ri i' σ' w' /\ f i' σ' w' < f i σ w
                                          | inr r => <[ {Ret (r, σ')}, w' |= ψ \/ φ AX ψ ]>
                                          end} ]>) ->
    <[ {interp_state h (Ctree.iter k i) σ}, w |= φ AU ψ ]>.
  Proof.
    intros.
    eapply aur_state_iter with Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.
  
  (*| Iter with ranking function [f] for EU |*)
  Lemma eul_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ EU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ EU EN done
                      {fun '(lr, σ') w' =>
                         exists i', lr = inl i' /\ Ri i' σ' w' /\ f i' σ' w' < f i σ w}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ EU ψ )>.
  Proof.
    intros.
    eapply eul_state_iter with Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.

  Theorem eur_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat)(i: I) w
    (k: I -> ctree E (I + X)) (φ: ctllW W) (ψ: ctlrW W (X * Σ)):
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ EU EN done
                    {fun '(lr, σ') w' =>
                       match lr with
                       | inl i' => Ri i' σ' w' /\ f i' σ' w' < f i σ w
                       | inr r => <[ {Ret (r, σ')}, w' |= ψ \/ φ EX ψ ]>
                       end} ]>) ->
    <[ {interp_state h (iter k i) σ}, w |= φ EU ψ ]>.
  Proof.
    intros.
    eapply eur_state_iter with Ri (ltof _ (fun '((i, σ), w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.  
End StateLemmas.
