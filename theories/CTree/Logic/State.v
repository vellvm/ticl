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

  (*| Bind lemmas for [AN] |*)
  Theorem anl_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AN done {fun '(x, σ) => R x σ} ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ AN ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ )>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    apply anl_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] w' HR...
  Qed.    
  
  Theorem anr_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AN done {fun '(x, σ) => R x σ} ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ AN ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ ]>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    apply anr_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] w' HR...
  Qed.

  Theorem anr_state_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ AN done= {(r, σ')} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= φ AN ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ ]>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply anr_bind_r... 
    intros [y σ_] w_ (Hinv & HR); inv Hinv; subst...
  Qed.

  (*| Bind lemmas for [EN] |*)
  Typeclasses Transparent sbisim.
  Theorem enl_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EN done {fun '(r,σ) => R r σ}  ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ EN ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ )>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply enl_bind_r...
    intros [y σ'] * HR...
  Qed.
  
  Theorem enl_state_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ EN done= {(r,σ')} w' ]> ->
      <( {interp_state h (k r) σ'}, w' |= φ EN ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ )>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply enl_bind_r_eq...
  Qed.

  Theorem enr_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EN done {fun '(r,σ) => R r σ}  ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ EN ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ ]>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply enr_bind_r...
    intros [y σ'] * HR...
  Qed.

  Theorem enr_state_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' r σ' φ ψ,
      <[ {interp_state h t σ}, w |= φ EN done= {(r,σ')} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= φ EN ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ ]>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply enr_bind_r_eq...
  Qed.
  
  (*| Bind lemmas for [AU] |*)
  Theorem aul_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AU AX done {fun '(r,σ) => R r σ} ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ AU ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ )>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply aul_bind_r...
    intros [y σ'] * HR...
  Qed.

  Theorem aul_state_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ AU AX done= {(x',σ')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= φ AU ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ )>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply aul_bind_r...
    intros [y σ''] * [Heq ->]; inv Heq...
  Qed.
  
  Theorem aur_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AU AX done {fun '(r,σ) => R r σ} ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ AU ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ ]>.  
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply aur_bind_r...
    intros [y σ'] * HR...
  Qed.

  Theorem aur_state_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ AU AX done= {(x',σ')} w' ]> ->
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
      <[ {interp_state h t σ}, w |= φ EU EX done {fun '(r,σ) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <( {interp_state h (k r) σ}, w |= φ EU ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ )>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    apply eul_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] * HR...
  Qed.

  Theorem eul_state_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ EU EX done= {(x',σ')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= φ EU ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ )>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply eul_bind_r... 
    intros [y σ''] * [Heq ->]; inv Heq... 
  Qed.
  
  Theorem eur_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EU EX done {fun '(r,σ) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <[ {interp_state h (k r) σ}, w |= φ EU ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ ]>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    apply eur_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] * HR...
  Qed.

  Theorem eur_state_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ EU EX done= {(x',σ')} w' ]> ->
      <[ {interp_state h (k x') σ'}, w' |= φ EU ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ ]>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply eur_bind_r... 
    intros [y σ''] * [Heq ->]; inv Heq... 
  Qed.

  (*| Bind lemma for [AG] |*)
  Theorem ag_state_bind_r{X Y}: forall (t: ctree E X) w (k: X -> ctree E Y) φ R,
      <[ {interp_state h t σ}, w |= φ AU AX done {fun '(r, σ) => R r σ} ]> ->
      (forall (x: X) σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= AG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= AG φ )>.
  Proof with auto with ctl.
    intros.
    rewrite interp_state_bind.
    apply ag_bind_r with (R:=fun '(r, σ) => R r σ)...
    intros [y σ'] * HR...
  Qed.
  
  Theorem ag_state_bind_r_eq{X Y}: forall (t: ctree E X) w w' (k: X -> ctree E Y) φ x' σ',
      <[ {interp_state h t σ}, w |= φ AU AX done= {(x',σ')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= AG φ )> ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= AG φ )>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply ag_bind_r...
    intros [y σ''] * [Heq HR]; inv Heq...    
  Qed.
  
  (*| Bind lemma for [EG] |*)
  Theorem eg_state_bind_r{X Y}: forall (t: ctree E X) w (k: X -> ctree E Y) R φ,
      <[ {interp_state h t σ}, w |= φ EU EX done {fun '(r, σ) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <( {interp_state h (k r) σ}, w |= EG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= EG φ )>.
  Proof with auto with ctl.
    intros.
    rewrite interp_state_bind.
    apply eg_bind_r with (R:=fun '(r, σ) => R r σ)...
    intros [y σ'] * HR...
  Qed.

  Theorem eg_state_bind_r_eq{X Y}: forall (t: ctree E X) w w' (k: X -> ctree E Y) φ x' σ',
      <[ {interp_state h t σ}, w |= φ EU EX done= {(x',σ')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= EG φ )> ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= EG φ )>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply eg_bind_r...
    intros [y σ''] * [Heq HR]; inv Heq...    
  Qed.
  
  (*| Iter lemmas for [AN] |*)
  Theorem anl_state_iter{X I} Ri (Rv: relation I) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AN ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AN done
                      {fun '(lr, σ') w' => 
                         exists (i': I), lr = inl i' /\ Ri i' σ' w' /\ Rv i' i}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ AN ψ )>.
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
    - eapply anl_bind_r with
        (R:=fun '(lr, σ') w' =>
              exists i' : I, lr = inl i' /\ Ri i' σ' w' /\ Rv i' i)... 
      intros [[i' | r] σ'] w'.            
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.        
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Theorem anr_state_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E (I + X))
    (φ: ctllW W) (ψ: ctlrW W (X * Σ)):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ AN done
                                       {fun '(lr, σ') (w': WorldW W) =>
                                          match lr with
                                          | inl i' => Ri i' σ' w' /\ Rv i' i
                                          | inr r => <[ {Ret (r, σ')}, w' |= φ AN ψ ]>
                                          end} ]>) ->
    <[ {interp_state h (Ctree.iter k i) σ}, w |= φ AN ψ ]>.
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
    eapply anr_bind_r with
        (R:=fun '(lr, σ') w' =>
               match lr with
               | inl i' => Ri i' σ' w' /\ Rv i' i
               | inr r => <[ {Ret (r, σ')}, w' |= φ AN ψ ]>
               end)...
    intros [[i' | r] σ'] w'.            
    - intros (Hi' & Hv). 
      rewrite sb_guard.        
      apply HindWf...
    - auto.
  Qed.

  (*| Iter lemmas for [EN] |*)
  Theorem enl_state_iter{X I} Ri (Rv: relation I) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ EN ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ EN done
                      {fun '(lr, σ') w' => 
                         exists (i': I), lr = inl i' /\ Ri i' σ' w' /\ Rv i' i}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ EN ψ )>.
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
    - apply enr_done in H0 as (Hφ & [[l | r] σ'] & Heqt & i' & Hinv & HRi & HRv); inv Hinv.
      rewrite Heqt, bind_ret_l, sb_guard.
      apply HindWf...
  Qed.

  Theorem enr_state_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E (I + X)) φ ψ:
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ EN done
                                       {fun '(lr, σ') (w': WorldW W) =>
                                          match lr with
                                          | inl i' => Ri i' σ' w' /\ Rv i' i
                                          | inr r => <[ {Ret (r, σ')}, w' |= φ EN ψ ]>
                                          end} ]>) ->
    <[ {interp_state h (Ctree.iter k i) σ}, w |= φ EN ψ ]>.
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
    apply enr_done in H' as (Hφ & [[l | r] σ'] & Heqt & H').
    - destruct H'.
      rewrite Heqt, bind_ret_l, sb_guard.
      apply HindWf...
    - rewrite Heqt, bind_ret_l...
  Qed.


  (*| Iter lemmas for [AU] |*)
  Theorem aul_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AU AX done
                      {fun '(lr, σ') (w': WorldW W) =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ Rv (i', σ', w') (i, σ, w)}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ AU ψ )>.
  Proof with auto with ctl.
    unfold iter, MonadIter_ctree.
    remember (i, σ, w) as P.
    replace i with (fst (fst P)) by now subst.
    replace σ with (snd (fst P)) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w σ.
    intros WfR Hd Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as ((i, σ), w); cbn in *. 
    rename H into HindWf.
    intros.
    destruct (H _ _ _ Hd Hi); rewrite interp_state_unfold_iter.
    - now apply ctll_bind_l.
    - eapply aul_bind_r with
        (R:=fun '(lr, σ') w' =>
              exists i' : I, lr = inl i'
                        /\ not_done w'
                        /\ Ri i' σ' w'
                        /\ Rv (i', σ', w') (i, σ, w))... 
      intros [[i' | r] σ'] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, σ', w') as y.
        replace j with (fst (fst y)) in Hi' |- * by now subst.
        replace σ' with (snd (fst y)) in Hi' |- * by now subst.
        replace w' with (snd y) in Hd', Hi' |- * by now subst.
        apply HindWf... 
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Theorem aur_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E (I + X)) (φ: ctllW W) (ψ: ctlrW W (X * Σ)):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ AU AX done
                    {fun '(lr, σ') (w': WorldW W) =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
                       | inr r => <[ {Ret (r, σ')}, w' |= φ AN ψ ]>
                       end} ]>) ->
    <[ {interp_state h (iter k i) σ}, w |= φ AU ψ ]>.
  Proof with auto with ctl.
    remember (i, σ, w) as P.
    replace i with (fst (fst P)) by now subst.
    replace σ with (snd (fst P)) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w σ.
    intros WfR Hi Hd H.
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
             | inl i' => not_done w' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
             | inr r => <[ {Ret (r, σ')}, w' |= φ AN ψ ]>
             end)...
    intros [[i' | r] σ'] w'...
    - intros (Hd' & Hi' & Hv). 
      rewrite sb_guard.
      remember (i', σ', w') as y.
      replace i' with (fst (fst y)) in Hi' |- * by now subst.
      replace σ' with (snd (fst y)) in Hi' |- * by now subst.
      replace w' with (snd y) in Hi', Hd' |- * by now subst.
      apply HindWf...
    - apply ctlr_an_au. 
  Qed.
  
  (*| Iter lemmas for [EU] |*)
  Lemma eul_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E (I + X)) (φ ψ: ctllW W):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ EU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ EU EX done
                      {fun '(lr, σ') w' =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ Rv (i', σ', w') (i, σ, w)}]>) ->
    <( {interp_state h (iter k i) σ}, w |= φ EU ψ )>.
  Proof with auto with ctl.
    unfold iter, MonadIter_ctree.
    remember (i, σ, w) as P.
    replace i with (fst (fst P)) by now subst.
    replace σ with (snd (fst P)) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w σ.
    intros WfR Hd Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as ((i, σ), w); cbn in *. 
    rename H into HindWf.
    intros.
    destruct (H _ _ _ Hd Hi); rewrite interp_state_unfold_iter.
    - apply ctll_bind_l...
    - eapply eul_bind_r with
        (R:=fun '(lr, σ') w' =>
              exists i' : I, lr = inl i'
                        /\ not_done w'
                        /\ Ri i' σ' w'
                        /\ Rv (i', σ', w') (i, σ, w))... 
      intros [[i' | r] σ'] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, σ', w') as y.
        replace j with (fst (fst y)) in Hi' |- * by now subst.
        replace σ' with (snd (fst y)) in Hi' |- * by now subst.
        replace w' with (snd y) in Hd', Hi' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Theorem eur_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w (k: I -> ctree E (I + X)) (φ: ctllW W) (ψ: ctlrW W (X * Σ)):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ EU EX done
                    {fun '(lr, σ') w' =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
                       | inr r => <[ {Ret (r, σ')}, w' |= φ EN ψ ]>
                       end} ]>) ->
    <[ {interp_state h (iter k i) σ}, w |= φ EU ψ ]>.
  Proof with auto with ctl.
    remember (i, σ, w) as P.
    replace i with (fst (fst P)) by now subst.
    replace σ with (snd (fst P)) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i σ w.
    intros WfR Hd Hi H.
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
            | inl i' => not_done w' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
            | inr r => <[ {Ret (r, σ')}, w' |= φ EN ψ ]>
             end)...
    intros [[i' | r] σ'] w'...
    - intros (Hd' & Hi' & Hv). 
      rewrite sb_guard.
      remember (i', σ', w') as y.
      replace i' with (fst (fst y)) in Hi' |- * by now subst.
      replace σ' with (snd (fst y)) in Hi' |- * by now subst.
      replace w' with (snd y) in Hd', Hi' |- * by now subst.
      apply HindWf...
    - apply ctlr_en_eu.
  Qed.

  (*| Iter lemma for [AG] |*)
  Typeclasses Transparent sbisim.
  Lemma ag_state_iter{X I} R i w (k: I -> ctree E (I + X)) φ:
    not_done w ->
    R i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <( {interp_state h (iter k i) σ}, w |= φ )> /\
        <[ {interp_state h (k i) σ}, w |= AX (φ AU AX done
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
    specialize (H1 _ _ _ H H0) as (Hφ & H1').
    cdestruct H1'.
    split2.
    - now apply Hφ. 
    - rewrite interp_state_unfold_iter.
      destruct Hs as (k' & wk & TRk).
      apply can_step_bind_l with k' wk...
      specialize (H1' _ _ TRk).
      now apply aur_not_done in H1'.
    - intros t' w' TR.
      rewrite interp_state_unfold_iter in TR.
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
        specialize (H1' _ _ TRt0) as HAN.
        now apply aur_stuck, anr_stuck in HAN.
  Qed.

  (*| Iter lemma for [EG] |*)
  Lemma eg_state_iter{X I} R (i: I) w (k: I -> ctree E (I + X)) φ:
    R i σ w ->
    not_done w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <( {interp_state h (iter k i) σ}, w |= φ )> /\
        <[ {interp_state h (k i) σ}, w |= EX (φ EU EX done
                    {fun '(lr, σ') w' =>
                       exists (i': I), lr = inl X i' /\ not_done w' /\ R i' σ' w'}) ]>) ->
    <( {interp_state h (iter k i) σ}, w |= EG φ )>.
  Proof with auto with ctl.
    unfold iter, MonadIter_ctree.
    intros.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    generalize dependent σ.
    coinduction RR CIH; intros.
    specialize (H1 _ _ _ H0 H) as (Hφ & H1').
    cdestruct H1'.
    split.
    - now apply Hφ. 
    - setoid_rewrite interp_state_unfold_iter.
      exists (pat <- t;; match pat with
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
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AU AX done
                      {fun '(lr, σ') (w': WorldW W) =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ f i' σ' w' < f i σ w}]>) ->
    <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>.
  Proof.
    intros.
    eapply aul_state_iter with Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.

  Theorem aur_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E (I + X)) (φ: ctllW W) (ψ: ctlrW W (X * Σ)):
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ AU AX done
                                       {fun '(lr, σ') (w': WorldW W) =>
                                          match lr with
                                          | inl i' => not_done w'
                                                     /\ Ri i' σ' w'
                                                     /\ f i' σ' w' < f i σ w
                                          | inr r => <[ {Ret (r, σ')}, w' |= φ AN ψ ]>
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
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ EU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ EU EX done
                      {fun '(lr, σ') w' =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ f i' σ' w' < f i σ w}]>) ->
    <( {interp_state h (Ctree.iter k i) σ}, w |= φ EU ψ )>.
  Proof.
    intros.
    eapply eul_state_iter with Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.

  Theorem eur_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat)(i: I) w
    (k: I -> ctree E (I + X)) (φ: ctllW W) (ψ: ctlrW W (X * Σ)):
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ EU EX done
                    {fun '(lr, σ') w' =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' σ' w' /\ f i' σ' w' < f i σ w
                       | inr r => <[ {Ret (r, σ')}, w' |= φ EN ψ ]>
                       end} ]>) ->
    <[ {interp_state h (iter k i) σ}, w |= φ EU ψ ]>.
  Proof.
    intros.
    eapply eur_state_iter with Ri (ltof _ (fun '((i, σ), w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.  
End StateLemmas.
