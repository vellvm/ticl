From TICL Require Import
  Events.Core
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Events.Writer
  ICTree.Logic.Trans
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.EF
  ICTree.Logic.AG
  ICTree.Logic.EX
  Logic.Core  
  ICTree.Interp.State
  ICTree.Events.State.


From Coq Require Import Arith.Wf_nat.
From Coq Require Import Program.Tactics.

Generalizable All Variables.

Import ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.

(*| Instrumented ictree formulas |*)
Notation ticllW W := (ticll (writerE W)).
Notation ticlrW W := (ticlr (writerE W)).
Notation WorldW W := (World (writerE W)).

Section StateLemmas.
  (* E: Uniterpreted effect (to interpret)
     F: New uniterpreted effect (remainder)
     Σ: Interpretation state (concrete domain)
     W: Observation state (ghost domain)
  *)
  Context {E Σ W: Type} {HE: Encode E}
    (* Semantic handler with instrumentation *)
    (h: E ~> stateT Σ (ictreeW W))
    (* Initial state *)
    (σ: Σ).
  
  (*| Prove by induction on formulas [φ], very useful! |*)
  Theorem ticll_state_bind_l{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) (φ: ticllW W) w,
      <( {interp_state h t σ}, w |= φ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ )>.
  Proof with auto with ticl.
    intros.
    rewrite interp_state_bind.
    now apply ticll_bind_l.
  Qed.

  (*| Ret lemmas |*)
  Theorem axr_state_ret{X}: forall R (x: X) w,
      R (x, σ) w ->
      not_done w ->
      <[ {interp_state h (Ret x) σ}, w |= AX done R ]>.  
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_ret.
    apply axr_ret...
  Qed.
  
  Theorem aur_state_ret{X}: forall R (x: X) φ w,
      R (x, σ) w ->
      not_done w ->
      <[ {interp_state h (Ret x) σ}, w |= φ AU AX done R ]>.  
  Proof with eauto with ticl.
    intros.
    cleft.
    apply axr_state_ret...
  Qed.

    
  Theorem aul_state_ret{X}: forall (x: X) φ ψ w,
      not_done w ->
      <( {Ret (x, σ)}, w |= ψ )> ->
      <( {interp_state h (Ret x) σ}, w |= φ AU ψ )>.
  Proof with eauto with ticl.
    intros.
    cleft.
    now rewrite interp_state_ret.
  Qed.
  
  (*| Bind lemmas for [AN] |*)
  Theorem anl_state_bind_r{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AN done {fun '(x, σ) => R x σ} ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ AN ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ )>.  
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    apply anl_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] w' HR...
  Qed.    
  
  Theorem anr_state_bind_r{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AN done {fun '(x, σ) => R x σ} ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ AN ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ ]>.  
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    apply anr_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] w' HR...
  Qed.

  Theorem anr_state_bind_l{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AN AX done {fun '(x, σ) => R x σ} ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ ]>.  
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    apply anr_bind_l with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] w' HR...
  Qed.
  
  Theorem anr_state_bind_r_eq{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ AN done= {(r, σ')} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= φ AN ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ ]>.  
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply anr_bind_r... 
    intros [y σ_] w_ (Hinv & HR); inv Hinv; subst...
  Qed.

  Theorem anr_state_bind_l_eq{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ AN AX done= {(r, σ')} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ ]>.  
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply anr_bind_l...
    intros [y σ_] w_ (Hinv & HR); inv Hinv; subst...
  Qed.
  
  (*| Bind lemmas for [EN] |*)
  Typeclasses Transparent sbisim.
  Theorem enl_state_bind_r{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EN done {fun '(r,σ) => R r σ}  ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ EN ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ )>.
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply enl_bind_r...
    intros [y σ'] * HR...
  Qed.
  
  Theorem enl_state_bind_r_eq{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ EN done= {(r,σ')} w' ]> ->
      <( {interp_state h (k r) σ'}, w' |= φ EN ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ )>.
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply enl_bind_r_eq...
  Qed.

  Theorem enr_state_bind_r{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EN done {fun '(r,σ) => R r σ}  ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ EN ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ ]>.
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply enr_bind_r...
    intros [y σ'] * HR...
  Qed.

  Theorem enr_state_bind_r_eq{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w w' r σ' φ ψ,
      <[ {interp_state h t σ}, w |= φ EN done= {(r,σ')} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= φ EN ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ ]>.
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply enr_bind_r_eq...
  Qed.
  
  (*| Bind lemmas for [AU] |*)
  Theorem aul_state_bind_r{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AU AX done {fun '(r,σ) => R r σ} ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ AU ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ )>.  
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply aul_bind_r...
    intros [y σ'] * HR...
  Qed.

  Theorem aul_state_bind_r_eq{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ AU AX done= {(x',σ')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= φ AU ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ )>.  
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply aul_bind_r...
    intros [y σ''] * [Heq ->]; inv Heq...
  Qed.
  
  Theorem aur_state_bind_r{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AU AX done {fun '(r,σ) => R r σ} ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ AU ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ ]>.  
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply aur_bind_r...
    intros [y σ'] * HR...
  Qed.

  Theorem aur_state_bind_r_eq{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ AU AX done= {(x',σ')} w' ]> ->
      <[ {interp_state h (k x') σ'}, w' |= φ AU ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ ]>.  
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply aur_bind_r...
    intros [y σ''] * [Heq ->]; inv Heq...
  Qed.
  
  (*| Bind lemmas for [EU] |*)
  Theorem eul_state_bind_r{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EU EX done {fun '(r,σ) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <( {interp_state h (k r) σ}, w |= φ EU ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ )>.
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    apply eul_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] * HR...
  Qed.

  Theorem eul_state_bind_r_eq{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ EU EX done= {(x',σ')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= φ EU ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ )>.
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply eul_bind_r... 
    intros [y σ''] * [Heq ->]; inv Heq... 
  Qed.
  
  Theorem eur_state_bind_r{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EU EX done {fun '(r,σ) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <[ {interp_state h (k r) σ}, w |= φ EU ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ ]>.
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    apply eur_bind_r with (R:=fun '(x, σ) => R x σ)...
    intros [y σ'] * HR...
  Qed.

  Theorem eur_state_bind_r_eq{X Y}: forall (t: ictree E Y) (k: Y -> ictree E X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ EU EX done= {(x',σ')} w' ]> ->
      <[ {interp_state h (k x') σ'}, w' |= φ EU ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ ]>.
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply eur_bind_r... 
    intros [y σ''] * [Heq ->]; inv Heq... 
  Qed.

  (*| Bind lemma for [AG] |*)
  Theorem ag_state_bind_r{X Y}: forall (t: ictree E X) w (k: X -> ictree E Y) φ R,
      <[ {interp_state h t σ}, w |= φ AU AX done {fun '(r, σ) => R r σ} ]> ->
      (forall (x: X) σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= AG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= AG φ )>.
  Proof with auto with ticl.
    intros.
    rewrite interp_state_bind.
    apply ag_bind_r with (R:=fun '(r, σ) => R r σ)...
    intros [y σ'] * HR...
  Qed.
  
  Theorem ag_state_bind_r_eq{X Y}: forall (t: ictree E X) w w' (k: X -> ictree E Y) φ x' σ',
      <[ {interp_state h t σ}, w |= φ AU AX done= {(x',σ')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= AG φ )> ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= AG φ )>.
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply ag_bind_r...
    intros [y σ''] * [Heq HR]; inv Heq...    
  Qed.
  
  (*| Bind lemma for [EG] |*)
  Theorem eg_state_bind_r{X Y}: forall (t: ictree E X) w (k: X -> ictree E Y) R φ,
      <[ {interp_state h t σ}, w |= φ EU EX done {fun '(r, σ) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <( {interp_state h (k r) σ}, w |= EG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= EG φ )>.
  Proof with auto with ticl.
    intros.
    rewrite interp_state_bind.
    apply eg_bind_r with (R:=fun '(r, σ) => R r σ)...
    intros [y σ'] * HR...
  Qed.

  Theorem eg_state_bind_r_eq{X Y}: forall (t: ictree E X) w w' (k: X -> ictree E Y) φ x' σ',
      <[ {interp_state h t σ}, w |= φ EU EX done= {(x',σ')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= EG φ )> ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= EG φ )>.
  Proof with eauto with ticl.
    intros.
    rewrite interp_state_bind.
    eapply eg_bind_r...
    intros [y σ''] * [Heq HR]; inv Heq...    
  Qed.
  
  (*| Iter lemmas for [AN] |*)
  Theorem anl_state_iter{X I} Ri (Rv: relation I) (i: I) w
    (k: I -> ictree E (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AN ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AN done
                      {fun '(lr, σ') w' => 
                         exists (i': I), lr = inl i' /\ Ri i' σ' w' /\ Rv i' i}]>) ->
    <( {interp_state h (ICtree.iter k i) σ}, w |= φ AN ψ )>.
  Proof with auto with ticl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    generalize dependent σ.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    rewrite interp_state_unfold_iter.
    destruct (H _ _ _ Hi).
    - now eapply ticll_bind_l.
    - eapply anl_bind_r with
        (R:=fun '(lr, σ') w' =>
              exists i' : I, lr = inl i' /\ Ri i' σ' w' /\ Rv i' i)... 
      intros [[i' | r] σ'] w'.            
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.        
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  Theorem anr_state_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ictree E (I + X))
    (φ: ticllW W) (ψ: ticlrW W (X * Σ)):
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
    <[ {interp_state h (ICtree.iter k i) σ}, w |= φ AN ψ ]>.
  Proof with auto with ticl.
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
    (k: I -> ictree E (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ EN ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ EN done
                      {fun '(lr, σ') w' => 
                         exists (i': I), lr = inl i' /\ Ri i' σ' w' /\ Rv i' i}]>) ->
    <( {interp_state h (ICtree.iter k i) σ}, w |= φ EN ψ )>.
  Proof with auto with ticl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    generalize dependent σ.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    rewrite interp_state_unfold_iter.
    destruct (H _ _ _ Hi).
    - now eapply ticll_bind_l.
    - apply enr_done in H0 as (Hφ & [[l | r] σ'] & Heqt & i' & Hinv & HRi & HRv); inv Hinv.
      rewrite Heqt, bind_ret_l, sb_guard.
      apply HindWf...
  Qed.

  Theorem enr_state_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ictree E (I + X)) φ ψ:
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
    <[ {interp_state h (ICtree.iter k i) σ}, w |= φ EN ψ ]>.
  Proof with auto with ticl.
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
    (k: I -> ictree E (I + X)) (φ ψ: ticllW W):
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
    <( {interp_state h (ICtree.iter k i) σ}, w |= φ AU ψ )>.
  Proof with auto with ticl.
    unfold iter, MonadIter_ictree.
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
    - now apply ticll_bind_l.
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

  Theorem aul_state_iter_next{X I} R (i: I) w (k: I -> ictree E (I + X)) φ ψ:
    <[ {interp_state h (k i) σ}, w |= φ AU AX done {fun '(lr, σ) w => exists i, lr = inl i /\ not_done w /\ R i σ w} ]> ->
    (forall (i: I) σ w, R i σ w -> not_done w -> <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>) ->
    <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>.
  Proof with auto with ticl.
    unfold iter, MonadIter_ictree.
    intros.
    rewrite unfold_iter.
    apply aul_state_bind_r with (R:=(fun lr σ w => exists i, lr = inl i /\ not_done w /\ R i σ w))...
    intros ? ? ? (i' & -> & Hd & HR).
    rewrite interp_state_tau, sb_guard...
  Qed.

  Theorem aul_state_iter_next_eq{X I} (i i': I) w w' σ' (k: I -> ictree E (I + X)) φ ψ:
    <[ {interp_state h (k i) σ}, w |= φ AU AX done= {(inl i', σ')} w' ]> ->
    not_done w' ->
    <( {interp_state h (iter k i') σ'}, w' |= φ AU ψ )> ->
    <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>.
  Proof with auto with ticl.
    unfold iter, MonadIter_ictree.
    intros.
    rewrite unfold_iter.
    eapply aul_state_bind_r_eq.
    - apply H.
    - cbn.
      rewrite interp_state_tau, sb_guard...
  Qed.
  
  Theorem aur_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ictree E (I + X)) (φ: ticllW W) (ψ: ticlrW W (X * Σ)):
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
  Proof with auto with ticl.
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
    unfold iter, MonadIter_ictree.
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
    - apply ticlr_an_au. 
  Qed.

  Theorem aur_state_iter_next{X I} R (i: I) w (k: I -> ictree E (I + X)) φ ψ:
    <[ {interp_state h (k i) σ}, w |= φ AU AX done {fun '(lr, σ) w => exists i, lr = inl i /\ not_done w /\ R i σ w} ]> ->
    (forall (i: I) σ w, R i σ w -> not_done w -> <[ {interp_state h (iter k i) σ}, w |= φ AU ψ ]>) ->
    <[ {interp_state h (iter k i) σ}, w |= φ AU ψ ]>.
  Proof with auto with ticl.
    unfold iter, MonadIter_ictree.
    intros.
    rewrite unfold_iter.
    apply aur_state_bind_r with (R:=(fun lr σ w => exists i, lr = inl i /\ not_done w /\ R i σ w))...
    intros ? ? ? (i' & -> & Hd & HR).
    rewrite interp_state_tau, sb_guard...
  Qed.

  Theorem aur_state_iter_next_eq{X I} (i i': I) w w' σ' (k: I -> ictree E (I + X)) φ ψ:
    <[ {interp_state h (k i) σ}, w |= φ AU AX done= {(inl i', σ')} w' ]> ->
    not_done w' ->
    <[ {interp_state h (iter k i') σ'}, w' |= φ AU ψ ]> ->
    <[ {interp_state h (iter k i) σ}, w |= φ AU ψ ]>.
  Proof with auto with ticl.
    unfold iter, MonadIter_ictree.
    intros.
    rewrite unfold_iter.
    eapply aur_state_bind_r_eq.
    - apply H.
    - cbn.
      rewrite interp_state_tau, sb_guard...
  Qed.

  (*| Iter lemmas for [EU] |*)
  Lemma eul_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ictree E (I + X)) (φ ψ: ticllW W):
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
  Proof with auto with ticl.
    unfold iter, MonadIter_ictree.
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
    - apply ticll_bind_l...
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

  Theorem eur_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w (k: I -> ictree E (I + X)) (φ: ticllW W) (ψ: ticlrW W (X * Σ)):
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
  Proof with auto with ticl.
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
    unfold iter, MonadIter_ictree.
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
    - apply ticlr_en_eu.
  Qed.

  (*| Iter lemma for [AG] |*)
  Typeclasses Transparent sbisim.
  Lemma ag_state_iter{X I} R i w (k: I -> ictree E (I + X)) φ:
    not_done w ->
    R i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <( {interp_state h (iter k i) σ}, w |= φ )> /\
        <[ {interp_state h (k i) σ}, w |= AX (φ AU AX done
                    {fun '(lr, σ') w' =>
                       exists (i': I), lr = inl i' /\ not_done w' /\ R i' σ' w'}) ]>) ->
    <( {interp_state h (ICtree.iter k i) σ}, w |= AG φ )>.
  Proof with auto with ticl.
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
  Lemma eg_state_iter{X I} R (i: I) w (k: I -> ictree E (I + X)) φ:
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
  Proof with auto with ticl.
    unfold iter, MonadIter_ictree.
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
    (k: I -> ictree E (I + X)) (φ ψ: ticllW W):
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
    (k: I -> ictree E (I + X)) (φ: ticllW W) (ψ: ticlrW W (X * Σ)):
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
    <[ {interp_state h (ICtree.iter k i) σ}, w |= φ AU ψ ]>.
  Proof.
    intros.
    eapply aur_state_iter with Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.
  
  (*| Iter with ranking function [f] for EU |*)
  Lemma eul_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ictree E (I + X)) (φ ψ: ticllW W):
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
    <( {interp_state h (ICtree.iter k i) σ}, w |= φ EU ψ )>.
  Proof.
    intros.
    eapply eul_state_iter with Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.

  Theorem eur_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat)(i: I) w
    (k: I -> ictree E (I + X)) (φ: ticllW W) (ψ: ticlrW W (X * Σ)):
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

(* Lemmas for [stateE] handler [h_stateW] *)
Section StateELemmas.
  (* S: State, s: initial state *)
  Context {S: Type} (s: S).

  Lemma anr_get: forall (w: WorldW S) ψ R,
      R (s,s) w ->
      <( {Ret (s, s)}, {w} |= ψ )> ->
      <[ {instr_stateE get s}, w |= ψ AN done R ]>.
  Proof with eauto with ticl.
    intros.
    unfold instr_stateE.
    rewrite interp_state_get.
    apply anr_done...
  Qed.

  Lemma axr_get: forall (w: WorldW S) R,
      not_done w ->
      R (s,s) w ->
      <[ {instr_stateE get s}, w |= AX done R ]>.
  Proof with eauto with ticl.
    intros.
    unfold instr_stateE.
    rewrite interp_state_get.
    apply axr_ret... 
  Qed.

  Lemma aur_get: forall (w: WorldW S) ψ R,
      not_done w ->
      R (s,s) w ->
      <[ {instr_stateE get s}, w |= ψ AU AX done R ]>.
  Proof with eauto with ticl.
    intros.
    cleft.
    apply axr_get...
  Qed.
  
  Lemma aur_put: forall (s': S) (w: WorldW S) ψ R,
      <( {log s'}, {w} |= ψ )> ->
      R (tt, s') (Obs (Log s') tt) ->
      <[ {instr_stateE (put s') s}, w |= ψ AU AX done R ]>.
  Proof with eauto with ticl.
    intros.
    unfold instr_stateE.
    rewrite interp_state_put.
    eapply aur_log...
    - cleft; apply axr_ret...
    - now apply ticll_bind_l.
  Qed.

  Lemma enr_get: forall (w: WorldW S) ψ R,
      R (s,s) w ->
      <( {Ret (s, s)}, {w} |= ψ )> ->
      <[ {instr_stateE get s}, w |= ψ EN done R ]>.
  Proof with eauto with ticl.
    intros.
    unfold instr_stateE.
    rewrite interp_state_get.
    apply enr_done...
  Qed.

  Lemma exr_get: forall (w: WorldW S) R,
      not_done w ->
      R (s,s) w ->
      <[ {instr_stateE get s}, w |= EX done R ]>.
  Proof with eauto with ticl.
    intros.
    unfold instr_stateE.
    rewrite interp_state_get.
    apply exr_ret... 
  Qed.
  
  Lemma eur_put: forall (s': S) (w: WorldW S) ψ R,
      <( {log s'}, {w} |= ψ )> ->
      R (tt, s') (Obs (Log s') tt) ->
      <[ {instr_stateE (put s') s}, w |= ψ EU EX done R ]>.
  Proof with eauto with ticl.
    intros.
    unfold instr_stateE.
    rewrite interp_state_put.
    eapply eur_log...
    - cleft; apply exr_ret...
    - now apply ticll_bind_l.
  Qed.
End StateELemmas.
