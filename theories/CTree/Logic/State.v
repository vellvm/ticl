From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
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
  Logic.Core
  CTree.Interp.State.Mod
  CTree.Events.State.

From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Program.Tactics.

Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** * State lemmas *)
(** This section contains the main lemmas about state events [stateE] and Ticl operators applied on state events.
    Note the [ctrees] pair order: [interp_state h t σ : ctree F B (Σ * X)], the state comes first. *)

(** Notation for instrumented ctree formulas *)
Abbreviation ticllW W := (ticll (writerE W)).
Abbreviation ticlrW W := (ticlr (writerE W)).
Abbreviation WorldW W := (World (writerE W)).

Section StateLemmas.
  (** E: Uniterpreted effect (to interpret)
     B: Branch signature
     Σ: Interpretation state (concrete domain)
     W: Observation state (ghost domain)
  *)
  Context {E B: Type -> Type} {Σ W: Type}
    (** [h]: Semantic handler with instrumentation *)
    (h: E ~> stateT Σ (ctreeW W B))
    (** [σ]: Initial state *)
    (σ: Σ).
  
  (** Lift the [ticll_bind_l] lemma to state events. *)
  Theorem ticll_state_bind_l{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) (φ: ticllW W) w,
      <( {interp_state h t σ}, w |= φ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    now apply ticll_bind_l.
  Qed.

  (** Ret lemma for [interp_state] and suffix [ret] *)
  Theorem axr_state_ret{X}: forall R (x: X) w,
      R (σ, x) w ->
      not_done w ->
      <[ {interp_state h (Ret x: ctree E B X) σ}, w |= ret R ]>.  
  Proof.
    intros.
    rewrite interp_state_ret.
    apply ret_ret; eauto with ticl.
  Qed.
  
  (** Ret lemma for [interp_state] and prefix [AU] *)
  Theorem aur_state_ret{X}: forall R (x: X) φ w,
      R (σ, x) w ->
      not_done w ->
      <[ {interp_state h (Ret x: ctree E B X) σ}, w |= φ AU ret R ]>.  
  Proof.
    intros.
    cleft.
    apply axr_state_ret; eauto with ticl.
  Qed.

  (** Ret lemma for [interp_state] and prefix [AU] *)
  Theorem aul_state_ret{X}: forall (x: X) φ ψ w,
      not_done w ->
      <( {Ret (σ, x): ctreeW W B (Σ * X)}, w |= ψ )> ->
      <( {interp_state h (Ret x: ctree E B X) σ}, w |= φ AU ψ )>.
  Proof.
    intros.
    cleft.
    now rewrite interp_state_ret.
  Qed.
  
  (** Bind lemma for [interp_state] and prefix [AN] *)
  Theorem anl_state_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ {interp_state h t σ}, w |= ret {fun '(σ, x) => R x σ} ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ AN ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ )>.  
  Proof.
    intros.
    rewrite interp_state_bind.
    apply anl_bind_r with (R:=fun '(σ, x) => R x σ); eauto with ticl.
    intros [σ' y] w' HR; eauto with ticl.
  Qed.    
  
  (** Bind lemma for [interp_state] and suffix [AN] *)
  Theorem anr_state_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ {interp_state h t σ}, w |= ret {fun '(σ, x) => R x σ} ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ AN ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ ]>.  
  Proof.
    intros.
    rewrite interp_state_bind.
    apply anr_bind_r with (R:=fun '(σ, x) => R x σ); eauto with ticl.
    intros [σ' y] w' HR; eauto with ticl.
  Qed.

  (** Bind lemma for [interp_state] and prefix [AN] *)
  Theorem anr_state_bind_l{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AN ret {fun '(σ, x) => R x σ} ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ ]>.  
  Proof.
    intros.
    rewrite interp_state_bind.
    apply anr_bind_l with (R:=fun '(σ, x) => R x σ); eauto with ticl.
    intros [σ' y] w' HR; eauto with ticl.
  Qed.
  
  (** Convenience bind lemma for [interp_state] and suffix [AN], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem anr_state_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= ret= {(σ', r)} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= φ AN ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ ]>.  
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply anr_bind_r_eq; eauto with ticl.
  Qed.

  (** Convenience bind lemma for [interp_state] and prefix [AN], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem anr_state_bind_l_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ AN ret= {(σ', r)} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AN ψ ]>.  
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply anr_bind_l with (R:=fun p w_ => (σ', r) = p /\ w' = w_).
    - exact H.
    - intros [σ_ y] w_ (Hinv & HR); inv Hinv; subst; eauto with ticl.
  Qed.
  
  (** Bind lemma for [interp_state] and suffix [EN] *)
  Theorem enl_state_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ {interp_state h t σ}, w |= ret {fun '(σ, r) => R r σ}  ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ EN ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply enl_bind_r; eauto with ticl.
    intros [σ' y] * HR; eauto with ticl.
  Qed.
  
  (** Convenience bind lemma for [interp_state] and suffix [EN], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem enl_state_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= ret= {(σ', r)} w' ]> ->
      <( {interp_state h (k r) σ'}, w' |= φ EN ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply enl_bind_r_eq; eauto with ticl.
  Qed.

  (** Bind lemma for [interp_state] and prefix [EN] *)
  Theorem enr_state_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ {interp_state h t σ}, w |= ret {fun '(σ, r) => R r σ}  ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ EN ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ ]>.
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply enr_bind_r; eauto with ticl.
    intros [σ' y] * HR; eauto with ticl.
  Qed.

  (** Convenience bind lemma for [interp_state] and suffix [EN], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem enr_state_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' r σ' φ ψ,
      <[ {interp_state h t σ}, w |= ret= {(σ', r)} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= φ EN ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EN ψ ]>.
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply enr_bind_r_eq; eauto with ticl.
  Qed.

  (** Visible branch iff lemma for [interp_state] and suffix [AN] *)
  Lemma anr_state_brS{X}: forall {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) σ w φ ψ,
      <[ {interp_state h (BrS c k) σ}, w |= φ AN ψ ]> <->
        <( {interp_state h (BrS c k) σ}, w |= φ)>
        /\ (forall (y: Y), <[ {interp_state h (k y) σ}, w |= ψ ]>).
  Proof.
    intros.
    rewrite interp_state_brS.
    apply (anr_brS c _ y).
  Qed.

  (** Hidden branch lemma for [interp_state] and suffix [AN]: all successors of all
      interpreted branches satisfy [ψ], and at least one branch can step. *)
  Lemma anr_state_br{X}: forall {Y} (c: B Y) (k: Y -> ctree E B X) σ w φ ψ,
      <( {interp_state h (Br c k) σ}, w |= φ )> ->
      (exists y, can_step (interp_state h (k y) σ) w) ->
      (forall y t' w', |interp_state h (k y) σ, w| ↦ |t', w'| -> <[ t', w' |= ψ ]>) ->
      <[ {interp_state h (Br c k) σ}, w |= φ AN ψ ]>.
  Proof.
    intros * Hφ Hs Hk.
    rewrite interp_state_br in *.
    change (Monad.bind (mbr c) ?f) with (CTree.bind (branch c : ctreeW W B Y) f) in *.
    rewrite bind_branch in *.
    apply anr_br; [exact Hφ | |].
    - destruct Hs as (y & Hs); exists y; now apply can_step_guard.
    - intros y t' w' TR; rewrite ktrans_guard in TR; eauto with ticl.
  Qed.
  
  (** Bind lemma for [interp_state] and prefix [AU] *)
  Theorem aul_state_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AU ret {fun '(σ, r) => R r σ} ]> ->
      (forall x σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= φ AU ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ )>.  
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply aul_bind_r; eauto with ticl.
    intros [σ' y] * HR; eauto with ticl.
  Qed.

  (** Convenience bind lemma for [interp_state] and prefix [AU], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem aul_state_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ AU ret= {(σ', x')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= φ AU ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ )>.  
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply aul_bind_r_eq; eauto with ticl.
  Qed.
  
  (** Bind lemma for [interp_state] and suffix [AU] *)
  Theorem aur_state_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ AU ret {fun '(σ, r) => R r σ} ]> ->
      (forall x σ w, R x σ w -> <[ {interp_state h (k x) σ}, w |= φ AU ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ ]>.  
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply aur_bind_r; eauto with ticl.
    intros [σ' y] * HR; eauto with ticl.
  Qed.

  (** Convenience bind lemma for [interp_state] and suffix [AU], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem aur_state_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ AU ret= {(σ', x')} w' ]> ->
      <[ {interp_state h (k x') σ'}, w' |= φ AU ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ AU ψ ]>.  
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply aur_bind_r_eq; eauto with ticl.
  Qed.
  
  (** Bind lemma for [interp_state] and suffix [EU] *)
  Theorem eul_state_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EU ret {fun '(σ, r) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <( {interp_state h (k r) σ}, w |= φ EU ψ )>) ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply eul_bind_r with (R:=fun '(σ, x) => R x σ); eauto with ticl.
    intros [σ' y] * HR; eauto with ticl.
  Qed.

  (** Convenience bind lemma for [interp_state] and suffix [EU], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem eul_state_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ EU ret= {(σ', x')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= φ EU ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply eul_bind_r_eq; eauto with ticl.
  Qed.
  
  (** Bind lemma for [interp_state] and prefix [EU] *)
  Theorem eur_state_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ R,
      <[ {interp_state h t σ}, w |= φ EU ret {fun '(σ, r) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <[ {interp_state h (k r) σ}, w |= φ EU ψ ]>) ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ ]>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply eur_bind_r with (R:=fun '(σ, x) => R x σ); eauto with ticl.
    intros [σ' y] * HR; eauto with ticl.
  Qed.

  (** Convenience bind lemma for [interp_state] and prefix [EU], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem eur_state_bind_r_eq{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w φ ψ x' σ' w',
      <[ {interp_state h t σ}, w |= φ EU ret= {(σ', x')} w' ]> ->
      <[ {interp_state h (k x') σ'}, w' |= φ EU ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ ]>.
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply eur_bind_r_eq; eauto with ticl.
  Qed.

  (** Bind lemma for [interp_state] and [AG], unfolds the [AG] to an [AU] on [t] and an [AG] on the continuation [k r]. 
      Intuitively, this lemma extracts a finite prefix [t] from [x <- t; k x] and then applies the [AG] on the continuation [k x].
  *)
  Theorem ag_state_bind_r{X Y}: forall (t: ctree E B X) w (k: X -> ctree E B Y) φ R,
      <[ {interp_state h t σ}, w |= φ AU ret {fun '(σ, r) => R r σ} ]> ->
      (forall (x: X) σ w, R x σ w -> <( {interp_state h (k x) σ}, w |= AG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= AG φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply ag_bind_r with (R:=fun '(σ, r) => R r σ); auto with ticl.
    intros [σ' y] * HR; auto with ticl.
  Qed.
  
  (** Convenience bind lemma for [interp_state] and prefix [AG], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem ag_state_bind_r_eq{X Y}: forall (t: ctree E B X) w w' (k: X -> ctree E B Y) φ x' σ',
      <[ {interp_state h t σ}, w |= φ AU ret= {(σ', x')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= AG φ )> ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= AG φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply ag_bind_r with (R:=fun p w_ => (σ', x') = p /\ w' = w_).
    - exact H.
    - intros [σ'' y] * [Heq HR]; inv Heq; eauto with ticl.    
  Qed.
  
  (** Bind lemma for [interp_state] and [EG], unfolds the [EG] to an [EU] on [t] and an [EG] on the continuation [k r]. 
      Intuitively, this lemma extracts a finite prefix [t] from [x <- t; k x] and then applies the [EG] on the continuation [k x].
  *)
  Theorem eg_state_bind_r{X Y}: forall (t: ctree E B X) w (k: X -> ctree E B Y) R φ,
      <[ {interp_state h t σ}, w |= φ EU ret {fun '(σ, r) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <( {interp_state h (k r) σ}, w |= EG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= EG φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply eg_bind_r with (R:=fun '(σ, r) => R r σ); auto with ticl.
    intros [σ' y] * HR; auto with ticl.
  Qed.

  (** Convenience bind lemma for [interp_state] and [EG], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem eg_state_bind_r_eq{X Y}: forall (t: ctree E B X) w w' (k: X -> ctree E B Y) φ x' σ',
      <[ {interp_state h t σ}, w |= φ EU ret= {(σ', x')} w' ]> ->
      <( {interp_state h (k x') σ'}, w' |= EG φ )> ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= EG φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply eg_bind_r; eauto with ticl.
    intros [σ'' y] * [Heq HR]; inv Heq; eauto with ticl.    
  Qed.
 
  (** Lift the iter lemma [anl_iter] to state events. *)
  Theorem anl_state_iter{X I} Ri (Rv: relation I) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AN ψ )> \/
          <[ {interp_state h (k i) σ}, w |= ret
                      {fun '(σ', lr) w' => 
                         exists (i': I), lr = inl i' /\ Ri i' σ' w' /\ Rv i' i}]>) ->
    <( {interp_state h (CTree.iter k i) σ}, w |= φ AN ψ )>.
  Proof.
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
        (R:=fun '(σ', lr) w' =>
              exists i' : I, lr = inl i' /\ Ri i' σ' w' /\ Rv i' i); auto with ticl. 
      intros [σ' [i' | r]] w'.            
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.        
        apply HindWf; auto with ticl.
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.


  (** Lift the iter lemma [enl_iter] to state events. *)
  Theorem enl_state_iter{X I} Ri (Rv: relation I) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ EN ψ )> \/
          <[ {interp_state h (k i) σ}, w |= ret
                      {fun '(σ', lr) w' => 
                         exists (i': I), lr = inl i' /\ Ri i' σ' w' /\ Rv i' i}]>) ->
    <( {interp_state h (CTree.iter k i) σ}, w |= φ EN ψ )>.
  Proof.
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
    - eapply enl_bind_r with
        (R:=fun '(σ', lr) w' =>
              exists i' : I, lr = inl i' /\ Ri i' σ' w' /\ Rv i' i); auto with ticl.
      intros [σ' [i' | r]] w'.
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        apply HindWf; auto with ticl.
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.


  (** Lift the iter lemma [aul_iter] to state events. *)
  Theorem aul_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AU ret
                      {fun '(σ', lr) (w': WorldW W) =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ Rv (i', σ', w') (i, σ, w)}]>) ->
    <( {interp_state h (CTree.iter k i) σ}, w |= φ AU ψ )>.
  Proof.
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
        (R:=fun '(σ', lr) w' =>
              exists i' : I, lr = inl i'
                        /\ not_done w'
                        /\ Ri i' σ' w'
                        /\ Rv (i', σ', w') (i, σ, w)); auto with ticl. 
      intros [σ' [i' | r]] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, σ', w') as y.
        replace j with (fst (fst y)) in Hi' |- * by now subst.
        replace σ' with (snd (fst y)) in Hi' |- * by now subst.
        replace w' with (snd y) in Hd', Hi' |- * by now subst.
        apply HindWf; auto with ticl. 
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  (** Lift the iter lemma [aul_iter_next] to state events. 
      Intuitively this lemma unfolds one loop iteration [k i] *)
  Theorem aul_state_iter_next{X I} R (i: I) w (k: I -> ctree E B (I + X)) φ ψ:
    <[ {interp_state h (k i) σ}, w |= φ AU ret {fun '(σ, lr) w => exists i, lr = inl i /\ not_done w /\ R i σ w} ]> ->
    (forall (i: I) σ w, R i σ w -> not_done w -> <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>) ->
    <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>.
  Proof.
    unfold iter, MonadIter_ctree.
    intros.
    rewrite interp_state_unfold_iter.
    apply aul_bind_r with (R:=(fun '(σ, lr) w => exists i, lr = inl i /\ not_done w /\ R i σ w)); auto with ticl.
    intros [σ' lr] ? (i' & -> & Hd & HR).
    rewrite sb_guard; auto with ticl.
  Qed.

  (** Convenience lemma for [aul_state_iter_next], does not require the [R] postcondition if [k i] is deterministic. *)
  Theorem aul_state_iter_next_eq{X I} (i i': I) w w' σ' (k: I -> ctree E B (I + X)) φ ψ:
    <[ {interp_state h (k i) σ}, w |= φ AU ret= {(σ', inl i')} w' ]> ->
    not_done w' ->
    <( {interp_state h (iter k i') σ'}, w' |= φ AU ψ )> ->
    <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>.
  Proof.
    unfold iter, MonadIter_ctree.
    intros.
    rewrite interp_state_unfold_iter.
    eapply aul_bind_r_eq.
    - apply H.
    - cbn.
      rewrite sb_guard; auto with ticl.
  Qed.

  (** Lift the liveness split lemma [aul_iter_split] to state events. *)
  Theorem aul_state_iter_split{X I} R Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    not_done w ->
    R i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ AU ret
                    {fun '(σ', lr) (w': WorldW W) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ Ri i' σ' w'} ]> \/ 
        <[ {interp_state h (k i) σ}, w |= φ AU ret
                    {fun '(σ', lr) (w': WorldW W) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ R i' σ' w'
                             /\ Rv (i', σ', w') (i, σ, w) }]>) ->
    (forall i w σ, not_done w -> Ri i σ w -> <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>) -> 
    <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>.
  Proof.
    unfold iter, MonadIter_ctree.
    remember (i, σ, w) as P.
    replace i with (fst (fst P)) by now subst.
    replace σ with (snd (fst P)) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w σ.
    intros WfR Hd HR H Hi.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as ((i, σ), w); cbn in *. 
    rename H into HindWf.
    intros.
    destruct (H _ _ _ Hd HR); rewrite interp_state_unfold_iter.
    - apply aul_bind_r with (R:=fun '(σ', lr) w' => exists i' : I, lr = inl i' /\ not_done w' /\ Ri i' σ' w'); auto with ticl.
      intros (σ' & [i' | r]) w' (i_ & His & Hd' & HRi); inv His.
      rewrite sb_guard.
      apply Hi; auto with ticl.
    - eapply aul_bind_r with
        (R:=fun '(σ', lr) (w': WorldW W) =>
              exists i' : I, lr = inl i' /\ not_done w'/\ R i' σ' w' /\ Rv (i', σ', w') (i, σ, w)); auto with ticl. 
      intros (σ' & [i' | r]) w' (j & Hinv & Hd' & HR' & HRv'); inv Hinv.
      rewrite sb_guard.
      remember (j, σ', w') as y.
      replace j with (fst (fst y)) in HR' |- * by now subst.
      replace σ' with (snd (fst y)) in HR' |- * by now subst.
      replace w' with (snd y) in HR', Hd' |- * by now subst.      
      apply HindWf; auto with ticl.
  Qed.
    
  (** Lift the iter lemma [aur_iter] to state events. *)
  Theorem aur_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E B (I + X)) (φ: ticllW W) (ψ: ticlrW W (Σ * X)):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ AU ret
                    {fun '(σ', lr) (w': WorldW W) =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
                       | inr r => <[ {Ret (σ', r): ctreeW W B (Σ * X)}, w' |= ψ ]>
                       end} ]>) ->
    <[ {interp_state h (iter k i) σ}, w |= φ AU ψ ]>.
  Proof.
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
      (R:=fun '(σ', lr) w' =>
             match lr with
             | inl i' => not_done w' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
             | inr r => <[ {Ret (σ', r): ctreeW W B (Σ * X)}, w' |= ψ ]>
             end); auto with ticl.
    intros [σ' [i' | r]] w'; auto with ticl.
    - intros (Hd' & Hi' & Hv). 
      rewrite sb_guard.
      remember (i', σ', w') as y.
      replace i' with (fst (fst y)) in Hi' |- * by now subst.
      replace σ' with (snd (fst y)) in Hi' |- * by now subst.
      replace w' with (snd y) in Hi', Hd' |- * by now subst.
      apply HindWf; auto with ticl.
    - intro Hexit; cleft; exact Hexit.
  Qed.

  (** Lift the iter lemma [aur_iter_next] to state events. 
      Intuitively this lemma unfolds one loop iteration [k i] *)
  Theorem aur_state_iter_next{X I} R (i: I) w (k: I -> ctree E B (I + X)) φ ψ:
    <[ {interp_state h (k i) σ}, w |= φ AU ret {fun '(σ, lr) w => exists i, lr = inl i /\ not_done w /\ R i σ w} ]> ->
    (forall (i: I) σ w, R i σ w -> not_done w -> <[ {interp_state h (iter k i) σ}, w |= φ AU ψ ]>) ->
    <[ {interp_state h (iter k i) σ}, w |= φ AU ψ ]>.
  Proof.
    unfold iter, MonadIter_ctree.
    intros.
    rewrite interp_state_unfold_iter.
    apply aur_bind_r with (R:=(fun '(σ, lr) w => exists i, lr = inl i /\ not_done w /\ R i σ w)); auto with ticl.
    intros [σ' lr] ? (i' & -> & Hd & HR).
    rewrite sb_guard; auto with ticl.
  Qed.

  (** Convenience lemma for [aur_state_iter_next], does not require the [R] postcondition if [k i] is deterministic. *)
  Theorem aur_state_iter_next_eq{X I} (i i': I) w w' σ' (k: I -> ctree E B (I + X)) φ ψ:
    <[ {interp_state h (k i) σ}, w |= φ AU ret= {(σ', inl i')} w' ]> ->
    not_done w' ->
    <[ {interp_state h (iter k i') σ'}, w' |= φ AU ψ ]> ->
    <[ {interp_state h (iter k i) σ}, w |= φ AU ψ ]>.
  Proof.
    unfold iter, MonadIter_ctree.
    intros.
    rewrite interp_state_unfold_iter.
    eapply aur_bind_r_eq.
    - apply H.
    - cbn.
      rewrite sb_guard; auto with ticl.
  Qed.

  (** Lift the iter lemma [eul_iter] to state events. *)
  Lemma eul_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ EU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ EU ret
                      {fun '(σ', lr) w' =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ Rv (i', σ', w') (i, σ, w)}]>) ->
    <( {interp_state h (iter k i) σ}, w |= φ EU ψ )>.
  Proof.
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
    - apply ticll_bind_l; auto with ticl.
    - eapply eul_bind_r with
        (R:=fun '(σ', lr) w' =>
              exists i' : I, lr = inl i'
                        /\ not_done w'
                        /\ Ri i' σ' w'
                        /\ Rv (i', σ', w') (i, σ, w)); auto with ticl. 
      intros [σ' [i' | r]] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, σ', w') as y.
        replace j with (fst (fst y)) in Hi' |- * by now subst.
        replace σ' with (snd (fst y)) in Hi' |- * by now subst.
        replace w' with (snd y) in Hd', Hi' |- * by now subst.
        apply HindWf; auto with ticl.
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  (** Lift the iter lemma [eur_iter] to state events. *)
  Theorem eur_state_iter{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w 
    (k: I -> ctree E B (I + X)) (φ: ticllW W) (ψ: ticlrW W (Σ * X)):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ EU ret
                    {fun '(σ', lr) w' =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
                       | inr r => <[ {Ret (σ', r): ctreeW W B (Σ * X)}, w' |= ψ ]>
                       end} ]>) ->
    <[ {interp_state h (iter k i) σ}, w |= φ EU ψ ]>.
  Proof.
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
      (R:=fun '(σ', lr) w' =>
            match lr with
            | inl i' => not_done w' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
            | inr r => <[ {Ret (σ', r): ctreeW W B (Σ * X)}, w' |= ψ ]>
             end); auto with ticl.
    intros [σ' [i' | r]] w'; auto with ticl.
    - intros (Hd' & Hi' & Hv). 
      rewrite sb_guard.
      remember (i', σ', w') as y.
      replace i' with (fst (fst y)) in Hi' |- * by now subst.
      replace σ' with (snd (fst y)) in Hi' |- * by now subst.
      replace w' with (snd y) in Hd', Hi' |- * by now subst.
      apply HindWf; auto with ticl.
    - intro Hexit; cleft; exact Hexit.
  Qed.

  (** Lift the iter lemma [ag_iter] to state events. *)
  Lemma ag_state_iter{X I} R i w (k: I -> ctree E B (I + X)) φ:
    not_done w ->
    R i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <( {interp_state h (iter k i) σ}, w |= φ )> /\
        <[ {interp_state h (k i) σ}, w |= AX (φ AU ret
                    {fun '(σ', lr) w' =>
                       exists (i': I), lr = inl i' /\ not_done w' /\ R i' σ' w'}) ]>) ->
    <( {interp_state h (CTree.iter k i) σ}, w |= AG φ )>.
  Proof.
    intros.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    generalize dependent σ.
    coinduction_g RR CIH; intros.
    specialize (H1 _ _ _ H H0) as (Hφ & H1').
    cdestruct H1'.
    split2.
    - now apply Hφ. 
    - rewrite interp_state_unfold_iter.
      destruct Hs as (k' & wk & TRk).
      apply can_step_bind_l with k' wk; auto with ticl.
      specialize (H1' _ _ TRk).
      now apply aur_ret_not_done in H1'.
    - intros t' w' TR.
      rewrite interp_state_unfold_iter in TR.
      apply ktrans_bind_inv in TR as
          [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ag_bind_chain φ
                 (fun '(σ', lr) w' => exists i' : I, lr = inl i' /\ not_done w' /\ R i' σ' w')).
        * now apply H1'. 
        * intros [σ' [l | r]] w_ (? & Hinv & Hd & HR); inv Hinv.
          rewrite sb_guard.
          apply CIH; auto with ticl.
      + (* [k x] returns *)        
        specialize (H1' _ _ TRt0) as HAN.
        apply aur_stuck in HAN; cdestruct HAN; exfalso; eapply can_step_stuck; eauto.
  Qed.

  (** Lift the iter lemma [eg_iter] to state events. *)
  Lemma eg_state_iter{X I} R (i: I) w (k: I -> ctree E B (I + X)) φ:
    R i σ w ->
    not_done w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <( {interp_state h (iter k i) σ}, w |= φ )> /\
        <[ {interp_state h (k i) σ}, w |= EX (φ EU ret
                    {fun '(σ', lr) w' =>
                       exists (i': I), lr = inl i' /\ not_done w' /\ R i' σ' w'}) ]>) ->
    <( {interp_state h (iter k i) σ}, w |= EG φ )>.
  Proof.
    unfold iter, MonadIter_ctree.
    intros.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    generalize dependent σ.
    coinduction_g RR CIH; intros.
    specialize (H1 _ _ _ H0 H) as (Hφ & H1').
    cdestruct H1'.
    split.
    - now apply Hφ. 
    - setoid_rewrite interp_state_unfold_iter.
      exists (pat <- t;; match pat with
                 | (s, inl l) => Guard (interp_state h (CTree.iter k l) s)
                 | (s, inr r) => Ret (s, r)
                  end), w0; split.
      + apply ktrans_bind_l; auto with ticl.
        now apply eur_ret_not_done in H1'.
      + apply (eg_bind_chain φ
                 (fun '(σ', lr) w' => exists i' : I, lr = inl i' /\ not_done w' /\ R i' σ' w')).
        * now apply H1'. 
        * intros [σ' [l | r]] w_ (? & Hinv & Hd & HR); inv Hinv.
          rewrite sb_guard.
          apply CIH; auto with ticl.
  Qed.

  (** Lift the iter lemma [aul_iter_nat] to state events with ranking function [f]. *)
  Theorem aul_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ AU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ AU ret
                      {fun '(σ', lr) (w': WorldW W) =>
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

  (** Lift the liveness split lemma [aul_iter_split] to state events with ranking function [f]. *)
  Theorem aul_state_iter_split_nat{X I} R Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    not_done w ->
    R i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ AU ret
                    {fun '(σ', lr) (w': WorldW W) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ Ri i' σ' w'} ]> \/ 
        <[ {interp_state h (k i) σ}, w |= φ AU ret
                    {fun '(σ', lr) (w': WorldW W) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ R i' σ' w'
                             /\ f i' σ' w' < f i σ w }]>) ->
    (forall i w σ, not_done w -> Ri i σ w -> <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>) ->
    <( {interp_state h (iter k i) σ}, w |= φ AU ψ )>.
  Proof.     
    intros.
    eapply aul_state_iter_split with R Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.
  
  (** Lift the iter lemma [aur_iter_nat] to state events with ranking function [f]. *)
  Theorem aur_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E B (I + X)) (φ: ticllW W) (ψ: ticlrW W (Σ * X)):
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ AU ret
                                       {fun '(σ', lr) (w': WorldW W) =>
                                          match lr with
                                          | inl i' => not_done w'
                                                     /\ Ri i' σ' w'
                                                     /\ f i' σ' w' < f i σ w
                                          | inr r => <[ {Ret (σ', r): ctreeW W B (Σ * X)}, w' |= ψ ]>
                                          end} ]>) ->
    <[ {interp_state h (CTree.iter k i) σ}, w |= φ AU ψ ]>.
  Proof.
    intros.
    eapply aur_state_iter with Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.
  
  (** Lift the iter lemma [eul_iter_nat] to state events with ranking function [f]. *)
  Lemma eul_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |= φ EU ψ )> \/
          <[ {interp_state h (k i) σ}, w |= φ EU ret
                      {fun '(σ', lr) w' =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ f i' σ' w' < f i σ w}]>) ->
    <( {interp_state h (CTree.iter k i) σ}, w |= φ EU ψ )>.
  Proof.
    intros.
    eapply eul_state_iter with Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.

  (** Lift the iter lemma [eur_iter_nat] to state events with ranking function [f]. *)
  Theorem eur_state_iter_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat)(i: I) w
    (k: I -> ctree E B (I + X)) (φ: ticllW W) (ψ: ticlrW W (Σ * X)):
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <[ {interp_state h (k i) σ}, w |= φ EU ret
                    {fun '(σ', lr) w' =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' σ' w' /\ f i' σ' w' < f i σ w
                       | inr r => <[ {Ret (σ', r): ctreeW W B (Σ * X)}, w' |= ψ ]>
                       end} ]>) ->
    <[ {interp_state h (iter k i) σ}, w |= φ EU ψ ]>.
  Proof.
    intros.
    eapply eur_state_iter with Ri (ltof _ (fun '((i, σ), w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.  

End StateLemmas.

(** A state-iteration rule with a well-founded rank on ghost data.  The
    invariant relates that data to the control and concrete state; neither
    the concrete state nor the observation world must determine the rank.
    The proof uses the structural one-iteration and bind laws. *)
Theorem aul_state_iter_ghost {E B: Type -> Type} {Sg W}
  (hh: E ~> stateT Sg (ctreeW W B)) {X I G}
  (Rv: relation G) (Inv: G -> I -> Sg -> Prop)
  (bd: I -> ctree E B (I + X)) (phi psi: ticllW W):
  well_founded Rv ->
  forall (g: G) (i: I) (s: Sg) (w: WorldW W),
    not_done w ->
    Inv g i s ->
    (forall g i s w,
        not_done w ->
        Inv g i s ->
        <( {interp_state hh (bd i) s}, w |= phi AU psi )>
        \/ (exists g' i' s' w',
               not_done w'
               /\ <[ {interp_state hh (bd i) s}, w
                     |= phi AU ret= {(s', inl i')} w' ]>
               /\ Inv g' i' s'
               /\ Rv g' g)) ->
    <( {interp_state hh (CTree.iter bd i) s}, w |= phi AU psi )>.
Proof.
  intros Hwf g.
  induction g as [g IH] using (well_founded_induction Hwf).
  intros i s w Hd Hinv Hbody.
  destruct (Hbody g i s w Hd Hinv)
    as [Hnow | (g' & i' & s' & w' & Hd' & Hstep & Hinv' & Hlt)].
  - rewrite interp_state_unfold_iter; now apply ticll_bind_l.
  - eapply aul_state_iter_next_eq; [exact Hstep | exact Hd' |].
    eapply (IH g'); eauto.
Qed.

(** * Lemmas for [stateE] handler [h_stateW] *)
Section StateELemmas.
  (** S: State, s: initial state *)
  Context {B: Type -> Type} {S: Type} (s: S).


  (** [get] commands terminate in one step and return the initial state. *)
  Lemma axr_get: forall (w: WorldW S) R,
      not_done w ->
      R (s,s) w ->
      <[ {instr_stateE (get: ctree (stateE S) B S) s}, w |= ret R ]>.
  Proof.
    intros.
    unfold instr_stateE.
    rewrite interp_state_get.
    apply ret_ret; eauto with ticl. 
  Qed.

  (** [get] commands terminate eventually, this is a simple consequence of [axr_get]. *)
  Lemma aur_get: forall (w: WorldW S) ψ R,
      not_done w ->
      R (s,s) w ->
      <[ {instr_stateE (get: ctree (stateE S) B S) s}, w |= ψ AU ret R ]>.
  Proof.
    intros.
    cleft.
    apply axr_get; eauto with ticl.
  Qed.
  
  (** [put] commands terminate in two steps, first the [log] event is executed and then the [Ret] is executed. *)
  Lemma aur_put: forall (s': S) (w: WorldW S) ψ R,
      <( {log s': ctreeW S B unit}, {w} |= ψ )> ->
      R (s', tt) (Obs (Log s') tt) ->
      <[ {instr_stateE (put s': ctree (stateE S) B unit) s}, w |= ψ AU ret R ]>.
  Proof.
    intros.
    unfold instr_stateE.
    rewrite interp_state_put.
    eapply aur_log; eauto with ticl.
    - cleft; apply ret_ret; eauto with ticl.
    - now apply ticll_bind_l.
  Qed.

  (** Prefix version: after the [log] step, the returned state satisfies [φ]. *)
  Lemma aul_put: forall (s': S) (w: WorldW S) ψ φ,
      <( {log s': ctreeW S B unit}, {w} |= ψ )> ->
      <( {Ret (s', tt): ctreeW S B (S * unit)}, {Obs (Log s') tt} |= φ )> ->
      <( {instr_stateE (put s': ctree (stateE S) B unit) s}, w |= ψ AU φ )>.
  Proof.
    intros.
    unfold instr_stateE.
    rewrite interp_state_put.
    cright; apply anl_log.
    - cleft; eauto with ticl.
    - now apply ticll_bind_l.
  Qed.

 
  (** [get] commands terminate in one step and return the initial state. *)
  Lemma eur_get: forall (w: WorldW S) ψ R,
      R (s,s) w ->
      not_done w ->
      <[ {instr_stateE (get: ctree (stateE S) B S) s}, w |= ψ EU ret R ]>.
  Proof.
    intros.
    unfold instr_stateE.
    rewrite interp_state_get.
    cleft; eauto with ticl.
    apply ret_ret; eauto with ticl. 
  Qed.

  (** [put] commands terminate in two steps, first the [log] event is executed and then the [Ret] is executed. *)
  Lemma eur_put: forall (s': S) (w: WorldW S) ψ R,
      <( {log s': ctreeW S B unit}, {w} |= ψ )> ->
      R (s', tt) (Obs (Log s') tt) ->
      <[ {instr_stateE (put s': ctree (stateE S) B unit) s}, w |= ψ EU ret R ]>.
  Proof.
    intros.
    unfold instr_stateE.
    rewrite interp_state_put.
    eapply eur_log; eauto with ticl.
    - cleft; apply ret_ret; eauto with ticl.
    - now apply ticll_bind_l.
  Qed.
End StateELemmas.
