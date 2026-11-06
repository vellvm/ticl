From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Events.Writer
  CTree.Trace
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
Notation ticllW W := (ticll (writerE W)).
Notation ticlrW W X := (ticlr (writerE W) X).
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
      <( {interp_state h t σ}, w |=L φ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |=L φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    now apply ticll_bind_l.
  Qed.

  (** Ret lemma for [interp_state] and suffix [ret] *)
  Theorem axr_state_ret{X}: forall R (x: X) w,
      R (σ, x) w ->
      not_done w ->
      <( {interp_state h (Ret x: ctree E B X) σ}, w |=R ret R )>.
  Proof.
    intros.
    rewrite interp_state_ret.
    apply ret_ret; eauto with ticl.
  Qed.
  
  (** Ret lemma for [interp_state] and prefix [AU] *)

  (** An indexed endpoint establishes [AU] at an interpreted return. *)
  Theorem au_state_ret{X} {b : bool}: forall (x: X) (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b) w,
      (entails _ b (<( ψ )>) (Ret (σ, x): ctreeW W B (Σ * X)) (w)) ->
      (entails _ b (<( φ AU ψ )>) (interp_state h (Ret x: ctree E B X) σ) (w)).
  Proof.
    intros.
    cleft.
    now rewrite interp_state_ret.
  Qed.
  
  (** Bind lemma for [interp_state] and prefix [AN] *)
  
  Theorem ticl_state_bind_ret {X Y} {b : bool}
    (t : ctree E B Y) (k : Y -> ctree E B X) w
    (p : ticl_at (writerE W) (Σ * X) b)
    (R : Y -> Σ -> WorldW W -> Prop) :
    entails (Σ * Y) true (CRet (fun '(s,y) => R y s))
      (interp_state h t σ) w ->
    (forall y s w', R y s w' ->
      entails (Σ * X) b p (interp_state h (k y) s) w') ->
    entails (Σ * X) b p (interp_state h (CTree.bind t k) σ) w.
  Proof.
    intros Hret Hk; rewrite interp_state_bind.
    eapply (ticl_bind_ret (b:=b)) with (R:=fun '(s,y) => R y s).
    - exact Hret.
    - intros [s y] w' HR; exact (Hk y s w' HR).
  Qed.

  Theorem ticl_state_bind_ret_eq {X Y} {b : bool}
    (t : ctree E B Y) (k : Y -> ctree E B X) w
    (p : ticl_at (writerE W) (Σ * X) b) r σ' w' :
    entails (Σ * Y) true
      (CRet (fun result z => (σ',r) = result /\ w' = z))
      (interp_state h t σ) w ->
    entails (Σ * X) b p (interp_state h (k r) σ') w' ->
    entails (Σ * X) b p (interp_state h (CTree.bind t k) σ) w.
  Proof.
    intros Hret Hk.
    eapply (ticl_state_bind_ret (b:=b)) with
      (R:=fun y s z => (σ',r) = (s,y) /\ w' = z).
    - eapply ret_impl_ticl; [intros [s y] z HR; exact HR|exact Hret].
    - intros y s z [Heq Hw]; inversion Heq; subst; exact Hk.
  Qed.

  (** Bind lemma for [interp_state] and suffix [AN] *)
  Theorem an_state_bind_r{X Y} {b : bool}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b) R,
      (entails _ true (<( ret {fun '(σ, x) => R x σ} )>) (interp_state h t σ) (w)) ->
      (forall x σ w, R x σ w -> (entails _ b (<( φ AN ψ )>) (interp_state h (k x) σ) (w))) ->
      (entails _ b (<( φ AN ψ )>) (interp_state h (x <- t ;; k x) σ) (w)).  
  Proof.
    intros; eapply (ticl_state_bind_ret (b:=b)); eauto.
  Qed.

  (** Bind lemma for [interp_state] and prefix [AN] *)
  Theorem an_state_bind_l{X Y} {b : bool}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b) R,
      (entails _ true (<( φ AN ret {fun '(σ, x) => R x σ} )>) (interp_state h t σ) (w)) ->
      (forall x σ w, R x σ w -> (entails _ b (<( ψ )>) (interp_state h (k x) σ) (w))) ->
      (entails _ b (<( φ AN ψ )>) (interp_state h (x <- t ;; k x) σ) (w)).  
  Proof.
    intros.
    rewrite interp_state_bind.
    apply (an_bind_l (b:=b)) with (R:=fun '(σ, x) => R x σ); eauto with ticl.
    intros [σ' y] w' HR; eauto with ticl.
  Qed.
  
  (** Convenience bind lemma for [interp_state] and suffix [AN], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem an_state_bind_r_eq{X Y} {b : bool}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b) r σ',
      (entails _ true (<( ret= {(σ', r)} w' )>) (interp_state h t σ) (w)) ->
      (entails _ b (<( φ AN ψ )>) (interp_state h (k r) σ') (w')) ->
      (entails _ b (<( φ AN ψ )>) (interp_state h (x <- t ;; k x) σ) (w)).  
  Proof.
    intros; eapply (ticl_state_bind_ret_eq (b:=b)); eauto.
  Qed.

  (** Convenience bind lemma for [interp_state] and prefix [AN], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem an_state_bind_l_eq{X Y} {b : bool}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b) r σ',
      (entails _ true (<( φ AN ret= {(σ', r)} w' )>) (interp_state h t σ) (w)) ->
      (entails _ b (<( ψ )>) (interp_state h (k r) σ') (w')) ->
      (entails _ b (<( φ AN ψ )>) (interp_state h (x <- t ;; k x) σ) (w)).  
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply (an_bind_l (b:=b)) with (R:=fun p w_ => (σ', r) = p /\ w' = w_).
    - exact H.
    - intros [σ_ y] w_ (Hinv & HR); inv Hinv; subst; eauto with ticl.
  Qed.
  
  (** Bind lemma for [interp_state] and suffix [EN] *)
  
  (** Convenience bind lemma for [interp_state] and suffix [EN], does not require the [R] postcondition if [t] is deterministic. *)

  (** Bind lemma for [interp_state] and prefix [EN] *)
  Theorem en_state_bind_r{X Y} {b : bool}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b) R,
      (entails _ true (<( ret {fun '(σ, r) => R r σ} )>) (interp_state h t σ) (w)) ->
      (forall x σ w, R x σ w -> (entails _ b (<( φ EN ψ )>) (interp_state h (k x) σ) (w))) ->
      (entails _ b (<( φ EN ψ )>) (interp_state h (x <- t ;; k x) σ) (w)).
  Proof.
    intros; eapply (ticl_state_bind_ret (b:=b)); eauto.
  Qed.

  (** Convenience bind lemma for [interp_state] and suffix [EN], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem en_state_bind_r_eq{X Y} {b : bool}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w w' r σ' (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b),
      (entails _ true (<( ret= {(σ', r)} w' )>) (interp_state h t σ) (w)) ->
      (entails _ b (<( φ EN ψ )>) (interp_state h (k r) σ') (w')) ->
      (entails _ b (<( φ EN ψ )>) (interp_state h (x <- t ;; k x) σ) (w)).
  Proof.
    intros; eapply (ticl_state_bind_ret_eq (b:=b)); eauto.
  Qed.

  (** Visible branch iff lemma for [interp_state] and suffix [AN] *)
  Lemma an_state_brS{X} {b : bool}: forall {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) σ w (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b),
      (entails _ b (<( φ AN ψ )>) (interp_state h (BrS c k) σ) (w)) <->
        (entails _ false (<( φ )>) (interp_state h (BrS c k) σ) (w))
        /\ (forall (y: Y), (entails _ b (<( ψ )>) (interp_state h (k y) σ) (w))).
  Proof.
    intros.
    rewrite interp_state_brS.
    apply (an_brS (b:=b) c _ y).
  Qed.

  (** Hidden branch lemma for [interp_state] and suffix [AN]: all successors of all
      interpreted branches satisfy [ψ], and at least one branch can step. *)
  Lemma an_state_br{X} {b : bool}: forall {Y} (c: B Y) (k: Y -> ctree E B X) σ w (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b),
      (entails _ false (<( φ )>) (interp_state h (Br c k) σ) (w)) ->
      (exists y, can_step (interp_state h (k y) σ) w) ->
      (forall y t' w', |interp_state h (k y) σ, w| ↦ |t', w'| -> (entails _ b (<( ψ )>) (t') (w'))) ->
      (entails _ b (<( φ AN ψ )>) (interp_state h (Br c k) σ) (w)).
  Proof.
    intros * Hφ Hs Hk.
    rewrite interp_state_br in *.
    change (Monad.bind (mbr c) ?f) with (CTree.bind (branch c : ctreeW W B Y) f) in *.
    rewrite bind_branch in *.
    apply (an_br (b:=b)); [exact Hφ | |].
    - destruct Hs as (y & Hs); exists y; now apply can_step_guard.
    - intros y t' w' TR; rewrite ktrans_guard in TR; eauto with ticl.
  Qed.
  
  (** Bind lemma for [interp_state] and prefix [AU] *)

  (** Convenience bind lemma for [interp_state] and prefix [AU], does not require the [R] postcondition if [t] is deterministic. *)
  
  (** Bind lemma for [interp_state] and suffix [AU] *)
  Theorem au_state_bind_r{X Y} {b : bool}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b) R,
      (entails _ true (<( φ AU ret {fun '(σ, r) => R r σ} )>) (interp_state h t σ) (w)) ->
      (forall x σ w, R x σ w -> (entails _ b (<( φ AU ψ )>) (interp_state h (k x) σ) (w))) ->
      (entails _ b (<( φ AU ψ )>) (interp_state h (x <- t ;; k x) σ) (w)).  
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply (u_bind_r (b:=b) Q_A); eauto with ticl.
    intros [σ' y] * HR; eauto with ticl.
  Qed.

  (** Convenience bind lemma for [interp_state] and suffix [AU], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem au_state_bind_r_eq{X Y} {b : bool}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b) x' σ' w',
      (entails _ true (<( φ AU ret= {(σ', x')} w' )>) (interp_state h t σ) (w)) ->
      (entails _ b (<( φ AU ψ )>) (interp_state h (k x') σ') (w')) ->
      (entails _ b (<( φ AU ψ )>) (interp_state h (x <- t ;; k x) σ) (w)).  
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply (u_bind_r_eq (b:=b) Q_A); eauto with ticl.
  Qed.
  
  (** Bind lemma for [interp_state] and suffix [EU] *)

  (** Convenience bind lemma for [interp_state] and suffix [EU], does not require the [R] postcondition if [t] is deterministic. *)
  
  (** Bind lemma for [interp_state] and prefix [EU] *)
  Theorem eu_state_bind_r{X Y} {b : bool}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b) R,
      (entails _ true (<( φ EU ret {fun '(σ, r) => R r σ} )>) (interp_state h t σ) (w)) ->
      (forall r σ w, R r σ w -> (entails _ b (<( φ EU ψ )>) (interp_state h (k r) σ) (w))) ->
      (entails _ b (<( φ EU ψ )>) (interp_state h (x <- t ;; k x) σ) (w)).
  Proof.
    intros.
    rewrite interp_state_bind.
    apply (u_bind_r (b:=b) Q_E) with (R:=fun '(σ, x) => R x σ); eauto with ticl.
    intros [σ' y] * HR; eauto with ticl.
  Qed.

  (** Convenience bind lemma for [interp_state] and prefix [EU], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem eu_state_bind_r_eq{X Y} {b : bool}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b) x' σ' w',
      (entails _ true (<( φ EU ret= {(σ', x')} w' )>) (interp_state h t σ) (w)) ->
      (entails _ b (<( φ EU ψ )>) (interp_state h (k x') σ') (w')) ->
      (entails _ b (<( φ EU ψ )>) (interp_state h (x <- t ;; k x) σ) (w)).
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply (u_bind_r_eq (b:=b) Q_E); eauto with ticl.
  Qed.

  (** Bind lemma for [interp_state] and [AG], unfolds the [AG] to an [AU] on [t] and an [AG] on the continuation [k r]. 
      Intuitively, this lemma extracts a finite prefix [t] from [x <- t; k x] and then applies the [AG] on the continuation [k x].
  *)
  Theorem ag_state_bind_r{X Y}: forall (t: ctree E B X) w (k: X -> ctree E B Y) φ R,
      <( {interp_state h t σ}, w |=R φ AU ret {fun '(σ, r) => R r σ} )> ->
      (forall (x: X) σ w, R x σ w -> <( {interp_state h (k x) σ}, w |=L AG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |=L AG φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply ag_bind_r with (R:=fun '(σ, r) => R r σ); auto with ticl.
    intros [σ' y] * HR; auto with ticl.
  Qed.
  
  (** Convenience bind lemma for [interp_state] and prefix [AG], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem ag_state_bind_r_eq{X Y}: forall (t: ctree E B X) w w' (k: X -> ctree E B Y) φ x' σ',
      <( {interp_state h t σ}, w |=R φ AU ret= {(σ', x')} w' )> ->
      <( {interp_state h (k x') σ'}, w' |=L AG φ )> ->
      <( {interp_state h (x <- t ;; k x) σ} , w |=L AG φ )>.
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
      <( {interp_state h t σ}, w |=R φ EU ret {fun '(σ, r) => R r σ} )> ->
      (forall r σ w, R r σ w -> <( {interp_state h (k r) σ}, w |=L EG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |=L EG φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply eg_bind_r with (R:=fun '(σ, r) => R r σ); auto with ticl.
    intros [σ' y] * HR; auto with ticl.
  Qed.

  (** Convenience bind lemma for [interp_state] and [EG], does not require the [R] postcondition if [t] is deterministic. *)
  Theorem eg_state_bind_r_eq{X Y}: forall (t: ctree E B X) w w' (k: X -> ctree E B Y) φ x' σ',
      <( {interp_state h t σ}, w |=R φ EU ret= {(σ', x')} w' )> ->
      <( {interp_state h (k x') σ'}, w' |=L EG φ )> ->
      <( {interp_state h (x <- t ;; k x) σ} , w |=L EG φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    eapply eg_bind_r; eauto with ticl.
    intros [σ'' y] * [Heq HR]; inv Heq; eauto with ticl.    
  Qed.
 
  Theorem n_state_iter_prefix {X I} (q : ticlq)
    (Ri : I -> Σ -> WorldW W -> Prop) (Rv : relation I) (i : I) w
    (k : I -> ctree E B (I + X)) (φ ψ : ticllW W) :
    well_founded Rv -> Ri i σ w ->
    (forall i s w, Ri i s w ->
      entails (Σ * (I + X)) false (Cx q φ ψ) (interp_state h (k i) s) w \/
      entails (Σ * (I + X)) true
        (CRet (fun '(s',lr) w' =>
          exists i', lr = inl i' /\ Ri i' s' w' /\ Rv i' i))
        (interp_state h (k i) s) w) ->
    entails (Σ * X) false (Cx q φ ψ)
      (interp_state h (CTree.iter k i) σ) w.
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
    - eapply (ticl_bind_ret (b:=false)) with
        (R:=fun '(σ', lr) w' =>
          exists i' : I, lr = inl i' /\ Ri i' σ' w' /\ Rv i' i); auto with ticl.
      intros [σ' [i' | r]] w'.
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        apply HindWf; auto with ticl.
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  (** Lift the iter lemma [n_iter_prefix] to state events. *)
  Theorem anl_state_iter{X I} Ri (Rv: relation I) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |=L φ AN ψ )> \/
          <( {interp_state h (k i) σ}, w |=R ret
                      {fun '(σ', lr) w' => 
                         exists (i': I), lr = inl i' /\ Ri i' σ' w' /\ Rv i' i})>) ->
    <( {interp_state h (CTree.iter k i) σ}, w |=L φ AN ψ )>.
  Proof.
    apply (n_state_iter_prefix Q_A).
  Qed.


  (** Lift the iter lemma [n_iter_prefix] to state events. *)
  Theorem enl_state_iter{X I} Ri (Rv: relation I) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |=L φ EN ψ )> \/
          <( {interp_state h (k i) σ}, w |=R ret
                      {fun '(σ', lr) w' => 
                         exists (i': I), lr = inl i' /\ Ri i' σ' w' /\ Rv i' i})>) ->
    <( {interp_state h (CTree.iter k i) σ}, w |=L φ EN ψ )>.
  Proof.
    apply (n_state_iter_prefix Q_E).
  Qed.


  (** A ghost rank may relate the control, concrete state, and observation
      world without being determined by any of them.  This direct-prefix
      rule also permits the body to establish its endpoint before returning. *)
  Theorem u_state_iter_prefix_ghost {X I G} (q : ticlq)
    (Ri : G -> I -> Σ -> WorldW W -> Prop) (ltG : relation G)
    (k : I -> ctree E B (I + X)) (φ ψ : ticllW W) :
    well_founded ltG ->
    (forall g i sigma w, not_done w -> Ri g i sigma w ->
      entails (Σ * (I + X)) false (Cu q φ ψ)
        (interp_state h (k i) sigma) w \/
      entails (Σ * (I + X)) true
        (Cu q φ (CRet (fun '(sigma',lr) w' =>
          exists g' i', lr = inl i' /\ not_done w' /\
            Ri g' i' sigma' w' /\ ltG g' g)))
        (interp_state h (k i) sigma) w) ->
    forall g i sigma w, not_done w -> Ri g i sigma w ->
      entails (Σ * X) false (Cu q φ ψ)
        (interp_state h (CTree.iter k i) sigma) w.
  Proof.
    intros WfG Hbody g.
    induction g as [g IH] using (well_founded_induction WfG).
    intros i sigma w Hd Hi.
    destruct (Hbody g i sigma w Hd Hi) as [Hnow | Hstep];
      rewrite interp_state_unfold_iter.
    - now apply ticll_bind_l.
    - eapply (u_bind_r (b:=false) q) with
        (R:=fun '(sigma',lr) w' =>
          exists g' i', lr = inl i' /\ not_done w' /\
            Ri g' i' sigma' w' /\ ltG g' g).
      + exact Hstep.
      + intros [sigma' lr] w' (g' & i' & Hlr & Hd' & Hi' & Hlt).
        subst lr; rewrite sb_guard.
        exact (IH g' Hlt i' sigma' w' Hd' Hi').
  Qed.

  (** The return-driven ghost rule handles both a decreasing loop-head
      return and a final return satisfying an arbitrary indexed endpoint. *)
  Theorem u_state_iter_ghost {X I G b} (q : ticlq)
    (Ri : G -> I -> Σ -> WorldW W -> Prop) (ltG : relation G)
    (k : I -> ctree E B (I + X)) (φ : ticllW W)
    (ψ : ticl_at (writerE W) (Σ * X) b) :
    well_founded ltG ->
    (forall g i sigma w, not_done w -> Ri g i sigma w ->
      entails (Σ * (I + X)) true
        (Cu q φ (CRet (fun '(sigma',lr) w' =>
          match lr with
          | inl i' => exists g', not_done w' /\ Ri g' i' sigma' w' /\ ltG g' g
          | inr x => entails (Σ * X) b ψ
              (Ret (sigma',x) : ctreeW W B (Σ * X)) w'
          end))) (interp_state h (k i) sigma) w) ->
    forall g i sigma w, not_done w -> Ri g i sigma w ->
      entails (Σ * X) b (Cu q φ ψ)
        (interp_state h (CTree.iter k i) sigma) w.
  Proof.
    intros WfG Hbody g.
    induction g as [g IH] using (well_founded_induction WfG).
    intros i sigma w Hd Hi.
    rewrite interp_state_unfold_iter.
    eapply (u_bind_r (b:=b) q) with
      (R:=fun '(sigma',lr) w' =>
        match lr with
        | inl i' => exists g', not_done w' /\ Ri g' i' sigma' w' /\ ltG g' g
        | inr x => entails (Σ * X) b ψ
            (Ret (sigma',x) : ctreeW W B (Σ * X)) w'
        end).
    - exact (Hbody g i sigma w Hd Hi).
    - intros [sigma' [i' | x]] w'.
      + intros (g' & Hd' & Hi' & Hlt); rewrite sb_guard.
        exact (IH g' Hlt i' sigma' w' Hd' Hi').
      + intro Hexit; cleft; exact Hexit.
  Qed.

  Theorem u_state_iter_prefix {X I} (q : ticlq)
    (Ri : I -> Σ -> WorldW W -> Prop)
    (Rv : relation (I * Σ * WorldW W)) (i : I) w
    (k : I -> ctree E B (I + X)) (φ ψ : ticllW W) :
    well_founded Rv -> not_done w -> Ri i σ w ->
    (forall i s w, not_done w -> Ri i s w ->
      entails (Σ * (I + X)) false (Cu q φ ψ) (interp_state h (k i) s) w \/
      entails (Σ * (I + X)) true
        (Cu q φ (CRet (fun '(s',lr) w' =>
          exists i', lr = inl i' /\ not_done w' /\ Ri i' s' w' /\
            Rv (i',s',w') (i,s,w))))
        (interp_state h (k i) s) w) ->
    entails (Σ * X) false (Cu q φ ψ)
      (interp_state h (CTree.iter k i) σ) w.
  Proof.
    intros WfR Hd Hi Hbody.
    eapply (u_state_iter_prefix_ghost q
      (fun g i s z => g = (i,s,z) /\ Ri i s z) Rv k φ ψ).
    - exact WfR.
    - intros g i' s' w' Hd' [Heq Hinv]; subst g.
      destruct (Hbody i' s' w' Hd' Hinv) as [Hnow | Hstep].
      + left; exact Hnow.
      + right.
        eapply (impl_ticl_until (b:=true) q q eq_refl); [| | exact Hstep].
        * intros t z Hphi; exact Hphi.
        * apply ret_impl_ticl.
          intros [s'' lr] w'' (i'' & Hlr & Hlive & Hinv' & Hlt).
          exists (i'',s'',w''), i''; split; [exact Hlr |].
          split; [exact Hlive |].
          split; [split; [reflexivity | exact Hinv'] | exact Hlt].
    - exact Hd.
    - split; [reflexivity | exact Hi].
  Qed.

  (** Lift the iter lemma [u_iter_prefix] to state events. *)
  Theorem au_state_iter_prefix{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |=L φ AU ψ )> \/
          <( {interp_state h (k i) σ}, w |=R φ AU ret
                      {fun '(σ', lr) (w': WorldW W) =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ Rv (i', σ', w') (i, σ, w)})>) ->
    <( {interp_state h (CTree.iter k i) σ}, w |=L φ AU ψ )>.
  Proof.
    apply (u_state_iter_prefix Q_A).
  Qed.

  (** Lift the iter lemma [u_iter_next] to state events. 
      Intuitively this lemma unfolds one loop iteration [k i] *)

  (** Convenience lemma for [au_state_iter_next], does not require the [R] postcondition if [k i] is deterministic. *)

  (** Lift the liveness split lemma [u_iter_split] to state events. *)
  Theorem aul_state_iter_split{X I} R Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    not_done w ->
    R i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <( {interp_state h (k i) σ}, w |=R φ AU ret
                    {fun '(σ', lr) (w': WorldW W) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ Ri i' σ' w'} )> \/ 
        <( {interp_state h (k i) σ}, w |=R φ AU ret
                    {fun '(σ', lr) (w': WorldW W) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ R i' σ' w'
                             /\ Rv (i', σ', w') (i, σ, w) })>) ->
    (forall i w σ, not_done w -> Ri i σ w -> <( {interp_state h (iter k i) σ}, w |=L φ AU ψ )>) ->
    <( {interp_state h (iter k i) σ}, w |=L φ AU ψ )>.
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
    - apply (u_bind_r (b:=false) Q_A) with (R:=fun '(σ', lr) w' => exists i' : I, lr = inl i' /\ not_done w' /\ Ri i' σ' w'); auto with ticl.
      intros (σ' & [i' | r]) w' (i_ & His & Hd' & HRi); inv His.
      rewrite sb_guard.
      apply Hi; auto with ticl.
    - eapply (u_bind_r (b:=false) Q_A) with
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
    
  Theorem u_state_iter {X I} {b : bool} (q : ticlq)
    (Ri : I -> Σ -> WorldW W -> Prop)
    (Rv : relation (I * Σ * WorldW W)) (i : I) w
    (k : I -> ctree E B (I + X)) (φ : ticllW W)
    (ψ : ticl_at (writerE W) (Σ * X) b) :
    well_founded Rv -> not_done w -> Ri i σ w ->
    (forall i s w, not_done w -> Ri i s w ->
      entails (Σ * (I + X)) true
        (Cu q φ (CRet (fun '(s',lr) w' =>
          match lr with
          | inl i' => not_done w' /\ Ri i' s' w' /\ Rv (i',s',w') (i,s,w)
          | inr r => entails (Σ * X) b ψ
              (Ret (s',r) : ctreeW W B (Σ * X)) w'
          end))) (interp_state h (k i) s) w) ->
    entails (Σ * X) b (Cu q φ ψ)
      (interp_state h (CTree.iter k i) σ) w.
  Proof.
    intros WfR Hd Hi Hbody.
    eapply (u_state_iter_ghost (b:=b) q
      (fun g i s z => g = (i,s,z) /\ Ri i s z) Rv k φ ψ).
    - exact WfR.
    - intros g i' s' w' Hd' [Heq Hinv]; subst g.
      eapply (impl_ticl_until (b:=true) q q eq_refl);
        [| | exact (Hbody i' s' w' Hd' Hinv)].
      + intros t z Hphi; exact Hphi.
      + apply ret_impl_ticl.
        intros [s'' [i'' | x]] w'' Hret.
        * destruct Hret as (Hlive & Hinv' & Hlt).
          exists (i'',s'',w''); split; [exact Hlive |].
          split; [split; [reflexivity | exact Hinv'] | exact Hlt].
        * exact Hret.
    - exact Hd.
    - split; [reflexivity | exact Hi].
  Qed.

  (** Lift the iter lemma [u_iter] to state events. *)
  Theorem au_state_iter{X I} {b : bool} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E B (I + X)) (φ: ticllW W) (ψ: ticl_at (writerE W) (Σ * X) b):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        (entails _ true (<( φ AU ret
                    {fun '(σ', lr) (w': WorldW W) =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
                       | inr r => (entails _ b (<( ψ )>) (Ret (σ', r): ctreeW W B (Σ * X)) (w'))
                       end} )>) (interp_state h (k i) σ) (w))) ->
    (entails _ b (<( φ AU ψ )>) (interp_state h (iter k i) σ) (w)).
  Proof.
    apply (u_state_iter (b:=b) Q_A).
  Qed.

  (** Lift the iter lemma [u_iter_next] to state events. 
      Intuitively this lemma unfolds one loop iteration [k i] *)
  Theorem au_state_iter_next{X I} {b : bool} R (i: I) w (k: I -> ctree E B (I + X)) (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b):
    (entails _ true (<( φ AU ret {fun '(σ, lr) w => exists i, lr = inl i /\ not_done w /\ R i σ w} )>) (interp_state h (k i) σ) (w)) ->
    (forall (i: I) σ w, R i σ w -> not_done w -> (entails _ b (<( φ AU ψ )>) (interp_state h (iter k i) σ) (w))) ->
    (entails _ b (<( φ AU ψ )>) (interp_state h (iter k i) σ) (w)).
  Proof.
    unfold iter, MonadIter_ctree.
    intros.
    rewrite interp_state_unfold_iter.
    apply (u_bind_r (b:=b) Q_A) with (R:=(fun '(σ, lr) w => exists i, lr = inl i /\ not_done w /\ R i σ w)); auto with ticl.
    intros [σ' lr] ? (i' & -> & Hd & HR).
    rewrite sb_guard; auto with ticl.
  Qed.

  (** Convenience lemma for [au_state_iter_next], does not require the [R] postcondition if [k i] is deterministic. *)
  Theorem au_state_iter_next_eq{X I} {b : bool} (i i': I) w w' σ' (k: I -> ctree E B (I + X)) (φ : ticllW W) (ψ : ticl_at (writerE W) (Σ * X) b):
    (entails _ true (<( φ AU ret= {(σ', inl i')} w' )>) (interp_state h (k i) σ) (w)) ->
    not_done w' ->
    (entails _ b (<( φ AU ψ )>) (interp_state h (iter k i') σ') (w')) ->
    (entails _ b (<( φ AU ψ )>) (interp_state h (iter k i) σ) (w)).
  Proof.
    unfold iter, MonadIter_ctree.
    intros.
    rewrite interp_state_unfold_iter.
    eapply (u_bind_r_eq (b:=b) Q_A).
    - apply H.
    - cbn.
      rewrite sb_guard; auto with ticl.
  Qed.

  (** Lift the iter lemma [u_iter_prefix] to state events. *)
  Lemma eu_state_iter_prefix{X I} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |=L φ EU ψ )> \/
          <( {interp_state h (k i) σ}, w |=R φ EU ret
                      {fun '(σ', lr) w' =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ Rv (i', σ', w') (i, σ, w)})>) ->
    <( {interp_state h (iter k i) σ}, w |=L φ EU ψ )>.
  Proof.
    apply (u_state_iter_prefix Q_E).
  Qed.

  (** Lift the iter lemma [u_iter] to state events. *)
  Theorem eu_state_iter{X I} {b : bool} Ri (Rv: relation (I * Σ * WorldW W)) (i: I) w 
    (k: I -> ctree E B (I + X)) (φ: ticllW W) (ψ: ticl_at (writerE W) (Σ * X) b):
    well_founded Rv ->
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        (entails _ true (<( φ EU ret
                    {fun '(σ', lr) w' =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' σ' w' /\ Rv (i', σ', w') (i, σ, w)
                       | inr r => (entails _ b (<( ψ )>) (Ret (σ', r): ctreeW W B (Σ * X)) (w'))
                       end} )>) (interp_state h (k i) σ) (w))) ->
    (entails _ b (<( φ EU ψ )>) (interp_state h (iter k i) σ) (w)).
  Proof.
    apply (u_state_iter (b:=b) Q_E).
  Qed.

  (** Lift the iter lemma [ag_iter] to state events. *)
  Lemma ag_state_iter{X I} R i w (k: I -> ctree E B (I + X)) (φ : ticllW W):
    not_done w ->
    R i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <( {interp_state h (iter k i) σ}, w |=L φ )> /\
        <( {interp_state h (k i) σ}, w |=R AX (φ AU ret
                    {fun '(σ', lr) w' =>
                       exists (i': I), lr = inl i' /\ not_done w' /\ R i' σ' w'}) )>) ->
    <( {interp_state h (CTree.iter k i) σ}, w |=L AG φ )>.
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
      now apply ticl_not_done in H1'.
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
        apply (au_stuck (b:=true)) in HAN; cdestruct HAN; exfalso; eapply can_step_stuck; eauto.
  Qed.

  (** Continuation-aware invariance: pending observations retain the actual
      next iteration, rather than a detached body ending in [Ret]. *)
  Lemma ag_state_iter_logs {X I : Type}
    (Inv : I -> Σ -> Prop) (k : I -> ctree E B (I + X))
    (phi : ticl (writerE W) None) :
    (forall i sigma, Inv i sigma ->
      exists i' sigma' logs,
        logs <> List.nil /\
        interp_state h (k i) sigma ~ emit_list (B:=B) logs (Ret (sigma', @inl I X i')) /\
        Inv i' sigma') ->
    (forall (o : W) (t : ctreeW W B (Σ * X)) w,
      not_done w -> entails (Σ * X) false phi t (Obs (Log o) tt) ->
      entails (Σ * X) false phi (Vis (Log o) (fun _ => t)) w) ->
    (forall i sigma w, Inv i sigma -> not_done w ->
      entails (Σ * X) false phi (interp_state h (CTree.iter k i) sigma) w) ->
    forall i sigma w, Inv i sigma -> not_done w ->
      entails (Σ * X) false (Cg Q_A phi) (interp_state h (CTree.iter k i) sigma) w.
  Proof.
    intros Hbody Hlog Hboundary.
    assert (Hloop : forall i sigma, Inv i sigma ->
      exists i' sigma' logs, logs <> List.nil /\
        interp_state h (CTree.iter k i) sigma ~
          emit_list logs (interp_state h (CTree.iter k i') sigma') /\ Inv i' sigma').
    { intros i sigma Hinv.
      destruct (Hbody i sigma Hinv) as (i' & sigma' & logs & Hne & Hrun & Hinv').
      exists i', sigma', logs; split; [exact Hne|]; split; [|exact Hinv'].
      rewrite interp_state_unfold_iter, Hrun, emit_list_ret_bind.
      apply emit_list_sbisim, sb_guard. }
    assert (Hpref : forall pending i sigma w, Inv i sigma -> not_done w ->
      entails (Σ * X) false phi (emit_list pending (interp_state h (CTree.iter k i) sigma)) w).
    { induction pending as [|o pending IH]; intros i sigma w Hinv Hw.
      - apply Hboundary; assumption.
      - rewrite emit_list_cons; apply Hlog; [exact Hw|].
        apply IH; [exact Hinv|constructor]. }
    assert (Hsuffix : forall (t : ctreeW W B (Σ * X)) w,
      (exists i sigma pending, Inv i sigma /\ not_done w /\
        t ~ emit_list pending (interp_state h (CTree.iter k i) sigma)) ->
      entails (Σ * X) false (Cg Q_A phi) t w).
    { setoid_rewrite unfold_entails_ag.
      coinduction R CIH; intros t w (i & sigma & pending & Hinv & Hw & Ht).
      assert (Hfront : exists j sigma' o rest, Inv j sigma' /\
        t ~ Vis (Log o) (fun _ => emit_list rest (interp_state h (CTree.iter k j) sigma'))).
      { destruct pending as [|o rest].
        - cbn [emit_list List.fold_right] in Ht.
          destruct (Hloop i sigma Hinv) as (j & sigma' & logs & Hne & Hrun & Hj).
          destruct logs as [|o rest]; [contradiction|].
          exists j, sigma', o, rest; split; [exact Hj|].
          rewrite Ht, Hrun, emit_list_cons; reflexivity.
        - exists i, sigma, o, rest; split; [exact Hinv|].
          rewrite Ht, emit_list_cons; reflexivity. }
      destruct Hfront as (j & sigma' & o & rest & Hj & Efront).
      rewrite Efront; split; [|split].
      - apply Hlog; [exact Hw|]; apply Hpref; [exact Hj|constructor].
      - apply can_step_vis; [exact tt|exact Hw].
      - intros t' w' Htr; apply ktrans_vis in Htr as ([] & -> & Heq & _).
        rewrite <- Heq; apply CIH; exists j, sigma', rest.
        split; [exact Hj|]; split; [constructor|reflexivity]. }
    intros i sigma w Hinv Hw; apply Hsuffix.
    exists i, sigma, List.nil; split; [exact Hinv|]; split; [exact Hw|reflexivity].
  Qed.

  (** Lift the iter lemma [eg_iter] to state events. *)
  Lemma eg_state_iter{X I} R (i: I) w (k: I -> ctree E B (I + X)) (φ : ticllW W):
    R i σ w ->
    not_done w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <( {interp_state h (iter k i) σ}, w |=L φ )> /\
        <( {interp_state h (k i) σ}, w |=R EX (φ EU ret
                    {fun '(σ', lr) w' =>
                       exists (i': I), lr = inl i' /\ not_done w' /\ R i' σ' w'}) )>) ->
    <( {interp_state h (iter k i) σ}, w |=L EG φ )>.
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
        now apply ticl_not_done in H1'.
      + apply (eg_bind_chain φ
                 (fun '(σ', lr) w' => exists i' : I, lr = inl i' /\ not_done w' /\ R i' σ' w')).
        * now apply H1'. 
        * intros [σ' [l | r]] w_ (? & Hinv & Hd & HR); inv Hinv.
          rewrite sb_guard.
          apply CIH; auto with ticl.
  Qed.

  Theorem u_state_iter_prefix_nat {X I} (q : ticlq)
    (Ri : I -> Σ -> WorldW W -> Prop) (f : I -> Σ -> WorldW W -> nat)
    (i : I) w (k : I -> ctree E B (I + X)) (φ ψ : ticllW W) :
    not_done w -> Ri i σ w ->
    (forall i s w, not_done w -> Ri i s w ->
      entails (Σ * (I + X)) false (Cu q φ ψ) (interp_state h (k i) s) w \/
      entails (Σ * (I + X)) true
        (Cu q φ (CRet (fun '(s',lr) w' =>
          exists i', lr = inl i' /\ not_done w' /\ Ri i' s' w' /\
            f i' s' w' < f i s w))) (interp_state h (k i) s) w) ->
    entails (Σ * X) false (Cu q φ ψ)
      (interp_state h (CTree.iter k i) σ) w.
  Proof.
    intros.
    eapply (u_state_iter_prefix q) with
      (Ri:=Ri) (Rv:=ltof _ (fun '(i,s,w) => f i s w)); auto.
    apply well_founded_ltof.
  Qed.

  (** Lift the iter lemma [u_iter_prefix_nat] to state events with ranking function [f]. *)
  Theorem au_state_iter_prefix_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |=L φ AU ψ )> \/
          <( {interp_state h (k i) σ}, w |=R φ AU ret
                      {fun '(σ', lr) (w': WorldW W) =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ f i' σ' w' < f i σ w})>) ->
    <( {interp_state h (iter k i) σ}, w |=L φ AU ψ )>.
  Proof.
    apply (u_state_iter_prefix_nat Q_A).
  Qed.

  (** Lift the liveness split lemma [u_iter_split] to state events with ranking function [f]. *)
  Theorem aul_state_iter_split_nat{X I} R Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    not_done w ->
    R i σ w ->
    (forall (i: I) σ w,
        not_done w ->
        R i σ w ->
        <( {interp_state h (k i) σ}, w |=R φ AU ret
                    {fun '(σ', lr) (w': WorldW W) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ Ri i' σ' w'} )> \/ 
        <( {interp_state h (k i) σ}, w |=R φ AU ret
                    {fun '(σ', lr) (w': WorldW W) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ R i' σ' w'
                             /\ f i' σ' w' < f i σ w })>) ->
    (forall i w σ, not_done w -> Ri i σ w -> <( {interp_state h (iter k i) σ}, w |=L φ AU ψ )>) ->
    <( {interp_state h (iter k i) σ}, w |=L φ AU ψ )>.
  Proof.     
    intros.
    eapply aul_state_iter_split with R Ri (ltof _ (fun '(i, σ, w) => f i σ w)); auto.
    apply well_founded_ltof.
  Qed.
  
  Theorem u_state_iter_nat {X I} {b : bool} (q : ticlq)
    (Ri : I -> Σ -> WorldW W -> Prop) (f : I -> Σ -> WorldW W -> nat)
    (i : I) w (k : I -> ctree E B (I + X)) (φ : ticllW W)
    (ψ : ticl_at (writerE W) (Σ * X) b) :
    not_done w -> Ri i σ w ->
    (forall i s w, not_done w -> Ri i s w ->
      entails (Σ * (I + X)) true
        (Cu q φ (CRet (fun '(s',lr) w' =>
          match lr with
          | inl i' => not_done w' /\ Ri i' s' w' /\ f i' s' w' < f i s w
          | inr r => entails (Σ * X) b ψ
              (Ret (s',r) : ctreeW W B (Σ * X)) w'
          end))) (interp_state h (k i) s) w) ->
    entails (Σ * X) b (Cu q φ ψ)
      (interp_state h (CTree.iter k i) σ) w.
  Proof.
    intros.
    eapply (u_state_iter (b:=b) q) with
      (Ri:=Ri) (Rv:=ltof _ (fun '(i,s,w) => f i s w)); auto.
    apply well_founded_ltof.
  Qed.

  (** Lift the iter lemma [u_iter_nat] to state events with ranking function [f]. *)
  Theorem au_state_iter_nat{X I} {b : bool} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E B (I + X)) (φ: ticllW W) (ψ: ticl_at (writerE W) (Σ * X) b):
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        (entails _ true (<( φ AU ret
                                       {fun '(σ', lr) (w': WorldW W) =>
                                          match lr with
                                          | inl i' => not_done w'
                                                     /\ Ri i' σ' w'
                                                     /\ f i' σ' w' < f i σ w
                                          | inr r => (entails _ b (<( ψ )>) (Ret (σ', r): ctreeW W B (Σ * X)) (w'))
                                          end} )>) (interp_state h (k i) σ) (w))) ->
    (entails _ b (<( φ AU ψ )>) (interp_state h (CTree.iter k i) σ) (w)).
  Proof.
    apply (u_state_iter_nat (b:=b) Q_A).
  Qed.
  
  (** Lift direct-body existential iteration to state events with ranking function [f]. *)
  Lemma eu_state_iter_prefix_nat{X I} Ri (f: I -> Σ -> WorldW W -> nat) (i: I) w
    (k: I -> ctree E B (I + X)) (φ ψ: ticllW W):
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        <( {interp_state h (k i) σ}, w |=L φ EU ψ )> \/
          <( {interp_state h (k i) σ}, w |=R φ EU ret
                      {fun '(σ', lr) w' =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ Ri i' σ' w'
                               /\ f i' σ' w' < f i σ w})>) ->
    <( {interp_state h (CTree.iter k i) σ}, w |=L φ EU ψ )>.
  Proof.
    apply (u_state_iter_prefix_nat Q_E).
  Qed.

  (** Lift return-based existential iteration to state events with ranking function [f]. *)
  Theorem eu_state_iter_nat{X I} {b : bool} Ri (f: I -> Σ -> WorldW W -> nat)(i: I) w
    (k: I -> ctree E B (I + X)) (φ: ticllW W) (ψ: ticl_at (writerE W) (Σ * X) b):
    not_done w ->
    Ri i σ w ->    
    (forall (i: I) σ w,
        not_done w ->
        Ri i σ w ->
        (entails _ true (<( φ EU ret
                    {fun '(σ', lr) w' =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' σ' w' /\ f i' σ' w' < f i σ w
                       | inr r => (entails _ b (<( ψ )>) (Ret (σ', r): ctreeW W B (Σ * X)) (w'))
                       end} )>) (interp_state h (k i) σ) (w))) ->
    (entails _ b (<( φ EU ψ )>) (interp_state h (iter k i) σ) (w)).
  Proof.
    apply (u_state_iter_nat (b:=b) Q_E).
  Qed.  

End StateLemmas.


(** * Lemmas for [stateE] handler [h_stateW] *)
Section StateELemmas.
  (** S: State, s: initial state *)
  Context {B: Type -> Type} {S: Type} (s: S).


  (** [get] commands terminate in one step and return the initial state. *)
  Lemma axr_get: forall (w: WorldW S) R,
      not_done w ->
      R (s,s) w ->
      <( {instr_stateE (get: ctree (stateE S) B S) s}, w |=R ret R )>.
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
      <( {instr_stateE (get: ctree (stateE S) B S) s}, w |=R ψ AU ret R )>.
  Proof.
    intros.
    cleft.
    apply axr_get; eauto with ticl.
  Qed.
  
  (** [put] commands terminate in two steps, first the [log] event is executed and then the [Ret] is executed. *)

  (** After the [log] step, the returned state satisfies the indexed endpoint. *)
  Lemma au_put {b : bool}: forall (s': S) (w: WorldW S) (φ : ticllW S) (ψ : ticl_at (writerE S) (S * unit) b),
      entails unit false φ (log s': ctreeW S B unit) w ->
      entails (S * unit) b ψ (Ret (s', tt): ctreeW S B (S * unit)) (Obs (Log s') tt) ->
      entails (S * unit) b (Cu Q_A φ ψ) (instr_stateE (put s': ctree (stateE S) B unit) s) w.
  Proof.
    intros.
    unfold instr_stateE.
    rewrite interp_state_put.
    apply (ticl_an_au (S * unit) b).
    apply (an_log (b:=b)).
    - assumption.
    - now apply ticll_bind_l.
  Qed.

 
  (** [get] commands terminate in one step and return the initial state. *)
  Lemma eur_get: forall (w: WorldW S) ψ R,
      R (s,s) w ->
      not_done w ->
      <( {instr_stateE (get: ctree (stateE S) B S) s}, w |=R ψ EU ret R )>.
  Proof.
    intros.
    unfold instr_stateE.
    rewrite interp_state_get.
    cleft; eauto with ticl.
    apply ret_ret; eauto with ticl. 
  Qed.

  (** [put] commands terminate in two steps, first the [log] event is executed and then the [Ret] is executed. *)
  Lemma eur_put: forall (s': S) (w: WorldW S) (ψ : ticllW S) (R : S * unit -> WorldW S -> Prop),
      <( {log s': ctreeW S B unit}, {w} |=L ψ )> ->
      R (s', tt) (Obs (Log s') tt) ->
      <( {instr_stateE (put s': ctree (stateE S) B unit) s}, w |=R ψ EU ret R )>.
  Proof.
    intros.
    unfold instr_stateE.
    rewrite interp_state_put.
    eapply (eu_log (b:=true)); eauto with ticl.
    - cleft; apply ret_ret; eauto with ticl.
    - now apply ticll_bind_l.
  Qed.
End StateELemmas.
