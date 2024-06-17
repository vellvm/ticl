From Coinduction Require Import
  coinduction lattice.

From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Interp.State
  CTree.Events.Writer
  CTree.Logic.Trans
  CTree.Logic.Bind
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.EX
  Logic.Ctl.

Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

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

  Notation ctllW W := (ctll (writerE W)).
  
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
  
  Theorem eul_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ EU EN done= {(r, σ')} w' ]> ->
      <( {interp_state h (k r) σ'}, w' |= φ EU ψ )> ->
      <( {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ )>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply eul_bind_r...
  Qed.

  Theorem eur_state_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ ψ r σ',
      <[ {interp_state h t σ}, w |= φ EU EN done= {(r, σ')} w' ]> ->
      <[ {interp_state h (k r) σ'}, w' |= φ EU ψ ]> ->
      <[ {interp_state h (x <- t ;; k x) σ}, w |= φ EU ψ ]>.
  Proof with eauto with ctl.
    intros.
    rewrite interp_state_bind.
    eapply eur_bind_r...
  Qed.

  (*| Bind lemma for [AG] |*)
  Lemma ag_state_bind_r{X Y}: forall (t: ctree E X) w (k: X -> ctree E Y) φ R,
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
  Lemma eg_state_bind_r{X Y}: forall (t: ctree E X) w (k: X -> ctree E Y) R φ,
      <[ {interp_state h t σ}, w |= φ EU EN done {fun '(r, σ) => R r σ} ]> ->
      (forall r σ w, R r σ w -> <( {interp_state h (k r) σ}, w |= EG φ )>) ->
      <( {interp_state h (x <- t ;; k x) σ} , w |= EG φ )>.
  Proof with auto with ctl.
    intros.
    rewrite interp_state_bind.
    apply eg_bind_r with (R:=fun '(r, σ) => R r σ)...
    intros [y σ'] * HR...
  Qed.
  
End StateLemmas.
