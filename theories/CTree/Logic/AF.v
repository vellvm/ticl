From Stdlib Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Core
  CTree.Logic.AX
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** ** TICL structural lemmas for ctrees and the until [AU] and eventually [AF] operators *)
Section BasicLemmas.
  Context {E B: Type -> Type} {X: Type}.

  (** Stuckness lemma for prefix eventually [AU_L] *)
  Lemma aul_stuck: forall w φ ψ,
      <( {Stuck: ctree E B X}, w |= ψ )> <->
      <( {Stuck: ctree E B X}, w |= φ AU ψ )>.
  Proof.
    split; intros * H.
    - now cleft.
    - remember (Stuck) as S.
      cinduction H; subst.
      + apply Hp.
      + now apply can_step_stuck in Hs.
  Qed.

  (** Stuckness lemma for prefix eventually [AU_R] *)
  Lemma aur_stuck: forall w φ ψ,
      <[ {Stuck: ctree E B X}, w |= ψ ]> <->
      <[ {Stuck: ctree E B X}, w |= φ AU ψ ]>.
  Proof.
    split; intros * H.
    - now cleft.
    - remember (Stuck) as S.
      cinduction H; subst.
      + apply Hp.
      + now apply can_step_stuck in Hs.
  Qed.

  (** Return iff lemma for prefix eventually [AU_L] *)
  Lemma aul_ret: forall (r: X) w φ ψ,
      <( {Ret r: ctree E B X}, w |= ψ \/ φ AN ψ )> <->
      <( {Ret r: ctree E B X}, w |= φ AU ψ )>.
  Proof.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H; auto with ticl.
      intros t' w' TR.
      apply ticll_not_done in Hp.
      specialize (H _ _ TR).
      inv Hp.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H |- *.
        now cleft.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H |- *.
        now cleft.
    - now cleft.
    - cdestruct H.
      cright; csplit; auto with ticl.
      intros t' w' TR.
      apply ticll_not_done in Hp.
      specialize (H _ _ TR).
      inv Hp.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H |- *.
        now apply aul_stuck in H.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H |- *.
        now apply aul_stuck in H.
  Qed.

  (** Return iff lemma for prefix eventually [AU_R] *)
  Lemma aur_ret: forall (r: X) w φ ψ,
      <[ {Ret r: ctree E B X}, w |= ψ \/ φ AN ψ ]> <->
      <[ {Ret r: ctree E B X}, w |= φ AU ψ ]>.
  Proof.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H; auto with ticl.
      intros t' w' TR.
      apply ticll_not_done in Hp.
      specialize (H _ _ TR).
      inv Hp.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H |- *.
        now cleft.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H |- *.
        now cleft.
    - now cleft.
    - cdestruct H.
      cright; csplit; auto with ticl.
      intros t' w' TR.
      apply ticll_not_done in Hp.
      specialize (H _ _ TR).
      inv Hp.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H |- *.
        now apply aur_stuck in H.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H |- *.
        now apply aur_stuck in H.
  Qed.

  (** Hidden branch lemma for prefix eventually [AU_L]: [Br c k] is not a step,
      so the obligations are on the successors of the branches. *)
  Lemma aul_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      <( {Br c k}, w |= φ )> ->
      (exists y, can_step (k y) w) ->
      (forall y t' w', |k y, w| ↦ |t', w'| -> <( t', w' |= φ AU ψ )>) ->
      <( {Br c k}, w |= φ AU ψ )>.
  Proof.
    intros; cright; now apply anl_br.
  Qed.

  (** Visible branch iff lemma for prefix eventually [AU_L] *)
  Lemma aul_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) w ψ φ,
      (<( {BrS c k}, w |= φ )> \/
         <( {BrS c k}, w |= ψ )> /\
           forall (y: Y), <( {k y}, w |= ψ AU φ )>) <->
      <( {BrS c k}, w |= ψ AU φ )>.
  Proof.
    intros; symmetry.
    rewrite equivl_au_an at 1.
    now rewrite ticll_or, (anl_brS c k y).
  Qed.

  (** Visible step iff lemma for prefix eventually [AU_L] *)
  Lemma aul_step: forall (t: ctree E B X) w ψ φ,
      (<( {Step t}, w |= φ )> \/
         <( {Step t}, w |= ψ )> /\ <( t, w |= ψ AU φ )>) <->
      <( {Step t}, w |= ψ AU φ )>.
  Proof.
    intros; symmetry.
    rewrite equivl_au_an at 1.
    now rewrite ticll_or, anl_step.
  Qed.

  (** Vis iff emma for prefix eventually [AU_L] *)
  Lemma aul_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) (_: Y) w ψ φ,
      (<( {Vis e k}, w |= φ )> \/
         <( {Vis e k}, w |= ψ )> /\
           forall (v: Y), <( {k v}, {Obs e v} |= ψ AU φ )>) <->
      <( {Vis e k}, w |= ψ AU φ )>.
  Proof.
    intros Y e k v0 w ψ φ; symmetry.
    rewrite equivl_au_an at 1.
    now rewrite ticll_or, (anl_vis e k v0).
  Qed.

  (** Helper version of [aul_vis] for [AF] = [T AU]*)
  Lemma afl_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) (_: Y) w φ,
      <( {Vis e k}, w |= φ )> \/
         (not_done w /\ forall (v: Y), <( {k v}, {Obs e v} |= AF φ )>) <->
      <( {Vis e k}, w |= AF φ )>.
  Proof.
    intros Y e k v0 w φ; symmetry.
    rewrite equivl_au_an at 1.
    rewrite ticll_or, (anl_vis e k v0), ticll_now; tauto.
  Qed.

  (** Hidden branch lemma for suffix eventually [AU_R] *)
  Lemma aur_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      <( {Br c k}, w |= φ )> ->
      (exists y, can_step (k y) w) ->
      (forall y t' w', |k y, w| ↦ |t', w'| -> <[ t', w' |= φ AU ψ ]>) ->
      <[ {Br c k}, w |= φ AU ψ ]>.
  Proof.
    intros; cright; now apply anr_br.
  Qed.

  (** Visible branch iff lemma for suffix eventually [AU_R] *)
  Lemma aur_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) w ψ φ,
      (<[ {BrS c k}, w |= φ ]> \/
         <( {BrS c k}, w |= ψ )> /\
           forall (y: Y), <[ {k y}, w |= ψ AU φ ]>) <->
      <[ {BrS c k}, w |= ψ AU φ ]>.
  Proof.
    intros; symmetry.
    rewrite equivr_au_an at 1.
    now rewrite ticlr_or, (anr_brS c k y).
  Qed.

  (** Visible step iff lemma for suffix eventually [AU_R] *)
  Lemma aur_step: forall (t: ctree E B X) w ψ φ,
      (<[ {Step t}, w |= φ ]> \/
         <( {Step t}, w |= ψ )> /\ <[ t, w |= ψ AU φ ]>) <->
      <[ {Step t}, w |= ψ AU φ ]>.
  Proof.
    intros; symmetry.
    rewrite equivr_au_an at 1.
    now rewrite ticlr_or, anr_step.
  Qed.

  (** Vis iff lemma for suffix eventually [AU_R] *)
  Lemma aur_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) (_: Y) w ψ φ,
      (<[ {Vis e k}, w |= φ ]> \/
         <( {Vis e k}, w |= ψ )> /\
           forall (v: Y), <[ {k v}, {Obs e v} |= ψ AU φ ]>) <->
      <[ {Vis e k}, w |= ψ AU φ ]>.
  Proof.
    intros Y e k v0 w ψ φ; symmetry.
    rewrite equivr_au_an at 1.
    now rewrite ticlr_or, (anr_vis e k v0).
  Qed.

  (** Helper version of [aur_vis] for [AF] = [T AU]*)
  Lemma afr_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) (_: Y) w φ,
      <[ {Vis e k}, w |= φ ]> \/
         (not_done w /\ forall (v: Y), <[ {k v}, {Obs e v} |= AF φ ]>) <->
      <[ {Vis e k}, w |= AF φ ]>.
  Proof.
    intros Y e k v0 w φ; symmetry.
    rewrite equivr_au_an at 1.
    rewrite ticlr_or, (anr_vis e k v0), ticll_now; tauto.
  Qed.

  (** Not done lemma for suffix eventually [AU_R] *)
  Lemma aur_not_done: forall φ ψ ξ (t: ctree E B X) (w: World E),
      <[ t, w |= φ AU (ψ AN ξ) ]> ->
      not_done w.
  Proof.
    intros.
    cdestruct H; cdestruct H;
      now apply can_step_not_done with t.
  Qed.
End BasicLemmas.
