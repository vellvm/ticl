From Stdlib Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From TICL Require Import
  Events.Core
  Events.WriterE
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Interp.Core
  ICTree.Interp.State.Mod
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  Logic.Core
  ICTree.Logic.AX
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.

(** ** TICL structural lemmas for ICTrees and the until [AU] and eventually [AF] operators *)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  (** Stuckness lemma for prefix eventually [AU_L] *)
  Lemma aul_stuck: forall w φ ψ,
      <( {ICtree.stuck: ictree E X}, w |= ψ )> <->
      <( {ICtree.stuck: ictree E X}, w |= φ AU ψ )>.
  Proof.
    split; intros * H.
    - now cleft.
    - remember (ICtree.stuck) as S.
      cinduction H; subst.
      + apply Hp.
      + now apply can_step_stuck in Hs.
  Qed.

  (** Stuckness lemma for prefix eventually [AU_R] *)
  Lemma aur_stuck: forall w φ ψ,
      <[ {ICtree.stuck: ictree E X}, w |= ψ ]> <->
      <[ {ICtree.stuck: ictree E X}, w |= φ AU ψ ]>.
  Proof.
    split; intros * H.
    - now cleft.
    - remember (ICtree.stuck) as S.
      cinduction H; subst.
      + apply Hp.
      + now apply can_step_stuck in Hs.
  Qed.

  (** Return iff lemma for prefix eventually [AU_L] *)
  Lemma aul_ret: forall (r: X) w φ ψ,
      <( {Ret r}, w |= ψ \/ φ AN ψ )> <->
      <( {Ret r}, w |= φ AU ψ )>.
  Proof with auto with ticl.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H...
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
      cright; csplit...
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
      <[ {Ret r}, w |= ψ \/ φ AN ψ ]> <->
      <[ {Ret r}, w |= φ AU ψ ]>.
  Proof with auto with ticl.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H...
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
      cright; csplit...
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

  (** Branch iff lemma for prefix eventually [AU_L] *)
  Lemma aul_br: forall n (k: fin' n -> ictree E X) w ψ φ,
      (<( {Br n k}, w |= φ )> \/
         <( {Br n k}, w |= ψ )> /\
           forall (i: fin' n), <( {k i}, w |= ψ AU φ )>) <->
      <( {Br n k}, w |= ψ AU φ )>.
  Proof.
    intros; symmetry.
    rewrite equivl_au_an at 1.
    now rewrite ticll_or, anl_br.
  Qed.

  (** Vis iff emma for prefix eventually [AU_L] *)
  Lemma aul_vis: forall (e: E) (k: encode e -> ictree E X) (_: encode e) w ψ φ,
      (<( {Vis e k}, w |= φ )> \/
         <( {Vis e k}, w |= ψ )> /\
           forall (v: encode e), <( {k v}, {Obs e v} |= ψ AU φ )>) <->
      <( {Vis e k}, w |= ψ AU φ )>.
  Proof.
    intros e k v0 w ψ φ; symmetry.
    rewrite equivl_au_an at 1.
    now rewrite ticll_or, (anl_vis e k v0).
  Qed.

  (** Helper version of [aul_vis] for [AF] = [T AU]*)
  Lemma afl_vis: forall (e: E) (k: encode e -> ictree E X) (_: encode e) w φ,
      <( {Vis e k}, w |= φ )> \/
         (not_done w /\ forall (v: encode e), <( {k v}, {Obs e v} |= AF φ )>) <->
      <( {Vis e k}, w |= AF φ )>.
  Proof.
    intros e k v0 w φ; symmetry.
    rewrite equivl_au_an at 1.
    rewrite ticll_or, (anl_vis e k v0), ticll_now; tauto.
  Qed.

  (** Branch iff lemma for prefix eventually [AU_R] *)
  Lemma aur_br: forall n (k: fin' n -> ictree E X) w ψ φ,
      (<[ {Br n k}, w |= φ ]> \/
         <( {Br n k}, w |= ψ )> /\
           forall (i: fin' n), <[ {k i}, w |= ψ AU φ ]>) <->
      <[ {Br n k}, w |= ψ AU φ ]>.
  Proof.
    intros; symmetry.
    rewrite equivr_au_an at 1.
    now rewrite ticlr_or, anr_br.
  Qed.

  (** Vis iff lemma for prefix eventually [AU_R] *)
  Lemma aur_vis: forall (e: E) (k: encode e -> ictree E X) (_: encode e) w ψ φ,
      (<[ {Vis e k}, w |= φ ]> \/
         <( {Vis e k}, w |= ψ )> /\
           forall (v: encode e), <[ {k v}, {Obs e v} |= ψ AU φ ]>) <->
      <[ {Vis e k}, w |= ψ AU φ ]>.
  Proof.
    intros e k v0 w ψ φ; symmetry.
    rewrite equivr_au_an at 1.
    now rewrite ticlr_or, (anr_vis e k v0).
  Qed.

  (** Helper version of [aur_vis] for [AF] = [T AU]*)
  Lemma afr_vis: forall (e: E) (k: encode e -> ictree E X) (_: encode e) w φ,
      <[ {Vis e k}, w |= φ ]> \/
         (not_done w /\ forall (v: encode e), <[ {k v}, {Obs e v} |= AF φ ]>) <->
      <[ {Vis e k}, w |= AF φ ]>.
  Proof.
    intros e k v0 w φ; symmetry.
    rewrite equivr_au_an at 1.
    rewrite ticlr_or, (anr_vis e k v0), ticll_now; tauto.
  Qed.

  (** Not done lemma for prefix eventually [AU_R] *)
  Lemma aur_not_done: forall φ ψ ξ (t: ictree E X) (w: World E),
      <[ t, w |= φ AU (ψ AN ξ) ]> ->
      not_done w.
  Proof.
    intros.
    cdestruct H; cdestruct H;
      now apply can_step_not_done with t.
  Qed.
End BasicLemmas.
