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
  CTree.Logic.EX.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.
  
(** * TICL logic lemmas on ctrees and the exists-until [EU] operator *)
Section BasicLemmas.
  Context {E B: Type -> Type} {X: Type}.

  (** A stuck tree satisfies prefix [φ EU ψ] if and only if it satisfies [ψ]. *)
  Lemma eul_stuck: forall w φ ψ,
      <( {Stuck: ctree E B X}, w |= φ EU ψ )> <->
      <( {Stuck: ctree E B X}, w |= ψ )>.
  Proof with auto with ticl.
    split; intros.
    - cdestruct H...
      cdestruct H.
      now apply ktrans_stuck in TR.
    - now cleft. 
  Qed.

  (** A stuck tree satisfies suffix [φ EU ψ] if and only if it satisfies [ψ]. *)
  Lemma eur_stuck: forall w φ ψ,
      <[ {Stuck: ctree E B X}, w |= φ EU ψ ]> <->
      <[ {Stuck: ctree E B X}, w |= ψ ]>.
  Proof with auto with ticl.
    split; intros.
    - cdestruct H...
      cdestruct H.
      now apply ktrans_stuck in TR.
    - now cleft. 
  Qed.

  (** A return tree satisfies prefix [φ EU ψ] if and only if it satisfies [ψ] or [φ EN ψ]. *)
  Lemma eul_ret: forall (r: X) w φ ψ,
      <( {Ret r: ctree E B X}, w |= ψ \/ φ EN ψ )> <->
      <( {Ret r: ctree E B X}, w |= φ EU ψ )>.
  Proof with auto with ticl.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H...
      assert (Hd: not_done w) by now apply ktrans_not_done in TR.
      inv Hd.
      + apply ktrans_done in TR as (-> & ?).
        exists (Stuck), (Done r); split.
        * apply ktrans_done...
        * rewrite H0 in H.
          now cleft.
      + apply ktrans_finish in TR as (-> & ?).
        exists (Stuck), (Finish e v r); split.
        * apply ktrans_finish...
        * rewrite H0 in H.
          now cleft.
    - now cleft.
    - cdestruct H.
      cright; csplit...
      assert (Hd: not_done w) by now apply ktrans_not_done in TR.
      inv Hd.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H.
        apply eul_stuck in H.
        apply ticll_not_done in H; inv H.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H.
        apply eul_stuck in H.
        apply ticll_not_done in H; inv H.
  Qed.

  (** A return tree satisfies suffix [φ EU ψ] if and only if it satisfies [ψ] or [φ EN ψ]. *)
  Lemma eur_ret: forall (r: X) w φ ψ,
      <[ {Ret r: ctree E B X}, w |= ψ \/ φ EN ψ ]> <->
      <[ {Ret r: ctree E B X}, w |= φ EU ψ ]>.
  Proof with auto with ticl.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H...
      assert (Hd: not_done w) by now apply ktrans_not_done in TR.
      inv Hd.
      + apply ktrans_done in TR as (-> & ?).
        exists (Stuck), (Done r); split.
        * apply ktrans_done...
        * rewrite H0 in H.
          now cleft.
      + apply ktrans_finish in TR as (-> & ?).
        exists (Stuck), (Finish e v r); split.
        * apply ktrans_finish...
        * rewrite H0 in H.
          now cleft.
    - now cleft.
    - cdestruct H.
      assert (Hd: not_done w) by now apply ktrans_not_done in TR.
      inv Hd.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H.
        apply eur_stuck in H.
        cright; csplit...
        exists (Stuck), (Done r); split...
        apply ktrans_done...
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H.
        apply eur_stuck in H.
        cright; csplit...
        exists (Stuck), (Finish e v r); split...
        apply ktrans_finish...
  Qed.

  (** A hidden branch satisfies prefix [φ EU ψ] if it satisfies [φ] and some
      successor of some branch satisfies [φ EU ψ]. *)
  Lemma eul_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      <( {Br c k}, w |= φ )> ->
      (exists (y: Y) t' w', |k y, w| ↦ |t', w'| /\ <( t', w' |= φ EU ψ )>) ->
      <( {Br c k}, w |= φ EU ψ )>.
  Proof.
    intros; cright; now apply enl_br.
  Qed.

  (** A hidden branch satisfies suffix [φ EU ψ] if it satisfies [φ] and some
      successor of some branch satisfies [φ EU ψ]. *)
  Lemma eur_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      <( {Br c k}, w |= φ )> ->
      (exists (y: Y) t' w', |k y, w| ↦ |t', w'| /\ <[ t', w' |= φ EU ψ ]>) ->
      <[ {Br c k}, w |= φ EU ψ ]>.
  Proof.
    intros; cright; now apply enr_br.
  Qed.

  (** A visible choice satisfies prefix [φ EU ψ] if and only if it satisfies [ψ] or [φ EU ψ] for some [y]. *)
  Lemma eul_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      (<( {BrS c k}, w |= φ )> \/
         <( {BrS c k}, w |= ψ )> /\
           exists (y: Y), <( {k y}, w |= ψ EU φ )>) <->
        <( {BrS c k}, w |= ψ EU φ )>.
  Proof.
    intros; symmetry.
    rewrite equivl_eu_en at 1.
    now rewrite ticll_or, enl_brS.
  Qed.

  (** A visible choice satisfies suffix [φ EU ψ] if and only if it satisfies [ψ] or [φ EU ψ] for some [y]. *)
  Lemma eur_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) w φ ψ,
      (<[ {BrS c k}, w |= φ ]> \/
         <( {BrS c k}, w |= ψ )> /\
           exists (y: Y), <[ {k y}, w |= ψ EU φ ]>) <->
        <[ {BrS c k}, w |= ψ EU φ ]>.
  Proof.
    intros; symmetry.
    rewrite equivr_eu_en at 1.
    now rewrite ticlr_or, enr_brS.
  Qed.

  (** A visible step satisfies prefix [φ EU ψ] if and only if it satisfies [ψ] or [t] satisfies [φ EU ψ]. *)
  Lemma eul_step: forall (t: ctree E B X) w φ ψ,
      (<( {Step t}, w |= φ )> \/
         <( {Step t}, w |= ψ )> /\ <( t, w |= ψ EU φ )>) <->
        <( {Step t}, w |= ψ EU φ )>.
  Proof.
    intros; symmetry.
    rewrite equivl_eu_en at 1.
    now rewrite ticll_or, enl_step.
  Qed.

  (** A visible step satisfies suffix [φ EU ψ] if and only if it satisfies [ψ] or [t] satisfies [φ EU ψ]. *)
  Lemma eur_step: forall (t: ctree E B X) w φ ψ,
      (<[ {Step t}, w |= φ ]> \/
         <( {Step t}, w |= ψ )> /\ <[ t, w |= ψ EU φ ]>) <->
        <[ {Step t}, w |= ψ EU φ ]>.
  Proof.
    intros; symmetry.
    rewrite equivr_eu_en at 1.
    now rewrite ticlr_or, enr_step.
  Qed.

  (** A visible event satisfies prefix [φ EU ψ] if and only if it satisfies [ψ] or [φ EU ψ] for some [v]. *)
  Lemma eul_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) w φ ψ,
      (<( {Vis e k}, w |= φ )> \/
         <( {Vis e k}, w |= ψ )> /\
           exists (v: Y), <( {k v}, {Obs e v} |= ψ EU φ )>) <->
        <( {Vis e k}, w |= ψ EU φ )>.
  Proof.
    intros; symmetry.
    rewrite equivl_eu_en at 1.
    now rewrite ticll_or, enl_vis.
  Qed.

  (** A visible event satisfies suffix [φ EU ψ] if and only if it satisfies [ψ] or [φ EU ψ] for some [v]. *)
  Lemma eur_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) w φ ψ,
      (<[ {Vis e k}, w |= φ ]> \/
         <( {Vis e k}, w |= ψ )> /\
           exists (v: Y), <[ {k v}, {Obs e v} |= ψ EU φ ]>) <->
        <[ {Vis e k}, w |= ψ EU φ ]>.
  Proof.
    intros; symmetry.
    rewrite equivr_eu_en at 1.
    now rewrite ticlr_or, enr_vis.
  Qed.

  Lemma eur_not_done: forall φ ψ (t: ctree E B X) (w: World E),
      <[ t, w |= φ EU EX ψ ]> ->
      not_done w.
  Proof.
    intros.
    cdestruct H; cdestruct H;
      now apply ktrans_not_done with t t0 w0.
  Qed.
End BasicLemmas.
