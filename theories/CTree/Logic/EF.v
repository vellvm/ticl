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

  (** A stuck tree satisfies [φ EU ψ] if and only if it satisfies [ψ]. *)
  Lemma eu_stuck: forall {b: bool} w (φ: ticll E) (ψ: ticl_at E X b),
      entails X b (Cu Q_E φ ψ) (Stuck: ctree E B X) w <->
      entails X b ψ (Stuck: ctree E B X) w.
  Proof.
    split; intros.
    - cdestruct H; auto with ticl.
      cdestruct H.
      now apply ktrans_stuck in TR.
    - now cleft.
  Qed.

  (** A return tree satisfies [φ EU ψ] if and only if it satisfies [ψ] or [φ EN ψ]. *)
  Lemma eu_ret: forall {b: bool} (r: X) w (φ: ticll E) (ψ: ticl_at E X b),
      entails X b (COr ψ (Cx Q_E φ ψ)) (Ret r: ctree E B X) w <->
      entails X b (Cu Q_E φ ψ) (Ret r: ctree E B X) w.
  Proof.
    intros b r w φ ψ; split; intro H; cdestruct H.
    - now cleft.
    - exfalso; eapply (en_ret (b:=b)); exact H.
    - now cleft.
    - exfalso; eapply (en_ret (b:=b)); exact H.
  Qed.

  (** A hidden branch satisfies [φ EU ψ] if it satisfies [φ] and some
      successor of some branch satisfies [φ EU ψ]. *)
  Lemma eu_br: forall {b: bool} {Y} (c: B Y) (k: Y -> ctree E B X)
      w (φ: ticll E) (ψ: ticl_at E X b),
      entails X false φ (Br c k) w ->
      (exists (y: Y) t' w', |k y, w| ↦ |t', w'| /\
        entails X b (Cu Q_E φ ψ) t' w') ->
      entails X b (Cu Q_E φ ψ) (Br c k) w.
  Proof.
    intros b Y c k w φ ψ Hφ Hnext.
    cright; apply (en_br (b:=b)); split; assumption.
  Qed.

  (** A visible choice satisfies [φ EU ψ] if and only if it satisfies [ψ]
      or it satisfies [φ] and some branch satisfies [φ EU ψ]. *)
  Lemma eu_brS: forall {b: bool} {Y} (c: B Y) (k: Y -> ctree E B X)
      w (φ: ticll E) (ψ: ticl_at E X b),
      (entails X b ψ (BrS c k) w \/
         entails X false φ (BrS c k) w /\
           exists (y: Y), entails X b (Cu Q_E φ ψ) (k y) w) <->
        entails X b (Cu Q_E φ ψ) (BrS c k) w.
  Proof.
    intros; symmetry.
    rewrite (equiv_eu_en (b:=b)) at 1.
    now rewrite ticl_or, (en_brS (b:=b)).
  Qed.

  (** A visible step satisfies [φ EU ψ] if and only if it satisfies [ψ]
      or it satisfies [φ] and its continuation satisfies [φ EU ψ]. *)
  Lemma eu_step: forall {b: bool} (t: ctree E B X)
      w (φ: ticll E) (ψ: ticl_at E X b),
      (entails X b ψ (Step t) w \/
         entails X false φ (Step t) w /\ entails X b (Cu Q_E φ ψ) t w) <->
        entails X b (Cu Q_E φ ψ) (Step t) w.
  Proof.
    intros; symmetry.
    rewrite (equiv_eu_en (b:=b)) at 1.
    now rewrite ticl_or, (en_step (b:=b)).
  Qed.

  (** A visible event satisfies [φ EU ψ] if and only if it satisfies [ψ]
      or it satisfies [φ] and some response satisfies [φ EU ψ]. *)
  Lemma eu_vis: forall {b: bool} {Y} (e: E Y) (k: Y -> ctree E B X)
      w (φ: ticll E) (ψ: ticl_at E X b),
      (entails X b ψ (Vis e k) w \/
         entails X false φ (Vis e k) w /\
           exists (v: Y), entails X b (Cu Q_E φ ψ) (k v) (Obs e v)) <->
        entails X b (Cu Q_E φ ψ) (Vis e k) w.
  Proof.
    intros; symmetry.
    rewrite (equiv_eu_en (b:=b)) at 1.
    now rewrite ticl_or, (en_vis (b:=b)).
  Qed.
End BasicLemmas.
