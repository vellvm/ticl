From Stdlib Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Interp.Yield.Mod
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

  (** Stuckness preserves precisely the indexed until target. *)
  Lemma au_stuck: forall {b: bool} w (phi: ticll E) (psi: ticl_at E X b),
      entails X b psi (Stuck: ctree E B X) w <->
      entails X b (Cu Q_A phi psi) (Stuck: ctree E B X) w.
  Proof.
    split; intros * H.
    - now cleft.
    - remember (Stuck) as S.
      cinduction H; subst.
      + apply Hp.
      + now apply can_step_stuck in Hs.
  Qed.

  (** Return-until retains the target-or-next decomposition. *)
  Lemma au_ret: forall {b: bool} (r: X) w (phi: ticll E) (psi: ticl_at E X b),
      entails X b (COr psi (Cx Q_A phi psi)) (Ret r: ctree E B X) w <->
      entails X b (Cu Q_A phi psi) (Ret r: ctree E B X) w.
  Proof.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H; auto with ticl.
      intros t' w' TR.
      apply ticl_not_done in Hp.
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
      apply ticl_not_done in Hp.
      specialize (H _ _ TR).
      inv Hp.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H |- *.
        now apply au_stuck in H.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H |- *.
        now apply au_stuck in H.
  Qed.

  (** Hidden branching requires actual transitions from its branches. *)
  Lemma au_br: forall {b: bool} {Y} (c: B Y) (k: Y -> ctree E B X)
      w (phi: ticll E) (psi: ticl_at E X b),
      entails X false phi (Br c k) w ->
      (exists y, can_step (k y) w) ->
      (forall y t' w', |k y, w| ↦ |t', w'| ->
        entails X b (Cu Q_A phi psi) t' w') ->
      entails X b (Cu Q_A phi psi) (Br c k) w.
  Proof.
    intros; cright; now apply an_br.
  Qed.

  (** Until through a nonempty family of policy alternatives. *)
  Lemma au_br_alts `{Bn -< B}: forall {b : bool} m
      (k : Fin.t (S m) -> ctree E B X) w (phi : ticll E) (psi : ticl_at E X b),
      entails X false phi (br_alts m k) w ->
      (exists a, can_step (k a) w) ->
      (forall a t' w', |k a, w| ↦ |t', w'| -> entails X b (Cu Q_A phi psi) t' w') ->
      entails X b (Cu Q_A phi psi) (br_alts m k) w.
  Proof.
    intros; cright; now apply an_br_alts.
  Qed.

  (** Visible branching keeps an explicit inhabitant to witness progress. *)
  Lemma au_brS: forall {b: bool} {Y} (c: B Y) (k: Y -> ctree E B X)
      (y: Y) w (phi: ticll E) (psi: ticl_at E X b),
      (entails X b psi (BrS c k) w \/
         entails X false phi (BrS c k) w /\
           forall (y: Y), entails X b (Cu Q_A phi psi) (k y) w) <->
      entails X b (Cu Q_A phi psi) (BrS c k) w.
  Proof.
    intros; symmetry.
    rewrite equiv_au_an at 1.
    now rewrite ticl_or, (an_brS (b:=b) c k y).
  Qed.

  (** Visible step iff lemma for indexed until. *)
  Lemma au_step: forall {b: bool} (t: ctree E B X)
      w (phi: ticll E) (psi: ticl_at E X b),
      (entails X b psi (Step t) w \/
         entails X false phi (Step t) w /\ entails X b (Cu Q_A phi psi) t w) <->
      entails X b (Cu Q_A phi psi) (Step t) w.
  Proof.
    intros; symmetry.
    rewrite equiv_au_an at 1.
    now rewrite ticl_or, (an_step (b:=b)).
  Qed.

  (** Visible events keep an explicit result inhabitant to witness progress. *)
  Lemma au_vis: forall {b: bool} {Y} (e: E Y) (k: Y -> ctree E B X)
      (_: Y) w (phi: ticll E) (psi: ticl_at E X b),
      (entails X b psi (Vis e k) w \/
         entails X false phi (Vis e k) w /\
           forall (v: Y), entails X b (Cu Q_A phi psi) (k v) (Obs e v)) <->
      entails X b (Cu Q_A phi psi) (Vis e k) w.
  Proof.
    intros b Y e k v0 w phi psi; symmetry.
    rewrite equiv_au_an at 1.
    now rewrite ticl_or, (an_vis (b:=b) e k v0).
  Qed.

  (** Helper version of [au_vis] for [AF] = [T AU]. *)
  Lemma af_vis: forall {b: bool} {Y} (e: E Y) (k: Y -> ctree E B X)
      (_: Y) w (psi: ticl_at E X b),
      entails X b psi (Vis e k) w \/
         (not_done w /\ forall (v: Y),
           entails X b (Cu Q_A (CNow (fun _ => True)) psi) (k v) (Obs e v)) <->
      entails X b (Cu Q_A (CNow (fun _ => True)) psi) (Vis e k) w.
  Proof.
    intros b Y e k v0 w psi; symmetry.
    rewrite equiv_au_an at 1.
    rewrite ticl_or, (an_vis (b:=b) e k v0), ticl_now; tauto.
  Qed.
End BasicLemmas.
