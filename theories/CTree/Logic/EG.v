From Stdlib Require Import
  Basics
  Classes.Morphisms
  Arith.PeanoNat
  Lia.

From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  Logic.Kripke
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Setoid
  CTree.Logic.EX
  Logic.Core
  Utils.Relations
  Utils.Execution.

Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** * TICL logic lemmas on ctrees and the exists-always [EG] operator *)
Section BasicLemmas.
  Context {E B: Type -> Type} {X: Type}.

  (** A visible event satisfies [EG φ] if and only if it satisfies [φ] and its continuation [k v] satisfies [EG φ] for some [v]. *)
  Lemma eg_vis: forall {Y} (e: E Y) (k: Y -> ctree E B X) w (φ : ticll E),
      (<( {Vis e k}, w |=L φ )> /\ exists v, <( {k v}, {Obs e v} |=L EG φ )>) <->
         <( {Vis e k}, w |=L EG φ )>.
  Proof.
    ticl_normalize.
    split; intros.
    - destruct H as (Hφ & v & H).
      csplit; eauto with ticl.
      exists (k v), (Obs e v); split; eauto with ticl.
      apply ticl_not_done in Hφ.
      apply ktrans_vis.
      exists v; split2; eauto with ticl.
    - cdestruct H.
      split; eauto with ticl.
      apply ktrans_vis in TR as (v & -> & Heqt & ?).
      rewrite <- Heqt in H.
      exists v.
      apply H.
  Qed.

  (** A visible branch satisfies [EG φ] if and only if it satisfies [φ] and its continuation [k y] satisfies [EG φ] for some [y]. *)
  Lemma eg_brS: forall {Y} (c: B Y) (k: Y -> ctree E B X) w (φ : ticll E),
      (<( {BrS c k}, w |=L φ )> /\ exists (y: Y), <( {k y}, w |=L EG φ )>) <->
        <( {BrS c k}, w |=L EG φ )>.
  Proof.
    ticl_normalize.
    split; intros.
    - destruct H as (Hφ & y & H).
      csplit; eauto with ticl.
      exists (k y), w; split; eauto with ticl.
      apply ticl_not_done in Hφ.
      apply ktrans_brS.
      exists y; eauto with ticl.
    - cdestruct H.
      apply ktrans_brS in TR as (y & Heqt & -> & ?).
      split; eauto with ticl.
      rewrite Heqt in H.
      exists y.
      apply H.
  Qed.

  (** A visible step satisfies [EG φ] if and only if it satisfies [φ] and its continuation satisfies [EG φ]. *)
  Lemma eg_step: forall (t: ctree E B X) w (φ : ticll E),
      (<( {Step t}, w |=L φ )> /\ <( t, w |=L EG φ )>) <->
        <( {Step t}, w |=L EG φ )>.
  Proof.
    ticl_normalize.
    split; intros.
    - destruct H as (Hφ & H).
      csplit; eauto with ticl.
      exists t, w; split; eauto with ticl.
      apply ticl_not_done in Hφ.
      apply ktrans_step; eauto with ticl.
    - cdestruct H.
      apply ktrans_step in TR as (Heqt & -> & ?).
      split; eauto with ticl.
      now rewrite Heqt in H.
  Qed.

  (** A hidden branch satisfies [EG φ] if it satisfies [φ] and some branch has
      a successor satisfying [EG φ]. *)
  Lemma eg_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) w (φ : ticll E),
      <( {Br c k}, w |=L φ )> ->
      (exists y t' w', |k y, w| ↦ |t', w'| /\ <( t', w' |=L EG φ )>) ->
      <( {Br c k}, w |=L EG φ )>.
  Proof.
    ticl_normalize.
    intros * Hφ (y & t' & w' & TR & H).
    csplit; eauto with ticl.
    exists t', w'; split; eauto with ticl.
    apply ktrans_br; eauto with ticl.
  Qed.

  (** Inversion of [EG φ] at a hidden branch: some branch has a successor satisfying [EG φ]. *)
  Lemma eg_br_inv: forall {Y} (c: B Y) (k: Y -> ctree E B X) w (φ : ticll E),
      <( {Br c k}, w |=L EG φ )> ->
      <( {Br c k}, w |=L φ )> /\
      (exists y t' w', |k y, w| ↦ |t', w'| /\ <( t', w' |=L EG φ )>).
  Proof.
    ticl_normalize.
    intros * H.
    cdestruct H; split; eauto with ticl.
    apply ktrans_br in TR as (y & TR); eauto with ticl.
  Qed.

  (** A stuck tree does not satisfy [EG φ]; it does not step. *)
  Lemma eg_stuck: forall w (φ : ticll E),
      ~ <( {Stuck: ctree E B X}, w |=L EG φ )>.
  Proof.
    intros * H.
    cdestruct H; subst.
    now apply ktrans_stuck in TR.
  Qed.

  (** A return tree does not satisfy [EG φ]; it does not infinitely step. *)
  Lemma eg_ret: forall (x: X) w (φ : ticll E),
      ~ <( {Ret x: ctree E B X}, w |=L EG φ )>.
  Proof.
    intros * H.
    cdestruct H.
    assert(Hd: not_done w) by now apply ticl_not_done in Hp.
    inv Hd.
    - apply ktrans_done in TR as (-> & Heqt).
      rewrite Heqt in H.
      now apply eg_stuck in H.
    - apply ktrans_finish in TR as (-> & Heqt).
      rewrite Heqt in H.
      now apply eg_stuck in H.
  Qed.

End BasicLemmas.

(** A productive sequence of raw transitions establishes existential always.
    Indices without a retained transition preserve both the tree and world. *)
Lemma egc_of_sequence {E B X}
    (T : nat -> ctree E B X) (W : nat -> World E)
    (V : nat -> Prop) (P : ctree E B X -> World E -> Prop) :
  (forall n, {V n} + {~ V n}) -> infinitely V ->
  (forall n, P (T n) (W n)) ->
  Proper (sbisim eq ==> eq ==> iff) P ->
  (forall n, ~ V n -> T n ~ T (S n) /\ W (S n) = W n) ->
  (forall n, V n -> exists u,
    ktrans (T n) (W n) u (W (S n)) /\ u ~ T (S n)) ->
  forall n, egc P (T n) (W n).
Proof.
  intros Hdec Hinf HP Hproper Hskip Hstep.
  assert (Hinterval : forall n len,
    (forall j, n <= j < n + len -> ~ V j) ->
    T n ~ T (n + len) /\ W (n + len) = W n).
  { intros n len; induction len as [|len IH]; intro Hnone.
    - rewrite Nat.add_0_r; split; reflexivity.
    - destruct (IH ltac:(intros; apply Hnone; lia)) as [Et Ew].
      destruct (Hskip (n + len) ltac:(apply Hnone; lia)) as [Et' Ew'].
      replace (n + S len) with (S (n + len)) by lia.
      split; [etransitivity; eassumption|congruence]. }
  set (Z := fun (t : ctree E B X) (w : World E) =>
    exists n, t ~ T n /\ w = W n).
  assert (HZ : forall t w, Z t w -> egcF P Z t w).
  { intros t w (n & Et & ->).
    change (P t (W n) /\ exists u v, ktrans t (W n) u v /\ Z u v).
    split.
    - apply (proj2 (Hproper t (T n) Et _ _ eq_refl)); apply HP.
    - destruct (Hinf n) as (bound & Hbound & HV).
      destruct (finite_first V Hdec n (S bound - n))
        as [Hnone|(m & Hm & Hvisible & Hfirst)].
      + exfalso; apply (Hnone bound); [lia|exact HV].
      + destruct (Hinterval n (m - n) ltac:(intros; apply Hfirst; lia))
          as [Eprefix Eworld].
        replace (n + (m - n)) with m in Eprefix, Eworld by lia.
        destruct (Hstep m Hvisible) as (u & Hu & Eu).
        rewrite Eworld in Hu.
        assert (Estart : T m ~ t) by
          (symmetry; etransitivity; eassumption).
        destruct (ktrans_semiproper t (T m) u _ _ Estart Hu)
          as (v & Hv & Euv).
        exists v, (W (S m)); split; [exact Hv|].
        exists (S m); split;
          [etransitivity; [symmetry; exact Euv|exact Eu]|reflexivity]. }
  intro n; apply (leq_gfp (egcF P) Z); [exact HZ|].
  exists n; split; reflexivity.
Qed.
