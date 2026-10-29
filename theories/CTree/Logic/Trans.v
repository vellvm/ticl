From Stdlib Require Import
  Basics
  Classes.SetoidClass
  Classes.RelationPairs.

From TICL Require Import
  CTree.Core
  CTree.Events.Writer
  Logic.Kripke
  Logic.Setoid.

Generalizable All Variables.

Import CTree CTreeNotations.
Local Open Scope ctree_scope.

(** * Kripke transition system *)
(** This section defines the Kripke transition system for ctrees, on top of the
    labelled transition system [trans] of the [ctrees] library.

    A labelled transition [trans l t t'] becomes a world transition:
    - [τ] keeps the world (visible step, [Step]/[BrS]);
    - [obs e v] records the observation [Obs e v];
    - [val x] finishes the computation in [Done x] (from [Pure]) or [Finish e v x] (from [Obs e v]).
    Delayed branches [Br c k] and [Guard] are crawled through by [trans], so they are not steps.

    Intuitively, [ktrans] is the small-step semantics of ctrees, independent of the event type [E].
    We then use [ktrans] in [Semantics.v] to define the semantic entailment relation [|=] for each Ticl formula.
*)
Section CTreeTrans.
  Context {E B: Type -> Type}.

  (*| Kripke transition system |*)
  Variant ktrans_ {X}: ctree E B X -> World E -> ctree E B X -> World E -> Prop :=
  | KtransTau (t t': ctree E B X) w:
    not_done w ->
    trans τ t t' ->
    ktrans_ t w t' w
  | KtransObs {Y} (e: E Y) (v: Y) (t t': ctree E B X) w:
    not_done w ->
    trans (obs e v) t t' ->
    ktrans_ t w t' (Obs e v)
  | KtransDone (x: X) (t t': ctree E B X):
    trans (val x) t t' ->
    ktrans_ t Pure t' (Done x)
  | KtransFinish {Y} (e: E Y) (v: Y) (x: X) (t t': ctree E B X):
    trans (val x) t t' ->
    ktrans_ t (Obs e v) t' (Finish e v x).
  Hint Constructors ktrans_: ticl.

  (** [ktrans] is a Kripke transition system for ctrees. *)
  Global Program Instance ctree_kripke: Kripke ctree E B | 1 := {
      ktrans X := @ktrans_ X
    }.
  Next Obligation.
    inversion H; auto with ticl.
  Defined.
  Hint Unfold ktrans: ticl.
  Arguments ktrans /.

  (* This hint tells Rocq that when trying to resolve an instance of
  Kripke ?A ?B ?C, it should first try to unify the first parameter with
  ctree. The priority 0 ensures this hint is tried before other
  resolution strategies. *)
  Hint Extern 0 (Kripke ?A ?B ?C) => 
         first [ is_evar A; exact ctree
               | fail ] : typeclass_instances.

  (** [ktrans] preserves equality [equ eq]*)
  Global Instance ktrans_equ_proper{X}:
    Proper (equ eq ==> eq ==> equ eq ==> eq ==> iff) (ktrans (X:=X)).
  Proof.
    unfold Proper, respectful; cbn; intros t t' Ht w ? <- u u' Hu w' ? <-.
    split; intros TR; ddestruction TR.
    - apply KtransTau; auto; now rewrite <- Ht, <- Hu.
    - apply KtransObs; auto; now rewrite <- Ht, <- Hu.
    - apply KtransDone; now rewrite <- Ht, <- Hu.
    - apply KtransFinish; now rewrite <- Ht, <- Hu.
    - apply KtransTau; auto; now rewrite Ht, Hu.
    - apply KtransObs; auto; now rewrite Ht, Hu.
    - apply KtransDone; now rewrite Ht, Hu.
    - apply KtransFinish; now rewrite Ht, Hu.
  Qed.

  (** Characterization of [ktrans] in terms of the labelled [trans]. *)
  Lemma ktrans_trans{X}: forall (t t': ctree E B X) w w',
      ktrans_ t w t' w' <->
        (exists l, trans l t t' /\
                ((l = τ /\ not_done w /\ w' = w)
                 \/ (exists Y (e: E Y) (x: Y), l = obs e x /\ not_done w /\ w' = Obs e x)
                 \/ (exists (x: X), l = val x /\ w = Pure /\ t' ≅ Stuck /\ w' = Done x)
                 \/ (exists Y (e: E Y) (v: Y) (x: X), l = val x /\ w = Obs e v /\ t' ≅ Stuck /\ w' = Finish e v x))).
  Proof.
    split; intro H.
    - inv H.
      + exists τ; split; auto.
      + exists (obs e v); split; auto.
        right; left; exists Y, e, v; eauto with ticl.
      + exists (val x); split; auto.
        right; right; left; exists x; split2; auto.
        now apply trans_val_inv in H0.
      + exists (val x); split; auto.
        right; right; right; exists Y, e, v, x; split2; auto.
        now apply trans_val_inv in H0.
    - destruct H as (l & TR & [(-> & Hd & ->) | [(Y & e & x & -> & Hd & ->) | [(x & -> & -> & Hs & ->) | (Y & e & v & x & -> & -> & Hs & ->)]]]); eauto with ticl.
  Qed.

  (** [equ eq] is a Kripke setoid for [ktrans]. *)
  Global Instance KripkeSetoidEqu {X}:
    @KripkeSetoid ctree E B ctree_kripke X (equ eq) _.
  Proof.
    repeat red; intros.
    exists s'; split; auto.
    now rewrite <- H.
  Qed.

  (** [sbisim eq] is a Kripke setoid for [ktrans]: a strongly bisimilar tree
      can match every world transition up to [sbisim eq]. *)
  Global Instance KripkeSetoidSBisim {X}:
    @KripkeSetoid ctree E B ctree_kripke X (sbisim eq) _.
  Proof.
    repeat red; intros t s s' w w' Hsb TR.
    ddestruction TR; step in Hsb; destruct Hsb as [Hf _]; cbn in Hf.
    - edestruct Hf as (l' & u' & TR' & EQ & <-); [eassumption|].
      exists u'; split; auto; now apply KtransTau.
    - edestruct Hf as (l' & u' & TR' & EQ & <-); [eassumption|].
      exists u'; split; auto; now apply KtransObs.
    - edestruct Hf as (l' & u' & TR' & EQ & <-); [eassumption|].
      exists u'; split; auto; now apply KtransDone.
    - edestruct Hf as (l' & u' & TR' & EQ & <-); [eassumption|].
      exists u'; split; auto; now apply KtransFinish.
  Qed.

  Hint Extern 0 (KripkeSetoid ?A ?B ?C) => 
         first [ is_evar A; exact ctree
               | fail ] : typeclass_instances.

  Local Open Scope ticl_scope.

  (** [ktrans] can ignore any finite number of [Guard] nodes on the left-hand side. *)
  Lemma ktrans_guard{X}: forall (t t': ctree E B X) w w',
      |Guard t, w| ↦ |t', w'| <-> |t, w| ↦ |t', w'|.
  Proof.
    split; intro TR; cbn in *; ddestruction TR.
    - apply trans_guard_inv in H0; now apply KtransTau.
    - apply trans_guard_inv in H0; now apply KtransObs.
    - apply trans_guard_inv in H; now apply KtransDone.
    - apply trans_guard_inv in H; now apply KtransFinish.
    - apply KtransTau; auto; now apply trans_guard.
    - apply KtransObs; auto; now apply trans_guard.
    - apply KtransDone; now apply trans_guard.
    - apply KtransFinish; now apply trans_guard.
  Qed.
  Hint Resolve ktrans_guard: ticl.

  (** Delayed branches [Br c k] are crawled through: [Br c k] steps iff one of
      its branches steps. This matches the [ctrees] LTS, where only [Step]
      (and hence [BrS]) is a visible [τ] step. *)
  Lemma ktrans_br {X Y}: forall (c: B Y) (t: ctree E B X) (k: Y -> ctree E B X) w w',
      |Br c k, w| ↦ |t, w'| <-> (exists (i: Y), |k i, w| ↦ |t, w'|).
  Proof.
    split; intro TR; cbn in *.
    - ddestruction TR.
      + apply trans_br_inv in H0 as (i & TR); exists i; now apply KtransTau.
      + apply trans_br_inv in H0 as (i & TR); exists i; now apply KtransObs.
      + apply trans_br_inv in H as (i & TR); exists i; now apply KtransDone.
      + apply trans_br_inv in H as (i & TR); exists i; now apply KtransFinish.
    - destruct TR as (i & TR); ddestruction TR.
      + apply KtransTau; auto; eapply trans_br; eauto; reflexivity.
      + apply KtransObs; auto; eapply trans_br; eauto; reflexivity.
      + apply KtransDone; eapply trans_br; eauto; reflexivity.
      + apply KtransFinish; eapply trans_br; eauto; reflexivity.
  Qed.
  Hint Resolve ktrans_br: ticl.

  (** [Step t] is a single [τ] step. *)
  Lemma ktrans_step {X}: forall (t t': ctree E B X) w w',
      |Step t, w| ↦ |t', w'| <-> (t' ≅ t /\ w = w' /\ not_done w).
  Proof.
    split; intro TR; cbn in *.
    - ddestruction TR.
      + apply trans_step_inv in H0 as (? & _); auto.
      + apply trans_step_inv in H0 as (_ & ?); discriminate.
      + apply trans_step_inv in H as (_ & ?); discriminate.
      + apply trans_step_inv in H as (_ & ?); discriminate.
    - destruct TR as (Heq & <- & Hd).
      apply KtransTau; auto.
      rewrite Heq; apply trans_step.
  Qed.
  Hint Resolve ktrans_step: ticl.

  (** [BrS c k] is a single [τ] step choosing a branch. *)
  Lemma ktrans_brS {X Y}: forall (c: B Y) (t: ctree E B X) (k: Y -> ctree E B X) w w',
      |BrS c k, w| ↦ |t, w'| <-> (exists (i: Y), t ≅ k i /\ w = w' /\ not_done w).
  Proof.
    split; intro TR.
    - apply ktrans_br in TR as (i & TR).
      apply ktrans_step in TR as (Heq & <- & Hd); eauto.
    - destruct TR as (i & Heq & <- & Hd).
      apply ktrans_br; exists i.
      apply ktrans_step; auto.
  Qed.
  Hint Resolve ktrans_brS: ticl.

  (** [ktrans] considers [Ret x] as a single step. *)
  Lemma ktrans_done {X}: forall (t: ctree E B X) (w': World E) x,
      |Ret x, Pure| ↦ |t, w'| <-> (w' = Done x /\ t ≅ Stuck).
  Proof.
    split; intro TR; cbn in *.
    - ddestruction TR.
      + apply trans_ret_inv in H0 as (_ & ?); discriminate.
      + apply trans_ret_inv in H0 as (_ & ?); discriminate.
      + apply trans_ret_inv in H as (? & Hv).
        apply val_eq_inv in Hv; subst; auto.
    - destruct TR as (-> & Heq).
      apply KtransDone.
      rewrite Heq; apply trans_ret.
  Qed.
  Hint Resolve ktrans_done: ticl.

  (** [ktrans] considers [Ret x] as a single step. *)
  Lemma ktrans_finish {X Y}: forall (t: ctree E B X) (w': World E) (e: E Y) (v: Y) x,
      |Ret x, Obs e v| ↦ |t, w'| <->
        (w' = Finish e v x /\ t ≅ Stuck).
  Proof.
    split; intro TR; cbn in *.
    - ddestruction TR.
      + apply trans_ret_inv in H0 as (_ & ?); discriminate.
      + apply trans_ret_inv in H0 as (_ & ?); discriminate.
      + apply trans_ret_inv in H as (? & Hv).
        apply val_eq_inv in Hv; subst; auto.
    - destruct TR as (-> & Heq).
      apply KtransFinish.
      rewrite Heq; apply trans_ret.
  Qed.
  Hint Resolve ktrans_finish: ticl.

  (** [ktrans] considers [Vis e k] as a single step. *)
  Lemma ktrans_vis{X Y}: forall (t: ctree E B X) (s s': World E) (e: E Y) (k: Y -> ctree E B X),
      |Vis e k, s| ↦ |t, s'| <->
        (exists (x: Y), s' = Obs e x /\ k x ≅ t /\ not_done s).
  Proof.
    split; intro TR; cbn in *.
    - ddestruction TR.
      + apply trans_vis_inv in H0 as (? & _ & ?); discriminate.
      + apply trans_vis_inv in H0 as (x & Heq & Hl).
        dependent destruction Hl.
        exists x; split2; auto; now symmetry.
      + apply trans_vis_inv in H as (? & _ & ?); discriminate.
      + apply trans_vis_inv in H as (? & _ & ?); discriminate.
    - destruct TR as (x & -> & Heq & Hd).
      apply KtransObs; auto.
      rewrite <- Heq; apply trans_vis.
  Qed.
  Hint Resolve ktrans_vis: ticl.

  (** [ktrans] cannot step from an observation to a pure state. *)
  Lemma ktrans_pure_pred{X}: forall (t t': ctree E B X) w,
      |t, w| ↦ |t', Pure| -> w = Pure.
  Proof.
    intros * TR; cbn in TR; ddestruction TR; reflexivity.
  Qed.
  Hint Resolve ktrans_pure_pred: ticl.

  (** [ktrans] cannot step from a stuck state. *)
  Lemma ktrans_stuck{X}: forall (t: ctree E B X) w w',
      ~ |Stuck, w| ↦ |t, w'|.
  Proof.
    intros * TR; cbn in TR; ddestruction TR; eapply trans_stuck_inv; eauto.
  Qed.
  Hint Resolve ktrans_stuck: ticl.

  (** [ktrans] cannot step from a done world [w]. *)
  Lemma done_not_ktrans{X}: forall (t: ctree E B X) w,
      is_done X w ->
      ~ (exists t' w', |t, w| ↦ |t', w'|).
  Proof.
    intros * Hret (t' & w' & TR).
    inv Hret; cbn in TR; ddestruction TR; inv H.
  Qed.
  Hint Resolve done_not_ktrans: ticl.

  (** [ktrans] cannot step from a done state. *)
  Lemma ktrans_done_inv{X}: forall (t t': ctree E B X) (x: X) w,
      ~ |t, Done x| ↦ |t', w|.
  Proof.
    intros * TR; cbn in TR; ddestruction TR; inv H.
  Qed.
  Hint Resolve ktrans_done_inv: ticl.

  (** [ktrans] cannot step from a finish state. *)
  Lemma ktrans_finish_inv{X Y}: forall (t t': ctree E B X) (e: E Y) (v: Y) (x: X) w,
      ~ |t, Finish e v x| ↦ |t', w|.
  Proof.
    intros * TR; cbn in TR; ddestruction TR; inv H.
  Qed.
  Hint Resolve ktrans_finish_inv: ticl.

  Lemma ktrans_to_done_inv{X}: forall (t t': ctree E B X) w (x: X),
      |t, w| ↦ |t', Done x| ->
      t' ≅ Stuck /\ w = Pure.
  Proof.
    intros * TR; cbn in TR; ddestruction TR.
    - inv H.
    - split; auto; now apply trans_val_inv in H.
  Qed.
  Hint Resolve ktrans_to_done_inv: ticl.

  Lemma ktrans_to_finish_inv{X Y}: forall (t t': ctree E B X) w (e: E Y) (v: Y) (x: X),
      |t, w| ↦ |t', Finish e v x| ->
      t' ≅ Stuck /\ w = Obs e v.
  Proof.
    intros * TR; cbn in TR; ddestruction TR.
    - inv H.
    - split; auto; now apply trans_val_inv in H.
  Qed.
  Hint Resolve ktrans_to_finish_inv: ticl.

  (** Any [ktrans] to a [done] world returns the value through [val]. *)
  Lemma ktrans_done_eq_inv{X}: forall (t t': ctree E B X) w (x: X) w',
      |t, w| ↦ |t', w'| ->
      done_eq x w' ->
      trans (val x) t Stuck /\ not_done w /\ done_of x w w'.
  Proof.
    intros * TR Hd; cbn in TR; inv Hd; ddestruction TR.
    - inv H.
    - pose proof (trans_val_inv H) as Hs; rewrite Hs in H; split2; auto with ticl.
    - inv H.
    - pose proof (trans_val_inv H) as Hs; rewrite Hs in H; split2; auto with ticl.
  Qed.

  (** Left [ktrans] and [bind] lemma, if [t] steps to [t'], then [x <- t ;; k x] steps to [x <- t' ;; k x]. *)
  Lemma ktrans_bind_l{X Y}: forall (t t': ctree E B Y) (k: Y -> ctree E B X) w w',
      |t, w| ↦ |t', w'| ->
      not_done w' ->
      |x <- t ;; k x, w| ↦ |x <- t' ;; k x, w'|.
  Proof.
    intros * TR Hd; cbn in *; ddestruction TR.
    - apply KtransTau; auto.
      apply trans_bind_l; auto.
      intro Hv; inv Hv.
    - apply KtransObs; auto.
      apply trans_bind_l; auto.
      intro Hv; inv Hv.
    - inv Hd.
    - inv Hd.
  Qed.

  (** Right [ktrans] and [bind] lemma, if [t] returns [y] and [k y] steps, then [x <- t ;; k x] steps. *)
  Lemma ktrans_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) (u: ctree E B X) (y: Y) w w_ w',
      |t, w| ↦ |Stuck, w_| ->
      done_eq y w_ ->
      |k y, w| ↦ |u, w'| ->
      |x <- t ;; k x, w| ↦ |u, w'|.
  Proof.
    intros * TRt Hd TRk.
    apply (ktrans_done_eq_inv _ _ _ y) in TRt as (TRv & _ & _); auto.
    cbn in *; ddestruction TRk.
    - apply KtransTau; auto; eapply trans_bind_r; eauto.
    - apply KtransObs; auto; eapply trans_bind_r; eauto.
    - apply KtransDone; eapply trans_bind_r; eauto.
    - apply KtransFinish; eapply trans_bind_r; eauto.
  Qed.

  Lemma ktrans_bind_inv: forall {X Y} (w w': World E)
                           (t: ctree E B X) (u: ctree E B Y) (k: X -> ctree E B Y),
      |x <- t ;; k x, w| ↦ |u, w'| ->
      (exists t', |t, w| ↦ |t', w'|
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
        (* [t] returns [x], [t>>=k] steps if [k x] steps *)
        (exists y w_, |t, w| ↦ |Stuck, w_|
                 /\ done_eq y w_
                 /\ |k y, w| ↦ |u, w'|).
  Proof.
    intros X Y w w' t u k TR; cbn in *.
    ddestruction TR.
    - apply trans_bind_inv in H0 as [(Hv & t_ & TR & Heq) | (x & TRv & TRk)].
      + left; exists t_; split2; eauto with ticl.
      + right; dependent destruction H.
        * exists x, (Done x); split2; eauto with ticl.
        * exists x, (Finish e v x); split2; eauto with ticl.
    - apply trans_bind_inv in H0 as [(Hv & t_ & TR & Heq) | (x & TRv & TRk)].
      + left; exists t_; split2; eauto with ticl.
      + right; dependent destruction H.
        * exists x, (Done x); split2; eauto with ticl.
        * exists x, (Finish e0 v0 x); split2; eauto with ticl.
    - apply trans_bind_inv in H as [(Hv & t_ & TR & Heq) | (x' & TRv & TRk)].
      + exfalso; apply Hv; constructor.
      + right; exists x', (Done x'); split2; eauto with ticl.
    - apply trans_bind_inv in H as [(Hv & t_ & TR & Heq) | (x' & TRv & TRk)].
      + exfalso; apply Hv; constructor.
      + right; exists x', (Finish e v x'); split2; eauto with ticl.
  Qed.
  Hint Resolve ktrans_bind_inv: ticl.

End CTreeTrans.

#[global] Hint Constructors
  ktrans_ not_done done_with vis_with: ticl.

#[global] Hint Resolve
  ktrans_stuck ktrans_br ktrans_brS ktrans_step ktrans_vis ktrans_done
  ktrans_done_inv ktrans_finish can_step_not_done
  ktrans_not_done ktrans_finish_inv ktrans_bind_inv
  ktrans_to_done_inv ktrans_to_finish_inv
  ktrans_guard ktrans_pure_pred: ticl.

(** * Inversion lemmas for [ktrans] and [bind] *)
(** Inversion lemma for [ktrans] and [bind] with [Ret x]. 
    Any tree strongly bisimilar to [Ret x], for example [Guard ... Guard (Ret x)],
    behaves like a return in the context of [ktrans] and [bind].
  *)
Local Open Scope ticl_scope.
Local Typeclasses Opaque sbisim.
Local Typeclasses Opaque equ.
Lemma ktrans_sbisim_ret {E B X Y}:
  forall (t : ctree E B X) (k: X -> ctree E B Y) t' x w w',
  t ~ (Ret x : ctree E B X) ->
  |x <- t;; k x, w| ↦ |t', w'| ->
  |k x, w| ↦ |t', w'|.
Proof.
  intros * Hsb TR.
  apply ktrans_bind_inv in TR as [(t2 & TR2 & Hd & Eq2) | (y & w_ & TRr & Hd & TRk)].
  - (* [t] takes a non-return step; impossible since [t ~ Ret x] *)
    exfalso.
    apply ktrans_trans in TR2 as (l & TR2 & Hl).
    step in Hsb; destruct Hsb as [Hf _]; cbn in Hf.
    destruct (Hf _ _ TR2) as (l' & u' & TR' & _ & <-).
    apply trans_ret_inv in TR' as (_ & ->).
    destruct Hl as [(Hl & _) | [(? & ? & ? & Hl & _) | [(? & _ & _ & _ & Hw) | (? & ? & ? & ? & _ & _ & _ & Hw)]]];
      try discriminate; subst; inv Hd.
  - (* [t] returns [y]; [y = x] by bisimulation with [Ret x] *)
    apply (ktrans_done_eq_inv _ _ _ y) in TRr as (TRv & _ & _); auto.
    step in Hsb; destruct Hsb as [Hf _]; cbn in Hf.
    destruct (Hf _ _ TRv) as (l' & u' & TR' & _ & <-).
    apply trans_ret_inv in TR' as (_ & Hv).
    apply val_eq_inv in Hv; now subst.
Qed.
