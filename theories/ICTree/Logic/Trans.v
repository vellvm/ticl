From ExtLib Require Import
  Structures.MonadWriter
  Structures.Monads
  Structures.MonadState
  Data.Monads.StateMonad.

From Stdlib Require Import
  List
  Basics
  Fin
  Relations.Relation_Definitions
  Classes.SetoidClass
  Classes.RelationPairs.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.Trans
  ICTree.Events.Writer
  Events.Core
  Logic.Kripke
  Logic.Setoid.

Generalizable All Variables.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

(** * Kripke transition system *)
(** This section defines the Kripke transition system for ictrees. 
    We define a relation [ktrans_] that relates a pair of ictrees and worlds to a pair of ictrees and worlds.
    We then prove that this relation is a Kripke transition system.

    Intuitively, [ktrans] is the small-step semantics of ictrees, independent of the event type [E].
    We then use [ktrans] in [Semantics.v] to define the semantic entailment relation [|=] for each Ticl formula.
*)
Section ICTreeTrans.
  Context {E: Type} `{HE: Encode E}.
  Notation encode := (@encode E HE).

  (*| Kripke transition system |*)
  Inductive ktrans_{X}: ictree' E X -> World E -> ictree' E X -> World E -> Prop :=
  | KtransGuard w w' (t t': ictree E X):
    ktrans_ (observe t) w (observe t') w' ->
    ktrans_ (GuardF t) w (observe t') w'
  | KtransBr (n: nat) (i: fin' n) k t w:
    not_done w ->
    t ≅ k i ->
    ktrans_ (BrF n k) w (observe t) w
  | KtransObs (e: E) (v: encode e) k t w:
    not_done w ->
    t ≅ k v ->
    ktrans_ (VisF e k) w (observe t) (Obs e v)
  | KtransDone (x: X) t:
    t ≅ ICtree.stuck ->
    ktrans_ (RetF x) Pure (observe t) (Done x)
  | KtransFinish (e: E) (v: encode e) (x: X) t:
    t ≅ ICtree.stuck ->
    ktrans_ (RetF x) (Obs e v) (observe t) (Finish e v x).
  Hint Constructors ktrans_: ticl.

  Local Instance ktrans_equ_aux1 {X}(t: ictree' E X) (w: World E):
    Proper (going (equ eq) ==> eq ==> flip impl) (ktrans_ t w).
  Proof.
    unfold Proper, respectful, iff, fst, snd; cbn; unfold fst, snd;
      cbn; unfold RelCompFun; cbn.
    intros u u' Hequ s s' <-  TR.
    inv Hequ; rename H into equ; cbn in *.
    step in equ.
    revert u equ.
    dependent induction TR; intros; subst; eauto;
      rename u into U;
      remember ({| _observe := U |}) as u;
      replace U with (observe u) in * by now subst.
    - eapply KtransGuard; auto.
    - eapply KtransBr; auto.
      transitivity t; eauto.
      now step.
    - eapply KtransObs; auto.
      transitivity t; eauto.
      now step.
    - eapply KtransDone.
      transitivity t; auto.
      now step.
    - eapply KtransFinish.
      transitivity t; auto.
      now step.
  Qed.

  Global Instance ktrans_equ_aux2{X}:
    Proper (going (equ eq) ==> eq ==> going (equ eq) ==> eq ==> impl) (ktrans_ (X:=X)).
  Proof.
    intros t t' Heqt x x' <- u u' Hequ y y' <- TR.
    rewrite <- Hequ; clear u' Hequ.
    inv Heqt; rename H into eqt.
    revert t' eqt.
    dependent induction TR; intros; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      eapply KtransGuard; eauto.
      eapply IHTR; auto.
      now rewrite <- !ictree_eta.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      rewrite H0.
      eapply KtransBr; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      rewrite H0.
      apply KtransObs; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      apply KtransDone; auto.
    + step in eqt; cbn in eqt; dependent destruction eqt.
      apply KtransFinish; auto.
  Qed.

  (** [ktrans] is a Kripke transition system for ictrees. *)
  Global Program Instance ictree_kripke: Kripke ictree E | 1 := {
      ktrans X t w t' w' :=
        ktrans_ (X:=X) (observe t) w (observe t') w'
    }.
  Next Obligation.
    dependent induction H; cbn; eauto with ticl.
  Defined.
  Hint Unfold ktrans: ticl.
  Arguments ktrans /.

  (* This hint tells Coq that when trying to resolve an instance of
  Kripke ?A ?B, it should first try to unify the first parameter with
  ictree. The priority 0 ensures this hint is tried before other
  resolution strategies. *)
  Hint Extern 0 (Kripke ?A ?B) => 
         first [ is_evar A; exact ictree
               | fail ] : typeclass_instances.
  
  (** [ktrans] preserves equality [equ eq]*)
  Global Instance ktrans_equ_proper{X}:
    Proper (equ eq ==> eq ==> equ eq ==> eq ==> iff) (ktrans (X:=X)).
  Proof.
    unfold Proper, respectful, RelCompFun, fst, snd; cbn; intros; subst.
    split; intros TR; unfold ktrans.
    - now rewrite <- H, <- H1.
    - now rewrite H, H1.
  Qed.

  (** [ktrans] is in lockstep with [trans], the LTS transition relation used to define strong bisimulation in [SBisim.v].
      Consequently, Kripke worlds and LTS labels are 1-1. *)
  Lemma ktrans_trans{X}: forall (t t': ictree E X) w w',
      ktrans_ (observe t) w (observe t') w' <->
        (exists l, trans_ l (observe t) (observe t') /\
                ((l = tau /\ not_done w /\ w' = w)
                 \/ (exists e (x: encode e), l = obs e x /\ not_done w /\ w' = Obs e x)
                 \/ (exists (x: X), l = val x /\ w = Pure /\ t' ≅ stuck /\ w' = Done x)
                 \/ (exists e (v: encode e) (x: X), l = val x /\ w = Obs e v /\ t' ≅ stuck /\ w' = Finish e v x))).
  Proof with eauto with ictree.
    intros; split; intro H.
    - remember (observe t) as T; remember (observe t') as T';
      generalize dependent t; generalize dependent t'.
      induction H; intros; subst.
      + destruct (IHktrans_ _ HeqT' _ eq_refl) as (l & TR & Hl).
        exists l; split...
        apply trans_guard...
      + exists tau; split...
        apply trans_br with (x:=i).
        now symmetry.
      + exists (obs e v); split.
        * econstructor; now symmetry.
        * right; left.
          exists e, v...
      + exists (val x); rewrite H; split.
        * now econstructor.
        * right; right; left.
          exists x; intuition.
          transitivity t...
          step; cbn; rewrite HeqT'; reflexivity.
      + exists (val x); rewrite H; split; auto.
        * now econstructor.
        * right; right; right.
          exists e, v, x; intuition.
          transitivity t...
          step; cbn; rewrite HeqT'; reflexivity.
    - destruct H as (l & ? & Hl);
      remember (observe t) as T; remember (observe t') as T';
        generalize dependent t; generalize dependent t'; revert w w'.
      induction H; intros; subst.
      + apply KtransGuard...
      + destruct Hl as [ (? & ? & ?) |
             [(e & x' & ? & ? & ?) |
               [(x' & ? & ? & Ht & ?) |
                 (e & v & x' & ? & ? & Ht & ?)]]];
          subst; inv H0.
        apply KtransBr with x...
        now symmetry.
      + destruct Hl as [ (? & ? & ?) |
             [(e' & x' & ? & ? & ?) |
               [(x' & ? & ? & Ht & ?) |
                 (e' & v & x' & ? & ? & Ht & ?)]]]; subst;
          dependent destruction H0.
        apply KtransObs; auto.
        now symmetry.
      + destruct Hl as [ (? & ? & ?) |
             [(e' & x' & ? & ? & ?) |
               [(x' & ? & ? & Ht & ?) |
                 (e' & v & x' & ? & ? & Ht & ?)]]]; subst;
          dependent destruction H0.
        * apply KtransDone.
          transitivity t'; auto.
          step; cbn; rewrite HeqT'; reflexivity.
        * apply KtransFinish.
          transitivity t'; auto.
          step; cbn; rewrite HeqT'; reflexivity.
  Qed.

  (* Here I define two setoid instaces, one for [equ eq]
     and one for [sbisim eq]. Even though [equ eq] is a subrelation
     of [sbisim eq], I had to delete the subrelation instance and
     duplicate here beaucse instance resolution became extremely slow. *)
  Global Instance KripkeSetoidEqu {X}:
    @KripkeSetoid ictree E HE ictree_kripke X (equ eq) _.
  Proof.
    repeat red; intros.
    rewrite H in H0.
    exists s'; intuition.
  Qed.

  (** This hint tells Coq that when trying to resolve an instance of
  KripkeSetoid ?A ?B, it should first try to unify the first parameter with
  ictree. The priority 0 ensures this hint is tried before other
  resolution strategies. *)
  Hint Extern 0 (KripkeSetoid ?A ?B) => 
         first [ is_evar A; exact ictree
               | fail ] : typeclass_instances.
  
  
  (** [ktrans] can ignore any finite number of [guard] nodes on the left-hand side. *)
  Local Open Scope ticl_scope.
  Lemma ktrans_guard{X}: forall (t t': ictree E X) w w',
      |Guard t, w| ↦ |t', w'| <-> |t, w| ↦ |t', w'|.
  Proof.
    split; intro H.
    - cbn in H; dependent induction H; cbn in *.
      now rewrite <- x.
    - cbn in *.
      now econstructor.
  Qed.
  Hint Resolve ktrans_guard: ticl.

  (** [ktrans] considers nondeterministic choices [Br n k] as a single step. 
      This is in contrast to CTrees (Chappe et al. 2022) which define [BrD n k] as
      a delayed-branching node, such that [ktrans] can take finitely many choices in one step.
      We make this choice because the [bind_aul_r] and [bind_aur_r] lemmas in [Bind.v]
      are very hard to prove with [BrD n k]. Yet, we did not disprove this fact either, 
      so we leave this as an open question.
  *)
  Lemma ktrans_br {X}: forall n (t: ictree E X) (k: fin' n -> ictree E X) w w',
      |Br n k, w| ↦ |t, w'| <->
        (exists (i: fin' n), t ≅ k i /\ w = w' /\ not_done w).
  Proof.
    split; intro H.
    - cbn in H; dependent induction H.
      exists i; intuition.
      step in H0; step; cbn in *.
      now rewrite <- x.
    - destruct H as (i & Heq & -> & Hd).
      econstructor; eauto.
  Qed.
  Hint Resolve ktrans_br: ticl.

  (** [ktrans] considers [Ret x] as a single step. *)
  Lemma ktrans_done {X}: forall (t: ictree E X) (w': World E) x,
      |Ret x, Pure| ↦ |t, w'| <-> (w' = Done x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
    - cbn in H; dependent destruction H; split; auto.
      step; cbn; rewrite <- x; step in H; cbn in H; auto.
    - destruct H as (-> & ->); constructor.
      reflexivity.
  Qed.
  Hint Resolve ktrans_done: ticl.

  (** [ktrans] considers [Ret x] as a single step. *)
  Lemma ktrans_finish {X}: forall (t: ictree E X) (w': World E) (e: E) (v: encode e) x,
      |Ret x, Obs e v| ↦ |t, w'| <->
        (w' = Finish e v x /\ t ≅ stuck).
  Proof.
    intros; split; intros.
     - cbn in H; dependent destruction H; split; auto.
      step; cbn; rewrite <- x; step in H; cbn in H; auto.
    - destruct H as (-> & ->); constructor.
      reflexivity.
  Qed.
  Hint Resolve ktrans_finish: ticl.

  (** [ktrans] considers [Vis e k] as a single step. *)
  Lemma ktrans_vis{X}: forall (t: ictree E X) (s s': World E) (e: E) (k: encode e -> ictree E X),
      |Vis e k, s| ↦ |t, s'| <->
        (exists (x: encode e), s' = Obs e x /\ k x ≅ t /\ not_done s).
  Proof.
    intros; split; intro TR.
    - cbn in TR.
      dependent induction TR.
      exists v; split; [reflexivity|split]; auto.
      transitivity t0; [now symmetry|].
      step; cbn; rewrite x; reflexivity.
    - destruct TR as (? & -> & <- & ?).
      econstructor; auto.
  Qed.
  Hint Resolve ktrans_vis: ticl.

  (** [ktrans] cannot step from an observation to a pure state. *)
  Lemma ktrans_pure_pred{X}: forall (t t': ictree E X) w,
      |t, w| ↦ |t', Pure| -> w = Pure.
  Proof.
    intros * H; cbn in H; dependent induction H; eauto.
  Qed.
  Hint Resolve ktrans_pure_pred: ticl.

  (** [ktrans] cannot step from a stuck state. *)
  Lemma ktrans_stuck{X}: forall (t: ictree E X) w w',
      ~ |stuck, w| ↦ |t, w'|.
  Proof.
    intros * Hcontra.
    cbn in Hcontra; dependent induction Hcontra; eauto.
  Qed.
  Hint Resolve ktrans_stuck: ticl.

  (** [ktrans] cannot step from a done world [w]. *)
  Lemma done_not_ktrans{X}: forall (t: ictree E X) w,
      is_done X w ->
      ~ (exists t' w', |t, w| ↦ |t', w'|).
  Proof.
    intros * Hret Htr.
    destruct Htr as (? & ? & ?).
    inv Hret;
      apply ktrans_not_done in H; inv H.
  Qed.
  Hint Resolve done_not_ktrans: ticl.

  (** [ktrans] cannot step from a done state. *)
  Lemma ktrans_done_inv{X}: forall (t t': ictree E X) (x: X) w,
      ~ |t, Done x| ↦ |t', w|.
  Proof.
    intros * Hcontra; cbn in Hcontra; dependent induction Hcontra; eauto; inv H.
  Qed.
  Hint Resolve ktrans_done_inv: ticl.

  (** [ktrans] cannot step from a finish state. *)
  Lemma ktrans_finish_inv{X}: forall (t t': ictree E X) (e: E) (v: encode e) (x: X) w,
      ~ |t, Finish e v x| ↦ |t', w|.
  Proof.
    intros * Hcontra; cbn in Hcontra; dependent induction Hcontra; eauto; inv H.
  Qed.
  Hint Resolve ktrans_finish_inv: ticl.

  Lemma ktrans_to_done_inv{X}: forall (t t': ictree E X) w (x: X),
      |t, w| ↦ |t', Done x| ->
      t' ≅ ICtree.stuck /\ w = Pure.
  Proof.
    intros.
    cbn in H.
    dependent induction H; intros; eauto.
    - inv H.
    - observe_equ x.
      rewrite Eqt in H.
      intuition.
  Qed.
  Hint Resolve ktrans_to_done_inv: ticl.

  Lemma ktrans_to_finish_inv{X}: forall (t t': ictree E X) w (e: E) (v: encode e) (x: X),
      |t, w| ↦ |t', Finish e v x| ->
      t' ≅ ICtree.stuck /\ w = Obs e v.
  Proof.
    intros.
    cbn in H.
    dependent induction H; intros; eauto.
    - inv H.
    - observe_equ x.
      rewrite Eqt in H.
      intuition.
  Qed.
  Hint Resolve ktrans_to_finish_inv: ticl.

  (** Left [ktrans] and [bind] lemma, if [t] steps to [t'], then [x <- t ;; k x] steps to [x <- t' ;; k x]. *)
  Lemma ktrans_bind_l{X Y}: forall (t t': ictree E Y) (k: Y -> ictree E X) w w',
      |t, w| ↦ |t', w'| ->
      not_done w' ->
      |x <- t ;; k x, w| ↦ |x <- t' ;; k x, w'|.
  Proof.
    intros; cbn in *.
    revert k.
    dependent induction H; intros; rewrite unfold_bind.
    - rewrite <- x0.
      econstructor; eauto.
    - rewrite <- x0.
      econstructor; eauto.
      eapply equ_clo_bind with (S:=eq).
      + step; cbn; rewrite <- x.
        step in H0; apply H0.
      + now intros * ->.
    - rewrite <- x0.
      econstructor; auto.
      eapply equ_clo_bind with (S:=eq).
      + rewrite <- H0.
        step; cbn; rewrite x.
        reflexivity.
      + now intros * ->.
    - inv H0.
    - inv H0.
  Qed.


  (** Auxiliary lemma for [ktrans_bind_inv], the inversion lemma for [ktrans] and [bind]. It is used to take cases
  on the transition of [t] and [t>>=k]. *)
  Opaque ICtree.stuck.
  Lemma ktrans_bind_inv_aux {X Y} (w w': World E)(T U: ictree' E Y) :
    ktrans_ T w U w' ->
    forall (t: ictree E X) (k: X -> ictree E Y) (u: ictree E Y),
      go T ≅ t >>= k ->
      go U ≅ u ->
      (* [t] steps, [t>>=k] steps *)
      (exists t', |t, w| ↦ |t', w'|
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
        (* [t] returns [x], [t>>=k] steps if [k x] steps *)
        (exists y w_, |t, w| ↦ |stuck, w_|
                 /\ done_eq y w_
                 /\ |k y, w| ↦ |u, w'|).
  Proof with (auto with ticl).
    intros TR.
    dependent induction TR; intros.
    - rewrite unfold_bind in H; unfold ktrans; cbn;
        desobs t0; observe_equ Heqt.
      + right.
        pose proof (ktrans_not_done (X:=Y) t t' w w' TR) as Hw.
        inv Hw; exists x.
        * exists (Done x).
          split; [|split]...
          rewrite <- H, <- H0; cbn; now apply KtransGuard.
        * exists (Finish e v x).
          split; [|split]...
          rewrite <- H, <- H0; cbn; now apply KtransGuard.
      + step in H; inv H.
      + pose proof (equ_guard_invE H).
        rewrite ictree_eta in H1.
        destruct (IHTR _ _ _ H1 H0)
          as [(t2 & TR2 & Hd & Eq2) |
               (x & w_ & TRr & ? & TRk)].
        * left.
          exists t2; split; [|split]...
        * right.
          inv H2.
          -- exists x0, (Done x0); split...
          -- exists x0, (Finish e v x0); split...
      + step in H; inv H.
    - rewrite unfold_bind in H1; unfold ktrans; cbn; desobs t0; observe_equ Heqt.
      + right; inv H.
        * exists x, (Done x).
          split; [|split]...
          rewrite <- H1; cbn; apply KtransBr with i...
          rewrite <- ictree_eta in H2.
          transitivity t; [symmetry|]...
        * exists x, (Finish e v x).
          split; [|split]...
          rewrite <- H1; cbn; apply KtransBr with i...
          rewrite <- ictree_eta in H2.
          transitivity t; [symmetry|]...
      + left.
        pose proof (equ_br_invT H1); subst.
        eapply equ_br_invE with i in H1.
        exists (k1 i); split; [|split]...
        * apply KtransBr with i...
        * rewrite <- H2, <- H1.
          now rewrite <- ictree_eta.
      + step in H1; inv H1.
      + step in H1; inv H1.
    - rewrite unfold_bind in H1; unfold ktrans; cbn; desobs t0; observe_equ Heqt.
      + right; inv H.
        * exists x, (Done x).
          split; [|split]...
          rewrite <- H1; cbn; apply KtransObs...
          rewrite <- ictree_eta in H2.
          transitivity t; [symmetry|]...
        * exists x, (Finish e0 v0 x).
          split; [|split]...
          rewrite <- H1; cbn; apply KtransObs...
          rewrite <- ictree_eta in H2.
          transitivity t; [symmetry|]...
      + step in H1; inv H1.
      + step in H1; inv H1.
      + left.
        pose proof (equ_vis_invT H1) as (_ & <-).
        eapply equ_vis_invE with v in H1.
        exists (k1 v); split; [|split]; auto with ticl.
        rewrite <- H1, <- H2.
        now rewrite <- ictree_eta.
    - rewrite unfold_bind in H0; unfold ktrans; cbn;
        desobs t0; observe_equ Heqt.
      + right.
        exists x0, (Done x0).
        split; [|split]...
        rewrite <- H1, H, <- H0; cbn.
        now apply KtransDone.
      + step in H0; inv H0.
      + step in H0; inv H0.
      + step in H0; inv H0.
    - rewrite unfold_bind in H0; unfold ktrans; cbn;
        desobs t0; observe_equ Heqt.
      + right.
        exists x0, (Finish e v x0).
        split; [|split]...
        rewrite <- H1, H, <- H0; cbn.
        now apply KtransFinish.
      + step in H0; inv H0.
      + step in H0; inv H0.
      + step in H0; inv H0.
  Qed.

  (** Inversion lemma for [ktrans] and [bind]. 
    If [x <- t ;; k x] steps to [u], then either:
    - [t] steps to [t'], [t>>=k] steps to [x <- t' ;; k x], and [t'] is not done.
    - [t] returns [x], [t>>=k] steps to [u] if [k x] steps.
  *)
  Lemma ktrans_bind_inv: forall {X Y} (w w': World E)
                           (t: ictree E X) (u: ictree E Y) (k: X -> ictree E Y),
      |x <- t ;; k x, w| ↦ |u, w'| ->
      (exists t', |t, w| ↦ |t', w'|
             /\ not_done w'
             /\ u ≅ x <- t' ;; k x) \/
        (* [t] returns [x], [t>>=k] steps if [k x] steps *)
        (exists y w_, |t, w| ↦ |stuck, w_|
                 /\ done_eq y w_
                 /\ |k y, w| ↦ |u, w'|).
  Proof.
    intros * TR.
    eapply ktrans_bind_inv_aux.
    apply TR.
    rewrite <- ictree_eta; reflexivity.
    rewrite <- ictree_eta; reflexivity.
  Qed.
  Hint Resolve ktrans_bind_inv: ticl.

End ICTreeTrans.

#[global] Hint Constructors
  ktrans_ not_done done_with vis_with: ticl.

#[global] Hint Resolve
  ktrans_stuck ktrans_br ktrans_vis ktrans_done
  ktrans_done_inv ktrans_finish can_step_not_done
  ktrans_not_done ktrans_finish_inv ktrans_bind_inv
  ktrans_to_done_inv ktrans_to_finish_inv
  ktrans_guard ktrans_pure_pred: ticl.

(** * Inversion lemmas for [ktrans] and [bind] *)
(** Inversion lemma for [ktrans] and [bind] with [Ret x]. 
    This is a bit forward looking, as it uses the notion
    of strong bisimulation [sbisim] to prove the inversion lemma. This is because any strongly bisimilar tree
    to [Ret x], for example [Guard ... Guard (Ret x)] 
    behaves like a return in the context of [ktrans] and [bind].
  *)
From TICL Require Import ICTree.SBisim.
Local Open Scope ticl_scope.
Local Typeclasses Opaque sbisim.
Local Typeclasses Opaque equ.
Lemma ktrans_sbisim_ret `{Encode E} {X Y}:
  forall (t : ictree E X) (k: X -> ictree E Y) t' x w w',
  t ~ Ret x ->
  |x <- t;; k x, w| ↦ |t', w'| ->
  |k x, w| ↦ |t', w'|.
Proof.
  intros.
  apply ktrans_bind_inv in H1.
  __eplayR_sbisim.
  pose proof (trans_val_inv TR).
  cbn in H1.
  rewrite <- H0 in TR.
  clear EQ H0 x1.
  unfold trans in TR.
  remember (observe t) as T.
  remember (observe stuck) as S.
  remember (val x) as V.
  clear HeqT t.
  destruct H1 as [(t2 & TR2 & Hd & Eq2) |
                   (y & w_ & TRr & ? & TRk)].
  - induction TR; ddestruction HeqV.
    + apply IHTR; auto.
      now apply ktrans_guard in TR2.
    + inv TR2; inv Hd.
  - induction TR; ddestruction HeqV.
    + apply IHTR; auto.
      assert(TRr': |Guard t, w| ↦ |stuck, w_|)
        by now apply TRr. clear TRr.
      rewrite ktrans_guard in TRr'.
      apply TRr'.
    + ddestruction TRr; ddestruction H1; auto.
Qed.

(** Inversion lemma for terminating [t] with [Ret x]. 
    If it terminates with [Done x], then [t] is strongly bisimilar to [Ret x] and the world is [Pure].
*)
Local Opaque ICtree.stuck.
Lemma ktrans_to_done `{Encode E} {X}:
  forall (t: ictree E X) (x: X) w,
    |t, w| ↦ |ICtree.stuck, Done x| ->
    (t ~ Ret x /\ w = Pure).
Proof.
  intros.
  cbn in H0.
  rewrite (ictree_eta t).
  remember (observe t) as T.
  remember (observe stuck) as S.
  remember (Done x) as D.
  clear HeqT t.
  induction H0; subst.
  - rewrite sb_guard.
    rewrite (ictree_eta t).
    apply IHktrans_; auto.
  - inv H0.
  - inv HeqD.
  - ddestruction HeqD; auto.
  - ddestruction HeqD.
Qed.

(** Inversion lemma for terminating [t] with [Ret x]. 
    If it terminates with [Finish e v x], then [t] is strongly bisimilar to [Ret x] and the world is [Obs e v].
*)
Lemma ktrans_to_finish `{Encode E} {X}:
  forall (t: ictree E X) (e: E) (v: encode e) (x: X) w,
    |t, w| ↦ |ICtree.stuck, Finish e v x| ->
    (t ~ Ret x /\ w = Obs e v).
Proof.
  intros.
  cbn in H0.
  rewrite (ictree_eta t).
  remember (observe t) as T.
  remember (observe stuck) as S.
  remember (Finish e v x) as D.
  clear HeqT t.
  induction H0; subst.
  - rewrite sb_guard.
    rewrite (ictree_eta t).
    apply IHktrans_; auto.
  - inv H0.
  - inv HeqD.
  - ddestruction HeqD.
  - ddestruction HeqD; auto.
Qed.

Lemma ktrans_bind_r_done `{Encode E} {X Y}: forall (t: ictree E X) t' (k: X -> ictree E Y) (u: ictree E Y) x w w',
  |t, w| ↦ |ICtree.stuck, Done x| ->
  |k x, w| ↦ |t', w'| ->
  |x <- t ;; k x, w| ↦ |t', w'|. 
Proof.
  intros; cbn in *.
  generalize dependent k.
  dependent induction H0; intros; rewrite unfold_bind.
    - rewrite <- x1.
      econstructor; eauto.
    - inv H0.
    - now rewrite <- x2.      
Qed.

Lemma ktrans_bind_r_finish `{Encode E} {X Y}: forall (t: ictree E X) t' (k: X -> ictree E Y) (u: ictree E Y) x w w',
  |t, w| ↦ |ICtree.stuck, Done x| ->
  |k x, w| ↦ |t', w'| ->
  |x <- t ;; k x, w| ↦ |t', w'|. 
Proof.
  intros; cbn in *.
  generalize dependent k.
  dependent induction H0; intros; rewrite unfold_bind.
    - rewrite <- x1.
      econstructor; eauto.
    - inv H0.
    - now rewrite <- x2.      
Qed.

(** * Kripke setoid for ictrees and [sbisim] *)
(** Kripke transition system for ictrees is a Kripke setoid
with respect to strong bisimulation [sbisim]. This is a very powerful result, and sufficient to prove that Ticl formulas
are invariant under strong bisimulation. *)
Global Instance KripkeSetoidSBisim `{HE: Encode E} {X}:
    @KripkeSetoid ictree E HE ictree_kripke X (sbisim eq) _.
Proof.
  repeat red; intros.
  apply ktrans_trans in H0 as
      (l & TR &
         [ (? & ? & ?) |
           [(e & x & ? & ? & ?) |
             [(x & ? & ? & Ht & ?) |
               (e & v & x & ? & ? & Ht & ?)]]]); subst;
    destruct (SBisim.sbisim_trans (X:=X) _ _ _ _ eq H TR)
    as (l' & c1' & ? & <- & ?); exists c1'.
  - split; [apply ktrans_trans|auto].
    exists tau; split; auto.
  - split; [apply ktrans_trans|auto].
    exists (obs e x); split; auto.
    right; left.
    exists e, x; intuition.
  - split; [apply ktrans_trans|auto].
    exists (val x); split; auto.
    right; right; left.
    pose proof trans_val_inv H0.
    exists x; intuition.
  - split; [apply ktrans_trans|auto].
    exists (val x); split; auto.
    right; right; right.
    pose proof trans_val_inv H0.
    exists e, v, x; intuition.
Defined.
