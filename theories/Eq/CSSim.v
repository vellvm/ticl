From Coq Require Import
     Lia
     Basics
     Fin
     RelationClasses
     Program.Equality
     Logic.Eqdep.

From Coinduction Require Import all.

From ITree Require Import Core.Subevent.

From CTree Require Import
     CTree
     Utils
     Eq.Equ
     Eq.Shallow
     Eq.Trans
     Eq.SSim.

From RelationAlgebra Require Export
     rel srel.

Import CoindNotations.
Import CTree.
Set Implicit Arguments.

(* TODO: Decide where to set this *)
Arguments trans : simpl never.

Section CompleteStrongSim.

(*|
Complete strong simulation [css].
|*)
  Program Definition css {E F C D : Type -> Type} {X Y : Type}
    (L : rel (@label E) (@label F)) : mon (ctree E C X -> ctree F D Y -> Prop) :=
    {| body R t u :=
        ss L R t u /\ (forall l u', trans l u u' -> exists l' t', trans l' t t')
    |}.
  Next Obligation.
    split; eauto. intros.
    edestruct H0 as (? & ? & ? & ? & ?); repeat econstructor; eauto.
  Qed.

End CompleteStrongSim.

Definition cssim {E F C D X Y} L :=
  (gfp (@css E F C D X Y L) : hrel _ _).

Module CSSimNotations.

  (*| css (complete simulation) notation |*)
  Notation "t (⪅ L ) u" := (cssim L t u) (at level 70).
  Notation "t ⪅ u" := (cssim eq t u) (at level 70).
  Notation "t [⪅ L ] u" := (css L _ t u) (at level 79).
  Notation "t [⪅] u" := (css eq _ t u) (at level 79).

End CSSimNotations.

Import CSSimNotations.

Ltac fold_cssim :=
  repeat
    match goal with
    | h: context[gfp (@css ?E ?F ?C ?D ?X ?Y ?L)] |- _ => fold (@cssim E F C D X Y L) in h
    | |- context[gfp (@css ?E ?F ?C ?D ?X ?Y ?L)]      => fold (@cssim E F C D X Y L)
    end.

(* Ltac __coinduction_cssim R H := *)
(*   (try unfold cssim); *)
(*   apply_coinduction; fold_cssim; intros R H. *)

Tactic Notation "__step_cssim" :=
  match goal with
  | |- context[@cssim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold cssim;
      step;
      fold (@cssim E F C D X Y L)
  end.

#[local] Tactic Notation "step" := __step_cssim || step.

(* #[local] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) := *)
(*   __coinduction_cssim R H || coinduction R H. *)

Ltac __step_in_cssim H :=
  match type of H with
  | context[@cssim ?E ?F ?C ?D ?X ?Y ?LR] =>
      unfold cssim in H;
      step in H;
      fold (@cssim E F C D X Y L) in H
  end.

#[local] Tactic Notation "step" "in" ident(H) := __step_in_cssim H || step in H.

Import CTreeNotations.
Import EquNotations.

Section cssim_homogenous_theory.

  Context {E B : Type -> Type} {X : Type}
          {L: relation (@label E)}.

  Notation css := (@css E E B B X X).
  Notation cssim  := (@cssim E E B B X X).

  Lemma cssim_subrelation : forall (t t' : ctree E B X) L',
      subrelation L L' -> cssim L t t' -> cssim L' t t'.
  Proof.
    intros. revert t t' H0. unfold cssim at 2. coinduction R CH.
    intros. step in H0. simpl; split; intros; cbn in H0; destruct H0 as [H0' H0''].
    - cbn in H0'; apply H0' in H1 as (? & ? & ? & ? & ?);
        apply H in H2. exists x, x0. auto.
    - apply H0'' in H1 as (? & ? & ?).
      do 2 eexists; apply H0.
  Qed.

(*|
    Various results on reflexivity and transitivity.
|*)
  #[global] Instance refl_csst {LR: Reflexive L} {C: Chain (css L)}: Reflexive `C.
  Proof.
    apply Reflexive_chain; cbn; eauto 9.
  Qed.

  #[global] Instance square_csst {LT: Transitive L} {C: Chain (css L)}: Transitive `C.
  Proof.
    apply Transitive_chain.
    cbn. intros ????? [xy xy'] [yz yz'].
    split.
    - intros ?? xx'.
      destruct (xy _ _ xx') as (l' & y' & yy' & ? & ?).
      destruct (yz _ _ yy') as (l'' & z' & zz' & ? & ?).
      eauto 8.
    - intros ?? xx'.
      destruct (yz' _ _ xx') as (l'' & z' & zz').
      destruct (xy' _ _ zz') as (l' & y' & yy').
      eauto 8.
  Qed.

  (*| PreOrder |*)
  #[global] Instance PreOrder_csst {LPO: PreOrder L} {C: Chain (css L)}: PreOrder `C.
  Proof. split; typeclasses eauto. Qed.

End cssim_homogenous_theory.

Section cssim_heterogenous_theory.

  Arguments label: clear implicits.
  Context {E F C D: Type -> Type} {X Y: Type}
          {L: rel (@label E) (@label F)}.

  Notation css := (@css E F C D X Y).
  Notation cssim  := (@cssim E F C D X Y).

(*|
   Strong simulation up-to [equ] is valid
   ----------------------------------------
|*)

  Lemma equ_clos_csst {c: Chain (css L)}:
    forall x y, equ_clos `c x y -> `c x y.
  Proof.
    apply tower.
    - intros ? INC x y [x' y' x'' y'' EQ' EQ''] ??. red.
      apply INC; auto.
      econstructor; eauto.
      apply leq_infx in H.
      now apply H.
    - intros a b ?? [x' y' x'' y'' EQ' [SIM COMP]].
      split; intros ?? tr.
      + rewrite EQ' in tr.
        edestruct SIM as (l' & ? & ? & ? & ?); eauto.
        exists l',x0; intuition.
        rewrite <- Equu; auto.
      + rewrite <- Equu in tr.
        edestruct COMP as (l' & ? & ?); eauto.
        setoid_rewrite EQ'. eauto.
   Qed.

  #[global] Instance equ_clos_csst_goal {c: Chain (css L)} :
    Proper (equ eq ==> equ eq ==> flip impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_csst; econstructor; [eauto | | symmetry; eauto]; assumption.
  Qed.

  #[global] Instance equ_clos_csst_ctx  {c: Chain (css L)} :
    Proper (equ eq ==> equ eq ==> impl) `c.
  Proof.
    cbn; intros ? ? eq1 ? ? eq2 H.
    apply equ_clos_csst; econstructor; [symmetry; eauto | | eauto]; assumption.
  Qed.

  #[global] Instance equ_css_closed_goal {r} : Proper (equ eq ==> equ eq ==> flip impl) (css L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros [H H0]; split; intros l t0 TR.
    - rewrite tt' in TR. destruct (H _ _ TR) as (? & ? & ? & ? & ?).
      exists x, x0; auto; rewrite uu'; auto.
    - rewrite uu' in TR. destruct (H0 _ _ TR) as (? & ? & ?).
      exists x, x0; eauto; rewrite tt'; auto.
  Qed.

  #[global] Instance equ_css_closed_ctx {r} : Proper (equ eq ==> equ eq ==> impl) (css L r).
  Proof.
    intros t t' tt' u u' uu'; cbn; intros [H H0]; split; intros l t0 TR.
    - rewrite <- tt' in TR. destruct (H _ _ TR) as (? & ? & ? & ? & ?).
      exists x, x0; auto; rewrite <- uu'; auto.
    - rewrite <- uu' in TR. destruct (H0 _ _ TR) as (? & ? & ?).
      exists x, x0; auto; rewrite <- tt'; auto.
  Qed.

  Lemma is_stuck_css : forall (t: ctree E C X) (u: ctree F D Y) R,
      css L R t u -> is_stuck t <-> is_stuck u.
  Proof.
    split; intros; intros ? ? ?.
    - apply H in H1 as (? & ? & ?). now apply H0 in H1.
    - apply H in H1 as (? & ? & ? & ? & ?). now apply H0 in H1.
  Qed.

  Lemma is_stuck_cssim :  forall (t: ctree E C X) (u: ctree F D Y),
      t (⪅ L) u -> is_stuck t <-> is_stuck u.
  Proof.
    intros. step in H. eapply is_stuck_css; eauto.
  Qed.

  Lemma css_is_stuck : forall (t : ctree E C X) (u: ctree F D Y) R,
      is_stuck t -> is_stuck u -> css L R t u.
  Proof.
    split; intros.
    - cbn. intros. now apply H in H1.
    - now apply H0 in H1.
  Qed.

  Lemma cssim_is_stuck : forall (t : ctree E C X) (u: ctree F D Y),
      is_stuck t -> is_stuck u -> t (⪅ L) u.
  Proof.
    intros. step. now apply css_is_stuck.
  Qed.

End cssim_heterogenous_theory.


(*|
Up-to [bind] context simulations
----------------------------------
We have proved in the module [Equ] that up-to bind context is
a valid enhancement to prove [equ].
We now prove the same result, but for strong simulation.
|*)

Section bind.
  Arguments label: clear implicits.
  Obligation Tactic := idtac.

  Context {E F C D: Type -> Type} {X X' Y Y': Type}
    (L : hrel (@label E) (@label F)) (R0 : rel X Y).

(*|
Specialization of [bind_ctx] to a function acting with [cssim] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Lemma bind_chain_gen
    (RR : rel (label E) (label F))
    (ISVR : is_update_val_rel L R0 RR)
    (HL: Respects_val RR)
    {R : Chain (@css E F C D X' Y' L)} :
    forall (t : ctree E C X) (t' : ctree F D Y) (k : X -> ctree E C X') (k' : Y -> ctree F D Y'),
      cssim RR t t' ->
      (* (forall x x', L0 (val x) (val x') -> elem R (k x) (k' x')) -> *)
      (forall x x', R0 x x' -> (elem R (k x) (k' x') /\ exists l t', trans l (k x) t')) ->
      elem R (bind t k) (bind t' k').
  Proof.
    apply tower.
    - intros ? INC ? ? ? ? tt' kk' ? ?.
      apply INC. apply H. apply tt'.
      intros x x' xx'. split. apply leq_infx in H. apply H. now apply kk'.
      edestruct kk'; eauto.
    - intros ? ? ? ? ? ? tt' kk'.
      step in tt'.
      destruct tt' as [tt tt'].
      split.
      + cbn; intros * STEP.
        apply trans_bind_inv in STEP as [(?H & ?t' & STEP & EQ) | (v & STEPres & STEP)].
        * apply tt in STEP as (? & ? & ? & ? & ?).
          do 2 eexists; split; [| split].
          apply trans_bind_l; eauto.
          ++ intro Hl. destruct Hl.
             apply ISVR in H3; etrans.
             inversion H3; subst. apply H0. constructor. apply H5. constructor.
          ++ rewrite EQ.
             apply H.
             apply H2.
             intros * HR.
             split.
             now apply (b_chain x), kk'.
             apply (kk' _ _ HR).
          ++ apply ISVR in H3; etrans.
             destruct H3. exfalso. apply H0. constructor. eauto.
        * apply tt in STEPres as (u' & ? & STEPres & EQ' & ?).
          apply ISVR in H0; etrans.
          dependent destruction H0.
          2 : exfalso; apply H0; constructor.
          pose proof (trans_val_inv STEPres) as EQ.
          rewrite EQ in STEPres.
          specialize (kk' v v2 H0).
          apply kk' in STEP as (u'' & ? & STEP & EQ'' & ?); cbn in *.
          do 2 eexists; split.
          eapply trans_bind_r; eauto.
          split; auto.
      + cbn; intros * STEP.
        apply trans_bind_inv_l in STEP as (l' & t2' & STEP).
        apply tt' in STEP as (l'' & t1' & TR1).
        destruct l''.
        do 2 eexists; apply trans_bind_l; eauto; intros abs; inv abs.
        do 2 eexists; apply trans_bind_l; eauto; intros abs; inv abs.
        apply trans_val_invT in TR1 as ?. subst X0.
        apply trans_val_inv in TR1 as ?. rewrite H0 in TR1.
        pose proof TR1 as tmp.
        apply tt in tmp as (? & ? & TR & ? & ?).
        assert (is_val x0) by (eapply HL; eauto; constructor).
        inv H3; pose proof trans_val_invT TR; subst X0.
        specialize (kk' v x2).
        destruct kk'.
        apply ISVR in H2; etrans.
        dependent destruction H2; auto. exfalso; apply H2; constructor.
        edestruct H4 as (? & ? & ?); eauto.
        eapply trans_bind_r in H5; eauto.
  Qed.

End bind.

(* CHECKPOINT *)

(*|
Expliciting the reasoning rule provided by the up-to principles.
Note: could be refined so that the third hypothesis only quantified on [x] that are related to some [y] by [L].
|*)
Lemma csst_clo_bind {E F C D: Type -> Type}
      {X X' Y Y' : Type} {L: rel (@label E) (@label F)} {HL: Respects_val L} (t1 : ctree E C X) (t2 : ctree F D X')
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y') RR:
		t1 (⪅ L) t2 ->
    (forall x y, L (val x) (val y) -> (csst L RR) (k1 x) (k2 y)) ->
    (forall x, exists l t', trans l (k1 x) t') ->
    csst L RR (t1 >>= k1) (t2 >>= k2).
Proof.
  intros.
  apply (ft_t (@bind_ctx_cssim_t E F C D X Y X' Y' _ _ L HL)).
  apply in_bind_ctx; auto.
  intros ? ? Hl; split; auto.
Qed.

(*|
Specializing the congruence principle for [~]
|*)
Lemma cssim_clo_bind {E F C D: Type -> Type}
      {X X' Y Y' : Type} L {HL: Respects_val L} (t1 : ctree E C X) (t2 : ctree F D X')
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y'):
		t1 (⪅L) t2 ->
    (forall x x', L (val x) (val x') -> k1 x (⪅L) k2 x') ->
    (forall x, exists l t', trans l (k1 x) t') ->
    t1 >>= k1 (⪅L) t2 >>= k2
.
Proof.
  intros.
  apply (ft_t (@bind_ctx_cssim_t E F C D X Y X' Y' _ _ L HL)).
  apply in_bind_ctx; auto.
  intros ? ? Hl; split; auto.
  apply H2; auto.
Qed.

(*|
And in particular, we can justify rewriting [⪅] to the left of a [bind].
|*)
Lemma bind_cssim_cong_gen {E F C D X X' Y Y'} RR (L : rel _ _)
      {HL: Respects_val L} (t1 : ctree E C X) (t2 : ctree F D X')
      (k1 : X -> ctree E C Y) (k2 : X' -> ctree F D Y'):
    cssim L t1 t2 ->
    (forall x x', L (val x) (val x') -> csst L RR (k1 x) (k2 x')) ->
    (forall x, exists l t', trans l (k1 x) t') ->
    csst L RR (CTree.bind t1 k1) (CTree.bind t2 k2).
Proof.
  intros; eapply csst_clo_bind; red in H2; eauto.
Qed.

(* TODO: This has been specialized to [eq] rather than any [L] respecting [val] as in the other cases, it should be regeneralized. *)
(*|
Ltac automation rule for [bind] and [cssim]
|*)
Ltac __upto_bind_cssim :=
  match goal with
    |- @cssim _ _ _ _ ?X ?X' _ _ _ (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T') _ _) =>
      apply cssim_clo_bind
  | |- body (t (@css ?E ?E ?C ?C ?X ?X _ _ eq)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (ft_t (@bind_ctx_cssim_eq_t E C T X _)), in_bind_ctx
  | |- body (bt (@css ?E ?E ?C ?C ?X ?X _ _ eq)) ?R (CTree.bind (T := ?T) _ _) (CTree.bind (T := ?T) _ _) =>
      apply (fbt_bt (@bind_ctx_cssim_eq_t E C T X _)), in_bind_ctx
  end.

Ltac __upto_bind_eq_cssim :=
  __upto_bind_cssim; [reflexivity | intros ? _ _].

Ltac __play_cssim := step; cbn; split; [intros ? ? ?TR | etrans].

Ltac __play_cssim_in H :=
  step in H;
  cbn in H; edestruct H as [(? & ? & ?TR & ?EQ & ?HL) ?PROG];
  clear H; [etrans |].

Ltac __eplay_cssim :=
  match goal with
  | h : @cssim ?E ?F ?C ?D ?X ?Y _ _ ?L _ _ |- _ =>
      __play_cssim_in h
  end.

#[local] Tactic Notation "play" := __play_cssim.
#[local] Tactic Notation "play" "in" ident(H) := __play_cssim_in H.
#[local] Tactic Notation "eplay" := __eplay_cssim.

Section Proof_Rules.
  Arguments label: clear implicits.
  Context {E C : Type -> Type} {X: Type}.

  Lemma step_css_ret_gen {Y F D}(x : X) (y : Y)
        {L: rel (label E) (label F)} {R : rel (ctree E C X) (ctree F D Y)}:
    R stuckD stuckD ->
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L (val x) (val y) ->
    css L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros Rstuck PROP Lval.
    cbn; split; intros ? ? TR; inv_trans; subst;
      cbn; eexists; eexists; intuition; etrans;
      now rewrite EQ.
  Qed.

  Lemma step_css_ret  {Y F D}(x : X) (y : Y)
        {L: rel (label E) (label F)} {R : rel (ctree E C X) (ctree F D Y)}:
    L (val x) (val y) ->
    cssbt L R (Ret x : ctree E C X) (Ret y : ctree F D Y).
  Proof.
    intros.
    apply step_css_ret_gen.
    - step. intros. apply css_is_stuck; apply stuckD_is_stuck.
    - typeclasses eauto.
    - apply H.
  Qed.

(*|
The vis nodes are deterministic from the perspective of the labeled
transition system, stepping is hence symmetric and we can just recover
the itree-style rule.
|*)
  (* LEF: Here, I got lazy -- it would be nice to have [k': Z' -> ctree F D Y]
     see [step_ss0_vis_gen] *)
   Lemma step_css_vis_gen {Y Z F D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (forall x, R (k x) (k' x)) ->
    (forall x, L (obs e x) (obs f x)) ->
    css L R (Vis e k) (Vis f k').
  Proof.
    split.
    - apply step_ss_vis_gen; eauto.
    - intros. inv_trans; subst; etrans.
    Unshelve. auto.
  Qed.

  Lemma step_css_vis {Y Z F D} (e : E Z) (f: F Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F D Y) (R L: rel _ _) :
    (forall x, csst L R (k x) (k' x)) ->
    (forall x, L (obs e x) (obs f x)) ->
    cssbt L R (Vis e k) (Vis f k').
  Proof.
    intros * EQ.
    apply step_css_vis_gen; auto.
    typeclasses eauto.
  Qed.

(*|
Same goes for visible tau nodes.
|*)
  Lemma step_ss_step_gen{Y F D}
        (t : ctree E C X) (t' : ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    (R t t') ->
    L tau tau ->
    css L R (Step t) (Step t').
  Proof.
    intros PR EQs ?.
    cbn; split; intros ? ? TR; inv_trans; subst;
      eexists; eexists; intuition.
    - now rewrite EQ.
  Qed.

  Lemma step_css_step{Y F D}
        (t : ctree E C X) (t' : ctree F D Y) (R L: rel _ _) :
    L tau tau ->
    (csst L R t t') ->
    cssbt L R (Step t) (Step t').
  Proof.
    intros. eapply step_ss_step_gen; eauto.
    typeclasses eauto.
  Qed.

(*|
    When matching visible brs one against another, in general we need to explain how
    we map the branches from the left to the branches to the right.
    A useful special case is the one where the arity coincide and we simply use
    the identity in both directions. We can in this case have [n] rather than [2n]
    obligations.
|*)
  (** LEF: Here I need to show [Z] is inhabited,
      I think the way to go is to axiomatize it. Maybe it's possible
      to extract a [Z] from [HasTau: B1 -< C]? YZ says no,
      so maybe the extra restriction is truly needed. *)
  Lemma step_ss_brS_gen{Y Z Z' F D} (c : C Z) (d: D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    inhabited Z ->
    (forall x, exists y, R (k x) (k' y)) ->
    css L R (BrS c k) (BrS d k').
  Proof.
    intros PROP ? EX EQs; cbn; split;
      intros ? ? TR; inv_trans; subst.
    - destruct (EQs x) as [z HR].
      do 2 eexists; intuition.
      rewrite EQ; eassumption.
    - exists tau; eexists; intuition.
      Unshelve. apply (proj1_sig EX).
  Qed.

  Lemma step_css_brS {Y Z Z' F D} (c : C Z) (d: D Z')
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    L tau tau ->
    inhabited Z ->
    (forall x, exists y, csst L R (k x) (k' y)) ->
    cssbt L R (BrS c k) (BrS d k').
  Proof.
    intros.
    apply step_ss_brS_gen; auto.
    typeclasses eauto.
  Qed.

  Lemma step_css_brS_id_gen {Y Z F } (c : C Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R L: rel _ _) :
    (Proper (equ eq ==> equ eq ==> impl) R) ->
    L tau tau ->
    inhabited Z ->
    (forall x, R (k x) (k' x)) ->
    css L R (BrS c k) (BrS c k').
  Proof.
    intros PROP ? ? EQs.
    apply step_ss_brS_gen; auto.
    intros x; exists x; auto.
  Qed.

  Lemma step_css_brS_id {Y Z F } (c : C Z)
        (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R L: rel _ _) :
    L tau tau ->
    inhabited Z ->
    (forall x, csst L R (k x) (k' x)) ->
    cssbt L R (BrS c k) (BrS c k').
  Proof.
    apply step_css_brS_id_gen.
    typeclasses eauto.
  Qed.

(*|
For invisible nodes, the situation is different: we may kill them, but that
execution cannot act as going under the guard.
|*)
  Lemma step_css_guard_gen {Y F D}
        (t : ctree E C X) (t' : ctree F D Y) (R L: rel _ _) :
    css L R t t' ->
    css L R (Guard t) (Guard t').
  Proof.
    intros EQ; cbn; split; intros ? ? TR; inv_trans; subst.
    - apply EQ in TR as (? & ? & ? & ? & ?).
      do 2 eexists; intuition; subst; [apply trans_guard; eauto | eauto | eauto].
    - apply EQ in TR as (? & ? & ?).
      do 2 eexists; subst; intuition.
      apply trans_guard; eauto.
  Qed.

  Lemma step_css_guard {Y F D}
        (t : ctree E C X) (t' : ctree F D Y) (R L : rel _ _) :
    cssbt L R t t' ->
    cssbt L R (Guard t) (Guard t').
  Proof.
    apply step_css_guard_gen.
  Qed.

  Lemma step_css_brD_l_gen {Y F D Z} (c : C Z)
    (k : Z -> ctree E C X) (t' : ctree F D Y) (R L: rel _ _) :
    (forall x, css L R (k x) t') ->
    inhabited Z ->
    css L R (BrD c k) t'.
  Proof.
    intros EQs ?; cbn; split;
      intros ? ? TR; inv_trans; subst.
    - apply EQs in TR as (u' & ? & TR' & EQ' & ?); eauto.
    - pose proof (proj1_sig X0) as z.
      edestruct (EQs z) as (tt & ? & ? & ?); eauto.
      do 2 eexists; intuition.
      eapply trans_brD; eauto.
  Qed.

  Lemma step_css_brD_l {Y F D Z} (c : C Z)
    (k : Z -> ctree E C X) (t' : ctree F D Y) (R L: rel _ _) :
    (forall x, cssbt L R (k x) t') ->
    inhabited Z ->
    cssbt L R (BrD c k) t'.
  Proof.
    apply step_css_brD_l_gen.
  Qed.

  Lemma step_css_brD_r_gen {Y F D Z} (c : D Z)
    (t : ctree E C X) (k : Z -> ctree F D Y) (R L: rel _ _) z :
    (exists l t', trans l t t') ->
    css L R t (k z) ->
    css L R t (BrD c k).
  Proof.
    simpl. intros * (? & ? & TR) CSS; split; intros * TR'.
    - apply CSS in TR' as (? & ? & ? & ? & ?); subst.
      do 2 eexists; intuition; eauto; econstructor; eauto.
    - apply trans_brD_inv in TR' as (? & ?).
      do 2 eexists; intuition; eauto.
  Qed.

  Lemma step_css_brD_r {Y F D Z} (c : D Z)
        (t : ctree E C X) (k : Z -> ctree F D Y) (R L: rel _ _) z :
    (exists l t', trans l t t') ->
    cssbt L R t (k z) ->
    cssbt L R t (BrD c k).
  Proof.
    intros. eapply step_css_brD_r_gen; eauto. apply H0.
  Qed.

  Lemma step_css_brD_gen {Y F D Z Z'} (c: C Z) (c': D Z') x
    (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (exists l' t', trans l' (k x) t') ->
    (forall x, exists y, css L R (k x) (k' y)) ->
    css L R (BrD c k) (BrD c' k').
  Proof.
    intros ? EQs. split; intros.
    - apply step_ss_brD_gen. intros.
      destruct (EQs x0). destruct H0. eauto.
    - destruct H as (? & ? & ?). etrans.
  Qed.

  Lemma step_css_brD {Y F D Z Z'} (c: C Z) (c': D Z') x
        (k : Z -> ctree E C X) (k' : Z' -> ctree F D Y) (R L: rel _ _) :
    (forall x, exists y, cssbt L R (k x) (k' y)) ->
    (exists l' t', trans l' (k x) t') ->
    cssbt L R (BrD c k) (BrD c' k').
  Proof.
    intros; eapply step_css_brD_gen; eauto.
  Qed.

  Lemma step_css_brD_id_gen {Y F Z} (c: C Z) x
        (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R L: rel _ _) :
    (forall x, css L R (k x) (k' x)) ->
    (exists l' t', trans l' (k x) t') ->
    css L R (BrD c k) (BrD c k').
  Proof.
    intros; eapply step_css_brD_gen; eauto.
  Qed.

  Lemma step_css_brD_id {Y F Z} (c: C Z) x
        (k : Z -> ctree E C X) (k' : Z -> ctree F C Y) (R L: rel _ _) :
    (forall x, cssbt L R (k x) (k' x)) ->
    (exists l' t', trans l' (k x) t') ->
    cssbt L R (BrD c k) (BrD c k').
  Proof.
    apply step_css_brD_id_gen.
  Qed.

End Proof_Rules.

Section WithParams.

  Context {E F C D : Type -> Type}.
  Context (L : rel (@label E) (@label F)).

(*|
Note that with visible schedules, nary-spins are equivalent only
if neither are empty, or if both are empty: they match each other's
tau challenge infinitely often.
With invisible schedules, they are always equivalent: neither of them
produce any challenge for the other.
|*)
  Lemma spinS_gen_nonempty : forall {Z Z' X Y} (c: C X) (c': D Y) (x: X) (y: Y) (L : rel _ _),
    L tau tau ->
    cssim L (@spinS_gen E C Z X c) (@spinS_gen F D Z' Y c').
  Proof.
    intros.
    red. coinduction R CH.
    simpl; split; intros l t' TR; rewrite ctree_eta in TR; cbn in TR;
    apply trans_brS_inv in TR as (_ & EQ & ->);
      do 2 eexists;
      rewrite ctree_eta; cbn; intuition.
    - econstructor; auto.
    - rewrite EQ; eauto.
    - eapply H.
    - econstructor; auto.
  Qed.

(*|
Inversion principles
--------------------
|*)
  Lemma cssim_ret_inv X Y (r1 : X) (r2 : Y) :
    (Ret r1 : ctree E C X) (⪅L) (Ret r2 : ctree F D Y) ->
    L (val r1) (val r2).
  Proof.
    intros.
    eplay.
    inv_trans.
    now subst.
  Qed.

  Lemma cssim_vis_inv_type {X X1 X2}
        (e1 : E X1) (e2 : E X2) (k1 : X1 -> ctree E C X) (k2 : X2 -> ctree E C X) (x : X1):
    Vis e1 k1 ⪅ Vis e2 k2 ->
    X1 = X2.
  Proof.
    intros.
    eplay.
    subst.
    inv_trans. reflexivity.
    Unshelve. auto.
  Qed.

  Lemma cssbt_eq_vis_inv {X Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) R :
    cssbt eq R (Vis e1 k1) (Vis e2 k2) ->
    e1 = e2 /\ forall x, csst eq R (k1 x) (k2 x).
  Proof.
    intros.
    split.
    - edestruct H as [(? & ? & ?TR & ?EQ & ?HL) ?PROG].
      etrans. subst.
      now inv_trans.
    - intros.
      edestruct H as [(? & ? & ? & ? & ?) _].
      etrans. subst. inv_trans. subst. apply H1.
    Unshelve. auto.
  Qed.

  Lemma cssim_eq_vis_inv {X Y} (e1 e2 : E Y) (k1 k2 : Y -> ctree E C X) (x : Y) :
    Vis e1 k1 ⪅ Vis e2 k2 ->
    e1 = e2 /\ forall x, k1 x ⪅ k2 x.
  Proof.
    intros.
    (* Why doesn't apply work directly here? *)
    epose proof (proj1 (enhanced_gfp (@css E E C C X X _ _ eq) _ _)). apply H0 in H. clear H0.
    step in H. apply cssbt_eq_vis_inv in H; auto.
    destruct H. split; auto.
    intro. subst. specialize (H0 x0).
    apply (proj1 (t_gfp_bt (@css E E C C X X _ _ eq) _ _)) in H0. apply H0.
  Qed.

  Lemma cssim_brS_inv {X Y Z Z'}
        c1 c2 (k1 : X -> ctree E C Z) (k2 : Y -> ctree F D Z') :
    BrS c1 k1 (⪅L) BrS c2 k2 ->
    (forall i1, exists i2, k1 i1 (⪅L) k2 i2).
  Proof.
    intros.
    eplay.
    inv_trans; eexists; eauto.
  Qed.

  Lemma css_brD_l_inv :
    forall {X Y Z} (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L R x,
      css L R (BrD c k) t ->
      (exists l t', trans l (k x) t') ->
      css L R (k x) t.
  Proof.
    split.
    - eapply ss_brD_l_inv. now apply H.
    - intros. apply H0.
  Qed.

  Lemma cssim_brD_l_inv :
    forall {X Y Z} (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L x,
      BrD c k (⪅L) t ->
      (exists l t', trans l (k x) t') ->
      k x (⪅L) t.
  Proof.
    intros. step. step in H. eapply css_brD_l_inv. apply H. auto.
  Qed.

  (* This one isn't very convenient... *)
  Lemma cssim_brD_r_inv : forall {X Y Z}
    (t : ctree E C X) (c : D Y) (k : Y -> ctree F D Z) L,
    cssim L t (BrD c k) ->
    forall l t', trans l t t' ->
    exists x t'' l', trans l' (k x) t'' /\ cssim L t' t'' /\ L l l'.
  Proof.
    cbn. intros. step in H. apply H in H0 as (? & ? & ? & ? & ?). subst. inv_trans.
    exists x1, x0, x. auto.
  Qed.

End WithParams.
