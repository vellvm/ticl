From Stdlib Require Import
  Basics
  Init.Wf.
From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Interp.State.Mod
  CTree.Events.Writer
  Logic.Core
  Logic.Kripke.

Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** * The [can_step] relation lemmas *)
(** Relation [can_step] ensures that an always [AG, AU, AN] formula is not trivially satisfied by a stuck ctree. 
    It ensures at least one step is possible from any state to take a universally quantified step. *)
Section CanStepCtrees.
  Context {E B: Type -> Type}.

  Global Add Parametric Morphism{X}: (can_step (M:=ctree) (E:=E) (B:=B) (X:=X))
         with signature (@equ E B X X eq ==> eq ==> iff)
           as proper_ctree_can_step.
  Proof.
    intros t w Ht w'. 
    unfold can_step.
    setoid_rewrite Ht.
    reflexivity.
  Qed.

  (** A delayed (hidden) branch can step iff one of its branches can. *)
  Lemma can_step_br{X Y}: forall (c: B Y) (k: Y -> ctree E B X) w,
      can_step (Br c k) w <-> exists y, can_step (k y) w.
  Proof.
    split; intros.
    - destruct H as (t' & w' & TR).
      apply ktrans_br in TR as (y & TR).
      exists y, t', w'; auto.
    - destruct H as (y & t' & w' & TR).
      exists t', w'.
      apply ktrans_br; exists y; auto.
  Qed.
  Hint Resolve can_step_br: ticl.

  (** A visible branch can always step, if world [w] is not done. *)
  Lemma can_step_brS{X Y}: forall (c: B Y) (k: Y -> ctree E B X) (y: Y) w,
      can_step (BrS c k) w <-> not_done w.
  Proof.
    split; intros.
    - destruct H as (t' & w' & TR).
      eapply ktrans_not_done; eauto.
    - exists (k y), w.
      apply ktrans_brS; exists y; auto.
  Qed.
  Hint Resolve can_step_brS: ticl.

  (** A visible step can always step, if world [w] is not done. *)
  Lemma can_step_step{X}: forall (t: ctree E B X) w,
      can_step (Step t) w <-> not_done w.
  Proof.
    split; intros.
    - destruct H as (t' & w' & TR).
      eapply ktrans_not_done; eauto.
    - exists t, w.
      apply ktrans_step; auto.
  Qed.
  Hint Resolve can_step_step: ticl.
  
  (** A guard can always step, if the guarded tree can step. *)
  Lemma can_step_guard{X}: forall (t: ctree E B X) w,
      can_step (Guard t) w <-> can_step t w.
  Proof.
    split; intros.
    - destruct H as (t' & w' & TR).
      rewrite ktrans_guard in TR.
      now (exists t', w').
    - destruct H as (t' & w' & TR).
      apply ktrans_guard in TR.
      now (exists t', w').
  Qed.
  Hint Resolve can_step_guard: ticl.
  
  (** A visible event can always step, if world [w] is not done. *)
  Lemma can_step_vis{X Y}: forall (e: E Y) (k: Y -> ctree E B X) (v: Y) w,
      can_step (Vis e k) w <-> not_done w.
  Proof.
    split; intros.
    - destruct H as (t' & w' & TR).
      eapply ktrans_not_done; eauto.
    - exists (k v), (Obs e v).
      apply ktrans_vis; exists v; auto.
  Qed.
  Hint Resolve can_step_vis: ticl.

  (** A return can always step, if world [w] is not done. *)
  Lemma can_step_ret{X}: forall w (x: X),
    not_done w ->
    can_step (Ret x: ctree E B X) w.
  Proof.
    intros; inv H.
    - exists Stuck, (Done x); apply ktrans_done; auto.
    - exists Stuck, (Finish e v x); apply ktrans_finish; auto.
  Qed.
  Hint Resolve can_step_ret: ticl.

  (** A stuck tree cannot step. *)
  Lemma can_step_stuck{X}: forall w,
      ~ (can_step (Stuck: ctree E B X) w).
  Proof.
    intros * (t' & w' & TRcontra).
    now apply ktrans_stuck in TRcontra.
  Qed.
  Hint Resolve can_step_stuck: ticl.

  (** A bind can always step, if the left-hand side can step or the right-hand side can step. *)
  Lemma can_step_bind{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w,
      can_step (x <- t ;; k x) w <->        
        (exists t' w', |t, w| ↦ |t', w'| /\ not_done w')
        \/ (exists y w', |t, w| ↦ |Stuck, w'|
                   /\ done_eq y w'
                   /\ can_step (k y) w).
  Proof with eauto with ticl.
    unfold can_step; split.
    - intros (k' & w' & TR).
      apply ktrans_bind_inv in TR
          as [(t' & TR' & Hd & ?) |
               (x & w_ & TRr & ? & TRk)].
      + left; exists t', w'...
      + right; exists x, w_...
    - intros * [(t' & w' & TR & Hd) |
                 (y & w' & TR & Hd & k_ & w_ & TR_)].
      + exists (x <- t' ;; k x), w'.
        apply ktrans_bind_l...
      + exists k_, w_.
        eapply ktrans_bind_r; eauto.
  Qed.
  Hint Resolve can_step_bind: ticl.

  (** A bind can always step, if the left-hand side can step. *)
  Lemma can_step_bind_l{X Y}: forall (t t': ctree E B Y) (k: Y -> ctree E B X) w w',
      |t, w| ↦ |t', w'| ->
      not_done w' ->
      can_step (x <- t ;; k x) w.
  Proof.
    intros.
    eapply can_step_bind.
    left.
    exists t', w'; auto.
  Qed.
  Hint Resolve can_step_bind_l: ticl.

  (** A bind can always step, if the right-hand side can step. *)
  Lemma can_step_bind_r{X Y}: forall (t: ctree E B Y) (k: Y -> ctree E B X) w R,      
      <[ t, w |= AF AX done R ]> ->
      (forall y w, R y w -> can_step (k y) w) ->
      can_step (x <- t ;; k x) w.
  Proof with eauto with ticl. 
    intros * Hau Hk.
    apply can_step_bind.
    induction Hau.
    - (* MatchA: AX done R at (t, w) *)
      destruct H as (? & (t' & w' & TR') & Hdone).
      specialize (Hdone _ _ TR') as Hd; inv Hd.
      + (* Done x: t returned from Pure *)
        apply ktrans_to_done_inv in TR' as Hinv; destruct Hinv as (Heq & ->).
        right; exists x, (Done x); split2...
        now rewrite <- Heq.
      + (* Finish e v x *)
        apply ktrans_to_finish_inv in TR' as Hinv; destruct Hinv as (Heq & ->).
        right; exists x, (Finish e v x); split2...
        now rewrite <- Heq.
    - (* StepA *)
      destruct H as (Hp & (t' & w' & TR') & Htr); clear H0.
      pose proof TR' as TR_; cbn in TR_; ddestruction TR_.
      + left; exists t', w; split...
      + left; exists t', (Obs e v); split...
      + (* the successor is done: the successor [Stuck] must be a [MatchA] of [AX done R],
           but a stuck tree cannot step; contradiction *)
        exfalso.
        pose proof (trans_val_inv H) as Heq; rewrite Heq in TR'.
        specialize (Htr _ _ TR') as Hs.
        inv Hs; destruct H0 as (_ & (? & ? & TRc) & _); now apply ktrans_stuck in TRc.
      + exfalso.
        pose proof (trans_val_inv H) as Heq; rewrite Heq in TR'.
        specialize (Htr _ _ TR') as Hs.
        inv Hs; destruct H0 as (_ & (? & ? & TRc) & _); now apply ktrans_stuck in TRc.
  Qed.
  Hint Resolve can_step_bind_r: ticl.

  (** An iteration can always step, if its continuation can step. *)
  Lemma can_step_iter{I X}: forall (k: I -> ctree E B (I+X))
                              (i: I) t' w w',
      |k i, w| ↦ |t', w'| ->
      not_done w' ->
      can_step (CTree.iter k i) w.
  Proof.
    intros k i t' w w' TR Hd.
    rewrite unfold_iter.
    apply can_step_bind_l with t' w'; auto.   
  Qed.
  
End CanStepCtrees.

(** ** The [can_step] relation lemmas for [ctree] interpretations *)
Section CanStepInterp.
  Context {E F B: Type -> Type} {S: Type} (h: E ~> stateT S (ctree F B)) (s: S).

  (** A stateful bind can always step, if the left-hand side can step. *)
  Lemma can_step_state_bind_l{X Y}: forall (k: X -> ctree E B Y) (s: S) (t: ctree E B X) t' w w',
      |interp_state h t s, w| ↦ |t', w'| ->
      not_done w' ->
      can_step (interp_state h (x <- t ;; k x) s) w.
  Proof.
    intros k i t t' w w' TR Hd. 
    rewrite interp_state_bind.
    apply can_step_bind_l with t' w'; auto.   
  Qed.

  (** A stateful bind can always step, if the right-hand side can step. *)
  Lemma can_step_state_bind_r{X Y}: forall (k: X -> ctree E B Y) (s s': S) (t: ctree E B X) x w w',
      <[ {interp_state h t s}, w |= AF AX done= {(s', x)} w' ]> ->
      can_step (interp_state h (k x) s') w' ->
      can_step (interp_state h (x <- t ;; k x) s) w.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply can_step_bind_r with (R:= fun p w => (s', x) = p /\ w' = w); auto.
    intros [] ? (Hp & <-); inv Hp; auto.
  Qed.
  
  (** A stateful iteration can always step, if its continuation can step. *)
  Lemma can_step_state_iter{I X}: forall (k: I -> ctree E B (I+X)) (i: I) t' w w',
      |interp_state h (k i) s, w| ↦ |t', w'| ->
      not_done w' ->
      can_step (interp_state h (CTree.iter k i) s) w.
  Proof.
    intros k i t' w w' TR Hd.
    rewrite interp_state_unfold_iter.
    apply can_step_bind_l with t' w'; auto.   
  Qed.
End CanStepInterp.

(** ** Instrumentation events [log s] can always step, if world [w] is not done. *)
Section CanStepLog.
  Context {S X: Type} {B: Type -> Type}.
  Lemma can_step_log: forall (s: S) (w: World (writerE S)),
      not_done w ->
      can_step (M:=ctree) (B:=B) (log s) w.
  Proof.
    intros.
    unfold log, CTree.trigger.
    apply can_step_vis; auto.
  Qed.
  Lemma can_step_log_bind: forall (s: S) (w: World (writerE S)) (t: ctreeW S B X),
      not_done w ->
      can_step (M:=ctree) (log s ;; t) w.
  Proof.
    intros.
    apply can_step_bind_l with (Ret tt) (Obs (Log s) tt); auto with ticl.
    unfold log, CTree.trigger.
    apply ktrans_vis; exists tt; auto.
  Qed.
End CanStepLog.

(** A bind cannot step when its prefix cannot: the residual continuation is
    never reached.  Arbitrary effect, arbitrary result types. *)
Lemma nostep_bind {E B} {X Y}:
  forall (t : ctree E B Y) (k : Y -> ctree E B X) w,
    ~ can_step t w -> ~ can_step (x <- t ;; k x) w.
Proof.
  intros t k w Hns Hs.
  apply can_step_bind in Hs as [(t' & w' & TR & _) | (y & w' & TR & _)].
  - apply Hns; exists t', w'; exact TR.
  - apply Hns; exists Stuck, w'; exact TR.
Qed.

(** * The [ret] atom on ctrees *)
(** [<[ t, w |= ret R ]>] says every transition of [t] returns the same value
    [x] with [R x w]. On ctrees this is exactly strong bisimilarity to [Ret x]:
    hidden branches that return different values ([brn 2 (fun i => Ret i)])
    satisfy [AX done R] but not [ret R]. *)
Section CTreeRet.
  Context {E B: Type -> Type} {X: Type}.

  (** Every [ktrans] out of a state satisfying [AX done= x w] is a [val x] step to [Stuck]. *)
  Local Lemma trans_done_eq_inv: forall (t t': ctree E B X) w (x: X) l,
      not_done w ->
      (forall t' w', |t, w| ↦ |t', w'| -> done_eq x w') ->
      trans l t t' ->
      l = val x /\ t' ≅ Stuck.
  Proof.
    intros * Hd Htr TR.
    destruct l as [| Y e v | Y y].
    - exfalso; specialize (Htr t' w (KtransTau _ _ _ Hd TR)); inv Hd; inv Htr.
    - exfalso; specialize (Htr t' (Obs e v) (KtransObs _ _ _ _ _ Hd TR)); inv Htr.
    - pose proof (trans_val_invT TR) as HXY; subst Y.
      pose proof (trans_val_inv TR) as Heq.
      inv Hd.
      + specialize (Htr t' (Done y) (KtransDone _ _ _ TR)); inv Htr.
        match goal with [HH: existT _ _ _ = existT _ _ _ |- _] => dependent destruction HH end; auto.
      + specialize (Htr t' (Finish e v y) (KtransFinish _ _ _ _ _ TR)); inv Htr.
        match goal with [HH: existT _ _ _ = existT _ _ _ |- _] => dependent destruction HH end; auto.
  Qed.

  Lemma ret_sbisim: forall (t: ctree E B X) w (R: X -> World E -> Prop),
      <[ t, w |= ret R ]> ->
      exists x, R x w /\ t ~ (Ret x : ctree E B X).
  Proof.
    intros * H.
    apply ret_unfold in H as (x & HR & H).
    rewrite unfold_entailsR in H; destruct H as (Hd & Hs & Htr).
    rewrite unfold_entailsL in Hd; destruct Hd as (_ & Hd).
    exists x; split; auto.
    assert (Htr': forall t' w', |t, w| ↦ |t', w'| -> done_eq (E:=E) x w').
    { intros t' w' TR; specialize (Htr t' w' TR); rewrite unfold_entailsR in Htr.
      unfold done_eq; inv Htr; destruct H as (-> & ->); now constructor. }
    clear Htr HR R.
    step; split; cbn.
    - (* t simulates Ret x *)
      intros l t' TR.
      destruct (trans_done_eq_inv _ _ _ _ _ Hd Htr' TR) as (-> & Heq).
      exists (val x), Stuck; split2; auto.
      + apply trans_ret.
      + now rewrite Heq.
    - (* Ret x simulates t *)
      intros l u' TR.
      apply trans_ret_inv in TR as (Hequ & ->).
      destruct Hs as (t' & w' & TRk).
      assert (TRv: trans (val x) t t').
      { cbn in TRk; ddestruction TRk.
        - exfalso; specialize (Htr' t' w (KtransTau _ _ _ H H0)); inv H; inv Htr'.
        - exfalso; specialize (Htr' t' (Obs e v) (KtransObs _ _ _ _ _ H H0)); inv Htr'.
        - specialize (Htr' t' (Done x0) (KtransDone _ _ _ H)); inv Htr'.
          match goal with [HH: existT _ _ _ = existT _ _ _ |- _] => dependent destruction HH end; auto.
        - specialize (Htr' t' (Finish e v x0) (KtransFinish _ _ _ _ _ H)); inv Htr'.
          match goal with [HH: existT _ _ _ = existT _ _ _ |- _] => dependent destruction HH end; auto. }
      exists (val x), t'; split2; auto.
      pose proof (trans_val_inv TRv) as Heq.
      now rewrite Heq, Hequ.
  Qed.

  (** [Ret x] itself satisfies [ret R] in every not-done world. *)
  Lemma ret_ret: forall (x: X) w (R: X -> World E -> Prop),
      not_done w ->
      R x w ->
      <[ {Ret x : ctree E B X}, w |= ret R ]>.
  Proof.
    intros * Hd HR.
    apply ret_unfold; exists x; split; auto.
    rewrite unfold_entailsR; split2.
    - rewrite unfold_entailsL; split; auto.
    - now apply can_step_ret.
    - intros t' w' TR; rewrite unfold_entailsR.
      inv Hd.
      + apply ktrans_done in TR as (-> & _); now constructor.
      + apply ktrans_finish in TR as (-> & _); now constructor.
  Qed.

  (** [ret] is invariant under strong bisimulation; in particular under [Guard]. *)
  Lemma ret_guard: forall (t: ctree E B X) w (R: X -> World E -> Prop),
      <[ {Guard t}, w |= ret R ]> <-> <[ t, w |= ret R ]>.
  Proof.
    intros; now rewrite sb_guard.
  Qed.

  (** A hidden branch whose every branch returns exactly [x] returns [x]. *)
  Lemma ret_br: forall {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) w (x: X) (R: X -> World E -> Prop),
      not_done w ->
      R x w ->
      (forall y, <[ {k y}, w |= ret= x w ]>) ->
      <[ {Br c k}, w |= ret R ]>.
  Proof.
    intros Y c k y w x R Hd HR Hk.
    apply ret_unfold; exists x; split; auto.
    rewrite unfold_entailsR; split2.
    - rewrite unfold_entailsL; split; auto.
    - apply can_step_br; exists y.
      specialize (Hk y); apply ret_unfold in Hk as (x' & _ & Hk).
      rewrite unfold_entailsR in Hk; now destruct Hk as (_ & ? & _).
    - intros t' w' TR.
      apply ktrans_br in TR as (y' & TR).
      specialize (Hk y'); apply ret_unfold in Hk as (x' & (-> & _) & Hk).
      rewrite unfold_entailsR in Hk; destruct Hk as (_ & _ & Hk).
      now apply Hk.
  Qed.
End CTreeRet.

#[global] Hint Resolve
  can_step_br can_step_brS can_step_step can_step_guard can_step_vis can_step_ret
  can_step_stuck can_step_bind_l can_step_bind_r can_step_iter
  can_step_state_bind_l can_step_state_bind_r can_step_state_iter
  can_step_log can_step_log_bind: ticl.
