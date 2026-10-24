From Stdlib Require Import Fin Vector Program.Equality Arith.PeanoNat Relations.Relation_Operators.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Interp.State.Mod
  CTree.Interp.Refine
  CTree.Events.Yield
  CTree.Events.State
  CTree.Events.Writer
  CTree.Interp.Yield.Mod
  Utils.Vectors.

Import CTreeNotations CoindNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** * Observations and finitely many leading guards (formerly TICL's own [Equ] module). *)

(** Equal observations give [equ]-equal trees. *)
Lemma observe_eq_equ {E B X} (t u : ctree E B X) :
  observe t = observe u -> t ≅ u.
Proof. apply observe_equ_eq. Qed.

Lemma observe_equ_go {E B X} (t : ctree E B X) ot :
  observe t = ot -> t ≅ go ot.
Proof. intro H; rewrite (ctree_eta t), H; reflexivity. Qed.

(** [guard_equ] is the equivalence closure of "raw-equivalent, or one leading
    guard away".  It forgets ONLY finitely many leading guards and raw
    equivalence: it never erases a branch node, and it never equates a
    divergent prefix with a productive one. *)
Definition guard_step {E B X} (t u : ctree E B X) : Prop :=
  t ≅ u \/ t ≅ Guard u.

Definition guard_equ {E B X} : ctree E B X -> ctree E B X -> Prop :=
  clos_refl_sym_trans _ guard_step.

Section GuardEqu.
  Context {E B : Type -> Type} {X : Type}.

  Lemma guard_equ_equ (t u : ctree E B X) : t ≅ u -> guard_equ t u.
  Proof. intro H; apply rst_step; now left. Qed.

  Lemma guard_equ_left (t u : ctree E B X) :
    guard_equ t u -> guard_equ (Guard t) u.
  Proof.
    intro H; eapply rst_trans; [| exact H].
    apply rst_step; right; reflexivity.
  Qed.

  Lemma guard_equ_right (t u : ctree E B X) :
    guard_equ t u -> guard_equ t (Guard u).
  Proof.
    intro H; eapply rst_trans; [exact H |].
    apply rst_sym, rst_step; right; reflexivity.
  Qed.

  Lemma guard_equ_sym (t u : ctree E B X) : guard_equ t u -> guard_equ u t.
  Proof. apply rst_sym. Qed.

  Lemma guard_equ_trans (t u v : ctree E B X) :
    guard_equ t u -> guard_equ u v -> guard_equ t v.
  Proof. apply rst_trans. Qed.

  #[global] Instance guard_equ_Equivalence : Equivalence (@guard_equ E B X).
  Proof.
    split.
    - intro t; apply rst_refl.
    - intros t u; apply rst_sym.
    - intros t u v; apply rst_trans.
  Qed.

  #[global] Instance guard_equ_proper :
    Proper (equ eq ==> equ eq ==> iff) (@guard_equ E B X).
  Proof.
    intros t t' Ht u u' Hu; split; intro H.
    - eapply guard_equ_trans; [apply guard_equ_equ; symmetry; exact Ht|].
      eapply guard_equ_trans; [exact H|apply guard_equ_equ; exact Hu].
    - eapply guard_equ_trans; [apply guard_equ_equ; exact Ht|].
      eapply guard_equ_trans; [exact H|apply guard_equ_equ; symmetry; exact Hu].
  Qed.
End GuardEqu.

(** * Bisimilar and branch-free pools *)

(** One transition of a [sbisim] pair, played from the left. *)
Lemma sbisim_trans_l {E B X} (t u t' : ctree E B X) l :
  t ~ u -> trans l t t' -> exists u', trans l u u' /\ t' ~ u'.
Proof.
  intros Hsb TR; step in Hsb; destruct Hsb as [Hf _]; cbn in Hf.
  edestruct Hf as (l' & u' & TR' & Hsb' & <-); eauto.
Qed.

(** Transitions preserve branch freedom. *)
Lemma branchfree_trans {E B X} (t u : ctree E B X) l :
  BranchFree t -> trans l t u -> BranchFree u.
Proof.
  intros Hb TR; rewrite <- trans__trans in TR.
  remember (observe t) as ot eqn:Hot; remember (observe u) as ou eqn:Hou.
  revert t u Hb Hot Hou; induction TR; intros t0 u0 Hb Hot Hou;
    apply branchfree_unfold in Hb; rewrite <- Hot in Hb.
  - inversion Hb.
  - inversion Hb; subst; eapply IHTR; eauto.
  - inversion Hb; subst; rewrite (observe_eq_equ u0 u (eq_sym Hou)), H; assumption.
  - ddestruction Hb; rewrite (observe_eq_equ u0 t (eq_sym Hou)), <- H; auto.
  - apply branchfree_unfold; rewrite <- Hou; constructor.
Qed.

Section PoolSBisim.
  Context {E B : Type -> Type}.

  Definition pool_sbisim {n : nat} (v1 v2 : pool E B n) : Prop :=
    forall i, (v1 $ i) ~ (v2 $ i).

  Lemma pool_sbisim_sym {n} (v1 v2 : pool E B n) :
    pool_sbisim v1 v2 -> pool_sbisim v2 v1.
  Proof. intros Hpool i; symmetry; apply Hpool. Qed.

  Lemma replace_pool_sbisim {n} (v1 v2 : pool E B n) (i : Fin.t n)
        (t1 t2 : thread E B) :
    pool_sbisim v1 v2 ->
    t1 ~ t2 ->
    pool_sbisim (v1 @ i := t1) (v2 @ i := t2).
  Proof.
    intros Hv Ht.
    exact (vector_replace_pointwise (fun a b : thread E B => a ~ b)
      v1 v2 i t1 t2 (fun j _ => Hv j) Ht).
  Qed.

  Lemma remove_pool_sbisim {n} (v1 v2 : pool E B (S n)) (i : Fin.t (S n)) :
    pool_sbisim v1 v2 ->
    pool_sbisim (v1 -- i) (v2 -- i).
  Proof.
    intros Hv.
    exact (vector_remove_pointwise (fun a b : thread E B => a ~ b) v1 v2 i
             (fun j _ => Hv j)).
  Qed.

  Lemma cons_pool_sbisim {n} (t1 t2 : thread E B) (v1 v2 : pool E B n) :
    t1 ~ t2 ->
    pool_sbisim v1 v2 ->
    pool_sbisim ((t1 :: v1)%vector) ((t2 :: v2)%vector).
  Proof.
    exact (vector_cons_pointwise (fun a b : thread E B => a ~ b) t1 t2 v1 v2).
  Qed.

  (** ** [equ]-level pool congruences, used by [schedule_pool_proper]. *)
  Definition pool_equ {n : nat} (v1 v2 : pool E B n) : Prop :=
    forall i, (v1 $ i) ≅ (v2 $ i).

  Lemma replace_pool_equ {n} (v1 v2 : pool E B n) (i : Fin.t n)
        (t1 t2 : thread E B) :
    pool_equ v1 v2 ->
    t1 ≅ t2 ->
    pool_equ (v1 @ i := t1) (v2 @ i := t2).
  Proof.
    intros Hv Ht.
    exact (vector_replace_pointwise (fun a b : thread E B => a ≅ b)
      v1 v2 i t1 t2 (fun j _ => Hv j) Ht).
  Qed.

  Lemma remove_pool_equ {n} (v1 v2 : pool E B (S n)) (i : Fin.t (S n)) :
    pool_equ v1 v2 ->
    pool_equ (v1 -- i) (v2 -- i).
  Proof.
    intros Hv.
    exact (vector_remove_pointwise (fun a b : thread E B => a ≅ b) v1 v2 i
             (fun j _ => Hv j)).
  Qed.

  Lemma cons_pool_equ {n} (t1 t2 : thread E B) (v1 v2 : pool E B n) :
    t1 ≅ t2 ->
    pool_equ v1 v2 ->
    pool_equ ((t1 :: v1)%vector) ((t2 :: v2)%vector).
  Proof.
    exact (vector_cons_pointwise (fun a b : thread E B => a ≅ b) t1 t2 v1 v2).
  Qed.

  (** ** Branch-free pools: no hidden branch in any thread.

      Hidden branching above a [Fork] is not respected by the scheduler
      (both answers of one fork node are spawned together), so the scheduler
      is a [sbisim]-congruence only on branch-free pools. *)
  Definition pool_branchfree {n : nat} (v : pool E B n) : Prop :=
    forall i, BranchFree (v $ i).

  Lemma pool_branchfree_replace {n} (v : pool E B n) (i : Fin.t n) (t : thread E B) :
    pool_branchfree v -> BranchFree t -> pool_branchfree (v @ i := t).
  Proof.
    intros Hv Ht.
    exact (vector_replace_pointwise (fun a _ : thread E B => BranchFree a)
      v v i t t (fun j _ => Hv j) Ht).
  Qed.

  Lemma pool_branchfree_remove {n} (v : pool E B (S n)) (i : Fin.t (S n)) :
    pool_branchfree v -> pool_branchfree (v -- i).
  Proof.
    intros Hv.
    exact (vector_remove_pointwise (fun a _ : thread E B => BranchFree a) v v i
             (fun j _ => Hv j)).
  Qed.

  Lemma pool_branchfree_cons {n} (t : thread E B) (v : pool E B n) :
    BranchFree t -> pool_branchfree v -> pool_branchfree ((t :: v)%vector).
  Proof.
    exact (vector_cons_pointwise (fun a _ : thread E B => BranchFree a) t t v v).
  Qed.
End PoolSBisim.

Section SchedulerTransitions.
  Context {E B : Type -> Type} `{Bn -< B}.

  Abbreviation Yield' := (inl1 Yield : (yieldE +' (spawnE +' E)) unit).
  Abbreviation Spawn' := (inr1 (inl1 Spawn) : (yieldE +' (spawnE +' E)) unit).
  Abbreviation Yield_ := (inl1 Yield : (yieldE +' (forkE +' E)) unit).
  Abbreviation Fork_ := (inr1 (inl1 Fork) : (yieldE +' (forkE +' E)) bool).

  (** ** Phase 1: [equ]-unfoldings of the scheduler. *)

  Lemma trans_schedule_empty_ret (v : pool E B 0) :
    schedule 0 v None ≅ Ret tt.
  Proof. apply (observe_equ_go _ _ (schedule_empty_none v)). Qed.

  Lemma schedule_no_focus_equ n (v : pool E B (S n)) :
    schedule (S n) v None
      ≅ Vis Yield' (fun _ => brS (branchn (S n)) (fun i => schedule (S n) v (Some i))).
  Proof. apply (observe_equ_go _ _ (schedule_no_focus_nonempty n v)). Qed.

  Lemma trans_schedule_focused_ret n (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = RetF tt ->
    schedule (S n) v (Some i) ≅ Guard (schedule n ((v -- i)) None).
  Proof. intro Hobs; apply (observe_equ_go _ _ (schedule_focused_ret n v i Hobs)). Qed.

  Lemma trans_schedule_focused_stuck n (v : pool E B (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = StuckF ->
    schedule (S n) v (Some i) ≅ Stuck.
  Proof. intro Hobs; apply (observe_equ_go _ _ (schedule_focused_stuck n v i Hobs)). Qed.

  Lemma trans_schedule_focused_guard n (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    schedule (S n) v (Some i)
      ≅ Guard (schedule (S n) ((v @ i := t)) (Some i)).
  Proof. intro Hobs; apply (observe_equ_go _ _ (schedule_focused_guard n v i t Hobs)). Qed.

  Lemma schedule_focused_step_equ n (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = StepF t ->
    schedule (S n) v (Some i)
      ≅ Step (schedule (S n) ((v @ i := t)) (Some i)).
  Proof. intro Hobs; apply (observe_equ_go _ _ (schedule_focused_step n v i t Hobs)). Qed.

  Lemma schedule_focused_br_equ n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k :
    observe (v $ i) = BrF c k ->
    schedule (S n) v (Some i)
      ≅ Br c (fun j => schedule (S n) ((v @ i := k j)) (Some i)).
  Proof. intro Hobs; apply (observe_equ_go _ _ (schedule_focused_br n v i c k Hobs)). Qed.

  (** ** Phase 2: scheduler transitions from a head node. *)

  Lemma trans_schedule_no_focus_nonempty n (v : pool E B (S n)) :
    trans (obs Yield' tt)
      (schedule (S n) v None)
      (brS (branchn (S n)) (fun i => schedule (S n) v (Some i))).
  Proof.
    rewrite schedule_no_focus_equ.
    apply (trans_vis Yield' tt).
  Qed.

  Lemma trans_schedule_focused_yield n (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF Yield_ k ->
    trans (obs Yield' tt)
      (schedule (S n) v (Some i))
      (brS (branchn (S n)) (fun j => schedule (S n) ((v @ i := (k tt))) (Some j))).
  Proof.
    intro Hobs.
    rewrite (observe_equ_go _ _ (schedule_focused_yield n v i k Hobs)).
    apply trans_guard, trans_schedule_no_focus_nonempty.
  Qed.

  Lemma trans_schedule_focused_fork n (v : pool E B (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF Fork_ k ->
    trans (obs Spawn' tt)
      (schedule (S n) v (Some i))
      (schedule (S (S n))
         (((k true) :: ((v @ i := (k false))))%vector)
         (Some (Fin.FS i))).
  Proof.
    intro Hobs.
    rewrite (observe_equ_go _ _ (schedule_focused_fork n v i k Hobs)).
    apply (trans_vis Spawn' tt).
  Qed.

  Lemma trans_schedule_focused_user_event
        n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k x :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    trans (obs (inr1 (inr1 e) : (yieldE +' (spawnE +' E)) Y) x)
      (schedule (S n) v (Some i))
      (schedule (S n) ((v @ i := (k x))) (Some i)).
  Proof.
    intro Hobs.
    rewrite (observe_equ_go _ _ (schedule_focused_user_event n v i e k Hobs)).
    apply (trans_vis (inr1 (inr1 e) : (yieldE +' (spawnE +' E)) Y) x).
  Qed.

  (** A visible step of the focused thread is a [τ] step of the scheduler. *)
  Lemma trans_schedule_focused_step n (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = StepF t ->
    trans τ (schedule (S n) v (Some i)) (schedule (S n) ((v @ i := t)) (Some i)).
  Proof.
    intro Hobs.
    rewrite (schedule_focused_step_equ n v i t Hobs).
    apply trans_step.
  Qed.

  (** A hidden branch of the focused thread is crawled by the scheduler. *)
  Lemma trans_schedule_focused_br
        n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k (j : Y) l u :
    observe (v $ i) = BrF c k ->
    trans l (schedule (S n) ((v @ i := (k j))) (Some i)) u ->
    trans l (schedule (S n) v (Some i)) u.
  Proof.
    intros Hobs TR.
    rewrite (schedule_focused_br_equ n v i c k Hobs).
    eapply trans_br with (x := j); [exact TR | reflexivity].
  Qed.

  (** ** Phase 3: scheduler transition inversions. *)

  Lemma trans_schedule_no_focus_inv n (v : pool E B (S n)) l t' :
    trans l (schedule (S n) v None) t' ->
    l = obs Yield' tt /\
    t' ≅ brS (branchn (S n)) (fun i => schedule (S n) v (Some i)).
  Proof.
    intro TR.
    rewrite schedule_no_focus_equ in TR.
    apply trans_vis_inv in TR as (x & Heq & Hl).
    destruct x.
    split; auto.
  Qed.

  (** ** [schedule] respects [equ]-equality of pools, in every focus. *)
  Lemma schedule_pool_proper n (v w : pool E B n) focus :
    pool_equ v w ->
    schedule n v focus ≅ schedule n w focus.
  Proof.
    revert n v w focus.
    __coinduction_equ R CH.
    intros n v w focus Hvw.
    destruct focus as [i |].
    - destruct n as [| n']; [ inversion i |].
      pose proof (Hvw i) as Hi.
      assert (Hgo : go (observe (v $ i)) ≅ go (observe (w $ i))).
      { rewrite <- !ctree_eta. exact Hi. }
      rewrite (ctree_eta (schedule (S n') v (Some i))).
      rewrite (ctree_eta (schedule (S n') w (Some i))).
      destruct (observe (v $ i)) as [r | | t | g | Y e k | Y c k] eqn:Hv;
      destruct (observe (w $ i)) as [r2 | | t2 | g2 | Y2 e2 k2 | Y2 c2 k2] eqn:Hw;
        try (step in Hgo; cbn in Hgo; inversion Hgo; fail).
      + destruct r, r2.
        rewrite (schedule_focused_ret n' v i Hv).
        rewrite (schedule_focused_ret n' w i Hw).
        cbn. constructor. apply CH. apply remove_pool_equ. exact Hvw.
      + rewrite (schedule_focused_stuck n' v i Hv).
        rewrite (schedule_focused_stuck n' w i Hw).
        cbn. constructor.
      + apply equ_step_inv in Hgo.
        rewrite (schedule_focused_step n' v i t Hv).
        rewrite (schedule_focused_step n' w i t2 Hw).
        cbn. constructor. apply CH.
        apply replace_pool_equ. exact Hvw. exact Hgo.
      + apply equ_guard_inv in Hgo.
        rewrite (schedule_focused_guard n' v i g Hv).
        rewrite (schedule_focused_guard n' w i g2 Hw).
        cbn. constructor. apply CH.
        apply replace_pool_equ. exact Hvw. exact Hgo.
      + pose proof (equ_vis_invT _ _ _ _ Hgo) as HY; subst Y2.
        pose proof (equ_vis_invE _ _ _ _ Hgo) as [He Hke]; subst e2.
        destruct e as [yld | [frk | usr]].
        * destruct yld.
          rewrite (schedule_focused_yield n' v i k Hv).
          rewrite (schedule_focused_yield n' w i k2 Hw).
          cbn. constructor. apply CH.
          apply replace_pool_equ. exact Hvw. apply (Hke tt).
        * destruct frk.
          rewrite (schedule_focused_fork n' v i k Hv).
          rewrite (schedule_focused_fork n' w i k2 Hw).
          cbn. constructor. intros _. apply CH.
          apply cons_pool_equ.
          -- apply (Hke true).
          -- apply replace_pool_equ. exact Hvw. apply (Hke false).
        * rewrite (schedule_focused_user_event n' v i usr k Hv).
          rewrite (schedule_focused_user_event n' w i usr k2 Hw).
          cbn. constructor. intro x. apply CH.
          apply replace_pool_equ. exact Hvw. apply (Hke x).
      + pose proof (equ_br_invT _ _ _ _ Hgo) as HY; subst Y2.
        pose proof (equ_br_invE _ _ _ _ Hgo) as [Hc Hke]; subst c2.
        rewrite (schedule_focused_br n' v i c k Hv).
        rewrite (schedule_focused_br n' w i c k2 Hw).
        cbn. constructor. intro j. apply CH.
        apply replace_pool_equ. exact Hvw. apply Hke.
    - destruct n as [| n'].
      + rewrite (ctree_eta (schedule 0 v None)).
        rewrite (ctree_eta (schedule 0 w None)).
        rewrite schedule_empty_none, schedule_empty_none.
        cbn. reflexivity.
      + rewrite (ctree_eta (schedule (S n') v None)).
        rewrite (ctree_eta (schedule (S n') w None)).
        rewrite schedule_no_focus_nonempty, schedule_no_focus_nonempty.
        cbn. constructor. intros _. cbn. step.
        constructor. intro i. cbn. step. constructor. apply CH. exact Hvw.
  Qed.

  (** ** Phase 4: thread-step to scheduler-step lifts. *)

  Lemma pool_equ_refl {n} (v : pool E B n) : pool_equ v v.
  Proof. intro j; reflexivity. Qed.

  Lemma replace_pool_idem_equ {n} (v : pool E B (S n)) (i : Fin.t (S n))
        (a b : thread E B) :
    pool_equ (v @ i := b) ((v @ i := a) @ i := b).
  Proof. rewrite Vector.replace_replace_eq. apply pool_equ_refl. Qed.

  Lemma br_schedule_pool_equ {n} (v w : pool E B (S n)) :
    pool_equ v w ->
    brS (branchn (S n)) (fun j => schedule (S n) v (Some j))
      ≅ brS (branchn (S n)) (fun j => schedule (S n) w (Some j)).
  Proof.
    intro Hvw. step. constructor. intro j. step. constructor.
    apply schedule_pool_proper. exact Hvw.
  Qed.

  Lemma schedule_some_pool_equ {m} (v w : pool E B (S m)) (i : Fin.t (S m)) :
    pool_equ v w ->
    schedule (S m) v (Some i) ≅ schedule (S m) w (Some i).
  Proof. intro Hvw. apply schedule_pool_proper. exact Hvw. Qed.

  Lemma schedule_lift_yield n (v : pool E B (S n)) (i : Fin.t (S n))
        (u : thread E B) :
    trans (obs Yield_ tt) (v $ i) u ->
    trans (obs Yield' tt)
      (schedule (S n) v (Some i))
      (brS (branchn (S n)) (fun j => schedule (S n) ((v @ i := u)) (Some j))).
  Proof.
    intro TR.
    rewrite <- trans__trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (obs Yield_ tt) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR as [Y c x k l t TR IH | t t' l TR IH | t w Equ | Y e k x t Equ | r];
      intros v i u Hot Hou Hlbl.
    - (* Transbr *)
      apply (trans_schedule_focused_br n v i c k x); [now symmetry |].
      specialize (IH (v @ i := k x) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite Vector.replace_replace_eq in IH; exact IH.
    - (* Transguard *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      apply trans_guard.
      specialize (IH (v @ i := t) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite Vector.replace_replace_eq in IH; exact IH.
    - discriminate Hlbl.
    - (* Transobs *)
      dependent destruction Hlbl.
      assert (Hu : u ≅ k tt).
      { transitivity t.
        - rewrite (ctree_eta u), (ctree_eta t), <- Hou; reflexivity.
        - symmetry; assumption. }
      rewrite (br_schedule_pool_equ ((v @ i := u))
                 ((v @ i := (k tt)))
                 (replace_pool_equ v v i u (k tt) (pool_equ_refl v) Hu)).
      apply (trans_schedule_focused_yield n v i k (eq_sym Hot)).
    - discriminate Hlbl.
  Qed.

  Lemma schedule_lift_user n (v : pool E B (S n)) (i : Fin.t (S n))
        {Y} (e : E Y) (x : Y) (u : thread E B) :
    trans (obs (inr1 (inr1 e) : (yieldE +' (forkE +' E)) Y) x) (v $ i) u ->
    trans (obs (inr1 (inr1 e) : (yieldE +' (spawnE +' E)) Y) x)
      (schedule (S n) v (Some i))
      (schedule (S n) ((v @ i := u)) (Some i)).
  Proof.
    intro TR.
    rewrite <- trans__trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (obs (inr1 (inr1 e) : (yieldE +' (forkE +' E)) Y) x) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR as [Y0 c x0 k l t TR IH | t t' l TR IH | t w Equ | Y0 e0 k x0 t Equ | r];
      intros v i u Hot Hou Hlbl.
    - (* Transbr *)
      apply (trans_schedule_focused_br n v i c k x0); [now symmetry |].
      specialize (IH (v @ i := k x0) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite Vector.replace_replace_eq in IH; exact IH.
    - (* Transguard *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      apply trans_guard.
      specialize (IH (v @ i := t) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite Vector.replace_replace_eq in IH; exact IH.
    - discriminate Hlbl.
    - (* Transobs *)
      dependent destruction Hlbl.
      assert (Hu : u ≅ k x).
      { transitivity t.
        - rewrite (ctree_eta u), (ctree_eta t), <- Hou; reflexivity.
        - symmetry; assumption. }
      rewrite (schedule_some_pool_equ ((v @ i := u))
                 ((v @ i := (k x))) i
                 (replace_pool_equ v v i u (k x) (pool_equ_refl v) Hu)).
      apply (trans_schedule_focused_user_event n v i e k x (eq_sym Hot)).
    - discriminate Hlbl.
  Qed.

  Lemma schedule_lift_tau n (v : pool E B (S n)) (i : Fin.t (S n))
        (u : thread E B) :
    trans τ (v $ i) u ->
    trans τ
      (schedule (S n) v (Some i))
      (schedule (S n) ((v @ i := u)) (Some i)).
  Proof.
    intro TR.
    rewrite <- trans__trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (τ : @label (yieldE +' (forkE +' E))) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR as [Y c x k l t TR IH | t t' l TR IH | t w Equ | Y e k x t Equ | r];
      intros v i u Hot Hou Hlbl.
    - (* Transbr *)
      apply (trans_schedule_focused_br n v i c k x); [now symmetry |].
      specialize (IH (v @ i := k x) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite Vector.replace_replace_eq in IH; exact IH.
    - (* Transguard *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      apply trans_guard.
      specialize (IH (v @ i := t) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite Vector.replace_replace_eq in IH; exact IH.
    - (* Transtau *)
      assert (Hu : u ≅ t).
      { transitivity w.
        - rewrite (ctree_eta u), (ctree_eta w), <- Hou; reflexivity.
        - assumption. }
      rewrite (schedule_some_pool_equ ((v @ i := u)) ((v @ i := t)) i
                 (replace_pool_equ v v i u t (pool_equ_refl v) Hu)).
      apply (trans_schedule_focused_step n v i t (eq_sym Hot)).
    - discriminate Hlbl.
    - discriminate Hlbl.
  Qed.

  Lemma schedule_lift_fork n (v : pool E B (S n)) (i : Fin.t (S n))
        (b : bool) (u : thread E B) :
    trans (obs Fork_ b) (v $ i) u ->
    exists k2,
      (forall c : bool, trans (obs Fork_ c) (v $ i) (k2 c)) /\
      trans (obs Spawn' tt)
        (schedule (S n) v (Some i))
        (schedule (S (S n))
           (((k2 true) :: ((v @ i := (k2 false))))%vector)
           (Some (Fin.FS i))).
  Proof.
    intro TR.
    rewrite <- trans__trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (obs Fork_ b) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR as [Y c x k l t TR IH | t t' l TR IH | t w Equ | Y e k x t Equ | r];
      intros v i u Hot Hou Hlbl.
    - (* Transbr *)
      destruct (IH (v @ i := k x) i u
                  ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl)
        as (k2 & Hcont & Hstep).
      rewrite Vector.replace_replace_eq in Hstep.
      exists k2. split.
      + intro c0. specialize (Hcont c0).
        rewrite Vector.nth_replace_eq in Hcont.
        rewrite (ctree_eta (v $ i)), <- Hot.
        eapply trans_br with (x := x); [exact Hcont | reflexivity].
      + apply (trans_schedule_focused_br n v i c k x); [now symmetry | exact Hstep].
    - (* Transguard *)
      destruct (IH (v @ i := t) i u
                  ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl)
        as (k2 & Hcont & Hstep).
      rewrite Vector.replace_replace_eq in Hstep.
      exists k2. split.
      + intro c. specialize (Hcont c).
        rewrite Vector.nth_replace_eq in Hcont.
        rewrite (ctree_eta (v $ i)), <- Hot.
        now apply trans_guard.
      + rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
        apply trans_guard. exact Hstep.
    - discriminate Hlbl.
    - (* Transobs *)
      dependent destruction Hlbl.
      exists k. split.
      + intro c.
        rewrite (ctree_eta (v $ i)), <- Hot.
        apply trans_vis.
      + apply (trans_schedule_focused_fork n v i k (eq_sym Hot)).
    - discriminate Hlbl.
  Qed.

  Lemma remove_pool_agree {n} :
    forall (v w : pool E B (S n)) (i : Fin.t (S n)),
    (forall j, i <> j -> (v $ j) ≅ (w $ j)) ->
    pool_equ (v -- i) (w -- i).
  Proof.
    intros v w i Hag.
    exact (vector_remove_pointwise (fun a b : thread E B => a ≅ b) v w i Hag).
  Qed.

  Lemma remove_replace_pool_equ {n} (v : pool E B (S n)) (i : Fin.t (S n))
        (a : thread E B) :
    pool_equ ((v @ i := a) -- i) (v -- i).
  Proof.
    apply remove_pool_agree. intros j Hij.
    rewrite Vector.nth_replace_neq by congruence. reflexivity.
  Qed.

  (** When the focused thread returns, the scheduler crawls to the pool
      without it: every transition of the latter is one of the former. *)
  Lemma schedule_lift_ret n (v : pool E B (S n)) (i : Fin.t (S n))
        (u : thread E B) :
    trans (val tt : @label (yieldE +' (forkE +' E))) (v $ i) u ->
    forall l t',
      trans l (schedule n ((v -- i)) None) t' ->
      trans l (schedule (S n) v (Some i)) t'.
  Proof.
    intro TR.
    rewrite <- trans__trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (val tt : @label (yieldE +' (forkE +' E))) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR as [Y c x k l t TR IH | t t' l TR IH | t w Equ | Y e k x t Equ | r];
      intros v i u Hot Hou Hlbl l' t'' TR'.
    - (* Transbr *)
      apply (trans_schedule_focused_br n v i c k x); [now symmetry |].
      apply (IH (v @ i := k x) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite (schedule_pool_proper n _ _ None (remove_replace_pool_equ v i (k x))).
      exact TR'.
    - (* Transguard *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      apply trans_guard.
      apply (IH (v @ i := t) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite (schedule_pool_proper n _ _ None (remove_replace_pool_equ v i t)).
      exact TR'.
    - discriminate Hlbl.
    - discriminate Hlbl.
    - (* Transval *)
      dependent destruction Hlbl.
      rewrite (trans_schedule_focused_ret n v i (eq_sym Hot)).
      apply trans_guard. exact TR'.
  Qed.

  (** ** Phase 5: [schedule] preserves pool strong bisimilarity (branch-free pools). *)

  Abbreviation completed' := (completed E B).
  Abbreviation sbC := (@sb (yieldE +' (spawnE +' E)) (yieldE +' (spawnE +' E)) B B unit unit eq).

  Local Ltac branchfree_absurd Hbf Hvi :=
    exfalso; let Hb := fresh "Hb" in
    pose proof Hbf as Hb; apply branchfree_unfold in Hb; rewrite Hvi in Hb; inversion Hb.

  (** Dispatch the head of the focused thread against a scheduler head
      ([Hos : <head> = observe (schedule (S n') v1 (Some i))]); impossible
      pairings are discharged, the remaining goals are in thread-head order. *)
  Local Ltac focused_heads v1 i Hos Hbf Hvi :=
    destruct (observe (v1 $ i)) as [[] | | t0 | g | Y0 e0 k0 | Y0 c0 k0] eqn:Hvi;
    [ rewrite (schedule_focused_ret _ v1 i Hvi) in Hos
    | rewrite (schedule_focused_stuck _ v1 i Hvi) in Hos
    | rewrite (schedule_focused_step _ v1 i _ Hvi) in Hos
    | rewrite (schedule_focused_guard _ v1 i _ Hvi) in Hos
    | destruct e0 as [y | [f | usr]];
      [ dependent destruction y; rewrite (schedule_focused_yield _ v1 i _ Hvi) in Hos
      | dependent destruction f; rewrite (schedule_focused_fork _ v1 i _ Hvi) in Hos
      | rewrite (schedule_focused_user_event _ v1 i usr _ Hvi) in Hos ]
    | branchfree_absurd (Hbf i) Hvi ];
    try discriminate Hos.

  Lemma schedule_match {R : Chain sbC}
    (Hch : forall m (w1 w2 : pool E B m) f,
       pool_branchfree w1 -> pool_branchfree w2 ->
       pool_sbisim w1 w2 -> `R (schedule m w1 f) (schedule m w2 f)) :
    forall l os ot', trans_ l os ot' ->
    forall n (v1 v2 : pool E B n) focus (t' : completed'),
      os = observe (schedule n v1 focus) ->
      ot' = observe t' ->
      pool_branchfree v1 -> pool_branchfree v2 ->
      pool_sbisim v1 v2 ->
      exists u', trans l (schedule n v2 focus) u' /\ `R t' u'.
  Proof.
    intros l os ot' TR.
    induction TR as [Y c x k l t TR IHTR | t t2 l TR IHTR | t w Equ | Y e k x t Equ | r];
      intros nn v1 v2 focus t' Hos Hot' Hbf1 Hbf2 Hpool.
    - (* Transbr: the scheduler only branches when the thread does *)
      destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        focused_heads v1 i Hos Hbf1 Hvi.
      + destruct nn as [| n'].
        * rewrite (schedule_empty_none v1) in Hos. discriminate Hos.
        * rewrite (schedule_no_focus_nonempty n' v1) in Hos. discriminate Hos.
    - (* Transguard *)
      destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        focused_heads v1 i Hos Hbf1 Hvi.
        * (* Ret: recurse on the smaller pool *)
          injection Hos as ->.
          destruct (IHTR n' ((v1 -- i)) ((v2 -- i)) None t'
                      eq_refl Hot'
                      (pool_branchfree_remove v1 i Hbf1)
                      (pool_branchfree_remove v2 i Hbf2)
                      (remove_pool_sbisim v1 v2 i Hpool))
            as (u' & Htru & Hresu).
          assert (Hvr : (v1 $ i) ≅ Ret tt).
          { rewrite (ctree_eta (v1 $ i)), Hvi. reflexivity. }
          assert (Htrv : trans (val tt : @label (yieldE +' (forkE +' E)))
                           (v1 $ i) Stuck).
          { rewrite Hvr. apply trans_ret. }
          destruct (sbisim_trans_l _ _ _ _ (Hpool i) Htrv) as (uv & Htr2v & _).
          exists u'. split; [| exact Hresu].
          exact (schedule_lift_ret n' v2 i uv Htr2v l u' Htru).
        * (* Guard: recurse on the same pool, focus unchanged *)
          injection Hos as ->.
          assert (Hbg : BranchFree g).
          { pose proof (Hbf1 i) as Hb; apply branchfree_unfold in Hb;
              rewrite Hvi in Hb; now inversion Hb. }
          apply (IHTR (S n') ((v1 @ i := g)) v2 (Some i) t' eq_refl Hot'
                   (pool_branchfree_replace v1 i g Hbf1 Hbg) Hbf2).
          intro j. destruct (Fin.eq_dec i j) as [Hij | Hij].
          -- subst j.
             rewrite Vector.nth_replace_eq.
             assert (Hvg : (v1 $ i) ≅ Guard g).
             { rewrite (ctree_eta (v1 $ i)), Hvi. reflexivity. }
             transitivity (v1 $ i); [| apply Hpool].
             rewrite Hvg. symmetry. apply sb_guard.
          -- rewrite Vector.nth_replace_neq by congruence. apply Hpool.
        * (* Yield: invert the focused-yield residual directly *)
          injection Hos as ->.
          assert (TR0 : trans l (schedule (S n') ((v1 @ i := (k0 tt))) None) t').
          { rewrite <- trans__trans, <- Hot'. exact TR. }
          apply trans_schedule_no_focus_inv in TR0 as (Hl & Hbr).
          subst l.
          assert (Hvis : (v1 $ i) ≅ Vis Yield_ k0).
          { rewrite (ctree_eta (v1 $ i)), Hvi. reflexivity. }
          assert (Htry : trans (obs Yield_ tt) (v1 $ i) (k0 tt)).
          { rewrite Hvis. apply trans_vis. }
          destruct (sbisim_trans_l _ _ _ _ (Hpool i) Htry) as (uy & Htr2y & Hsby).
          assert (Hbk : BranchFree (k0 tt)).
          { pose proof (Hbf1 i) as Hb; apply branchfree_unfold in Hb;
              rewrite Hvi in Hb; ddestruction Hb; auto. }
          exists (brS (branchn (S n')) (fun j =>
            schedule (S n') ((v2 @ i := uy)) (Some j))). split.
          ++ apply (schedule_lift_yield n' v2 i uy Htr2y).
          ++ rewrite Hbr.
             apply (b_chain R).
             apply step_sb_brS_id; [reflexivity | intro j].
             apply Hch.
             ** apply pool_branchfree_replace; assumption.
             ** apply pool_branchfree_replace; [assumption |].
                exact (branchfree_trans _ _ _ (Hbf2 i) Htr2y).
             ** apply replace_pool_sbisim; assumption.
      + destruct nn as [| n'].
        * rewrite (schedule_empty_none v1) in Hos. discriminate Hos.
        * rewrite (schedule_no_focus_nonempty n' v1) in Hos. discriminate Hos.
    - (* Transtau: a visible step of the focused thread *)
      destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        focused_heads v1 i Hos Hbf1 Hvi.
        injection Hos as ->.
        assert (Htr1 : trans τ (v1 $ i) t0).
        { rewrite (ctree_eta (v1 $ i)), Hvi. apply trans_step. }
        destruct (sbisim_trans_l _ _ _ _ (Hpool i) Htr1) as (u' & Htr2 & Hsb).
        assert (Hbt : BranchFree t0).
        { pose proof (Hbf1 i) as Hb; apply branchfree_unfold in Hb;
            rewrite Hvi in Hb; now inversion Hb. }
        exists (schedule (S n') ((v2 @ i := u')) (Some i)). split.
        * apply schedule_lift_tau. exact Htr2.
        * assert (Ht' : t' ≅ schedule (S n') ((v1 @ i := t0)) (Some i)).
          { rewrite (ctree_eta t'), <- Hot', <- (ctree_eta w). assumption. }
          rewrite Ht'. apply Hch.
          -- apply pool_branchfree_replace; assumption.
          -- apply pool_branchfree_replace; [assumption |].
             exact (branchfree_trans _ _ _ (Hbf2 i) Htr2).
          -- apply replace_pool_sbisim; assumption.
      + destruct nn as [| n'].
        * rewrite (schedule_empty_none v1) in Hos. discriminate Hos.
        * rewrite (schedule_no_focus_nonempty n' v1) in Hos. discriminate Hos.
    - (* Transobs *)
      destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        focused_heads v1 i Hos Hbf1 Hvi.
        * (* Fork *)
          dependent destruction Hos.
          destruct x.
          assert (Hvis : (v1 $ i) ≅ Vis Fork_ k0).
          { rewrite (ctree_eta (v1 $ i)), Hvi. reflexivity. }
          assert (Htrf : trans (obs Fork_ false) (v1 $ i) (k0 false)).
          { rewrite Hvis. apply trans_vis. }
          destruct (sbisim_trans_l _ _ _ _ (Hpool i) Htrf) as (uf & Htr2 & Hsbf).
          destruct (schedule_lift_fork n' v2 i false uf Htr2)
            as (kf & Hforall & Hstep).
          assert (Hbk : forall c, BranchFree (k0 c)).
          { pose proof (Hbf1 i) as Hb; apply branchfree_unfold in Hb;
              rewrite Hvi in Hb; ddestruction Hb; auto. }
          exists (schedule (S (S n'))
                    (((kf true) :: ((v2 @ i := (kf false))))%vector)
                    (Some (Fin.FS i))).
          split.
          ++ exact Hstep.
          ++ assert (Ht' : t' ≅ schedule (S (S n'))
               (((k0 true) :: ((v1 @ i := (k0 false))))%vector)
               (Some (Fin.FS i))).
             { rewrite (ctree_eta t'), <- Hot', <- (ctree_eta t).
               symmetry; assumption. }
             rewrite Ht'.
             assert (Hii : (v2 $ i) ~ (v1 $ i)) by (symmetry; apply Hpool).
             assert (Hkf : forall c, k0 c ~ kf c).
             { intro c.
               destruct (sbisim_trans_l _ _ _ _ Hii (Hforall c)) as (wc & Htrc & Hsbc).
               rewrite Hvis in Htrc.
               apply trans_vis_inv in Htrc as (y & Hwy & Hly).
               apply obs_eq_inv in Hly as [_ <-].
               rewrite Hwy in Hsbc. symmetry; exact Hsbc. }
             apply Hch.
             ** apply pool_branchfree_cons; [apply Hbk |].
                apply pool_branchfree_replace; [assumption | apply Hbk].
             ** apply pool_branchfree_cons;
                  [| apply pool_branchfree_replace; [assumption |]];
                  exact (branchfree_trans _ _ _ (Hbf2 i) (Hforall _)).
             ** apply cons_pool_sbisim.
                --- apply Hkf.
                --- apply replace_pool_sbisim; [exact Hpool | apply Hkf].
        * (* user event *)
          dependent destruction Hos.
          assert (Hvis : (v1 $ i) ≅ Vis (inr1 (inr1 usr) : (yieldE +' (forkE +' E)) Y0) k0).
          { rewrite (ctree_eta (v1 $ i)), Hvi. reflexivity. }
          assert (Htru : trans (obs (inr1 (inr1 usr) : (yieldE +' (forkE +' E)) Y0) x)
                           (v1 $ i) (k0 x)).
          { rewrite Hvis. apply trans_vis. }
          destruct (sbisim_trans_l _ _ _ _ (Hpool i) Htru) as (u' & Htr2 & Hsbu).
          assert (Hbk : BranchFree (k0 x)).
          { pose proof (Hbf1 i) as Hb; apply branchfree_unfold in Hb;
              rewrite Hvi in Hb; ddestruction Hb; auto. }
          exists (schedule (S n') ((v2 @ i := u')) (Some i)). split.
          ++ apply (schedule_lift_user n' v2 i usr x u' Htr2).
          ++ assert (Ht' : t' ≅ schedule (S n') ((v1 @ i := (k0 x))) (Some i)).
             { rewrite (ctree_eta t'), <- Hot', <- (ctree_eta t).
               symmetry; assumption. }
             rewrite Ht'. apply Hch.
             ** apply pool_branchfree_replace; assumption.
             ** apply pool_branchfree_replace; [assumption |].
                exact (branchfree_trans _ _ _ (Hbf2 i) Htr2).
             ** apply replace_pool_sbisim; assumption.
      + destruct nn as [| n'].
        * rewrite (schedule_empty_none v1) in Hos. discriminate Hos.
        * (* None nonempty: the scheduling Yield *)
          rewrite (schedule_no_focus_nonempty n' v1) in Hos.
          dependent destruction Hos.
          destruct x.
          exists (brS (branchn (S n')) (fun j => schedule (S n') v2 (Some j))). split.
          -- apply (trans_schedule_no_focus_nonempty n' v2).
          -- assert (Ht' : t' ≅ brS (branchn (S n')) (fun j => schedule (S n') v1 (Some j))).
             { rewrite (ctree_eta t'), <- Hot', <- (ctree_eta t).
               symmetry; assumption. }
             rewrite Ht'.
             apply (b_chain R).
             apply step_sb_brS_id; [reflexivity | intro j].
             apply Hch; assumption.
    - (* Transval *)
      destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        focused_heads v1 i Hos Hbf1 Hvi.
      + destruct nn as [| n'].
        * rewrite (schedule_empty_none v1) in Hos.
          inversion Hos; subst.
          exists Stuck. split.
          -- rewrite (trans_schedule_empty_ret v2). apply trans_ret.
          -- assert (Ht' : t' ≅ Stuck).
             { rewrite (ctree_eta t'), <- Hot'. reflexivity. }
             rewrite Ht'. reflexivity.
        * rewrite (schedule_no_focus_nonempty n' v1) in Hos.
          discriminate Hos.
  Qed.

  Theorem sbisim_schedule n (v1 v2 : pool E B n) focus :
    pool_branchfree v1 -> pool_branchfree v2 ->
    pool_sbisim v1 v2 -> schedule n v1 focus ~ schedule n v2 focus.
  Proof.
    revert n v1 v2 focus.
    unfold sbisim; coinduction R CH.
    intros n v1 v2 focus Hbf1 Hbf2 Hpool.
    split.
    - intros l t' TR.
      destruct (schedule_match CH _ _ _ TR n v1 v2 focus t'
                  eq_refl eq_refl Hbf1 Hbf2 Hpool) as (u' & Htru & Hres).
      exists l, u'. split; [exact Htru | split; [exact Hres | reflexivity]].
    - intros l t' TR.
      destruct (schedule_match CH _ _ _ TR n v2 v1 focus t'
                  eq_refl eq_refl Hbf2 Hbf1 (pool_sbisim_sym v1 v2 Hpool))
        as (u' & Htru & Hres).
      exists l, u'. split; [exact Htru | split].
      + unfold Basics.flip. symmetry. exact Hres.
      + reflexivity.
  Qed.

End SchedulerTransitions.

(** ** Instrumented scheduling respects [equ]-equal pools. *)
(** This is the bridge used to normalize a source denotation before applying a
    singleton scheduler rule: it transports [pool_equ] through both erasures
    and through state instrumentation. *)
Lemma instr_schedule_pool_equ {Σ B} `{Bn -< B} n (v v' : pool (stateE Σ) B n) focus σ :
  pool_equ v v' ->
  instr_schedule n v focus σ ≅ instr_schedule n v' focus σ.
Proof.
  intro Hvv.
  unfold instr_schedule, interp_yield, interp_spawn, instr_stateE.
  rewrite (schedule_pool_proper n v v' focus Hvv).
  reflexivity.
Qed.

(** * Pools up to finitely many leading guards.

    The canonical slotwise lift of [guard_equ].  Reuses
    [vector_replace_pointwise] and the Stdlib vector replacement laws; there
    is no second pool relation. *)
Section PoolGuardEqu.
  Context {E B : Type -> Type}.

  Definition pool_guard_equ {n} (ts us : pool E B n) : Prop :=
    forall i, guard_equ (ts $ i) (us $ i).

  Lemma pool_equ_guard {n} (ts us : pool E B n) :
    pool_equ ts us -> pool_guard_equ ts us.
  Proof. intros H i; apply guard_equ_equ, H. Qed.

  Lemma pool_replace_current {n} (ts : pool E B n) (i : Fin.t n) :
    pool_equ (ts @ i := (ts $ i)) ts.
  Proof.
    intro j; destruct (Fin.eq_dec j i) as [->|Hne].
    - rewrite Vector.nth_replace_eq; reflexivity.
    - rewrite Vector.nth_replace_neq by congruence; reflexivity.
  Qed.

  Lemma pool_equ_guard_trans {n} (ts us vs : pool E B n) :
    pool_equ ts us -> pool_guard_equ us vs -> pool_guard_equ ts vs.
  Proof.
    intros Eq H i; eapply guard_equ_trans; [apply guard_equ_equ, Eq|apply H].
  Qed.
End PoolGuardEqu.

Local Typeclasses Transparent equ.


(** * Alignment up to finitely many leading guards.

    [galigned t u] relates two trees whose every node agrees, except that
    each side may carry finitely many extra guards before a node.  A pure
    guard round consumes at least one guard on BOTH sides, so silent
    divergence is only ever aligned with silent divergence.  Hidden branches
    align branchwise.  The relation is preserved by the erasure and state
    interpreters and by the scheduler on guard-equivalent pools, and it
    implies strong bisimulation. *)

Fixpoint guards {E B} {X} (n : nat) (t : ctree E B X) : ctree E B X :=
  match n with 0 => t | S n => Guard (guards n t) end.

Section Guards.
  Context {E B : Type -> Type} {X : Type}.

  Lemma guards_equ n (t u : ctree E B X) : t ≅ u -> guards n t ≅ guards n u.
  Proof. intro H; induction n; cbn [guards]; [exact H|apply guard_equ_node; exact IHn]. Qed.

  Lemma guards_add n m (t : ctree E B X) : guards (n + m)%nat t = guards n (guards m t).
  Proof. induction n; cbn [guards Nat.add]; [reflexivity|now rewrite IHn]. Qed.

  Lemma guards_guard n (t : ctree E B X) : guards n (Guard t) = guards (S n) t.
  Proof. induction n; cbn [guards]; [reflexivity|now rewrite IHn]. Qed.

  Lemma guards_trans n l (t u : ctree E B X) : trans l t u -> trans l (guards n t) u.
  Proof. intro H; induction n; cbn [guards]; [exact H|now apply trans_guard]. Qed.

  (** Guard prefixes are cancellative. *)
  Lemma guards_cancel : forall b c (x y : ctree E B X),
    guards b x ≅ guards c y ->
    (exists d, x ≅ guards d y /\ c = (b + d)%nat) \/ (exists d, y ≅ guards d x /\ b = (c + d)%nat).
  Proof.
    induction b as [|b IH]; intros c x y H.
    - left; exists c; split; [exact H|reflexivity].
    - destruct c as [|c].
      + right; exists (S b); split; [symmetry; exact H|reflexivity].
      + cbn [guards] in H; apply equ_guard_inv in H.
        destruct (IH c x y H) as [(d & Hd & ->)|(d & Hd & ->)];
          [left|right]; exists d; split; auto.
  Qed.

  (** [guard_equ] is exactly "the same tree after finitely many guards". *)
  Lemma guard_equ_guards (t u : ctree E B X) :
    guard_equ t u -> exists a b x, t ≅ guards a x /\ u ≅ guards b x.
  Proof.
    intro H; induction H as [t u [Eq|Eg]|t|t u H IH|t u v H1 IH1 H2 IH2].
    - exists 0, 0, u; split; [exact Eq|reflexivity].
    - exists 1, 0, u; split; [exact Eg|reflexivity].
    - exists 0, 0, t; split; reflexivity.
    - destruct IH as (a & b & x & Ht & Hu); exists b, a, x; split; assumption.
    - destruct IH1 as (a & b & x & Ht & Hu), IH2 as (c & d & y & Hu' & Hv).
      assert (Hxy : guards b x ≅ guards c y) by (rewrite <- Hu, <- Hu'; reflexivity).
      destruct (guards_cancel b c x y Hxy) as [(e & Hx & ->)|(e & Hy & ->)].
      + exists (a + e)%nat, d, y; split; [|exact Hv].
        rewrite Ht, (guards_equ a _ _ Hx), guards_add; reflexivity.
      + exists a, (d + e)%nat, x; split; [exact Ht|].
        rewrite Hv, (guards_equ d _ _ Hy), guards_add; reflexivity.
  Qed.
End Guards.

CoInductive galigned {E B} {X} : ctree E B X -> ctree E B X -> Prop :=
| galign_guard t u n m t' u' :
    t ≅ guards (S n) t' -> u ≅ guards (S m) u' ->
    galigned t' u' -> galigned t u
| galign_ret t u n m r :
    t ≅ guards n (Ret r) -> u ≅ guards m (Ret r) -> galigned t u
| galign_br t u n m {Y} (c : B Y) (k k' : Y -> ctree E B X) :
    t ≅ guards n (Br c k) -> u ≅ guards m (Br c k') ->
    (forall i, galigned (k i) (k' i)) -> galigned t u
| galign_vis t u n m {Y} (e : E Y) (k k' : Y -> ctree E B X) :
    t ≅ guards n (Vis e k) -> u ≅ guards m (Vis e k') ->
    (forall x, galigned (k x) (k' x)) -> galigned t u
| galign_stuck t u n m :
    t ≅ guards n Stuck -> u ≅ guards m Stuck -> galigned t u
| galign_step t u n m t' u' :
    t ≅ guards n (Step t') -> u ≅ guards m (Step u') ->
    galigned t' u' -> galigned t u.

Section GuardAlignment.
  Context {E B : Type -> Type} {X : Type}.

  Lemma galigned_equ (t u a b : ctree E B X) :
    t ≅ a -> u ≅ b -> galigned t u -> galigned a b.
  Proof.
    intros Et Eu H; destruct H as
      [t u n m t' u' El Er H|t u n m r El Er|t u n m Y c k k' El Er H
      |t u n m Y e k k' El Er H|t u n m El Er|t u n m t' u' El Er H].
    - eapply galign_guard; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
    - eapply galign_ret; [rewrite <- Et; exact El|rewrite <- Eu; exact Er].
    - eapply galign_br; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
    - eapply galign_vis; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
    - eapply galign_stuck; [rewrite <- Et; exact El|rewrite <- Eu; exact Er].
    - eapply galign_step; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
  Qed.

  Lemma galigned_sym : forall t u : ctree E B X, galigned t u -> galigned u t.
  Proof.
    cofix IH; intros t u H; destruct H as
      [t u n m t' u' El Er H|t u n m r El Er|t u n m Y c k k' El Er H
      |t u n m Y e k k' El Er H|t u n m El Er|t u n m t' u' El Er H].
    - eapply galign_guard; [exact Er|exact El|apply IH; exact H].
    - eapply galign_ret; [exact Er|exact El].
    - eapply galign_br; [exact Er|exact El|intro i; apply IH, H].
    - eapply galign_vis; [exact Er|exact El|intro x; apply IH, H].
    - eapply galign_stuck; [exact Er|exact El].
    - eapply galign_step; [exact Er|exact El|apply IH; exact H].
  Qed.

  Lemma galigned_stuck : galigned (Stuck : ctree E B X) Stuck.
  Proof. apply (galign_stuck Stuck Stuck 0 0); reflexivity. Qed.

  Lemma galigned_refl : forall t : ctree E B X, galigned t t.
  Proof.
    cofix IH; intro t.
    destruct (observe t) as [r| |s|g|Y e k|Y c k] eqn:Ht;
      pose proof (observe_equ_go t _ Ht) as Et.
    - apply (galign_ret _ _ 0 0 r); exact Et.
    - apply (galign_stuck _ _ 0 0); exact Et.
    - apply (galign_step _ _ 0 0 s s); [exact Et|exact Et|apply IH].
    - apply (galign_guard _ _ 0 0 g g); [exact Et|exact Et|apply IH].
    - apply (galign_vis _ _ 0 0 e k k); [exact Et|exact Et|intro x; apply IH].
    - apply (galign_br _ _ 0 0 c k k); [exact Et|exact Et|intro i; apply IH].
  Qed.

  Local Ltac head_absurd H := step in H; cbn in H; inversion H.

  Local Ltac galigned_inv A :=
    inversion A as
      [left right n m tl tr El Er Hnext|left right n m r El Er
      |left right n m Y c kk kk' El Er Hnext|left right n m Y e kk kk' El Er Hnext
      |left right n m El Er|left right n m tl tr El Er Hnext];
    subst; clear A.

  Lemma galigned_match l T U :
    @trans_ E B X l T U ->
    forall u, galigned (go T) u ->
    exists u', trans l u u' /\ galigned (go U) u'.
  Proof.
    intro TR; induction TR as
      [Y0 c0 pick k0 l target TR IH
      |inner target l TR IH
      |target result Eresult
      |Y0 e0 k0 answer result Eresult
      |value]; intros u A.
    - (* Transbr: hidden branch, aligned branchwise *)
      galigned_inv A.
      + head_absurd El.
      + destruct n; head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El.
        pose proof (equ_br_invT _ _ _ _ El) as HY; subst Y.
        pose proof (equ_br_invE _ _ _ _ El) as [Hc Ek]; subst c.
        assert (Ai : galigned (go (observe (k0 pick))) (kk' pick)).
        { eapply galigned_equ; [|reflexivity|exact (Hnext pick)].
          transitivity (k0 pick); [symmetry; exact (Ek pick)|apply ctree_eta]. }
        destruct (IH (kk' pick) Ai) as (next & Tnext & Anext).
        exists next; split; [|exact Anext].
        rewrite Er; apply guards_trans; eapply trans_br; [exact Tnext|reflexivity].
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
    - (* Transguard *)
      galigned_inv A.
      + cbn [guards] in El; apply equ_guard_inv in El; destruct n as [|n].
        * cbn [guards] in El.
          assert (Ai : galigned (go (observe inner)) tr).
          { eapply galigned_equ; [|reflexivity|exact Hnext].
            transitivity inner; [symmetry; exact El|apply ctree_eta]. }
          destruct (IH tr Ai) as (next & Tnext & Anext).
          exists next; split; [rewrite Er; now apply guards_trans|exact Anext].
        * apply IH; eapply galigned_equ; [apply ctree_eta|reflexivity|].
          eapply galign_guard; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_inv in El.
        apply IH; eapply galigned_equ; [apply ctree_eta|reflexivity|].
        eapply galign_ret; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_inv in El.
        apply IH; eapply galigned_equ; [apply ctree_eta|reflexivity|].
        eapply galign_br; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_inv in El.
        apply IH; eapply galigned_equ; [apply ctree_eta|reflexivity|].
        eapply galign_vis; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_inv in El.
        apply IH; eapply galigned_equ; [apply ctree_eta|reflexivity|].
        eapply galign_stuck; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_inv in El.
        apply IH; eapply galigned_equ; [apply ctree_eta|reflexivity|].
        eapply galign_step; eassumption.
    - (* Transtau: a visible step *)
      galigned_inv A.
      + head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El; apply equ_step_inv in El.
        exists tr; split.
        * rewrite Er; apply guards_trans, trans_step.
        * eapply galigned_equ; [|reflexivity|exact Hnext].
          transitivity target; [symmetry; exact El|].
          transitivity result; [symmetry; exact Eresult|apply ctree_eta].
    - (* Transobs *)
      galigned_inv A.
      + head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El.
        pose proof (equ_vis_invT _ _ _ _ El) as HY; subst Y.
        pose proof (equ_vis_invE _ _ _ _ El) as [He Ek]; subst e.
        exists (kk' answer); split.
        * rewrite Er; apply guards_trans; apply trans_vis.
        * eapply galigned_equ; [|reflexivity|exact (Hnext answer)].
          transitivity (k0 answer); [symmetry; exact (Ek answer)|].
          transitivity result; [exact Eresult|apply ctree_eta].
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
    - (* Transval *)
      galigned_inv A.
      + head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El; apply equ_ret_inv in El; subst r.
        exists Stuck; split.
        * rewrite Er; apply guards_trans, trans_ret.
        * exact galigned_stuck.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
  Qed.

  Lemma galigned_trans (t u next : ctree E B X) l :
    galigned t u -> trans l t next ->
    exists other, trans l u other /\ galigned next other.
  Proof.
    intros A TR.
    assert (Ae : galigned (go (observe t)) u).
    { eapply galigned_equ; [apply ctree_eta|reflexivity|exact A]. }
    destruct (galigned_match l (observe t) (observe next) TR u Ae)
      as (other & To & Ao).
    exists other; split; [exact To|].
    eapply galigned_equ; [symmetry; apply ctree_eta|reflexivity|exact Ao].
  Qed.

  Lemma galigned_sbisim : forall t u : ctree E B X, galigned t u -> t ~ u.
  Proof.
    unfold sbisim; coinduction R IH.
    intros t u A; split; intros l next TR.
    - destruct (galigned_trans t u next l A TR) as (other & To & Ao).
      exists l, other; split; [exact To|]; split; [now apply IH|reflexivity].
    - destruct (galigned_trans u t next l (galigned_sym t u A) TR)
        as (other & To & Ao).
      exists l, other; split; [exact To|]; split.
      + apply IH, galigned_sym; exact Ao.
      + reflexivity.
  Qed.
End GuardAlignment.

(** ** A coinduction principle for guard alignment *)

Inductive galignF {E B} {X} (R : ctree E B X -> ctree E B X -> Prop)
  : ctree E B X -> ctree E B X -> Prop :=
| galignF_guard t u n m t' u' :
    t ≅ guards (S n) t' -> u ≅ guards (S m) u' -> R t' u' -> galignF R t u
| galignF_ret t u n m r :
    t ≅ guards n (Ret r) -> u ≅ guards m (Ret r) -> galignF R t u
| galignF_br t u n m {Y} (c : B Y) (k k' : Y -> ctree E B X) :
    t ≅ guards n (Br c k) -> u ≅ guards m (Br c k') ->
    (forall i, R (k i) (k' i)) -> galignF R t u
| galignF_vis t u n m {Y} (e : E Y) (k k' : Y -> ctree E B X) :
    t ≅ guards n (Vis e k) -> u ≅ guards m (Vis e k') ->
    (forall x, R (k x) (k' x)) -> galignF R t u
| galignF_stuck t u n m :
    t ≅ guards n Stuck -> u ≅ guards m Stuck -> galignF R t u
| galignF_step t u n m t' u' :
    t ≅ guards n (Step t') -> u ≅ guards m (Step u') -> R t' u' -> galignF R t u.

Lemma galigned_coind {E B} {X} (R : ctree E B X -> ctree E B X -> Prop) :
  (forall t u, R t u -> galignF R t u) -> forall t u, R t u -> galigned t u.
Proof.
  intro Hstep; cofix CIH; intros t u H.
  destruct (Hstep t u H) as
    [t u n m t' u' El Er H'|t u n m r El Er|t u n m Y c k k' El Er H'
    |t u n m Y e k k' El Er H'|t u n m El Er|t u n m t' u' El Er H'].
  - exact (galign_guard t u n m t' u' El Er (CIH t' u' H')).
  - exact (galign_ret t u n m r El Er).
  - exact (galign_br t u n m c k k' El Er (fun i => CIH (k i) (k' i) (H' i))).
  - exact (galign_vis t u n m e k k' El Er (fun x => CIH (k x) (k' x) (H' x))).
  - exact (galign_stuck t u n m El Er).
  - exact (galign_step t u n m t' u' El Er (CIH t' u' H')).
Qed.

#[global] Instance guards_proper {E B} {X} n :
  Proper (equ eq ==> equ eq) (@guards E B X n).
Proof. intros t u H; apply guards_equ, H. Qed.

Lemma guards_shift {E B} {X} n a (t : ctree E B X) :
  guards n (guards (S a) t) = guards (S (n + a)) t.
Proof. rewrite <- guards_add, Nat.add_succ_r; reflexivity. Qed.


(** ** Interpretation preserves guard alignment *)
Section InterpAlign.
  Universe r.
  Context {E F B : Type -> Type} (h : E ~> ctree@{_ _ _ _ r _} F B) {X : Type}.

  Abbreviation interp' := (interp (M := ctree F B) h).

  Lemma interp_guards n (t : ctree E B X) : interp' (guards n t) ≅ guards n (interp' t).
  Proof.
    induction n; cbn [guards]; [reflexivity|].
    rewrite interp_guard_node; apply guard_equ_node; exact IHn.
  Qed.

  Inductive interp_rel : ctree F B X -> ctree F B X -> Prop :=
  | interp_rel_tree n m (t u : ctree E B X) T U :
      galigned t u -> T ≅ guards n (interp' t) -> U ≅ guards m (interp' u) ->
      interp_rel T U
  | interp_rel_bind n m (A : Type) (a : ctree F B A) (k k' : A -> ctree E B X) T U :
      (forall x, galigned (k x) (k' x)) ->
      T ≅ guards n (a >>= fun x => Guard (interp' (k x))) ->
      U ≅ guards m (a >>= fun x => Guard (interp' (k' x))) -> interp_rel T U.

  Lemma interp_rel_bind_step n m A (a : ctree F B A) (k k' : A -> ctree E B X) T U :
    (forall x, galigned (k x) (k' x)) ->
    T ≅ guards n (a >>= fun x => Guard (interp' (k x))) ->
    U ≅ guards m (a >>= fun x => Guard (interp' (k' x))) -> galignF interp_rel T U.
  Proof.
    intros Hk ET EU.
    destruct (observe a) as [x| |s|g|Y e kk|Y c kk] eqn:Ha;
      pose proof (observe_equ_go a _ Ha) as Ea.
    - apply (galignF_guard _ T U n m (interp' (k x)) (interp' (k' x))).
      + rewrite ET, Ea, bind_ret_l, guards_guard; reflexivity.
      + rewrite EU, Ea, bind_ret_l, guards_guard; reflexivity.
      + apply (interp_rel_tree 0 0 (k x) (k' x)); [apply Hk|reflexivity|reflexivity].
    - apply (galignF_stuck _ T U n m).
      + rewrite ET, Ea, bind_stuck; reflexivity.
      + rewrite EU, Ea, bind_stuck; reflexivity.
    - apply (galignF_step _ T U n m (s >>= fun x => Guard (interp' (k x)))
                                    (s >>= fun x => Guard (interp' (k' x)))).
      + rewrite ET, Ea, bind_step; reflexivity.
      + rewrite EU, Ea, bind_step; reflexivity.
      + apply (interp_rel_bind 0 0 A s k k'); [exact Hk|reflexivity|reflexivity].
    - apply (galignF_guard _ T U n m (g >>= fun x => Guard (interp' (k x)))
                                     (g >>= fun x => Guard (interp' (k' x)))).
      + rewrite ET, Ea, bind_guard, guards_guard; reflexivity.
      + rewrite EU, Ea, bind_guard, guards_guard; reflexivity.
      + apply (interp_rel_bind 0 0 A g k k'); [exact Hk|reflexivity|reflexivity].
    - apply (galignF_vis _ T U n m e (fun y => kk y >>= fun x => Guard (interp' (k x)))
                                     (fun y => kk y >>= fun x => Guard (interp' (k' x)))).
      + rewrite ET, Ea, bind_vis; reflexivity.
      + rewrite EU, Ea, bind_vis; reflexivity.
      + intro y; apply (interp_rel_bind 0 0 A (kk y) k k'); [exact Hk|reflexivity|reflexivity].
    - apply (galignF_br _ T U n m c (fun i => kk i >>= fun x => Guard (interp' (k x)))
                                    (fun i => kk i >>= fun x => Guard (interp' (k' x)))).
      + rewrite ET, Ea, bind_br; reflexivity.
      + rewrite EU, Ea, bind_br; reflexivity.
      + intro i; apply (interp_rel_bind 0 0 A (kk i) k k'); [exact Hk|reflexivity|reflexivity].
  Qed.

  Lemma interp_rel_step T U : interp_rel T U -> galignF interp_rel T U.
  Proof.
    intros [n m t u T' U' A ET EU|n m A0 a k k' T' U' Hk ET EU].
    - destruct A as [t u a b t' u' Et Eu A|t u a b r Et Eu
        |t u a b Y c kk kk' Et Eu Hk|t u a b Y e kk kk' Et Eu Hk
        |t u a b Et Eu|t u a b t' u' Et Eu A].
      + apply (galignF_guard _ T' U' (n + a) (m + b) (interp' t') (interp' u')).
        * rewrite ET, Et, interp_guards, guards_shift; reflexivity.
        * rewrite EU, Eu, interp_guards, guards_shift; reflexivity.
        * apply (interp_rel_tree 0 0 t' u'); [exact A|reflexivity|reflexivity].
      + apply (galignF_ret _ T' U' (n + a) (m + b) r).
        * rewrite ET, Et, interp_guards, interp_ret_node, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, interp_ret_node, <- guards_add; reflexivity.
      + apply (galignF_br _ T' U' (n + a) (m + b) c
          (fun i => Guard (interp' (kk i))) (fun i => Guard (interp' (kk' i)))).
        * rewrite ET, Et, interp_guards, interp_br_node, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, interp_br_node, <- guards_add; reflexivity.
        * intro i; apply (interp_rel_tree 1 1 (kk i) (kk' i)); [apply Hk|reflexivity|reflexivity].
      + apply (interp_rel_bind_step (n + a) (m + b) _ (h _ e) kk kk' T' U' Hk).
        * rewrite ET, Et, interp_guards, interp_vis_node, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, interp_vis_node, <- guards_add; reflexivity.
      + apply (galignF_stuck _ T' U' (n + a) (m + b)).
        * rewrite ET, Et, interp_guards, interp_stuck_node, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, interp_stuck_node, <- guards_add; reflexivity.
      + apply (galignF_step _ T' U' (n + a) (m + b) (Guard (interp' t')) (Guard (interp' u'))).
        * rewrite ET, Et, interp_guards, interp_step_node, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, interp_step_node, <- guards_add; reflexivity.
        * apply (interp_rel_tree 1 1 t' u'); [exact A|reflexivity|reflexivity].
    - exact (interp_rel_bind_step n m A0 a k k' T' U' Hk ET EU).
  Qed.

  Lemma interp_galigned (t u : ctree E B X) :
    galigned t u -> galigned (interp' t) (interp' u).
  Proof.
    intro H; apply (galigned_coind interp_rel interp_rel_step).
    apply (interp_rel_tree 0 0 t u); [exact H|reflexivity|reflexivity].
  Qed.
End InterpAlign.

(** ** State interpretation preserves guard alignment *)
Section InterpStateAlign.
  Context {E F B : Type -> Type} {S : Type}
    (h : E ~> stateT S (ctree F B)) {X : Type}.

  Lemma interp_state_guards n (t : ctree E B X) s :
    interp_state h (guards n t) s ≅ guards n (interp_state h t s).
  Proof.
    induction n; cbn [guards]; [reflexivity|].
    rewrite interp_state_guard; apply guard_equ_node; exact IHn.
  Qed.

  Lemma interp_state_br_node {Y} (c : B Y) (k : Y -> ctree E B X) s :
    interp_state h (Br c k) s ≅ Br c (fun y => Guard (interp_state h (k y) s)).
  Proof.
    rewrite interp_state_br.
    change (Monad.bind (mbr c) ?f) with (CTree.bind (branch c : ctree F B Y) f).
    rewrite bind_branch; reflexivity.
  Qed.

  Inductive istate_rel : ctree F B (S * X) -> ctree F B (S * X) -> Prop :=
  | istate_rel_tree n m (t u : ctree E B X) s T U :
      galigned t u -> T ≅ guards n (interp_state h t s) ->
      U ≅ guards m (interp_state h u s) -> istate_rel T U
  | istate_rel_bind n m (A : Type) (a : ctree F B (S * A)) (k k' : A -> ctree E B X) T U :
      (forall x, galigned (k x) (k' x)) ->
      T ≅ guards n (a >>= fun sx => Guard (interp_state h (k (snd sx)) (fst sx))) ->
      U ≅ guards m (a >>= fun sx => Guard (interp_state h (k' (snd sx)) (fst sx))) ->
      istate_rel T U.

  Lemma istate_rel_bind_step n m A (a : ctree F B (S * A)) (k k' : A -> ctree E B X) T U :
    (forall x, galigned (k x) (k' x)) ->
    T ≅ guards n (a >>= fun sx => Guard (interp_state h (k (snd sx)) (fst sx))) ->
    U ≅ guards m (a >>= fun sx => Guard (interp_state h (k' (snd sx)) (fst sx))) ->
    galignF istate_rel T U.
  Proof.
    intros Hk ET EU.
    destruct (observe a) as [[s' x]| |st|g|Y e kk|Y c kk] eqn:Ha;
      pose proof (observe_equ_go a _ Ha) as Ea.
    - apply (galignF_guard _ T U n m (interp_state h (k x) s') (interp_state h (k' x) s')).
      + rewrite ET, Ea, bind_ret_l; cbn [fst snd]; rewrite guards_guard; reflexivity.
      + rewrite EU, Ea, bind_ret_l; cbn [fst snd]; rewrite guards_guard; reflexivity.
      + apply (istate_rel_tree 0 0 (k x) (k' x) s'); [apply Hk|reflexivity|reflexivity].
    - apply (galignF_stuck _ T U n m).
      + rewrite ET, Ea, bind_stuck; reflexivity.
      + rewrite EU, Ea, bind_stuck; reflexivity.
    - apply (galignF_step _ T U n m
        (st >>= fun sx => Guard (interp_state h (k (snd sx)) (fst sx)))
        (st >>= fun sx => Guard (interp_state h (k' (snd sx)) (fst sx)))).
      + rewrite ET, Ea, bind_step; reflexivity.
      + rewrite EU, Ea, bind_step; reflexivity.
      + apply (istate_rel_bind 0 0 A st k k'); [exact Hk|reflexivity|reflexivity].
    - apply (galignF_guard _ T U n m
        (g >>= fun sx => Guard (interp_state h (k (snd sx)) (fst sx)))
        (g >>= fun sx => Guard (interp_state h (k' (snd sx)) (fst sx)))).
      + rewrite ET, Ea, bind_guard, guards_guard; reflexivity.
      + rewrite EU, Ea, bind_guard, guards_guard; reflexivity.
      + apply (istate_rel_bind 0 0 A g k k'); [exact Hk|reflexivity|reflexivity].
    - apply (galignF_vis _ T U n m e
        (fun y => kk y >>= fun sx => Guard (interp_state h (k (snd sx)) (fst sx)))
        (fun y => kk y >>= fun sx => Guard (interp_state h (k' (snd sx)) (fst sx)))).
      + rewrite ET, Ea, bind_vis; reflexivity.
      + rewrite EU, Ea, bind_vis; reflexivity.
      + intro y; apply (istate_rel_bind 0 0 A (kk y) k k'); [exact Hk|reflexivity|reflexivity].
    - apply (galignF_br _ T U n m c
        (fun i => kk i >>= fun sx => Guard (interp_state h (k (snd sx)) (fst sx)))
        (fun i => kk i >>= fun sx => Guard (interp_state h (k' (snd sx)) (fst sx)))).
      + rewrite ET, Ea, bind_br; reflexivity.
      + rewrite EU, Ea, bind_br; reflexivity.
      + intro i; apply (istate_rel_bind 0 0 A (kk i) k k'); [exact Hk|reflexivity|reflexivity].
  Qed.

  Lemma istate_rel_step T U : istate_rel T U -> galignF istate_rel T U.
  Proof.
    intros [n m t u s T' U' A ET EU|n m A0 a k k' T' U' Hk ET EU].
    - destruct A as [t u a b t' u' Et Eu A|t u a b r Et Eu
        |t u a b Y c kk kk' Et Eu Hk|t u a b Y e kk kk' Et Eu Hk
        |t u a b Et Eu|t u a b t' u' Et Eu A].
      + apply (galignF_guard _ T' U' (n + a) (m + b)
          (interp_state h t' s) (interp_state h u' s)).
        * rewrite ET, Et, interp_state_guards, guards_shift; reflexivity.
        * rewrite EU, Eu, interp_state_guards, guards_shift; reflexivity.
        * apply (istate_rel_tree 0 0 t' u' s); [exact A|reflexivity|reflexivity].
      + apply (galignF_ret _ T' U' (n + a) (m + b) (s, r)).
        * rewrite ET, Et, interp_state_guards, interp_state_ret, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_state_guards, interp_state_ret, <- guards_add; reflexivity.
      + apply (galignF_br _ T' U' (n + a) (m + b) c
          (fun i => Guard (interp_state h (kk i) s))
          (fun i => Guard (interp_state h (kk' i) s))).
        * rewrite ET, Et, interp_state_guards, interp_state_br_node, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_state_guards, interp_state_br_node, <- guards_add; reflexivity.
        * intro i; apply (istate_rel_tree 1 1 (kk i) (kk' i) s);
            [apply Hk|reflexivity|reflexivity].
      + apply (istate_rel_bind_step (n + a) (m + b) _ (h _ e s) kk kk' T' U' Hk).
        * rewrite ET, Et, interp_state_guards, interp_state_vis, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_state_guards, interp_state_vis, <- guards_add; reflexivity.
      + apply (galignF_stuck _ T' U' (n + a) (m + b)).
        * rewrite ET, Et, interp_state_guards, interp_state_stuck, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_state_guards, interp_state_stuck, <- guards_add; reflexivity.
      + apply (galignF_step _ T' U' (n + a) (m + b)
          (Guard (interp_state h t' s)) (Guard (interp_state h u' s))).
        * rewrite ET, Et, interp_state_guards, interp_state_step, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_state_guards, interp_state_step, <- guards_add; reflexivity.
        * apply (istate_rel_tree 1 1 t' u' s); [exact A|reflexivity|reflexivity].
    - exact (istate_rel_bind_step n m A0 a k k' T' U' Hk ET EU).
  Qed.

  Lemma interp_state_galigned (t u : ctree E B X) s :
    galigned t u -> galigned (interp_state h t s) (interp_state h u s).
  Proof.
    intro H; apply (galigned_coind istate_rel istate_rel_step).
    apply (istate_rel_tree 0 0 t u s); [exact H|reflexivity|reflexivity].
  Qed.
End InterpStateAlign.

(** ** The scheduler maps guard-equivalent pools to aligned trees *)
Section ScheduleAlign.
  Context {E B : Type -> Type} `{Bn -< B}.

  Abbreviation Yield' := (inl1 Yield : (yieldE +' (spawnE +' E)) unit).
  Abbreviation Spawn' := (inr1 (inl1 Spawn) : (yieldE +' (spawnE +' E)) unit).

  Lemma schedule_focus_guards : forall a N (ts : pool E B (S N)) i (x : thread E B),
    (ts $ i) ≅ guards a x ->
    schedule (S N) ts (Some i) ≅ guards a (schedule (S N) (ts @ i := x) (Some i)).
  Proof.
    induction a as [|a IH]; intros N ts i x Hx; cbn [guards] in *.
    - apply schedule_pool_proper.
      intro j; destruct (Fin.eq_dec j i) as [->|Hne].
      + rewrite Vector.nth_replace_eq; exact Hx.
      + rewrite Vector.nth_replace_neq by congruence; reflexivity.
    - transitivity (schedule (S N) (ts @ i := Guard (guards a x)) (Some i)).
      { apply schedule_pool_proper.
        intro j; destruct (Fin.eq_dec j i) as [->|Hne].
        + rewrite Vector.nth_replace_eq; exact Hx.
        + rewrite Vector.nth_replace_neq by congruence; reflexivity. }
      rewrite (trans_schedule_focused_guard N (ts @ i := Guard (guards a x)) i (guards a x)
          ltac:(rewrite Vector.nth_replace_eq; reflexivity)).
      rewrite Vector.replace_replace_eq.
      apply guard_equ_node.
      rewrite (IH N (ts @ i := guards a x) i x)
        by (rewrite Vector.nth_replace_eq; reflexivity).
      rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  Lemma pool_guard_equ_replace {N} (ts us : pool E B N) i x :
    pool_guard_equ ts us -> pool_guard_equ (ts @ i := x) (us @ i := x).
  Proof.
    unfold pool_guard_equ; intros Hp; apply vector_replace_pointwise; [intros j _; apply Hp|reflexivity].
  Qed.

  Lemma pool_guard_equ_remove {N} (ts us : pool E B (S N)) i :
    pool_guard_equ ts us -> pool_guard_equ (ts -- i) (us -- i).
  Proof. unfold pool_guard_equ; intros Hp; apply vector_remove_pointwise; intros j _; apply Hp. Qed.

  Lemma pool_guard_equ_cons {N} x (ts us : pool E B N) :
    pool_guard_equ ts us -> pool_guard_equ (x :: ts) (x :: us).
  Proof. unfold pool_guard_equ; intros Hp; apply vector_cons_pointwise; [reflexivity|exact Hp]. Qed.

  Inductive sched_rel : completed E B -> completed E B -> Prop :=
  | sched_rel_at n m N (ts us : pool E B N) f T U :
      pool_guard_equ ts us ->
      T ≅ guards n (schedule N ts f) -> U ≅ guards m (schedule N us f) ->
      sched_rel T U
  | sched_rel_pick n m N (ts us : pool E B (S N)) T U :
      pool_guard_equ ts us ->
      T ≅ guards n (brS (branchn (S N)) (fun i => schedule (S N) ts (Some i))) ->
      U ≅ guards m (brS (branchn (S N)) (fun i => schedule (S N) us (Some i))) ->
      sched_rel T U
  | sched_rel_picked n m N (ts us : pool E B (S N)) i T U :
      pool_guard_equ ts us ->
      T ≅ guards n (Step (schedule (S N) ts (Some i))) ->
      U ≅ guards m (Step (schedule (S N) us (Some i))) ->
      sched_rel T U.

  Lemma sched_rel_step T U : sched_rel T U -> galignF sched_rel T U.
  Proof.
    intros [n m N ts us f T' U' Hp ET EU|n m N ts us T' U' Hp ET EU|n m N ts us i T' U' Hp ET EU].
    2: { apply (galignF_br _ T' U' n m (subevent _ (branchn (S N)))
           (fun i => Step (schedule (S N) ts (Some i))) (fun i => Step (schedule (S N) us (Some i))));
           [exact ET|exact EU|].
         intro i; apply (sched_rel_picked 0 0 N ts us i); [exact Hp|reflexivity|reflexivity]. }
    2: { apply (galignF_step _ T' U' n m (schedule (S N) ts (Some i)) (schedule (S N) us (Some i)));
           [exact ET|exact EU|].
         apply (sched_rel_at 0 0 (S N) ts us (Some i)); [exact Hp|reflexivity|reflexivity]. }
    destruct f as [i|].
    2: { destruct N as [|N].
         - apply (galignF_ret _ T' U' n m tt).
           + rewrite ET, (observe_equ_go _ _ (schedule_empty_none ts)); reflexivity.
           + rewrite EU, (observe_equ_go _ _ (schedule_empty_none us)); reflexivity.
         - apply (galignF_vis _ T' U' n m Yield'
             (fun _ => brS (branchn (S N)) (fun i => schedule (S N) ts (Some i)))
             (fun _ => brS (branchn (S N)) (fun i => schedule (S N) us (Some i)))).
           + rewrite ET, (observe_equ_go _ _ (schedule_no_focus_nonempty N ts)); reflexivity.
           + rewrite EU, (observe_equ_go _ _ (schedule_no_focus_nonempty N us)); reflexivity.
           + intros _; apply (sched_rel_pick 0 0 N ts us); [exact Hp|reflexivity|reflexivity]. }
    destruct N as [|N]; [inversion i|].
    destruct (guard_equ_guards _ _ (Hp i)) as (a & b & x & Ea & Eb).
    pose proof (pool_guard_equ_replace ts us i x Hp) as Hp'.
    set (ts' := ts @ i := x) in *; set (us' := us @ i := x) in *.
    assert (ET' : T' ≅ guards (n + a) (schedule (S N) ts' (Some i)))
      by (rewrite ET, (schedule_focus_guards a N ts i x Ea), <- guards_add; reflexivity).
    assert (EU' : U' ≅ guards (m + b) (schedule (S N) us' (Some i)))
      by (rewrite EU, (schedule_focus_guards b N us i x Eb), <- guards_add; reflexivity).
    assert (Hts : observe (ts' $ i) = observe x) by (unfold ts'; now rewrite Vector.nth_replace_eq).
    assert (Hus : observe (us' $ i) = observe x) by (unfold us'; now rewrite Vector.nth_replace_eq).
    clearbody ts' us'; clear ET EU.
    destruct (observe x) as [[]| |st|y|Y e k|Y c k] eqn:Hx.
    - apply (galignF_guard _ T' U' (n + a) (m + b)
        (schedule N (ts' -- i) None) (schedule N (us' -- i) None)).
      + rewrite ET', (observe_equ_go _ _ (schedule_focused_ret N ts' i Hts)); rewrite <- guards_guard; reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_focused_ret N us' i Hus)); rewrite <- guards_guard; reflexivity.
      + apply (sched_rel_at 0 0 N (ts' -- i) (us' -- i) None);
          [apply pool_guard_equ_remove, Hp'|reflexivity|reflexivity].
    - apply (galignF_stuck _ T' U' (n + a) (m + b)).
      + rewrite ET', (observe_equ_go _ _ (schedule_focused_stuck N ts' i Hts)); reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_focused_stuck N us' i Hus)); reflexivity.
    - apply (galignF_step _ T' U' (n + a) (m + b)
        (schedule (S N) (ts' @ i := st) (Some i)) (schedule (S N) (us' @ i := st) (Some i))).
      + rewrite ET', (observe_equ_go _ _ (schedule_focused_step N ts' i st Hts)); reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_focused_step N us' i st Hus)); reflexivity.
      + eapply (sched_rel_at 0 0 (S N) _ _ (Some i));
          [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
    - apply (galignF_guard _ T' U' (n + a) (m + b)
        (schedule (S N) (ts' @ i := y) (Some i)) (schedule (S N) (us' @ i := y) (Some i))).
      + rewrite ET', (observe_equ_go _ _ (schedule_focused_guard N ts' i y Hts)); rewrite <- guards_guard; reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_focused_guard N us' i y Hus)); rewrite <- guards_guard; reflexivity.
      + eapply (sched_rel_at 0 0 (S N) _ _ (Some i));
          [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
    - destruct e as [y|[f|e']]; [dependent destruction y|dependent destruction f|].
      + apply (galignF_guard _ T' U' (n + a) (m + b)
          (schedule (S N) (ts' @ i := k tt) None) (schedule (S N) (us' @ i := k tt) None)).
        * rewrite ET', (observe_equ_go _ _ (schedule_focused_yield N ts' i k Hts)); rewrite <- guards_guard; reflexivity.
        * rewrite EU', (observe_equ_go _ _ (schedule_focused_yield N us' i k Hus)); rewrite <- guards_guard; reflexivity.
        * eapply (sched_rel_at 0 0 (S N) _ _ None);
            [|cbn [guards]; reflexivity|cbn [guards]; reflexivity];
            apply pool_guard_equ_replace, Hp'.
      + apply (galignF_vis _ T' U' (n + a) (m + b) Spawn'
          (fun _ => schedule (S (S N)) (k true :: (ts' @ i := k false)) (Some (Fin.FS i)))
          (fun _ => schedule (S (S N)) (k true :: (us' @ i := k false)) (Some (Fin.FS i)))).
        * rewrite ET', (observe_equ_go _ _ (schedule_focused_fork N ts' i k Hts)); reflexivity.
        * rewrite EU', (observe_equ_go _ _ (schedule_focused_fork N us' i k Hus)); reflexivity.
        * intros _; eapply (sched_rel_at 0 0 (S (S N)) _ _ (Some (Fin.FS i)));
            [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_cons, pool_guard_equ_replace, Hp'.
      + apply (galignF_vis _ T' U' (n + a) (m + b) (inr1 (inr1 e') : (yieldE +' (spawnE +' E)) Y)
          (fun z => schedule (S N) (ts' @ i := k z) (Some i))
          (fun z => schedule (S N) (us' @ i := k z) (Some i))).
        * rewrite ET', (observe_equ_go _ _ (schedule_focused_user_event N ts' i e' k Hts)); reflexivity.
        * rewrite EU', (observe_equ_go _ _ (schedule_focused_user_event N us' i e' k Hus)); reflexivity.
        * intro z; eapply (sched_rel_at 0 0 (S N) _ _ (Some i));
            [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
    - apply (galignF_br _ T' U' (n + a) (m + b) c
        (fun j => schedule (S N) (ts' @ i := k j) (Some i))
        (fun j => schedule (S N) (us' @ i := k j) (Some i))).
      + rewrite ET', (observe_equ_go _ _ (schedule_focused_br N ts' i c k Hts)); reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_focused_br N us' i c k Hus)); reflexivity.
      + intro j; eapply (sched_rel_at 0 0 (S N) _ _ (Some i));
          [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
  Qed.

  Lemma schedule_galigned N (ts us : pool E B N) f :
    pool_guard_equ ts us -> galigned (schedule N ts f) (schedule N us f).
  Proof.
    intro Hp; apply (galigned_coind sched_rel sched_rel_step).
    apply (sched_rel_at 0 0 N ts us f); [exact Hp|reflexivity|reflexivity].
  Qed.

  (** The erased scheduled view of guard-equivalent pools is aligned. *)
  Lemma erased_schedule_galigned N (ts us : pool E B N) f :
    pool_guard_equ ts us ->
    galigned (interp_yield (interp_spawn (schedule N ts f)))
             (interp_yield (interp_spawn (schedule N us f))).
  Proof.
    intro Hp; unfold interp_yield, interp_spawn.
    apply interp_galigned, interp_galigned, schedule_galigned, Hp.
  Qed.
End ScheduleAlign.
