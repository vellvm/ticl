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

  (** Forgetting finitely many leading guards is a strong bisimulation. *)
  Lemma guard_equ_sbisim (t u : ctree E B X) : guard_equ t u -> t ~ u.
  Proof.
    intro H; induction H as [t u [E1|E1]|t|t u H IH|t u v H1 IH1 H2 IH2].
    - now rewrite E1.
    - rewrite E1; apply sb_guard.
    - reflexivity.
    - now symmetry.
    - now transitivity u.
  Qed.

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
      (both answers of one fork node are installed together), so the scheduler
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
  Context {E B : Type -> Type} {HB : Bn -< B} (sch : Scheduler).
  Abbreviation Yield_ := (inl1 Yield : (yieldE +' (forkE +' E)) unit).
  Abbreviation Fork_ := (inr1 (inl1 Fork) : (yieldE +' (forkE +' E)) bool).

  Lemma schedule_policy_empty_equ (v : pool E B 0) (st : sched_state sch) :
    schedule_policy sch 0 v None st ≅ Ret tt.
  Proof. apply (observe_equ_go _ _ (schedule_policy_empty_none sch v st)). Qed.

  Lemma schedule_policy_focused_ret_equ n (v : pool E B (S n)) (i : Fin.t (S n)) (st : sched_state sch) :
    observe (v $ i) = RetF tt ->
    schedule_policy sch (S n) v (Some i) st ≅ Guard (schedule_policy sch n ((v -- i)) None st).
  Proof. intro Hobs; apply (observe_equ_go _ _ (schedule_policy_focused_ret sch n v i st Hobs)). Qed.

  Lemma schedule_policy_focused_stuck_equ n (v : pool E B (S n)) (i : Fin.t (S n)) (st : sched_state sch) :
    observe (v $ i) = StuckF ->
    schedule_policy sch (S n) v (Some i) st ≅ Stuck.
  Proof. intro Hobs; apply (observe_equ_go _ _ (schedule_policy_focused_stuck sch n v i st Hobs)). Qed.

  Lemma schedule_policy_focused_guard_equ n (v : pool E B (S n)) (i : Fin.t (S n)) t (st : sched_state sch) :
    observe (v $ i) = GuardF t ->
    schedule_policy sch (S n) v (Some i) st
      ≅ Guard (schedule_policy sch (S n) ((v @ i := t)) (Some i) st).
  Proof. intro Hobs; apply (observe_equ_go _ _ (schedule_policy_focused_guard sch n v i t st Hobs)). Qed.

  Lemma schedule_policy_focused_step_equ n (v : pool E B (S n)) (i : Fin.t (S n)) t (st : sched_state sch) :
    observe (v $ i) = StepF t ->
    schedule_policy sch (S n) v (Some i) st
      ≅ Step (schedule_policy sch (S n) ((v @ i := t)) (Some i) st).
  Proof. intro Hobs; apply (observe_equ_go _ _ (schedule_policy_focused_step sch n v i t st Hobs)). Qed.

  Lemma schedule_policy_focused_br_equ n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k (st : sched_state sch) :
    observe (v $ i) = BrF c k ->
    schedule_policy sch (S n) v (Some i) st
      ≅ Br c (fun j => schedule_policy sch (S n) ((v @ i := k j)) (Some i) st).
  Proof. intro Hobs; apply (observe_equ_go _ _ (schedule_policy_focused_br sch n v i c k st Hobs)). Qed.

  Lemma schedule_policy_focused_yield_equ n (v : pool E B (S n)) i k st :
    observe (v $ i) = VisF (inl1 Yield) k ->
    schedule_policy sch (S n) v (Some i) st ≅
      Guard (schedule_policy sch (S n) (v @ i := k tt) None st).
  Proof. intro H; apply observe_equ_go, schedule_policy_focused_yield, H. Qed.

  Lemma schedule_policy_focused_fork_equ n (v : pool E B (S n)) i k st :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    schedule_policy sch (S n) v (Some i) st ≅
      Guard (schedule_policy sch (S (S n)) (k true :: (v @ i := k false)) (Some (Fin.FS i)) st).
  Proof. intro H; apply observe_equ_go, schedule_policy_focused_fork, H. Qed.

  Lemma schedule_policy_focused_user_event_equ n (v : pool E B (S n)) i {Y} (e : E Y) k st :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    schedule_policy sch (S n) v (Some i) st ≅
      Vis (inl1 e) (fun x => schedule_policy sch (S n) (v @ i := k x) (Some i) st).
  Proof. intro H; apply observe_equ_go, schedule_policy_focused_user_event, H. Qed.
  Lemma schedule_policy_no_focus_equ n (v : pool E B (S n)) st :
    schedule_policy sch (S n) v None st ≅
    match sched_arity sch n st as a return
              (Fin.t (S a) -> Fin.t (S n) * sched_state sch) -> completed E B with
            | 0 => fun pick => let '(i, st') := pick Fin.F1 in
                Vis (inr1 (Scheduled (slot_index i)))
                  (fun _ => schedule_policy sch (S n) v (Some i) st')
            | S a => fun pick => Br (subevent _ (branchn (S (S a))))
                (fun x => let '(i, st') := pick x in
                  Vis (inr1 (Scheduled (slot_index i)))
                    (fun _ => schedule_policy sch (S n) v (Some i) st'))
            end (sched_pick sch n st).
  Proof. rewrite unfold_schedule_policy; reflexivity. Qed.

  Lemma schedule_policy_select_bisim n (v : pool E B (S n)) st :
    schedule_policy sch (S n) v None st ~
      Br (subevent _ (branchn (S (sched_arity sch n st))))
        (fun a => let '(i, st') := sched_pick sch n st a in
          Vis (inr1 (Scheduled (slot_index i)))
            (fun _ => schedule_policy sch (S n) v (Some i) st')).
  Proof.
    rewrite schedule_policy_no_focus_equ.
    generalize (sched_pick sch n st); destruct (sched_arity sch n st) as [|a]; intro pick; cbn.
    - symmetry; apply sb_br_l with (y := Fin.F1); intro x.
      assert (Hx : x = Fin.F1) by (dependent destruction x; [reflexivity|inversion x]).
      now subst x.
    - reflexivity.
  Qed.
  Lemma schedule_policy_no_focus_observe n (v : pool E B (S n)) st :
    observe (schedule_policy sch (S n) v None st) =
    observe (match sched_arity sch n st as a return
              (Fin.t (S a) -> Fin.t (S n) * sched_state sch) -> completed E B with
            | 0 => fun pick => let '(i, st') := pick Fin.F1 in
                Vis (inr1 (Scheduled (slot_index i)))
                  (fun _ => schedule_policy sch (S n) v (Some i) st')
            | S a => fun pick => Br (subevent _ (branchn (S (S a))))
                (fun x => let '(i, st') := pick x in
                  Vis (inr1 (Scheduled (slot_index i)))
                    (fun _ => schedule_policy sch (S n) v (Some i) st'))
            end (sched_pick sch n st)).
  Proof. reflexivity. Qed.
  Lemma schedule_policy_pool_proper n (v w : pool E B n) focus (st : sched_state sch) :
    pool_equ v w ->
    schedule_policy sch n v focus st ≅ schedule_policy sch n w focus st.
  Proof.
    revert n v w focus st.
    __coinduction_equ R CH.
    intros n v w focus st Hvw.
    destruct focus as [i |].
    - destruct n as [| n']; [ inversion i |].
      pose proof (Hvw i) as Hi.
      assert (Hgo : go (observe (v $ i)) ≅ go (observe (w $ i))).
      { rewrite <- !ctree_eta. exact Hi. }
      rewrite (ctree_eta (schedule_policy sch (S n') v (Some i) st)).
      rewrite (ctree_eta (schedule_policy sch (S n') w (Some i) st)).
      destruct (observe (v $ i)) as [r | | t | g | Y e k | Y c k] eqn:Hv;
      destruct (observe (w $ i)) as [r2 | | t2 | g2 | Y2 e2 k2 | Y2 c2 k2] eqn:Hw;
        try (step in Hgo; cbn in Hgo; inversion Hgo; fail).
      + destruct r, r2.
        rewrite (schedule_policy_focused_ret sch n' v i st Hv).
        rewrite (schedule_policy_focused_ret sch n' w i st Hw).
        cbn. constructor. apply CH. apply remove_pool_equ. exact Hvw.
      + rewrite (schedule_policy_focused_stuck sch n' v i st Hv).
        rewrite (schedule_policy_focused_stuck sch n' w i st Hw).
        cbn. constructor.
      + apply equ_step_inv in Hgo.
        rewrite (schedule_policy_focused_step sch n' v i t st Hv).
        rewrite (schedule_policy_focused_step sch n' w i t2 st Hw).
        cbn. constructor. apply CH.
        apply replace_pool_equ. exact Hvw. exact Hgo.
      + apply equ_guard_inv in Hgo.
        rewrite (schedule_policy_focused_guard sch n' v i g st Hv).
        rewrite (schedule_policy_focused_guard sch n' w i g2 st Hw).
        cbn. constructor. apply CH.
        apply replace_pool_equ. exact Hvw. exact Hgo.
      + pose proof (equ_vis_invT _ _ _ _ Hgo) as HY; subst Y2.
        pose proof (equ_vis_invE _ _ _ _ Hgo) as [He Hke]; subst e2.
        destruct e as [yld | [frk | usr]].
        * destruct yld.
          rewrite (schedule_policy_focused_yield sch n' v i k st Hv).
          rewrite (schedule_policy_focused_yield sch n' w i k2 st Hw).
          cbn. constructor. apply CH.
          apply replace_pool_equ. exact Hvw. apply (Hke tt).
        * destruct frk.
          rewrite (schedule_policy_focused_fork sch n' v i k st Hv).
          rewrite (schedule_policy_focused_fork sch n' w i k2 st Hw).
          cbn. constructor. apply CH.
          apply cons_pool_equ.
          -- apply (Hke true).
          -- apply replace_pool_equ. exact Hvw. apply (Hke false).
        * rewrite (schedule_policy_focused_user_event sch n' v i usr k st Hv).
          rewrite (schedule_policy_focused_user_event sch n' w i usr k2 st Hw).
          cbn. constructor. intro x. apply CH.
          apply replace_pool_equ. exact Hvw. apply (Hke x).
      + pose proof (equ_br_invT _ _ _ _ Hgo) as HY; subst Y2.
        pose proof (equ_br_invE _ _ _ _ Hgo) as [Hc Hke]; subst c2.
        rewrite (schedule_policy_focused_br sch n' v i c k st Hv).
        rewrite (schedule_policy_focused_br sch n' w i c k2 st Hw).
        cbn. constructor. intro j. apply CH.
        apply replace_pool_equ. exact Hvw. apply Hke.
    - destruct n as [| n'].
      + rewrite (ctree_eta (schedule_policy sch 0 v None st)).
        rewrite (ctree_eta (schedule_policy sch 0 w None st)).
        rewrite !schedule_policy_empty_none.
        cbn. reflexivity.
      + rewrite (ctree_eta (schedule_policy sch (S n') v None st)).
        rewrite (ctree_eta (schedule_policy sch (S n') w None st)).
        rewrite (schedule_policy_no_focus_observe n' v st), (schedule_policy_no_focus_observe n' w st).
        generalize (sched_pick sch n' st).
        destruct (sched_arity sch n' st) as [|a]; intros pick; cbn.
        * destruct (pick Fin.F1) as [i st']; cbn.
          constructor; intros []; apply CH; exact Hvw.
        * constructor; intro x; destruct (pick x) as [i st']; cbn.
          step; constructor; intros []; apply CH; exact Hvw.
  Qed.
  Lemma schedule_policy_some_pool_equ {m} (v w : pool E B (S m)) (i : Fin.t (S m)) st :
    pool_equ v w ->
    schedule_policy sch (S m) v (Some i) st ≅ schedule_policy sch (S m) w (Some i) st.
  Proof. apply schedule_policy_pool_proper. Qed.
  Lemma pool_equ_refl {n} (v : pool E B n) : pool_equ v v.
  Proof. intro j; reflexivity. Qed.

  Lemma replace_pool_idem_equ {n} (v : pool E B (S n)) (i : Fin.t (S n))
        (a b : thread E B) :
    pool_equ (v @ i := b) ((v @ i := a) @ i := b).
  Proof. rewrite Vector.replace_replace_eq. apply pool_equ_refl. Qed.
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

  Lemma trans_schedule_policy_no_focus_nonempty n (v : pool E B (S n)) st
      (a : Fin.t (S (sched_arity sch n st))) :
    let '(i, st') := sched_pick sch n st a in
    trans (obs (inr1 (Scheduled (slot_index i))) tt)
      (schedule_policy sch (S n) v None st)
      (schedule_policy sch (S n) v (Some i) st').
  Proof.
    destruct (sched_pick sch n st a) as [i st'] eqn:Hp.
    rewrite schedule_policy_no_focus_equ.
    revert a Hp; generalize (sched_pick sch n st).
    destruct (sched_arity sch n st) as [|arity]; intros pick a Hp.
    - assert (a = Fin.F1) by (dependent destruction a; [reflexivity|inversion a]).
      subst a; rewrite Hp; apply (trans_vis (inr1 (Scheduled (slot_index i))) tt).
    - eapply trans_br with (x := a); [|rewrite Hp; reflexivity].
      apply (trans_vis (inr1 (Scheduled (slot_index i))) tt).
  Qed.

  Lemma trans_schedule_policy_no_focus_inv n (v : pool E B (S n)) st l q :
    trans l (schedule_policy sch (S n) v None st) q ->
    exists a, let '(i, st') := sched_pick sch n st a in
      l = obs (inr1 (Scheduled (slot_index i))) tt /\
      q ≅ schedule_policy sch (S n) v (Some i) st'.
  Proof.
    rewrite schedule_policy_no_focus_equ.
    generalize (sched_pick sch n st).
    destruct (sched_arity sch n st) as [|arity]; intros pick TR.
    - destruct (pick Fin.F1) as [i st'] eqn:Hp.
      apply trans_vis_inv in TR as (x & Eq & L); destruct x.
      exists Fin.F1; rewrite Hp; auto.
    - apply trans_br_inv in TR as (a & TR).
      destruct (pick a) as [i st'] eqn:Hp.
      apply trans_vis_inv in TR as (x & Eq & L); destruct x.
      exists a; rewrite Hp; auto.
  Qed.

  Section FixedState.
    Context (st : sched_state sch).
  Lemma trans_schedule_policy_focused_user_event
        n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (e : E Y) k x :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    trans (obs (inl1 e : (E +' schedE) Y) x)
      (schedule_policy sch (S n) v (Some i) st)
      (schedule_policy sch (S n) ((v @ i := (k x))) (Some i) st).
  Proof.
    intro Hobs.
    rewrite (observe_equ_go _ _ (schedule_policy_focused_user_event sch n v i e k st Hobs)).
    apply (trans_vis (inl1 e : (E +' schedE) Y) x).
  Qed.

  (** A visible step of the focused thread is a [τ] step of the scheduler. *)
  Lemma trans_schedule_policy_focused_step n (v : pool E B (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = StepF t ->
    trans τ (schedule_policy sch (S n) v (Some i) st) (schedule_policy sch (S n) ((v @ i := t)) (Some i) st).
  Proof.
    intro Hobs.
    rewrite (schedule_policy_focused_step_equ n v i t st Hobs).
    apply trans_step.
  Qed.

  (** A hidden branch of the focused thread is crawled by the scheduler. *)
  Lemma trans_schedule_policy_focused_br
        n (v : pool E B (S n)) (i : Fin.t (S n)) {Y} (c : B Y) k (j : Y) l u :
    observe (v $ i) = BrF c k ->
    trans l (schedule_policy sch (S n) ((v @ i := (k j))) (Some i) st) u ->
    trans l (schedule_policy sch (S n) v (Some i) st) u.
  Proof.
    intros Hobs TR.
    rewrite (schedule_policy_focused_br_equ n v i c k st Hobs).
    eapply trans_br with (x := j); [exact TR | reflexivity].
  Qed.
  Lemma schedule_lift_yield n (v : pool E B (S n)) (i : Fin.t (S n))
        (u : thread E B) :
    trans (obs Yield_ tt) (v $ i) u ->
    forall l q,
      trans l (schedule_policy sch (S n) (v @ i := u) None st) q ->
      trans l (schedule_policy sch (S n) v (Some i) st) q.
  Proof.
    intro TR.
    rewrite <- trans__trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (obs Yield_ tt) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR as [Y c x k l t TR IH | t t' l TR IH | t w Equ | Y e k x t Equ | r];
      intros v i u Hot Hou Hlbl lq q Tq.
    - (* Transbr *)
      apply (trans_schedule_policy_focused_br n v i c k x); [now symmetry |].
      specialize (IH (v @ i := k x) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl lq q).
      rewrite Vector.replace_replace_eq in IH; exact (IH Tq).
    - (* Transguard *)
      rewrite (schedule_policy_focused_guard_equ n v i t st (eq_sym Hot)).
      apply trans_guard.
      specialize (IH (v @ i := t) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl lq q).
      rewrite Vector.replace_replace_eq in IH; exact (IH Tq).
    - discriminate Hlbl.
    - (* Transobs *)
      dependent destruction Hlbl.
      assert (Hu : u ≅ k tt).
      { transitivity t.
        - rewrite (ctree_eta u), (ctree_eta t), <- Hou; reflexivity.
        - symmetry; assumption. }
      rewrite (schedule_policy_focused_yield_equ n v i k st (eq_sym Hot)).
      apply trans_guard.
      rewrite <- (schedule_policy_pool_proper (S n) (v @ i := u) (v @ i := k tt) None st
        (replace_pool_equ v v i u (k tt) (pool_equ_refl v) Hu)).
      exact Tq.
    - discriminate Hlbl.
  Qed.
  Lemma schedule_lift_user n (v : pool E B (S n)) (i : Fin.t (S n))
        {Y} (e : E Y) (x : Y) (u : thread E B) :
    trans (obs (inr1 (inr1 e) : (yieldE +' (forkE +' E)) Y) x) (v $ i) u ->
    trans (obs (inl1 e : (E +' schedE) Y) x)
      (schedule_policy sch (S n) v (Some i) st)
      (schedule_policy sch (S n) ((v @ i := u)) (Some i) st).
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
      apply (trans_schedule_policy_focused_br n v i c k x0); [now symmetry |].
      specialize (IH (v @ i := k x0) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite Vector.replace_replace_eq in IH; exact IH.
    - (* Transguard *)
      rewrite (schedule_policy_focused_guard_equ n v i t st (eq_sym Hot)).
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
      rewrite (schedule_policy_some_pool_equ ((v @ i := u)) ((v @ i := (k x))) i st
                 (replace_pool_equ v v i u (k x) (pool_equ_refl v) Hu)).
      apply (trans_schedule_policy_focused_user_event n v i e k x (eq_sym Hot)).
    - discriminate Hlbl.
  Qed.

  Lemma schedule_lift_tau n (v : pool E B (S n)) (i : Fin.t (S n))
        (u : thread E B) :
    trans τ (v $ i) u ->
    trans τ
      (schedule_policy sch (S n) v (Some i) st)
      (schedule_policy sch (S n) ((v @ i := u)) (Some i) st).
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
      apply (trans_schedule_policy_focused_br n v i c k x); [now symmetry |].
      specialize (IH (v @ i := k x) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite Vector.replace_replace_eq in IH; exact IH.
    - (* Transguard *)
      rewrite (schedule_policy_focused_guard_equ n v i t st (eq_sym Hot)).
      apply trans_guard.
      specialize (IH (v @ i := t) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite Vector.replace_replace_eq in IH; exact IH.
    - (* Transtau *)
      assert (Hu : u ≅ t).
      { transitivity w.
        - rewrite (ctree_eta u), (ctree_eta w), <- Hou; reflexivity.
        - assumption. }
      rewrite (schedule_policy_some_pool_equ ((v @ i := u)) ((v @ i := t)) i st
                 (replace_pool_equ v v i u t (pool_equ_refl v) Hu)).
      apply (trans_schedule_policy_focused_step n v i t (eq_sym Hot)).
    - discriminate Hlbl.
    - discriminate Hlbl.
  Qed.
  Lemma schedule_lift_fork n (v : pool E B (S n)) (i : Fin.t (S n))
        (b : bool) (u : thread E B) :
    trans (obs Fork_ b) (v $ i) u ->
    exists k2,
      (forall c : bool, trans (obs Fork_ c) (v $ i) (k2 c)) /\
      (forall l q,
        trans l (schedule_policy sch (S (S n))
          (k2 true :: (v @ i := k2 false)) (Some (Fin.FS i)) st) q ->
        trans l (schedule_policy sch (S n) v (Some i) st) q).
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
      + intros l' q Tq; apply (trans_schedule_policy_focused_br n v i c k x); [now symmetry|now apply Hstep].
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
      + intros l' q Tq; rewrite (schedule_policy_focused_guard_equ n v i t st (eq_sym Hot)).
        apply trans_guard; now apply Hstep.
    - discriminate Hlbl.
    - (* Transobs *)
      dependent destruction Hlbl.
      exists k. split.
      + intro c.
        rewrite (ctree_eta (v $ i)), <- Hot.
        apply trans_vis.
      + intros l' q Tq; rewrite (schedule_policy_focused_fork_equ n v i k st (eq_sym Hot)).
        now apply trans_guard.
    - discriminate Hlbl.
  Qed.
  Lemma schedule_lift_ret n (v : pool E B (S n)) (i : Fin.t (S n))
        (u : thread E B) :
    trans (val tt : @label (yieldE +' (forkE +' E))) (v $ i) u ->
    forall l t',
      trans l (schedule_policy sch n ((v -- i)) None st) t' ->
      trans l (schedule_policy sch (S n) v (Some i) st) t'.
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
      apply (trans_schedule_policy_focused_br n v i c k x); [now symmetry |].
      apply (IH (v @ i := k x) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite (schedule_policy_pool_proper n _ _ None st (remove_replace_pool_equ v i (k x))).
      exact TR'.
    - (* Transguard *)
      rewrite (schedule_policy_focused_guard_equ n v i t st (eq_sym Hot)).
      apply trans_guard.
      apply (IH (v @ i := t) i u ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      rewrite (schedule_policy_pool_proper n _ _ None st (remove_replace_pool_equ v i t)).
      exact TR'.
    - discriminate Hlbl.
    - discriminate Hlbl.
    - (* Transval *)
      dependent destruction Hlbl.
      rewrite (schedule_policy_focused_ret_equ n v i st (eq_sym Hot)).
      apply trans_guard. exact TR'.
  Qed.
  End FixedState.

  Abbreviation completed' := (completed E B).
  Abbreviation sbC := (@sb (E +' schedE) (E +' schedE) B B unit unit eq).

  (** Exact phase shapes support induction on [trans_].  The public local
      invariant below closes these shapes under structural equality, so a
      hidden boundary choice and its selected child remain distinct phases. *)
  Inductive schedule_sb_shape : completed' -> completed' -> Prop :=
  | shape_at n (v w : pool E B n) f st :
      pool_branchfree v -> pool_branchfree w -> pool_sbisim v w ->
      schedule_sb_shape (schedule_policy sch n v f st) (schedule_policy sch n w f st)
  | shape_choice n a (v w : pool E B (S n))
      (pick : Fin.t (S (S a)) -> Fin.t (S n) * sched_state sch) :
      pool_branchfree v -> pool_branchfree w -> pool_sbisim v w ->
      schedule_sb_shape
        (Br (subevent _ (branchn (S (S a)))) (fun x => let '(i,s) := pick x in
          Vis (inr1 (Scheduled (slot_index i))) (fun _ => schedule_policy sch (S n) v (Some i) s)))
        (Br (subevent _ (branchn (S (S a)))) (fun x => let '(i,s) := pick x in
          Vis (inr1 (Scheduled (slot_index i))) (fun _ => schedule_policy sch (S n) w (Some i) s)))
  | shape_selected n (v w : pool E B (S n)) i st :
      pool_branchfree v -> pool_branchfree w -> pool_sbisim v w ->
      schedule_sb_shape
        (Vis (inr1 (Scheduled (slot_index i))) (fun _ => schedule_policy sch (S n) v (Some i) st))
        (Vis (inr1 (Scheduled (slot_index i))) (fun _ => schedule_policy sch (S n) w (Some i) st)).

  Inductive schedule_sb_phase : completed' -> completed' -> Prop :=
  | sb_phase_at n (v w : pool E B n) f st T U :
      pool_branchfree v -> pool_branchfree w -> pool_sbisim v w ->
      T ≅ schedule_policy sch n v f st -> U ≅ schedule_policy sch n w f st ->
      schedule_sb_phase T U
  | sb_phase_choice n a (v w : pool E B (S n))
      (pick : Fin.t (S (S a)) -> Fin.t (S n) * sched_state sch) T U :
      pool_branchfree v -> pool_branchfree w -> pool_sbisim v w ->
      T ≅ Br (subevent _ (branchn (S (S a)))) (fun x => let '(i,s) := pick x in
        Vis (inr1 (Scheduled (slot_index i))) (fun _ => schedule_policy sch (S n) v (Some i) s)) ->
      U ≅ Br (subevent _ (branchn (S (S a)))) (fun x => let '(i,s) := pick x in
        Vis (inr1 (Scheduled (slot_index i))) (fun _ => schedule_policy sch (S n) w (Some i) s)) ->
      schedule_sb_phase T U
  | sb_phase_selected n (v w : pool E B (S n)) i st T U :
      pool_branchfree v -> pool_branchfree w -> pool_sbisim v w ->
      T ≅ Vis (inr1 (Scheduled (slot_index i))) (fun _ => schedule_policy sch (S n) v (Some i) st) ->
      U ≅ Vis (inr1 (Scheduled (slot_index i))) (fun _ => schedule_policy sch (S n) w (Some i) st) ->
      schedule_sb_phase T U.
  Local Ltac branchfree_absurd Hbf Hvi :=
    exfalso; let Hb := fresh "Hb" in
    pose proof Hbf as Hb; apply branchfree_unfold in Hb; rewrite Hvi in Hb; inversion Hb.

  (** Dispatch the head of the focused thread against a scheduler head
      ([Hos : <head> = observe (schedule (S n') v1 (Some i))]); impossible
      pairings are discharged, the remaining goals are in thread-head order. *)
  Local Ltac focused_heads st v1 i Hos Hbf Hvi :=
    destruct (observe (v1 $ i)) as [[] | | t0 | g | Y0 e0 k0 | Y0 c0 k0] eqn:Hvi;
    [ rewrite (schedule_policy_focused_ret sch _ v1 i st Hvi) in Hos
    | rewrite (schedule_policy_focused_stuck sch _ v1 i st Hvi) in Hos
    | rewrite (schedule_policy_focused_step sch _ v1 i _ st Hvi) in Hos
    | rewrite (schedule_policy_focused_guard sch _ v1 i _ st Hvi) in Hos
    | destruct e0 as [y | [f | usr]];
      [ dependent destruction y; rewrite (schedule_policy_focused_yield sch _ v1 i _ st Hvi) in Hos
      | dependent destruction f; rewrite (schedule_policy_focused_fork sch _ v1 i _ st Hvi) in Hos
      | rewrite (schedule_policy_focused_user_event sch _ v1 i usr _ st Hvi) in Hos ]
    | branchfree_absurd (Hbf i) Hvi ];
    try discriminate Hos.
  Lemma schedule_sb_shape_match {R : Chain sbC}
    (Hch : forall n (v w : pool E B n) f st,
      pool_branchfree v -> pool_branchfree w -> pool_sbisim v w ->
      `R (schedule_policy sch n v f st) (schedule_policy sch n w f st)) :
    forall l os ot', trans_ l os ot' ->
    forall t u t', os = observe t -> ot' = observe t' ->
      schedule_sb_shape t u -> exists u', trans l u u' /\ `R t' u'.
  Proof.
    intros l os ot' TR.
    induction TR as [Y c x k l t TR IHTR | t t2 l TR IHTR | t w Equ | Y e k x t Equ | r];
      intros left right t' Hos Hot' HP;
      destruct HP as [nn v1 v2 focus st Hbf1 Hbf2 Hpool
        |nn a v1 v2 pick Hbf1 Hbf2 Hpool
        |nn v1 v2 i st Hbf1 Hbf2 Hpool].
    - destruct focus as [i|].
      + destruct nn as [|n']; [inversion i|].
        focused_heads st v1 i Hos Hbf1 Hvi.
      + destruct nn as [|n'].
        * rewrite (schedule_policy_empty_none sch v1 st) in Hos; discriminate Hos.
        * rewrite (schedule_policy_no_focus_observe n' v1 st) in Hos.
          setoid_rewrite (schedule_policy_no_focus_equ n' v2 st).
          revert Hos; generalize (sched_pick sch n' st).
          destruct (sched_arity sch n' st) as [|a]; intros pick Hos.
          -- destruct (pick Fin.F1) as [i st']; discriminate Hos.
          -- cbn in Hos; dependent destruction Hos.
             destruct (pick x) as [i st'] eqn:Hp.
             destruct (IHTR _ _ t' eq_refl eq_refl
               (shape_selected n' v1 v2 i st' Hbf1 Hbf2 Hpool)) as (u' & Tu & Hu).
             exists u'; split; [eapply trans_br with (x:=x); [exact Tu|rewrite Hp; reflexivity]|exact Hu].
    - cbn in Hos; dependent destruction Hos.
      destruct (pick x) as [i st'] eqn:Hp.
      destruct (IHTR _ _ t' eq_refl Hot'
        (shape_selected nn v1 v2 i st' Hbf1 Hbf2 Hpool)) as (u' & Tu & Hu).
      exists u'; split; [eapply trans_br with (x:=x); [exact Tu|rewrite Hp; reflexivity]|exact Hu].
    - discriminate Hos.
    - destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        focused_heads st v1 i Hos Hbf1 Hvi.
        * (* Ret: recurse on the smaller pool *)
          injection Hos as ->.
          destruct (IHTR _ _ t' eq_refl Hot'
                    (shape_at n' (v1 -- i) (v2 -- i) None st
                      (pool_branchfree_remove v1 i Hbf1)
                      (pool_branchfree_remove v2 i Hbf2)
                      (remove_pool_sbisim v1 v2 i Hpool)))
            as (u' & Htru & Hresu).
          assert (Hvr : (v1 $ i) ≅ Ret tt).
          { rewrite (ctree_eta (v1 $ i)), Hvi. reflexivity. }
          assert (Htrv : trans (val tt : @label (yieldE +' (forkE +' E)))
                           (v1 $ i) Stuck).
          { rewrite Hvr. apply trans_ret. }
          destruct (sbisim_trans_l _ _ _ _ (Hpool i) Htrv) as (uv & Htr2v & _).
          exists u'. split; [| exact Hresu].
          exact (schedule_lift_ret st n' v2 i uv Htr2v l u' Htru).
        * (* Guard: recurse on the same pool, focus unchanged *)
          injection Hos as ->.
          assert (Hbg : BranchFree g).
          { pose proof (Hbf1 i) as Hb; apply branchfree_unfold in Hb;
              rewrite Hvi in Hb; now inversion Hb. }
          eapply IHTR; [reflexivity|exact Hot'|].
          apply (shape_at (S n') (v1 @ i := g) v2 (Some i) st
            (pool_branchfree_replace v1 i g Hbf1 Hbg) Hbf2).
          intro j. destruct (Fin.eq_dec i j) as [Hij | Hij].
          -- subst j.
             rewrite Vector.nth_replace_eq.
             assert (Hvg : (v1 $ i) ≅ Guard g).
             { rewrite (ctree_eta (v1 $ i)), Hvi. reflexivity. }
             transitivity (v1 $ i); [| apply Hpool].
             rewrite Hvg. symmetry. apply sb_guard.
          -- rewrite Vector.nth_replace_neq by congruence. apply Hpool.
        * (* Yield consumes the source event without introducing a transition. *)
          injection Hos as ->.
          assert (Hy : trans (obs Yield_ tt) (v1 $ i) (k0 tt)).
          { rewrite (ctree_eta (v1 $ i)), Hvi; apply trans_vis. }
          destruct (sbisim_trans_l _ _ _ _ (Hpool i) Hy) as (uy & Ty & Sy).
          assert (B1 : BranchFree (k0 tt)) by (exact (branchfree_trans _ _ _ (Hbf1 i) Hy)).
          assert (B2 : BranchFree uy) by (exact (branchfree_trans _ _ _ (Hbf2 i) Ty)).
          destruct (IHTR _ _ t' eq_refl Hot'
            (shape_at (S n') (v1 @ i := k0 tt) (v2 @ i := uy) None st
              (pool_branchfree_replace v1 i _ Hbf1 B1)
              (pool_branchfree_replace v2 i _ Hbf2 B2)
              (replace_pool_sbisim v1 v2 i _ _ Hpool Sy))) as (u' & Tu & Hu).
          exists u'; split; [eapply schedule_lift_yield; eassumption|exact Hu].
        * (* Both fork answers are reconstructed at the same source node. *)
          injection Hos as ->.
          assert (Hvis : (v1 $ i) ≅ Vis Fork_ k0).
          { rewrite (ctree_eta (v1 $ i)), Hvi; reflexivity. }
          assert (Tf : trans (obs Fork_ false) (v1 $ i) (k0 false)).
          { rewrite Hvis; apply trans_vis. }
          destruct (sbisim_trans_l _ _ _ _ (Hpool i) Tf) as (uf & Tf2 & Sf).
          destruct (schedule_lift_fork st n' v2 i false uf Tf2) as (kf & Tforall & Tlift).
          assert (Sk : forall c, k0 c ~ kf c).
          { intro c; destruct (sbisim_trans_l _ _ _ _
              (ltac:(symmetry; apply Hpool) : (v2 $ i) ~ (v1 $ i)) (Tforall c))
              as (wc & Tc & Sc).
            rewrite Hvis in Tc; apply trans_vis_inv in Tc as (y & Ey & Ly).
            apply obs_eq_inv in Ly as [_ <-]. rewrite Ey in Sc; symmetry; exact Sc. }
          assert (B1 : forall c, BranchFree (k0 c)).
          { intro c; eapply branchfree_trans; [apply Hbf1|rewrite Hvis; apply trans_vis]. }
          assert (B2 : forall c, BranchFree (kf c)).
          { intro c; eapply branchfree_trans; [apply Hbf2|apply Tforall]. }
          destruct (IHTR _ _ t' eq_refl Hot'
            (shape_at (S (S n')) (k0 true :: (v1 @ i := k0 false))
              (kf true :: (v2 @ i := kf false)) (Some (Fin.FS i)) st
              (pool_branchfree_cons _ _ (B1 true) (pool_branchfree_replace _ _ _ Hbf1 (B1 false)))
              (pool_branchfree_cons _ _ (B2 true) (pool_branchfree_replace _ _ _ Hbf2 (B2 false)))
              (cons_pool_sbisim _ _ _ _ (Sk true) (replace_pool_sbisim _ _ _ _ _ Hpool (Sk false)))))
            as (u' & Tu & Hu).
          exists u'; split; [now apply Tlift|exact Hu].
      + destruct nn as [|n'].
        * rewrite (schedule_policy_empty_none sch v1 st) in Hos; discriminate Hos.
        * rewrite (schedule_policy_no_focus_observe n' v1 st) in Hos.
          revert Hos; generalize (sched_pick sch n' st).
          destruct (sched_arity sch n' st) as [|a]; intros pick Hos;
            [destruct (pick Fin.F1) as [i st']|]; discriminate Hos.
    - discriminate Hos.
    - discriminate Hos.
    - destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        focused_heads st v1 i Hos Hbf1 Hvi.
        injection Hos as ->.
        assert (Htr1 : trans τ (v1 $ i) t0).
        { rewrite (ctree_eta (v1 $ i)), Hvi. apply trans_step. }
        destruct (sbisim_trans_l _ _ _ _ (Hpool i) Htr1) as (u' & Htr2 & Hsb).
        assert (Hbt : BranchFree t0).
        { pose proof (Hbf1 i) as Hb; apply branchfree_unfold in Hb;
            rewrite Hvi in Hb; now inversion Hb. }
        exists (schedule_policy sch (S n') ((v2 @ i := u')) (Some i) st). split.
        * apply schedule_lift_tau. exact Htr2.
        * assert (Ht' : t' ≅ schedule_policy sch (S n') ((v1 @ i := t0)) (Some i) st).
          { rewrite (ctree_eta t'), <- Hot', <- (ctree_eta w). assumption. }
          rewrite Ht'. apply Hch.
          -- apply pool_branchfree_replace; assumption.
          -- apply pool_branchfree_replace; [assumption |].
             exact (branchfree_trans _ _ _ (Hbf2 i) Htr2).
          -- apply replace_pool_sbisim; assumption.
      + destruct nn as [|n'].
        * rewrite (schedule_policy_empty_none sch v1 st) in Hos; discriminate Hos.
        * rewrite (schedule_policy_no_focus_observe n' v1 st) in Hos.
          revert Hos; generalize (sched_pick sch n' st).
          destruct (sched_arity sch n' st) as [|a]; intros pick Hos;
            [destruct (pick Fin.F1) as [i st']|]; discriminate Hos.
    - discriminate Hos.
    - discriminate Hos.
    - destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        focused_heads st v1 i Hos Hbf1 Hvi.
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
          exists (schedule_policy sch (S n') ((v2 @ i := u')) (Some i) st). split.
          ++ apply (schedule_lift_user st n' v2 i usr x u' Htr2).
          ++ assert (Ht' : t' ≅ schedule_policy sch (S n') ((v1 @ i := (k0 x))) (Some i) st).
             { rewrite (ctree_eta t'), <- Hot', <- (ctree_eta t).
               symmetry; assumption. }
             rewrite Ht'. apply Hch.
             ** apply pool_branchfree_replace; assumption.
             ** apply pool_branchfree_replace; [assumption |].
                exact (branchfree_trans _ _ _ (Hbf2 i) Htr2).
             ** apply replace_pool_sbisim; assumption.
      + destruct nn as [|n'].
        * rewrite (schedule_policy_empty_none sch v1 st) in Hos; discriminate Hos.
        * rewrite (schedule_policy_no_focus_observe n' v1 st) in Hos.
          setoid_rewrite (schedule_policy_no_focus_equ n' v2 st).
          revert Hos; generalize (sched_pick sch n' st).
          destruct (sched_arity sch n' st) as [|a]; intros pick Hos; [|discriminate Hos].
          destruct (pick Fin.F1) as [i st'] eqn:Hp; cbn in Hos.
          dependent destruction Hos; destruct x.
          exists (schedule_policy sch (S n') v2 (Some i) st'); split.
          -- apply (trans_vis (inr1 (Scheduled (slot_index i))) tt).
          -- assert (Et : t' ≅ schedule_policy sch (S n') v1 (Some i) st').
             { rewrite (ctree_eta t'), <- Hot', <- (ctree_eta t); symmetry; assumption. }
             rewrite Et; apply Hch; assumption.
    - discriminate Hos.
    - dependent destruction Hos; destruct x.
      exists (schedule_policy sch (S nn) v2 (Some i) st); split.
      + apply (trans_vis (inr1 (Scheduled (slot_index i))) tt).
      + assert (Et : t' ≅ schedule_policy sch (S nn) v1 (Some i) st).
        { rewrite (ctree_eta t'), <- Hot', <- (ctree_eta t); symmetry; assumption. }
        rewrite Et; apply Hch; assumption.
    - destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        focused_heads st v1 i Hos Hbf1 Hvi.
      + destruct nn as [| n'].
        * rewrite (schedule_policy_empty_none sch v1 st) in Hos.
          inversion Hos; subst.
          exists Stuck. split.
          -- rewrite (schedule_policy_empty_equ v2 st). apply trans_ret.
          -- assert (Ht' : t' ≅ Stuck).
             { rewrite (ctree_eta t'), <- Hot'. reflexivity. }
             rewrite Ht'. reflexivity.
        * rewrite (schedule_policy_no_focus_observe n' v1 st) in Hos.
          revert Hos; generalize (sched_pick sch n' st).
          destruct (sched_arity sch n' st) as [|a]; intros pick Hos;
            [destruct (pick Fin.F1) as [i st']|]; discriminate Hos.
    - discriminate Hos.
    - discriminate Hos.
  Qed.
  Lemma schedule_sb_phase_match {R : Chain sbC}
    (Hch : forall n (v w : pool E B n) f st,
      pool_branchfree v -> pool_branchfree w -> pool_sbisim v w ->
      `R (schedule_policy sch n v f st) (schedule_policy sch n w f st))
    T U l q : schedule_sb_phase T U -> trans l T q ->
      exists u, trans l U u /\ `R q u.
  Proof.
    intros HP TR; destruct HP as
      [n v w f st T' U' Bv Bw P ET EU
      |n a v w pick T' U' Bv Bw P ET EU
      |n v w i st T' U' Bv Bw P ET EU].
    all: rewrite ET in TR; setoid_rewrite EU;
      eapply (schedule_sb_shape_match Hch _ _ _ TR);
      [reflexivity|reflexivity|constructor; assumption].
  Qed.

  Theorem sbisim_schedule_policy n (v1 v2 : pool E B n) focus st :
    pool_branchfree v1 -> pool_branchfree v2 -> pool_sbisim v1 v2 ->
    schedule_policy sch n v1 focus st ~ schedule_policy sch n v2 focus st.
  Proof.
    revert n v1 v2 focus st.
    unfold sbisim; coinduction R CH.
    intros n v1 v2 focus st B1 B2 P; split; intros l q TR.
    - destruct (schedule_sb_phase_match CH _ _ l q
        (sb_phase_at n v1 v2 focus st _ _ B1 B2 P ltac:(reflexivity) ltac:(reflexivity)) TR)
        as (u & Tu & Hu).
      exists l, u; split; [exact Tu|split; [exact Hu|reflexivity]].
    - destruct (schedule_sb_phase_match CH _ _ l q
        (sb_phase_at n v2 v1 focus st _ _ B2 B1 (pool_sbisim_sym _ _ P) ltac:(reflexivity) ltac:(reflexivity)) TR)
        as (u & Tu & Hu).
      exists l, u; split; [exact Tu|split; [unfold Basics.flip; symmetry; exact Hu|reflexivity]].
  Qed.
End SchedulerTransitions.

Section SchedulerSpecializations.
  Context {E B : Type -> Type} {HB : Bn -< B}.
  Lemma trans_schedule_empty_ret (v : pool E B 0) :
    schedule 0 v None ≅ Ret tt.
  Proof. apply (schedule_policy_empty_equ nd_scheduler v tt). Qed.

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

  Lemma schedule_no_focus_equ n (v : pool E B (S n)) :
    schedule (S n) v None ≅
      match n as m return pool E B (S m) -> completed E B with
      | 0 => fun v => Vis (inr1 (Scheduled 0))
          (fun _ => schedule 1 v (Some Fin.F1))
      | S m => fun v => Br (subevent _ (branchn (S (S m))))
          (fun i => Vis (inr1 (Scheduled (slot_index i)))
            (fun _ => schedule (S (S m)) v (Some i)))
      end v.
  Proof. destruct n; step; cbn; reflexivity. Qed.

  Lemma schedule_pool_proper n (v w : pool E B n) focus :
    pool_equ v w -> schedule n v focus ≅ schedule n w focus.
  Proof. apply (schedule_policy_pool_proper nd_scheduler n v w focus tt). Qed.

  Lemma schedule_rr_pool_proper n (v w : pool E B n) focus cursor :
    pool_equ v w -> schedule_rr n v focus cursor ≅ schedule_rr n w focus cursor.
  Proof. apply (schedule_policy_pool_proper rr_scheduler n v w focus cursor). Qed.

  Theorem sbisim_schedule n (v w : pool E B n) focus :
    pool_branchfree v -> pool_branchfree w -> pool_sbisim v w ->
    schedule n v focus ~ schedule n w focus.
  Proof. apply (sbisim_schedule_policy nd_scheduler n v w focus tt). Qed.

  Theorem sbisim_schedule_rr n (v w : pool E B n) focus cursor :
    pool_branchfree v -> pool_branchfree w -> pool_sbisim v w ->
    schedule_rr n v focus cursor ~ schedule_rr n w focus cursor.
  Proof. apply (sbisim_schedule_policy rr_scheduler n v w focus cursor). Qed.

  Lemma trans_schedule_focused_yield n (v : pool E B (S n)) i k l q :
    observe (v $ i) = VisF (inl1 Yield) k ->
    trans l (schedule (S n) (v @ i := k tt) None) q ->
    trans l (schedule (S n) v (Some i)) q.
  Proof. intros H TR; unfold schedule; rewrite (schedule_policy_focused_yield_equ nd_scheduler n v i k tt H); now apply trans_guard. Qed.

  Lemma trans_schedule_focused_fork n (v : pool E B (S n)) i k l q :
    observe (v $ i) = VisF (inr1 (inl1 Fork)) k ->
    trans l (schedule (S (S n)) (k true :: (v @ i := k false)) (Some (Fin.FS i))) q ->
    trans l (schedule (S n) v (Some i)) q.
  Proof. intros H TR; unfold schedule; rewrite (schedule_policy_focused_fork_equ nd_scheduler n v i k tt H); now apply trans_guard. Qed.

  Lemma trans_schedule_focused_user_event n (v : pool E B (S n)) i {Y} (e : E Y) k x :
    observe (v $ i) = VisF (inr1 (inr1 e)) k ->
    trans (obs (inl1 e : (E +' schedE) Y) x) (schedule (S n) v (Some i))
      (schedule (S n) (v @ i := k x) (Some i)).
  Proof. apply (trans_schedule_policy_focused_user_event nd_scheduler tt n v i e k x). Qed.

  Lemma trans_schedule_focused_step n (v : pool E B (S n)) i t :
    observe (v $ i) = StepF t ->
    trans τ (schedule (S n) v (Some i)) (schedule (S n) (v @ i := t) (Some i)).
  Proof. apply (trans_schedule_policy_focused_step nd_scheduler tt n v i t). Qed.

  Lemma trans_schedule_focused_br n (v : pool E B (S n)) i {Y} (c : B Y) k j l q :
    observe (v $ i) = BrF c k ->
    trans l (schedule (S n) (v @ i := k j) (Some i)) q ->
    trans l (schedule (S n) v (Some i)) q.
  Proof. apply (trans_schedule_policy_focused_br nd_scheduler tt n v i c k j l q). Qed.

  Lemma trans_schedule_no_focus_nonempty n (v : pool E B (S n)) (i : Fin.t (S n)) :
    trans (obs (inr1 (Scheduled (slot_index i))) tt) (schedule (S n) v None)
      (schedule (S n) v (Some i)).
  Proof. apply (trans_schedule_policy_no_focus_nonempty nd_scheduler n v tt i). Qed.

  Lemma trans_schedule_no_focus_inv n (v : pool E B (S n)) l q :
    trans l (schedule (S n) v None) q ->
    exists i, l = obs (inr1 (Scheduled (slot_index i))) tt /\ q ≅ schedule (S n) v (Some i).
  Proof. apply (trans_schedule_policy_no_focus_inv nd_scheduler n v tt l q). Qed.

  Lemma schedule_some_pool_equ {m} (v w : pool E B (S m)) i :
    pool_equ v w -> schedule (S m) v (Some i) ≅ schedule (S m) w (Some i).
  Proof. apply schedule_pool_proper. Qed.

  Lemma br_schedule_pool_equ {n} (v w : pool E B (S n)) :
    pool_equ v w ->
    brS (branchn (S n)) (fun j => schedule (S n) v (Some j)) ≅
    brS (branchn (S n)) (fun j => schedule (S n) w (Some j)).
  Proof. intro Hp; step; constructor; intro j; step; constructor; apply schedule_pool_proper, Hp. Qed.
End SchedulerSpecializations.
(** ** Instrumented scheduling respects [equ]-equal pools. *)
(** This is the bridge used to normalize a source denotation before applying a
    singleton scheduler rule: it transports [pool_equ] through the scheduled projection
    and through state instrumentation. *)
Lemma instr_schedule_pool_equ {Σ B} `{Bn -< B} n (v v' : pool (stateE Σ) B n) focus σ :
  pool_equ v v' ->
  instr_schedule n v focus σ ≅ instr_schedule n v' focus σ.
Proof.
  intro Hvv.
  unfold instr_schedule, instr_stateE.
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
    rewrite (interp_guard (C:=B) (D:=B) (h:=h)); apply guard_equ_node; exact IHn.
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
        * rewrite ET, Et, interp_guards, (interp_ret (C:=B) (D:=B) (h:=h)), <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, (interp_ret (C:=B) (D:=B) (h:=h)), <- guards_add; reflexivity.
      + apply (galignF_br _ T' U' (n + a) (m + b) c
          (fun i => Guard (interp' (kk i))) (fun i => Guard (interp' (kk' i)))).
        * rewrite ET, Et, interp_guards, (interp_br' (C:=B) (D:=B) (h:=h)), <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, (interp_br' (C:=B) (D:=B) (h:=h)), <- guards_add; reflexivity.
        * intro i; apply (interp_rel_tree 1 1 (kk i) (kk' i)); [apply Hk|reflexivity|reflexivity].
      + apply (interp_rel_bind_step (n + a) (m + b) _ (h _ e) kk kk' T' U' Hk).
        * rewrite ET, Et, interp_guards, (interp_vis (C:=B) (D:=B) (h:=h)), <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, (interp_vis (C:=B) (D:=B) (h:=h)), <- guards_add; reflexivity.
      + apply (galignF_stuck _ T' U' (n + a) (m + b)).
        * rewrite ET, Et, interp_guards, (interp_stuck (C:=B) (D:=B) (h:=h)), <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, (interp_stuck (C:=B) (D:=B) (h:=h)), <- guards_add; reflexivity.
      + apply (galignF_step _ T' U' (n + a) (m + b) (Guard (interp' t')) (Guard (interp' u'))).
        * rewrite ET, Et, interp_guards, (interp_step (C:=B) (D:=B) (h:=h)), <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, (interp_step (C:=B) (D:=B) (h:=h)), <- guards_add; reflexivity.
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

Section ScheduleAlign.
  Context {E B : Type -> Type} {HB : Bn -< B} (sch : Scheduler).
  Lemma schedule_policy_focus_guards : forall st a N (ts : pool E B (S N)) i (x : thread E B),
    (ts $ i) ≅ guards a x ->
    schedule_policy sch (S N) ts (Some i) st ≅ guards a (schedule_policy sch (S N) (ts @ i := x) (Some i) st).
  Proof.
    intros st; induction a as [|a IH]; intros N ts i x Hx; cbn [guards] in *.
    - apply (schedule_policy_pool_proper sch).
      intro j; destruct (Fin.eq_dec j i) as [->|Hne].
      + rewrite Vector.nth_replace_eq; exact Hx.
      + rewrite Vector.nth_replace_neq by congruence; reflexivity.
    - transitivity (schedule_policy sch (S N) (ts @ i := Guard (guards a x)) (Some i) st).
      { apply (schedule_policy_pool_proper sch).
        intro j; destruct (Fin.eq_dec j i) as [->|Hne].
        + rewrite Vector.nth_replace_eq; exact Hx.
        + rewrite Vector.nth_replace_neq by congruence; reflexivity. }
      rewrite (schedule_policy_focused_guard_equ sch N (ts @ i := Guard (guards a x)) i (guards a x) st
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
  | sched_rel_at n m N (ts us : pool E B N) f st T U :
      pool_guard_equ ts us ->
      T ≅ guards n (schedule_policy sch N ts f st) ->
      U ≅ guards m (schedule_policy sch N us f st) -> sched_rel T U
  | sched_rel_choice n m N a (ts us : pool E B (S N))
      (pick : Fin.t (S (S a)) -> Fin.t (S N) * sched_state sch) T U :
      pool_guard_equ ts us ->
      T ≅ guards n (Br (subevent _ (branchn (S (S a))))
        (fun x => let '(i, st') := pick x in Vis (inr1 (Scheduled (slot_index i)))
          (fun _ => schedule_policy sch (S N) ts (Some i) st'))) ->
      U ≅ guards m (Br (subevent _ (branchn (S (S a))))
        (fun x => let '(i, st') := pick x in Vis (inr1 (Scheduled (slot_index i)))
          (fun _ => schedule_policy sch (S N) us (Some i) st'))) -> sched_rel T U
  | sched_rel_selected n m N (ts us : pool E B (S N)) i st T U :
      pool_guard_equ ts us ->
      T ≅ guards n (Vis (inr1 (Scheduled (slot_index i)))
        (fun _ => schedule_policy sch (S N) ts (Some i) st)) ->
      U ≅ guards m (Vis (inr1 (Scheduled (slot_index i)))
        (fun _ => schedule_policy sch (S N) us (Some i) st)) -> sched_rel T U.

  Lemma sched_rel_step T U : sched_rel T U -> galignF sched_rel T U.
  Proof.
    intros [n m N ts us f st T' U' Hp ET EU
      |n m N a ts us pick T' U' Hp ET EU
      |n m N ts us i st T' U' Hp ET EU].
    2: { apply (galignF_br _ T' U' n m (subevent _ (branchn (S (S a))))
           (fun x => let '(i, st') := pick x in
             Vis (inr1 (Scheduled (slot_index i)))
               (fun _ => schedule_policy sch (S N) ts (Some i) st')) (fun x => let '(i, st') := pick x in
             Vis (inr1 (Scheduled (slot_index i)))
               (fun _ => schedule_policy sch (S N) us (Some i) st')));
           [exact ET|exact EU|].
         intro x; destruct (pick x) as [i st'];
           eapply (sched_rel_selected 0 0 N ts us i st'); [exact Hp|reflexivity|reflexivity]. }
    2: { eapply galignF_vis; [exact ET|exact EU|].
         intros []; eapply (sched_rel_at 0 0 (S N) ts us (Some i) st); [exact Hp|reflexivity|reflexivity]. }
    destruct f as [i|].
    2: { destruct N as [|N].
         - eapply galignF_ret.
           + rewrite ET, (schedule_policy_empty_equ sch); reflexivity.
           + rewrite EU, (schedule_policy_empty_equ sch); reflexivity.
         - rewrite (schedule_policy_no_focus_equ sch N ts st) in ET.
           rewrite (schedule_policy_no_focus_equ sch N us st) in EU.
           revert ET EU; generalize (sched_pick sch N st).
           destruct (sched_arity sch N st) as [|a]; intros pick ET EU.
           + destruct (pick Fin.F1) as [i st']; cbn in ET, EU.
             eapply galignF_vis; [exact ET|exact EU|].
             intros []; eapply (sched_rel_at 0 0 (S N) ts us (Some i) st'); [exact Hp|reflexivity|reflexivity].
           + apply (galignF_br _ T' U' n m (subevent _ (branchn (S (S a))))
               (fun x => let '(i, st') := pick x in
             Vis (inr1 (Scheduled (slot_index i)))
               (fun _ => schedule_policy sch (S N) ts (Some i) st')) (fun x => let '(i, st') := pick x in
             Vis (inr1 (Scheduled (slot_index i)))
               (fun _ => schedule_policy sch (S N) us (Some i) st')));
               [exact ET|exact EU|].
             intro x; destruct (pick x) as [i st'];
               eapply (sched_rel_selected 0 0 N ts us i st'); [exact Hp|reflexivity|reflexivity]. }
    destruct N as [|N]; [inversion i|].
    destruct (guard_equ_guards _ _ (Hp i)) as (a & b & x & Ea & Eb).
    pose proof (pool_guard_equ_replace ts us i x Hp) as Hp'.
    set (ts' := ts @ i := x) in *; set (us' := us @ i := x) in *.
    assert (ET' : T' ≅ guards (n + a) (schedule_policy sch (S N) ts' (Some i) st))
      by (rewrite ET, (schedule_policy_focus_guards st a N ts i x Ea), <- guards_add; reflexivity).
    assert (EU' : U' ≅ guards (m + b) (schedule_policy sch (S N) us' (Some i) st))
      by (rewrite EU, (schedule_policy_focus_guards st b N us i x Eb), <- guards_add; reflexivity).
    assert (Hts : observe (ts' $ i) = observe x) by (unfold ts'; now rewrite Vector.nth_replace_eq).
    assert (Hus : observe (us' $ i) = observe x) by (unfold us'; now rewrite Vector.nth_replace_eq).
    clearbody ts' us'; clear ET EU.
    destruct (observe x) as [[]| |next|y|Y e k|Y c k] eqn:Hx.
    - apply (galignF_guard _ T' U' (n + a) (m + b)
        (schedule_policy sch N (ts' -- i) None st) (schedule_policy sch N (us' -- i) None st)).
      + rewrite ET', (observe_equ_go _ _ (schedule_policy_focused_ret sch N ts' i st Hts)); rewrite <- guards_guard; reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_policy_focused_ret sch N us' i st Hus)); rewrite <- guards_guard; reflexivity.
      + apply (sched_rel_at 0 0 N (ts' -- i) (us' -- i) None st);
          [apply pool_guard_equ_remove, Hp'|reflexivity|reflexivity].
    - apply (galignF_stuck _ T' U' (n + a) (m + b)).
      + rewrite ET', (observe_equ_go _ _ (schedule_policy_focused_stuck sch N ts' i st Hts)); reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_policy_focused_stuck sch N us' i st Hus)); reflexivity.
    - apply (galignF_step _ T' U' (n + a) (m + b)
        (schedule_policy sch (S N) (ts' @ i := next) (Some i) st) (schedule_policy sch (S N) (us' @ i := next) (Some i) st)).
      + rewrite ET', (observe_equ_go _ _ (schedule_policy_focused_step sch N ts' i next st Hts)); reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_policy_focused_step sch N us' i next st Hus)); reflexivity.
      + eapply (sched_rel_at 0 0 (S N) _ _ (Some i) st);
          [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
    - apply (galignF_guard _ T' U' (n + a) (m + b)
        (schedule_policy sch (S N) (ts' @ i := y) (Some i) st) (schedule_policy sch (S N) (us' @ i := y) (Some i) st)).
      + rewrite ET', (observe_equ_go _ _ (schedule_policy_focused_guard sch N ts' i y st Hts)); rewrite <- guards_guard; reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_policy_focused_guard sch N us' i y st Hus)); rewrite <- guards_guard; reflexivity.
      + eapply (sched_rel_at 0 0 (S N) _ _ (Some i) st);
          [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
    - destruct e as [y|[f|e']]; [dependent destruction y|dependent destruction f|].
      + apply (galignF_guard _ T' U' (n + a) (m + b)
          (schedule_policy sch (S N) (ts' @ i := k tt) None st) (schedule_policy sch (S N) (us' @ i := k tt) None st)).
        * rewrite ET', (observe_equ_go _ _ (schedule_policy_focused_yield sch N ts' i k st Hts)); rewrite <- guards_guard; reflexivity.
        * rewrite EU', (observe_equ_go _ _ (schedule_policy_focused_yield sch N us' i k st Hus)); rewrite <- guards_guard; reflexivity.
        * eapply (sched_rel_at 0 0 (S N) _ _ None st);
            [|cbn [guards]; reflexivity|cbn [guards]; reflexivity];
            apply pool_guard_equ_replace, Hp'.
      + apply (galignF_guard _ T' U' (n + a) (m + b)
          (schedule_policy sch (S (S N)) (k true :: (ts' @ i := k false)) (Some (Fin.FS i)) st)
          (schedule_policy sch (S (S N)) (k true :: (us' @ i := k false)) (Some (Fin.FS i)) st)).
        * rewrite ET', (observe_equ_go _ _ (schedule_policy_focused_fork sch N ts' i k st Hts)); rewrite <- guards_guard; reflexivity.
        * rewrite EU', (observe_equ_go _ _ (schedule_policy_focused_fork sch N us' i k st Hus)); rewrite <- guards_guard; reflexivity.
        * eapply (sched_rel_at 0 0 (S (S N)) _ _ (Some (Fin.FS i)) st);
            [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_cons, pool_guard_equ_replace, Hp'.
      + apply (galignF_vis _ T' U' (n + a) (m + b) (inl1 e' : (E +' schedE) Y)
          (fun z => schedule_policy sch (S N) (ts' @ i := k z) (Some i) st)
          (fun z => schedule_policy sch (S N) (us' @ i := k z) (Some i) st)).
        * rewrite ET', (observe_equ_go _ _ (schedule_policy_focused_user_event sch N ts' i e' k st Hts)); reflexivity.
        * rewrite EU', (observe_equ_go _ _ (schedule_policy_focused_user_event sch N us' i e' k st Hus)); reflexivity.
        * intro z; eapply (sched_rel_at 0 0 (S N) _ _ (Some i) st);
            [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
    - apply (galignF_br _ T' U' (n + a) (m + b) c
        (fun j => schedule_policy sch (S N) (ts' @ i := k j) (Some i) st)
        (fun j => schedule_policy sch (S N) (us' @ i := k j) (Some i) st)).
      + rewrite ET', (observe_equ_go _ _ (schedule_policy_focused_br sch N ts' i c k st Hts)); reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_policy_focused_br sch N us' i c k st Hus)); reflexivity.
      + intro j; eapply (sched_rel_at 0 0 (S N) _ _ (Some i) st);
          [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
  Qed.

  Lemma schedule_policy_galigned N (ts us : pool E B N) f st :
    pool_guard_equ ts us ->
    galigned (schedule_policy sch N ts f st) (schedule_policy sch N us f st).
  Proof.
    intro Hp; apply (galigned_coind sched_rel sched_rel_step).
    apply (sched_rel_at 0 0 N ts us f st); [exact Hp|reflexivity|reflexivity].
  Qed.

  Lemma erased_schedule_policy_galigned N (ts us : pool E B N) f st :
    pool_guard_equ ts us ->
    galigned (project_scheduled (schedule_policy sch N ts f st))
      (project_scheduled (schedule_policy sch N us f st)).
  Proof. intro Hp; unfold project_scheduled; apply interp_galigned, schedule_policy_galigned, Hp. Qed.
End ScheduleAlign.

Section ScheduleAlignmentSpecializations.
  Context {E B : Type -> Type} {HB : Bn -< B}.

  Lemma schedule_focus_guards a N (ts : pool E B (S N)) i (x : thread E B) :
    (ts $ i) ≅ guards a x ->
    schedule (S N) ts (Some i) ≅ guards a (schedule (S N) (ts @ i := x) (Some i)).
  Proof. apply (schedule_policy_focus_guards nd_scheduler tt a N ts i x). Qed.

  Lemma schedule_galigned N (ts us : pool E B N) f :
    pool_guard_equ ts us -> galigned (schedule N ts f) (schedule N us f).
  Proof. apply (schedule_policy_galigned nd_scheduler N ts us f tt). Qed.

  Lemma schedule_rr_galigned N (ts us : pool E B N) f cursor :
    pool_guard_equ ts us -> galigned (schedule_rr N ts f cursor) (schedule_rr N us f cursor).
  Proof. apply (schedule_policy_galigned rr_scheduler N ts us f cursor). Qed.

  Lemma erased_schedule_galigned N (ts us : pool E B N) f :
    pool_guard_equ ts us ->
    galigned (project_scheduled (schedule N ts f)) (project_scheduled (schedule N us f)).
  Proof. apply (erased_schedule_policy_galigned nd_scheduler N ts us f tt). Qed.

  Lemma erased_schedule_rr_galigned N (ts us : pool E B N) f cursor :
    pool_guard_equ ts us ->
    galigned (project_scheduled (schedule_rr N ts f cursor))
      (project_scheduled (schedule_rr N us f cursor)).
  Proof. apply (erased_schedule_policy_galigned rr_scheduler N ts us f cursor). Qed.
End ScheduleAlignmentSpecializations.

(** Round-robin introduces no branch, including at a singleton boundary. *)
Lemma branchfree_schedule_rr {E B} {HB : Bn -< B} :
  forall n (ts : pool E B n) focus cursor,
    pool_branchfree ts -> BranchFree (schedule_rr n ts focus cursor).
Proof.
  unfold BranchFree; coinduction R IH; intros n ts focus cursor Hbf.
  destruct focus as [i|].
  - destruct n as [|n]; [inversion i|].
    pose proof (Hbf i) as Hi; apply branchfree_unfold in Hi.
    destruct (observe (ts $ i)) eqn:Hobs.
    + destruct r.
      rewrite (observe_equ_go _ _ (schedule_rr_focused_ret n ts i cursor Hobs)); constructor.
      apply IH; now apply pool_branchfree_remove.
    + rewrite (observe_equ_go _ _ (schedule_rr_focused_stuck n ts i cursor Hobs)); constructor.
    + rewrite (observe_equ_go _ _ (schedule_rr_focused_step n ts i t cursor Hobs)); constructor.
      inversion Hi; subst; apply IH; eauto using pool_branchfree_replace.
    + rewrite (observe_equ_go _ _ (schedule_rr_focused_guard n ts i t cursor Hobs)); constructor.
      inversion Hi; subst; apply IH; eauto using pool_branchfree_replace.
    + ddestruction Hi.
      destruct e as [y|[f|e]]; [destruct y|destruct f|].
      * rewrite (observe_equ_go _ _ (schedule_rr_focused_yield n ts i k cursor Hobs)); constructor.
        apply IH; eauto using pool_branchfree_replace.
      * rewrite (observe_equ_go _ _ (schedule_rr_focused_fork n ts i k cursor Hobs)); constructor.
        apply IH; eauto using pool_branchfree_cons, pool_branchfree_replace.
      * rewrite (observe_equ_go _ _ (schedule_rr_focused_user_event n ts i e k cursor Hobs)); constructor.
        intro x; apply IH; eauto using pool_branchfree_replace.
    + inversion Hi.
  - destruct n as [|n].
    + rewrite (observe_equ_go _ _ (schedule_rr_empty_none ts cursor)); constructor.
    + rewrite (observe_equ_go _ _ (schedule_rr_no_focus_nonempty n ts cursor)); constructor.
      intros []; apply IH; exact Hbf.
Qed.
