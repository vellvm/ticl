From Stdlib Require Import Fin Vector Program.Equality Arith.PeanoNat.
From Coinduction Require Import coinduction lattice tactics.
From TICL Require Import
  ICTree.Core
  ICTree.Trans
  ICTree.Equ
  ICTree.Eq.Core
  ICTree.Eq.Bind
  ICTree.SBisim
  ICTree.Interp.Core
  ICTree.Interp.State.Mod
  ICTree.Events.Yield
  ICTree.Events.State
  ICTree.Events.Writer
  ICTree.Interp.Yield.Mod
  Utils.Vectors.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

Section PoolSBisim.
  Context {E : Type} `{Encode E}.

  Definition pool_sbisim {n : nat} (v1 v2 : pool E n) : Prop :=
    forall i, (v1 $ i) ~ (v2 $ i).

  Lemma pool_sbisim_sym {n} (v1 v2 : pool E n) :
    pool_sbisim v1 v2 -> pool_sbisim v2 v1.
  Proof. intros Hpool i; symmetry; apply Hpool. Qed.

  Lemma replace_pool_sbisim {n} (v1 v2 : pool E n) (i : Fin.t n)
        (t1 t2 : thread E) :
    pool_sbisim v1 v2 ->
    t1 ~ t2 ->
    pool_sbisim (v1 @ i := t1) (v2 @ i := t2).
  Proof.
    intros Hv Ht.
    exact (vector_replace_pointwise (fun a b : thread E => a ~ b)
      v1 v2 i t1 t2 (fun j _ => Hv j) Ht).
  Qed.

  Lemma remove_pool_sbisim {n} (v1 v2 : pool E (S n)) (i : Fin.t (S n)) :
    pool_sbisim v1 v2 ->
    pool_sbisim (v1 -- i) (v2 -- i).
  Proof.
    intros Hv.
    exact (vector_remove_pointwise (fun a b : thread E => a ~ b) v1 v2 i
             (fun j _ => Hv j)).
  Qed.

  Lemma cons_pool_sbisim {n} (t1 t2 : thread E) (v1 v2 : pool E n) :
    t1 ~ t2 ->
    pool_sbisim v1 v2 ->
    pool_sbisim ((t1 :: v1)%vector) ((t2 :: v2)%vector).
  Proof.
    exact (vector_cons_pointwise (fun a b : thread E => a ~ b) t1 t2 v1 v2).
  Qed.

  (** ** [equ]-level pool congruences, used by [schedule_pool_proper]. *)
  Definition pool_equ {n : nat} (v1 v2 : pool E n) : Prop :=
    forall i, (v1 $ i) ≅ (v2 $ i).

  Lemma replace_pool_equ {n} (v1 v2 : pool E n) (i : Fin.t n)
        (t1 t2 : thread E) :
    pool_equ v1 v2 ->
    t1 ≅ t2 ->
    pool_equ (v1 @ i := t1) (v2 @ i := t2).
  Proof.
    intros Hv Ht.
    exact (vector_replace_pointwise (fun a b : thread E => a ≅ b)
      v1 v2 i t1 t2 (fun j _ => Hv j) Ht).
  Qed.

  Lemma remove_pool_equ {n} (v1 v2 : pool E (S n)) (i : Fin.t (S n)) :
    pool_equ v1 v2 ->
    pool_equ (v1 -- i) (v2 -- i).
  Proof.
    intros Hv.
    exact (vector_remove_pointwise (fun a b : thread E => a ≅ b) v1 v2 i
             (fun j _ => Hv j)).
  Qed.

  Lemma cons_pool_equ {n} (t1 t2 : thread E) (v1 v2 : pool E n) :
    t1 ≅ t2 ->
    pool_equ v1 v2 ->
    pool_equ ((t1 :: v1)%vector) ((t2 :: v2)%vector).
  Proof.
    exact (vector_cons_pointwise (fun a b : thread E => a ≅ b) t1 t2 v1 v2).
  Qed.
End PoolSBisim.

Section SchedulerTransitions.
  Context {E : Type} `{Encode E}.

  Lemma trans_schedule_no_focus_nonempty n (v : pool E (S n)) :
    trans (obs (inl Yield : yieldE + (spawnE + E)) tt)
      (schedule (S n) v None)
      (Br n (fun i => schedule (S n) v (Some i))).
  Proof.
    unfold trans; cbn.
    eapply (@Stepobs
      (yieldE + (spawnE + E)) _ unit
      (inl Yield) _ tt
      (Br n (fun i => schedule (S n) v (Some i)))).
    reflexivity.
  Qed.

  Lemma trans_schedule_focused_yield n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inl Yield) k ->
    trans (obs (inl Yield : yieldE + (spawnE + E)) tt)
      (schedule (S n) v (Some i))
      (Br n (fun j => schedule (S n) ((v @ i := (k tt))) (Some j))).
  Proof.
    intro Hobs.
    unfold trans; lazy [schedule observe _observe].
    change (@_observe _ _ unit (v $ i)) with (observe (v $ i)).
    rewrite Hobs.
    eapply Stepguard.
    eapply (@Stepobs
      (yieldE + (spawnE + E)) _ unit
      (inl Yield) _ tt
      (Br n (fun j => schedule (S n) ((v @ i := (k tt))) (Some j)))).
    reflexivity.
  Qed.

  Lemma trans_schedule_focused_fork n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v $ i) = VisF (inr (inl Fork)) k ->
    trans (obs (inr (inl Spawn) : yieldE + (spawnE + E)) tt)
      (schedule (S n) v (Some i))
      (schedule (S (S n))
         (((k true) :: ((v @ i := (k false))))%vector)
         (Some (Fin.FS i))).
  Proof.
    intro Hobs.
    unfold trans; lazy [schedule observe _observe].
    change (@_observe _ _ unit (v $ i)) with (observe (v $ i)).
    rewrite Hobs.
    eapply (@Stepobs
      (yieldE + (spawnE + E)) _ unit
      (inr (inl Spawn)) _ tt
      (schedule (S (S n))
         (((k true) :: ((v @ i := (k false))))%vector)
         (Some (Fin.FS i)))).
    reflexivity.
  Qed.

  Lemma trans_schedule_focused_user_event
        n (v : pool E (S n)) (i : Fin.t (S n)) e k x :
    observe (v $ i) = VisF (inr (inr e)) k ->
    trans (obs (inr (inr e) : yieldE + (spawnE + E)) x)
      (schedule (S n) v (Some i))
      (schedule (S n) ((v @ i := (k x))) (Some i)).
  Proof.
    intro Hobs.
    unfold trans; lazy [schedule observe _observe].
    change (@_observe _ _ unit (v $ i)) with (observe (v $ i)).
    rewrite Hobs.
    eapply (@Stepobs
      (yieldE + (spawnE + E)) _ unit
      (inr (inr e)) _ x
      (schedule (S n) ((v @ i := (k x))) (Some i))).
    reflexivity.
  Qed.

  Lemma trans_schedule_focused_br
        n (v : pool E (S n)) (i : Fin.t (S n)) b k (j : Fin.t (S b)) :
    observe (v $ i) = BrF b k ->
    trans tau (schedule (S n) v (Some i))
      (schedule (S n) ((v @ i := (k j))) (Some i)).
  Proof.
    intro Hobs.
    unfold trans; lazy [schedule observe _observe].
    change (@_observe _ _ unit (v $ i)) with (observe (v $ i)).
    rewrite Hobs.
    eapply (@Steptau
      (yieldE + (spawnE + E)) _ unit b j _
      (schedule (S n) ((v @ i := (k j))) (Some i))).
    reflexivity.
  Qed.

  (** ** Phase 2: remaining transition / unfold constructors. *)

  Lemma trans_schedule_empty_ret (v : pool E 0) :
    schedule 0 v None ≅ Ret tt.
  Proof.
    rewrite (ictree_eta (schedule 0 v None)).
    rewrite schedule_empty_none.
    reflexivity.
  Qed.

  Lemma trans_schedule_focused_ret n (v : pool E (S n)) (i : Fin.t (S n)) :
    observe (v $ i) = RetF tt ->
    schedule (S n) v (Some i) ≅ Guard (schedule n ((v -- i)) None).
  Proof.
    intro Hobs.
    rewrite (ictree_eta (schedule (S n) v (Some i))).
    rewrite (schedule_focused_ret _ v i Hobs).
    reflexivity.
  Qed.

  Lemma trans_schedule_focused_guard n (v : pool E (S n)) (i : Fin.t (S n)) t :
    observe (v $ i) = GuardF t ->
    schedule (S n) v (Some i)
      ≅ Guard (schedule (S n) ((v @ i := t)) (Some i)).
  Proof.
    intro Hobs.
    rewrite (ictree_eta (schedule (S n) v (Some i))).
    rewrite (schedule_focused_guard _ v i t Hobs).
    reflexivity.
  Qed.

  (** ** Phase 3: scheduler transition inversions. *)

  Lemma schedule_no_focus_equ n (v : pool E (S n)) :
    schedule (S n) v None
      ≅ Vis (inl Yield : yieldE + (spawnE + E))
          (fun _ => Br n (fun i => schedule (S n) v (Some i))).
  Proof.
    rewrite (ictree_eta (schedule (S n) v None)).
    rewrite schedule_no_focus_nonempty.
    reflexivity.
  Qed.

  Lemma trans_schedule_no_focus_inv n (v : pool E (S n)) l t' :
    trans l (schedule (S n) v None) t' ->
    l = obs (inl Yield : yieldE + (spawnE + E)) tt /\
    t' ≅ Br n (fun i => schedule (S n) v (Some i)).
  Proof.
    intro TR.
    rewrite schedule_no_focus_equ in TR.
    apply trans_vis_inv in TR as (x & Heq & Hl).
    destruct x.
    split; auto.
  Qed.

  (** ** [schedule] respects [equ]-equality of pools, in every focus. *)
  Lemma schedule_pool_proper n (v w : pool E n) focus :
    pool_equ v w ->
    schedule n v focus ≅ schedule n w focus.
  Proof.
    revert n v w focus.
    coinduction R CH.
    intros n v w focus Hvw.
    destruct focus as [i |].
    - destruct n as [| n']; [ inversion i |].
      pose proof (Hvw i) as Hi.
      assert (Hgo : go (observe (v $ i)) ≅ go (observe (w $ i))).
      { rewrite <- !ictree_eta. exact Hi. }
      rewrite (ictree_eta (schedule (S n') v (Some i))).
      rewrite (ictree_eta (schedule (S n') w (Some i))).
      destruct (observe (v $ i)) as [r | b k | g | e k] eqn:Hv;
      destruct (observe (w $ i)) as [r2 | b2 k2 | g2 | e2 k2] eqn:Hw;
        try (step in Hgo; inversion Hgo; fail).
      + destruct r, r2.
        rewrite (@schedule_focused_ret E _ n' v i Hv).
        rewrite (@schedule_focused_ret E _ n' w i Hw).
        cbn. constructor. apply CH. apply remove_pool_equ. exact Hvw.
      + pose proof (equ_br_invT Hgo) as Hbeq; subst b2.
        pose proof (equ_br_invE Hgo) as Hke.
        rewrite (@schedule_focused_br E _ n' v i b k Hv).
        rewrite (@schedule_focused_br E _ n' w i b k2 Hw).
        cbn. constructor. intro j. apply CH.
        apply replace_pool_equ. exact Hvw. apply Hke.
      + pose proof (equ_guard_invE Hgo) as Hge.
        rewrite (@schedule_focused_guard E _ n' v i g Hv).
        rewrite (@schedule_focused_guard E _ n' w i g2 Hw).
        cbn. constructor. apply CH.
        apply replace_pool_equ. exact Hvw. exact Hge.
      + pose proof (equ_vis_invT Hgo) as [_ Heeq]; subst e2.
        pose proof (equ_vis_invE Hgo) as Hke.
        destruct e as [yld | [frk | usr]].
        * destruct yld.
          rewrite (@schedule_focused_yield E _ n' v i k Hv).
          rewrite (@schedule_focused_yield E _ n' w i k2 Hw).
          cbn. constructor. apply CH.
          apply replace_pool_equ. exact Hvw. apply (Hke tt).
        * destruct frk.
          rewrite (@schedule_focused_fork E _ n' v i k Hv).
          rewrite (@schedule_focused_fork E _ n' w i k2 Hw).
          cbn. constructor. intros _. apply CH.
          apply cons_pool_equ.
          -- apply (Hke true).
          -- apply replace_pool_equ. exact Hvw. apply (Hke false).
        * rewrite (@schedule_focused_user_event E _ n' v i usr k Hv).
          rewrite (@schedule_focused_user_event E _ n' w i usr k2 Hw).
          cbn. constructor. intro x. apply CH.
          apply replace_pool_equ. exact Hvw. apply (Hke x).
    - destruct n as [| n'].
      + rewrite (ictree_eta (schedule 0 v None)).
        rewrite (ictree_eta (schedule 0 w None)).
        rewrite schedule_empty_none, schedule_empty_none.
        cbn. reflexivity.
      + rewrite (ictree_eta (schedule (S n') v None)).
        rewrite (ictree_eta (schedule (S n') w None)).
        rewrite schedule_no_focus_nonempty, schedule_no_focus_nonempty.
        cbn. constructor. intros _. cbn. step.
        constructor. intro i. apply CH. exact Hvw.
  Qed.
  (** ** Phase 4: thread-step to scheduler-step lifts. *)

  Lemma pool_equ_refl {n} (v : pool E n) : pool_equ v v.
  Proof. intro j; reflexivity. Qed.

  Lemma replace_pool_idem_equ {n} (v : pool E (S n)) (i : Fin.t (S n))
        (a b : thread E) :
    pool_equ (v @ i := b) ((v @ i := a) @ i := b).
  Proof. rewrite Vector.replace_replace_eq. apply pool_equ_refl. Qed.

  Lemma br_schedule_pool_equ {n} (v w : pool E (S n)) :
    pool_equ v w ->
    Br n (fun j => schedule (S n) v (Some j))
      ≅ Br n (fun j => schedule (S n) w (Some j)).
  Proof.
    intro Hvw. step. constructor. intro j.
    apply schedule_pool_proper. exact Hvw.
  Qed.

  Lemma schedule_lift_yield n (v : pool E (S n)) (i : Fin.t (S n))
        (u : thread E) :
    trans (obs (inl Yield : yieldE + (forkE + E)) tt) (v $ i) u ->
    trans (obs (inl Yield : yieldE + (spawnE + E)) tt)
      (schedule (S n) v (Some i))
      (Br n (fun j => schedule (S n) ((v @ i := u)) (Some j))).
  Proof.
    intro TR.
    unfold trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (obs (inl Yield : yieldE + (forkE + E)) tt) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR; intros.
    - (* Stepguard: observe (v $ i) = GuardF t *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      apply trans_guard.
      rewrite (br_schedule_pool_equ ((v @ i := u0))
                 ((((v @ i := t)) @ i := u0))
                 (replace_pool_idem_equ v i t u0)).
      apply (IHTR ((v @ i := t)) i u0).
      + now rewrite Vector.nth_replace_eq.
      + exact Hou.
      + exact Hlbl.
    - discriminate Hlbl.
    - (* Stepobs *)
      dependent destruction Hlbl.
      assert (Hu0 : u ≅ k tt).
      { transitivity t.
        - rewrite (ictree_eta u), (ictree_eta t), <- Hou; reflexivity.
        - symmetry; assumption. }
      rewrite (br_schedule_pool_equ ((v @ i := u))
                 ((v @ i := (k tt)))
                 (replace_pool_equ v v i u (k tt) (pool_equ_refl v) Hu0)).
      apply (trans_schedule_focused_yield n v i k (eq_sym Hot)).
    - discriminate Hlbl.
  Qed.

  Lemma schedule_some_pool_equ {m} (v w : pool E (S m)) (i : Fin.t (S m)) :
    pool_equ v w ->
    schedule (S m) v (Some i) ≅ schedule (S m) w (Some i).
  Proof. intro Hvw. apply schedule_pool_proper. exact Hvw. Qed.

  Lemma schedule_lift_user n (v : pool E (S n)) (i : Fin.t (S n))
        (e : E) (x : encode e) (u : thread E) :
    trans (obs (inr (inr e) : yieldE + (forkE + E)) x) (v $ i) u ->
    trans (obs (inr (inr e) : yieldE + (spawnE + E)) x)
      (schedule (S n) v (Some i))
      (schedule (S n) ((v @ i := u)) (Some i)).
  Proof.
    intro TR.
    unfold trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (obs (inr (inr e) : yieldE + (forkE + E)) x) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR; intros.
    - (* Stepguard *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      apply trans_guard.
      rewrite (schedule_some_pool_equ ((v @ i := u0))
                 ((((v @ i := t)) @ i := u0)) i
                 (replace_pool_idem_equ v i t u0)).
      apply (IHTR ((v @ i := t)) i u0).
      + now rewrite Vector.nth_replace_eq.
      + exact Hou.
      + exact Hlbl.
    - discriminate Hlbl.
    - (* Stepobs *)
      dependent destruction Hlbl.
      assert (Hu0 : u ≅ k x).
      { transitivity t.
        - rewrite (ictree_eta u), (ictree_eta t), <- Hou; reflexivity.
        - symmetry; assumption. }
      rewrite (schedule_some_pool_equ ((v @ i := u))
                 ((v @ i := (k x))) i
                 (replace_pool_equ v v i u (k x) (pool_equ_refl v) Hu0)).
      apply (trans_schedule_focused_user_event n v i e k x (eq_sym Hot)).
    - discriminate Hlbl.
  Qed.

  Lemma schedule_lift_tau n (v : pool E (S n)) (i : Fin.t (S n))
        (u : thread E) :
    trans tau (v $ i) u ->
    trans tau
      (schedule (S n) v (Some i))
      (schedule (S n) ((v @ i := u)) (Some i)).
  Proof.
    intro TR.
    unfold trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (tau : label (yieldE + (forkE + E))) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR; intros.
    - (* Stepguard *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      apply trans_guard.
      rewrite (schedule_some_pool_equ ((v @ i := u0))
                 ((((v @ i := t)) @ i := u0)) i
                 (replace_pool_idem_equ v i t u0)).
      apply (IHTR ((v @ i := t)) i u0).
      + now rewrite Vector.nth_replace_eq.
      + exact Hou.
      + exact Hlbl.
    - (* Steptau *)
      assert (Hu0 : u ≅ k x).
      { transitivity t.
        - rewrite (ictree_eta u), (ictree_eta t), <- Hou; reflexivity.
        - symmetry; assumption. }
      rewrite (schedule_some_pool_equ ((v @ i := u))
                 ((v @ i := (k x))) i
                 (replace_pool_equ v v i u (k x) (pool_equ_refl v) Hu0)).
      apply (trans_schedule_focused_br n v i n0 k x (eq_sym Hot)).
    - discriminate Hlbl.
    - discriminate Hlbl.
  Qed.

  Lemma schedule_lift_fork n (v : pool E (S n)) (i : Fin.t (S n))
        (b : bool) (u : thread E) :
    trans (obs (inr (inl Fork) : yieldE + (forkE + E)) b) (v $ i) u ->
    exists k2,
      (forall c : bool,
         trans (obs (inr (inl Fork) : yieldE + (forkE + E)) c) (v $ i) (k2 c)) /\
      trans (obs (inr (inl Spawn) : yieldE + (spawnE + E)) tt)
        (schedule (S n) v (Some i))
        (schedule (S (S n))
           (((k2 true) :: ((v @ i := (k2 false))))%vector)
           (Some (Fin.FS i))).
  Proof.
    intro TR.
    unfold trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (obs (inr (inl Fork) : yieldE + (forkE + E)) b) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR; intros.
    - (* Stepguard *)
      destruct (IHTR ((v @ i := t)) i u0
                  ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl)
        as (k2 & Hcont & Hstep).
      exists k2. split.
      + intro c. specialize (Hcont c).
        rewrite Vector.nth_replace_eq in Hcont.
        rewrite (ictree_eta (v $ i)), <- Hot.
        now apply trans_guard.
      + rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
        apply trans_guard.
        rewrite (schedule_pool_proper (S (S n))
                   (((k2 true) :: ((v @ i := (k2 false))))%vector)
                   (((k2 true) :: ((((v @ i := t)) @ i := (k2 false))))%vector)
                   (Some (Fin.FS i))).
        * exact Hstep.
        * apply cons_pool_equ; [reflexivity |].
          apply replace_pool_idem_equ.
    - discriminate Hlbl.
    - (* Stepobs *)
      dependent destruction Hlbl.
      exists k. split.
      + intro c.
        rewrite (ictree_eta (v $ i)), <- Hot.
        apply trans_vis.
      + apply (trans_schedule_focused_fork n v i k (eq_sym Hot)).
    - discriminate Hlbl.
  Qed.

  Lemma remove_pool_agree {n} :
    forall (v w : pool E (S n)) (i : Fin.t (S n)),
    (forall j, i <> j -> (v $ j) ≅ (w $ j)) ->
    pool_equ (v -- i) (w -- i).
  Proof.
    intros v w i Hag.
    exact (vector_remove_pointwise (fun a b : thread E => a ≅ b) v w i Hag).
  Qed.

  Lemma remove_replace_pool_equ {n} (v : pool E (S n)) (i : Fin.t (S n))
        (a : thread E) :
    pool_equ ((v @ i := a) -- i) (v -- i).
  Proof.
    apply remove_pool_agree. intros j Hij.
    rewrite Vector.nth_replace_neq by congruence. reflexivity.
  Qed.

  Lemma schedule_lift_ret n (v : pool E (S n)) (i : Fin.t (S n))
        (u : thread E) :
    trans (val tt : label (yieldE + (forkE + E))) (v $ i) u ->
    schedule (S n) v (Some i) ~ schedule n ((v -- i)) None.
  Proof.
    intro TR.
    unfold trans in TR.
    remember (observe (v $ i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (val tt : label (yieldE + (forkE + E))) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR; intros.
    - (* Stepguard *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      rewrite sb_guard.
      rewrite (IHTR ((v @ i := t)) i u0
                 ltac:(now rewrite Vector.nth_replace_eq) Hou Hlbl).
      now rewrite (schedule_pool_proper n ((((v @ i := t)) -- i))
               ((v -- i)) None (remove_replace_pool_equ v i t)).
    - discriminate Hlbl.
    - discriminate Hlbl.
    - (* Stepval *)
      dependent destruction Hlbl.
      rewrite (trans_schedule_focused_ret n v i (eq_sym Hot)).
      apply sb_guard.
  Qed.

  (** ** Phase 5: [schedule] preserves pool strong bisimilarity. *)

  Notation completed' := (completed E).
  Notation stR R := (lattice.body (coinduction.t (sb eq)) R).

  Lemma schedule_match (R : rel completed' completed')
    (Hch : forall m (w1 w2 : pool E m) f,
       pool_sbisim w1 w2 -> stR R (schedule m w1 f) (schedule m w2 f)) :
    forall l os ot', trans_ l os ot' ->
    forall n (v1 v2 : pool E n) focus (t' : completed'),
      os = observe (schedule n v1 focus) ->
      ot' = observe t' ->
      pool_sbisim v1 v2 ->
      exists u', trans l (schedule n v2 focus) u' /\ stR R t' u'.
  Proof.
    intros l os ot' TR.
    induction TR; intros nn v1 v2 focus t' Hos Hot' Hpool.
    - (* Stepguard *)
      destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        destruct (observe (v1 $ i)) as [r0 | b0 k0 | g | e0 k0] eqn:Hvi.
        * (* Ret: recurse on the smaller pool *)
          destruct r0.
          rewrite (schedule_focused_ret n' v1 i Hvi) in Hos.
          dependent destruction Hos.
          destruct (IHTR n' ((v1 -- i)) ((v2 -- i)) None t'
                      eq_refl Hot' (remove_pool_sbisim v1 v2 i Hpool))
            as (u' & Htru & Hresu).
          assert (Hvr : (v1 $ i) ≅ Ret tt).
          { rewrite (ictree_eta (v1 $ i)), Hvi. reflexivity. }
          assert (Htrv : trans (val tt : label (yieldE + (forkE + E)))
                           (v1 $ i) stuck).
          { rewrite Hvr. apply trans_ret. }
          destruct (sbisim_trans (v1 $ i) (v2 $ i) stuck (val tt) eq
                      (Hpool i) Htrv) as (lv & uv & Htr2v & Hlv & Hsbv).
          subst lv.
          assert (Hlift : schedule (S n') v2 (Some i)
                          ~ schedule n' ((v2 -- i)) None).
          { apply (schedule_lift_ret n' v2 i uv Htr2v). }
          destruct (sbisim_trans (schedule n' ((v2 -- i)) None)
                      (schedule (S n') v2 (Some i)) u' l eq
                      ltac:(symmetry; exact Hlift) Htru)
            as (lq & uq & Htrq & Hlq & Hsbq).
          subst lq.
          exists uq. split.
          -- exact Htrq.
          -- rewrite <- Hsbq. exact Hresu.
        * (* Br: schedule head is a Br, not a Guard *)
          rewrite (schedule_focused_br n' v1 i b0 k0 Hvi) in Hos.
          discriminate Hos.
        * (* Guard: recurse on the same pool, focus unchanged *)
          rewrite (schedule_focused_guard n' v1 i g Hvi) in Hos.
          dependent destruction Hos.
          apply (IHTR (S n') ((v1 @ i := g)) v2 (Some i) t'
                   eq_refl Hot').
          intro j. destruct (Fin.eq_dec i j) as [Hij | Hij].
          -- subst j.
             rewrite Vector.nth_replace_eq.
             assert (Hvg : (v1 $ i) ≅ Guard g).
             { rewrite (ictree_eta (v1 $ i)), Hvi. reflexivity. }
             transitivity (v1 $ i); [| apply Hpool].
             rewrite Hvg. symmetry. apply sb_guard.
          -- rewrite Vector.nth_replace_neq by congruence. apply Hpool.
        * (* Vis: Yield (Guard head), or Fork / user (Vis head) *)
          destruct e0 as [yld | [frk | usr]].
          -- (* Yield: invert the focused-yield residual directly *)
             destruct yld.
             rewrite (schedule_focused_yield n' v1 i k0 Hvi) in Hos.
             dependent destruction Hos.
             assert (TR0 : trans l
               (schedule (S n') ((v1 @ i := (k0 tt))) None) t').
             { unfold trans. rewrite <- Hot'. exact TR. }
             apply trans_schedule_no_focus_inv in TR0 as (Hl & Hbr).
             subst l.
             assert (Hvis : (v1 $ i) ≅ Vis (inl Yield) k0).
             { rewrite (ictree_eta (v1 $ i)), Hvi. reflexivity. }
             assert (Htry : trans
               (obs (inl Yield : yieldE + (forkE + E)) tt) (v1 $ i) (k0 tt)).
             { rewrite Hvis. apply trans_vis. }
             destruct (sbisim_trans (v1 $ i) (v2 $ i) (k0 tt)
                         (obs (inl Yield : yieldE + (forkE + E)) tt) eq
                         (Hpool i) Htry) as (ly & uy & Htr2y & Hly & Hsby).
             subst ly.
             exists (Br n' (fun j =>
               schedule (S n') ((v2 @ i := uy)) (Some j))). split.
             ++ apply (schedule_lift_yield n' v2 i uy Htr2y).
             ++ rewrite Hbr.
                apply (coinduction.bt_t (sb eq)).
                apply step_sb_br_id; [reflexivity | intro j].
                apply Hch.
                apply replace_pool_sbisim; assumption.
          -- (* Fork: Vis head, not a Guard *)
             destruct frk.
             rewrite (schedule_focused_fork n' v1 i k0 Hvi) in Hos.
             discriminate Hos.
          -- (* user: Vis head, not a Guard *)
             rewrite (schedule_focused_user_event n' v1 i usr k0 Hvi) in Hos.
             discriminate Hos.
      + destruct nn as [| n'].
        * rewrite (schedule_empty_none v1) in Hos. discriminate Hos.
        * rewrite (schedule_no_focus_nonempty n' v1) in Hos. discriminate Hos.
    - (* Steptau *)
      destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        destruct (observe (v1 $ i)) as [r0 | b0 k0 | g | e0 k0] eqn:Hvi.
        * destruct r0. rewrite (schedule_focused_ret n' v1 i Hvi) in Hos.
          discriminate Hos.
        * rewrite (schedule_focused_br n' v1 i b0 k0 Hvi) in Hos.
          dependent destruction Hos.
          assert (Htr1 : trans tau (v1 $ i) (k0 x)).
          { rewrite (ictree_eta (v1 $ i)), Hvi.
            apply trans_br with (x := x). reflexivity. }
          destruct (sbisim_trans (v1 $ i) (v2 $ i) (k0 x) tau eq (Hpool i) Htr1)
            as (l' & u' & Htr2 & Hl' & Hsb).
          subst l'.
          exists (schedule (S n') ((v2 @ i := u')) (Some i)). split.
          -- apply schedule_lift_tau. exact Htr2.
          -- assert (Ht' : t' ≅ schedule (S n') ((v1 @ i := (k0 x))) (Some i)).
             { rewrite (ictree_eta t'), <- Hot', <- (ictree_eta t).
               symmetry; assumption. }
             rewrite Ht'. apply Hch.
             apply replace_pool_sbisim; assumption.
        * rewrite (schedule_focused_guard n' v1 i g Hvi) in Hos.
          discriminate Hos.
        * destruct e0 as [yld | [frk | usr]].
          -- destruct yld.
             rewrite (schedule_focused_yield n' v1 i k0 Hvi) in Hos.
             discriminate Hos.
          -- destruct frk.
             rewrite (schedule_focused_fork n' v1 i k0 Hvi) in Hos.
             discriminate Hos.
          -- rewrite (schedule_focused_user_event n' v1 i usr k0 Hvi) in Hos.
             discriminate Hos.
      + destruct nn as [| n'].
        * rewrite (schedule_empty_none v1) in Hos. discriminate Hos.
        * rewrite (schedule_no_focus_nonempty n' v1) in Hos. discriminate Hos.
    - (* Stepobs *)
      destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        destruct (observe (v1 $ i)) as [r0 | b0 k0 | g | e1 k0] eqn:Hvi.
        * destruct r0. rewrite (schedule_focused_ret n' v1 i Hvi) in Hos.
          discriminate Hos.
        * rewrite (schedule_focused_br n' v1 i b0 k0 Hvi) in Hos.
          discriminate Hos.
        * rewrite (schedule_focused_guard n' v1 i g Hvi) in Hos.
          discriminate Hos.
        * destruct e1 as [yld | [frk | usr]].
          -- destruct yld.
             rewrite (schedule_focused_yield n' v1 i k0 Hvi) in Hos.
             discriminate Hos.
          -- (* Fork *)
             destruct frk.
             rewrite (schedule_focused_fork n' v1 i k0 Hvi) in Hos.
             dependent destruction Hos.
             destruct x.
             assert (Hvis : (v1 $ i) ≅ Vis (inr (inl Fork)) k0).
             { rewrite (ictree_eta (v1 $ i)), Hvi. reflexivity. }
             assert (Htrf : trans
               (obs (inr (inl Fork) : yieldE + (forkE + E)) false) (v1 $ i)
               (k0 false)).
             { rewrite Hvis. apply trans_vis. }
             destruct (sbisim_trans (v1 $ i) (v2 $ i) (k0 false)
                         (obs (inr (inl Fork)) false) eq (Hpool i) Htrf)
               as (lf & uf & Htr2 & Hlf & Hsbf).
             subst lf.
             destruct (schedule_lift_fork n' v2 i false uf Htr2)
               as (kf & Hforall & Hstep).
             exists (schedule (S (S n'))
                       (((kf true) :: ((v2 @ i := (kf false))))%vector)
                       (Some (Fin.FS i))).
             split.
             ++ exact Hstep.
             ++ assert (Ht' : t' ≅ schedule (S (S n'))
                  (((k0 true) :: ((v1 @ i := (k0 false))))%vector)
                  (Some (Fin.FS i))).
                { rewrite (ictree_eta t'), <- Hot', <- (ictree_eta t).
                  symmetry; assumption. }
                rewrite Ht'.
                assert (Hii : (v2 $ i) ~ (v1 $ i)) by (symmetry; apply Hpool).
                assert (Hkf : forall c, k0 c ~ kf c).
                { intro c.
                  destruct (sbisim_trans (v2 $ i) (v1 $ i) (kf c)
                              (obs (inr (inl Fork)) c) eq Hii (Hforall c))
                    as (lc & wc & Htrc & Hlc & Hsbc).
                  subst lc.
                  rewrite Hvis in Htrc.
                  apply trans_vis_inv in Htrc as (y & Hwy & Hly).
                  dependent destruction Hly.
                  rewrite Hwy in Hsbc. symmetry; exact Hsbc. }
                apply Hch.
                apply cons_pool_sbisim.
                ** apply Hkf.
                ** apply replace_pool_sbisim; [exact Hpool | apply Hkf].
          -- (* user event *)
             rewrite (schedule_focused_user_event n' v1 i usr k0 Hvi) in Hos.
             dependent destruction Hos.
             assert (Hvis : (v1 $ i) ≅ Vis (inr (inr usr)) k0).
             { rewrite (ictree_eta (v1 $ i)), Hvi. reflexivity. }
             assert (Htru : trans
               (obs (inr (inr usr) : yieldE + (forkE + E)) x) (v1 $ i) (k0 x)).
             { rewrite Hvis. apply trans_vis. }
             destruct (sbisim_trans (v1 $ i) (v2 $ i) (k0 x)
                         (obs (inr (inr usr) : yieldE + (forkE + E)) x) eq
                         (Hpool i) Htru)
               as (lu & u' & Htr2 & Hlu & Hsbu).
             subst lu.
             exists (schedule (S n') ((v2 @ i := u')) (Some i)). split.
             ++ apply (schedule_lift_user n' v2 i usr x u' Htr2).
             ++ assert (Ht' : t' ≅
                  schedule (S n') ((v1 @ i := (k0 x))) (Some i)).
                { rewrite (ictree_eta t'), <- Hot', <- (ictree_eta t).
                  symmetry; assumption. }
                rewrite Ht'. apply Hch.
                apply replace_pool_sbisim; assumption.
      + destruct nn as [| n'].
        * rewrite (schedule_empty_none v1) in Hos. discriminate Hos.
        * (* None nonempty Yield *)
          rewrite (schedule_no_focus_nonempty n' v1) in Hos.
          dependent destruction Hos.
          destruct x.
          exists (Br n' (fun j => schedule (S n') v2 (Some j))). split.
          -- apply (trans_schedule_no_focus_nonempty n' v2).
          -- assert (Ht' : t' ≅ Br n' (fun j => schedule (S n') v1 (Some j))).
             { rewrite (ictree_eta t'), <- Hot', <- (ictree_eta t).
               symmetry; assumption. }
             rewrite Ht'.
             apply (coinduction.bt_t (sb eq)).
             apply step_sb_br_id; [reflexivity | intro j].
             apply Hch. exact Hpool.
    - (* Stepval *)
      destruct focus as [i | ].
      + destruct nn as [| n']; [inversion i | ].
        destruct (observe (v1 $ i)) as [r0 | b k | g | e k] eqn:Hvi.
        * destruct r0. rewrite (schedule_focused_ret n' v1 i Hvi) in Hos.
          discriminate Hos.
        * rewrite (schedule_focused_br n' v1 i b k Hvi) in Hos.
          discriminate Hos.
        * rewrite (schedule_focused_guard n' v1 i g Hvi) in Hos.
          discriminate Hos.
        * destruct e as [yld | [frk | usr]].
          -- destruct yld.
             rewrite (schedule_focused_yield n' v1 i k Hvi) in Hos.
             discriminate Hos.
          -- destruct frk.
             rewrite (schedule_focused_fork n' v1 i k Hvi) in Hos.
             discriminate Hos.
          -- rewrite (schedule_focused_user_event n' v1 i usr k Hvi) in Hos.
             discriminate Hos.
      + destruct nn as [| n'].
        * rewrite (schedule_empty_none v1) in Hos.
          inversion Hos; subst.
          exists stuck. split.
          -- rewrite (trans_schedule_empty_ret v2). apply trans_ret.
          -- assert (Ht' : t' ≅ stuck).
             { rewrite (ictree_eta t'), <- Hot', <- (ictree_eta t).
               symmetry; assumption. }
             rewrite Ht'. reflexivity.
        * rewrite (schedule_no_focus_nonempty n' v1) in Hos.
          discriminate Hos.
  Qed.

  Theorem sbisim_schedule n (v1 v2 : pool E n) focus :
    pool_sbisim v1 v2 -> schedule n v1 focus ~ schedule n v2 focus.
  Proof.
    revert n v1 v2 focus.
    coinduction R CH.
    intros n v1 v2 focus Hpool.
    assert (Hch : forall m (w1 w2 : pool E m) f,
       pool_sbisim w1 w2 -> stR R (schedule m w1 f) (schedule m w2 f)).
    { intros m w1 w2 f Hw. apply CH. exact Hw. }
    split.
    - intros l t' TR.
      destruct (schedule_match R Hch _ _ _ TR n v1 v2 focus t'
                  eq_refl eq_refl Hpool) as (u' & Htru & Hres).
      exists l, u'. split; [exact Htru | split; [exact Hres | reflexivity]].
    - intros l t' TR.
      destruct (schedule_match R Hch _ _ _ TR n v2 v1 focus t'
                  eq_refl eq_refl (pool_sbisim_sym v1 v2 Hpool))
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
Lemma instr_schedule_pool_equ {Σ} n (v v' : pool (stateE Σ) n) focus σ :
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
  Context {E : Type} {HE : Encode E}.

  Definition pool_guard_equ {n} (ts us : pool E n) : Prop :=
    forall i, guard_equ (ts $ i) (us $ i).

  Lemma pool_equ_guard {n} (ts us : pool E n) :
    pool_equ ts us -> pool_guard_equ ts us.
  Proof. intros H i; apply guard_equ_equ, H. Qed.

  Lemma pool_replace_current {n} (ts : pool E n) (i : Fin.t n) :
    pool_equ (ts @ i := (ts $ i)) ts.
  Proof.
    intro j; destruct (Fin.eq_dec j i) as [->|Hne].
    - rewrite Vector.nth_replace_eq; reflexivity.
    - rewrite Vector.nth_replace_neq by congruence; reflexivity.
  Qed.

  Lemma pool_equ_guard_trans {n} (ts us vs : pool E n) :
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
    divergence is only ever aligned with silent divergence.  The relation is
    preserved by the erasure and state interpreters, by round-robin
    refinement, and by the scheduler on guard-equivalent pools, and it
    implies strong bisimulation. *)

Fixpoint guards {E} {HE : Encode E} {X} (n : nat) (t : ictree E X) : ictree E X :=
  match n with 0 => t | S n => Guard (guards n t) end.

Section Guards.
  Context {E : Type} {HE : Encode E} {X : Type}.

  Lemma guards_equ n (t u : ictree E X) : t ≅ u -> guards n t ≅ guards n u.
  Proof. intro H; induction n; cbn [guards]; [exact H|apply guard_equ_node; exact IHn]. Qed.

  Lemma guards_add n m (t : ictree E X) : guards (n + m)%nat t = guards n (guards m t).
  Proof. induction n; cbn [guards Nat.add]; [reflexivity|now rewrite IHn]. Qed.

  Lemma guards_guard n (t : ictree E X) : guards n (Guard t) = guards (S n) t.
  Proof. induction n; cbn [guards]; [reflexivity|now rewrite IHn]. Qed.

  Lemma guards_trans n l (t u : ictree E X) : trans l t u -> trans l (guards n t) u.
  Proof. intro H; induction n; cbn [guards]; [exact H|now apply trans_guard]. Qed.

  (** Guard prefixes are cancellative. *)
  Lemma guards_cancel : forall b c (x y : ictree E X),
    guards b x ≅ guards c y ->
    (exists d, x ≅ guards d y /\ c = (b + d)%nat) \/ (exists d, y ≅ guards d x /\ b = (c + d)%nat).
  Proof.
    induction b as [|b IH]; intros c x y H.
    - left; exists c; split; [exact H|reflexivity].
    - destruct c as [|c].
      + right; exists (S b); split; [symmetry; exact H|reflexivity].
      + cbn [guards] in H; apply equ_guard_invE in H.
        destruct (IH c x y H) as [(d & Hd & ->)|(d & Hd & ->)];
          [left|right]; exists d; split; auto.
  Qed.

  (** [guard_equ] is exactly "the same tree after finitely many guards". *)
  Lemma guard_equ_guards (t u : ictree E X) :
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

CoInductive galigned {E} {HE : Encode E} {X} : ictree E X -> ictree E X -> Prop :=
| galign_guard t u n m t' u' :
    t ≅ guards (S n) t' -> u ≅ guards (S m) u' ->
    galigned t' u' -> galigned t u
| galign_ret t u n m r :
    t ≅ guards n (Ret r) -> u ≅ guards m (Ret r) -> galigned t u
| galign_br t u n m c (k k' : fin' c -> ictree E X) :
    t ≅ guards n (Br c k) -> u ≅ guards m (Br c k') ->
    (forall i, galigned (k i) (k' i)) -> galigned t u
| galign_vis t u n m (e : E) (k k' : encode e -> ictree E X) :
    t ≅ guards n (Vis e k) -> u ≅ guards m (Vis e k') ->
    (forall x, galigned (k x) (k' x)) -> galigned t u.

Section GuardAlignment.
  Context {E : Type} {HE : Encode E} {X : Type}.

  Lemma galigned_equ (t u a b : ictree E X) :
    t ≅ a -> u ≅ b -> galigned t u -> galigned a b.
  Proof.
    intros Et Eu H; destruct H as
      [t u n m t' u' El Er H|t u n m r El Er|t u n m c k k' El Er H
      |t u n m e k k' El Er H].
    - eapply galign_guard; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
    - eapply galign_ret; [rewrite <- Et; exact El|rewrite <- Eu; exact Er].
    - eapply galign_br; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
    - eapply galign_vis; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
  Qed.

  Lemma galigned_sym : forall t u : ictree E X, galigned t u -> galigned u t.
  Proof.
    cofix IH; intros t u H; destruct H as
      [t u n m t' u' El Er H|t u n m r El Er|t u n m c k k' El Er H
      |t u n m e k k' El Er H].
    - eapply galign_guard; [exact Er|exact El|apply IH; exact H].
    - eapply galign_ret; [exact Er|exact El].
    - eapply galign_br; [exact Er|exact El|intro i; apply IH, H].
    - eapply galign_vis; [exact Er|exact El|intro x; apply IH, H].
  Qed.

  Lemma galigned_stuck : galigned (stuck : ictree E X) stuck.
  Proof.
    cofix IH.
    apply (galign_guard stuck stuck 0 0 stuck stuck);
      [exact unfold_stuck|exact unfold_stuck|exact IH].
  Qed.

  Lemma galigned_refl : forall t : ictree E X, galigned t t.
  Proof.
    cofix IH; intro t.
    destruct (observe t) as [r|c k|g|e k] eqn:Ht.
    - pose proof (observe_eq_equ t (Ret r) Ht) as Et.
      apply (galign_ret _ _ 0 0 r); exact Et.
    - pose proof (observe_eq_equ t (Br c k) Ht) as Et.
      apply (galign_br _ _ 0 0 c k k); [exact Et|exact Et|intro i; apply IH].
    - pose proof (observe_eq_equ t (Guard g) Ht) as Et.
      apply (galign_guard _ _ 0 0 g g); [exact Et|exact Et|apply IH].
    - pose proof (observe_eq_equ t (Vis e k) Ht) as Et.
      apply (galign_vis _ _ 0 0 e k k); [exact Et|exact Et|intro x; apply IH].
  Qed.

  Local Ltac head_absurd H := step in H; cbn in H; inversion H.

  Lemma galigned_match l T U :
    @trans_ E HE X l T U ->
    forall u, galigned (go T) u ->
    exists u', trans l u u' /\ galigned (go U) u'.
  Proof.
    intro TR; induction TR as
      [l inner target TR IH
      |c pick k result Eresult
      |e k answer result Eresult
      |result value Eresult]; intros u A.
    - inversion A as
        [left right n m tl tr El Er Hnext|left right n m r El Er
        |left right n m c k k' El Er Hnext|left right n m e k k' El Er Hnext];
        subst; clear A.
      + cbn [guards] in El; apply equ_guard_invE in El; destruct n as [|n].
        * cbn [guards] in El.
          assert (Ai : galigned (go (observe inner)) tr).
          { eapply galigned_equ; [|reflexivity|exact Hnext].
            transitivity inner; [symmetry; exact El|apply ictree_eta]. }
          destruct (IH tr Ai) as (next & Tnext & Anext).
          exists next; split; [rewrite Er; now apply guards_trans|exact Anext].
        * apply IH; eapply galigned_equ; [apply ictree_eta|reflexivity|].
          eapply galign_guard; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_invE in El.
        apply IH; eapply galigned_equ; [apply ictree_eta|reflexivity|].
        eapply galign_ret; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_invE in El.
        apply IH; eapply galigned_equ; [apply ictree_eta|reflexivity|].
        eapply galign_br; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_invE in El.
        apply IH; eapply galigned_equ; [apply ictree_eta|reflexivity|].
        eapply galign_vis; eassumption.
    - inversion A as
        [left right n m tl tr El Er Hnext|left right n m r El Er
        |left right n m c' kk kk' El Er Hnext|left right n m e kk kk' El Er Hnext];
        subst; clear A.
      + head_absurd El.
      + destruct n; head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El.
        pose proof (equ_br_invT El) as Ec; subst c'.
        pose proof (equ_br_invE El pick) as Ek.
        exists (kk' pick); split.
        * rewrite Er; apply guards_trans; eapply trans_br; reflexivity.
        * eapply galigned_equ; [|reflexivity|exact (Hnext pick)].
          transitivity (k pick); [symmetry; exact Ek|].
          transitivity result; [exact Eresult|apply ictree_eta].
      + destruct n; head_absurd El.
    - inversion A as
        [left right n m tl tr El Er Hnext|left right n m r El Er
        |left right n m c kk kk' El Er Hnext|left right n m e' kk kk' El Er Hnext];
        subst; clear A.
      + head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El.
        pose proof (equ_vis_invT El) as [_ Ee]; subst e'.
        pose proof (equ_vis_invE El answer) as Ek.
        exists (kk' answer); split.
        * rewrite Er; apply guards_trans; apply trans_vis.
        * eapply galigned_equ; [|reflexivity|exact (Hnext answer)].
          transitivity (k answer); [symmetry; exact Ek|].
          transitivity result; [exact Eresult|apply ictree_eta].
    - inversion A as
        [left right n m tl tr El Er Hnext|left right n m r El Er
        |left right n m c kk kk' El Er Hnext|left right n m e kk kk' El Er Hnext];
        subst; clear A.
      + head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El; apply equ_ret_inv in El; subst r.
        exists stuck; split.
        * rewrite Er; apply guards_trans, trans_ret.
        * eapply galigned_equ; [|reflexivity|exact galigned_stuck].
          transitivity result; [exact Eresult|apply ictree_eta].
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
  Qed.

  Lemma galigned_trans (t u next : ictree E X) l :
    galigned t u -> trans l t next ->
    exists other, trans l u other /\ galigned next other.
  Proof.
    intros A TR.
    assert (Ae : galigned (go (observe t)) u).
    { eapply galigned_equ; [apply ictree_eta|reflexivity|exact A]. }
    destruct (galigned_match l (observe t) (observe next) TR u Ae)
      as (other & To & Ao).
    exists other; split; [exact To|].
    eapply galigned_equ; [symmetry; apply ictree_eta|reflexivity|exact Ao].
  Qed.

  Lemma galigned_sbisim : forall t u : ictree E X, galigned t u -> t ~ u.
  Proof.
    unfold sbisim; apply_coinduction; fold_sbisim.
    intros R IH t u A; split; intros l next TR.
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

Inductive galignF {E} {HE : Encode E} {X} (R : ictree E X -> ictree E X -> Prop)
  : ictree E X -> ictree E X -> Prop :=
| galignF_guard t u n m t' u' :
    t ≅ guards (S n) t' -> u ≅ guards (S m) u' -> R t' u' -> galignF R t u
| galignF_ret t u n m r :
    t ≅ guards n (Ret r) -> u ≅ guards m (Ret r) -> galignF R t u
| galignF_br t u n m c (k k' : fin' c -> ictree E X) :
    t ≅ guards n (Br c k) -> u ≅ guards m (Br c k') ->
    (forall i, R (k i) (k' i)) -> galignF R t u
| galignF_vis t u n m (e : E) (k k' : encode e -> ictree E X) :
    t ≅ guards n (Vis e k) -> u ≅ guards m (Vis e k') ->
    (forall x, R (k x) (k' x)) -> galignF R t u.

Lemma galigned_coind {E} {HE : Encode E} {X} (R : ictree E X -> ictree E X -> Prop) :
  (forall t u, R t u -> galignF R t u) -> forall t u, R t u -> galigned t u.
Proof.
  intro Hstep; cofix CIH; intros t u H.
  destruct (Hstep t u H) as
    [t u n m t' u' El Er H'|t u n m r El Er|t u n m c k k' El Er H'
    |t u n m e k k' El Er H'].
  - exact (galign_guard t u n m t' u' El Er (CIH t' u' H')).
  - exact (galign_ret t u n m r El Er).
  - exact (galign_br t u n m c k k' El Er (fun i => CIH (k i) (k' i) (H' i))).
  - exact (galign_vis t u n m e k k' El Er (fun x => CIH (k x) (k' x) (H' x))).
Qed.

#[global] Instance guards_proper {E} {HE : Encode E} {X} n :
  Proper (equ eq ==> equ eq) (@guards E HE X n).
Proof. intros t u H; apply guards_equ, H. Qed.

Lemma guards_shift {E} {HE : Encode E} {X} n a (t : ictree E X) :
  guards n (guards (S a) t) = guards (S (n + a)) t.
Proof. rewrite <- guards_add, Nat.add_succ_r; reflexivity. Qed.


(** ** Interpretation preserves guard alignment *)
Section InterpAlign.
  Context {E F : Type} {HE : Encode E} {HF : Encode F} (h : E ~> ictree F) {X : Type}.

  Lemma interp_guards n (t : ictree E X) : interp h (guards n t) ≅ guards n (interp h t).
  Proof.
    induction n; cbn [guards]; [reflexivity|].
    rewrite interp_guard_node; apply guard_equ_node; exact IHn.
  Qed.

  Inductive interp_rel : ictree F X -> ictree F X -> Prop :=
  | interp_rel_tree n m (t u : ictree E X) T U :
      galigned t u -> T ≅ guards n (interp h t) -> U ≅ guards m (interp h u) ->
      interp_rel T U
  | interp_rel_bind n m (A : Type) (a : ictree F A) (k k' : A -> ictree E X) T U :
      (forall x, galigned (k x) (k' x)) ->
      T ≅ guards n (a >>= fun x => Guard (interp h (k x))) ->
      U ≅ guards m (a >>= fun x => Guard (interp h (k' x))) -> interp_rel T U.

  Lemma interp_rel_bind_step n m A (a : ictree F A) (k k' : A -> ictree E X) T U :
    (forall x, galigned (k x) (k' x)) ->
    T ≅ guards n (a >>= fun x => Guard (interp h (k x))) ->
    U ≅ guards m (a >>= fun x => Guard (interp h (k' x))) -> galignF interp_rel T U.
  Proof.
    intros Hk ET EU.
    destruct (observe a) as [x|c kk|g|e kk] eqn:Ha.
    - pose proof (observe_eq_equ a (Ret x) Ha) as Ea.
      apply (galignF_guard _ T U n m (interp h (k x)) (interp h (k' x))).
      + rewrite ET, Ea, bind_ret_l, guards_guard; reflexivity.
      + rewrite EU, Ea, bind_ret_l, guards_guard; reflexivity.
      + apply (interp_rel_tree 0 0 (k x) (k' x)); [apply Hk|reflexivity|reflexivity].
    - pose proof (observe_eq_equ a (Br c kk) Ha) as Ea.
      apply (galignF_br _ T U n m c (fun i => kk i >>= fun x => Guard (interp h (k x)))
                                     (fun i => kk i >>= fun x => Guard (interp h (k' x)))).
      + rewrite ET, Ea, bind_br; reflexivity.
      + rewrite EU, Ea, bind_br; reflexivity.
      + intro i; apply (interp_rel_bind 0 0 A (kk i) k k'); [exact Hk|reflexivity|reflexivity].
    - pose proof (observe_eq_equ a (Guard g) Ha) as Ea.
      apply (galignF_guard _ T U n m (g >>= fun x => Guard (interp h (k x)))
                                     (g >>= fun x => Guard (interp h (k' x)))).
      + rewrite ET, Ea, bind_guard, guards_guard; reflexivity.
      + rewrite EU, Ea, bind_guard, guards_guard; reflexivity.
      + apply (interp_rel_bind 0 0 A g k k'); [exact Hk|reflexivity|reflexivity].
    - pose proof (observe_eq_equ a (Vis e kk) Ha) as Ea.
      apply (galignF_vis _ T U n m e (fun y => kk y >>= fun x => Guard (interp h (k x)))
                                     (fun y => kk y >>= fun x => Guard (interp h (k' x)))).
      + rewrite ET, Ea, bind_vis; reflexivity.
      + rewrite EU, Ea, bind_vis; reflexivity.
      + intro y; apply (interp_rel_bind 0 0 A (kk y) k k'); [exact Hk|reflexivity|reflexivity].
  Qed.

  Lemma interp_rel_step T U : interp_rel T U -> galignF interp_rel T U.
  Proof.
    intros [n m t u T' U' A ET EU|n m B a k k' T' U' Hk ET EU].
    - destruct A as [t u a b t' u' Et Eu A|t u a b r Et Eu
        |t u a b c kk kk' Et Eu Hk|t u a b e kk kk' Et Eu Hk].
      + apply (galignF_guard _ T' U' (n + a) (m + b) (interp h t') (interp h u')).
        * rewrite ET, Et, interp_guards, guards_shift; reflexivity.
        * rewrite EU, Eu, interp_guards, guards_shift; reflexivity.
        * apply (interp_rel_tree 0 0 t' u'); [exact A|reflexivity|reflexivity].
      + apply (galignF_ret _ T' U' (n + a) (m + b) r).
        * rewrite ET, Et, interp_guards, interp_ret_node, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, interp_ret_node, <- guards_add; reflexivity.
      + apply (galignF_br _ T' U' (n + a) (m + b) c
          (fun i => Guard (interp h (kk i))) (fun i => Guard (interp h (kk' i)))).
        * rewrite ET, Et, interp_guards, interp_br_node, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, interp_br_node, <- guards_add; reflexivity.
        * intro i; apply (interp_rel_tree 1 1 (kk i) (kk' i)); [apply Hk|reflexivity|reflexivity].
      + apply (interp_rel_bind_step (n + a) (m + b) _ (h e) kk kk' T' U' Hk).
        * rewrite ET, Et, interp_guards, interp_vis_node, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_guards, interp_vis_node, <- guards_add; reflexivity.
    - exact (interp_rel_bind_step n m B a k k' T' U' Hk ET EU).
  Qed.

  Lemma interp_galigned (t u : ictree E X) :
    galigned t u -> galigned (interp h t) (interp h u).
  Proof.
    intro H; apply (galigned_coind interp_rel interp_rel_step).
    apply (interp_rel_tree 0 0 t u); [exact H|reflexivity|reflexivity].
  Qed.
End InterpAlign.

(** ** State interpretation preserves guard alignment *)
Section InterpStateAlign.
  Context {E F S : Type} {HE : Encode E} {HF : Encode F}
    (h : E ~> stateT S (ictree F)) {X : Type}.

  Lemma interp_state_guards n (t : ictree E X) s :
    interp_state h (guards n t) s ≅ guards n (interp_state h t s).
  Proof.
    induction n; cbn [guards]; [reflexivity|].
    rewrite interp_state_tau; apply guard_equ_node; exact IHn.
  Qed.

  Inductive istate_rel : ictree F (X * S) -> ictree F (X * S) -> Prop :=
  | istate_rel_tree n m (t u : ictree E X) s T U :
      galigned t u -> T ≅ guards n (interp_state h t s) ->
      U ≅ guards m (interp_state h u s) -> istate_rel T U
  | istate_rel_bind n m (A : Type) (a : ictree F (A * S)) (k k' : A -> ictree E X) T U :
      (forall x, galigned (k x) (k' x)) ->
      T ≅ guards n (a >>= fun '(x, s') => Guard (interp_state h (k x) s')) ->
      U ≅ guards m (a >>= fun '(x, s') => Guard (interp_state h (k' x) s')) ->
      istate_rel T U.

  Lemma istate_rel_bind_step n m A (a : ictree F (A * S)) (k k' : A -> ictree E X) T U :
    (forall x, galigned (k x) (k' x)) ->
    T ≅ guards n (a >>= fun '(x, s') => Guard (interp_state h (k x) s')) ->
    U ≅ guards m (a >>= fun '(x, s') => Guard (interp_state h (k' x) s')) ->
    galignF istate_rel T U.
  Proof.
    intros Hk ET EU.
    destruct (observe a) as [[x s']|c kk|g|e kk] eqn:Ha.
    - pose proof (observe_eq_equ a (Ret (x, s')) Ha) as Ea.
      apply (galignF_guard _ T U n m (interp_state h (k x) s') (interp_state h (k' x) s')).
      + rewrite ET, Ea, bind_ret_l; cbv beta iota; rewrite guards_guard; reflexivity.
      + rewrite EU, Ea, bind_ret_l; cbv beta iota; rewrite guards_guard; reflexivity.
      + apply (istate_rel_tree 0 0 (k x) (k' x) s'); [apply Hk|reflexivity|reflexivity].
    - pose proof (observe_eq_equ a (Br c kk) Ha) as Ea.
      apply (galignF_br _ T U n m c
        (fun i => kk i >>= fun '(x, s') => Guard (interp_state h (k x) s'))
        (fun i => kk i >>= fun '(x, s') => Guard (interp_state h (k' x) s'))).
      + rewrite ET, Ea, bind_br; reflexivity.
      + rewrite EU, Ea, bind_br; reflexivity.
      + intro i; apply (istate_rel_bind 0 0 A (kk i) k k'); [exact Hk|reflexivity|reflexivity].
    - pose proof (observe_eq_equ a (Guard g) Ha) as Ea.
      apply (galignF_guard _ T U n m
        (g >>= fun '(x, s') => Guard (interp_state h (k x) s'))
        (g >>= fun '(x, s') => Guard (interp_state h (k' x) s'))).
      + rewrite ET, Ea, bind_guard, guards_guard; reflexivity.
      + rewrite EU, Ea, bind_guard, guards_guard; reflexivity.
      + apply (istate_rel_bind 0 0 A g k k'); [exact Hk|reflexivity|reflexivity].
    - pose proof (observe_eq_equ a (Vis e kk) Ha) as Ea.
      apply (galignF_vis _ T U n m e
        (fun y => kk y >>= fun '(x, s') => Guard (interp_state h (k x) s'))
        (fun y => kk y >>= fun '(x, s') => Guard (interp_state h (k' x) s'))).
      + rewrite ET, Ea, bind_vis; reflexivity.
      + rewrite EU, Ea, bind_vis; reflexivity.
      + intro y; apply (istate_rel_bind 0 0 A (kk y) k k'); [exact Hk|reflexivity|reflexivity].
  Qed.

  Lemma istate_rel_step T U : istate_rel T U -> galignF istate_rel T U.
  Proof.
    intros [n m t u s T' U' A ET EU|n m B a k k' T' U' Hk ET EU].
    - destruct A as [t u a b t' u' Et Eu A|t u a b r Et Eu
        |t u a b c kk kk' Et Eu Hk|t u a b e kk kk' Et Eu Hk].
      + apply (galignF_guard _ T' U' (n + a) (m + b)
          (interp_state h t' s) (interp_state h u' s)).
        * rewrite ET, Et, interp_state_guards, guards_shift; reflexivity.
        * rewrite EU, Eu, interp_state_guards, guards_shift; reflexivity.
        * apply (istate_rel_tree 0 0 t' u' s); [exact A|reflexivity|reflexivity].
      + apply (galignF_ret _ T' U' (n + a) (m + b) (r, s)).
        * rewrite ET, Et, interp_state_guards, interp_state_ret, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_state_guards, interp_state_ret, <- guards_add; reflexivity.
      + apply (galignF_br _ T' U' (n + a) (m + b) c
          (fun i => Guard (interp_state h (kk i) s))
          (fun i => Guard (interp_state h (kk' i) s))).
        * rewrite ET, Et, interp_state_guards, interp_state_br, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_state_guards, interp_state_br, <- guards_add; reflexivity.
        * intro i; apply (istate_rel_tree 1 1 (kk i) (kk' i) s);
            [apply Hk|reflexivity|reflexivity].
      + apply (istate_rel_bind_step (n + a) (m + b) _ (runStateT (h e) s) kk kk' T' U' Hk).
        * rewrite ET, Et, interp_state_guards, interp_state_vis, <- guards_add; reflexivity.
        * rewrite EU, Eu, interp_state_guards, interp_state_vis, <- guards_add; reflexivity.
    - exact (istate_rel_bind_step n m B a k k' T' U' Hk ET EU).
  Qed.

  Lemma interp_state_galigned (t u : ictree E X) s :
    galigned t u -> galigned (interp_state h t s) (interp_state h u s).
  Proof.
    intro H; apply (galigned_coind istate_rel istate_rel_step).
    apply (istate_rel_tree 0 0 t u s); [exact H|reflexivity|reflexivity].
  Qed.
End InterpStateAlign.

(** ** The scheduler maps guard-equivalent pools to aligned trees *)
Section ScheduleAlign.
  Context {E : Type} {HE : Encode E}.

  Lemma schedule_focus_guards : forall a N (ts : pool E (S N)) i (x : thread E),
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
      rewrite (observe_eq_equ _ (Guard (schedule (S N)
        ((ts @ i := Guard (guards a x)) @ i := guards a x) (Some i)))
        (schedule_focused_guard N (ts @ i := Guard (guards a x)) i (guards a x)
          ltac:(rewrite Vector.nth_replace_eq; reflexivity))).
      rewrite Vector.replace_replace_eq.
      apply guard_equ_node.
      rewrite (IH N (ts @ i := guards a x) i x)
        by (rewrite Vector.nth_replace_eq; reflexivity).
      rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  Lemma observe_equ_go {F} {HF : Encode F} {X} (t : ictree F X) ot :
    observe t = ot -> t ≅ go ot.
  Proof. intro H; apply observe_eq_equ; exact H. Qed.

  Lemma pool_guard_equ_replace {N} (ts us : pool E N) i x :
    pool_guard_equ ts us -> pool_guard_equ (ts @ i := x) (us @ i := x).
  Proof.
    unfold pool_guard_equ; intros H; apply vector_replace_pointwise; [intros j _; apply H|reflexivity].
  Qed.

  Lemma pool_guard_equ_remove {N} (ts us : pool E (S N)) i :
    pool_guard_equ ts us -> pool_guard_equ (ts -- i) (us -- i).
  Proof. unfold pool_guard_equ; intros H; apply vector_remove_pointwise; intros j _; apply H. Qed.

  Lemma pool_guard_equ_cons {N} x (ts us : pool E N) :
    pool_guard_equ ts us -> pool_guard_equ (x :: ts) (x :: us).
  Proof. unfold pool_guard_equ; intros H; apply vector_cons_pointwise; [reflexivity|exact H]. Qed.

  Inductive sched_rel : completed E -> completed E -> Prop :=
  | sched_rel_at n m N (ts us : pool E N) f T U :
      pool_guard_equ ts us ->
      T ≅ guards n (schedule N ts f) -> U ≅ guards m (schedule N us f) ->
      sched_rel T U
  | sched_rel_pick n m N (ts us : pool E (S N)) T U :
      pool_guard_equ ts us ->
      T ≅ guards n (Br N (fun i => schedule (S N) ts (Some i))) ->
      U ≅ guards m (Br N (fun i => schedule (S N) us (Some i))) ->
      sched_rel T U.

  Lemma sched_rel_step T U : sched_rel T U -> galignF sched_rel T U.
  Proof.
    intros [n m N ts us f T' U' Hp ET EU|n m N ts us T' U' Hp ET EU].
    2: { apply (galignF_br _ T' U' n m N
           (fun i => schedule (S N) ts (Some i)) (fun i => schedule (S N) us (Some i)));
           [exact ET|exact EU|].
         intro i; apply (sched_rel_at 0 0 (S N) ts us (Some i)); [exact Hp|reflexivity|reflexivity]. }
    destruct f as [i|].
    2: { destruct N as [|N].
         - apply (galignF_ret _ T' U' n m tt).
           + rewrite ET, (observe_eq_equ _ (Ret tt) (schedule_empty_none ts)); reflexivity.
           + rewrite EU, (observe_eq_equ _ (Ret tt) (schedule_empty_none us)); reflexivity.
         - apply (galignF_vis _ T' U' n m (inl Yield)
             (fun _ => Br N (fun i => schedule (S N) ts (Some i)))
             (fun _ => Br N (fun i => schedule (S N) us (Some i)))).
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
    destruct (observe x) as [[]|c k|y|e k] eqn:Hx.
    - apply (galignF_guard _ T' U' (n + a) (m + b)
        (schedule N (ts' -- i) None) (schedule N (us' -- i) None)).
      + rewrite ET', (observe_equ_go _ _ (schedule_focused_ret N ts' i Hts)); rewrite <- guards_guard; reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_focused_ret N us' i Hus)); rewrite <- guards_guard; reflexivity.
      + apply (sched_rel_at 0 0 N (ts' -- i) (us' -- i) None);
          [apply pool_guard_equ_remove, Hp'|reflexivity|reflexivity].
    - apply (galignF_br _ T' U' (n + a) (m + b) c
        (fun j => schedule (S N) (ts' @ i := k j) (Some i))
        (fun j => schedule (S N) (us' @ i := k j) (Some i))).
      + rewrite ET', (observe_equ_go _ _ (schedule_focused_br N ts' i c k Hts)); reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_focused_br N us' i c k Hus)); reflexivity.
      + intro j; eapply (sched_rel_at 0 0 (S N) _ _ (Some i));
          [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
    - apply (galignF_guard _ T' U' (n + a) (m + b)
        (schedule (S N) (ts' @ i := y) (Some i)) (schedule (S N) (us' @ i := y) (Some i))).
      + rewrite ET', (observe_equ_go _ _ (schedule_focused_guard N ts' i y Hts)); rewrite <- guards_guard; reflexivity.
      + rewrite EU', (observe_equ_go _ _ (schedule_focused_guard N us' i y Hus)); rewrite <- guards_guard; reflexivity.
      + eapply (sched_rel_at 0 0 (S N) _ _ (Some i));
          [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
    - destruct e as [[]|[[]|e']].
      + apply (galignF_guard _ T' U' (n + a) (m + b)
          (schedule (S N) (ts' @ i := k tt) None) (schedule (S N) (us' @ i := k tt) None)).
        * rewrite ET', (observe_equ_go _ _ (schedule_focused_yield N ts' i k Hts)); rewrite <- guards_guard; reflexivity.
        * rewrite EU', (observe_equ_go _ _ (schedule_focused_yield N us' i k Hus)); rewrite <- guards_guard; reflexivity.
        * eapply (sched_rel_at 0 0 (S N) _ _ None);
            [|cbn [guards]; reflexivity|cbn [guards]; reflexivity];
            apply pool_guard_equ_replace, Hp'.
      + apply (galignF_vis _ T' U' (n + a) (m + b) (inr (inl Spawn))
          (fun _ => schedule (S (S N)) (k true :: (ts' @ i := k false)) (Some (Fin.FS i)))
          (fun _ => schedule (S (S N)) (k true :: (us' @ i := k false)) (Some (Fin.FS i)))).
        * rewrite ET', (observe_equ_go _ _ (schedule_focused_fork N ts' i k Hts)); reflexivity.
        * rewrite EU', (observe_equ_go _ _ (schedule_focused_fork N us' i k Hus)); reflexivity.
        * intros _; eapply (sched_rel_at 0 0 (S (S N)) _ _ (Some (Fin.FS i)));
            [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_cons, pool_guard_equ_replace, Hp'.
      + apply (galignF_vis _ T' U' (n + a) (m + b) (inr (inr e'))
          (fun z => schedule (S N) (ts' @ i := k z) (Some i))
          (fun z => schedule (S N) (us' @ i := k z) (Some i))).
        * rewrite ET', (observe_equ_go _ _ (schedule_focused_user_event N ts' i e' k Hts)); reflexivity.
        * rewrite EU', (observe_equ_go _ _ (schedule_focused_user_event N us' i e' k Hus)); reflexivity.
        * intro z; eapply (sched_rel_at 0 0 (S N) _ _ (Some i));
            [|cbn [guards]; reflexivity|cbn [guards]; reflexivity]; apply pool_guard_equ_replace, Hp'.
  Qed.

  Lemma schedule_galigned N (ts us : pool E N) f :
    pool_guard_equ ts us -> galigned (schedule N ts f) (schedule N us f).
  Proof.
    intro H; apply (galigned_coind sched_rel sched_rel_step).
    apply (sched_rel_at 0 0 N ts us f); [exact H|reflexivity|reflexivity].
  Qed.

  (** The erased scheduled view of guard-equivalent pools is aligned. *)
  Lemma erased_schedule_galigned N (ts us : pool E N) f :
    pool_guard_equ ts us ->
    galigned (interp_yield (interp_spawn (schedule N ts f)))
             (interp_yield (interp_spawn (schedule N us f))).
  Proof.
    intro H; unfold interp_yield, interp_spawn.
    apply interp_galigned, interp_galigned, schedule_galigned, H.
  Qed.
End ScheduleAlign.
