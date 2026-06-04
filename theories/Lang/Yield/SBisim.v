From Stdlib Require Import Fin Program.Equality.
From TICL Require Import
  ICTree.Core
  ICTree.Trans
  ICTree.Equ
  ICTree.Eq.Core
  ICTree.Eq.Bind
  ICTree.SBisim
  Lang.Yield.Events
  Lang.Yield.Vec
  Lang.Yield.Scheduler
  Lang.Yield.Denote
  Lang.Yield.Interp
  Lang.Yield.Ticl.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

Section PoolSBisim.
  Context {E : Type} `{Encode E}.

  Definition pool_sbisim {n : nat} (v1 v2 : pool E n) : Prop :=
    forall i, v1 i ~ v2 i.

  Lemma pool_sbisim_refl {n} (v : pool E n) : pool_sbisim v v.
  Proof. intro i; reflexivity. Qed.

  Lemma pool_sbisim_sym {n} (v1 v2 : pool E n) :
    pool_sbisim v1 v2 -> pool_sbisim v2 v1.
  Proof. intros Hpool i; symmetry; apply Hpool. Qed.

  Lemma replace_pool_sbisim {n} (v1 v2 : pool E n) (i : Fin.t n)
        (t1 t2 : thread E) :
    pool_sbisim v1 v2 ->
    t1 ~ t2 ->
    pool_sbisim (replace_pool v1 i t1) (replace_pool v2 i t2).
  Proof.
    intros Hv Ht j.
    unfold replace_pool.
    destruct (Fin.eq_dec i j); auto.
  Qed.

  Lemma remove_pool_sbisim {n} (v1 v2 : pool E (S n)) (i : Fin.t (S n)) :
    pool_sbisim v1 v2 ->
    pool_sbisim (remove_pool v1 i) (remove_pool v2 i).
  Proof.
    intros Hv j.
    revert v1 v2 i j Hv.
    induction n as [| n IH]; intros v1 v2 i j Hv.
    - dependent destruction j.
    - cbn.
      dependent destruction i.
      + apply Hv.
      + dependent destruction j.
        * apply Hv.
        * apply IH. intro k. apply Hv.
  Qed.

  Lemma cons_pool_sbisim {n} (t1 t2 : thread E) (v1 v2 : pool E n) :
    t1 ~ t2 ->
    pool_sbisim v1 v2 ->
    pool_sbisim (cons_pool t1 v1) (cons_pool t2 v2).
  Proof.
    intros Ht Hv i.
    refine (Fin.caseS' i (fun i => cons_pool t1 v1 i ~ cons_pool t2 v2 i) _ _).
    - exact Ht.
    - intro j. apply Hv.
  Qed.

  (** ** [equ]-level pool congruences, used by [schedule_pool_proper]. *)
  Definition pool_equ {n : nat} (v1 v2 : pool E n) : Prop :=
    forall i, v1 i ≅ v2 i.

  Lemma replace_pool_equ {n} (v1 v2 : pool E n) (i : Fin.t n)
        (t1 t2 : thread E) :
    pool_equ v1 v2 ->
    t1 ≅ t2 ->
    pool_equ (replace_pool v1 i t1) (replace_pool v2 i t2).
  Proof.
    intros Hv Ht j.
    unfold replace_pool.
    destruct (Fin.eq_dec i j); auto.
  Qed.

  Lemma remove_pool_equ {n} (v1 v2 : pool E (S n)) (i : Fin.t (S n)) :
    pool_equ v1 v2 ->
    pool_equ (remove_pool v1 i) (remove_pool v2 i).
  Proof.
    intros Hv j.
    revert v1 v2 i j Hv.
    induction n as [| n IH]; intros v1 v2 i j Hv.
    - dependent destruction j.
    - cbn.
      dependent destruction i.
      + apply Hv.
      + dependent destruction j.
        * apply Hv.
        * apply IH. intro k. apply Hv.
  Qed.

  Lemma cons_pool_equ {n} (t1 t2 : thread E) (v1 v2 : pool E n) :
    t1 ≅ t2 ->
    pool_equ v1 v2 ->
    pool_equ (cons_pool t1 v1) (cons_pool t2 v2).
  Proof.
    intros Ht Hv i.
    refine (Fin.caseS' i (fun i => cons_pool t1 v1 i ≅ cons_pool t2 v2 i) _ _).
    - exact Ht.
    - intro j. apply Hv.
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

  Lemma trans_schedule_no_focus_choose n (v : pool E (S n)) (i : Fin.t (S n)) :
    trans tau
      (Br n (fun i => schedule (S n) v (Some i)))
      (schedule (S n) v (Some i)).
  Proof.
    apply trans_br with (x := i). reflexivity.
  Qed.

  Lemma trans_schedule_focused_yield n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inl Yield) k ->
    trans (obs (inl Yield : yieldE + (spawnE + E)) tt)
      (schedule (S n) v (Some i))
      (Br n (fun j => schedule (S n) (replace_pool v i (k tt)) (Some j))).
  Proof.
    intro Hobs.
    unfold trans; lazy [schedule observe _observe].
    change (@_observe _ _ unit (v i)) with (observe (v i)).
    rewrite Hobs.
    eapply Stepguard.
    eapply (@Stepobs
      (yieldE + (spawnE + E)) _ unit
      (inl Yield) _ tt
      (Br n (fun j => schedule (S n) (replace_pool v i (k tt)) (Some j)))).
    reflexivity.
  Qed.

  Lemma trans_schedule_focused_fork n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inr (inl Fork)) k ->
    trans (obs (inr (inl Spawn) : yieldE + (spawnE + E)) tt)
      (schedule (S n) v (Some i))
      (schedule (S (S n))
         (cons_pool (k true) (replace_pool v i (k false)))
         (Some (Fin.FS i))).
  Proof.
    intro Hobs.
    unfold trans; lazy [schedule observe _observe].
    change (@_observe _ _ unit (v i)) with (observe (v i)).
    rewrite Hobs.
    eapply (@Stepobs
      (yieldE + (spawnE + E)) _ unit
      (inr (inl Spawn)) _ tt
      (schedule (S (S n))
         (cons_pool (k true) (replace_pool v i (k false)))
         (Some (Fin.FS i)))).
    reflexivity.
  Qed.

  Lemma trans_schedule_focused_user_event
        n (v : pool E (S n)) (i : Fin.t (S n)) e k x :
    observe (v i) = VisF (inr (inr e)) k ->
    trans (obs (inr (inr e) : yieldE + (spawnE + E)) x)
      (schedule (S n) v (Some i))
      (schedule (S n) (replace_pool v i (k x)) (Some i)).
  Proof.
    intro Hobs.
    unfold trans; lazy [schedule observe _observe].
    change (@_observe _ _ unit (v i)) with (observe (v i)).
    rewrite Hobs.
    eapply (@Stepobs
      (yieldE + (spawnE + E)) _ unit
      (inr (inr e)) _ x
      (schedule (S n) (replace_pool v i (k x)) (Some i))).
    reflexivity.
  Qed.

  Lemma trans_schedule_focused_br
        n (v : pool E (S n)) (i : Fin.t (S n)) b k (j : Fin.t (S b)) :
    observe (v i) = BrF b k ->
    trans tau (schedule (S n) v (Some i))
      (schedule (S n) (replace_pool v i (k j)) (Some i)).
  Proof.
    intro Hobs.
    unfold trans; lazy [schedule observe _observe].
    change (@_observe _ _ unit (v i)) with (observe (v i)).
    rewrite Hobs.
    eapply (@Steptau
      (yieldE + (spawnE + E)) _ unit b j _
      (schedule (S n) (replace_pool v i (k j)) (Some i))).
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
    observe (v i) = RetF tt ->
    schedule (S n) v (Some i) ≅ Guard (schedule n (remove_pool v i) None).
  Proof.
    intro Hobs.
    rewrite (ictree_eta (schedule (S n) v (Some i))).
    rewrite (schedule_focused_ret _ v i Hobs).
    reflexivity.
  Qed.

  Lemma trans_schedule_focused_guard n (v : pool E (S n)) (i : Fin.t (S n)) t :
    observe (v i) = GuardF t ->
    schedule (S n) v (Some i)
      ≅ Guard (schedule (S n) (replace_pool v i t) (Some i)).
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

  Lemma trans_schedule_focused_inv n (v : pool E (S n)) (i : Fin.t (S n)) l t' :
    trans l (schedule (S n) v (Some i)) t' ->
    (** focused [Ret]: collapse the [Guard], step the residual pool *)
    (observe (v i) = RetF tt /\
       trans l (schedule n (remove_pool v i) None) t')
    \/
    (** focused [Guard]: collapse, step the [replace_pool] residual *)
    (exists g, observe (v i) = GuardF g /\
       trans l (schedule (S n) (replace_pool v i g) (Some i)) t')
    \/
    (** focused [Br b k]: [tau] to one of the branches *)
    (exists b k (j : Fin.t (S b)), observe (v i) = BrF b k /\
       l = tau /\
       t' ≅ schedule (S n) (replace_pool v i (k j)) (Some i))
    \/
    (** focused [Yield]: visible [Yield], [Br] back over the residual pool *)
    (exists k, observe (v i) = VisF (inl Yield) k /\
       l = obs (inl Yield : yieldE + (spawnE + E)) tt /\
       t' ≅ Br n (fun j =>
              schedule (S n) (replace_pool v i (k tt)) (Some j)))
    \/
    (** focused [Fork]: visible [Spawn], cons the child, focus it *)
    (exists k, observe (v i) = VisF (inr (inl Fork)) k /\
       l = obs (inr (inl Spawn) : yieldE + (spawnE + E)) tt /\
       t' ≅ schedule (S (S n))
              (cons_pool (k true) (replace_pool v i (k false)))
              (Some (Fin.FS i)))
    \/
    (** focused user event [e]: visible [e], step the focused thread *)
    (exists e k x, observe (v i) = VisF (inr (inr e)) k /\
       l = obs (inr (inr e) : yieldE + (spawnE + E)) x /\
       t' ≅ schedule (S n) (replace_pool v i (k x)) (Some i)).
  Proof.
    intro TR.
    destruct (observe (v i)) as [r | b k | g | e k] eqn:Hobs.
    - (* RetF *)
      destruct r.
      left.
      split; auto.
      rewrite (trans_schedule_focused_ret _ v i Hobs) in TR.
      now apply trans_guard_inv in TR.
    - (* BrF b k *)
      do 2 right; left.
      assert (Hsch := schedule_focused_br _ v i b k Hobs).
      rewrite (ictree_eta (schedule (S n) v (Some i))) in TR.
      rewrite Hsch in TR.
      apply trans_br_inv in TR as (j & Heq & Hl).
      exists b, k, j; auto.
    - (* GuardF g *)
      right; left.
      exists g.
      split; auto.
      rewrite (trans_schedule_focused_guard _ v i g Hobs) in TR.
      now apply trans_guard_inv in TR.
    - (* VisF e k *)
      destruct e as [yld | [frk | usr]].
      + (* Yield *)
        destruct yld.
        do 3 right; left.
        exists k.
        split; auto.
        rewrite (ictree_eta (schedule (S n) v (Some i))) in TR.
        rewrite (schedule_focused_yield _ v i k Hobs) in TR.
        apply trans_guard_inv in TR.
        rewrite schedule_no_focus_equ in TR.
        apply trans_vis_inv in TR as (x & Heq & Hl).
        destruct x.
        split; auto.
      + (* Fork *)
        destruct frk.
        do 4 right; left.
        exists k.
        split; auto.
        rewrite (ictree_eta (schedule (S n) v (Some i))) in TR.
        rewrite (schedule_focused_fork _ v i k Hobs) in TR.
        apply trans_vis_inv in TR as (x & Heq & Hl).
        destruct x.
        split; auto.
      + (* user event *)
        do 5 right.
        rewrite (ictree_eta (schedule (S n) v (Some i))) in TR.
        rewrite (schedule_focused_user_event _ v i usr k Hobs) in TR.
        apply trans_vis_inv in TR as (x & Heq & Hl).
        exists usr, k, x; auto.
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
      assert (Hgo : go (observe (v i)) ≅ go (observe (w i))).
      { rewrite <- !ictree_eta. exact Hi. }
      rewrite (ictree_eta (schedule (S n') v (Some i))).
      rewrite (ictree_eta (schedule (S n') w (Some i))).
      destruct (observe (v i)) as [r | b k | g | e k] eqn:Hv;
      destruct (observe (w i)) as [r2 | b2 k2 | g2 | e2 k2] eqn:Hw;
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
    pool_equ (replace_pool v i b) (replace_pool (replace_pool v i a) i b).
  Proof. intro j. unfold replace_pool. destruct (Fin.eq_dec i j); reflexivity. Qed.

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
    trans (obs (inl Yield : yieldE + (forkE + E)) tt) (v i) u ->
    trans (obs (inl Yield : yieldE + (spawnE + E)) tt)
      (schedule (S n) v (Some i))
      (Br n (fun j => schedule (S n) (replace_pool v i u) (Some j))).
  Proof.
    intro TR.
    unfold trans in TR.
    remember (observe (v i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (obs (inl Yield : yieldE + (forkE + E)) tt) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR; intros.
    - (* Stepguard: observe (v i) = GuardF t *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      apply trans_guard.
      rewrite (br_schedule_pool_equ (replace_pool v i u0)
                 (replace_pool (replace_pool v i t) i u0)
                 (replace_pool_idem_equ v i t u0)).
      apply (IHTR (replace_pool v i t) i u0).
      + now rewrite replace_pool_hit.
      + exact Hou.
      + exact Hlbl.
    - discriminate Hlbl.
    - (* Stepobs *)
      dependent destruction Hlbl.
      assert (Hu0 : u ≅ k tt).
      { transitivity t.
        - rewrite (ictree_eta u), (ictree_eta t), <- Hou; reflexivity.
        - symmetry; assumption. }
      rewrite (br_schedule_pool_equ (replace_pool v i u)
                 (replace_pool v i (k tt))
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
    trans (obs (inr (inr e) : yieldE + (forkE + E)) x) (v i) u ->
    trans (obs (inr (inr e) : yieldE + (spawnE + E)) x)
      (schedule (S n) v (Some i))
      (schedule (S n) (replace_pool v i u) (Some i)).
  Proof.
    intro TR.
    unfold trans in TR.
    remember (observe (v i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (obs (inr (inr e) : yieldE + (forkE + E)) x) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR; intros.
    - (* Stepguard *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      apply trans_guard.
      rewrite (schedule_some_pool_equ (replace_pool v i u0)
                 (replace_pool (replace_pool v i t) i u0) i
                 (replace_pool_idem_equ v i t u0)).
      apply (IHTR (replace_pool v i t) i u0).
      + now rewrite replace_pool_hit.
      + exact Hou.
      + exact Hlbl.
    - discriminate Hlbl.
    - (* Stepobs *)
      dependent destruction Hlbl.
      assert (Hu0 : u ≅ k x).
      { transitivity t.
        - rewrite (ictree_eta u), (ictree_eta t), <- Hou; reflexivity.
        - symmetry; assumption. }
      rewrite (schedule_some_pool_equ (replace_pool v i u)
                 (replace_pool v i (k x)) i
                 (replace_pool_equ v v i u (k x) (pool_equ_refl v) Hu0)).
      apply (trans_schedule_focused_user_event n v i e k x (eq_sym Hot)).
    - discriminate Hlbl.
  Qed.

  Lemma schedule_lift_tau n (v : pool E (S n)) (i : Fin.t (S n))
        (u : thread E) :
    trans tau (v i) u ->
    trans tau
      (schedule (S n) v (Some i))
      (schedule (S n) (replace_pool v i u) (Some i)).
  Proof.
    intro TR.
    unfold trans in TR.
    remember (observe (v i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (tau : label (yieldE + (forkE + E))) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR; intros.
    - (* Stepguard *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      apply trans_guard.
      rewrite (schedule_some_pool_equ (replace_pool v i u0)
                 (replace_pool (replace_pool v i t) i u0) i
                 (replace_pool_idem_equ v i t u0)).
      apply (IHTR (replace_pool v i t) i u0).
      + now rewrite replace_pool_hit.
      + exact Hou.
      + exact Hlbl.
    - (* Steptau *)
      assert (Hu0 : u ≅ k x).
      { transitivity t.
        - rewrite (ictree_eta u), (ictree_eta t), <- Hou; reflexivity.
        - symmetry; assumption. }
      rewrite (schedule_some_pool_equ (replace_pool v i u)
                 (replace_pool v i (k x)) i
                 (replace_pool_equ v v i u (k x) (pool_equ_refl v) Hu0)).
      apply (trans_schedule_focused_br n v i n0 k x (eq_sym Hot)).
    - discriminate Hlbl.
    - discriminate Hlbl.
  Qed.

  Lemma schedule_lift_fork n (v : pool E (S n)) (i : Fin.t (S n))
        (b : bool) (u : thread E) :
    trans (obs (inr (inl Fork) : yieldE + (forkE + E)) b) (v i) u ->
    exists k2,
      (forall c : bool,
         trans (obs (inr (inl Fork) : yieldE + (forkE + E)) c) (v i) (k2 c)) /\
      trans (obs (inr (inl Spawn) : yieldE + (spawnE + E)) tt)
        (schedule (S n) v (Some i))
        (schedule (S (S n))
           (cons_pool (k2 true) (replace_pool v i (k2 false)))
           (Some (Fin.FS i))).
  Proof.
    intro TR.
    unfold trans in TR.
    remember (observe (v i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (obs (inr (inl Fork) : yieldE + (forkE + E)) b) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR; intros.
    - (* Stepguard *)
      destruct (IHTR (replace_pool v i t) i u0
                  ltac:(now rewrite replace_pool_hit) Hou Hlbl)
        as (k2 & Hcont & Hstep).
      exists k2. split.
      + intro c. specialize (Hcont c).
        rewrite replace_pool_hit in Hcont.
        rewrite (ictree_eta (v i)), <- Hot.
        now apply trans_guard.
      + rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
        apply trans_guard.
        rewrite (schedule_pool_proper (S (S n))
                   (cons_pool (k2 true) (replace_pool v i (k2 false)))
                   (cons_pool (k2 true)
                      (replace_pool (replace_pool v i t) i (k2 false)))
                   (Some (Fin.FS i))).
        * exact Hstep.
        * apply cons_pool_equ; [reflexivity |].
          apply replace_pool_idem_equ.
    - discriminate Hlbl.
    - (* Stepobs *)
      dependent destruction Hlbl.
      exists k. split.
      + intro c.
        rewrite (ictree_eta (v i)), <- Hot.
        apply trans_vis.
      + apply (trans_schedule_focused_fork n v i k (eq_sym Hot)).
    - discriminate Hlbl.
  Qed.

  Lemma cast_refl m (i : Fin.t m) : Fin.cast i eq_refl = i.
  Proof. induction i; cbn; [reflexivity | now rewrite IHi]. Qed.

  Lemma remove_pool_agree {n} :
    forall (v w : pool E (S n)) (i : Fin.t (S n)),
    (forall j, i <> j -> v j ≅ w j) ->
    pool_equ (remove_pool v i) (remove_pool w i).
  Proof.
    induction n as [| n IH]; intros v w i Hag j.
    - dependent destruction j.
    - cbn. dependent destruction i.
      + apply Hag. intro Hc; discriminate.
      + dependent destruction j.
        * apply Hag. intro Hc; discriminate.
        * apply IH. intros k Hik.
          rewrite (cast_refl _ i) in Hik.
          apply Hag. intro Heq. apply Hik.
          apply Fin.FS_inj. exact Heq.
  Qed.

  Lemma remove_replace_pool_equ {n} (v : pool E (S n)) (i : Fin.t (S n))
        (a : thread E) :
    pool_equ (remove_pool (replace_pool v i a) i) (remove_pool v i).
  Proof.
    apply remove_pool_agree. intros j Hij.
    rewrite replace_pool_miss; [reflexivity | exact Hij].
  Qed.

  Lemma schedule_lift_ret n (v : pool E (S n)) (i : Fin.t (S n))
        (u : thread E) :
    trans (val tt : label (yieldE + (forkE + E))) (v i) u ->
    schedule (S n) v (Some i) ~ schedule n (remove_pool v i) None.
  Proof.
    intro TR.
    unfold trans in TR.
    remember (observe (v i)) as ot eqn:Hot.
    remember (observe u) as ou eqn:Hou.
    remember (val tt : label (yieldE + (forkE + E))) as lbl eqn:Hlbl.
    revert v i u Hot Hou Hlbl.
    induction TR; intros.
    - (* Stepguard *)
      rewrite (trans_schedule_focused_guard n v i t (eq_sym Hot)).
      rewrite sb_guard.
      rewrite (IHTR (replace_pool v i t) i u0
                 ltac:(now rewrite replace_pool_hit) Hou Hlbl).
      now rewrite (schedule_pool_proper n (remove_pool (replace_pool v i t) i)
               (remove_pool v i) None (remove_replace_pool_equ v i t)).
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
        destruct (observe (v1 i)) as [r0 | b0 k0 | g | e0 k0] eqn:Hvi.
        * (* Ret: recurse on the smaller pool *)
          destruct r0.
          rewrite (schedule_focused_ret n' v1 i Hvi) in Hos.
          dependent destruction Hos.
          destruct (IHTR n' (remove_pool v1 i) (remove_pool v2 i) None t'
                      eq_refl Hot' (remove_pool_sbisim v1 v2 i Hpool))
            as (u' & Htru & Hresu).
          assert (Hvr : v1 i ≅ Ret tt).
          { rewrite (ictree_eta (v1 i)), Hvi. reflexivity. }
          assert (Htrv : trans (val tt : label (yieldE + (forkE + E)))
                           (v1 i) stuck).
          { rewrite Hvr. apply trans_ret. }
          destruct (sbisim_trans (v1 i) (v2 i) stuck (val tt) eq
                      (Hpool i) Htrv) as (lv & uv & Htr2v & Hlv & Hsbv).
          subst lv.
          assert (Hlift : schedule (S n') v2 (Some i)
                          ~ schedule n' (remove_pool v2 i) None).
          { apply (schedule_lift_ret n' v2 i uv Htr2v). }
          destruct (sbisim_trans (schedule n' (remove_pool v2 i) None)
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
          apply (IHTR (S n') (replace_pool v1 i g) v2 (Some i) t'
                   eq_refl Hot').
          intro j. unfold replace_pool. destruct (Fin.eq_dec i j) as [Hij | Hij].
          -- subst j.
             assert (Hvg : v1 i ≅ Guard g).
             { rewrite (ictree_eta (v1 i)), Hvi. reflexivity. }
             transitivity (v1 i); [| apply Hpool].
             rewrite Hvg. symmetry. apply sb_guard.
          -- apply Hpool.
        * (* Vis: Yield (Guard head), or Fork / user (Vis head) *)
          destruct e0 as [yld | [frk | usr]].
          -- (* Yield: invert the focused-yield residual directly *)
             destruct yld.
             rewrite (schedule_focused_yield n' v1 i k0 Hvi) in Hos.
             dependent destruction Hos.
             assert (TR0 : trans l
               (schedule (S n') (replace_pool v1 i (k0 tt)) None) t').
             { unfold trans. rewrite <- Hot'. exact TR. }
             apply trans_schedule_no_focus_inv in TR0 as (Hl & Hbr).
             subst l.
             assert (Hvis : v1 i ≅ Vis (inl Yield) k0).
             { rewrite (ictree_eta (v1 i)), Hvi. reflexivity. }
             assert (Htry : trans
               (obs (inl Yield : yieldE + (forkE + E)) tt) (v1 i) (k0 tt)).
             { rewrite Hvis. apply trans_vis. }
             destruct (sbisim_trans (v1 i) (v2 i) (k0 tt)
                         (obs (inl Yield : yieldE + (forkE + E)) tt) eq
                         (Hpool i) Htry) as (ly & uy & Htr2y & Hly & Hsby).
             subst ly.
             exists (Br n' (fun j =>
               schedule (S n') (replace_pool v2 i uy) (Some j))). split.
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
        destruct (observe (v1 i)) as [r0 | b0 k0 | g | e0 k0] eqn:Hvi.
        * destruct r0. rewrite (schedule_focused_ret n' v1 i Hvi) in Hos.
          discriminate Hos.
        * rewrite (schedule_focused_br n' v1 i b0 k0 Hvi) in Hos.
          dependent destruction Hos.
          assert (Htr1 : trans tau (v1 i) (k0 x)).
          { rewrite (ictree_eta (v1 i)), Hvi.
            apply trans_br with (x := x). reflexivity. }
          destruct (sbisim_trans (v1 i) (v2 i) (k0 x) tau eq (Hpool i) Htr1)
            as (l' & u' & Htr2 & Hl' & Hsb).
          subst l'.
          exists (schedule (S n') (replace_pool v2 i u') (Some i)). split.
          -- apply schedule_lift_tau. exact Htr2.
          -- assert (Ht' : t' ≅ schedule (S n') (replace_pool v1 i (k0 x)) (Some i)).
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
        destruct (observe (v1 i)) as [r0 | b0 k0 | g | e1 k0] eqn:Hvi.
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
             assert (Hvis : v1 i ≅ Vis (inr (inl Fork)) k0).
             { rewrite (ictree_eta (v1 i)), Hvi. reflexivity. }
             assert (Htrf : trans
               (obs (inr (inl Fork) : yieldE + (forkE + E)) false) (v1 i)
               (k0 false)).
             { rewrite Hvis. apply trans_vis. }
             destruct (sbisim_trans (v1 i) (v2 i) (k0 false)
                         (obs (inr (inl Fork)) false) eq (Hpool i) Htrf)
               as (lf & uf & Htr2 & Hlf & Hsbf).
             subst lf.
             destruct (schedule_lift_fork n' v2 i false uf Htr2)
               as (kf & Hforall & Hstep).
             exists (schedule (S (S n'))
                       (cons_pool (kf true) (replace_pool v2 i (kf false)))
                       (Some (Fin.FS i))).
             split.
             ++ exact Hstep.
             ++ assert (Ht' : t' ≅ schedule (S (S n'))
                  (cons_pool (k0 true) (replace_pool v1 i (k0 false)))
                  (Some (Fin.FS i))).
                { rewrite (ictree_eta t'), <- Hot', <- (ictree_eta t).
                  symmetry; assumption. }
                rewrite Ht'.
                assert (Hii : v2 i ~ v1 i) by (symmetry; apply Hpool).
                assert (Hkf : forall c, k0 c ~ kf c).
                { intro c.
                  destruct (sbisim_trans (v2 i) (v1 i) (kf c)
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
             assert (Hvis : v1 i ≅ Vis (inr (inr usr)) k0).
             { rewrite (ictree_eta (v1 i)), Hvi. reflexivity. }
             assert (Htru : trans
               (obs (inr (inr usr) : yieldE + (forkE + E)) x) (v1 i) (k0 x)).
             { rewrite Hvis. apply trans_vis. }
             destruct (sbisim_trans (v1 i) (v2 i) (k0 x)
                         (obs (inr (inr usr) : yieldE + (forkE + E)) x) eq
                         (Hpool i) Htru)
               as (lu & u' & Htr2 & Hlu & Hsbu).
             subst lu.
             exists (schedule (S n') (replace_pool v2 i u') (Some i)). split.
             ++ apply (schedule_lift_user n' v2 i usr x u' Htr2).
             ++ assert (Ht' : t' ≅
                  schedule (S n') (replace_pool v1 i (k0 x)) (Some i)).
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
        destruct (observe (v1 i)) as [r0 | b k | g | e k] eqn:Hvi.
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

(** ** Phase 6: scheduler-visible denotation respects thread bisimilarity. *)

(** Two source statements with strongly-bisimilar thread denotations yield
    strongly-bisimilar scheduler-visible computations.  This is the singleton
    instance of [sbisim_schedule] for the start-up pool of [scheduled_visible]. *)
Corollary sbisim_scheduled_visible (s1 s2 : YStmt) :
  denote_stmt s1 ~ denote_stmt s2 ->
  scheduled_visible s1 ~ scheduled_visible s2.
Proof.
  intro Hs.
  unfold scheduled_visible.
  apply sbisim_schedule.
  intro i. exact Hs.
Qed.
