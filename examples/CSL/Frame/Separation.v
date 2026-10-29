(** * Regression proofs for the CoCSL owned machine and modal splitting.

    Concrete forked [CProg] programs over [init_owned]/[project]:
    - [NextRegression]: the direct AN split, own-clock AX/EX, its necessary
      boundaries, and the last-finisher [hRet] disjunction;
    - [HeapRegression]: nested-fork lineage, CAS/free success and fault
      reflection, and non-confined foreign reads;
    - [AlwaysRegression]: AG release certificates, one fair EG execution, and
      the non-yielding and guard-only boundaries;
    - [FiniteRegression]: finite AU/EU splits, the erased raw trace through
      [owned_fork_erasure], local versus global emission indices, read-only
      context, and rejected allocation/assignment. *)

From Stdlib Require Import List Lia Fin Vector Relations Program.Equality.
From CTree Require Import CTree Eq.
From TICL Require Import Lang.CoCSL.Separation Logic.Tactics Logic.World.
From TICL Require Import CTree.Interp.Yield.SBisim Utils.Vectors Utils.Pcm Events.HeapModel.

(** ** Next: the direct AN split, its clocks, and its boundaries *)
Module NextRegression.
Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

Definition ctx0 : Ctx.Ctx := List.nil.
Definition hC : ManagedHeap := (hsingle 1 0, hemp).
Definition hP : ManagedHeap := (hsingle 2 7, hemp).
Definition hC' : ManagedHeap := (upd (fst hC) 1 1, snd hC).
Definition hP' : ManagedHeap := (upd (fst hP) 2 8, snd hP).

Definition cell (i : side) (a v : nat) : hprop := fun c => fst (oc_heap c i) a = Some v.
Definition Fnone : hprop := fun c => tp_focus (oc_pool c) = None.

Lemma cell_view i a v : view_pred (cell i a v).
Proof.
  intros c d (Hh & _) H; unfold cell in *.
  destruct (Hh i) as [H1 _]; rewrite <- (H1 a); exact H.
Qed.

Lemma cell_proper i a v : hproper (cell i a v).
Proof. apply view_pred_proper, cell_view. Qed.

Lemma cell_stable i a v : SelectionStable (cell i a v).
Proof. apply view_selection_stable, cell_view. Qed.

Lemma Fnone_proper : hproper Fnone.
Proof.
  intros c d ((_ & Hf) & _); unfold Fnone, focus_nat in *.
  destruct (tp_focus (oc_pool c)), (tp_focus (oc_pool d)); cbn in Hf;
    split; intro; congruence.
Qed.

(** Thread heads of the denoted programs. *)
Lemma denote_write a v :
  denote (CWrite a v) ≅ guards 0 (Vis (inr1 (inr1 (inl1 (HWrite a v))) : CEff unit) (fun _ => Ret tt)).
Proof. exact (source_raw_write_head a v (fun _ => Ret tt)). Qed.

Definition parentY : CProg unit := CBind CYield (fun _ => CWrite 2 8).

Lemma denote_yield_write :
  denote parentY ≅ guards 0 (Vis (inl1 Yield : CEff unit) (fun _ => denote (CWrite 2 8))).
Proof.
  unfold denote, parentY; etransitivity; [apply source_raw_bind|].
  exact (source_raw_yield_head _).
Qed.

Local Ltac chg X := lazymatch goal with |- _ <-> ?R => change (X <-> R) end.

Lemma ret_guards (t : thread sE Bn) : t ≅ Ret tt -> t ≅ guards 0 (Ret tt).
Proof. exact (fun H => H). Qed.

(** Admission of both forks. *)
Lemma hC_hP_disj : hC # hP.
Proof.
  split; intro x; cbn; unfold hsingle, hemp; [|left; reflexivity].
  destruct (PeanoNat.Nat.eq_dec 1 x) as [<-|]; [right|left; reflexivity].
  destruct (PeanoNat.Nat.eq_dec 2 1); [discriminate|reflexivity].
Qed.

Lemma admA : admissible (CWrite 1 1) ((fun _ : unit => CWrite 2 8) tt) hC hP ctx0 0.
Proof.
  apply admissible_intro; try apply managed_wf_preallocated; try apply hC_hP_disj;
    cbn; try exact I; discriminate.
Qed.

Lemma admB : admissible (CWrite 1 1) parentY hC hP ctx0 0.
Proof.
  apply admissible_intro; try apply managed_wf_preallocated; try apply hC_hP_disj;
    cbn; repeat split; try exact I; try discriminate; intros _; discriminate.
Qed.

(** *** The run [Parent(write, return); Child(select, write, return)] *)

Definition dc := denote (CWrite 1 1).
Definition dp := denote (CWrite 2 8).

Definition A0 := init_owned (CWrite 1 1) (CWrite 2 8) hC hP ctx0 0.
Definition A1 (t : thread sE Bn) :=
  set_pool (set_heap A0 Parent hP') (mk_pool 2 [dc; t] [Child; Parent] (Some (FS F1))).
Definition A2 := set_pool (set_heap A0 Parent hP') (mk_pool 1 [dc] [Child] None).
Definition A3 := set_pool (set_heap A0 Parent hP') (mk_pool 1 [dc] [Child] (Some F1)).
Definition A4 (t : thread sE Bn) :=
  set_pool (set_heap (set_heap A0 Parent hP') Child hC') (mk_pool 1 [t] [Child] (Some F1)).
Definition A5 := set_pool (set_heap (set_heap A0 Parent hP') Child hC') (mk_pool 0 [] [] None).

Lemma stepA0 a c' :
  owned_step A0 a c' <-> a = act Parent OAWrite /\ exists t, t ≅ Ret tt /\ c' = A1 t.
Proof.
  chg (focus_step A0 1 [dc; dp] [Child; Parent] (FS F1) a c').
  rewrite (focus_step_head_prim A0 1 [dc; dp] [Child; Parent] (FS F1) _ _ _ a c' (denote_write 2 8)).
  split.
  - intros (k & kind & y & c1 & Hk & Hp & -> & ->); cbn in Hp.
    injection Hp as <- <- <-; split; [reflexivity|].
    exists (k tt); split; [apply Hk|reflexivity].
  - intros (-> & t & Ht & ->).
    exists (fun _ => t), OAWrite, tt, (set_heap A0 Parent hP'); repeat split; try reflexivity.
    intros _; exact Ht.
Qed.

Lemma stepA1 t a c' : t ≅ Ret tt ->
  owned_step (A1 t) a c' <-> a = act Parent OAReturn /\ c' = A2.
Proof.
  intro Ht.
  chg (focus_step (A1 t) 1 [dc; t] [Child; Parent] (FS F1) a c').
  rewrite (focus_step_head_ret (A1 t) 1 [dc; t] [Child; Parent] (FS F1) 0 a c' (ret_guards t Ht)).
  rewrite !vector_remove_tail, !vector_remove_head; reflexivity.
Qed.

Lemma stepA2 a c' : owned_step A2 a c' <-> a = act Child OASelect /\ c' = A3.
Proof.
  chg (sel_step A2 0 [dc] [Child] a c'); unfold sel_step; split.
  - intros (j & -> & ->); dependent destruction j; [split; reflexivity|inversion j].
  - intros (-> & ->); exists F1; split; reflexivity.
Qed.

Lemma stepA3 a c' :
  owned_step A3 a c' <-> a = act Child OAWrite /\ exists t, t ≅ Ret tt /\ c' = A4 t.
Proof.
  chg (focus_step A3 0 [dc] [Child] F1 a c').
  rewrite (focus_step_head_prim A3 0 [dc] [Child] F1 _ _ _ a c' (denote_write 1 1)).
  split.
  - intros (k & kind & y & c1 & Hk & Hp & -> & ->); cbn in Hp.
    injection Hp as <- <- <-; split; [reflexivity|].
    exists (k tt); split; [apply Hk|reflexivity].
  - intros (-> & t & Ht & ->).
    exists (fun _ => t), OAWrite, tt, (set_heap A3 Child hC'); repeat split; try reflexivity.
    intros _; exact Ht.
Qed.

Lemma stepA4 t a c' : t ≅ Ret tt ->
  owned_step (A4 t) a c' <-> a = act Child OAReturn /\ c' = A5.
Proof.
  intro Ht.
  chg (focus_step (A4 t) 0 [t] [Child] F1 a c').
  rewrite (focus_step_head_ret (A4 t) 0 [t] [Child] F1 0 a c' (ret_guards t Ht)).
  rewrite !vector_remove_head; reflexivity.
Qed.

Lemma sA0 : owned_step A0 (act Parent OAWrite) (A1 (Ret tt)).
Proof. apply stepA0; split; [reflexivity|exists (Ret tt); split; reflexivity]. Qed.
Lemma sA1 : owned_step (A1 (Ret tt)) (act Parent OAReturn) A2.
Proof. apply stepA1; [reflexivity|split; reflexivity]. Qed.
Lemma sA2 : owned_step A2 (act Child OASelect) A3.
Proof. apply stepA2; split; reflexivity. Qed.
Lemma sA3 : owned_step A3 (act Child OAWrite) (A4 (Ret tt)).
Proof. apply stepA3; split; [reflexivity|exists (Ret tt); split; reflexivity]. Qed.
Lemma sA4 : owned_step (A4 (Ret tt)) (act Child OAReturn) A5.
Proof. apply stepA4; [reflexivity|split; reflexivity]. Qed.

Lemma wfA0 : owned_wf A0.
Proof. apply init_owned_wf; try apply managed_wf_preallocated; apply hC_hP_disj. Qed.
Lemma wfA1 t : t ≅ Ret tt -> owned_wf (A1 t).
Proof. intro Ht; eapply owned_step_wf; [exact wfA0|apply stepA0; eauto]. Qed.
Lemma wfA2 : owned_wf A2.
Proof. eapply owned_step_wf; [apply (wfA1 (Ret tt)); reflexivity|exact sA1]. Qed.
Lemma wfA3 : owned_wf A3.
Proof. eapply owned_step_wf; [exact wfA2|exact sA2]. Qed.
Lemma wfA4 t : t ≅ Ret tt -> owned_wf (A4 t).
Proof. intro Ht; eapply owned_step_wf; [exact wfA3|apply stepA3; eauto]. Qed.
Lemma wfA5 : owned_wf A5.
Proof. eapply owned_step_wf; [apply (wfA4 (Ret tt)); reflexivity|exact sA4]. Qed.

(** The global AN premise: every next state keeps the anchored split, the
    child's cell untouched and the parent's cell written. *)
Lemma A_global_han :
  hAN owned_next (hsep hTrue hTrue) (hsep (cell Child 1 0) (cell Parent 2 8)) A0.
Proof.
  apply hAN_iff; split; [split; [exact wfA0|split; exact I]|split].
  - exists (A1 (Ret tt)), (act Parent OAWrite); exact sA0.
  - intros c' (a & Ha); apply stepA0 in Ha as (_ & t & Ht & ->).
    split; [exact (wfA1 t Ht)|split; reflexivity].
Qed.

(** The two-program AN frame theorem on the source fork: the child still owes
    its selection, the parent is focused. *)
Lemma A_fork_han :
  hAN owned_next hTrue (cell Child 1 0) (init_local Child (CWrite 1 1) hC ctx0 0 false) /\
  hAN owned_next hTrue (cell Parent 2 8) (init_local Parent (CWrite 2 8) hP ctx0 0 true).
Proof.
  apply (fork_han_split (CWrite 1 1) (fun _ => CWrite 2 8) hC hP ctx0 0 hTrue hTrue);
    try apply hTrue_proper; try apply cell_proper; try apply cell_stable.
  - exact admA.
  - exact A_global_han.
Qed.

(** The child's first own action is its selection; the parent's is its write. *)
Lemma A_child_first a d :
  owned_step (init_local Child (CWrite 1 1) hC ctx0 0 false) a d ->
  a = act Child OASelect /\ cell Child 1 0 d.
Proof. intros [-> ->]%init_local_select; split; reflexivity. Qed.

Lemma A_parent_first a d :
  owned_step (init_local Parent (CWrite 2 8) hP ctx0 0 true) a d -> a = act Parent OAWrite.
Proof.
  intro H; change (focus_step (init_local Parent (CWrite 2 8) hP ctx0 0 true) 0 [dp] [Parent] F1 a d) in H.
  rewrite (focus_step_head_prim _ 0 [dp] [Parent] F1 _ _ _ a d (denote_write 2 8)) in H.
  destruct H as (k & kind & y & c1 & _ & Hp & -> & _); cbn in Hp; now injection Hp as <- _ _.
Qed.

(** *** The child's own-action clock *)

Lemma rt_no_foreign i c mid :
  (forall a c', owned_step c a c' -> owner a = i) ->
  clos_refl_trans _ (foreign_next i) c mid -> mid = c.
Proof.
  intros Hown H; apply clos_rt_rt1n in H; destruct H as [|y z (a & Hs & Ho) _];
    [reflexivity|].
  exfalso; exact (Ho (Hown _ _ Hs)).
Qed.

Lemma foreign_star_A0 mid :
  clos_refl_trans _ (foreign_next Child) A0 mid ->
  mid = A0 \/ (exists t, t ≅ Ret tt /\ mid = A1 t) \/ mid = A2.
Proof.
  intro H; apply clos_rt_rtn1 in H; induction H as [|y z Hyz _ IH];
    [left; reflexivity|].
  destruct Hyz as (a & Hs & Ho); destruct IH as [->|[(t & Ht & ->)| ->]].
  - apply stepA0 in Hs as (_ & t & Ht & ->); right; left; eauto.
  - apply (stepA1 t a z Ht) in Hs as (_ & ->); right; right; reflexivity.
  - apply stepA2 in Hs as (-> & _); contradiction.
Qed.

Lemma weak_A0 c' : weak_next Child A0 c' <-> c' = A3.
Proof.
  split.
  - intros (mid & Hmid & a & Hs & Ho).
    destruct (foreign_star_A0 mid Hmid) as [->|[(t & Ht & ->)| ->]].
    + apply stepA0 in Hs as (-> & _); discriminate.
    + apply (stepA1 t a c' Ht) in Hs as (-> & _); discriminate.
    + apply stepA2 in Hs as (_ & ->); reflexivity.
  - intros ->; exists A2; split.
    + eapply rt_trans; apply rt_step; eexists; split; [exact sA0| |exact sA1|]; discriminate.
    + exists (act Child OASelect); split; [exact sA2|reflexivity].
Qed.

Lemma weak_A3 c' : weak_next Child A3 c' <-> exists t, t ≅ Ret tt /\ c' = A4 t.
Proof.
  split.
  - intros (mid & Hmid & a & Hs & _).
    rewrite (rt_no_foreign Child A3 mid) in Hs
      by (exact Hmid || (intros ? ? H; apply stepA3 in H as (-> & _); reflexivity)).
    now apply stepA3 in Hs as (_ & H).
  - intros (t & Ht & ->); exists A3; split; [apply rt_refl|].
    exists (act Child OAWrite); split; [apply stepA3; eauto|reflexivity].
Qed.

(** The child's first own action keeps cell 1 at 0: the weak clock agrees with
    the projected local AX. *)
Lemma A_weak_ax_select :
  hAX (weak_next Child) (at_side Child (cell Child 1 0)) A0 /\
  hAX owned_next (cell Child 1 0) (project Child A0).
Proof.
  assert (H : hAX (weak_next Child) (at_side Child (cell Child 1 0)) A0).
  { apply hAN_iff; split; [exact I|split].
    - exists A3; apply weak_A0; reflexivity.
    - intros c' ->%weak_A0; reflexivity. }
  split; [exact H|apply weak_hax_to_local; [apply cell_proper|exact H]].
Qed.

(** Its second own action writes cell 1. *)
Lemma A_weak_ax2 :
  hAX (weak_next Child) (hAX (weak_next Child) (at_side Child (cell Child 1 1))) A0.
Proof.
  apply hAN_iff; split; [exact I|split].
  - exists A3; apply weak_A0; reflexivity.
  - intros c' ->%weak_A0; apply hAN_iff; split; [exact I|split].
    + exists (A4 (Ret tt)); apply weak_A3; eauto.
    + intros c' (t & _ & ->)%weak_A3; reflexivity.
Qed.

Lemma A_weak_ex2 :
  hEX (weak_next Child) (hEX (weak_next Child) (at_side Child (cell Child 1 1))) A0.
Proof.
  apply hEN_iff; split; [exact I|exists A3; split; [apply weak_A0; reflexivity|]].
  apply hEN_iff; split; [exact I|exists (A4 (Ret tt)); split; [apply weak_A3; eauto|reflexivity]].
Qed.

(** *** Boundary (a): a selection-sensitive target defeats the split *)

Lemma Fnone_not_stable : ~ SelectionStable Fnone.
Proof.
  intro H.
  specialize (H (init_local Child (CWrite 1 1) hC ctx0 0 false) (act Child OASelect)
    (init_local Child (CWrite 1 1) hC ctx0 0 true)
    (proj2 (init_local_select _ _ _ _ _ _ _) (conj eq_refl eq_refl)) eq_refl).
  assert (Hn : Fnone (init_local Child (CWrite 1 1) hC ctx0 0 true)) by (apply H; reflexivity).
  discriminate Hn.
Qed.

Lemma Fnone_defeats_split :
  hproper Fnone /\
  hAN owned_next (hsep hTrue hTrue) (hsep Fnone (cell Parent 2 8)) A0 /\
  ~ hAN owned_next hTrue Fnone (init_local Child (CWrite 1 1) hC ctx0 0 false).
Proof.
  split; [exact Fnone_proper|split].
  - apply hAN_iff; split; [split; [exact wfA0|split; exact I]|split].
    + exists (A1 (Ret tt)), (act Parent OAWrite); exact sA0.
    + intros c' (a & Ha); apply stepA0 in Ha as (_ & t & Ht & ->).
      split; [exact (wfA1 t Ht)|split; reflexivity].
  - intros (_ & _ & H)%hAN_iff.
    assert (Hn : Fnone (init_local Child (CWrite 1 1) hC ctx0 0 true)).
    { apply H; exists (act Child OASelect); apply init_local_select; split; reflexivity. }
    discriminate Hn.
Qed.

(** *** Boundary (b): the child conclusion must keep its pending selection *)

Definition L1 := set_pool (set_heap (init_local Child (CWrite 1 1) hC ctx0 0 true) Child hC')
  (mk_pool 1 [Ret tt] [Child] (Some F1)).

Lemma A_focused_child_fails :
  ~ hAN owned_next hTrue (cell Child 1 0) (init_local Child (CWrite 1 1) hC ctx0 0 true).
Proof.
  intros (_ & _ & H)%hAN_iff.
  assert (Hn : cell Child 1 0 L1).
  { apply H; exists (act Child OAWrite).
    change (focus_step (init_local Child (CWrite 1 1) hC ctx0 0 true) 0 [dc] [Child] F1
      (act Child OAWrite) L1).
    apply (focus_step_head_prim _ 0 [dc] [Child] F1 _ _ _ _ _ (denote_write 1 1)).
    exists (fun _ => Ret tt), OAWrite, tt,
      (set_heap (init_local Child (CWrite 1 1) hC ctx0 0 true) Child hC');
      repeat split; reflexivity. }
  change (Some 1 = Some 0) in Hn; discriminate Hn.
Qed.

(** *** Boundary (c): after the parent finishes, its empty projection has no
    next step although the survivor satisfies global AN *)

Lemma A_finished_parent :
  coupled A2 /\ tp_size (oc_pool (project Parent A2)) = 0 /\
  hAN owned_next (hsep hTrue hTrue) (hsep hTrue hTrue) A2 /\
  ~ hAN owned_next hTrue hTrue (project Parent A2).
Proof.
  assert (Hz : tp_size (oc_pool (project Parent A2)) = 0) by reflexivity.
  split; [|split; [exact Hz|split]].
  - eapply coupled_step; [eapply coupled_step; [apply coupled_init, admA|exact sA0]|exact sA1].
  - apply hAN_iff; split; [split; [exact wfA2|split; exact I]|split].
    + exists A3, (act Child OASelect); exact sA2.
    + intros c' (a & Ha); apply stepA2 in Ha as (_ & ->); split; [exact wfA3|split; exact I].
  - intros (_ & (c' & a & Hs) & _)%hAN_iff; exact (owned_step_empty _ a c' Hz Hs).
Qed.

(** *** The symmetric case: the parent yields first *)

Definition B0 := init_owned (CWrite 1 1) parentY hC hP ctx0 0.
Definition B1 := set_pool B0 (mk_pool 2 [dc; dp] [Child; Parent] None).
Definition B2 := set_pool B0 (mk_pool 2 [dc; dp] [Child; Parent] (Some F1)).

Lemma sB0 : owned_step B0 (act Parent OAYield) B1.
Proof.
  change (focus_step B0 1 [dc; denote parentY] [Child; Parent] (FS F1) (act Parent OAYield) B1).
  apply (focus_step_head_yield B0 1 [dc; denote parentY] [Child; Parent] (FS F1) _ 0 _ _
    denote_yield_write).
  exists (fun _ => dp); repeat split; reflexivity.
Qed.

Lemma sB1 : owned_step B1 (act Child OASelect) B2.
Proof. exists F1; split; reflexivity. Qed.

Lemma coupledB2 : coupled B2.
Proof.
  eapply coupled_step; [eapply coupled_step; [apply coupled_init, admB|exact sB0]|exact sB1].
Qed.

Lemma B_global_han :
  hAN owned_next (hsep hTrue hTrue) (hsep (cell Child 1 1) (cell Parent 2 7)) B2.
Proof.
  pose proof (coupled_wf _ coupledB2) as Hwf.
  apply hAN_iff; split; [split; [exact Hwf|split; exact I]|split].
  - exists (set_pool (set_heap B2 Child hC') (mk_pool 2 [Ret tt; dp] [Child; Parent] (Some F1))),
      (act Child OAWrite).
    change (focus_step B2 1 [dc; dp] [Child; Parent] F1 (act Child OAWrite)
      (set_pool (set_heap B2 Child hC') (mk_pool 2 [Ret tt; dp] [Child; Parent] (Some F1)))).
    apply (focus_step_head_prim B2 1 [dc; dp] [Child; Parent] F1 _ _ _ _ _ (denote_write 1 1)).
    exists (fun _ => Ret tt), OAWrite, tt, (set_heap B2 Child hC'); repeat split; reflexivity.
  - intros c' (a & Ha); pose proof (owned_step_wf _ _ _ Hwf Ha) as Hwf'.
    change (focus_step B2 1 [dc; dp] [Child; Parent] F1 a c') in Ha.
    apply (focus_step_head_prim B2 1 [dc; dp] [Child; Parent] F1 _ _ _ _ _ (denote_write 1 1)) in Ha.
    destruct Ha as (k & kind & y & c1 & _ & Hp & -> & ->); cbn in Hp.
    injection Hp as <- <- <-; split; [exact Hwf'|split; reflexivity].
Qed.

Lemma B_han_split :
  hAN owned_next hTrue (cell Child 1 1) (project Child B2) /\
  hAN owned_next hTrue (cell Parent 2 7) (project Parent B2).
Proof.
  apply global_han_split; try apply hTrue_proper; try apply cell_proper; try apply cell_stable.
  - exact coupledB2.
  - apply PeanoNat.Nat.lt_0_succ.
  - apply PeanoNat.Nat.lt_0_succ.
  - exact B_global_han.
Qed.

(** The yielded parent's projection owes a selection, so "focus is None" is
    not its next-state property. *)
Lemma B_parent_Fnone_fails : ~ hAN owned_next hTrue Fnone (project Parent B2).
Proof.
  intros (_ & _ & H)%hAN_iff.
  unshelve epose proof (H _ _) as Hn.
  2: { exists (act Parent OASelect); exists F1; split; reflexivity. }
  unfold Fnone in Hn; cbn in Hn; discriminate Hn.
Qed.

(** *** Return suffixes: only the last finisher returns *)

Lemma A_global_hret :
  hRet owned_next (hsep (cell Child 1 1) (cell Parent 2 8)) (A4 (Ret tt)).
Proof.
  exists (result A5); split; [exists A5, (act Child OAReturn); exact sA4|].
  intros c' (a & Ha); apply stepA4 in Ha as (_ & ->); [|reflexivity].
  split; [reflexivity|split].
  - repeat split; intros; try apply peq_refl; reflexivity.
  - split; [exact wfA5|split; reflexivity].
Qed.

Lemma A_hret_split :
  (hRet owned_next (cell Child 1 1) (project Child (A4 (Ret tt))) /\
   hDone (cell Parent 2 8) (project Parent (A4 (Ret tt)))) \/
  (hDone (cell Child 1 1) (project Child (A4 (Ret tt))) /\
   hRet owned_next (cell Parent 2 8) (project Parent (A4 (Ret tt)))).
Proof. apply global_hret_split; try apply cell_proper; exact A_global_hret. Qed.

Lemma A_not_both_hret :
  ~ (hRet owned_next (cell Child 1 1) (project Child (A4 (Ret tt))) /\
     hRet owned_next (cell Parent 2 8) (project Parent (A4 (Ret tt)))).
Proof.
  intros (_ & (_ & (c' & a & Hs) & _)).
  exact (owned_step_empty (project Parent (A4 (Ret tt))) a c' eq_refl Hs).
Qed.

End NextRegression.

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Relations Program.Equality.
From Coinduction Require Import all.
From TICL Require Import Lang.CoCSL.Separation.
From TICL Require Import CTree.Core Utils.Pcm Utils.Vectors
  CTree.Interp.Yield.SBisim CTree.Interp.Yield.Nondeterministic CTree.Logic.Sim.

Module HeapRegression.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

(** ** One-step constructors of the owned machine and reachability *)

Definition reach : relation OwnedCfg := clos_refl_trans _ owned_next.

Lemma ostep_select c n v g j :
  oc_pool c = mk_pool (S n) v g None ->
  owned_step c (act (g $ j) OASelect) (set_pool c (mk_pool (S n) v g (Some j))).
Proof. intros H; apply (owned_step_sel _ _ _ _ _ _ H); exists j; split; reflexivity. Qed.

Lemma ostep_yield c n v g j k v' :
  oc_pool c = mk_pool (S n) v g (Some j) ->
  (v $ j) ≅ Vis (inl1 Yield : CEff unit) k -> (v @ j := k tt) = v' ->
  owned_step c (act (g $ j) OAYield) (set_pool c (mk_pool (S n) v' g None)).
Proof.
  intros H Hh <-; apply (owned_step_focus _ _ _ _ _ _ _ H).
  right; left; exists k; split; [exists 0; exact Hh|split; reflexivity].
Qed.

Lemma ostep_fork c n v g j k v' :
  oc_pool c = mk_pool (S n) v g (Some j) ->
  (v $ j) ≅ Vis (inr1 (inl1 Fork) : CEff bool) k -> (v @ j := k false) = v' ->
  owned_step c (act (g $ j) OAFork)
    (set_pool c (mk_pool (S (S n)) (k true :: v') ((g $ j) :: g) (Some (Fin.FS j)))).
Proof.
  intros H Hh <-; apply (owned_step_focus _ _ _ _ _ _ _ H).
  right; right; left; exists k; split; [exists 0; exact Hh|split; reflexivity].
Qed.

Lemma ostep_ret c n v g j v' g' :
  oc_pool c = mk_pool (S n) v g (Some j) ->
  (v $ j) ≅ Ret tt -> (v -- j) = v' -> (g -- j) = g' ->
  owned_step c (act (g $ j) OAReturn) (set_pool c (mk_pool n v' g' None)).
Proof.
  intros H Hh <- <-; apply (owned_step_focus _ _ _ _ _ _ _ H).
  right; right; right; left; split; [exists 0; exact Hh|split; reflexivity].
Qed.

Lemma ostep_prim c n v g j Y (e : sE Y) k kind y c1 v' :
  oc_pool c = mk_pool (S n) v g (Some j) ->
  (v $ j) ≅ Vis (inr1 (inr1 e) : CEff Y) k ->
  prim_step (g $ j) c e = Some (kind, y, c1) -> (v @ j := k y) = v' ->
  owned_step c (act (g $ j) kind) (set_pool c1 (mk_pool (S n) v' g (Some j))).
Proof.
  intros H Hh Hp <-; apply (owned_step_focus _ _ _ _ _ _ _ H).
  right; right; right; right.
  exists Y, e, k, kind, y, c1; split; [exists 0; exact Hh|auto].
Qed.

Lemma reach_step c a c' d : owned_step c a c' -> reach c' d -> reach c d.
Proof. intros H R; eapply rt_trans; [apply rt_step; exists a; exact H|exact R]. Qed.

Lemma reach_wf c d : owned_wf c -> reach c d -> owned_wf d.
Proof.
  intros Hc R; induction R as [x y [a H]|x|x y z _ IH1 _ IH2]; auto.
  exact (owned_step_wf _ _ _ Hc H).
Qed.

(** ** Source heads *)

Lemma denote_write_head a v :
  denote (CWrite a v) ≅ Vis (inr1 (inr1 (inl1 (HWrite a v))) : CEff unit) (fun _ => Ret tt).
Proof. exact (source_raw_write_head a v (fun _ => Ret tt)). Qed.

Lemma denote_read_bind_head a (next : nat -> CProg unit) :
  denote (CBind (CRead a) next) ≅
    Vis (inr1 (inr1 (inl1 (HRead a))) : CEff nat) (fun v => denote (next v)).
Proof. unfold denote at 1; rewrite source_raw_bind; exact (source_raw_read_head a _). Qed.

Lemma denote_free_head b :
  denote (CFree b) ≅ Vis (inr1 (inr1 (inl1 (HFree b))) : CEff unit) (fun _ => Ret tt).
Proof. exact (source_raw_free_head b (fun _ => Ret tt)). Qed.

Lemma denote_cas_bind_head a old desired (next : bool -> CProg unit) :
  denote (CBind (CCAS (CLit a) (CLit old) (CLit desired)) next) ≅
    Vis (inr1 (inr1 (inl1 (HCAS a old desired))) : CEff bool) (fun b => denote (next b)).
Proof. unfold denote at 1; rewrite source_raw_bind; exact (source_raw_cas_head a old desired _). Qed.

Lemma denote_yield_head : denote CYield ≅ Vis (inl1 Yield : CEff unit) (fun _ => Ret tt).
Proof. exact (source_raw_yield_head (fun _ => Ret tt)). Qed.

Lemma denote_yield_bind_head (next : unit -> CProg unit) :
  denote (CBind CYield next) ≅ Vis (inl1 Yield : CEff unit) (fun _ => denote (next tt)).
Proof. unfold denote at 1; rewrite source_raw_bind; exact (source_raw_yield_head _). Qed.

Lemma denote_free_bind_head b (next : unit -> CProg unit) :
  denote (CBind (CFree b) next) ≅
    Vis (inr1 (inr1 (inl1 (HFree b))) : CEff unit) (fun _ => denote (next tt)).
Proof. unfold denote at 1; rewrite source_raw_bind; exact (source_raw_free_head b _). Qed.

Ltac head :=
  cbn -[denote];
  first [ reflexivity
        | apply denote_write_head | apply denote_read_bind_head | apply denote_free_head
        | apply denote_cas_bind_head | apply denote_yield_bind_head | apply denote_yield_head
        | apply denote_free_bind_head | apply denote_fork_bind ].

(** One concrete action of the focused or selected slot. *)
Ltac ostep :=
  eapply reach_step;
  [ first
      [ eapply ostep_prim; [reflexivity|head|reflexivity|reflexivity]
      | eapply ostep_ret; [reflexivity|head|reflexivity|reflexivity]
      | eapply ostep_yield; [reflexivity|head|reflexivity]
      | eapply ostep_fork; [reflexivity|head|reflexivity] ]
  |].

Tactic Notation "oselect" uconstr(j) := eapply reach_step; [eapply (ostep_select _ _ _ _ j); reflexivity|].

(** [owned_equ] of two projections with computable (empty or equal) pools. *)
Ltac owned_equ_proj :=
  split; [split; [cbn; constructor|reflexivity]|];
  split; [intros [|]; apply peq_refl|];
  split; [intros [|]; apply peq_refl|];
  split; [reflexivity|]; split; [reflexivity|];
  split; intros [|]; reflexivity.

Lemma hsingle_disj a b v w : a <> b -> hdisj (hsingle a v) (hsingle b w).
Proof.
  intros Hab x; unfold hsingle.
  destruct (Nat.eq_dec a x); [right|left; reflexivity].
  destruct (Nat.eq_dec b x); [congruence|reflexivity].
Qed.

(** ** Nested fork: lineage under insertion, removal and both schedules *)

(** The child forks a writer of cell [1], yields, and writes cell [1] again;
    the parent writes its own cell [2]. *)
Definition nchild : CProg unit :=
  CBind (CFork (CWrite 1 1)) (fun _ => CBind CYield (fun _ => CWrite 1 2)).
Definition nparent : CProg unit := CWrite 2 8.
Definition nh : ManagedHeap := (hsingle 1 0, hemp).
Definition nh' : ManagedHeap := (hsingle 2 7, hemp).
Definition n0 : OwnedCfg := init_owned nchild nparent nh nh' List.nil 0.

Lemma nested_admissible : admissible nchild nparent nh nh' List.nil 0.
Proof.
  apply admissible_intro.
  - apply managed_wf_preallocated.
  - apply managed_wf_preallocated.
  - split; [apply hsingle_disj; discriminate|apply hdisj_hemp].
  - cbn; tauto.
  - cbn; tauto.
  - cbn; repeat split; discriminate.
  - cbn; discriminate.
Qed.

Lemma n0_wf : owned_wf n0.
Proof.
  apply init_owned_wf; try apply managed_wf_preallocated.
  split; [apply hsingle_disj; discriminate|apply hdisj_hemp].
Qed.

(** The parent wrote and returned; the child is selected before its fork. *)
Definition n_fork : OwnedCfg :=
  set_pool (set_heap n0 Parent (upd (hsingle 2 7) 2 8, hemp))
    (mk_pool 1 [denote nchild] [Child] (Some Fin.F1)).

Lemma n_fork_reach : reach n0 n_fork.
Proof. ostep; ostep; oselect Fin.F1; apply rt_refl. Qed.

(** The nested fork inserts the spawned writer in front, tags both
    descendants [Child], keeps the forker focused, and leaves the Parent
    projection unchanged. *)
Lemma nested_fork_insert a c' :
  owned_step n_fork a c' ->
  a = act Child OAFork /\
  (exists k : bool -> thread sE Bn,
     (forall b, k b ≅ (if b then denote (CWrite 1 1)
                       else denote (CBind CYield (fun _ => CWrite 1 2)))) /\
     c' = set_pool n_fork (mk_pool 2 [k true; k false] [Child; Child] (Some (Fin.FS Fin.F1)))) /\
  tp_size (oc_pool (project Child c')) = 2 /\
  owned_equ (project Parent c') (project Parent n_fork).
Proof.
  intros H.
  apply (owned_step_focus _ 0 [denote nchild] [Child] Fin.F1) in H; [|reflexivity].
  apply (focus_step_head_fork n_fork 0 [denote nchild] [Child] Fin.F1 _ 0 _ _ (denote_fork_bind _ _)) in H.
  destruct H as (k & Hk & -> & ->).
  split; [reflexivity|]; split; [exists k; split; [exact Hk|reflexivity]|].
  split; [reflexivity|].
  owned_equ_proj.
Qed.

(** After the fork and the forker's yield: two Child writers, unfocused. *)
Definition n_sched : OwnedCfg :=
  set_pool n_fork
    (mk_pool 2 [denote (CWrite 1 1); denote (CWrite 1 2)] [Child; Child] None).

Lemma n_sched_reach : reach n0 n_sched.
Proof.
  eapply rt_trans; [exact n_fork_reach|].
  ostep; ostep; apply rt_refl.
Qed.

(** The two legal schedules after the inserted yield: select either Child
    writer. *)
Lemma nested_schedules a c' :
  owned_step n_sched a c' ->
  a = act Child OASelect /\
  (c' = set_pool n_sched (mk_pool 2 [denote (CWrite 1 1); denote (CWrite 1 2)] [Child; Child]
                            (Some Fin.F1)) \/
   c' = set_pool n_sched (mk_pool 2 [denote (CWrite 1 1); denote (CWrite 1 2)] [Child; Child]
                            (Some (Fin.FS Fin.F1)))).
Proof.
  intros H.
  apply (owned_step_sel _ 1 [denote (CWrite 1 1); denote (CWrite 1 2)] [Child; Child]) in H;
    [|reflexivity].
  destruct H as (j & -> & ->).
  dependent destruction j; [split; [reflexivity|left; reflexivity]|].
  dependent destruction j; [split; [reflexivity|right; reflexivity]|inversion j].
Qed.

(** The spawned writer finished: its removal keeps the survivor [Child]. *)
Definition n_remove : OwnedCfg :=
  set_pool (set_heap n_sched Child (upd (hsingle 1 0) 1 1, hemp))
    (mk_pool 2 [Ret tt; denote (CWrite 1 2)] [Child; Child] (Some Fin.F1)).

Lemma n_remove_reach : reach n0 n_remove.
Proof.
  eapply rt_trans; [exact n_sched_reach|].
  oselect Fin.F1; ostep; apply rt_refl.
Qed.

Lemma nested_remove a c' :
  owned_step n_remove a c' ->
  a = act Child OAReturn /\
  c' = set_pool n_remove (mk_pool 1 [denote (CWrite 1 2)] [Child] None) /\
  owned_equ (project Parent c') (project Parent n_fork).
Proof.
  intros H.
  apply (owned_step_focus _ 1 [Ret tt; denote (CWrite 1 2)] [Child; Child] Fin.F1) in H;
    [|reflexivity].
  apply (focus_step_head_ret n_remove 1 [Ret tt; denote (CWrite 1 2)] [Child; Child] Fin.F1 0 _ _ (reflexivity _)) in H.
  destruct H as [-> ->].
  split; [reflexivity|]; split; [reflexivity|].
  owned_equ_proj.
Qed.

(** Both schedules terminate, keep ownership and the Parent projection, and
    race within the Child lineage: cell [1] ends at [2] or at [1]. *)
Lemma nested_schedule_spawned_first :
  exists d, reach n_sched d /\ tp_size (oc_pool d) = 0 /\ owned_wf d /\
    fst (oc_heap d Child) 1 = Some 2 /\ fst (oc_heap d Parent) 2 = Some 8 /\
    owned_equ (project Parent d) (project Parent n_fork).
Proof.
  eexists; split.
  { oselect Fin.F1; ostep; ostep; oselect Fin.F1; ostep; ostep; apply rt_refl. }
  split; [reflexivity|].
  split.
  { eapply reach_wf; [exact n0_wf|]. eapply rt_trans; [exact n_sched_reach|].
    oselect Fin.F1; ostep; ostep; oselect Fin.F1; ostep; ostep; apply rt_refl. }
  split; [reflexivity|]; split; [reflexivity|].
  owned_equ_proj.
Qed.

Lemma nested_schedule_forker_first :
  exists d, reach n_sched d /\ tp_size (oc_pool d) = 0 /\ owned_wf d /\
    fst (oc_heap d Child) 1 = Some 1 /\ fst (oc_heap d Parent) 2 = Some 8 /\
    owned_equ (project Parent d) (project Parent n_fork).
Proof.
  eexists; split.
  { oselect (Fin.FS Fin.F1); ostep; ostep; oselect Fin.F1; ostep; ostep; apply rt_refl. }
  split; [reflexivity|].
  split.
  { eapply reach_wf; [exact n0_wf|]. eapply rt_trans; [exact n_sched_reach|].
    oselect (Fin.FS Fin.F1); ostep; ostep; oselect Fin.F1; ostep; ostep; apply rt_refl. }
  split; [reflexivity|]; split; [reflexivity|].
  owned_equ_proj.
Qed.

(** ** Free, CAS and faults on allocated blocks *)

Definition bC : ManagedHeap := (hsingle 1 0, hsingle 1 1).
Definition bP : ManagedHeap := (hsingle 2 7, hsingle 2 1).

Lemma managed_wf_block a v : 0 < a -> managed_wf (hsingle a v, hsingle a 1).
Proof.
  intros Ha; split; cbn; unfold hsingle.
  - intros b n Hb; destruct (Nat.eq_dec a b) as [<-|]; [|discriminate].
    injection Hb as <-; split; [exact Ha|split; [lia|]].
    intros x Hx; assert (x = a) as -> by lia.
    destruct (Nat.eq_dec a a); [discriminate|congruence].
  - intros b1 n1 b2 n2 H1 H2 Hne.
    destruct (Nat.eq_dec a b1), (Nat.eq_dec a b2); try discriminate; congruence.
Qed.

Lemma blocks_disj : bC # bP.
Proof. split; apply hsingle_disj; discriminate. Qed.

(** The parent yields at once; the child is then selected while the parent
    block stays live. *)
Definition b0 (p : CProg unit) : OwnedCfg := init_owned p CYield bC bP List.nil 0.
Definition bfocus (p : CProg unit) : OwnedCfg :=
  set_pool (b0 p) (mk_pool 2 [denote p; Ret tt] [Child; Parent] (Some Fin.F1)).

Lemma bfocus_reach p : reach (b0 p) (bfocus p).
Proof. ostep; oselect Fin.F1; apply rt_refl. Qed.

Lemma bfocus_coupled p : component_ok p -> addr_ok bC p -> coupled (bfocus p).
Proof.
  intros Hok Haddr.
  exists p, CYield, bC, bP, List.nil, 0, (bfocus p); split; [|split; [apply bfocus_reach|reflexivity]].
  apply admissible_intro; try exact Hok; try exact Haddr; try apply blocks_disj;
    try (apply managed_wf_block; lia); cbn; tauto.
Qed.

Lemma prim_read_none c a : fst (oc_heap c Child) a = None -> prim_step Child c (inl1 (HRead a)) = None.
Proof. intros H; cbn; rewrite H; reflexivity. Qed.

Lemma prim_free_none c b : managed_free (oc_heap c Child) b = None -> prim_step Child c (inl1 (HFree b)) = None.
Proof. intros H; cbn; rewrite H; reflexivity. Qed.

(** *** CAS *)

Definition pcas_ok : CProg unit := CBind (CCAS (CLit 1) (CLit 0) (CLit 5)) (fun _ => CRet tt).
Definition pcas_fail : CProg unit := CBind (CCAS (CLit 1) (CLit 3) (CLit 5)) (fun _ => CRet tt).

Lemma cas_success_response :
  prim_step Child (bfocus pcas_ok) (inl1 (HCAS 1 0 5)) =
    Some (OACAS, true, set_heap (bfocus pcas_ok) Child (upd (hsingle 1 0) 1 5, hsingle 1 1)).
Proof. reflexivity. Qed.

(** A successful CAS answers [true] and changes only cell [1] of the child. *)
Lemma cas_success_step a c' :
  owned_step (bfocus pcas_ok) a c' ->
  a = act Child OACAS /\
  (exists k : bool -> thread sE Bn, (forall b, k b ≅ denote (CRet tt)) /\
     c' = set_pool (set_heap (bfocus pcas_ok) Child (upd (hsingle 1 0) 1 5, hsingle 1 1))
            (mk_pool 2 [k true; Ret tt] [Child; Parent] (Some Fin.F1))) /\
  fst (oc_heap c' Child) 1 = Some 5 /\
  (forall x, x <> 1 -> fst (oc_heap c' Child) x = fst bC x) /\
  snd (oc_heap c' Child) = snd bC /\ oc_heap c' Parent = bP.
Proof.
  intros H.
  apply (owned_step_focus _ 1 [denote pcas_ok; Ret tt] [Child; Parent] Fin.F1) in H; [|reflexivity].
  apply (focus_step_head_prim (bfocus pcas_ok) 1 [denote pcas_ok; Ret tt] [Child; Parent] Fin.F1
           _ _ 0 _ _ (denote_cas_bind_head 1 0 5 _)) in H.
  destruct H as (k & kind & y & c1 & Hk & Hp & -> & ->).
  change (prim_step Child (bfocus pcas_ok) (inl1 (HCAS 1 0 5)) = Some (kind, y, c1)) in Hp.
  rewrite cas_success_response in Hp; injection Hp as <- <- <-.
  split; [reflexivity|]; split; [exists k; split; [exact Hk|reflexivity]|].
  split; [reflexivity|]; split; [intros x Hx; exact (upd_neq _ _ _ _ Hx)|].
  split; reflexivity.
Qed.

Lemma cas_failure_response :
  prim_step Child (bfocus pcas_fail) (inl1 (HCAS 1 3 5)) = Some (OACAS, false, bfocus pcas_fail).
Proof. reflexivity. Qed.

(** A failed CAS answers [false] and leaves both heaps unchanged. *)
Lemma cas_failure_step a c' :
  owned_step (bfocus pcas_fail) a c' ->
  a = act Child OACAS /\
  (exists k : bool -> thread sE Bn, (forall b, k b ≅ denote (CRet tt)) /\
     c' = set_pool (bfocus pcas_fail) (mk_pool 2 [k false; Ret tt] [Child; Parent] (Some Fin.F1))) /\
  oc_heap c' Child = bC /\ oc_heap c' Parent = bP.
Proof.
  intros H.
  apply (owned_step_focus _ 1 [denote pcas_fail; Ret tt] [Child; Parent] Fin.F1) in H; [|reflexivity].
  apply (focus_step_head_prim (bfocus pcas_fail) 1 [denote pcas_fail; Ret tt] [Child; Parent] Fin.F1
           _ _ 0 _ _ (denote_cas_bind_head 1 3 5 _)) in H.
  destruct H as (k & kind & y & c1 & Hk & Hp & -> & ->).
  change (prim_step Child (bfocus pcas_fail) (inl1 (HCAS 1 3 5)) = Some (kind, y, c1)) in Hp.
  rewrite cas_failure_response in Hp; injection Hp as <- <- <-.
  split; [reflexivity|]; split; [exists k; split; [exact Hk|reflexivity]|].
  split; reflexivity.
Qed.

(** *** Free and faults after free *)

Definition pfree_read : CProg unit := CBind (CFree 1) (fun _ => CBind (CRead 1) (fun _ => CRet tt)).
Definition pfree_twice : CProg unit := CBind (CFree 1) (fun _ => CFree 1).
Definition pfree0 : CProg unit := CFree 0.

(** The child's block after [CFree 1]. *)
Definition freed : ManagedHeap := (hfree_block 1 1 (hsingle 1 0), hfree 1 (hsingle 1 1)).

Lemma freed_empty : (forall x, fst freed x = None) /\ (forall b, snd freed b = None).
Proof.
  split; intro x; cbn; unfold hfree_block, hfree, hsingle;
    destruct (Nat.eq_dec 1 x) as [<-|]; try reflexivity.
  destruct (andb _ _); reflexivity.
Qed.

Lemma free_response p :
  prim_step Child (bfocus p) (inl1 (HFree 1)) = Some (OAFree, tt, set_heap (bfocus p) Child freed).
Proof. reflexivity. Qed.

(** [CFree 1] removes the child's data and extent, keeps the parent block,
    and continues with the rest of the child. *)
Lemma free_step (next : unit -> CProg unit) a c' :
  owned_step (bfocus (CBind (CFree 1) next)) a c' ->
  a = act Child OAFree /\
  (exists t, t ≅ denote (next tt) /\
     c' = set_pool (set_heap (bfocus (CBind (CFree 1) next)) Child freed)
            (mk_pool 2 [t; Ret tt] [Child; Parent] (Some Fin.F1))) /\
  oc_heap c' Child = freed /\ oc_heap c' Parent = bP.
Proof.
  intros H.
  apply (owned_step_focus _ 1 [denote (CBind (CFree 1) next); Ret tt] [Child; Parent] Fin.F1) in H;
    [|reflexivity].
  apply (focus_step_head_prim _ 1 [denote (CBind (CFree 1) next); Ret tt] [Child; Parent] Fin.F1
           _ _ 0 _ _ (denote_free_bind_head 1 next)) in H.
  destruct H as (k & kind & y & c1 & Hk & Hp & -> & ->).
  change (prim_step Child (bfocus (CBind (CFree 1) next)) (inl1 (HFree 1)) = Some (kind, y, c1)) in Hp.
  rewrite free_response in Hp; injection Hp as <- <- <-.
  split; [reflexivity|]; split; [exists (k tt); split; [exact (Hk tt)|reflexivity]|].
  split; reflexivity.
Qed.

Lemma bfocus_free_read_coupled : coupled (bfocus pfree_read).
Proof. apply bfocus_coupled; cbn; [tauto|split; [right; discriminate|intros; split; [discriminate|auto]]]. Qed.

Lemma bfocus_free_twice_coupled : coupled (bfocus pfree_twice).
Proof. apply bfocus_coupled; cbn; [tauto|split; intros; right; discriminate]. Qed.

(** Stuckness of the erased side, from [owned_erasure] and the runner. *)
Lemma erased_stuck c :
  coupled c ->
  is_stuck (interp_schedule_nd sh (tp_size (oc_pool c)) (tp_threads (oc_pool c))
              (tp_focus (oc_pool c)) (joined_state c)) ->
  is_stuck (erase_owned (instrument_owned c)).
Proof.
  intros Hc Hs.
  eapply is_stuck_sbisim; [exact (owned_erasure c (coupled_erasable c Hc))|exact Hs].
Qed.

(** After [CFree 1], reading cell [1] faults: no owned action, no action of
    the child's projection, and the original runner on the joined heap (and
    hence the erasure) is stuck rather than reading the parent's memory. *)
Lemma free_read_faults a c' :
  owned_step (bfocus pfree_read) a c' ->
  (forall a' c'', ~ owned_step c' a' c'') /\
  (forall a' c'', ~ owned_step (project Child c') a' c'') /\
  is_stuck (interp_schedule_nd sh (tp_size (oc_pool c')) (tp_threads (oc_pool c'))
              (tp_focus (oc_pool c')) (joined_state c')) /\
  is_stuck (erase_owned (instrument_owned c')).
Proof.
  intros H.
  pose proof (coupled_step _ _ _ bfocus_free_read_coupled H) as Hc.
  destruct (free_step _ _ _ H) as (_ & (t & Ht & ->) & _).
  assert (Hh : t ≅ Vis (inr1 (inr1 (inl1 (HRead 1))) : CEff nat) (fun _ => denote (CRet tt)))
    by (rewrite Ht; apply denote_read_bind_head).
  assert (Hrun : is_stuck (interp_schedule_nd sh 2 [t; Ret tt] (Some Fin.F1)
                   ((hunion (fst freed) (fst bP), hunion (snd freed) (snd bP)), (List.nil, 0)))).
  { rewrite (interp_schedule_nd_equ sh 2 [t; Ret tt]
               ([Ret tt; Ret tt] @ Fin.F1 := (denote_flow (CRead 1) >>=
                  fun flow => match flow with None => Ret tt | Some _ => denote (CRet tt) end))
               (Some Fin.F1) _).
    - rewrite (interp_nd_source_read_missing 1 [Ret tt; Ret tt] Fin.F1 1 _ _ _ List.nil 0 eq_refl).
      apply Stuck_is_stuck.
    - intros i; dependent destruction i; [|reflexivity].
      etransitivity; [exact Ht|apply source_raw_bind]. }
  split; [|split; [|split; [exact Hrun|exact (erased_stuck _ Hc Hrun)]]].
  - intros a' c'' H'.
    apply (owned_step_focus _ 1 [t; Ret tt] [Child; Parent] Fin.F1) in H'; [|reflexivity].
    apply (focus_step_head_prim _ 1 [t; Ret tt] [Child; Parent] Fin.F1 _ _ 0 _ _ Hh) in H'.
    destruct H' as (k & kind & y & c1 & _ & Hp & _).
    rewrite prim_read_none in Hp; [discriminate|reflexivity].
  - intros a' c'' H'.
    apply (owned_step_focus _ 0 [t] [Child] Fin.F1) in H'; [|reflexivity].
    apply (focus_step_head_prim _ 0 [t] [Child] Fin.F1 _ _ 0 _ _ Hh) in H'.
    destruct H' as (k & kind & y & c1 & _ & Hp & _).
    rewrite prim_read_none in Hp; [discriminate|reflexivity].
Qed.

(** A second [CFree 1] faults the same way: it does not free the parent's
    block. *)
Lemma free_twice_faults a c' :
  owned_step (bfocus pfree_twice) a c' ->
  (forall a' c'', ~ owned_step c' a' c'') /\
  (forall a' c'', ~ owned_step (project Child c') a' c'') /\
  is_stuck (interp_schedule_nd sh (tp_size (oc_pool c')) (tp_threads (oc_pool c'))
              (tp_focus (oc_pool c')) (joined_state c')) /\
  is_stuck (erase_owned (instrument_owned c')).
Proof.
  intros H.
  pose proof (coupled_step _ _ _ bfocus_free_twice_coupled H) as Hc.
  destruct (free_step _ _ _ H) as (_ & (t & Ht & ->) & _).
  assert (Hh : t ≅ Vis (inr1 (inr1 (inl1 (HFree 1))) : CEff unit) (fun _ => Ret tt))
    by (rewrite Ht; apply denote_free_head).
  assert (Hrun : is_stuck (interp_schedule_nd sh 2 [t; Ret tt] (Some Fin.F1)
                   ((hunion (fst freed) (fst bP), hunion (snd freed) (snd bP)), (List.nil, 0)))).
  { rewrite (interp_schedule_nd_equ sh 2 [t; Ret tt]
               ([Ret tt; Ret tt] @ Fin.F1 := (denote_flow (CFree 1) >>= fun _ => Ret tt))
               (Some Fin.F1) _).
    - rewrite (interp_nd_source_free_invalid 1 [Ret tt; Ret tt] Fin.F1 1 _
               (hunion (fst freed) (fst bP), hunion (snd freed) (snd bP)) List.nil 0 eq_refl).
      apply Stuck_is_stuck.
    - intros i; dependent destruction i; [exact Ht|reflexivity]. }
  split; [|split; [|split; [exact Hrun|exact (erased_stuck _ Hc Hrun)]]].
  - intros a' c'' H'.
    apply (owned_step_focus _ 1 [t; Ret tt] [Child; Parent] Fin.F1) in H'; [|reflexivity].
    apply (focus_step_head_prim _ 1 [t; Ret tt] [Child; Parent] Fin.F1 _ _ 0 _ _ Hh) in H'.
    destruct H' as (k & kind & y & c1 & _ & Hp & _).
    rewrite prim_free_none in Hp; [discriminate|reflexivity].
  - intros a' c'' H'.
    apply (owned_step_focus _ 0 [t] [Child] Fin.F1) in H'; [|reflexivity].
    apply (focus_step_head_prim _ 0 [t] [Child] Fin.F1 _ _ 0 _ _ Hh) in H'.
    destruct H' as (k & kind & y & c1 & _ & Hp & _).
    rewrite prim_free_none in Hp; [discriminate|reflexivity].
Qed.

(** [CFree 0] succeeds and changes neither heap. *)
Lemma free_zero_noop :
  hcan_step owned_next (bfocus pfree0) /\
  forall a c', owned_step (bfocus pfree0) a c' ->
    a = act Child OAFree /\ forall i, oc_heap c' i = oc_heap (bfocus pfree0) i.
Proof.
  split.
  - eexists; eexists; eapply ostep_prim; [reflexivity|head|reflexivity|reflexivity].
  - intros a c' H.
    apply (owned_step_focus _ 1 [denote pfree0; Ret tt] [Child; Parent] Fin.F1) in H; [|reflexivity].
    apply (focus_step_head_prim _ 1 [denote pfree0; Ret tt] [Child; Parent] Fin.F1
             _ _ 0 _ _ (denote_free_head 0)) in H.
    destruct H as (k & kind & y & c1 & _ & Hp & -> & ->).
    change (Some (OAFree, tt, set_heap (bfocus pfree0) Child bC) = Some (kind, y, c1)) in Hp.
    injection Hp as <- <- <-.
    split; [reflexivity|intros [|]; reflexivity].
Qed.

(** *** A foreign read is not confined *)

Definition pread_foreign : CProg unit := CBind (CRead 2) (fun _ => CRet tt).

Lemma read_foreign_not_confined : ~ confined bC (project Child (b0 pread_foreign)).
Proof.
  intros Hc.
  assert (Hr : reach (project Child (b0 pread_foreign))
                 (set_pool (project Child (b0 pread_foreign))
                    (mk_pool 1 [denote pread_foreign] [Child] (Some Fin.F1)))).
  { apply rt_step; eexists; apply (ostep_select _ 0 [denote pread_foreign] [Child] Fin.F1); reflexivity. }
  apply (Hc _ Hr (denote pread_foreign) Child nat (inl1 (HRead 2)) (fun _ => denote (CRet tt))
           eq_refl (ex_intro _ 0 (denote_read_bind_head 2 _))).
  reflexivity.
Qed.

Lemma read_foreign_not_admissible : ~ admissible pread_foreign CYield bC bP List.nil 0.
Proof. intros (_ & _ & _ & _ & _ & Hc & _); exact (read_foreign_not_confined Hc). Qed.

(** Yet cell [2] is present in the joined heap, where the original runner
    reads [7] and continues. *)
Lemma read_foreign_joined :
  fst (bC ⊎ bP) 2 = Some 7 /\
  interp_schedule_nd sh 2 [denote pread_foreign; Ret tt] (Some Fin.F1) (bC ⊎ bP, (List.nil, 0)) ~
  interp_schedule_nd sh 2 [denote (CRet tt); Ret tt] (Some Fin.F1) (bC ⊎ bP, (List.nil, 0)).
Proof.
  split; [reflexivity|].
  rewrite (interp_schedule_nd_equ sh 2 [denote pread_foreign; Ret tt]
             ([Ret tt; Ret tt] @ Fin.F1 := (denote_flow (CRead 2) >>=
                fun flow => match flow with None => Ret tt | Some _ => denote (CRet tt) end))
             (Some Fin.F1) _).
  - exact (interp_nd_source_read_value 1 [Ret tt; Ret tt] Fin.F1 2 7 _ _ _ List.nil 0 eq_refl).
  - intros i; dependent destruction i; [apply source_raw_bind|reflexivity].
Qed.

End HeapRegression.

From TICL Require Import Lang.CoCSL.Separation.
From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Relations
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From Coinduction Require Import all.
From TICL Require Import CTree.Core CTree.Events.Yield CTree.Events.Writer CTree.Interp.Yield.SBisim
  Utils.Vectors Utils.Pcm Utils.Relations Utils.Execution.

(** * Obligation 6: AG splitting with release certificates, and its boundaries *)
Module AlwaysRegression.
(** The imported libraries turn universe polymorphism on; these concrete
    configurations would otherwise carry hundreds of universes each. *)
#[local] Unset Universe Polymorphism.
Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

(** ** Threads *)


(** Each lineage loops: write its cell with the value it already holds, emit,
    yield. *)
Definition body (a v tag : nat) : CProg (option unit) :=
  CBind (CWrite a v) (fun _ => CBind (CEmit tag v) (fun _ =>
    CBind CYield (fun _ => CRet (Some tt : option unit)))).
Definition cloop (a v tag : nat) : CProg unit := CUntilNone (body a v tag).

(** Its three phases, after any guards and pure binds. *)
Definition tY a v tag : thread sE Bn :=
  Vis (inl1 Yield : CEff unit) (fun _ => Guard (denote (cloop a v tag))).
Definition tE a v tag : thread sE Bn :=
  Vis (inr1 (inr1 (inr1 (inr1 (Log (tag, v))))) : CEff unit) (fun _ => tY a v tag).
Definition tW a v tag : thread sE Bn :=
  Vis (inr1 (inr1 (inl1 (HWrite a v))) : CEff unit) (fun _ => tE a v tag).

Lemma cloop_unfold a v tag : denote (cloop a v tag) ≅ tW a v tag.
Proof.
  unfold denote at 1, cloop; rewrite source_raw_until; unfold body.
  rewrite source_raw_bind, source_raw_write_head.
  unfold tW; apply vis_equ_node; intros [].
  rewrite source_raw_bind, source_raw_emit_head.
  unfold tE; apply vis_equ_node; intros [].
  rewrite source_raw_bind, source_raw_yield_head.
  unfold tY; apply vis_equ_node; intros [].
  rewrite source_raw_ret; reflexivity.
Qed.

Inductive phase := PW | PE | PY.

Definition in_phase (a v tag : nat) (ph : phase) (t : thread sE Bn) : Prop :=
  match ph with
  | PW => exists n, t ≅ guards n (tW a v tag)
  | PE => t ≅ tE a v tag
  | PY => t ≅ tY a v tag
  end.

Definition phase_succ (ph : phase) : phase :=
  match ph with PW => PE | PE => PY | PY => PW end.

Definition phase_thread (a v tag : nat) (ph : phase) : thread sE Bn :=
  match ph with PW => tE a v tag | PE => tY a v tag | PY => Guard (denote (cloop a v tag)) end.

Definition phase_kind (a v tag : nat) (ph : phase) (c : OwnedCfg) : OwnedKind :=
  match ph with PW => OAWrite | PE => OAEmit (tag, v) (global_count c) | PY => OAYield end.

Definition phase_cfg (i : side) (a v tag : nat) (ph : phase) (c : OwnedCfg) : OwnedCfg :=
  match ph with
  | PW => set_heap c i (upd (fst (oc_heap c i)) a v, snd (oc_heap c i))
  | PE => emit_cfg c i (tag, v)
  | PY => c
  end.

Definition phase_focus {n} (j : Fin.t n) (ph : phase) : option (Fin.t n) :=
  match ph with PY => None | _ => Some j end.

Lemma phase_thread_in a v tag ph t :
  t ≅ phase_thread a v tag ph -> in_phase a v tag (phase_succ ph) t.
Proof.
  destruct ph; cbn; intro H; [exact H|exact H|].
  exists 1; cbn; rewrite H; apply guard_equ_node, cloop_unfold.
Qed.

Lemma tE_in a v tag : in_phase a v tag PE (tE a v tag).
Proof. cbn; reflexivity. Qed.
Lemma tY_in a v tag : in_phase a v tag PY (tY a v tag).
Proof. cbn; reflexivity. Qed.

(** The focused slot in a phase has exactly one action. *)
Lemma phase_step c n (v : pool sE Bn (S n)) g j a0 v0 tag0 ph a c' :
  in_phase a0 v0 tag0 ph (v $ j) -> fst (oc_heap c (g $ j)) a0 = Some v0 ->
  focus_step c n v g j a c' ->
  exists t, t ≅ phase_thread a0 v0 tag0 ph /\ a = act (g $ j) (phase_kind a0 v0 tag0 ph c) /\
    c' = set_pool (phase_cfg (g $ j) a0 v0 tag0 ph c) (mk_pool (S n) (v @ j := t) g (phase_focus j ph)).
Proof.
  intros Hph Hcell H; destruct ph; cbn in Hph |- *.
  - destruct Hph as [m Hm]; unfold tW in Hm.
    apply (focus_step_head_prim c n v g j _ _ _ _ _ Hm) in H
      as (k & kind & y & c1 & Hk & Hprim & -> & ->).
    cbn in Hprim; rewrite Hcell in Hprim; injection Hprim as <- <- <-.
    exists (k tt); split; [apply Hk|split; reflexivity].
  - apply (focus_step_head_prim c n v g j _ _ 0 _ _ Hph) in H
      as (k & kind & y & c1 & Hk & Hprim & -> & ->).
    cbn in Hprim; injection Hprim as <- <- <-.
    exists (k tt); split; [apply Hk|split; reflexivity].
  - apply (focus_step_head_yield c n v g j _ 0 _ _ Hph) in H as (k & Hk & -> & ->).
    exists (k tt); split; [apply Hk|split; reflexivity].
Qed.

Lemma phase_step_intro c n (v : pool sE Bn (S n)) g j a0 v0 tag0 ph :
  in_phase a0 v0 tag0 ph (v $ j) -> fst (oc_heap c (g $ j)) a0 = Some v0 ->
  focus_step c n v g j (act (g $ j) (phase_kind a0 v0 tag0 ph c))
    (set_pool (phase_cfg (g $ j) a0 v0 tag0 ph c)
       (mk_pool (S n) (v @ j := phase_thread a0 v0 tag0 ph) g (phase_focus j ph))).
Proof.
  intros Hph Hcell; destruct ph; cbn in Hph |- *.
  - destruct Hph as [m Hm]; unfold tW in Hm.
    apply (focus_step_head_prim c n v g j _ _ _ _ _ Hm).
    exists (fun _ => tE a0 v0 tag0), OAWrite, tt.
    eexists; split; [intro; reflexivity|].
    split; [cbn; rewrite Hcell; reflexivity|split; reflexivity].
  - apply (focus_step_head_prim c n v g j _ _ 0 _ _ Hph).
    exists (fun _ => tY a0 v0 tag0), (OAEmit (tag0, v0) (global_count c)), tt.
    eexists; split; [intro; reflexivity|].
    split; [reflexivity|split; reflexivity].
  - apply (focus_step_head_yield c n v g j _ 0 _ _ Hph).
    exists (fun _ => Guard (denote (cloop a0 v0 tag0))); split; [intro; reflexivity|].
    split; reflexivity.
Qed.

Lemma phase_cfg_own i a0 v0 tag0 ph c :
  fst (oc_heap c i) a0 = Some v0 -> fst (oc_heap (phase_cfg i a0 v0 tag0 ph c) i) a0 = Some v0.
Proof.
  intro H; destruct ph; cbn; [|exact H|exact H].
  unfold side_upd; rewrite (proj2 (side_eqb_spec i i) eq_refl); apply upd_eq.
Qed.

Lemma phase_cfg_other i k a0 v0 tag0 ph c :
  i <> k -> oc_heap (phase_cfg i a0 v0 tag0 ph c) k = oc_heap c k.
Proof.
  intro H; destruct ph; cbn; [|reflexivity|reflexivity].
  unfold side_upd; destruct (side_eqb k i) eqn:E; [|reflexivity].
  apply side_eqb_spec in E; congruence.
Qed.

(** ** Release ranks *)

(** 3/2/1 before a write/emit/yield head; guards count as a write head. *)
Definition head_rank (t : thread sE Bn) : nat :=
  match observe t with
  | VisF e _ =>
      match e with
      | inl1 _ => 1
      | inr1 (inr1 (inr1 (inr1 _))) => 2
      | _ => 3
      end
  | _ => 3
  end.

Lemma head_rank_equ t u : t ≅ u -> head_rank t = head_rank u.
Proof.
  intro H; unfold head_rank; step in H; cbn in H.
  remember (observe t) as ot; remember (observe u) as ou; destruct H; subst; reflexivity.
Qed.

Definition phase_rank (ph : phase) : nat := match ph with PW => 3 | PE => 2 | PY => 1 end.

Lemma head_rank_phase a v tag ph t : in_phase a v tag ph t -> head_rank t = phase_rank ph.
Proof.
  destruct ph; cbn; intro H.
  - destruct H as [[|m] Hm]; rewrite (head_rank_equ _ _ Hm); reflexivity.
  - rewrite (head_rank_equ _ _ H); reflexivity.
  - rewrite (head_rank_equ _ _ H); reflexivity.
Qed.

(** The focused thread's rank; [0] when the scheduler must select. *)
Definition rank (d : OwnedCfg) : nat :=
  match focused_thread (oc_pool d) with Some (t, _) => head_rank t | None => 0 end.

(** Lineage [i]'s release rank: [0] when [i] is directly ready (focused or
    selectable), else the foreign focused head's rank. *)
Definition release_rank (i : side) (d : OwnedCfg) : nat :=
  match focused_thread (oc_pool d) with
  | Some (t, j) => if side_eqb j i then 0 else head_rank t
  | None => 0
  end.

Lemma release_rank_le i d : (release_rank i d <= rank d)%nat.
Proof.
  unfold release_rank, rank; destruct (focused_thread (oc_pool d)) as [[t j]|];
    [destruct (side_eqb j i)|]; lia.
Qed.


(** Every action from a focused configuration belongs to the focused lineage. *)
Lemma owned_step_owner d a d' t j :
  focused_thread (oc_pool d) = Some (t, j) -> owned_step d a d' -> owner a = j.
Proof.
  unfold focused_thread, owned_step; destruct (oc_pool d) as [n v g [k|]]; cbn; [|discriminate].
  intros [= _ <-]; destruct n as [|n]; [inversion k|apply focus_step_owner].
Qed.

(** ** The two-loop fork *)

Definition pc : CProg unit := cloop 1 1 1.
Definition pp : CProg unit := cloop 2 8 0.
Definition hC : ManagedHeap := (hsingle 1 1, hemp).
Definition hP : ManagedHeap := (hsingle 2 8, hemp).
Definition ctx0 : Ctx.Ctx := List.nil.
Definition c0 : OwnedCfg := init_owned pc pp hC hP ctx0 0.

Definition cellC : hprop := fun c => fst (oc_heap c Child) 1 = Some 1.
Definition cellP : hprop := fun c => fst (oc_heap c Parent) 2 = Some 8.

Lemma cell_proper i a v : hproper (fun c => fst (oc_heap c i) a = Some v).
Proof.
  intros c d (_ & _ & Hh & _); destruct (Hh i) as [Hf _]; cbn in Hf.
  unfold heq in Hf; rewrite Hf; reflexivity.
Qed.

Lemma cellC_proper : hproper cellC.
Proof. apply cell_proper. Qed.
Lemma cellP_proper : hproper cellP.
Proof. apply cell_proper. Qed.

Definition thC := in_phase 1 1 1.
Definition thP := in_phase 2 8 0.

(** Unfocused slots are before their write; with no focus, both are. *)
Definition pool_ok (tc tp : thread sE Bn) (f : option (Fin.t 2)) : Prop :=
  match f with
  | None => thC PW tc /\ thP PW tp
  | Some j =>
      (j = Fin.F1 /\ (exists ph, thC ph tc) /\ thP PW tp) \/
      (j = Fin.FS Fin.F1 /\ thC PW tc /\ exists ph, thP ph tp)
  end.

(** The step-closed invariant of the two loop phases. *)
Definition Inv (d : OwnedCfg) : Prop :=
  owned_wf d /\ cellC d /\ cellP d /\
  exists tc tp f, oc_pool d = mk_pool 2 [tc; tp] [Child; Parent] f /\ pool_ok tc tp f.

Lemma hC_hP_disj : hC # hP.
Proof.
  split; intro x; cbn; unfold hsingle, hemp; [|now left].
  destruct (Nat.eq_dec 1 x); [right; destruct (Nat.eq_dec 2 x); [lia|reflexivity]|now left].
Qed.

Lemma Inv_c0 : Inv c0.
Proof.
  split; [apply init_owned_wf; [apply managed_wf_preallocated|apply managed_wf_preallocated|apply hC_hP_disj]|].
  split; [reflexivity|split; [reflexivity|]].
  exists (denote pc), (denote pp), (Some (Fin.FS Fin.F1)); split; [reflexivity|].
  right; split; [reflexivity|split].
  - exists 0; apply cloop_unfold.
  - exists PW, 0; apply cloop_unfold.
Qed.

(** Every action preserves [Inv]; a focused action lowers the rank. *)
Lemma Inv_step d a d' :
  Inv d -> owned_step d a d' ->
  Inv d' /\ (focused_thread (oc_pool d) = None \/ rank d' < rank d).
Proof.
  intros HI Hs; pose proof HI as (Hwf & Hc & Hp & tc & tp & f & Hpool & Hok).
  pose proof (owned_step_wf d a d' Hwf Hs) as Hwf'.
  unfold rank, focused_thread; rewrite Hpool; cbn [tp_focus mk_pool].
  unfold owned_step in Hs; rewrite Hpool in Hs; cbn -[sel_step focus_step] in Hs.
  destruct f as [j|].
  - destruct Hok as [(-> & [ph Hph] & HtP)|(-> & HtC & [ph Hph])].
    + destruct (phase_step d 1 [tc; tp] [Child; Parent] Fin.F1 1 1 1 ph a d' Hph Hc Hs)
        as (t & Ht & -> & ->).
      pose proof (phase_thread_in _ _ _ _ _ Ht) as Hin.
      split.
      * split; [exact Hwf'|].
        split; [unfold cellC; cbn [set_pool oc_heap]; apply phase_cfg_own, Hc|].
        split; [unfold cellP; cbn [set_pool oc_heap]; rewrite phase_cfg_other by discriminate; exact Hp|].
        exists t, tp, (phase_focus Fin.F1 ph); split; [reflexivity|].
        destruct ph; [left; split; [reflexivity|split; [exists PE; exact Hin|exact HtP]]
          |left; split; [reflexivity|split; [exists PY; exact Hin|exact HtP]]
          |split; [exact Hin|exact HtP]].
      * right; cbn -[head_rank]; rewrite (head_rank_phase _ _ _ _ _ Hph).
        destruct ph; cbn -[head_rank]; try lia; rewrite (head_rank_phase _ _ _ _ _ Hin); cbn; lia.
    + destruct (phase_step d 1 [tc; tp] [Child; Parent] (Fin.FS Fin.F1) 2 8 0 ph a d' Hph Hp Hs)
        as (t & Ht & -> & ->).
      pose proof (phase_thread_in _ _ _ _ _ Ht) as Hin.
      split.
      * split; [exact Hwf'|].
        split; [unfold cellC; cbn [set_pool oc_heap]; rewrite phase_cfg_other by discriminate; exact Hc|].
        split; [unfold cellP; cbn [set_pool oc_heap]; apply phase_cfg_own, Hp|].
        exists tc, t, (phase_focus (Fin.FS Fin.F1) ph); split; [reflexivity|].
        destruct ph; [right; split; [reflexivity|split; [exact HtC|exists PE; exact Hin]]
          |right; split; [reflexivity|split; [exact HtC|exists PY; exact Hin]]
          |split; [exact HtC|exact Hin]].
      * right; cbn -[head_rank]; rewrite (head_rank_phase _ _ _ _ _ Hph).
        destruct ph; cbn -[head_rank]; try lia; rewrite (head_rank_phase _ _ _ _ _ Hin); cbn; lia.
  - split; [|left; reflexivity].
    destruct Hs as (j & -> & ->); destruct Hok as [HtC HtP].
    split; [exact Hwf'|split; [exact Hc|split; [exact Hp|]]].
    exists tc, tp, (Some j); split; [reflexivity|].
    dependent destruction j; [left; repeat split; eauto|].
    dependent destruction j; [right; repeat split; eauto|inversion j].
Qed.

Lemma Inv_closed : step_closed Inv.
Proof. intros d a d' HI Hs; exact (proj1 (Inv_step d a d' HI Hs)). Qed.

Lemma Inv_select d i :
  Inv d -> focused_thread (oc_pool d) = None -> exists d', owned_step d (act i OASelect) d'.
Proof.
  intros (_ & _ & _ & tc & tp & f & Hpool & _) Hf.
  unfold focused_thread in Hf; rewrite Hpool in Hf; destruct f as [j|]; [discriminate|].
  unfold owned_step; rewrite Hpool; cbn -[sel_step].
  destruct i; eexists; [exists Fin.F1|exists (Fin.FS Fin.F1)]; split; reflexivity.
Qed.

Lemma Inv_can d : Inv d -> hcan_step owned_next d.
Proof.
  intro HI; pose proof HI as (_ & Hc & Hp & tc & tp & f & Hpool & Hok).
  destruct f as [j|].
  - destruct Hok as [(-> & [ph Hph] & _)|(-> & _ & [ph Hph])].
    + eexists; eexists; unfold owned_step; rewrite Hpool; cbn -[focus_step].
      exact (phase_step_intro d 1 [tc; tp] [Child; Parent] Fin.F1 1 1 1 ph Hph Hc).
    + eexists; eexists; unfold owned_step; rewrite Hpool; cbn -[focus_step].
      exact (phase_step_intro d 1 [tc; tp] [Child; Parent] (Fin.FS Fin.F1) 2 8 0 ph Hph Hp).
  - destruct (Inv_select d Child HI) as [d' Hs].
    + unfold focused_thread; rewrite Hpool; reflexivity.
    + exists d', (act Child OASelect); exact Hs.
Qed.

(** From every progressing state, lineage [i] is enabled after finitely many
    rank-decreasing foreign actions. *)
Lemma Inv_release i : finite_release i Inv (release_rank i).
Proof.
  intros d HI Hcan.
  destruct (scheduler_shape i d Hcan) as [Hst|Hown]; [right|left; exact Hown].
  destruct Hcan as (d' & a & Hs).
  destruct (Inv_step d a d' HI Hs) as [HI' [Hf|Hr]].
  - exfalso; destruct (Inv_select d i HI Hf) as [d'' Hsel].
    exact (Hst _ _ Hsel eq_refl).
  - exists d'; split; [exists a; split; [exact Hs|exact (Hst _ _ Hs)]|split; [exact HI'|]].
    assert (Hj : release_rank i d = rank d).
    { unfold release_rank, rank; destruct (focused_thread (oc_pool d)) as [[t j]|] eqn:Ef; [|reflexivity].
      destruct (side_eqb j i) eqn:E; [|reflexivity].
      apply side_eqb_spec in E; subst j.
      exfalso; exact (Hst _ _ Hs (owned_step_owner _ _ _ _ _ Ef Hs)). }
    rewrite Hj; eapply Nat.le_lt_trans; [apply release_rank_le|exact Hr].
Qed.

(** ** Global AG and its split *)

Lemma Inv_hsep d : Inv d -> hsep cellC cellP d.
Proof. intros (Hwf & Hc & Hp & _); split; [exact Hwf|split; [exact Hc|exact Hp]]. Qed.

Theorem loops_global_hag : hAG owned_next (hsep cellC cellP) c0.
Proof.
  apply (hAG_coind _ _ Inv); [|exact Inv_c0].
  intros d HI; split; [apply Inv_hsep, HI|split; [apply Inv_can, HI|]].
  intros d' [a Hs]; exact (Inv_closed d a d' HI Hs).
Qed.

Lemma loops_admissible : admissible pc pp hC hP ctx0 0.
Proof.
  apply admissible_intro.
  - apply managed_wf_preallocated.
  - apply managed_wf_preallocated.
  - apply hC_hP_disj.
  - cbn; repeat split.
  - cbn; repeat split.
  - cbn; repeat split; discriminate.
  - cbn; repeat split; discriminate.
Qed.

(** Both lineages always keep their cells, from the conventional focused
    singleton initializers. *)
Theorem loops_fork_hag :
  hAG owned_next cellC (init_local Child pc hC ctx0 0 true) /\
  hAG owned_next cellP (init_local Parent pp hP ctx0 0 true).
Proof.
  exact (fork_hag_split pc (fun _ => pp) hC hP ctx0 0 Inv
    (release_rank Child) (release_rank Parent) cellC cellP loops_admissible
    cellC_proper cellP_proper Inv_c0 Inv_closed
    (Inv_release Child) (Inv_release Parent) loops_global_hag).
Qed.


Theorem loops_global_hag_split :
  hAG owned_next cellC (project Child c0) /\ hAG owned_next cellP (project Parent c0) /\
  hAG owned_next cellC (init_local Child pc hC ctx0 0 false) /\
  hAG owned_next cellC (init_local Child pc hC ctx0 0 true) /\
  hAG owned_next cellP (init_local Parent pp hP ctx0 0 true).
Proof.
  destruct (global_hag_split Inv (release_rank Child) (release_rank Parent) cellC cellP c0
    (coupled_init _ _ _ _ _ _ loops_admissible) cellC_proper cellP_proper Inv_c0 Inv_closed
    (Inv_release Child) (Inv_release Parent) loops_global_hag) as [HC HP].
  assert (HC' : hAG owned_next cellC (init_local Child pc hC ctx0 0 false)).
  { exact (proj1 (hAG_proper cellC cellC_proper _ _ (project_init_child pc pp hC hP ctx0 0)) HC). }
  split; [exact HC|split; [exact HP|split; [exact HC'|split; [apply hAG_select_strip, HC'|]]]].
  exact (proj1 (hAG_proper cellP cellP_proper _ _ (project_init_parent pc pp hC hP ctx0 0)) HP).
Qed.

(** ** EG along one fair execution *)

(** Schedule positions: the parent's first iteration, then the child's first
    selection and write, then the periodic rounds. *)
Inductive pos := Q0 | Q1 | Q2 | R0 | R1 | C0 | C1 | C2 | C3 | P0 | P1 | P2 | P3.

Definition next_pos (p : pos) : pos :=
  match p with
  | Q0 => Q1 | Q1 => Q2 | Q2 => R0 | R0 => R1 | R1 => C2
  | C0 => C1 | C1 => C2 | C2 => C3 | C3 => P0
  | P0 => P1 | P1 => P2 | P2 => P3 | P3 => C0
  end.

Definition GLc : thread sE Bn := Guard (denote pc).
Definition GLp : thread sE Bn := Guard (denote pp).

Definition pool_of (p : pos) : TaggedPool :=
  match p with
  | Q0 => mk_pool 2 [denote pc; denote pp] [Child; Parent] (Some (Fin.FS Fin.F1))
  | Q1 => mk_pool 2 [denote pc; tE 2 8 0] [Child; Parent] (Some (Fin.FS Fin.F1))
  | Q2 => mk_pool 2 [denote pc; tY 2 8 0] [Child; Parent] (Some (Fin.FS Fin.F1))
  | R0 => mk_pool 2 [denote pc; GLp] [Child; Parent] None
  | R1 => mk_pool 2 [denote pc; GLp] [Child; Parent] (Some Fin.F1)
  | C0 => mk_pool 2 [GLc; GLp] [Child; Parent] None
  | C1 => mk_pool 2 [GLc; GLp] [Child; Parent] (Some Fin.F1)
  | C2 => mk_pool 2 [tE 1 1 1; GLp] [Child; Parent] (Some Fin.F1)
  | C3 => mk_pool 2 [tY 1 1 1; GLp] [Child; Parent] (Some Fin.F1)
  | P0 => mk_pool 2 [GLc; GLp] [Child; Parent] None
  | P1 => mk_pool 2 [GLc; GLp] [Child; Parent] (Some (Fin.FS Fin.F1))
  | P2 => mk_pool 2 [GLc; tE 2 8 0] [Child; Parent] (Some (Fin.FS Fin.F1))
  | P3 => mk_pool 2 [GLc; tY 2 8 0] [Child; Parent] (Some (Fin.FS Fin.F1))
  end.

Definition pos_owner (p : pos) : side :=
  match p with
  | Q0 | Q1 | Q2 | P0 | P1 | P2 | P3 => Parent
  | R0 | R1 | C0 | C1 | C2 | C3 => Child
  end.

Definition pos_phase (p : pos) : option phase :=
  match p with
  | Q0 | R1 | C1 | P1 => Some PW
  | Q1 | C2 | P2 => Some PE
  | Q2 | C3 | P3 => Some PY
  | R0 | C0 | P0 => None
  end.

Definition side_cell (i : side) : nat * nat * nat :=
  match i with Child => (1, 1, 1) | Parent => (2, 8, 0) end.

Definition pos_kind (p : pos) (c : OwnedCfg) : OwnedKind :=
  match pos_phase p with
  | Some ph => let '(a, v, tag) := side_cell (pos_owner p) in phase_kind a v tag ph c
  | None => OASelect
  end.

Definition pos_cfg (p : pos) (c : OwnedCfg) : OwnedCfg :=
  match pos_phase p with
  | Some ph => let '(a, v, tag) := side_cell (pos_owner p) in phase_cfg (pos_owner p) a v tag ph c
  | None => c
  end.

Fixpoint run (n : nat) : pos * OwnedCfg :=
  match n with
  | 0 => (Q0, c0)
  | S n => let '(p, c) := run n in (next_pos p, set_pool (pos_cfg p c) (pool_of (next_pos p)))
  end.

Definition fair_exec : Execution OwnedCfg OwnedAction unit :=
  {| states := fun n => snd (run n);
     selected := fun n => act (pos_owner (fst (run n))) (pos_kind (fst (run n)) (snd (run n)));
     emitted := fun _ => tt |}.

Lemma run_pool n : oc_pool (snd (run n)) = pool_of (fst (run n)).
Proof. destruct n as [|n]; [reflexivity|cbn; destruct (run n); reflexivity]. Qed.

Lemma run_step n :
  cellC (snd (run n)) -> cellP (snd (run n)) ->
  owned_step (states fair_exec n) (selected fair_exec n) (states fair_exec (S n)).
Proof.
  cbn [states selected fair_exec]; cbn [run].
  pose proof (run_pool n) as Hpool.
  destruct (run n) as [p c]; cbn [fst snd] in *; intros Hc Hp.
  unfold owned_step; rewrite Hpool.
  assert (HWc : thC PW (denote pc)) by (exists 0; apply cloop_unfold).
  assert (HWp : thP PW (denote pp)) by (exists 0; apply cloop_unfold).
  assert (HGc : thC PW GLc) by (exists 1; apply guard_equ_node, cloop_unfold).
  assert (HGp : thP PW GLp) by (exists 1; apply guard_equ_node, cloop_unfold).
  destruct p; cbn [pool_of mk_pool next_pos pos_owner pos_kind pos_cfg pos_phase side_cell].
  - exact (phase_step_intro c 1 [denote pc; denote pp] [Child; Parent] (Fin.FS Fin.F1) 2 8 0 PW HWp Hp).
  - exact (phase_step_intro c 1 [denote pc; tE 2 8 0] [Child; Parent] (Fin.FS Fin.F1) 2 8 0 PE (tE_in _ _ _) Hp).
  - exact (phase_step_intro c 1 [denote pc; tY 2 8 0] [Child; Parent] (Fin.FS Fin.F1) 2 8 0 PY (tY_in _ _ _) Hp).
  - exists Fin.F1; split; reflexivity.
  - exact (phase_step_intro c 1 [denote pc; GLp] [Child; Parent] Fin.F1 1 1 1 PW HWc Hc).
  - exists Fin.F1; split; reflexivity.
  - exact (phase_step_intro c 1 [GLc; GLp] [Child; Parent] Fin.F1 1 1 1 PW HGc Hc).
  - exact (phase_step_intro c 1 [tE 1 1 1; GLp] [Child; Parent] Fin.F1 1 1 1 PE (tE_in _ _ _) Hc).
  - exact (phase_step_intro c 1 [tY 1 1 1; GLp] [Child; Parent] Fin.F1 1 1 1 PY (tY_in _ _ _) Hc).
  - exists (Fin.FS Fin.F1); split; reflexivity.
  - exact (phase_step_intro c 1 [GLc; GLp] [Child; Parent] (Fin.FS Fin.F1) 2 8 0 PW HGp Hp).
  - exact (phase_step_intro c 1 [GLc; tE 2 8 0] [Child; Parent] (Fin.FS Fin.F1) 2 8 0 PE (tE_in _ _ _) Hp).
  - exact (phase_step_intro c 1 [GLc; tY 2 8 0] [Child; Parent] (Fin.FS Fin.F1) 2 8 0 PY (tY_in _ _ _) Hp).
Qed.

Lemma fair_exec_inv n : Inv (states fair_exec n).
Proof.
  induction n as [|n IH]; [exact Inv_c0|].
  pose proof IH as (_ & Hc & Hp & _).
  exact (Inv_closed _ _ _ IH (run_step n Hc Hp)).
Qed.

Lemma fair_exec_run : owned_run fair_exec.
Proof. intro n; pose proof (fair_exec_inv n) as (_ & Hc & Hp & _); exact (run_step n Hc Hp). Qed.

Lemma run_pos_S n : fst (run (S n)) = next_pos (fst (run n)).
Proof. cbn [run]; destruct (run n); reflexivity. Qed.

Lemma run_pos_add k n : fst (run (k + n)) = Nat.iter k next_pos (fst (run n)).
Proof.
  induction k as [|k IH]; [reflexivity|].
  change (S k + n) with (S (k + n)); rewrite run_pos_S, IH; reflexivity.
Qed.

Lemma fair_exec_recurrent i : infinitely (fun n => owner (selected fair_exec n) = i).
Proof.
  intro n; cbn [selected fair_exec owner act].
  assert (H : exists k, pos_owner (Nat.iter k next_pos (fst (run n))) = i).
  { destruct i, (fst (run n));
      solve [ exists 0; reflexivity | exists 1; reflexivity | exists 2; reflexivity
            | exists 3; reflexivity | exists 4; reflexivity | exists 5; reflexivity ]. }
  destruct H as [k Hk]; exists (k + n); split; [lia|].
  rewrite run_pos_add; exact Hk.
Qed.

Theorem loops_global_heg :
  hEG owned_next cellC (project Child c0) /\ hEG owned_next cellP (project Parent c0).
Proof.
  apply (global_heg_fair_split cellC cellP c0 fair_exec
    (coupled_init _ _ _ _ _ _ loops_admissible) cellC_proper cellP_proper eq_refl fair_exec_run).
  - intro n; apply Inv_hsep, fair_exec_inv.
  - apply fair_exec_recurrent.
  - apply fair_exec_recurrent.
Qed.

Theorem loops_fork_heg :
  hEG owned_next cellC (init_local Child pc hC ctx0 0 true) /\
  hEG owned_next cellP (init_local Parent pp hP ctx0 0 true).
Proof.
  apply (fork_heg_fair_split pc (fun _ => pp) hC hP ctx0 0 cellC cellP fair_exec
    loops_admissible cellC_proper cellP_proper eq_refl fair_exec_run).
  - intro n; apply Inv_hsep, fair_exec_inv.
  - apply fair_exec_recurrent.
  - apply fair_exec_recurrent.
Qed.

(** ** Boundary: a parent that never yields *)

(** The parent emits forever without yielding; the child's write of [1] over
    its [0] is pending. *)
Definition bchild : CProg unit := CWrite 1 1.
Definition bparent : CProg unit :=
  CUntilNone (CBind (CEmit 0 8) (fun _ => CRet (Some tt : option unit))).
Definition bC : ManagedHeap := (hsingle 1 0, hemp).
Definition b0 : OwnedCfg := init_owned bchild bparent bC hP ctx0 0.

Definition cell0 : hprop := fun c => fst (oc_heap c Child) 1 = Some 0.

Definition tM : thread sE Bn :=
  Vis (inr1 (inr1 (inr1 (inr1 (Log (0, 8))))) : CEff unit) (fun _ => Guard (denote bparent)).
Definition tWc : thread sE Bn :=
  Vis (inr1 (inr1 (inl1 (HWrite 1 1))) : CEff unit) (fun _ => Ret tt).

Lemma bparent_unfold : denote bparent ≅ tM.
Proof.
  unfold denote at 1, bparent; rewrite source_raw_until.
  rewrite source_raw_bind, source_raw_emit_head.
  unfold tM; apply vis_equ_node; intros [].
  rewrite source_raw_ret; reflexivity.
Qed.

Lemma bchild_unfold : denote bchild ≅ tWc.
Proof.
  unfold denote, bchild; rewrite source_raw_write_head.
  apply vis_equ_node; intros []; reflexivity.
Qed.

Definition BInv (d : OwnedCfg) : Prop :=
  owned_wf d /\ cell0 d /\
  exists tp, oc_pool d = mk_pool 2 [denote bchild; tp] [Child; Parent] (Some (Fin.FS Fin.F1)) /\
    exists m, tp ≅ guards m tM.

Lemma bC_hP_disj : bC # hP.
Proof.
  split; intro x; cbn; unfold hsingle, hemp; [|now left].
  destruct (Nat.eq_dec 1 x); [right; destruct (Nat.eq_dec 2 x); [lia|reflexivity]|now left].
Qed.

Lemma BInv_b0 : BInv b0.
Proof.
  split; [apply init_owned_wf; [apply managed_wf_preallocated|apply managed_wf_preallocated|apply bC_hP_disj]|].
  split; [reflexivity|].
  exists (denote bparent); split; [reflexivity|exists 0; apply bparent_unfold].
Qed.

(** Only the parent ever acts: one emission, after its guards. *)
Lemma BInv_step d a d' : BInv d -> owned_step d a d' -> BInv d'.
Proof.
  intros (Hwf & Hc & tp & Hpool & m & Hm) Hs.
  pose proof (owned_step_wf d a d' Hwf Hs) as Hwf'.
  unfold owned_step in Hs; rewrite Hpool in Hs; cbn -[focus_step] in Hs.
  unfold tM in Hm.
  apply (focus_step_head_prim d 1 [denote bchild; tp] [Child; Parent] (Fin.FS Fin.F1) _ _ m _ _ Hm) in Hs
    as (k & kind & y & c1 & Hk & Hprim & -> & ->).
  cbn in Hprim; injection Hprim as <- <- <-.
  split; [exact Hwf'|split; [exact Hc|]].
  exists (k tt); split; [reflexivity|].
  exists 1; cbn; rewrite (Hk tt); apply guard_equ_node, bparent_unfold.
Qed.

Lemma BInv_can d : BInv d -> exists d', owned_next d d' /\ BInv d'.
Proof.
  intro HI; pose proof HI as (_ & _ & tp & Hpool & m & Hm).
  assert (Hs : exists d', owned_next d d').
  { unfold tM in Hm; eexists; eexists; unfold owned_step; rewrite Hpool; cbn -[focus_step].
    apply (focus_step_head_prim d 1 [denote bchild; tp] [Child; Parent] (Fin.FS Fin.F1) _ _ m _ _ Hm).
    exists (fun _ => Guard (denote bparent)), (OAEmit (0, 8) (global_count d)), tt.
    eexists; split; [intro; reflexivity|split; [reflexivity|split; reflexivity]]. }
  destruct Hs as (d' & a & Hs); exists d'; split; [exists a; exact Hs|exact (BInv_step d a d' HI Hs)].
Qed.

Theorem boundary_global_hag : hAG owned_next (hsep cell0 hTrue) b0.
Proof.
  apply (hAG_coind _ _ BInv); [|exact BInv_b0].
  intros d HI; pose proof HI as (Hwf & Hc & _).
  split; [split; [exact Hwf|split; [exact Hc|exact I]]|].
  split; [destruct (BInv_can d HI) as (d' & Hs & _); exists d'; exact Hs|].
  intros d' [a Hs]; exact (BInv_step d a d' HI Hs).
Qed.

Theorem boundary_global_heg : hEG owned_next (hsep cell0 hTrue) b0.
Proof.
  apply (hEG_coind _ _ BInv); [|exact BInv_b0].
  intros d HI; pose proof HI as (Hwf & Hc & _).
  split; [split; [exact Hwf|split; [exact Hc|exact I]]|].
  exact (BInv_can d HI).
Qed.

(** The premises a release certificate cannot be traded for. *)
Lemma boundary_premises :
  bC # hP /\ 0 < tp_size (oc_pool (project Child b0)) /\
  0 < tp_size (oc_pool (project Parent b0)).
Proof. split; [exact bC_hP_disj|split; cbn; lia]. Qed.

Definition s1 : OwnedCfg := init_local Child bchild bC ctx0 0 true.

(** The standalone child's only action writes [1]. *)
Lemma s1_step a d : owned_step s1 a d -> ~ cell0 d.
Proof.
  unfold owned_step; cbn -[focus_step]; intro Hs.
  pose proof bchild_unfold as Hm; unfold tWc in Hm.
  apply (focus_step_head_prim s1 0 [denote bchild] [Child] Fin.F1 _ _ 0 _ _ Hm) in Hs
    as (k & kind & y & c1 & _ & Hprim & -> & ->).
  cbn in Hprim; injection Hprim as <- <- <-.
  unfold cell0; cbn; discriminate.
Qed.

Lemma s1_can : exists d, owned_next s1 d.
Proof.
  pose proof bchild_unfold as Hm; unfold tWc in Hm.
  eexists; eexists; unfold owned_step; cbn -[focus_step].
  apply (focus_step_head_prim s1 0 [denote bchild] [Child] Fin.F1 _ _ 0 _ _ Hm).
  exists (fun _ => Ret tt), OAWrite, tt.
  eexists; split; [intro; reflexivity|split; [reflexivity|split; reflexivity]].
Qed.

Theorem boundary_local_no_hag : ~ hAG owned_next cell0 s1.
Proof.
  intro H; apply hAG_unfold in H as (_ & _ & Hall).
  destruct s1_can as (d & a & Hs).
  pose proof (Hall d (ex_intro _ a Hs)) as Hd.
  apply hAG_unfold in Hd as (Hd & _); exact (s1_step a d Hs Hd).
Qed.

Theorem boundary_local_no_heg : ~ hEG owned_next cell0 s1.
Proof.
  intro H; apply hEG_unfold in H as (_ & d & [a Hs] & Hd).
  apply hEG_unfold in Hd as (Hd & _); exact (s1_step a d Hs Hd).
Qed.

Lemma boundary_admissible : admissible bchild bparent bC hP ctx0 0.
Proof.
  apply admissible_intro.
  - apply managed_wf_preallocated.
  - apply managed_wf_preallocated.
  - apply bC_hP_disj.
  - cbn; repeat split.
  - cbn; repeat split.
  - cbn; discriminate.
  - cbn; repeat split.
Qed.

(** Hence no release certificate for the child exists. *)
Corollary boundary_no_release I rankC rankP :
  I b0 -> step_closed I -> finite_release Parent I rankP -> ~ finite_release Child I rankC.
Proof.
  intros HI Hcl HrP HrC.
  destruct (global_hag_split I rankC rankP cell0 hTrue b0
    (coupled_init _ _ _ _ _ _ boundary_admissible) (cell_proper Child 1 0)
    (fun _ _ _ => iff_refl True) HI Hcl HrC HrP boundary_global_hag) as [HC _].
  apply (hAG_proper cell0 (cell_proper Child 1 0) _ _ (project_init_child bchild bparent bC hP ctx0 0))
    in HC.
  exact (boundary_local_no_hag (hAG_select_strip _ _ _ _ _ _ HC)).
Qed.

(** ** A guard-only divergent thread has no action *)

Definition spin : CProg unit := CUntilNone (CRet (Some tt : option unit)).

Lemma spin_unfold : denote spin ≅ Guard (denote spin).
Proof.
  unfold denote at 1, spin; rewrite source_raw_until, source_raw_ret; reflexivity.
Qed.

Definition is_guard (t : thread sE Bn) : Prop :=
  match observe t with GuardF _ => True | _ => False end.

Lemma is_guard_equ t u : t ≅ u -> is_guard u -> is_guard t.
Proof.
  intro H; unfold is_guard; step in H; cbn in H.
  remember (observe t) as ot; remember (observe u) as ou; destruct H; subst; tauto.
Qed.

Lemma spin_headed n u : denote spin ≅ guards n u -> is_guard u.
Proof.
  induction n as [|n IH]; cbn; intro H.
  - apply (is_guard_equ u (Guard (denote spin))); [|exact I].
    rewrite <- H; apply spin_unfold.
  - apply IH, equ_guard_inv; rewrite <- spin_unfold; exact H.
Qed.

Lemma spin_no_action a d : ~ owned_step (init_local Child spin managed_empty ctx0 0 true) a d.
Proof.
  unfold owned_step, focus_step; cbn -[guards]; intro Hs.
  destruct Hs as [(t & [n Hn] & _)|[(k & [n Hn] & _)|[(k & [n Hn] & _)|[([n Hn] & _)
    |(Y & e & k & kind & y & c1 & [n Hn] & _)]]]];
    apply spin_headed in Hn; exact Hn.
Qed.

Theorem spin_no_hag : ~ hAG owned_next hTrue (init_local Child spin managed_empty ctx0 0 true).
Proof.
  intro H; apply hAG_unfold in H as (_ & (d & a & Hs) & _); exact (spin_no_action a d Hs).
Qed.

End AlwaysRegression.

From TICL Require Import Lang.CoCSL.Separation.
From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Relations Strings.String
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From Coinduction Require Import all.
From ExtLib Require Import Structures.Maps Data.Map.FMapAList Data.String.
From TICL Require Import CTree.Core CTree.Events.Yield CTree.Events.Writer CTree.Logic.Sim
  Utils.Vectors Utils.Pcm.

Module FiniteRegression.
Import CTreeNotations TICL.Logic.Semantics TICL.Logic.Syntax.TiclNotations VectorNotations CoCSLSyntax.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

Definition fchild : CProg unit :=
  CBind (CRead 1) (fun v => CBind (CWrite 1 (S v)) (fun _ => CEmit 1 1)).
Definition fparent : CProg unit :=
  CBind (CRead 2) (fun v => CBind (CWrite 2 (S v)) (fun _ => CEmit 0 8)).
Definition fk : unit -> CProg unit := fun _ => fparent.
Definition hC : ManagedHeap := (hsingle 1 0, hemp).
Definition hP : ManagedHeap := (hsingle 2 7, hemp).
Definition ctx0 : Ctx.Ctx := List.nil.

Lemma denote_read_bind a (next : nat -> CProg unit) :
  denote (CBind (CRead a) next) ≅
    Vis (inr1 (inr1 (inl1 (HRead a))) : CEff nat) (fun v => denote (next v)).
Proof.
  unfold denote; cbn [denote_flow]; unfold heap_read, CTree.trigger.
  rewrite !bind_bind, bind_vis; step; constructor; intro x; rewrite !bind_ret_l; reflexivity.
Qed.

Lemma denote_write_bind a v (next : unit -> CProg unit) :
  denote (CBind (CWrite a v) next) ≅
    Vis (inr1 (inr1 (inl1 (HWrite a v))) : CEff unit) (fun u => denote (next u)).
Proof.
  unfold denote; cbn [denote_flow]; unfold heap_write, CTree.trigger.
  rewrite !bind_bind, bind_vis; step; constructor; intros [].
  rewrite !bind_ret_l; reflexivity.
Qed.

Lemma denote_emit q v :
  denote (CEmit q v) ≅
    Vis (inr1 (inr1 (inr1 (inr1 (Log (q, v))))) : CEff unit) (fun _ => Ret tt).
Proof.
  unfold denote; rewrite source_raw_emit_head; step; constructor; intros []; reflexivity.
Qed.

Lemma hC_hP_disj : hC # hP.
Proof.
  split; intro a; cbn; unfold hsingle, hemp; [|auto].
  destruct (Nat.eq_dec 1 a), (Nat.eq_dec 2 a); auto; congruence.
Qed.

Lemma fadmissible : admissible fchild (fk tt) hC hP ctx0 0.
Proof.
  apply admissible_intro.
  - apply managed_wf_preallocated.
  - apply managed_wf_preallocated.
  - exact hC_hP_disj.
  - cbn; repeat split; auto.
  - cbn; repeat split; auto.
  - cbn; repeat split; discriminate.
  - cbn; repeat split; discriminate.
Qed.


(** ** Concrete configurations of the finite run *)

Definition hC' : ManagedHeap := (upd (hsingle 1 0) 1 1, hemp).
Definition hP' : ManagedHeap := (upd (hsingle 2 7) 2 8, hemp).
Definition hsd (hc hp : ManagedHeap) : side -> ManagedHeap :=
  fun i => match i with Child => hc | Parent => hp end.

Definition mkc {n} (v : pool sE Bn n) (g : Vector.t side n) (f : option (Fin.t n))
  (hc hp : ManagedHeap) (cc cp : nat) (lc lp : option (indexed (nat * nat))) : OwnedCfg :=
  {| oc_pool := mk_pool n v g f; oc_anchor := hsd hC hP; oc_heap := hsd hc hp;
     oc_ctx := ctx0; oc_base := 0;
     oc_count := fun i => match i with Child => cc | Parent => cp end;
     oc_last := fun i => match i with Child => lc | Parent => lp end |}.

Definition tC1 : thread sE Bn := denote (CBind (CWrite 1 1) (fun _ => CEmit 1 1)).
Definition tC2 : thread sE Bn := denote (CEmit 1 1).
Definition tP1 : thread sE Bn := denote (CBind (CWrite 2 8) (fun _ => CEmit 0 8)).
Definition tP2 : thread sE Bn := denote (CEmit 0 8).
Definition lP := Some (stamp (0, 8) 0).
Definition lC := Some (stamp (1, 1) 0).

Definition s0 := init_owned fchild (fk tt) hC hP ctx0 0.
Definition s1 := mkc [denote fchild; tP1] [Child; Parent] (Some (Fin.FS Fin.F1)) hC hP 0 0 None None.
Definition s2 := mkc [denote fchild; tP2] [Child; Parent] (Some (Fin.FS Fin.F1)) hC hP' 0 0 None None.
Definition s3 := mkc [denote fchild; Ret tt] [Child; Parent] (Some (Fin.FS Fin.F1)) hC hP' 0 1 None lP.
Definition s4 := mkc [denote fchild] [Child] None hC hP' 0 1 None lP.
Definition s5 := mkc [denote fchild] [Child] (Some Fin.F1) hC hP' 0 1 None lP.
Definition s6 := mkc [tC1] [Child] (Some Fin.F1) hC hP' 0 1 None lP.
Definition s7 := mkc [tC2] [Child] (Some Fin.F1) hC' hP' 0 1 None lP.
Definition s8 := mkc [Ret tt] [Child] (Some Fin.F1) hC' hP' 1 1 lC lP.
Definition s9 := mkc [] [] None hC' hP' 1 1 lC lP.

(** [s] has exactly one action [a], to [s'] up to [owned_equ]. *)
Definition det_act (s : OwnedCfg) (a : OwnedAction) (s' : OwnedCfg) : Prop :=
  (exists c', owned_step s a c' /\ owned_equ c' s') /\
  (forall b c', owned_step s b c' -> b = a /\ owned_equ c' s').

Local Ltac slot_tac :=
  split; cbn -[denote];
  [first [reflexivity | match goal with H : forall x, _ ≅ _ |- _ => apply H end] | reflexivity].

Local Ltac oequ :=
  unfold owned_equ, tp_equ, tp_slots, focus_nat;
  rewrite ?vector_remove_tail, ?vector_remove_head;
  cbn -[denote];
  split; [split; [repeat (apply List.Forall2_cons; [slot_tac|]); apply List.Forall2_nil | reflexivity]|];
  repeat match goal with
  | |- _ /\ _ => split
  | |- forall i : side, _ => intros []
  | |- heq _ _ => intro; reflexivity
  | |- _ = _ => reflexivity
  | |- _ ≈ _ => cbn
  end.

Local Ltac det_prim L :=
  split;
  [ eexists; split;
    [ cbn -[denote]; eapply focus_step_head_prim with (m := 0); [cbn -[denote]; apply L|];
      eexists (fun x => _); do 3 eexists; split; [intro; reflexivity|split; [reflexivity|split; reflexivity]]
    | oequ ]
  | intros b c' H; cbn -[denote] in H;
    eapply focus_step_head_prim with (m := 0) in H; [|cbn -[denote]; apply L];
    destruct H as (k & kind & y & c1 & Hk & Hp & -> & ->);
    cbn in Hp; injection Hp as <- <- <-; split; [reflexivity|oequ] ].

Local Ltac det_ret :=
  split;
  [ eexists; split;
    [ cbn -[denote]; eapply focus_step_head_ret with (m := 0); [reflexivity|]; split; reflexivity
    | oequ ]
  | intros b c' H; cbn -[denote] in H;
    eapply focus_step_head_ret with (m := 0) in H; [|reflexivity];
    destruct H as [-> ->]; split; [reflexivity|oequ] ].

Local Ltac det_select :=
  split;
  [ eexists; split; [cbn; exists Fin.F1; split; reflexivity | oequ]
  | intros b c' H; cbn in H; destruct H as (j & -> & ->);
    destruct (fin_case 0 j) as [->|[j' ->]]; [split; [reflexivity|oequ]|inversion j'] ].

Lemma det01 : det_act s0 (act Parent OARead) s1.
Proof. det_prim denote_read_bind. Qed.
Lemma det12 : det_act s1 (act Parent OAWrite) s2.
Proof. det_prim denote_write_bind. Qed.
Lemma det23 : det_act s2 (act Parent (OAEmit (0, 8) 0)) s3.
Proof. det_prim denote_emit. Qed.
Lemma det34 : det_act s3 (act Parent OAReturn) s4.
Proof. det_ret. Qed.
Lemma det45 : det_act s4 (act Child OASelect) s5.
Proof. det_select. Qed.
Lemma det56 : det_act s5 (act Child OARead) s6.
Proof. det_prim denote_read_bind. Qed.
Lemma det67 : det_act s6 (act Child OAWrite) s7.
Proof. det_prim denote_write_bind. Qed.
Lemma det78 : det_act s7 (act Child (OAEmit (1, 1) 1)) s8.
Proof. det_prim denote_emit. Qed.
Lemma det89 : det_act s8 (act Child OAReturn) s9.
Proof. det_ret. Qed.


(** ** Generic consequences of a deterministic action *)

Lemma det_wf s a s' : det_act s a s' -> owned_wf s -> owned_wf s'.
Proof.
  intros [(c' & Hs & He) _] W.
  exact (owned_wf_equ _ _ He (owned_step_wf _ _ _ W Hs)).
Qed.

Lemma det_hAU P Q s a s' :
  hproper P -> hproper Q -> det_act s a s' -> P s ->
  hAU owned_next P Q s' -> hAU owned_next P Q s.
Proof.
  intros HP HQ [(c0 & Hs0 & _) Hall] Ps H.
  apply hAU_step; [exact Ps|exists c0; exists a; exact Hs0|].
  intros c' [b Hb]; destruct (Hall _ _ Hb) as [_ He].
  exact (proj2 (hAU_proper P Q HP HQ c' s' He) H).
Qed.

Lemma det_hEU P Q s a s' :
  hproper P -> hproper Q -> det_act s a s' -> P s ->
  hEU owned_next P Q s' -> hEU owned_next P Q s.
Proof.
  intros HP HQ [(c0 & Hs0 & He) _] Ps H.
  apply (hEU_step _ _ _ s c0); [exact Ps|exists a; exact Hs0|].
  exact (proj2 (hEU_proper P Q HP HQ c0 s' He) H).
Qed.

(** ** Heap-view assertions *)

Definition cell_is (i : side) (a v : nat) : hprop := fun c => fst (oc_heap c i) a = Some v.
Definition inv_C : hprop := hor (cell_is Child 1 0) (cell_is Child 1 1).
Definition inv_P : hprop := hor (cell_is Parent 2 7) (cell_is Parent 2 8).
Definition done_C : hprop := hDone (cell_is Child 1 1).
Definition done_P : hprop := hDone (cell_is Parent 2 8).

Lemma view_cell i a v : view_pred (cell_is i a v).
Proof.
  intros c d (Hh & _) H; unfold cell_is in *.
  destruct (Hh i) as [Hf _]; rewrite <- (Hf a); exact H.
Qed.

Lemma view_hor P Q : view_pred P -> view_pred Q -> view_pred (hor P Q).
Proof. intros HP HQ c d E [H|H]; [left; exact (HP c d E H)|right; exact (HQ c d E H)]. Qed.

Lemma view_hDone P : view_pred P -> view_pred (hDone P).
Proof.
  intros HP c d E [T H]; split; [apply (proj2 (proj2 (proj2 (proj2 (proj2 E))))), T|exact (HP c d E H)].
Qed.

Lemma view_inv_C : view_pred inv_C. Proof. apply view_hor; apply view_cell. Qed.
Lemma view_inv_P : view_pred inv_P. Proof. apply view_hor; apply view_cell. Qed.
Lemma view_done_C : view_pred done_C. Proof. apply view_hDone, view_cell. Qed.
Lemma view_done_P : view_pred done_P. Proof. apply view_hDone, view_cell. Qed.
Lemma view_cell_C0 : view_pred (cell_is Child 1 0). Proof. apply view_cell. Qed.

Lemma proper_sep_inv : hproper (hsep inv_C inv_P).
Proof. apply hsep_proper; apply view_pred_proper; [apply view_inv_C|apply view_inv_P]. Qed.
Lemma proper_sep_done : hproper (hsep done_C done_P).
Proof. apply hsep_proper; apply view_pred_proper; [apply view_done_C|apply view_done_P]. Qed.
Lemma proper_sep_zero : hproper (hsep (cell_is Child 1 0) done_P).
Proof. apply hsep_proper; apply view_pred_proper; [apply view_cell|apply view_done_P]. Qed.

(** ** Ownership along the run *)

Lemma wf0 : owned_wf s0.
Proof.
  apply init_owned_wf; [apply managed_wf_preallocated|apply managed_wf_preallocated|exact hC_hP_disj].
Qed.
Lemma wf1 : owned_wf s1. Proof. exact (det_wf _ _ _ det01 wf0). Qed.
Lemma wf2 : owned_wf s2. Proof. exact (det_wf _ _ _ det12 wf1). Qed.
Lemma wf3 : owned_wf s3. Proof. exact (det_wf _ _ _ det23 wf2). Qed.
Lemma wf4 : owned_wf s4. Proof. exact (det_wf _ _ _ det34 wf3). Qed.
Lemma wf5 : owned_wf s5. Proof. exact (det_wf _ _ _ det45 wf4). Qed.
Lemma wf6 : owned_wf s6. Proof. exact (det_wf _ _ _ det56 wf5). Qed.
Lemma wf7 : owned_wf s7. Proof. exact (det_wf _ _ _ det67 wf6). Qed.
Lemma wf8 : owned_wf s8. Proof. exact (det_wf _ _ _ det78 wf7). Qed.
Lemma wf9 : owned_wf s9. Proof. exact (det_wf _ _ _ det89 wf8). Qed.

Local Ltac sep_tac W :=
  split; [exact W|split; cbn; first [left; reflexivity|right; reflexivity|split; reflexivity]].

(** ** Global AU and EU, and their splits *)

Lemma fglobal_hau : hAU owned_next (hsep inv_C inv_P) (hsep done_C done_P) s0.
Proof.
  pose proof proper_sep_inv as HP; pose proof proper_sep_done as HQ.
  apply (det_hAU _ _ _ _ _ HP HQ det01); [sep_tac wf0|].
  apply (det_hAU _ _ _ _ _ HP HQ det12); [sep_tac wf1|].
  apply (det_hAU _ _ _ _ _ HP HQ det23); [sep_tac wf2|].
  apply (det_hAU _ _ _ _ _ HP HQ det34); [sep_tac wf3|].
  apply (det_hAU _ _ _ _ _ HP HQ det45); [sep_tac wf4|].
  apply (det_hAU _ _ _ _ _ HP HQ det56); [sep_tac wf5|].
  apply (det_hAU _ _ _ _ _ HP HQ det67); [sep_tac wf6|].
  apply (det_hAU _ _ _ _ _ HP HQ det78); [sep_tac wf7|].
  apply (det_hAU _ _ _ _ _ HP HQ det89); [sep_tac wf8|].
  apply hAU_now; sep_tac wf9.
Qed.

(** Child done with cell 1 = 1, parent done with cell 2 = 8. *)
Theorem fork_hau_finite :
  hAU owned_next inv_C done_C (init_local Child fchild hC ctx0 0 false) /\
  hAU owned_next inv_P done_P (init_local Parent fparent hP ctx0 0 true).
Proof.
  apply (fork_hau_split fchild fk hC hP ctx0 0); try apply view_pred_proper;
    [exact fadmissible|apply view_inv_C|apply view_inv_P|apply view_done_C|apply view_done_P|exact fglobal_hau].
Qed.

Theorem fork_hau_finite_view :
  hAU owned_next inv_C done_C (init_local Child fchild hC ctx0 0 true) /\
  hAU owned_next inv_P done_P (init_local Parent fparent hP ctx0 0 true).
Proof.
  apply (fork_hau_split_view fchild fk hC hP ctx0 0);
    [exact fadmissible|apply view_inv_C|apply view_inv_P|apply view_done_C|apply view_done_P|exact fglobal_hau].
Qed.

Lemma fglobal_heu : hEU owned_next (hsep inv_C inv_P) (hsep done_C done_P) s0.
Proof.
  pose proof proper_sep_inv as HP; pose proof proper_sep_done as HQ.
  apply (det_hEU _ _ _ _ _ HP HQ det01); [sep_tac wf0|].
  apply (det_hEU _ _ _ _ _ HP HQ det12); [sep_tac wf1|].
  apply (det_hEU _ _ _ _ _ HP HQ det23); [sep_tac wf2|].
  apply (det_hEU _ _ _ _ _ HP HQ det34); [sep_tac wf3|].
  apply (det_hEU _ _ _ _ _ HP HQ det45); [sep_tac wf4|].
  apply (det_hEU _ _ _ _ _ HP HQ det56); [sep_tac wf5|].
  apply (det_hEU _ _ _ _ _ HP HQ det67); [sep_tac wf6|].
  apply (det_hEU _ _ _ _ _ HP HQ det78); [sep_tac wf7|].
  apply (det_hEU _ _ _ _ _ HP HQ det89); [sep_tac wf8|].
  apply hEU_now; sep_tac wf9.
Qed.

Theorem fork_heu_finite :
  hEU owned_next inv_C done_C (init_local Child fchild hC ctx0 0 false) /\
  hEU owned_next inv_P done_P (init_local Parent fparent hP ctx0 0 true).
Proof.
  apply (fork_heu_split fchild fk hC hP ctx0 0); try apply view_pred_proper;
    [exact fadmissible|apply view_inv_C|apply view_inv_P|apply view_done_C|apply view_done_P|exact fglobal_heu].
Qed.

(** Zero own steps: the global witness ends at [s4], before any child action,
    where the child's endpoint already holds at its unchanged projection. *)
Lemma fglobal_heu_zero : hEU owned_next (hsep inv_C inv_P) (hsep (cell_is Child 1 0) done_P) s0.
Proof.
  pose proof proper_sep_inv as HP; pose proof proper_sep_zero as HQ.
  apply (det_hEU _ _ _ _ _ HP HQ det01); [sep_tac wf0|].
  apply (det_hEU _ _ _ _ _ HP HQ det12); [sep_tac wf1|].
  apply (det_hEU _ _ _ _ _ HP HQ det23); [sep_tac wf2|].
  apply (det_hEU _ _ _ _ _ HP HQ det34); [sep_tac wf3|].
  apply hEU_now; sep_tac wf4.
Qed.

Theorem fork_heu_zero :
  hEU owned_next inv_C (cell_is Child 1 0) (init_local Child fchild hC ctx0 0 false) /\
  hEU owned_next inv_P done_P (init_local Parent fparent hP ctx0 0 true).
Proof.
  apply (fork_heu_split fchild fk hC hP ctx0 0); try apply view_pred_proper;
    [exact fadmissible|apply view_inv_C|apply view_inv_P|apply view_cell|apply view_done_P|exact fglobal_heu_zero].
Qed.

(** All five projections of [s0..s4] onto [Child] coincide: the four global
    steps of the zero witness are foreign. *)
Lemma zero_child_projection :
  owned_equ (project Child s4) (project Child s0) /\
  cell_is Child 1 0 (init_local Child fchild hC ctx0 0 false).
Proof. split; [oequ|reflexivity]. Qed.


(** ** Erasure to the original runner *)

Definition sfinal : SSig := ((hunion (hsingle 1 1) (hsingle 2 8), hemp), (ctx0, 2)).

(** Parent stamp [(0,8)@0], one scheduler selection, child stamp [(1,1)@1],
    then the joined state with counter 2. *)
Definition ftrace : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) :=
  Vis (Log (inr (stamp (0, 8) 0) : CSLObs (nat * nat))) (fun _ =>
  brS (branchn 1) (fun _ =>
  Vis (Log (inr (stamp (1, 1) 1) : CSLObs (nat * nat))) (fun _ =>
  Ret (sfinal, tt)))).

(** The interpreter's administrative guards are not scheduler steps. *)
Local Lemma er_ret c : erase_owned (Ret c) ≅ Ret (joined_state c, tt).
Proof. unfold erase_owned; rewrite interp_ret_node, bind_ret_l; reflexivity. Qed.

Local Lemma er_guard t : erase_owned (Guard t) ≅ Guard (erase_owned t).
Proof. unfold erase_owned; rewrite interp_guard_node, bind_guard; reflexivity. Qed.

Local Lemma er_step t : erase_owned (Step t) ≅ Step (Guard (erase_owned t)).
Proof. unfold erase_owned; rewrite interp_step_node, bind_step, bind_guard; reflexivity. Qed.

Local Lemma er_br {X} (b : Bn X) k :
  erase_owned (Br b k) ≅ Br b (fun x => Guard (erase_owned (k x))).
Proof.
  unfold erase_owned; rewrite interp_br_node, bind_br.
  setoid_rewrite bind_guard; reflexivity.
Qed.

Local Lemma er_log a k :
  erase_owned (Vis (Log a) k) ≅
    match action_kind a with
    | OAEmit p n => Vis (Log (inr (stamp p n) : CSLObs (nat * nat)))
                         (fun x => Guard (erase_owned (k x)))
    | OAStep => Step (Guard (erase_owned (k tt)))
    | _ => Guard (erase_owned (k tt))
    end.
Proof.
  unfold erase_owned; rewrite interp_vis_node, bind_bind.
  destruct a as [i []]; cbn [handle_owned action_kind];
    rewrite ?bind_trigger, ?bind_step, ?bind_ret_l, ?bind_guard; try reflexivity.
  setoid_rewrite bind_guard; reflexivity.
Qed.

Local Ltac er :=
  try lazymatch goal with
  | |- context [instrument_owned ?c] =>
      rewrite (ctree_eta (instrument_owned c));
      let node := eval hnf in (observe (instrument_owned c)) in
      change (observe (instrument_owned c)) with node
  end;
  cbn -[instrument_owned erase_owned];
  rewrite ?er_ret, ?er_guard, ?er_step, ?er_br, ?er_log.

Lemma ferase : sbisim (simL owned_result_rel) (erase_owned (instrument_owned s0)) ftrace.
Proof.
  er; apply sbisim_guard_l.
  er; apply sbisim_guard_l.
  er; apply sbisim_vis_id; intros []; split; [|constructor].
  apply sbisim_guard_l.
  er; apply sbisim_guard_l.
  er; apply sbisim_br_id; intro x.
  destruct (fin_case 0 x) as [->|[x' ->]]; [|inversion x'].
  rewrite ?vector_remove_tail, ?vector_remove_head.
  apply sbisim_guard_l.
  er; apply sbisim_step; [constructor|].
  repeat apply sbisim_guard_l.
  er; apply sbisim_guard_l.
  er; apply sbisim_guard_l.
  er; apply sbisim_vis_id; intros []; split; [|constructor].
  apply sbisim_guard_l.
  er; apply sbisim_guard_l.
  er; apply sbisim_ret; constructor.
  split; [reflexivity|split; [reflexivity|]].
  split; intros [|[|[|a]]]; reflexivity.
Qed.


#[local] Instance owned_result_rel_Equivalence : Equivalence owned_result_rel.
Proof.
  split.
  - intros [s x]; repeat split; reflexivity.
  - intros [s x] [s' x'] (H1 & H2 & [Ha Hb]); repeat split; try (symmetry; assumption);
      intro a; [rewrite (Ha a)|rewrite (Hb a)]; reflexivity.
  - intros [s x] [s' x'] [s'' x''] (H1 & H2 & [Ha Hb]) (H1' & H2' & [Ha' Hb']);
      repeat split; try (etransitivity; eassumption);
      intro a; [rewrite (Ha a)|rewrite (Hb a)]; auto.
Qed.

#[local] Instance simL_result_Symmetric :
  Symmetric (simL (E := writerE (CSLObs (nat * nat))) owned_result_rel).
Proof. intros l l' []; constructor; symmetry; assumption. Qed.

#[local] Instance simL_result_Transitive :
  Transitive (simL (E := writerE (CSLObs (nat * nat))) owned_result_rel).
Proof.
  intros l1 l2 l3 H1 H2; destruct H1; dependent destruction H2; constructor.
  etransitivity; eassumption.
Qed.

(** The original runner, through [owned_fork_erasure], has the same trace. *)
Theorem fork_run_nd_trace :
  sbisim (simL owned_result_rel) (run_nd (CBind (CFork fchild) fk) (hC ⊎ hP, (ctx0, 0))) ftrace.
Proof.
  etransitivity; [symmetry; exact (owned_fork_erasure fchild fk hC hP ctx0 0 fadmissible)|].
  exact ferase.
Qed.


(** ** Observation projection *)

(** Both lineages' first emissions carry local index 0 in their projections;
    globally the child's is index 1, reconstructed from both counts. *)
Lemma emit_local_parent :
  det_act (project Parent s2) (act Parent (OAEmit (0, 8) 0)) (project Parent s3) /\
  project_action Parent s2 (act Parent (OAEmit (0, 8) 0)) = act Parent (OAEmit (0, 8) 0).
Proof. split; [det_prim denote_emit|reflexivity]. Qed.

Lemma emit_local_child :
  det_act (project Child s7) (act Child (OAEmit (1, 1) 0)) (project Child s8) /\
  project_action Child s7 (act Child (OAEmit (1, 1) 1)) = act Child (OAEmit (1, 1) 0).
Proof. split; [det_prim denote_emit|reflexivity]. Qed.

Lemma emit_counters :
  global_count s2 = oc_base s2 + oc_count s2 Child + oc_count s2 Parent /\ global_count s2 = 0 /\
  global_count s7 = oc_base s7 + oc_count s7 Child + oc_count s7 Parent /\ global_count s7 = 1 /\
  oc_last s9 Child = Some (stamp (1, 1) 0) /\ oc_last s9 Parent = Some (stamp (0, 8) 0) /\
  local_state Child s9 = (hC', (ctx0, 1)) /\ local_state Parent s9 = (hP', (ctx0, 1)) /\
  snd (joined_state s9) = (ctx0, 2).
Proof. repeat split. Qed.

(** The parent's emission leaves the child's projection, and in particular
    its last observation, unchanged. *)
Lemma foreign_emit_child b c' :
  owned_step s2 b c' ->
  owner b = Parent /\ owned_equ (project Child c') (project Child s2) /\
  oc_last (project Child c') Child = None.
Proof.
  intro H; destruct (proj2 det23 _ _ H) as [-> E]; split; [reflexivity|split].
  - transitivity (project Child s3); [apply project_equ, E|oequ].
  - destruct E as (_ & _ & _ & _ & _ & _ & HL); cbn; rewrite (HL Child); reflexivity.
Qed.

(** ** Read-only context *)

Definition ctxx : Ctx.Ctx := (("x"%string, 3) :: List.nil)%list.
Definition pe : CProg unit := CBind (CEval (CVar "x"%string)) (fun _ => CRet tt).

Lemma denote_var_bind name (next : nat -> CProg unit) :
  denote (CBind (CEval (CVar name)) next) ≅
    Vis (inr1 (inr1 (inr1 (inl1 Get))) : CEff Ctx.Ctx) (fun ctx =>
      match lookup name ctx with
      | Some v => Vis (inl1 Yield : CEff unit) (fun _ => denote (next v))
      | None => Stuck
      end).
Proof.
  unfold denote; cbn [denote_flow]; rewrite !bind_bind, source_raw_var.
  unfold source_get, CTree.trigger; rewrite bind_vis; step; constructor; intro ctx.
  rewrite bind_ret_l; match goal with |- context [match ?x with Some _ => _ | None => _ end] => destruct x end; [|reflexivity].
  step; constructor; intros []; rewrite bind_ret_l; reflexivity.
Qed.

Definition mkl (ctx : Ctx.Ctx) {n} (v : pool sE Bn n) (g : Vector.t side n) (f : option (Fin.t n))
  : OwnedCfg :=
  {| oc_pool := mk_pool n v g f; oc_anchor := fun _ => managed_empty;
     oc_heap := fun _ => managed_empty; oc_ctx := ctx; oc_base := 0;
     oc_count := fun _ => 0; oc_last := fun _ => None |}.

Definition ex0 := init_local Child pe managed_empty ctxx 0 true.
Definition ex1 := mkl ctxx [Vis (inl1 Yield : CEff unit) (fun _ => denote (CRet tt))] [Child] (Some Fin.F1).
Definition ex2 := mkl ctxx [denote (CRet tt)] [Child] None.

Local Ltac det_yield :=
  split;
  [ eexists; split;
    [ cbn -[denote]; eapply focus_step_head_yield with (m := 0); [cbn -[denote]; reflexivity|];
      eexists (fun x => _); split; [intro; reflexivity|split; reflexivity]
    | oequ ]
  | intros b c' H; cbn -[denote] in H;
    eapply focus_step_head_yield with (m := 0) in H; [|cbn -[denote]; reflexivity];
    destruct H as (k & Hk & -> & ->); split; [reflexivity|oequ] ].

(** [CVar] reads the context once, then yields; the context never changes. *)
Lemma var_get : det_act ex0 (act Child OAGet) ex1.
Proof. det_prim denote_var_bind. Qed.
Lemma var_yield : det_act ex1 (act Child OAYield) ex2.
Proof. det_yield. Qed.
Lemma var_ctx : oc_ctx ex1 = ctxx /\ oc_ctx ex2 = ctxx /\ tp_focus (oc_pool ex2) = None.
Proof. repeat split. Qed.

(** The original runner performs the same read-then-yield. *)
Lemma var_run_nd :
  run_nd pe (managed_empty, (ctxx, 0)) ~
    interp_schedule_nd sh 1 [denote (CRet tt)] None (managed_empty, (ctxx, 0)).
Proof.
  rewrite run_nd_unfold.
  rewrite (interp_schedule_nd_equ sh 1 _
             ([denote pe] @ Fin.F1 := (denote_exp (CVar "x"%string) >>= fun _ => denote (CRet tt)))).
  - exact (interp_nd_var 0 [denote pe] Fin.F1 "x"%string 3 (fun _ => denote (CRet tt)) (managed_empty, (ctxx, 0)) eq_refl).
  - intro j; destruct (fin_case 0 j) as [->|[j' ->]]; [|inversion j'].
    cbn -[denote denote_exp]; unfold denote, pe; cbn [denote_flow]; rewrite !bind_bind.
    apply equ_clo_bind_eq; intro v; rewrite !bind_ret_l; reflexivity.
Qed.

(** A missing variable is stuck after the read, in both semantics. *)
Definition exm0 := init_local Child pe managed_empty ctx0 0 true.
Definition exm1 := mkl ctx0 [Stuck] [Child] (Some Fin.F1).

Lemma var_missing_get : det_act exm0 (act Child OAGet) exm1.
Proof. det_prim denote_var_bind. Qed.

Lemma var_missing_stuck a c' : ~ owned_step exm1 a c'.
Proof. cbn; apply focus_step_head_stuck with (m := 0); reflexivity. Qed.

Lemma var_missing_run_nd :
  run_nd pe (managed_empty, (ctx0, 0)) ~ (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  rewrite run_nd_unfold.
  rewrite (interp_schedule_nd_equ sh 1 _
             ([denote pe] @ Fin.F1 := (denote_exp (CVar "x"%string) >>= fun _ => denote (CRet tt)))).
  - apply interp_nd_var_missing; reflexivity.
  - intro j; destruct (fin_case 0 j) as [->|[j' ->]]; [|inversion j'].
    cbn -[denote denote_exp]; unfold denote, pe; cbn [denote_flow]; rewrite !bind_bind.
    apply equ_clo_bind_eq; intro v; rewrite !bind_ret_l; reflexivity.
Qed.

(** The continuation observes the value returned by [Get], not just its clock. *)
Definition pe_value : CProg unit :=
  CBind (CEval (CVar "x"%string)) (fun v => CEmit 9 v).
Definition exv0 := init_local Child pe_value managed_empty ctxx 0 true.
Definition exv1 := mkl ctxx
  [Vis (inl1 Yield : CEff unit) (fun _ => denote (CEmit 9 3))] [Child] (Some Fin.F1).
Definition exv2 := mkl ctxx [denote (CEmit 9 3)] [Child] None.
Definition exv3 := mkl ctxx [denote (CEmit 9 3)] [Child] (Some Fin.F1).
Definition exv4 := set_pool (emit_cfg exv3 Child (9, 3))
  (mk_pool 1 [Ret tt] [Child] (Some Fin.F1)).

Lemma var_value_get : det_act exv0 (act Child OAGet) exv1.
Proof. det_prim denote_var_bind. Qed.
Lemma var_value_yield : det_act exv1 (act Child OAYield) exv2.
Proof. det_yield. Qed.
Lemma var_value_select : det_act exv2 (act Child OASelect) exv3.
Proof. det_select. Qed.
Lemma var_value_emit : det_act exv3 (act Child (OAEmit (9, 3) 0)) exv4.
Proof. det_prim denote_emit. Qed.

Lemma var_value_state :
  oc_ctx exv0 = ctxx /\ oc_ctx exv1 = ctxx /\ oc_ctx exv2 = ctxx /\
  oc_ctx exv3 = ctxx /\ oc_ctx exv4 = ctxx /\
  global_count exv3 = 0 /\ oc_count exv4 Child = 1 /\
  oc_last exv4 Child = Some (stamp (9, 3) 0) /\
  local_state Child exv4 = (managed_empty, (ctxx, 1)) /\
  snd (joined_state exv4) = (ctxx, 1).
Proof. repeat split. Qed.

Lemma var_value_run_nd_yield :
  run_nd pe_value (managed_empty, (ctxx, 0)) ~
    interp_schedule_nd sh 1 [denote (CEmit 9 3)] None (managed_empty, (ctxx, 0)).
Proof.
  rewrite run_nd_unfold.
  rewrite (interp_schedule_nd_equ sh 1 _
    ([denote pe_value] @ Fin.F1 :=
      (denote_exp (CVar "x"%string) >>= fun v => denote (CEmit 9 v)))).
  - exact (interp_nd_var 0 [denote pe_value] Fin.F1 "x"%string 3
      (fun v => denote (CEmit 9 v)) (managed_empty, (ctxx, 0)) eq_refl).
  - intro j; destruct (fin_case 0 j) as [->|[j' ->]]; [|inversion j'].
    cbn -[denote denote_exp]; unfold denote, pe_value; cbn [denote_flow]; rewrite !bind_bind.
    apply equ_clo_bind_eq; intro v; rewrite !bind_ret_l; reflexivity.
Qed.

(** Exactly one scheduler selection occurs after the implicit yield, before
    [(9,3)@0]; the context is retained and only the counter advances. *)
Lemma var_value_run_nd_trace :
  run_nd pe_value (managed_empty, (ctxx, 0)) ~
    (brS (branchn 1) (fun _ =>
      Vis (Log (inr (stamp (9, 3) 0) : CSLObs (nat * nat)))
        (fun _ => Ret ((managed_empty, (ctxx, 1)), tt)))
      : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  rewrite var_value_run_nd_yield, interp_schedule_nd_select.
  apply sbisim_br_id; intro j.
  destruct (fin_case 0 j) as [->|[j' ->]]; [|inversion j'].
  apply sbisim_step; [constructor|].
  lazymatch goal with |- _ ~ ?rhs =>
  change (interp_schedule_nd sh 1
    ([denote (CEmit 9 3)] @ Fin.F1 := (denote_flow (CEmit 9 3);; Ret tt))
    (Some Fin.F1) (managed_empty, (ctxx, 0)) ~ rhs)
  end.
  rewrite interp_nd_source_emit_log.
  unfold log, CTree.trigger; rewrite bind_vis.
  apply sbisim_vis_id; intros []; split; [|constructor].
  rewrite bind_ret_l.
  rewrite (interp_schedule_nd_ret sh 0 _ Fin.F1 _) by reflexivity.
  rewrite interp_schedule_nd_empty; reflexivity.
Qed.

Definition exvm0 := init_local Child pe_value managed_empty ctx0 0 true.

Lemma var_value_missing_get : det_act exvm0 (act Child OAGet) exm1.
Proof. det_prim denote_var_bind. Qed.

(** After the only [Get], no action (in particular no emission) is possible. *)
Lemma var_value_missing_fault a c' :
  owned_step exvm0 a c' ->
  action_kind a = OAGet /\ forall b c'', ~ owned_step c' b c''.
Proof.
  intro H; destruct (proj2 var_value_missing_get _ _ H) as [-> E].
  split; [reflexivity|].
  intros b c'' Hs.
  destruct (owned_step_equ _ _ _ _ E Hs) as (d & Hd & _).
  exact (var_missing_stuck b d Hd).
Qed.

Lemma var_value_missing_no_emit a c' payload index :
  owned_step exvm0 a c' -> action_kind a <> OAEmit payload index.
Proof.
  intro H; destruct (var_value_missing_fault _ _ H) as [-> _]; discriminate.
Qed.

Lemma var_value_missing_run_nd :
  run_nd pe_value (managed_empty, (ctx0, 0)) ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  rewrite run_nd_unfold.
  rewrite (interp_schedule_nd_equ sh 1 _
    ([denote pe_value] @ Fin.F1 :=
      (denote_exp (CVar "x"%string) >>= fun v => denote (CEmit 9 v)))).
  - apply interp_nd_var_missing; reflexivity.
  - intro j; destruct (fin_case 0 j) as [->|[j' ->]]; [|inversion j'].
    cbn -[denote denote_exp]; unfold denote, pe_value; cbn [denote_flow]; rewrite !bind_bind.
    apply equ_clo_bind_eq; intro v; rewrite !bind_ret_l; reflexivity.
Qed.

Lemma var_value_missing_raw_stuck :
  is_stuck (run_nd pe_value (managed_empty, (ctx0, 0))).
Proof. rewrite var_value_missing_run_nd; apply Stuck_is_stuck. Qed.

(** ** Allocation and context writes are outside the component fragment *)

Lemma assign_rejected : ~ component_ok (CAssign "x"%string (CLit 1)).
Proof. intro H; cbn in H; destruct H as (_ & _ & H); exact (H ctx0). Qed.

(** Rejection does not change the original runner's context-write semantics. *)
Local Lemma denote_assign_lit name n :
  denote (CAssign name (CLit n)) ≅
    (source_get >>= fun ctx => source_put (add name n ctx) >>= fun _ => Ret tt).
Proof.
  unfold denote; cbn [denote_flow denote_exp].
  rewrite bind_bind, bind_ret_l, bind_bind.
  apply equ_clo_bind_eq; intro ctx.
  rewrite bind_bind.
  apply equ_clo_bind_eq; intros [].
  rewrite bind_ret_l; reflexivity.
Qed.

Definition assigned_ctx : Ctx.Ctx := add "x"%string 1 ctx0.

Lemma assign_run_nd_trace memory base :
  run_nd (CAssign "x"%string (CLit 1)) (memory, (ctx0, base)) ~
    (Vis (Log (inl assigned_ctx : CSLObs (nat * nat)))
      (fun _ => Ret ((memory, (assigned_ctx, base)), tt))
      : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  rewrite run_nd_unfold.
  rewrite (interp_schedule_nd_equ sh 1 _
    ([Ret tt] @ Fin.F1 :=
      (source_get >>= fun ctx => source_put (add "x"%string 1 ctx) >>= fun _ => Ret tt))
    (Some Fin.F1) (memory, (ctx0, base))
    (cons_pool_equ _ _ _ _ (denote_assign_lit "x"%string 1) (pool_equ_refl _))).
  rewrite interp_nd_get_ctx; cbv beta.
  rewrite interp_nd_put_ctx.
  unfold log, CTree.trigger; rewrite bind_vis.
  apply sbisim_vis_id; intros []; split; [|constructor].
  rewrite bind_ret_l.
  rewrite (interp_schedule_nd_ret sh 0 _ Fin.F1 _) by reflexivity.
  rewrite interp_schedule_nd_empty; reflexivity.
Qed.

Lemma assign_result memory base :
  lookup "x"%string (csl_context (memory, (assigned_ctx, base))) = Some 1 /\
  csl_memory (memory, (assigned_ctx, base)) = memory /\
  csl_counter (memory, (assigned_ctx, base)) = base.
Proof. repeat split. Qed.

Lemma assign_original_return :
  <[ {run_nd (CAssign "x"%string (CLit 1)) (hC, (ctx0, 0))}, World.Pure |=
    ⊤ AU ret {fun '(s, _) _ =>
      lookup "x"%string (csl_context s) = Some 1 /\
      csl_memory s = hC /\ csl_counter s = 0} ]>.
Proof.
  apply aur_csl_nd_assign_lit.
  - apply ticll_now; split; [exact I|constructor].
  - exact (assign_result hC 0).
Qed.

Lemma alloc_rejected : ~ component_ok (CAlloc 1).
Proof. intro H; exact H. Qed.

(** First fit is absolute: alone, the allocator returns 1; with cell 1
    framed in, it returns 2. *)
Lemma alloc_isolated :
  heap_handler (F := writerE (CSLObs (nat * nat))) (B := Bn) _ (HAlloc 1) (managed_empty, tt) ≅
    Ret ((managed_alloc managed_empty 1 1, tt), 1).
Proof.
  apply (heap_handler_alloc_first_guards hemp hemp 1 1 tt); try lia.
  - intros o O; reflexivity.
Qed.

Lemma alloc_framed :
  heap_handler (F := writerE (CSLObs (nat * nat))) (B := Bn) _ (HAlloc 1) (hC, tt) ≅
    Guard (Ret ((managed_alloc hC 2 1, tt), 2)).
Proof.
  apply (heap_handler_alloc_first_guards (hsingle 1 0) hemp 1 2 tt); try lia.
  - intros [|o] O; [reflexivity|lia].
  - intros j J1 J2 F; assert (j = 1) as -> by lia; specialize (F 0 ltac:(lia)); discriminate.
Qed.

End FiniteRegression.

(** * Original-TICL bridge regressions: the owned and raw clocks differ. *)
From TICL Require Import CTree.Logic.AG CTree.Logic.Trans CTree.Logic.CanStep.

Module FiniteTiclRegression.
#[local] Unset Universe Polymorphism.
Import FiniteRegression CTreeNotations TICL.Logic.Semantics
  TICL.Logic.Syntax.TiclNotations VectorNotations CoCSLSyntax.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

Definition final_cells (r : SSig * unit) : Prop :=
  fst (csl_memory (fst r)) 1 = Some 1 /\
  fst (csl_memory (fst r)) 2 = Some 8.

Lemma final_cells_proper : Proper (owned_result_rel ==> iff) final_cells.
Proof.
  intros [s x] [s' x'] (_ & _ & [HD _]).
  unfold final_cells; cbn; rewrite (HD 1), (HD 2); reflexivity.
Qed.

Lemma separated_done_joined d :
  hsep done_C done_P d ->
  hDone (fun d => final_cells (joined_state d, tt)) d.
Proof.
  intros (W & [HCt HC] & [HPt HP]); split.
  - unfold terminal in HCt, HPt |- *.
    pose proof (project_size_partition d); lia.
  - change (fst (oc_heap d Child) 1 = Some 1) in HC.
    change (fst (oc_heap d Parent) 2 = Some 8) in HP.
    change (hunion (fst (oc_heap d Child)) (fst (oc_heap d Parent)) 1 = Some 1 /\
      hunion (fst (oc_heap d Child)) (fst (oc_heap d Parent)) 2 = Some 8).
    split; [apply hunion_some, HC|].
    destruct W as (_ & _ & _ & _ & _ & _ & _ & [HD _]).
    destruct (HD 2) as [Hnone|Hnone]; [rewrite hunion_none by exact Hnone; exact HP|congruence].
Qed.

Lemma finite_owned_haf :
  hAF owned_next (hDone (fun d => final_cells (joined_state d, tt))) s0.
Proof.
  eapply hAU_mono; [intros; exact I|apply separated_done_joined|exact fglobal_hau].
Qed.

Lemma finite_owned_hef :
  hEF owned_next (hDone (fun d => final_cells (joined_state d, tt))) s0.
Proof.
  eapply hEU_mono; [intros; exact I|apply separated_done_joined|exact fglobal_heu].
Qed.

Theorem finite_raw_af_done :
  auc (entailsL (SSig * unit) (CNow (fun _ => True)))
    (fun _ wd => done_with (fun r _ => final_cells r) wd)
    (run_nd (CBind (CFork fchild) fk) (hC ⊎ hP, (ctx0, 0))) World.Pure.
Proof.
  exact (fork_haf_done_ticl fchild fk hC hP ctx0 0 final_cells
    fadmissible final_cells_proper finite_owned_haf).
Qed.

Theorem finite_raw_ef_done :
  euc (entailsL (SSig * unit) (CNow (fun _ => True)))
    (fun _ wd => done_with (fun r _ => final_cells r) wd)
    (run_nd (CBind (CFork fchild) fk) (hC ⊎ hP, (ctx0, 0))) World.Pure.
Proof.
  exact (fork_hef_done_ticl fchild fk hC hP ctx0 0 final_cells
    fadmissible final_cells_proper finite_owned_hef).
Qed.

Lemma det_erasable s a s' : det_act s a s' -> erasable s -> erasable s'.
Proof.
  intros [(d & Hs & E) _] H.
  exact (erasable_equ d s' E (erasable_step s a d H Hs)).
Qed.

Lemma finite_terminal_erasable : erasable s9.
Proof.
  apply (det_erasable _ _ _ det89), (det_erasable _ _ _ det78),
    (det_erasable _ _ _ det67), (det_erasable _ _ _ det56),
    (det_erasable _ _ _ det45), (det_erasable _ _ _ det34),
    (det_erasable _ _ _ det23), (det_erasable _ _ _ det12),
    (det_erasable _ _ _ det01).
  exact (admissible_erasable _ _ _ _ _ _ fadmissible).
Qed.

Theorem terminal_zero_owned_actions : terminal s9 /\ ~ hcan_step owned_next s9.
Proof. split; [reflexivity|intros (d & a & Hs); exact Hs]. Qed.

Theorem terminal_raw_value_transition :
  exists T,
    ktrans_ (erase_owned (instrument_owned s9)) World.Pure
      T (World.Done (joined_state s9, tt)) /\
        T ~ (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  destruct (erase_owned_terminal_trans s9 s9 finite_terminal_erasable
    (rt_refl _ _ _) eq_refl) as (T & Ht & Hs).
  exists T; split; [apply KtransDone; exact Ht|exact Hs].
Qed.

Theorem terminal_not_raw_done :
  ~ done_with (E := writerE (CSLObs (nat * nat)))
      (fun (r : SSig * unit) _ => final_cells r) World.Pure.
Proof. intro H; inversion H. Qed.

Theorem terminal_raw_af_done :
  auc (entailsL (SSig * unit) (CNow (fun _ => True)))
    (fun _ wd => done_with (fun r _ => final_cells r) wd)
    (erase_owned (instrument_owned s9)) World.Pure.
Proof.
  apply (owned_haf_done_ticl final_cells s9 World.Pure);
    [exact finite_terminal_erasable|constructor|exact final_cells_proper|].
  apply hAU_now; split; [reflexivity|split; reflexivity].
Qed.

End FiniteTiclRegression.

Module AlwaysTiclRegression.
#[local] Unset Universe Polymorphism.
Import AlwaysRegression CTreeNotations TICL.Logic.Semantics
  TICL.Logic.Syntax.TiclNotations VectorNotations CoCSLSyntax.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

Lemma phase_rank_equ c d : owned_equ c d -> rank c = rank d.
Proof.
  intros (Ep & _); pose proof (proj2 Ep) as Ef.
  destruct (tp_focus (oc_pool c)) as [j|] eqn:Ec;
    destruct (tp_focus (oc_pool d)) as [k|] eqn:Ed.
  - destruct (tp_equ_slot _ _ k Ep) as (j0 & Hn & Et & _).
    unfold focus_nat in Ef; rewrite Ec, Ed in Ef; cbn in Ef; injection Ef as Ef.
    assert (j0 = j) as ->.
    { apply Fin.to_nat_inj; unfold fin_nat in *; congruence. }
    unfold rank, focused_thread; rewrite Ec, Ed; cbn.
    apply head_rank_equ, Et.
  - unfold focus_nat in Ef; rewrite Ec, Ed in Ef; discriminate.
  - unfold focus_nat in Ef; rewrite Ec, Ed in Ef; discriminate.
  - unfold rank, focused_thread; rewrite Ec, Ed; reflexivity.
Qed.

(** This is the focused phase rank, not either lineage's release rank:
    selection and emission already provide raw progress. *)
Definition raw_silence_rank (d : OwnedCfg) : nat := rank d.

Lemma phase_silent_decreases d a d' :
  Inv d -> owned_step d a d' -> erase_action_label a = None ->
  raw_silence_rank d' < raw_silence_rank d.
Proof.
  intros HI Hs He; destruct (Inv_step d a d' HI Hs) as [_ [Hf|Hr]]; [|exact Hr].
  destruct HI as (_ & _ & _ & tc & tp & f & Hpool & _).
  unfold focused_thread in Hf; rewrite Hpool in Hf; destruct f; [discriminate|].
  unfold owned_step in Hs; rewrite Hpool in Hs; cbn in Hs.
  destruct Hs as (j & -> & _); discriminate.
Qed.

(** Saturating the existing phase invariant only makes its setoid
    properness explicit; its operational cases are still [Inv_step]. *)
Definition raw_Inv (d : OwnedCfg) : Prop := exists q, Inv q /\ owned_equ q d.

Lemma raw_Inv_proper : hproper raw_Inv.
Proof.
  intros c d E; split.
  - intros (q & HI & Eq); exists q; split; [exact HI|].
    etransitivity; [exact Eq|exact E].
  - intros (q & HI & Eq); exists q; split; [exact HI|].
    etransitivity; [exact Eq|symmetry; exact E].
Qed.

Lemma raw_Inv_silent_decreases d a d' :
  raw_Inv d -> owned_step d a d' -> erase_action_label a = None ->
  raw_silence_rank d' < raw_silence_rank d.
Proof.
  intros (q & HI & E) Hs He.
  destruct (owned_step_equ d q a d' (symmetry E) Hs) as (q' & Hq & E').
  unfold raw_silence_rank; rewrite (phase_rank_equ d' q' E'), <- (phase_rank_equ q d E).
  exact (phase_silent_decreases q a q' HI Hq He).
Qed.

Lemma loops_raw_invariant_hag : hAG owned_next raw_Inv c0.
Proof.
  apply (hAG_coind _ _ Inv); [|exact Inv_c0].
  intros d HI; split; [exists d; split; [exact HI|reflexivity]|].
  split; [apply Inv_can, HI|].
  intros d' [a Hs]; exact (Inv_closed d a d' HI Hs).
Qed.

Theorem loops_raw_ag :
  <( {run_nd (CBind (CFork pc) (fun _ => pp)) (hC ⊎ hP, (ctx0, 0))},
    World.Pure |= AG ⊤ )>.
Proof.
  exact (fork_hag_ticl pc (fun _ => pp) hC hP ctx0 0 raw_Inv raw_silence_rank
    loops_admissible raw_Inv_proper raw_Inv_silent_decreases loops_raw_invariant_hag).
Qed.

(** Visibility is proved from this execution's actual emit positions, not
    from the independent facts that both owners occur infinitely often. *)
Lemma fair_exec_infinitely_visible :
  infinitely (fun n => erase_action_label (selected fair_exec n) <> None).
Proof.
  intro n.
  assert (H : exists k, forall d,
    erase_action_label (act (pos_owner (Nat.iter k next_pos (fst (run n))))
      (pos_kind (Nat.iter k next_pos (fst (run n))) d)) <> None).
  { destruct (fst (run n));
      solve [exists 0; intro; discriminate | exists 1; intro; discriminate
            | exists 2; intro; discriminate | exists 3; intro; discriminate]. }
  destruct H as [k Hk]; exists (k + n); split; [lia|].
  cbn [selected fair_exec]; rewrite run_pos_add; apply Hk.
Qed.

Theorem loops_raw_eg :
  <( {run_nd (CBind (CFork pc) (fun _ => pp)) (hC ⊎ hP, (ctx0, 0))},
    World.Pure |= EG ⊤ )>.
Proof.
  exact (fork_heg_ticl pc (fun _ => pp) hC hP ctx0 0 fair_exec
    loops_admissible eq_refl fair_exec_run fair_exec_infinitely_visible).
Qed.

End AlwaysTiclRegression.

Module SilentReadTiclRegression.
#[local] Unset Universe Polymorphism.
Import CTreeNotations TICL.Logic.Semantics TICL.Logic.Syntax.TiclNotations
  VectorNotations CoCSLSyntax.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

Definition read_loop : CProg unit :=
  CUntilNone (CBind (CRead 2) (fun _ => CoCSLSyntax.CRet (Some tt : option unit))).
Definition read_heap : ManagedHeap := (hsingle 2 8, hemp).
Definition read_initial : OwnedCfg :=
  init_owned (CoCSLSyntax.CRet tt) read_loop managed_empty read_heap List.nil 0.
Definition read_alone : OwnedCfg := init_local Parent read_loop read_heap List.nil 0 true.
Definition read_head : thread sE Bn :=
  Vis (inr1 (inr1 (inl1 (HRead 2))) : CEff nat)
    (fun _ => Guard (denote read_loop)).

Lemma read_loop_unfold : denote read_loop ≅ read_head.
Proof.
  unfold denote at 1, read_loop; rewrite source_raw_until, source_raw_bind,
    source_raw_read_head.
  unfold read_head; apply vis_equ_node; intro x.
  rewrite source_raw_ret; reflexivity.
Qed.

Lemma read_admissible :
  admissible (CoCSLSyntax.CRet tt) read_loop managed_empty read_heap List.nil 0.
Proof.
  apply admissible_intro.
  - apply managed_wf_empty.
  - apply managed_wf_preallocated.
  - split; intro a; left; reflexivity.
  - exact I.
  - cbn; split; [exact I|intro; exact I].
  - exact I.
  - cbn; split; [discriminate|intro; exact I].
Qed.

(** A successful read retains focus, heap, counter and observations; the
    continuation is a guard back to the same source loop. *)
Definition read_Inv (d : OwnedCfg) : Prop :=
  fst (oc_heap d Parent) 2 = Some 8 /\
  exists n (v : pool sE Bn (S n)) (g : Vector.t side (S n)) j,
    oc_pool d = mk_pool (S n) v g (Some j) /\ (g $ j) = Parent /\
    exists m, (v $ j) ≅ guards m read_head.

Lemma read_initial_Inv : read_Inv read_initial.
Proof.
  split; [reflexivity|].
  exists 1, [denote (CoCSLSyntax.CRet tt); denote read_loop],
    [Child; Parent], (Fin.FS Fin.F1).
  split; [reflexivity|split; [reflexivity|exists 0; apply read_loop_unfold]].
Qed.

Lemma read_alone_Inv : read_Inv read_alone.
Proof.
  split; [reflexivity|].
  exists 0, [denote read_loop], [Parent], Fin.F1.
  split; [reflexivity|split; [reflexivity|exists 0; apply read_loop_unfold]].
Qed.

Lemma read_Inv_step d a d' :
  read_Inv d -> owned_step d a d' -> a = act Parent OARead /\ read_Inv d'.
Proof.
  intros (Hcell & n & v & g & j & Hpool & Hg & m & Hm) Hs.
  unfold owned_step in Hs; rewrite Hpool in Hs; cbn -[focus_step] in Hs.
  unfold read_head in Hm.
  apply (focus_step_head_prim d n v g j _ _ m _ _ Hm) in Hs
    as (k & kind & y & c1 & Hk & Hprim & -> & ->).
  rewrite Hg in Hprim; cbn in Hprim; rewrite Hcell in Hprim.
  injection Hprim as <- <- <-; rewrite Hg; split; [reflexivity|].
  split; [exact Hcell|].
  exists n, (v @ j := k 8), g, j; split; [reflexivity|split; [exact Hg|]].
  rewrite Vector.nth_replace_eq; exists 1; cbn.
  rewrite (Hk 8); apply guard_equ_node, read_loop_unfold.
Qed.

Lemma read_Inv_can d : read_Inv d -> exists d', owned_step d (act Parent OARead) d'.
Proof.
  intros (Hcell & n & v & g & j & Hpool & Hg & m & Hm).
  unfold read_head in Hm; eexists; unfold owned_step; rewrite Hpool; cbn -[focus_step].
  apply (focus_step_head_prim d n v g j _ _ m _ _ Hm).
  exists (fun _ => Guard (denote read_loop)), OARead, 8, d.
  split; [intro; reflexivity|split].
  - rewrite Hg; cbn; rewrite Hcell; reflexivity.
  - split; [rewrite Hg; reflexivity|reflexivity].
Qed.

Lemma read_infinite_owned c : read_Inv c -> hAG owned_next hTrue c.
Proof.
  intro Hc; apply (hAG_coind _ _ read_Inv); [|exact Hc].
  intros d HI; split; [exact I|split].
  - destruct (read_Inv_can d HI) as [d' Hs]; exists d', (act Parent OARead); exact Hs.
  - intros d' [a Hs]; exact (proj2 (read_Inv_step d a d' HI Hs)).
Qed.

Theorem read_loop_owned_hag : hAG owned_next hTrue read_initial.
Proof. apply read_infinite_owned, read_initial_Inv. Qed.

Theorem read_loop_focused_owned_hag : hAG owned_next hTrue read_alone.
Proof. apply read_infinite_owned, read_alone_Inv. Qed.

Theorem read_loop_projection : owned_equ (project Parent read_initial) read_alone.
Proof. apply project_init_parent. Qed.

Lemma read_Inv_silent_reach c d :
  read_Inv c -> clos_refl_trans _ silent_next c d -> read_Inv d.
Proof.
  intros HI H; revert HI.
  induction H as [c d [a [Hs _]]|c|c d e _ IH1 _ IH2]; intro HI.
  - exact (proj2 (read_Inv_step c a d HI Hs)).
  - exact HI.
  - apply IH2, IH1, HI.
Qed.

Lemma read_Inv_nonterminal d : read_Inv d -> tp_size (oc_pool d) <> 0.
Proof. intros (_ & n & v & g & j & Hp & _); rewrite Hp; cbn; lia. Qed.

Theorem read_loop_erasure_stuck : is_stuck (erase_owned (instrument_owned read_initial)).
Proof.
  intros l T Ht.
  destruct (erase_owned_trans_forward read_initial l T
    (admissible_erasable (CoCSLSyntax.CRet tt) read_loop
      managed_empty read_heap List.nil 0 read_admissible) Ht)
    as (d & Hd & [(a & d' & Hs & Hl & _)|(Hz & _)]).
  - pose proof (read_Inv_silent_reach _ _ read_initial_Inv Hd) as HI.
    destruct (read_Inv_step d a d' HI Hs) as [-> _]; discriminate.
  - exact (read_Inv_nonterminal d (read_Inv_silent_reach _ _ read_initial_Inv Hd) Hz).
Qed.

Theorem read_loop_erasure_no_ag :
  ~ <( {erase_owned (instrument_owned read_initial)}, World.Pure |= AG ⊤ )>.
Proof.
  intro H; cdestruct H; destruct Hs as (T & w & Ht).
  apply ktrans_trans in Ht as (l & Ht & _); exact (read_loop_erasure_stuck l T Ht).
Qed.

Theorem read_loop_original_stuck :
  is_stuck (run_nd (CBind (CFork (CoCSLSyntax.CRet tt)) (fun _ => read_loop))
    (managed_empty ⊎ read_heap, (List.nil, 0))).
Proof.
  pose proof (owned_fork_erasure (CoCSLSyntax.CRet tt) (fun _ => read_loop)
    managed_empty read_heap List.nil 0 read_admissible) as Hsb.
  step in Hsb; destruct Hsb as [_ Hb]; cbn in Hb.
  intros l T Ht; destruct (Hb l T Ht) as (l' & T' & Ht' & _ & _).
  exact (read_loop_erasure_stuck l' T' Ht').
Qed.

Theorem read_loop_original_no_ag :
  ~ <( {run_nd (CBind (CFork (CoCSLSyntax.CRet tt)) (fun _ => read_loop))
    (managed_empty ⊎ read_heap, (List.nil, 0))}, World.Pure |= AG ⊤ )>.
Proof.
  intro H; cdestruct H; destruct Hs as (T & w & Ht).
  apply ktrans_trans in Ht as (l & Ht & _); exact (read_loop_original_stuck l T Ht).
Qed.

Definition read_again : OwnedCfg := set_pool read_initial
  (mk_pool 2 [denote (CoCSLSyntax.CRet tt); Guard (denote read_loop)]
    [Child; Parent] (Some (Fin.FS Fin.F1))).

Lemma read_first_step : owned_step read_initial (act Parent OARead) read_again.
Proof.
  change (focus_step read_initial 1
    [denote (CoCSLSyntax.CRet tt); denote read_loop] [Child; Parent]
    (Fin.FS Fin.F1) (act Parent OARead) read_again).
  apply (focus_step_head_prim read_initial 1
    [denote (CoCSLSyntax.CRet tt); denote read_loop] [Child; Parent]
    (Fin.FS Fin.F1) _ _ 0 _ _ read_loop_unfold).
  exists (fun _ => Guard (denote read_loop)), OARead, 8, read_initial.
  split; [intro; reflexivity|split; [reflexivity|split; reflexivity]].
Qed.

Lemma read_again_step : owned_step read_again (act Parent OARead) read_again.
Proof.
  change (focus_step read_again 1
    [denote (CoCSLSyntax.CRet tt); Guard (denote read_loop)] [Child; Parent]
    (Fin.FS Fin.F1) (act Parent OARead) read_again).
  assert (H : Guard (denote read_loop) ≅ guards 1 read_head).
  { apply guard_equ_node, read_loop_unfold. }
  apply (focus_step_head_prim read_again 1
    [denote (CoCSLSyntax.CRet tt); Guard (denote read_loop)] [Child; Parent]
    (Fin.FS Fin.F1) _ _ 1 _ _ H).
  exists (fun _ => Guard (denote read_loop)), OARead, 8, read_again.
  split; [intro; reflexivity|split; [reflexivity|split; reflexivity]].
Qed.

Definition read_forever : Execution OwnedCfg OwnedAction unit :=
  {| states := fun n => match n with 0 => read_initial | S _ => read_again end;
     selected := fun _ => act Parent OARead;
     emitted := fun _ => tt |}.

Theorem read_forever_run : states read_forever 0 = read_initial /\ owned_run read_forever.
Proof.
  split; [reflexivity|intros [|n]; cbn [states selected read_forever];
    [apply read_first_step|apply read_again_step]].
Qed.

Theorem read_forever_infinitely_reads :
  infinitely (fun n => selected read_forever n = act Parent OARead).
Proof. intro n; exists n; split; [lia|reflexivity]. Qed.

Theorem read_forever_not_infinitely_visible :
  ~ infinitely (fun n => erase_action_label (selected read_forever n) <> None).
Proof. intro H; destruct (H 0) as (n & _ & Hn); apply Hn; reflexivity. Qed.

End SilentReadTiclRegression.
