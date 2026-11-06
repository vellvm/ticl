(** * Regression: hidden vs visible branching under the ctrees semantics.

    ctrees' LTS crawls through delayed branches [Br c k] and [Guard]; only
    [Step]/[BrS], [Vis] and [Ret] are transitions. The TICL [ret R] atom
    distinguishes "all transitions return the same value" (strongly bisimilar
    to [Ret x]) from the shallow universal-next terminal postcondition
    ("every transition returns some value satisfying [R]"). The second
    goal is the regression that must fail if native [ret] is ever weakened
    to that terminal-next property. *)
From Stdlib Require Import Fin Vector Arith.PeanoNat Arith.Wf_nat Relations.Relation_Definitions Wellfounded Lia.
From Coinduction Require Import all.
From TICL Require Import CTree.Interp.Refine CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.Policy CTree.Events.Writer
  CTree.Events.State CTree.Events.Yield CTree.Interp.Yield.Mod
  CTree.Interp.State.Mod Utils.Vectors.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.EX
  CTree.Logic.Bind
  CTree.Logic.Iter
  Utils.Relations
  Logic.Core.

Import CTreeNotations TiclNotations VectorNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

Definition two : fin 2 -> ctree void1 Bn nat :=
  fun i => if Fin.eqb i (@Fin.F1 1) then Ret 1 else Ret 2.

(** Hidden value choice is one return, not a step: every transition of
    [brn two] returns [1] or [2] directly. *)
Goal anc (entails nat false (CNow (fun _ => True)))
  (fun _ wd => done_with (fun x _ => x = 1 \/ x = 2) wd) (brn two) Pure.
Proof.
  split; [csplit; auto with ticl | split].
  - apply can_step_br; exists Fin.F1; apply can_step_ret; constructor.
  - intros t' w' TR.
    apply ktrans_br in TR as (i & TR).
    unfold two in TR.
    destruct (Fin.eqb i Fin.F1).
    + apply ktrans_done in TR as (-> & _); constructor; auto.
    + apply ktrans_done in TR as (-> & _); constructor; auto.
Qed.

(** ... but it is NOT a single-valued return: [ret] fails. *)
Goal ~ <( {brn two}, Pure |=R ret {fun _ _ => True} )>.
Proof.
  intros H.
  apply ret_sbisim in H as (x & _ & Hsb).
  (* Both [Ret 1] and [Ret 2] are simulated by [Ret x], hence [x = 1] and [x = 2]. *)
  assert (H1: trans (val 1) (brn two) Stuck).
  { unfold brn, two; eapply trans_br with (x := Fin.F1); [apply trans_ret | reflexivity]. }
  assert (H2: trans (val 2) (brn two) Stuck).
  { unfold brn, two; eapply trans_br with (x := Fin.FS Fin.F1); [apply trans_ret | reflexivity]. }
  step in Hsb; destruct Hsb as [Hf _]; cbn in Hf.
  destruct (Hf _ _ H1) as (l1 & u1 & TR1 & _ & <-).
  destruct (Hf _ _ H2) as (l2 & u2 & TR2 & _ & <-).
  apply trans_ret_inv in TR1 as (_ & Hv1).
  apply trans_ret_inv in TR2 as (_ & Hv2).
  apply val_eq_inv in Hv1; apply val_eq_inv in Hv2.
  lia.
Qed.

(** Visible choice is a step, then a deterministic return. *)
Goal <( {brSn two}, Pure |=R AX (ret {fun x _ => x = 1 \/ x = 2}) )>.
Proof.
  unfold brSn.
  apply ((an_brS (b:=true)) _ _ Fin.F1); split.
  - csplit; auto with ticl.
  - intros i; unfold two; destruct (Fin.eqb i Fin.F1); apply ret_ret; auto; constructor.
Qed.

(** Bind through a visible choice (regime A, [u_bind_r]). *)
Goal auc (entails nat false (CNow (fun _ => True)))
  (anc (entails nat false (CNow (fun _ => True)))
    (fun _ wd => done_with (fun x w => 1 = x /\ Pure = w) wd))
  (x <- brSn two ;; (if Nat.eqb x 1 then Ret 1 else Step (Ret 1))) Pure.
Proof.
  eapply auc_mono_r with (q := entails nat true <( ret= 1 Pure )>).
  - intros t w H; now apply ret_done_next.
  - change <( {x <- brSn two ;; (if Nat.eqb x 1 then Ret 1 else Step (Ret 1))}, Pure
                |=R ⊤ AU ret= 1 Pure )>.
    apply (u_bind_r (b:=true) Q_A) with (R := fun x w => (x = 1 \/ x = 2) /\ w = Pure).
    + cright; apply ((an_brS (b:=true)) _ _ Fin.F1); split.
      * csplit; auto with ticl.
      * intros i; cleft; unfold two; destruct (Fin.eqb i Fin.F1); apply ret_ret; auto; constructor.
    + intros x w ([-> | ->] & ->); cbn.
      * cleft; apply ret_ret; auto; constructor.
      * cright; apply (an_step (b:=true)); split.
        -- csplit; auto with ticl.
        -- cleft; apply ret_ret; auto; constructor.
Qed.

(** sbisim invariance: a guard is invisible. *)
Goal forall (t : ctree void1 Bn nat) w (φ : ticlr void1 nat),
    <( {Guard t}, w |=R φ )> <-> <( t, w |=R φ )>.
Proof.
  intros; ticl_normalize; now ticl_normalize; rewrite sb_guard.
Qed.

(** Hidden value choice may mix immediate and delayed return. *)
Goal auc (entails nat false (CNow (fun _ => True)))
  (fun _ wd => done_with (fun x w => 1 = x /\ Pure = w) wd)
  (x <- brn two ;; (if Nat.eqb x 1 then Ret 1 else Step (Ret 1))) Pure.
Proof.
  unfold brn; ticl_normalize; rewrite bind_br.
  apply StepA; split; [csplit; auto with ticl | split].
  - apply can_step_br; exists Fin.F1.
    unfold two; cbn; ticl_normalize; rewrite bind_ret_l; apply can_step_ret; constructor.
  - intros t' w' TR; apply ktrans_br in TR as (i & TR).
    unfold two in TR; destruct (Fin.eqb i Fin.F1); ticl_normalize; rewrite bind_ret_l in TR; cbn in TR.
    + apply ktrans_done in TR as (-> & _).
      apply MatchA; constructor; auto.
    + apply ktrans_step in TR as (Ht & <- & _).
      ticl_normalize; rewrite Ht.
      apply StepA; split; [csplit; auto with ticl | split].
      * apply can_step_ret; constructor.
      * intros t'' w'' TR; apply ktrans_done in TR as (-> & _).
        apply MatchA; constructor; auto.
Qed.

(** Hidden iteration returns a uniform final value despite differing indices. *)
Definition body (n : nat) : ctree void1 Bn (nat + nat) :=
  if Nat.eqb n 0 then Ret (inr 7)
  else brn (fun i : fin 2 => Ret (inl (Nat.pred n - (if Fin.eqb i (@Fin.F1 1) then 0 else 1)))).

Local Lemma iter_body_ret (n : nat) :
  <( {CTree.iter body n}, Pure |=R ret= 7 Pure )>.
Proof.
  eapply ret_iter_wf with
    (Ri := fun _ w => w = Pure)
    (Rv := ltof _ (@fst nat (World void1))).
  - apply well_founded_ltof.
  - intros m w -> cont Hcont; unfold body.
    destruct (Nat.eqb m 0) eqn:Hm.
    + ticl_normalize; rewrite bind_ret_l; apply ret_ret; auto; constructor.
    + unfold brn; ticl_normalize; rewrite bind_br.
      eapply ret_br with (y := Fin.F1) (x := 7).
      * constructor.
      * auto.
      * intros i; ticl_normalize; rewrite bind_ret_l, sb_guard.
        apply Hcont; [reflexivity |].
        apply Nat.eqb_neq in Hm; unfold ltof; cbn.
        destruct (Fin.eqb i Fin.F1); lia.
  - reflexivity.
Qed.

Goal auc (entails nat false (CNow (fun _ => True)))
  (fun _ wd => done_with (fun x w => 7 = x /\ Pure = w) wd)
  (CTree.iter body 3) Pure.
Proof.
  apply af_ret_done; cleft; apply iter_body_ret.
Qed.

(** Delayed branching forgets branch order under strong bisimulation, but a
    cursor-driven refinement observes that order.  Such a replacement does
    not satisfy the guard-alignment premise of the runner congruences. *)
Definition branch01 : ctree void1 Bn nat :=
  Br (branchn 2)
    (fun i => if Fin.eqb i (@Fin.F1 1) then Ret 0 else Ret 1).

Definition branch10 : ctree void1 Bn nat :=
  Br (branchn 2)
    (fun i => if Fin.eqb i (@Fin.F1 1) then Ret 1 else Ret 0).

Lemma delayed_branch_permutation : branch01 ~ branch10.
Proof.
  unfold branch01, branch10; apply sb_br.
  - intro i; destruct (Fin.eqb i (@Fin.F1 1)).
    + exists (Fin.FS (@Fin.F1 0)); reflexivity.
    + exists (@Fin.F1 1); reflexivity.
  - intro i; destruct (Fin.eqb i (@Fin.F1 1)).
    + exists (Fin.FS (@Fin.F1 0)); reflexivity.
    + exists (@Fin.F1 1); reflexivity.
Qed.

Lemma refine_rr_branch01_zero :
  refine_rr branch01 0 ~ (Ret (0,1) : ctree void1 Bn (nat * nat)).
Proof.
  unfold branch01; ticl_normalize; rewrite unfold_refine_rr.
  change (Guard (refine_rr (Ret 0 : ctree void1 Bn nat) 1) ~
    (Ret (0,1) : ctree void1 Bn (nat * nat))).
  ticl_normalize; rewrite sb_guard, unfold_refine_rr; reflexivity.
Qed.

Lemma refine_rr_branch10_zero :
  refine_rr branch10 0 ~ (Ret (1,1) : ctree void1 Bn (nat * nat)).
Proof.
  unfold branch10; ticl_normalize; rewrite unfold_refine_rr.
  change (Guard (refine_rr (Ret 1 : ctree void1 Bn nat) 1) ~
    (Ret (1,1) : ctree void1 Bn (nat * nat))).
  ticl_normalize; rewrite sb_guard, unfold_refine_rr; reflexivity.
Qed.

Lemma refine_rr_not_sbisim_congruent :
  ~ (refine_rr branch01 0 ~ refine_rr branch10 0).
Proof.
  ticl_normalize; rewrite refine_rr_branch01_zero, refine_rr_branch10_zero.
  intro Hsb.
  assert (Hret : trans (val (0,1))
    (Ret (0,1) : ctree void1 Bn (nat * nat)) Stuck) by apply trans_ret.
  step in Hsb; destruct Hsb as [Hf _]; cbn in Hf.
  destruct (Hf _ _ Hret) as (l & u & TR & _ & <-).
  apply trans_ret_inv in TR as (_ & Hv).
  apply val_eq_inv in Hv; discriminate.
Qed.

(** The event-only round-robin scheduler never inspects a thread's hidden
    branches: both alternatives of a branching thread survive scheduling, and
    each one still logs its own value.  Contrast [refine_rr_branch01_zero],
    where the standalone refiner collapses the branch to its first alternative. *)
Definition rr_branch_thread : thread (stateE nat) Bn :=
  Br (branchn 2) (fun i => Vis (inr1 (inr1 (Put (slot_index i)))) (fun _ => Ret tt)).

Lemma rr_preserves_thread_branch (σ : nat) :
  interp_schedule_rr h_stateW 1 [rr_branch_thread]%vector (Some Fin.F1) 0 σ ~
  Br (branchn 2) (fun i => log (inl (slot_index i));; Ret (slot_index i, tt)).
Proof.
  rewrite (interp_schedule_rr_br h_stateW 0 [rr_branch_thread]%vector Fin.F1 (branchn 2)
    (fun i => Vis (inr1 (inr1 (Put (slot_index i)))) (fun _ => Ret tt)) 0 σ eq_refl).
  apply sb_br_id; intro i.
  erewrite interp_schedule_rr_user with (e := Put (slot_index i)) by reflexivity.
  cbn [h_stateW]; change (Monad.bind ?a ?b) with (CTree.bind a b).
  rewrite translate_log_bind, bind_bind.
  unfold log; rewrite !bind_vis; setoid_rewrite bind_ret_l.
  apply sb_vis; intros [].
  rewrite translate_ret, bind_ret_l.
  erewrite interp_schedule_rr_ret by reflexivity.
  cbn [Vector.replace vector_remove].
  rewrite interp_schedule_rr_empty; reflexivity.
Qed.

(** Visible iteration takes a real step in every continuing round. *)
Local Lemma iterS_body_af_ret (n : nat) :
  <( {CTree.iterS body n}, Pure |=R AF ret= 7 Pure )>.
Proof.
  eapply (u_iterS_wf (b:=true) Q_A
    (fun (_: nat) w => w = Pure)
    (ltof _ (@fst nat (World void1))) body
    (CNow (fun _ => True)) <( ret= 7 Pure )>).
  - apply well_founded_ltof.
  - intros m w -> cont Hcont; unfold body.
    destruct (Nat.eqb m 0) eqn:Hm.
    + ticl_normalize; rewrite bind_ret_l; cleft; apply ret_ret; auto; constructor.
    + unfold brn; ticl_normalize; rewrite bind_br; cright.
      rewrite (ticl_an _ true); split; [csplit; auto with ticl | split].
      * apply can_step_br; exists Fin.F1; ticl_normalize; rewrite bind_ret_l.
        apply can_step_step; constructor.
      * intros t' w' TR; apply ktrans_br in TR as (i & TR).
        ticl_normalize; rewrite bind_ret_l in TR.
        apply ktrans_step in TR as (Ht & <- & _).
        change <( t', Pure |=R AF ret= 7 Pure )>.
        ticl_normalize; rewrite Ht.
        apply Hcont; [reflexivity |].
        apply Nat.eqb_neq in Hm; unfold ltof; cbn.
        destruct (Fin.eqb i Fin.F1); lia.
  - reflexivity.
Qed.

Lemma iterS_body_af :
  auc (entails nat false (CNow (fun _ => True)))
    (fun _ wd => done_with (fun x w => 7 = x /\ Pure = w) wd)
    (CTree.iterS body 3) Pure.
Proof. apply af_ret_done; apply iterS_body_af_ret. Qed.

Lemma iterS_body_acc : Acc kripke_step (CTree.iterS body 3, Pure).
Proof. exact (af_done_accessible _ _ _ iterS_body_af). Qed.


(** Negative: a visible self-loop cannot eventually reach a terminal world. *)
Definition self_loop : ctree void1 Bn nat :=
  CTree.iterS (fun u : unit => Ret (inl u)) tt.

Lemma self_loop_not_af : forall (R : nat -> World void1 -> Prop),
  ~ auc (entails nat false (CNow (fun _ => True)))
      (fun _ wd => done_with R wd) self_loop Pure.
Proof.
  intros R H%af_done_accessible.
  assert (Hunf: self_loop ≅ Step self_loop).
  { unfold self_loop.
    transitivity (lr <- (Ret (inl tt) : ctree void1 Bn (unit + nat));;
                  match lr with
                  | inl l => Step (CTree.iterS (fun u : unit => Ret (inl u)) l)
                  | inr r => Ret r
                  end).
    - now step.
    - now ticl_normalize; rewrite bind_ret_l. }
  assert (TR: |self_loop, Pure| ↦ |self_loop, Pure|).
  { ticl_normalize; rewrite Hunf at 1; apply ktrans_step; split2; [reflexivity | reflexivity | constructor]. }
  exact (acc_self_loop kripke_step (self_loop, Pure) TR H).
Qed.

(** Negative: an empty hidden choice has no transition, so [AF] cannot
    pass vacuously. *)
Definition empty_choice : ctree void1 Bn nat := brn (fun _ : fin 0 => Ret 0).

Lemma empty_choice_not_af : forall (R : nat -> World void1 -> Prop),
  ~ auc (entails nat false (CNow (fun _ => True)))
      (fun _ wd => done_with R wd) empty_choice Pure.
Proof.
  intros R H.
  inversion H as [t w Hdone | t w (_ & (t' & w' & TR) & _)]; subst.
  - inversion Hdone.
  - apply ktrans_br in TR as (i & _); inversion i.
Qed.
