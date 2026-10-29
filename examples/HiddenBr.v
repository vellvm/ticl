(** * Regression: hidden vs visible branching under the ctrees semantics.

    ctrees' LTS crawls through delayed branches [Br c k] and [Guard]; only
    [Step]/[BrS], [Vis] and [Ret] are transitions. The TICL [ret R] atom
    distinguishes "all transitions return the same value" (strongly bisimilar
    to [Ret x]) from the shallow universal-next terminal postcondition
    ("every transition returns some value satisfying [R]"). The second
    goal is the regression that must fail if native [ret] is ever weakened
    to that terminal-next property. *)
From Stdlib Require Import Fin Arith.PeanoNat Relations.Relation_Definitions Wellfounded Lia.
From Coinduction Require Import all.
From TICL Require Import CTree.Interp.Refine.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.EX
  CTree.Logic.Bind
  CTree.Logic.Iter
  Logic.Core.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

Definition two : fin 2 -> ctree void1 Bn nat :=
  fun i => if Fin.eqb i (@Fin.F1 1) then Ret 1 else Ret 2.

(** Hidden value choice is one return, not a step: every transition of
    [brn two] returns [1] or [2] directly. *)
Goal anc (entailsL nat (CNow (fun _ => True)))
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
Goal ~ <[ {brn two}, Pure |= ret {fun _ _ => True} ]>.
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
Goal <[ {brSn two}, Pure |= AX (ret {fun x _ => x = 1 \/ x = 2}) ]>.
Proof.
  unfold brSn.
  apply (anr_brS _ _ Fin.F1); split.
  - csplit; auto with ticl.
  - intros i; unfold two; destruct (Fin.eqb i Fin.F1); apply ret_ret; auto; constructor.
Qed.

(** Bind through a visible choice (regime A, [aur_bind_r]). *)
Goal auc (entailsL nat (CNow (fun _ => True)))
  (anc (entailsL nat (CNow (fun _ => True)))
    (fun _ wd => done_with (fun x w => 1 = x /\ Pure = w) wd))
  (x <- brSn two ;; (if Nat.eqb x 1 then Ret 1 else Step (Ret 1))) Pure.
Proof.
  eapply auc_mono_r with (q := entailsR <[ ret= 1 Pure ]>).
  - intros t w H; now apply ret_done_next.
  - change <[ {x <- brSn two ;; (if Nat.eqb x 1 then Ret 1 else Step (Ret 1))}, Pure
                |= ⊤ AU ret= 1 Pure ]>.
    apply aur_bind_r with (R := fun x w => (x = 1 \/ x = 2) /\ w = Pure).
    + cright; apply (anr_brS _ _ Fin.F1); split.
      * csplit; auto with ticl.
      * intros i; cleft; unfold two; destruct (Fin.eqb i Fin.F1); apply ret_ret; auto; constructor.
    + intros x w ([-> | ->] & ->); cbn.
      * cleft; apply ret_ret; auto; constructor.
      * cright; apply anr_step; split.
        -- csplit; auto with ticl.
        -- cleft; apply ret_ret; auto; constructor.
Qed.

(** sbisim invariance: a guard is invisible. *)
Goal forall (t : ctree void1 Bn nat) w (φ : ticlr void1 nat),
    <[ {Guard t}, w |= φ ]> <-> <[ t, w |= φ ]>.
Proof.
  intros; now rewrite sb_guard.
Qed.

(** Hidden value choice may mix immediate and delayed return. *)
Goal auc (entailsL nat (CNow (fun _ => True)))
  (fun _ wd => done_with (fun x w => 1 = x /\ Pure = w) wd)
  (x <- brn two ;; (if Nat.eqb x 1 then Ret 1 else Step (Ret 1))) Pure.
Proof.
  unfold brn; rewrite bind_br.
  apply StepA; split; [csplit; auto with ticl | split].
  - apply can_step_br; exists Fin.F1.
    unfold two; cbn; rewrite bind_ret_l; apply can_step_ret; constructor.
  - intros t' w' TR; apply ktrans_br in TR as (i & TR).
    unfold two in TR; destruct (Fin.eqb i Fin.F1); rewrite bind_ret_l in TR; cbn in TR.
    + apply ktrans_done in TR as (-> & _).
      apply MatchA; constructor; auto.
    + apply ktrans_step in TR as (Ht & <- & _).
      rewrite Ht.
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
  <[ {CTree.iter body n}, Pure |= ret= 7 Pure ]>.
Proof.
  induction n as [n IH] using (well_founded_induction Nat.lt_wf_0).
  rewrite unfold_iter; unfold body.
  destruct (Nat.eqb n 0) eqn:Hn.
  - rewrite bind_ret_l; apply ret_ret; auto; constructor.
  - unfold brn; rewrite bind_br.
    eapply ret_br with (y := Fin.F1) (x := 7).
    + constructor.
    + auto.
    + intros i; rewrite bind_ret_l, sb_guard.
      apply IH; apply Nat.eqb_neq in Hn.
      destruct (Fin.eqb i Fin.F1); lia.
Qed.

Goal auc (entailsL nat (CNow (fun _ => True)))
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
  unfold branch01; rewrite unfold_refine_rr.
  change (Guard (refine_rr (Ret 0 : ctree void1 Bn nat) 1) ~
    (Ret (0,1) : ctree void1 Bn (nat * nat))).
  rewrite sb_guard, unfold_refine_rr; reflexivity.
Qed.

Lemma refine_rr_branch10_zero :
  refine_rr branch10 0 ~ (Ret (1,1) : ctree void1 Bn (nat * nat)).
Proof.
  unfold branch10; rewrite unfold_refine_rr.
  change (Guard (refine_rr (Ret 1 : ctree void1 Bn nat) 1) ~
    (Ret (1,1) : ctree void1 Bn (nat * nat))).
  rewrite sb_guard, unfold_refine_rr; reflexivity.
Qed.

Lemma refine_rr_not_sbisim_congruent :
  ~ (refine_rr branch01 0 ~ refine_rr branch10 0).
Proof.
  rewrite refine_rr_branch01_zero, refine_rr_branch10_zero.
  intro Hsb.
  assert (Hret : trans (val (0,1))
    (Ret (0,1) : ctree void1 Bn (nat * nat)) Stuck) by apply trans_ret.
  step in Hsb; destruct Hsb as [Hf _]; cbn in Hf.
  destruct (Hf _ _ Hret) as (l & u & TR & _ & <-).
  apply trans_ret_inv in TR as (_ & Hv).
  apply val_eq_inv in Hv; discriminate.
Qed.

(** Visible iteration takes a real step in every continuing round. *)
Local Lemma iterS_body_af_ret (n : nat) :
  <[ {CTree.iterS body n}, Pure |= AF ret= 7 Pure ]>.
Proof.
  induction n as [n IH] using (well_founded_induction Nat.lt_wf_0).
  assert (Hunf : CTree.iterS body n ≅
    (lr <- body n ;; match lr with
      | inl l => Step (CTree.iterS body l)
      | inr r => Ret r
      end)) by (now step).
  rewrite Hunf; unfold body.
  destruct (Nat.eqb n 0) eqn:Hn.
  - rewrite bind_ret_l; cleft; apply ret_ret; auto; constructor.
  - unfold brn; rewrite bind_br; cright.
    split; [csplit; auto with ticl | split].
    + apply can_step_br; exists Fin.F1; rewrite bind_ret_l.
      apply can_step_step; constructor.
    + intros t' w' TR; apply ktrans_br in TR as (i & TR).
      rewrite bind_ret_l in TR.
      apply ktrans_step in TR as (Ht & <- & _).
      change <[ t', Pure |= AF ret= 7 Pure ]>.
      rewrite Ht.
      apply IH; apply Nat.eqb_neq in Hn.
      destruct (Fin.eqb i Fin.F1); lia.
Qed.

Lemma iterS_body_af :
  auc (entailsL nat (CNow (fun _ => True)))
    (fun _ wd => done_with (fun x w => 7 = x /\ Pure = w) wd)
    (CTree.iterS body 3) Pure.
Proof. apply af_ret_done; apply iterS_body_af_ret. Qed.

Lemma iterS_body_acc : Acc kripke_step (CTree.iterS body 3, Pure).
Proof. exact (af_done_accessible _ _ _ iterS_body_af). Qed.

Lemma acc_self_loop {A} (R : A -> A -> Prop) (x : A) : R x x -> ~ Acc R x.
Proof.
  intros Hxx Hacc; revert Hxx; induction Hacc as [x _ IH]; intros Hxx.
  exact (IH x Hxx Hxx).
Qed.

(** Negative: a visible self-loop cannot eventually reach a terminal world. *)
Definition self_loop : ctree void1 Bn nat :=
  CTree.iterS (fun u : unit => Ret (inl u)) tt.

Lemma self_loop_not_af : forall (R : nat -> World void1 -> Prop),
  ~ auc (entailsL nat (CNow (fun _ => True)))
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
    - now rewrite bind_ret_l. }
  assert (TR: |self_loop, Pure| ↦ |self_loop, Pure|).
  { rewrite Hunf at 1; apply ktrans_step; split2; [reflexivity | reflexivity | constructor]. }
  exact (acc_self_loop kripke_step (self_loop, Pure) TR H).
Qed.

(** Negative: an empty hidden choice has no transition, so [AF] cannot
    pass vacuously. *)
Definition empty_choice : ctree void1 Bn nat := brn (fun _ : fin 0 => Ret 0).

Lemma empty_choice_not_af : forall (R : nat -> World void1 -> Prop),
  ~ auc (entailsL nat (CNow (fun _ => True)))
      (fun _ wd => done_with R wd) empty_choice Pure.
Proof.
  intros R H.
  inversion H as [t w Hdone | t w (_ & (t' & w' & TR) & _)]; subst.
  - inversion Hdone.
  - apply ktrans_br in TR as (i & _); inversion i.
Qed.
