(** * Regression: hidden vs visible branching under the ctrees semantics.

    ctrees' LTS crawls through delayed branches [Br c k] and [Guard]; only
    [Step]/[BrS], [Vis] and [Ret] are transitions. The TICL [ret R] atom
    distinguishes "all transitions return the same value" (strongly bisimilar
    to [Ret x]) from [AX done R] ("every transition returns some value
    satisfying [R]"). The second goal below is the regression that would
    silently pass under a visible-[Br] semantics and must fail if [ret] is
    ever weakened to [AX done]. *)
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
Goal <[ {brn two}, Pure |= AX done {fun x _ => x = 1 \/ x = 2} ]>.
Proof.
  csplit.
  - csplit; auto with ticl.
  - apply can_step_br; exists Fin.F1; apply can_step_ret; constructor.
  - intros t' w' TR.
    apply ktrans_br in TR as (i & TR).
    unfold two in TR.
    destruct (Fin.eqb i Fin.F1).
    + apply ktrans_done in TR as (-> & _); csplit; auto.
    + apply ktrans_done in TR as (-> & _); csplit; auto.
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
Goal <[ {x <- brSn two ;; (if Nat.eqb x 1 then Ret 1 else Step (Ret 1))}, Pure
        |= ⊤ AU AX done= 1 Pure ]>.
Proof.
  apply aur_bind_r with (R := fun x w => (x = 1 \/ x = 2) /\ w = Pure).
  - cright; apply (anr_brS _ _ Fin.F1); split.
    + csplit; auto with ticl.
    + intros i; cleft; unfold two; destruct (Fin.eqb i Fin.F1); apply ret_ret; auto; constructor.
  - intros x w ([-> | ->] & ->); cbn.
    + cleft; apply axr_ret; auto; constructor.
    + cright; apply anr_step; split.
      * csplit; auto with ticl.
      * cleft; apply axr_ret; auto; constructor.
Qed.

(** sbisim invariance: a guard is invisible. *)
Goal forall (t : ctree void1 Bn nat) w (φ : ticlr void1 nat),
    <[ {Guard t}, w |= φ ]> <-> <[ t, w |= φ ]>.
Proof.
  intros; now rewrite sb_guard.
Qed.

(** Regime B: hidden value choice composes on the world-only target. *)
Goal <[ {x <- brn two ;; (if Nat.eqb x 1 then Ret 1 else Step (Ret 1))}, Pure
        |= ⊤ AU done= 1 Pure ]>.
Proof.
  apply aur_bind_r_done_post with (R := fun x w => (x = 1 \/ x = 2) /\ w = Pure).
  - constructor.
  - cright; csplit.
    + csplit; auto with ticl.
    + apply can_step_br; exists Fin.F1; apply can_step_ret; constructor.
    + intros t' w' TR.
      apply ktrans_br in TR as (i & TR).
      unfold two in TR.
      destruct (Fin.eqb i Fin.F1).
      * apply ktrans_done in TR as (-> & _); cleft; csplit; auto.
      * apply ktrans_done in TR as (-> & _); cleft; csplit; auto.
  - intros x w ([-> | ->] & ->); cbn.
    + cright; csplit; [csplit; auto with ticl | apply can_step_ret; constructor |].
      intros t' w' TR; apply ktrans_done in TR as (-> & _); cleft; csplit; auto.
    + cright; apply anr_step; split.
      * csplit; auto with ticl.
      * cright; csplit; [csplit; auto with ticl | apply can_step_ret; constructor |].
        intros t' w' TR; apply ktrans_done in TR as (-> & _); cleft; csplit; auto.
Qed.

(** Regime B iteration: the loop body returns two different indices in one
    hidden state ([aur_iter_done_au]). *)
Definition body (n : nat) : ctree void1 Bn (nat + nat) :=
  if Nat.eqb n 0 then Ret (inr 7)
  else brn (fun i : fin 2 => Ret (inl (Nat.pred n - (if Fin.eqb i (@Fin.F1 1) then 0 else 1)))).

Goal <[ {CTree.iter body 3}, Pure |= ⊤ AU done= 7 Pure ]>.
Proof.
  apply aur_iter_done_au with
    (Rv := fun p q : nat * World void1 => fst p < fst q)
    (Ri := fun _ _ => True).
  - (* well-founded *)
    apply (wf_inverse_image _ _ lt fst); apply Nat.lt_wf_0.
  - constructor.
  - exact I.
  - intros n w Hd _.
    unfold body.
    destruct (Nat.eqb n 0) eqn:Hn.
    + (* return 7: one step to the leaf, whose payload is the [AN] obligation on [Ret 7] *)
      cright; csplit.
      * csplit; auto.
      * apply can_step_ret; auto.
      * intros t' w' TR.
        inv Hd; [| destruct e].
        apply ktrans_done in TR as (-> & _); cleft; csplit; cbn.
        apply axr_ret; auto with ticl.
    + (* hidden choice of the next index *)
      cright; csplit.
      * csplit; auto.
      * apply can_step_br; exists Fin.F1; apply can_step_ret; auto.
      * intros t' w' TR.
        apply ktrans_br in TR as (i & TR).
        apply Nat.eqb_neq in Hn.
        inv Hd; [| destruct e].
        apply ktrans_done in TR as (-> & _); cleft; csplit; cbn.
        split2; [constructor | exact I | lia].
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
