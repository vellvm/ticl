(** * Regression: two cooperative loops never fault and never stop.

    [fork2 (lproc 1) (lproc 2)]: each process loops forever on its own cell
    ([work i], then [CYield]).  RR retains its framed cooperative-turn proof.
    ND uses the canonical owned action machine, splits its AG invariant with
    finite lineage-release ranks, and reaches the original TICL judgment by
    erasure with a separate raw-visibility rank.  The contract is [AG ⊤],
    not a recurrence or scheduler-fairness assertion. *)
From Stdlib Require Import Fin Vector Program.Equality Lia Arith.PeanoNat.
From Coinduction Require Import all.
From examples Require Import CSL.Frame.Shared.
From TICL Require Import Lang.CoCSL.Owned Lang.CoCSL.Separation.
Import CoindNotations.

(** ** Slot shapes
    A slot is either at the head of its loop ([fresh]) or just past its
    yield, about to re-enter the loop ([spent]). *)
(** A slot at the head of process [i]'s cooperative loop. *)
Definition fresh (i : nat) : thread sE Bn := denote (lproc i).
(** A slot just past its yield, ready to re-enter the shared loop body. *)
Definition spent (i : nat) : thread sE Bn :=
  denote_flow (CRet (Some tt)) >>= until_tail (lproc_body i) (fun _ => Ret tt).
(** The two slot shapes preserved by a complete cooperative turn. *)
Definition slot (i : nat) (t : thread sE Bn) : Prop := t = fresh i \/ t = spent i.

(** The coinductive functional for the pool safety property [AG ⊤]. *)
Abbreviation agtop :=
  (agcF (@entailsL ctree (writerE (CSLObs (nat * nat))) Bn _ (SSig * unit) <( ⊤ )>)).

(** A spent slot, once focused, is back at the head of its loop. *)
Lemma spent_focus_rr (ts : pool sE Bn 2) (j : Fin.t 2) i m s :
  interp_schedule_rr sh 2 (ts @ j := spent i) (Some j) m s ~
  interp_schedule_rr sh 2 (ts @ j := fresh i) (Some j) m s.
Proof.
  unfold spent; rewrite interp_rr_ret.
  erewrite interp_schedule_rr_guard by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; unfold fresh, denote, lproc; reflexivity.
Qed.


(** ** One turn of process [i] (cell [i], framed by cell [k]) *)
(** A round-robin turn runs [work i] with the other cell framed, then yields. *)
Lemma turn_rr (R : Chain agtop) (ts : pool sE Bn 2) (j : Fin.t 2) i k a b ctx c m s w :
  not_done w ->
  frame_rel (region k b) (own i a ctx c) s ->
  (forall s', csl_memory s' ≈ region i (S a) ⊎ region k b -> snd s' = (ctx, S c) ->
     `R (interp_schedule_rr sh 2 (ts @ j := spent i) None m s')
        (Obs (Log (inr (stamp (i, S a) c))) tt)) ->
  `R (interp_schedule_rr sh 2 (ts @ j := fresh i) (Some j) m s) w.
Proof.
  intros Hw HR HK.
  unfold fresh, denote, lproc, lproc_body.
  rewrite interp_rr_until_none; rr_prefix work_yield_fork_free.
  apply (ag_bind_done_chain _ (frame_post (region k b) (Qwork i a ctx c)));
    [exact Hw | apply work_af_framed; assumption |].
  intros [s' r] w' HP; apply frame_post_work in HP as (-> & HE & HA & ->).
  cbv beta iota.
  rewrite interp_rr_bind, interp_rr_yield.
  cbv beta iota.
  apply HK; assumption.
Qed.


(** ** The unfocused-pool invariant *)
(** Round-robin selection preserves the two-slot loop and disjoint-heap invariant. *)
Lemma pool_ag_rr : forall R : Chain agtop,
  forall t1 t2 m s w a b ctx c, slot 1 t1 -> slot 2 t2 ->
  csl_memory s ≈ region 1 a ⊎ region 2 b -> snd s = (ctx, c) -> not_done w ->
  `R (interp_schedule_rr sh 2 [t1; t2] None m s) w.
Proof.
  apply (tower (b := agtop) (P := fun R => forall t1 t2 m s w a b ctx c, slot 1 t1 -> slot 2 t2 ->
    csl_memory s ≈ region 1 a ⊎ region 2 b -> snd s = (ctx, c) -> not_done w ->
    R (interp_schedule_rr sh 2 [t1; t2] None m s) w)).
  - intros T HT t1 t2 m s w a b ctx c H1 H2 HE HA Hw R HR; apply (HT R HR _ _ _ _ _ a b ctx c); auto.
  - intros R HR t1 t2 m s w a b ctx c H1 H2 HE HA Hw; cbn.
    rewrite interp_schedule_rr_select.
    split; [split; [exact I | exact Hw]|].
    split; [apply can_step_step; exact Hw|].
    intros t' w' TR; apply ktrans_step in TR as (Heq & -> & _); rewrite Heq; clear Heq.
    generalize (rr_pick 1 m); intro j.
    apply (Fin.caseS' j); [|intro j'; apply (Fin.caseS' j'); [|intro j''; inversion j'']].
    + destruct H1 as [-> | ->];
        [change ([fresh 1; t2] : pool sE Bn 2) with (([spent 1; t2] : pool sE Bn 2) @ child := fresh 1)
        |change ([spent 1; t2] : pool sE Bn 2) with (([spent 1; t2] : pool sE Bn 2) @ child := spent 1);
         rewrite spent_focus_rr];
      apply (turn_rr R _ _ 1 2 a b ctx c _ _ _ Hw (frame_rel_both_1 a b ctx c s HE HA));
      intros s' HE' HA';
      change (([spent 1; t2] : pool sE Bn 2) @ child := spent 1) with ([spent 1; t2] : pool sE Bn 2);
      (apply (HR _ _ _ _ _ (S a) b ctx (S c)); [right; reflexivity | exact H2 | exact HE' | exact HA' | constructor]).
    + destruct H2 as [-> | ->];
        [change ([t1; fresh 2] : pool sE Bn 2) with (([t1; spent 2] : pool sE Bn 2) @ parent := fresh 2)
        |change ([t1; spent 2] : pool sE Bn 2) with (([t1; spent 2] : pool sE Bn 2) @ parent := spent 2);
         rewrite spent_focus_rr];
      apply (turn_rr R _ _ 2 1 b a ctx c _ _ _ Hw (frame_rel_both_2 a b ctx c s HE HA));
      intros s' HE' HA';
      change (([t1; spent 2] : pool sE Bn 2) @ parent := spent 2) with ([t1; spent 2] : pool sE Bn 2);
      (apply (HR _ _ _ _ _ a (S b) ctx (S c)); [exact H1 | right; reflexivity | | exact HA' | constructor]);
      (eapply peq_trans; [exact HE' | apply pop_comm, region_disj; auto]).
Qed.


(** ** ND: the owned action clock and its two distinct progress measures *)
Module OwnedLoops.
#[local] Unset Universe Polymorphism.
Local Open Scope nat_scope.

Local Lemma vis_cong {X} (e : CEff X) (k k' : X -> thread sE Bn) :
  (forall x, k x ≅ k' x) -> Vis e k ≅ Vis e k'.
Proof. intro H; step; constructor; exact H. Qed.

Local Lemma guard_cong (t u : thread sE Bn) : t ≅ u -> Guard t ≅ Guard u.
Proof. intro H; step; constructor; exact H. Qed.

Definition tY (i : nat) : thread sE Bn :=
  Vis (inl1 Yield : CEff unit) (fun _ => Guard (denote (lproc i))).
Definition tE (i v : nat) : thread sE Bn :=
  Vis (inr1 (inr1 (inr1 (inr1 (Log (i, S v))))) : CEff unit) (fun _ => tY i).
Definition tW (i v : nat) : thread sE Bn :=
  Vis (inr1 (inr1 (inl1 (HWrite i (S v)))) : CEff unit) (fun _ => tE i v).
Definition tR (i : nat) : thread sE Bn :=
  Vis (inr1 (inr1 (inl1 (HRead i))) : CEff nat) (fun v => tW i v).

Lemma lproc_unfold i : denote (lproc i) ≅ tR i.
Proof.
  unfold denote at 1, lproc; rewrite source_raw_until; unfold lproc_body, work.
  rewrite source_raw_bind, source_raw_bind, source_raw_read_head.
  unfold tR; apply vis_cong; intro v.
  rewrite source_raw_bind, source_raw_write_head.
  unfold tW; apply vis_cong; intros [].
  rewrite source_raw_emit_head.
  unfold tE; apply vis_cong; intros [].
  rewrite source_raw_bind, source_raw_yield_head.
  unfold tY; apply vis_cong; intros [].
  rewrite source_raw_ret; reflexivity.
Qed.

Inductive phase := PR | PW | PE | PY.

Definition in_phase (i v : nat) (ph : phase) (t : thread sE Bn) : Prop :=
  match ph with
  | PR => exists n, t ≅ guards n (tR i)
  | PW => t ≅ tW i v
  | PE => t ≅ tE i v
  | PY => t ≅ tY i
  end.

Definition next_phase (ph : phase) : phase :=
  match ph with PR => PW | PW => PE | PE => PY | PY => PR end.
Definition next_value (v : nat) (ph : phase) : nat :=
  match ph with PY => S v | _ => v end.
Definition cell_value (v : nat) (ph : phase) : nat :=
  match ph with PR | PW => v | PE | PY => S v end.
Definition phase_thread (i v : nat) (ph : phase) : thread sE Bn :=
  match ph with PR => tW i v | PW => tE i v | PE => tY i
  | PY => Guard (denote (lproc i)) end.
Definition phase_kind (i v : nat) (ph : phase) (d : OwnedCfg) : OwnedKind :=
  match ph with PR => OARead | PW => OAWrite
  | PE => OAEmit (i, S v) (global_count d) | PY => OAYield end.
Definition phase_cfg (s : side) (i v : nat) (ph : phase) (d : OwnedCfg) : OwnedCfg :=
  match ph with
  | PW => set_heap d s (upd (fst (oc_heap d s)) i (S v), snd (oc_heap d s))
  | PE => emit_cfg d s (i, S v)
  | _ => d
  end.
Definition phase_focus {n} (j : Fin.t n) (ph : phase) : option (Fin.t n) :=
  match ph with PY => None | _ => Some j end.

Lemma in_phase_equ i v ph t u : t ≅ u -> in_phase i v ph t -> in_phase i v ph u.
Proof.
  intros E H; destruct ph; cbn in *.
  - destruct H as [n H]; exists n; etransitivity; [symmetry; exact E|exact H].
  - etransitivity; [symmetry; exact E|exact H].
  - etransitivity; [symmetry; exact E|exact H].
  - etransitivity; [symmetry; exact E|exact H].
Qed.

Lemma phase_thread_in i v ph t :
  t ≅ phase_thread i v ph -> in_phase i (next_value v ph) (next_phase ph) t.
Proof.
  destruct ph; cbn; intro H; try exact H.
  exists 1; cbn; rewrite H; apply guard_cong, lproc_unfold.
Qed.

(** These are the real read/write/emit/yield rules of [owned_step]. *)
Lemma phase_step d n (ts : pool sE Bn (S n)) tags j i v ph a d' :
  in_phase i v ph (ts $ j) ->
  fst (oc_heap d (tags $ j)) i = Some (cell_value v ph) ->
  focus_step d n ts tags j a d' ->
  exists t, t ≅ phase_thread i v ph /\ a = act (tags $ j) (phase_kind i v ph d) /\
    d' = set_pool (phase_cfg (tags $ j) i v ph d)
      (mk_pool (S n) (ts @ j := t) tags (phase_focus j ph)).
Proof.
  intros Hph Hcell H; destruct ph; cbn in Hph, Hcell |- *.
  - destruct Hph as [m Hm]; unfold tR in Hm.
    apply (focus_step_head_prim d n ts tags j _ _ _ _ _ Hm) in H
      as (k & kind & y & d1 & Hk & Hprim & -> & ->).
    cbn in Hprim; rewrite Hcell in Hprim; injection Hprim as <- <- <-.
    exists (k v); split; [apply Hk|split; reflexivity].
  - unfold tW in Hph.
    apply (focus_step_head_prim d n ts tags j _ _ 0 _ _ Hph) in H
      as (k & kind & y & d1 & Hk & Hprim & -> & ->).
    cbn in Hprim; rewrite Hcell in Hprim; injection Hprim as <- <- <-.
    exists (k tt); split; [apply Hk|split; reflexivity].
  - unfold tE in Hph.
    apply (focus_step_head_prim d n ts tags j _ _ 0 _ _ Hph) in H
      as (k & kind & y & d1 & Hk & Hprim & -> & ->).
    cbn in Hprim; injection Hprim as <- <- <-.
    exists (k tt); split; [apply Hk|split; reflexivity].
  - unfold tY in Hph.
    apply (focus_step_head_yield d n ts tags j _ 0 _ _ Hph) in H as (k & Hk & -> & ->).
    exists (k tt); split; [apply Hk|split; reflexivity].
Qed.

Lemma phase_step_intro d n (ts : pool sE Bn (S n)) tags j i v ph :
  in_phase i v ph (ts $ j) ->
  fst (oc_heap d (tags $ j)) i = Some (cell_value v ph) ->
  focus_step d n ts tags j (act (tags $ j) (phase_kind i v ph d))
    (set_pool (phase_cfg (tags $ j) i v ph d)
      (mk_pool (S n) (ts @ j := phase_thread i v ph) tags (phase_focus j ph))).
Proof.
  intros Hph Hcell; destruct ph; cbn in Hph, Hcell |- *.
  - destruct Hph as [m Hm]; unfold tR in Hm.
    apply (focus_step_head_prim d n ts tags j _ _ _ _ _ Hm).
    exists (fun x => tW i x), OARead, v, d.
    split; [intro; reflexivity|split; [cbn; rewrite Hcell; reflexivity|split; reflexivity]].
  - unfold tW in Hph.
    apply (focus_step_head_prim d n ts tags j _ _ 0 _ _ Hph).
    exists (fun _ => tE i v), OAWrite, tt.
    eexists; split; [intro; reflexivity|].
    split; [cbn; rewrite Hcell; reflexivity|split; reflexivity].
  - unfold tE in Hph.
    apply (focus_step_head_prim d n ts tags j _ _ 0 _ _ Hph).
    exists (fun _ => tY i), (OAEmit (i, S v) (global_count d)), tt.
    eexists; split; [intro; reflexivity|split; [reflexivity|split; reflexivity]].
  - unfold tY in Hph.
    apply (focus_step_head_yield d n ts tags j _ 0 _ _ Hph).
    exists (fun _ => Guard (denote (lproc i))); split; [intro; reflexivity|split; reflexivity].
Qed.

Lemma phase_cfg_own s i v ph d :
  fst (oc_heap d s) i = Some (cell_value v ph) ->
  fst (oc_heap (phase_cfg s i v ph d) s) i =
    Some (cell_value (next_value v ph) (next_phase ph)).
Proof.
  intro H; destruct ph; cbn; try exact H.
  unfold side_upd; rewrite (proj2 (side_eqb_spec s s) eq_refl); apply upd_eq.
Qed.

Lemma phase_cfg_other s k i v ph d :
  s <> k -> oc_heap (phase_cfg s i v ph d) k = oc_heap d k.
Proof.
  intro H; destruct ph; cbn; try reflexivity.
  unfold side_upd; destruct (side_eqb k s) eqn:E; [|reflexivity].
  apply side_eqb_spec in E; congruence.
Qed.

(** Release counts down to Yield: read/write/emit/yield have ranks 4/3/2/1.
    Visibility instead counts only erased actions: 3/2/0/1.  In particular
    emission resets visibility's countdown, and selection is already visible. *)
Definition head_release (t : thread sE Bn) : nat :=
  match observe t with
  | VisF e _ => match e with
    | inl1 _ => 1
    | inr1 (inr1 (inr1 (inr1 _))) => 2
    | inr1 (inr1 (inl1 (HWrite _ _))) => 3
    | _ => 4 end
  | _ => 4 end.
Definition head_visible (t : thread sE Bn) : nat :=
  match observe t with
  | VisF e _ => match e with
    | inl1 _ => 1
    | inr1 (inr1 (inr1 (inr1 _))) => 0
    | inr1 (inr1 (inl1 (HWrite _ _))) => 2
    | _ => 3 end
  | _ => 3 end.

Lemma head_ranks_equ t u : t ≅ u ->
  head_release t = head_release u /\ head_visible t = head_visible u.
Proof.
  intro H; unfold head_release, head_visible; step in H; cbn in H.
  remember (observe t) as ot; remember (observe u) as ou; destruct H; subst; split; reflexivity.
Qed.

Definition phase_release (ph : phase) : nat :=
  match ph with PR => 4 | PW => 3 | PE => 2 | PY => 1 end.
Definition phase_visible (ph : phase) : nat :=
  match ph with PR => 3 | PW => 2 | PE => 0 | PY => 1 end.

Lemma head_release_phase i v ph t : in_phase i v ph t -> head_release t = phase_release ph.
Proof.
  destruct ph; cbn; intro H.
  - destruct H as [[|m] Hm]; rewrite (proj1 (head_ranks_equ _ _ Hm)); reflexivity.
  - rewrite (proj1 (head_ranks_equ _ _ H)); reflexivity.
  - rewrite (proj1 (head_ranks_equ _ _ H)); reflexivity.
  - rewrite (proj1 (head_ranks_equ _ _ H)); reflexivity.
Qed.

Lemma head_visible_phase i v ph t : in_phase i v ph t -> head_visible t = phase_visible ph.
Proof.
  destruct ph; cbn; intro H.
  - destruct H as [[|m] Hm]; rewrite (proj2 (head_ranks_equ _ _ Hm)); reflexivity.
  - rewrite (proj2 (head_ranks_equ _ _ H)); reflexivity.
  - rewrite (proj2 (head_ranks_equ _ _ H)); reflexivity.
  - rewrite (proj2 (head_ranks_equ _ _ H)); reflexivity.
Qed.

Definition release_total (d : OwnedCfg) : nat :=
  match focused_thread (oc_pool d) with Some (t, _) => head_release t | None => 0 end.
Definition release_rank (i : side) (d : OwnedCfg) : nat :=
  match focused_thread (oc_pool d) with
  | Some (t, j) => if side_eqb j i then 0 else head_release t
  | None => 0 end.
Definition visible_rank (d : OwnedCfg) : nat :=
  match focused_thread (oc_pool d) with Some (t, _) => head_visible t | None => 0 end.

Lemma phase_release_drop d n (ts : pool sE Bn (S n)) tags j i v ph t :
  in_phase i v ph (ts $ j) ->
  in_phase i (next_value v ph) (next_phase ph) t ->
  release_total (set_pool (phase_cfg (tags $ j) i v ph d)
    (mk_pool (S n) (ts @ j := t) tags (phase_focus j ph))) < head_release (ts $ j).
Proof.
  intros Hph Ht; unfold release_total, focused_thread; cbn [oc_pool set_pool mk_pool tp_focus tp_threads tp_tags].
  rewrite (head_release_phase _ _ _ _ Hph).
  destruct ph; cbn [phase_focus] in *; rewrite ?Vector.nth_replace_eq;
    try rewrite (head_release_phase _ _ _ _ Ht); cbn [phase_release next_phase]; lia.
Qed.

Lemma phase_visible_drop d n (ts : pool sE Bn (S n)) tags j i v ph t :
  in_phase i v ph (ts $ j) ->
  in_phase i (next_value v ph) (next_phase ph) t ->
  erase_action_label (act (tags $ j) (phase_kind i v ph d)) = None ->
  visible_rank (set_pool (phase_cfg (tags $ j) i v ph d)
    (mk_pool (S n) (ts @ j := t) tags (phase_focus j ph))) < head_visible (ts $ j).
Proof.
  intros Hph Ht Hnone; unfold visible_rank, focused_thread; cbn [oc_pool set_pool mk_pool tp_focus tp_threads tp_tags].
  rewrite (head_visible_phase _ _ _ _ Hph).
  destruct ph; cbn [erase_action_label phase_kind act action_kind] in Hnone; try discriminate;
    cbn [phase_focus] in *; rewrite ?Vector.nth_replace_eq;
    try rewrite (head_visible_phase _ _ _ _ Ht); cbn [phase_visible next_phase]; lia.
Qed.

(** No history or scheduler implementation is stored: just the canonical
    two-slot pool, each slot's current source phase, and its own live cell. *)
Definition Inv (d : OwnedCfg) : Prop :=
  owned_wf d /\ exists tc tp f a b phC phP,
    oc_pool d = mk_pool 2 [tc; tp] [Child; Parent] f /\
    in_phase 1 a phC tc /\ in_phase 2 b phP tp /\
    fst (oc_heap d Child) 1 = Some (cell_value a phC) /\
    fst (oc_heap d Parent) 2 = Some (cell_value b phP).

Local Lemma two_pool_equ d e tc tp f :
  owned_equ d e -> oc_pool d = mk_pool 2 [tc; tp] [Child; Parent] f ->
  exists uc up, oc_pool e = mk_pool 2 [uc; up] [Child; Parent] f /\ tc ≅ uc /\ tp ≅ up.
Proof.
  intros E Hp; destruct (oc_pool e) as [n ts tags f'] eqn:He.
  change (oc_pool e = mk_pool n ts tags f') in He.
  assert (Ep : tp_equ (mk_pool 2 [tc; tp] [Child; Parent] f) (mk_pool n ts tags f')).
  { rewrite <- Hp, <- He; exact (proj1 E). }
  assert (Hn : n = 2) by (symmetry; exact (tp_equ_size _ _ Ep)); subst n.
  apply tp_equ_mk in Ep as (Et & Hg & Hf); subst tags; subst f'.
  exists (ts $ Fin.F1), (ts $ Fin.FS Fin.F1); split.
  - assert (Hv : ts = [ts $ Fin.F1; ts $ Fin.FS Fin.F1])
      by (repeat dependent destruction ts; reflexivity).
    rewrite Hv; reflexivity.
  - split; [exact (Et Fin.F1)|exact (Et (Fin.FS Fin.F1))].
Qed.

Lemma Inv_transport d e : owned_equ d e -> Inv d -> Inv e.
Proof.
  intros E (Hwf & tc & tp & f & a & b & phC & phP & Hpool & HC & HP & Hc & Hp).
  destruct (two_pool_equ d e tc tp f E Hpool) as (uc & up & Hpool' & EC & EP).
  split; [exact (owned_wf_equ d e E Hwf)|].
  exists uc, up, f, a, b, phC, phP; split; [exact Hpool'|].
  split; [exact (in_phase_equ _ _ _ _ _ EC HC)|].
  split; [exact (in_phase_equ _ _ _ _ _ EP HP)|].
  destruct E as (_ & _ & Eh & _); split.
  - rewrite <- (proj1 (Eh Child) 1); exact Hc.
  - rewrite <- (proj1 (Eh Parent) 2); exact Hp.
Qed.

Lemma Inv_proper : hproper Inv.
Proof.
  intros d e E; split; intro H; eapply Inv_transport; [exact E|exact H|symmetry; exact E|exact H].
Qed.

Lemma Inv_init a b ctx c :
  Inv (init_owned (lproc 1) (lproc 2) (region 1 a) (region 2 b) ctx c).
Proof.
  split; [apply init_owned_wf; [apply managed_wf_preallocated|apply managed_wf_preallocated|apply region_disj; lia]|].
  exists (denote (lproc 1)), (denote (lproc 2)), (Some (Fin.FS Fin.F1)), a, b, PR, PR.
  split; [reflexivity|split; [exists 0; apply lproc_unfold|]].
  split; [exists 0; apply lproc_unfold|split; apply hsingle_eq].
Qed.

Lemma Inv_step d a d' : Inv d -> owned_step d a d' ->
  Inv d' /\ (focused_thread (oc_pool d) = None \/ release_total d' < release_total d) /\
  (erase_action_label a = None -> visible_rank d' < visible_rank d).
Proof.
  intros HI Hs; pose proof HI as (Hwf & tc & tp & f & vC & vP & phC & phP & Hpool & HC & HP & Hc & Hp).
  pose proof (owned_step_wf d a d' Hwf Hs) as Hwf'.
  unfold owned_step in Hs; rewrite Hpool in Hs; cbn -[sel_step focus_step] in Hs.
  destruct f as [j|].
  - dependent destruction j.
    + destruct (phase_step d 1 [tc; tp] [Child; Parent] Fin.F1 1 vC phC a d' HC Hc Hs)
        as (t & Ht & -> & ->).
      pose proof (phase_thread_in _ _ _ _ Ht) as Hin.
      split.
      * split; [exact Hwf'|].
        exists t, tp, (phase_focus Fin.F1 phC), (next_value vC phC), vP, (next_phase phC), phP.
        split; [reflexivity|split; [exact Hin|split; [exact HP|split]]].
        -- cbn [set_pool oc_heap]; apply phase_cfg_own, Hc.
        -- cbn [set_pool oc_heap]; rewrite phase_cfg_other by discriminate; exact Hp.
      * split.
        -- right; unfold release_total at 2; unfold focused_thread; rewrite Hpool; cbn.
           exact (phase_release_drop d 1 [tc; tp] [Child; Parent] Fin.F1 1 vC phC t HC Hin).
        -- intro Hnone; unfold visible_rank at 2; unfold focused_thread; rewrite Hpool; cbn.
           exact (phase_visible_drop d 1 [tc; tp] [Child; Parent] Fin.F1 1 vC phC t HC Hin Hnone).
    + dependent destruction j; [|inversion j].
      destruct (phase_step d 1 [tc; tp] [Child; Parent] (Fin.FS Fin.F1) 2 vP phP a d' HP Hp Hs)
        as (t & Ht & -> & ->).
      pose proof (phase_thread_in _ _ _ _ Ht) as Hin.
      split.
      * split; [exact Hwf'|].
        exists tc, t, (phase_focus (Fin.FS Fin.F1) phP), vC, (next_value vP phP), phC, (next_phase phP).
        split; [reflexivity|split; [exact HC|split; [exact Hin|split]]].
        -- cbn [set_pool oc_heap]; rewrite phase_cfg_other by discriminate; exact Hc.
        -- cbn [set_pool oc_heap]; apply phase_cfg_own, Hp.
      * split.
        -- right; unfold release_total at 2; unfold focused_thread; rewrite Hpool; cbn.
           exact (phase_release_drop d 1 [tc; tp] [Child; Parent] (Fin.FS Fin.F1) 2 vP phP t HP Hin).
        -- intro Hnone; unfold visible_rank at 2; unfold focused_thread; rewrite Hpool; cbn.
           exact (phase_visible_drop d 1 [tc; tp] [Child; Parent] (Fin.FS Fin.F1) 2 vP phP t HP Hin Hnone).
  - destruct Hs as (j & -> & ->); split.
    + split; [exact Hwf'|].
      exists tc, tp, (Some j), vC, vP, phC, phP.
      split; [reflexivity|split; [exact HC|split; [exact HP|split; assumption]]].
    + split; [left; unfold focused_thread; rewrite Hpool; reflexivity|discriminate].
Qed.

Lemma Inv_closed : step_closed Inv.
Proof. intros d a d' HI Hs; exact (proj1 (Inv_step d a d' HI Hs)). Qed.

Lemma Inv_visible d a d' : Inv d -> owned_step d a d' ->
  erase_action_label a = None -> visible_rank d' < visible_rank d.
Proof. intros HI Hs; exact (proj2 (proj2 (Inv_step d a d' HI Hs))). Qed.

Lemma Inv_select d i : Inv d -> focused_thread (oc_pool d) = None ->
  exists d', owned_step d (act i OASelect) d'.
Proof.
  intros (_ & tc & tp & f & vC & vP & phC & phP & Hpool & _) Hf.
  unfold focused_thread in Hf; rewrite Hpool in Hf; destruct f as [j|]; [discriminate|].
  unfold owned_step; rewrite Hpool; cbn -[sel_step].
  destruct i; eexists; [exists Fin.F1|exists (Fin.FS Fin.F1)]; split; reflexivity.
Qed.

Lemma Inv_can d : Inv d -> hcan_step owned_next d.
Proof.
  intro HI; pose proof HI as (_ & tc & tp & f & vC & vP & phC & phP & Hpool & HC & HP & Hc & Hp).
  destruct f as [j|].
  - dependent destruction j.
    + eexists; eexists; unfold owned_step; rewrite Hpool; cbn -[focus_step].
      exact (phase_step_intro d 1 [tc; tp] [Child; Parent] Fin.F1 1 vC phC HC Hc).
    + dependent destruction j; [|inversion j].
      eexists; eexists; unfold owned_step; rewrite Hpool; cbn -[focus_step].
      exact (phase_step_intro d 1 [tc; tp] [Child; Parent] (Fin.FS Fin.F1) 2 vP phP HP Hp).
  - destruct (Inv_select d Child HI) as [d' Hs].
    + unfold focused_thread; rewrite Hpool; reflexivity.
    + exists d', (act Child OASelect); exact Hs.
Qed.

Lemma release_rank_le i d : release_rank i d <= release_total d.
Proof.
  unfold release_rank, release_total; destruct (focused_thread (oc_pool d)) as [[t j]|];
    [destruct (side_eqb j i)|]; lia.
Qed.

Local Lemma focused_owner d a d' t i :
  focused_thread (oc_pool d) = Some (t, i) -> owned_step d a d' -> owner a = i.
Proof.
  unfold focused_thread; destruct (tp_focus (oc_pool d)) as [j|] eqn:Hf; [|discriminate].
  intros [= _ <-] Hs; exact (owned_step_focused_owner d a d' Hs j Hf).
Qed.

Lemma Inv_release i : finite_release i Inv (release_rank i).
Proof.
  intros d HI Hcan.
  destruct (scheduler_shape i d Hcan) as [Hst|Hown]; [right|left; exact Hown].
  destruct Hcan as (d' & a & Hs).
  destruct (Inv_step d a d' HI Hs) as (HI' & [Hf|Hr] & _).
  - exfalso; destruct (Inv_select d i HI Hf) as [d'' Hsel].
    exact (Hst _ _ Hsel eq_refl).
  - exists d'; split; [exists a; split; [exact Hs|exact (Hst _ _ Hs)]|split; [exact HI'|]].
    assert (Hj : release_rank i d = release_total d).
    { unfold release_rank, release_total; destruct (focused_thread (oc_pool d)) as [[t j]|] eqn:Ef; [|reflexivity].
      destruct (side_eqb j i) eqn:E; [|reflexivity].
      apply side_eqb_spec in E; subst j.
      exfalso; exact (Hst _ _ Hs (focused_owner _ _ _ _ _ Ef Hs)). }
    rewrite Hj; eapply Nat.le_lt_trans; [apply release_rank_le|exact Hr].
Qed.

Lemma admitted a b ctx c :
  admissible (lproc 1) (lproc 2) (region 1 a) (region 2 b) ctx c.
Proof.
  apply admissible_intro.
  - apply managed_wf_preallocated.
  - apply managed_wf_preallocated.
  - apply region_disj; lia.
  - cbn; repeat split; auto.
  - cbn; repeat split; auto.
  - cbn; repeat split; discriminate.
  - cbn; repeat split; discriminate.
Qed.

Theorem global_hag a b ctx c :
  hAG owned_next Inv (init_owned (lproc 1) (lproc 2) (region 1 a) (region 2 b) ctx c).
Proof.
  apply (hAG_coind _ _ Inv); [|apply Inv_init].
  intros d HI; split; [exact HI|split; [apply Inv_can, HI|]].
  intros d' [a' Hs]; exact (Inv_closed d a' d' HI Hs).
Qed.

Definition live_cell (i : side) (addr : nat) : hprop :=
  fun d => exists v, fst (oc_heap d i) addr = Some v.

Lemma live_cell_proper i addr : hproper (live_cell i addr).
Proof.
  intros d e (_ & _ & Eh & _); unfold live_cell.
  destruct (Eh i) as [Hh _]; unfold heq in Hh; rewrite Hh; reflexivity.
Qed.

Lemma Inv_hsep d : Inv d -> hsep (live_cell Child 1) (live_cell Parent 2) d.
Proof.
  intros (Hwf & tc & tp & f & a & b & phC & phP & _ & _ & _ & Hc & Hp).
  split; [exact Hwf|split; [exists (cell_value a phC); exact Hc|exists (cell_value b phP); exact Hp]].
Qed.

(** An actual application of the directional global-to-local split.  Release
    of a foreign focus proves both focused local AG facts; it is not the
    visibility premise used below to recover the original runner clock. *)
Theorem local_hag a b ctx c :
  hAG owned_next (live_cell Child 1) (init_local Child (lproc 1) (region 1 a) ctx c true) /\
  hAG owned_next (live_cell Parent 2) (init_local Parent (lproc 2) (region 2 b) ctx c true).
Proof.
  apply (fork_hag_split (lproc 1) (fun _ => lproc 2) (region 1 a) (region 2 b) ctx c
    Inv (release_rank Child) (release_rank Parent) (live_cell Child 1) (live_cell Parent 2)).
  - apply admitted.
  - apply live_cell_proper.
  - apply live_cell_proper.
  - apply Inv_init.
  - apply Inv_closed.
  - apply Inv_release.
  - apply Inv_release.
  - eapply hAG_mono; [intros d HI; apply Inv_hsep, HI|apply global_hag].
Qed.
End OwnedLoops.

(** ** The pool properties: the first (focused) turn, then the invariant. *)
(** Two framed cooperative loops remain safe forever under round-robin scheduling. *)
Theorem ag_two_procs_rr a b ctx c :
  <( {run_rr (fork2 (lproc 1) (lproc 2)) (shared a b ctx c)}, Pure |= AG ⊤ )>.
Proof.
  unfold fork2; rewrite run_rr_fork_bind, unfold_entailsL.
  change ([denote (lproc 1); denote (lproc 2)] : pool sE Bn 2) with
    (([fresh 1; spent 2] : pool sE Bn 2) @ parent := fresh 2).
  apply (turn_rr (chain_gfp _) _ _ 2 1 b a ctx c _ _ _ ltac:(constructor) (frame_rel_shared_2 a b ctx c)).
  intros s' HE' HA'.
  change (([fresh 1; spent 2] : pool sE Bn 2) @ parent := spent 2) with ([fresh 1; spent 2] : pool sE Bn 2).
  apply (pool_ag_rr (chain_gfp _) _ _ _ _ _ a (S b) ctx (S c));
    [left; reflexivity | right; reflexivity | | exact HA' | constructor].
  eapply peq_trans; [exact HE' | apply pop_comm, region_disj; auto].
Qed.

(** Two framed cooperative loops remain safe forever under nondeterministic scheduling. *)
Theorem ag_two_procs_nd a b ctx c :
  <( {run_nd (fork2 (lproc 1) (lproc 2)) (shared a b ctx c)}, Pure |= AG ⊤ )>.
Proof.
  unfold fork2, shared.
  exact (fork_hag_ticl (lproc 1) (fun _ => lproc 2)
    (region 1 a) (region 2 b) ctx c OwnedLoops.Inv OwnedLoops.visible_rank
    (OwnedLoops.admitted a b ctx c) OwnedLoops.Inv_proper
    OwnedLoops.Inv_visible (OwnedLoops.global_hag a b ctx c)).
Qed.

(** Instantiate round-robin loop safety with concrete initial cell values. *)
Example ag_rr_3_5 ctx : <( {run_rr (fork2 (lproc 1) (lproc 2)) (shared 3 5 ctx 0)}, Pure |= AG ⊤ )>.
Proof. apply ag_two_procs_rr. Qed.
(** Instantiate nondeterministic loop safety with concrete initial cell values. *)
Example ag_nd_3_5 ctx : <( {run_nd (fork2 (lproc 1) (lproc 2)) (shared 3 5 ctx 0)}, Pure |= AG ⊤ )>.
Proof. apply ag_two_procs_nd. Qed.

Print Assumptions ag_two_procs_rr.
Print Assumptions ag_two_procs_nd.
