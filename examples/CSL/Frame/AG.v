(** * Regression: two cooperative loops never fault and never stop.

    [fork2 (lproc 1) (lproc 2)]: each process loops forever on its own cell
    ([work i], then [CYield]).  Each turn is proved on the process's own
    region and framed by the other one, then rejoined to the pool through the
    cooperative prefix equation; the coinductive invariant lives on the
    unfocused pool.  ponytail: [AG ⊤] only; the recurrence [AG (AF visW _)]
    needs [(AF visW _) AU done R] per turn — add when a client needs it. *)
From Stdlib Require Import Fin Vector.
From Coinduction Require Import all.
From examples Require Import CSL.Frame.Shared.
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

(** A spent slot also re-enters its loop under nondeterministic scheduling. *)
Lemma spent_focus_nd (ts : pool sE Bn 2) (j : Fin.t 2) i s :
  interp_schedule_nd sh 2 (ts @ j := spent i) (Some j) s ~
  interp_schedule_nd sh 2 (ts @ j := fresh i) (Some j) s.
Proof.
  unfold spent; rewrite interp_nd_source_ret.
  erewrite (interp_schedule_nd_guard sh) by (rewrite Vector.nth_replace_eq; reflexivity).
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

(** A nondeterministic turn runs [work i] with the other cell framed, then yields. *)
Lemma turn_nd (R : Chain agtop) (ts : pool sE Bn 2) (j : Fin.t 2) i k a b ctx c s w :
  not_done w ->
  frame_rel (region k b) (own i a ctx c) s ->
  (forall s', csl_memory s' ≈ region i (S a) ⊎ region k b -> snd s' = (ctx, S c) ->
     `R (interp_schedule_nd sh 2 (ts @ j := spent i) None s')
        (Obs (Log (inr (stamp (i, S a) c))) tt)) ->
  `R (interp_schedule_nd sh 2 (ts @ j := fresh i) (Some j) s) w.
Proof.
  intros Hw HR HK.
  unfold fresh, denote, lproc, lproc_body.
  rewrite interp_nd_source_until_none; nd_prefix work_yield_fork_free.
  apply (ag_bind_done_chain _ (frame_post (region k b) (Qwork i a ctx c)));
    [exact Hw | apply work_af_framed; assumption |].
  intros [s' r] w' HP; apply frame_post_work in HP as (-> & HE & HA & ->).
  cbv beta iota.
  rewrite interp_nd_source_bind, interp_nd_source_yield.
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

(** Every nondeterministic selection preserves the loop and disjoint-heap invariant. *)
Lemma pool_ag_nd : forall R : Chain agtop,
  forall t1 t2 s w a b ctx c, slot 1 t1 -> slot 2 t2 ->
  csl_memory s ≈ region 1 a ⊎ region 2 b -> snd s = (ctx, c) -> not_done w ->
  `R (interp_schedule_nd sh 2 [t1; t2] None s) w.
Proof.
  apply (tower (b := agtop) (P := fun R => forall t1 t2 s w a b ctx c, slot 1 t1 -> slot 2 t2 ->
    csl_memory s ≈ region 1 a ⊎ region 2 b -> snd s = (ctx, c) -> not_done w ->
    R (interp_schedule_nd sh 2 [t1; t2] None s) w)).
  - intros T HT t1 t2 s w a b ctx c H1 H2 HE HA Hw R HR; apply (HT R HR _ _ _ _ a b ctx c); auto.
  - intros R HR t1 t2 s w a b ctx c H1 H2 HE HA Hw; cbn.
    rewrite (interp_schedule_nd_select sh).
    split; [split; [exact I | exact Hw]|].
    split; [apply (can_step_brS _ _ child); exact Hw|].
    intros t' w' TR; apply ktrans_brS in TR as (j & Heq & -> & _); rewrite Heq; clear Heq.
    apply (Fin.caseS' j); [|intro j'; apply (Fin.caseS' j'); [|intro j''; inversion j'']].
    + destruct H1 as [-> | ->];
        [change ([fresh 1; t2] : pool sE Bn 2) with (([spent 1; t2] : pool sE Bn 2) @ child := fresh 1)
        |change ([spent 1; t2] : pool sE Bn 2) with (([spent 1; t2] : pool sE Bn 2) @ child := spent 1);
         rewrite spent_focus_nd];
      apply (turn_nd R _ _ 1 2 a b ctx c _ _ Hw (frame_rel_both_1 a b ctx c s HE HA));
      intros s' HE' HA';
      change (([spent 1; t2] : pool sE Bn 2) @ child := spent 1) with ([spent 1; t2] : pool sE Bn 2);
      (apply (HR _ _ _ _ (S a) b ctx (S c)); [right; reflexivity | exact H2 | exact HE' | exact HA' | constructor]).
    + destruct H2 as [-> | ->];
        [change ([t1; fresh 2] : pool sE Bn 2) with (([t1; spent 2] : pool sE Bn 2) @ parent := fresh 2)
        |change ([t1; spent 2] : pool sE Bn 2) with (([t1; spent 2] : pool sE Bn 2) @ parent := spent 2);
         rewrite spent_focus_nd];
      apply (turn_nd R _ _ 2 1 b a ctx c _ _ Hw (frame_rel_both_2 a b ctx c s HE HA));
      intros s' HE' HA';
      change (([t1; spent 2] : pool sE Bn 2) @ parent := spent 2) with ([t1; spent 2] : pool sE Bn 2);
      (apply (HR _ _ _ _ a (S b) ctx (S c)); [exact H1 | right; reflexivity | | exact HA' | constructor]);
      (eapply peq_trans; [exact HE' | apply pop_comm, region_disj; auto]).
Qed.

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
  unfold fork2; rewrite run_nd_fork_bind, unfold_entailsL.
  change ([denote (lproc 1); denote (lproc 2)] : pool sE Bn 2) with
    (([fresh 1; spent 2] : pool sE Bn 2) @ parent := fresh 2).
  apply (turn_nd (chain_gfp _) _ _ 2 1 b a ctx c _ _ ltac:(constructor) (frame_rel_shared_2 a b ctx c)).
  intros s' HE' HA'.
  change (([fresh 1; spent 2] : pool sE Bn 2) @ parent := spent 2) with ([fresh 1; spent 2] : pool sE Bn 2).
  apply (pool_ag_nd (chain_gfp _) _ _ _ _ a (S b) ctx (S c));
    [left; reflexivity | right; reflexivity | | exact HA' | constructor].
  eapply peq_trans; [exact HE' | apply pop_comm, region_disj; auto].
Qed.

(** Instantiate round-robin loop safety with concrete initial cell values. *)
Example ag_rr_3_5 ctx : <( {run_rr (fork2 (lproc 1) (lproc 2)) (shared 3 5 ctx 0)}, Pure |= AG ⊤ )>.
Proof. apply ag_two_procs_rr. Qed.
(** Instantiate nondeterministic loop safety with concrete initial cell values. *)
Example ag_nd_3_5 ctx : <( {run_nd (fork2 (lproc 1) (lproc 2)) (shared 3 5 ctx 0)}, Pure |= AG ⊤ )>.
Proof. apply ag_two_procs_nd. Qed.

Print Assumptions ag_two_procs_rr.
Print Assumptions ag_two_procs_nd.
