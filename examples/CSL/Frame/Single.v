(** * Regression: the heap frame rule on a single CSL process.

    [p] reads cell [1] and writes back its successor.  The property is proved
    on the one-cell heap, then transported by [aur_csl_frame_done] to the heap
    extended by the disjoint cell [2]; the framed postcondition still exposes
    the untouched frame.  The negative check shows allocation is not
    framable, and the prefix check frames an [AG] of the emit loop. *)
From examples Require Import CSL.Frame.Shared.


(** Read cell [1] and write its successor. *)
Definition p : CProg unit := CBind (CRead 1) (fun v => CWrite 1 (S v)).
(** Initial state with cell [1] owned and no shared heap. *)
Definition s0 (ctx : Ctx.Ctx) : SSig := ((hsingle 1 0, hemp), (ctx, 0)).
(** Disjoint region containing the untouched cell [2]. *)
Definition fr : ManagedHeap := (hsingle 2 7, hemp).

(** The standalone run: cell [1] ends at [1]. *)
Lemma p_af ctx :
  <[ {run_nd p (s0 ctx)}, Pure |= AF done {fun '(s', _) _ => fst (csl_memory s') 1 = Some 1} ]>.
Proof.
  unfold run_nd, run_nd_pool, csl_pool, denote, s0; cbn [Vector.map].
  change ([denote_flow p;; Ret tt] : pool sE Bn 1) with
    (([Ret tt] : pool sE Bn 1) @ Fin.F1 := (denote_flow p >>= fun _ => Ret tt)).
  unfold p; rewrite aur_csl_nd_bind.
  rewrite aur_csl_nd_read with (value := 0) by (unfold hsingle; cbn; reflexivity).
  rewrite aur_csl_nd_write by (unfold hsingle; cbn; discriminate).
  rewrite (interp_schedule_nd_ret sh) by reflexivity.
  rewrite (interp_schedule_nd_empty sh).
  close_ret.
  reflexivity.
Qed.

(** The initial state admits the disjoint frame [fr]. *)
Lemma frame_inv_s0 ctx : frame_inv fr (s0 ctx).
Proof.
  apply (region_frame_inv 1 2 0 7 ctx 0); discriminate.
Qed.

(** The framed run on the two-cell heap: cell [1] ends at [1] and cell [2]
    is still [7]. *)
Theorem p_af_framed ctx :
  <[ {run_nd p (frame_state fr (s0 ctx))}, Pure |=
     AF done {fun '(s', _) _ => fst (csl_memory s') 1 = Some 1 /\ fst (csl_memory s') 2 = Some 7} ]>.
Proof.
  eapply aur_done_mono; [|apply (aur_csl_frame_done fr _ _ _
    (run_nd_framable p ltac:(cbn; tauto)) (frame_rel_state fr _ (frame_inv_s0 ctx)));
    [constructor|apply p_af]].
  intros [[M aux] x] ? HP; apply frame_post_iff in HP.
  destruct HP as (m & [HD _] & _ & [HE _] & HP); cbn in *.
  split.
  - rewrite (HE 1); unfold hunion; now rewrite HP.
  - rewrite (HE 2); unfold hunion.
    destruct (HD 2) as [H0|H0];
      [rewrite H0; apply hsingle_eq|rewrite hsingle_eq in H0; discriminate].
Qed.

(** Allocation is not framable. *)
Goal ~ Framable no_alloc_sE (heap_alloc (E:=sE) (B:=Bn) 1).
Proof.
  intro H; apply framable_unfold in H; cbn in H.
  ddestruction H; contradiction.
Qed.

(** Prefix frame: the emit loop never stops on the framed heap either. *)
Theorem emit_loop_ag_framed ctx :
  <( {run_nd (CUntilNone (CBind (CEmit 1 2) (fun _ => CRet (Some tt : option unit))))
        (frame_state fr (s0 ctx))}, Pure |= AG ⊤ )>.
Proof.
  apply (ticll_csl_frame fr _ _ _
    (run_nd_framable (CUntilNone (CBind (CEmit 1 2) (fun _ => CRet (Some tt : option unit)))) ltac:(cbn; tauto))
    (frame_rel_state fr _ (frame_inv_s0 ctx))).
  apply run_nd_emit_loop_ag; constructor.
Qed.

Print Assumptions p_af_framed.
