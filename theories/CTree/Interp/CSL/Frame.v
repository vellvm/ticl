From TICL Require Export CTree.Interp.CSL.Mod CTree.Logic.Sim Logic.Simulation.
From TICL Require Import CTree.Core Logic.Kripke Logic.Semantics
  CTree.Logic.Trans CTree.Interp.State.Mod Utils.Pcm.

Import CTree CTreeNotations TiclNotations CoindNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope pcm_scope.

(* ponytail: deterministic first-fit allocation is excluded; a nondeterministic
   allocator is needed before allocation can frame in the universal direction. *)
(** Admit all state events except deterministic absolute-heap allocation. *)
Definition no_alloc_sE : forall Y, sE Y -> Prop :=
  fun Y e => match e with inl1 (HAlloc _) => False | _ => True end.
(** Add a managed heap frame without changing auxiliary state. *)
Definition frame_state (fr: ManagedHeap) (s: SSig) : SSig :=
  (csl_memory s ⊎ fr, snd s).
(** The source owns a well-formed heap disjoint from the frame. *)
Definition frame_inv (fr: ManagedHeap) (s: SSig) : Prop :=
  csl_memory s # fr /\ managed_wf (csl_memory s).
(** The target adds disjoint [fr] up to [≈], with equal auxiliary state. *)
Definition frame_rel (fr: ManagedHeap) (s s': SSig) : Prop :=
  frame_inv fr s /\ snd s' = snd s /\ csl_memory s' ≈ csl_memory s ⊎ fr.
(** Frame-related results carry equal values and frame-related states. *)
Definition frameRV {X} (fr: ManagedHeap) : SSig * X -> SSig * X -> Prop :=
  fun '(s,x) '(s',x') => x' = x /\ frame_rel fr s s'.
(** Existentially frame a result postcondition. *)
Definition frame_post {A X} (fr: ManagedHeap)
  (P: SSig * X -> World (writerE (CSLObs A)) -> Prop) :=
  fun x' w => exists x, frameRV fr x x' /\ P x w.

(** A disjoint well-formed source is related to its explicitly framed state. *)
Lemma frame_rel_state fr s : frame_inv fr s -> frame_rel fr s (frame_state fr s).
Proof. intro H; split; [exact H|split; [reflexivity|apply peq_refl]]. Qed.


(** State interpretation preserves finite guarded-step prefixes. *)
Lemma guards_to_step_interp_state {E F B X Σ} (h: E ~> stateT Σ (ctree F B))
  (t: ctree E B X) s : guards_to_step t -> guards_to_step (interp_state h t s).
Proof.
  induction 1.
  - eapply guards_to_step_equ; [symmetry; apply unfold_interp_state|].
    eapply GtsStep; cbn; now rewrite H.
  - eapply guards_to_step_equ; [symmetry; apply unfold_interp_state|].
    eapply GtsGuard; [cbn; now rewrite H|exact IHguards_to_step].
Qed.

(** Reading an owned cell agrees in frame-related states. *)
Lemma frame_rel_read fr s s' a v : frame_rel fr s s' ->
  fst (csl_memory s) a = Some v -> fst (csl_memory s') a = Some v.
Proof.
  intros [[HD HW] [HA [HE _]]] HV.
  rewrite (HE a); eapply managed_read_pop; eauto.
Qed.

(** Writing an owned cell preserves the frame relation. *)
Lemma frame_rel_write fr s s' a v : frame_rel fr s s' -> fst (csl_memory s) a <> None ->
  frame_rel fr ((upd (fst (csl_memory s)) a v, snd (csl_memory s)), snd s)
    ((upd (fst (csl_memory s')) a v, snd (csl_memory s')), snd s').
Proof.
  destruct s as [[h al] aux], s' as [[h' al'] aux']; cbn.
  intros [[HD HW] [HA [HE HEa]]] HV.
  destruct (managed_write_pop (h,al) fr a v HD HV) as [HD' [HE' HEa']].
  split; [split; [exact HD'|now apply managed_write_preserves_wf]|].
  split; [exact HA|split; cbn in *].
  - eapply heq_trans; [apply upd_heq; exact HE|apply heq_sym; exact HE'].
  - exact HEa.
Qed.

(** Structural invariant: both trees interpret the same source under frame-related states. *)
Definition frame_tree {X} (fr: ManagedHeap)
  (t t': ctreeW (CSLObs (nat * nat)) Bn (SSig * X)) : Prop :=
  exists (u: ctree sE Bn X) s s', Framable no_alloc_sE u /\ frame_rel fr s s' /\
    t ≅ interp_state sh u s /\ t' ≅ interp_state sh u s'.

(** The interpreter invariant respects equivalence of both trees. *)
#[global] Instance frame_tree_equ {X} fr :
  Proper (equ eq ==> equ eq ==> iff) (@frame_tree X fr).
Proof.
  intros t u Htu t' u' Htu'; unfold frame_tree; split;
    intros (v & s & s' & HF & HR & HE & HE'); exists v, s, s'.
  all: split; [exact HF|split; [exact HR|split]].
  - now rewrite <- Htu.
  - now rewrite <- Htu'.
  - now rewrite Htu.
  - now rewrite Htu'.
Qed.

(** The same framable source in related states establishes the invariant. *)
Lemma frame_tree_intro {X} fr (u: ctree sE Bn X) s s' :
  Framable no_alloc_sE u -> frame_rel fr s s' ->
  frame_tree fr (interp_state sh u s) (interp_state sh u s').
Proof.
  intros HF HR; exists u, s, s'; split; [exact HF|split; [exact HR|split; reflexivity]].
Qed.

(** Leading guards preserve the interpreter invariant. *)
Lemma frame_tree_guard {X} fr (u: ctree sE Bn X) s s' :
  Framable no_alloc_sE u -> frame_rel fr s s' ->
  frame_tree fr (Guard (interp_state sh u s)) (Guard (interp_state sh u s')).
Proof.
  intros; rewrite <- !interp_state_guard; apply frame_tree_intro; auto using fr_guard.
Qed.

(** Auxiliary-state updates preserve the frame relation. *)
Lemma frame_rel_aux fr s s' a : frame_rel fr s s' ->
  frame_rel fr (csl_memory s, a) (csl_memory s', a).
Proof. intros [HI [HA HE]]; split; [exact HI|split; [reflexivity|exact HE]]. Qed.

Local Ltac stuck_shape := rewrite bind_stuck; apply CsStuckF.
Local Ltac guard_shape := apply CsGuardF, frame_tree_intro; [eauto|].
(** One interpreter step preserves [frame_tree], by cases on the framable source node. *)
Lemma frame_shape {X} (fr: ManagedHeap) (u: ctree sE Bn X) s s' :
  Framable no_alloc_sE u -> frame_rel fr s s' ->
  csim_shape (frameRV fr) (frame_tree fr)
    (observe (interp_state sh u s)) (observe (interp_state sh u s')).
Proof.
  intros HF HR;
  apply framable_unfold in HF.
  rewrite !unfold_interp_state; cbn.
  destruct HF; cbn.
  - apply CsRetF; split; auto.
  - apply CsStuckF.
  - apply CsStepF, frame_tree_guard; auto.
  - apply CsGuardF, frame_tree_intro; auto.
  - destruct e as [e|[e|e]].
    + destruct e; cbn [no_alloc_sE] in H; try contradiction;
        cbn [sh h_sum heap_handler].
      * destruct (fst (fst s) a) eqn:HV.
        -- assert (HV': fst (fst s') a = Some n) by (eapply frame_rel_read; eauto).
           rewrite HV'; rewrite !bind_ret_l.
           apply CsGuardF, frame_tree_intro; auto.
        -- stuck_shape.
      * destruct (fst (fst s) a) eqn:HV.
        -- assert (HV': fst (fst s') a = Some n) by (eapply frame_rel_read; eauto).
           rewrite HV'; rewrite !bind_ret_l.
           guard_shape.
           eapply frame_rel_write; [exact HR|unfold csl_memory; congruence].
        -- stuck_shape.
      * destruct (managed_free (fst s) a) as [m|] eqn:HM.
        -- destruct HR as [[HD HW] [HA HE]].
           destruct (managed_free_pop _ _ _ _ HD HW HM) as [[mf [HF HEf]] HDf].
           destruct (managed_free_peq _ _ _ _ (peq_sym _ _ HE) HF) as [mb [HB HEb]].
           unfold csl_memory in HB; rewrite HB, !bind_ret_l.
           guard_shape.
           split; [split; [exact HDf|eapply managed_free_preserves_wf; eauto]|].
           split; [exact HA|eapply peq_trans; [apply peq_sym; exact HEb|exact HEf]].
        -- stuck_shape.
      * destruct (fst (fst s) a) eqn:HV.
        -- assert (HV': fst (fst s') a = Some n) by (eapply frame_rel_read; eauto).
           rewrite HV'; destruct (Nat.eqb n expected); rewrite !bind_ret_l;
             guard_shape; [|exact HR].
           eapply frame_rel_write; [exact HR|unfold csl_memory; congruence].
        -- stuck_shape.
    + destruct e; cbn [sh h_sum csl_context_handler].
      * assert (HC: csl_context s' = csl_context s) by (unfold csl_context; now rewrite (proj1 (proj2 HR))).
        rewrite HC, !bind_ret_l; apply CsGuardF, frame_tree_intro; auto.
      * unfold log, CTree.trigger; rewrite !bind_bind, !bind_vis.
        apply CsVisF; intros []; rewrite !bind_ret_l.
        apply frame_tree_guard; [apply H0|].
        unfold csl_set_context, csl_counter; cbn.
        rewrite (proj1 (proj2 HR)); apply frame_rel_aux, HR.
    + destruct e; cbn [sh h_sum csl_emit_handler].
      assert (HC: csl_counter s' = csl_counter s) by (unfold csl_counter; now rewrite (proj1 (proj2 HR))).
      rewrite HC; unfold log, CTree.trigger; rewrite !bind_bind, !bind_vis.
      apply CsVisF; intros []; rewrite !bind_ret_l.
      apply frame_tree_guard; [apply H0|].
      unfold csl_context; cbn.
      rewrite (proj1 (proj2 HR)); apply frame_rel_aux, HR.
  - cbn; apply CsBrF; intro y;
      change (subst ?g (subst ?f (Ret y))) with (CTree.bind (CTree.bind (Ret y) f) g);
      rewrite !bind_ret_l.
    + apply guards_to_step_can_trans, guards_to_step_guard,
        guards_to_step_interp_state, H.
    + apply frame_tree_guard; auto.
Qed.

(** Interpreting a framable source in related states gives a conditional simulation. *)
Theorem csim_interp_sh_frame {X} (fr: ManagedHeap) :
  forall (u: ctree sE Bn X) (s s': SSig), Framable no_alloc_sE u -> frame_rel fr s s' ->
  csim (frameRV fr) (interp_state sh u s) (interp_state sh u s').
Proof.
  intros u s s' HF HR; eapply (csim_structural (frameRV fr) (frame_tree fr)).
  - intros t t' (v & σ & σ' & HV & Hσ & HE & HE').
    rewrite HE, HE'; now apply frame_shape.
  - now apply frame_tree_intro.
Qed.


(** Client API: prefixes transport unchanged; suffixes use [framer] and [done] uses [frame_post]. *)
Section FrameLogic.
  Context {X: Type} (fr: ManagedHeap) (u: ctree sE Bn X) (s s': SSig).
  Hypothesis HF: Framable no_alloc_sE u.
  Hypothesis HR: frame_rel fr s s'.

  (** Transport a prefix formula unchanged through heap framing. *)
  Theorem ticll_csl_frame (φ: ticll (writerE (CSLObs (nat * nat)))) w :
    <( {interp_state sh u s}, w |= φ )> -> <( {interp_state sh u s'}, w |= φ )>.
  Proof. apply (ticll_csim (frameRV fr)); now apply csim_interp_sh_frame. Qed.

  (** Transport an implication-free suffix formula through heap framing. *)
  Theorem ticlr_csl_frame (ψ: ticlr (writerE (CSLObs (nat * nat))) (SSig * X)) w :
    implr_free ψ -> not_done w ->
    <[ {interp_state sh u s}, w |= ψ ]> ->
    <[ {interp_state sh u s'}, w |= {framer (frameRV fr) ψ} ]>.
  Proof.
    intros Hfree Hnd; eapply ticlr_csim; [exact Hfree| |now apply simW_refl].
    now apply csim_interp_sh_frame.
  Qed.

  (** Frame the terminal postcondition under universal next. *)
  Corollary anr_csl_frame_done φ P w : not_done w ->
    <[ {interp_state sh u s}, w |= φ AN done P ]> ->
    <[ {interp_state sh u s'}, w |= φ AN done {frame_post fr P} ]>.
  Proof. intros Hnd; apply (ticlr_csl_frame (CxR Q_A φ (CDone P))); exact I || exact Hnd. Qed.


  (** Frame the terminal postcondition under universal until. *)
  Corollary aur_csl_frame_done φ P w : not_done w ->
    <[ {interp_state sh u s}, w |= φ AU done P ]> ->
    <[ {interp_state sh u s'}, w |= φ AU done {frame_post fr P} ]>.
  Proof. intros Hnd; apply (ticlr_csl_frame (CuR Q_A φ (CDone P))); exact I || exact Hnd. Qed.

End FrameLogic.
