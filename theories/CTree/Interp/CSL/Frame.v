From Stdlib Require Import FunctionalExtensionality Arith.PeanoNat.
From TICL Require Export CTree.Interp.CSL.Mod CTree.Logic.Sim Logic.Simulation.
From TICL Require Import CTree.Core Events.YieldE Logic.Kripke Logic.Semantics
  CTree.Logic.Trans CTree.Interp.State.Mod CTree.Interp.Yield.Mod
  CTree.Interp.Yield.Policy CTree.Interp.Yield.Frame Utils.Pcm.

Import CTree CTreeNotations TiclNotations CoindNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope pcm_scope.

(* All atoms are transported through framer; literal prefix preservation needs
   prefix_stable. Unconditional framing excludes allocation because absolute
   first fit may change. Conditional allocation also preserves live extents. *)
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

(** Observation transport adds the passive frame only to heap snapshots. *)
Definition frameER {A} (fr : ManagedHeap) : event_rel (writerE (CSLObs A)) :=
  fun Y e e' =>
    match e, e' with
    | Log o, Log o' =>
        match o, o' with
        | CSLHeap m, CSLHeap m' => m # fr /\ managed_wf m /\ m' ≈ m ⊎ fr
        | CSLCtx ctx, CSLCtx ctx' => ctx = ctx'
        | CSLEmit emission, CSLEmit emission' => emission = emission'
        | _, _ => False
        end
    end.

Lemma frameER_context {A} fr ctx :
  frameER (A:=A) fr unit (Log (CSLCtx ctx)) (Log (CSLCtx ctx)).
Proof. reflexivity. Qed.
Lemma frameER_emit {A} fr (emission : indexed A) :
  frameER fr unit (Log (CSLEmit emission)) (Log (CSLEmit emission)).
Proof. reflexivity. Qed.

Lemma frameER_heap {A} fr s s' : frame_rel fr s s' ->
  frameER (A:=A) fr unit (Log (CSLHeap (csl_memory s))) (Log (CSLHeap (csl_memory s'))).
Proof. intros [[HD HW] [_ HE]]; exact (conj HD (conj HW HE)). Qed.

Lemma frameER_right_unique {A} fr : event_right_unique (@frameER A fr).
Proof.
  intros Y e e1 e2 H1 H2; destruct e as [o]; dependent destruction e1; dependent destruction e2.
  repeat match goal with o : CSLObs _ |- _ => destruct o end;
    cbn [frameER] in *; try contradiction; try congruence.
  destruct H1 as [_ [_ HE1]], H2 as [_ [_ HE2]].
  f_equal; f_equal; apply managed_heap_ext.
  eapply peq_trans; [exact HE1|apply peq_sym; exact HE2].
Qed.

(** Preserve scheduling picks while transporting program observations. *)
Definition policyER {W} (ER : event_rel (writerE W))
  : event_rel (writerE (W + nat)) :=
  fun Y e e' =>
    match e, e' with
    | Log o, Log o' =>
        match o, o' with
        | inl p, inl p' => ER unit (Log p) (Log p')
        | inr i, inr i' => i = i'
        | _, _ => False
        end
    end.

Lemma policyER_right_unique {W} (ER : event_rel (writerE W)) :
  event_right_unique ER -> event_right_unique (policyER ER).
Proof.
  intros HU Y e e1 e2 H1 H2.
  destruct e as [o]; dependent destruction e1; dependent destruction e2;
    repeat match goal with o : (_ + _)%type |- _ => destruct o end;
    cbn [policyER] in *; try contradiction; try congruence.
  match goal with
  | H1 : ER unit (Log ?o) (Log ?o1), H2 : ER unit (Log ?o) (Log ?o2) |- _ =>
      pose proof (HU unit (Log o) (Log o1) (Log o2) H1 H2)
  end; congruence.
Qed.

Definition frameERW {A} (fr : ManagedHeap)
  : event_rel (writerE (CSLObs A + nat)) := policyER (frameER fr).

Lemma frameERW_context {A} fr ctx :
  frameERW (A:=A) fr unit (Log (inl (CSLCtx ctx))) (Log (inl (CSLCtx ctx))).
Proof. reflexivity. Qed.
Lemma frameERW_emit {A} fr (emission : indexed A) :
  frameERW fr unit (Log (inl (CSLEmit emission))) (Log (inl (CSLEmit emission))).
Proof. reflexivity. Qed.
Lemma frameERW_heap {A} fr s s' : frame_rel fr s s' ->
  frameERW (A:=A) fr unit
    (Log (inl (CSLHeap (csl_memory s)))) (Log (inl (CSLHeap (csl_memory s')))).
Proof. apply (frameER_heap (A:=A)). Qed.
Lemma frameERW_pick {A} fr i :
  frameERW (A:=A) fr unit (Log (inr i)) (Log (inr i)).
Proof. reflexivity. Qed.
Lemma frameERW_right_unique {A} fr : event_right_unique (@frameERW A fr).
Proof. apply policyER_right_unique, frameER_right_unique. Qed.

(** Framing determines a unique target result, including both heap functions. *)
Lemma frameRV_right_unique {X} fr : forall (r r1 r2 : SSig * X),
  frameRV fr r r1 -> frameRV fr r r2 -> r1 = r2.
Proof.
  intros [[m aux] x] [[m1 aux1] x1] [[m2 aux2] x2].
  intros [Hx1 [_ [Ha1 Hm1]]] [Hx2 [_ [Ha2 Hm2]]]; cbn in Hx1, Ha1, Hx2, Ha2.
  assert (Hm : m1 = m2).
  { apply managed_heap_ext; eapply peq_trans with (b := m ⊎ fr);
      [exact Hm1|apply peq_sym; exact Hm2]. }
  now subst m2 aux1 aux2 x1 x2.
Qed.

(** Frame both the returned state/value and the preceding observation. *)
Definition frame_post {A X} (fr : ManagedHeap)
  (P : SSig * X -> World (writerE (CSLObs A)) -> Prop) :=
  fun x' w' => exists x w, frameRV fr x x' /\
    simW (frameER fr) (frameRV (X:=X) fr) w w' /\ P x w.

(** Logged runners retain transport of the preceding world, including picks. *)
Definition frame_postW {A X} (fr : ManagedHeap)
  (P : SSig * X -> World (writerE (CSLObs A + nat)) -> Prop) :=
  fun x' w' => exists x w, frameRV fr x x' /\
    simW (frameERW fr) (frameRV (X:=X) fr) w w' /\ P x w.

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

(** Auxiliary-state updates preserve the frame relation. *)
Lemma frame_rel_aux fr s s' a : frame_rel fr s s' ->
  frame_rel fr (csl_memory s, a) (csl_memory s', a).
Proof. intros [HI [HA HE]]; split; [exact HI|split; [reflexivity|exact HE]]. Qed.

(** ** Framing is a property of the handler.

    A response is stuck, a related return, or related observations followed
    by related returns. Mutation snapshots change when a frame is added;
    contexts, indexed emissions and scheduling picks retain their payload. *)
Variant frame_resp {Wo Y} (ER : event_rel (writerE Wo)) (fr : ManagedHeap)
  : ctreeW Wo Bn (SSig * Y) -> ctreeW Wo Bn (SSig * Y) -> Prop :=
| frame_resp_stuck t t' : t ≅ Stuck -> frame_resp ER fr t t'
| frame_resp_ret t t' s x s' : frame_rel fr s s' ->
    t ≅ Ret (s,x) -> t' ≅ Ret (s',x) -> frame_resp ER fr t t'
| frame_resp_log t t' o o' s x s' : ER unit (Log o) (Log o') ->
    frame_rel fr s s' ->
    t ≅ Vis (Log o) (fun _ => Ret (s,x)) ->
    t' ≅ Vis (Log o') (fun _ => Ret (s',x)) -> frame_resp ER fr t t'.

#[global] Instance frame_resp_equ {Wo Y} (ER : event_rel (writerE Wo)) fr :
  Proper (equ eq ==> equ eq ==> iff) (@frame_resp Wo Y ER fr).
Proof.
  intros t u Et t' u' Et'; split; intro HF;
    inversion HF as [a a' Ea|a a' s x s' HR Ea Ea'|a a' o o' s x s' HE HR Ea Ea']; subst.
  - apply frame_resp_stuck; rewrite <- Et; exact Ea.
  - eapply frame_resp_ret; [exact HR| |].
    + rewrite <- Et; exact Ea.
    + rewrite <- Et'; exact Ea'.
  - eapply frame_resp_log; [exact HE|exact HR| |].
    + rewrite <- Et; exact Ea.
    + rewrite <- Et'; exact Ea'.
  - apply frame_resp_stuck; rewrite Et; exact Ea.
  - eapply frame_resp_ret; [exact HR| |].
    + rewrite Et; exact Ea.
    + rewrite Et'; exact Ea'.
  - eapply frame_resp_log; [exact HE|exact HR| |].
    + rewrite Et; exact Ea.
    + rewrite Et'; exact Ea'.
Qed.

Definition FrameHandler {Es Wo} (h : Es ~> stateT SSig (ctreeW Wo Bn))
  (okE : forall Y, Es Y -> Prop)
  (ER : ManagedHeap -> event_rel (writerE Wo)) : Prop :=
  forall fr Y (e : Es Y) s s', okE Y e -> frame_rel fr s s' ->
    frame_resp (ER fr) fr (h Y e s) (h Y e s').


(** Relabelling preserves response shape and lifts its observation relation. *)
Lemma frame_resp_translate {W Y} (ER : event_rel (writerE W)) fr
  (t t' : ctreeW W Bn (SSig * Y)) :
  frame_resp ER fr t t' ->
  frame_resp (policyER ER) fr (translate relabel_log t) (translate relabel_log t').
Proof.
  intro HF; inversion HF as
    [u u' Eu|u u' s x s' HR Eu Eu'|u u' o o' s x s' HE HR Eu Eu']; subst.
  - apply frame_resp_stuck; rewrite Eu; apply translate_stuck_node.
  - eapply frame_resp_ret; [exact HR|rewrite Eu|rewrite Eu']; apply translate_ret.
  - eapply frame_resp_log with (o := inl o) (o' := inl o').
    + exact HE.
    + exact HR.
    + rewrite Eu, translate_vis; cbn [relabel_log].
      apply vis_equ_node; intros []; apply translate_ret.
    + rewrite Eu', translate_vis; cbn [relabel_log].
      apply vis_equ_node; intros []; apply translate_ret.
Qed.

(** A policy adds only equal scheduling observations and preserves state. *)
Lemma policy_handler_frame {E W} (h : E ~> stateT SSig (ctreeW W Bn)) okE ER :
  FrameHandler h okE ER ->
  FrameHandler (policy_handler h) (okE_policy okE) (fun fr => policyER (ER fr)).
Proof.
  intros HH fr Y e s s' Hok HR; destruct e as [e|e].
  - cbn [policy_handler h_sum]; apply frame_resp_translate, HH; assumption.
  - destruct e as [i]; cbn [policy_handler h_sum sched_handler].
    eapply frame_resp_log with (o := inr i) (o' := inr i);
      [reflexivity|exact HR|reflexivity|reflexivity].
Qed.

Section FrameCore.
  Context {Es : Type -> Type} {Wo : Type}
    (h: Es ~> stateT SSig (ctreeW Wo Bn)) (okE: forall Y, Es Y -> Prop)
    (ER : ManagedHeap -> event_rel (writerE Wo)) (HH : FrameHandler h okE ER).

  (** Structural invariant: both trees interpret the same source under frame-related states. *)
  Definition frame_tree {X} (fr: ManagedHeap)
    (t t': ctreeW Wo Bn (SSig * X)) : Prop :=
    exists (u: ctree Es Bn X) s s', Framable okE u /\ frame_rel fr s s' /\
      t ≅ interp_state h u s /\ t' ≅ interp_state h u s'.

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
  Lemma frame_tree_intro {X} fr (u: ctree Es Bn X) s s' :
    Framable okE u -> frame_rel fr s s' ->
    frame_tree fr (interp_state h u s) (interp_state h u s').
  Proof.
    intros HF HR; exists u, s, s'; split; [exact HF|split; [exact HR|split; reflexivity]].
  Qed.

  (** Leading guards preserve the interpreter invariant. *)
  Lemma frame_tree_guard {X} fr (u: ctree Es Bn X) s s' :
    Framable okE u -> frame_rel fr s s' ->
    frame_tree fr (Guard (interp_state h u s)) (Guard (interp_state h u s')).
  Proof.
    intros; rewrite <- !interp_state_guard; apply frame_tree_intro; auto using fr_guard.
  Qed.

  (** One interpreter step preserves [frame_tree], by cases on the framable source node. *)
  Lemma frame_shape {X} (fr: ManagedHeap) (u: ctree Es Bn X) s s' :
    Framable okE u -> frame_rel fr s s' ->
    csim_shape (ER fr) (frameRV fr) (frame_tree fr)
      (observe (interp_state h u s)) (observe (interp_state h u s')).
  Proof.
    intros HF HR;
    apply framable_unfold in HF.
    rewrite !unfold_interp_state; cbn.
    destruct HF; cbn.
    - apply CsRetF; split; auto.
    - apply CsStuckF.
    - apply CsStepF, frame_tree_guard; auto.
    - apply CsGuardF, frame_tree_intro; auto.
    - pose proof (HH fr _ e s s' H HR) as Hresp.
      inversion Hresp as
        [r r' Er|r r' s0 x s0' HR0 Er Er'|r r' o o' s0 x s0' HE HR0 Er Er']; subst.
      + rewrite Er, bind_stuck; apply CsStuckF.
      + rewrite Er, Er', !bind_ret_l; apply CsGuardF, frame_tree_intro; auto.
      + rewrite Er, Er', !bind_vis; apply CsVisF; [exact HE|].
        intros []; rewrite !bind_ret_l; apply frame_tree_guard; auto.
    - cbn; apply CsBrF; intro y;
        change (subst ?g (subst ?f (Ret y))) with (CTree.bind (CTree.bind (Ret y) f) g);
        rewrite !bind_ret_l.
      + apply guards_to_step_can_trans, guards_to_step_guard,
          guards_to_step_interp_state, H.
      + apply frame_tree_guard; auto.
  Qed.

  (** Interpreting a framable source in related states gives a conditional simulation. *)
  Theorem csim_interp_frame {X} (fr: ManagedHeap) :
    forall (u: ctree Es Bn X) (s s': SSig), Framable okE u -> frame_rel fr s s' ->
    csim (ER fr) (frameRV fr) (interp_state h u s) (interp_state h u s').
  Proof.
    intros u s s' HF HR; eapply (csim_structural (ER fr) (frameRV fr) (frame_tree fr)).
    - intros t t' (v & σ & σ' & HV & Hσ & HE & HE').
      rewrite HE, HE'; now apply frame_shape.
    - now apply frame_tree_intro.
  Qed.
  Theorem ticl_interp_frame {X b} (fr : ManagedHeap)
    (u : ctree Es Bn X) (s s' : SSig)
    (p : ticl_at (writerE Wo) (SSig * X) b) w w' :
    event_right_unique (ER fr) -> Framable okE u -> frame_rel fr s s' ->
    simW (ER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) b p (interp_state h u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (ER fr) (frameRV fr) p)
      (interp_state h u s') w'.
  Proof.
    intros HU HF HR HW HP; eapply (ticl_csim b (ER fr) (frameRV fr) p).
    - destruct b; [split; [exact HU|apply frameRV_right_unique]|exact I].
    - exact (csim_interp_frame fr u s s' HF HR).
    - exact HW.
    - exact HP.
  Qed.

  (** Related leading logs retain every atom, including nested formulas. *)
  Theorem ticl_interp_frame_log {X b} (fr : ManagedHeap)
    (u : ctree Es Bn X) (s s' : SSig) (o o' : Wo)
    (p : ticl_at (writerE Wo) (SSig * X) b) w w' :
    event_right_unique (ER fr) -> Framable okE u -> frame_rel fr s s' ->
    ER fr unit (Log o) (Log o') -> simW (ER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) b p (log o ;; interp_state h u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (ER fr) (frameRV fr) p)
      (log o' ;; interp_state h u s') w'.
  Proof.
    intros HU HF HR HE HW HP; eapply (ticl_csim b (ER fr) (frameRV fr) p).
    - destruct b; [split; [exact HU|apply frameRV_right_unique]|exact I].
    - pose proof (csim_interp_frame fr u s s' HF HR) as HCsim.
      unfold log; rewrite !bind_vis; setoid_rewrite bind_ret_l.
      step; split.
      + intros l v HT.
        apply trans_vis_inv with (e := Log o)
          (k := fun _ : unit => interp_state h u s) in HT as ([] & Ev & El); subst l.
        exists (obs (Log o') tt), (interp_state h u s').
        split; [exact (trans_vis (Log o') tt (fun _ => interp_state h u s'))|split; [now apply SimLObs|]].
        now rewrite Ev.
      + intros HC l' v' HT'.
        apply trans_vis_inv with (e := Log o')
          (k := fun _ : unit => interp_state h u s') in HT' as ([] & Ev' & El'); subst l'.
        exists (obs (Log o) tt), (interp_state h u s).
        split; [exact (trans_vis (Log o) tt (fun _ => interp_state h u s))|split; [now apply SimLObs|]].
        now rewrite Ev'.
    - exact HW.
    - unfold log in HP; rewrite bind_vis in HP; setoid_rewrite bind_ret_l in HP; exact HP.
  Qed.
End FrameCore.

Local Ltac response_log HE HR :=
  eapply frame_resp_log; [exact HE|exact HR| | ];
    unfold log, CTree.trigger; rewrite bind_vis;
    apply vis_equ_node; intros []; rewrite bind_ret_l; reflexivity.

(** Checked heap responses frame, including whole-block free and snapshots. *)
Lemma sh_frame_handler : FrameHandler (@sh (nat * nat)) no_alloc_sE frameER.
Proof.
  intros fr Y e s s' Hok HR.
  destruct s as [[h al] aux], s' as [[h' al'] aux'].
  pose proof (proj1 (proj2 HR)) as HA; cbn in HA; subst aux'.
  destruct e as [e|[e|e]].
  - destruct e; cbn [no_alloc_sE] in Hok; try contradiction; cbn [sh h_sum].
    + destruct (h a) as [current|] eqn:HV.
      * pose proof (frame_rel_read fr ((h,al),aux) ((h',al'),aux) a current HR HV) as HV'.
        rewrite (heap_handlerW_rd_some CSLHeap a h al aux current HV),
          (heap_handlerW_rd_some CSLHeap a h' al' aux current HV').
        eapply frame_resp_ret; [exact HR|reflexivity|reflexivity].
      * apply frame_resp_stuck; now apply heap_handlerW_rd_none.
    + destruct (h a) as [current|] eqn:HV.
      * pose proof (frame_rel_read fr ((h,al),aux) ((h',al'),aux) a current HR HV) as HV'.
        pose proof (frame_rel_write fr ((h,al),aux) ((h',al'),aux) a v HR
          ltac:(change (h a <> None); congruence)) as HRw.
        rewrite (heap_handlerW_wr_some CSLHeap a h al aux v current HV),
          (heap_handlerW_wr_some CSLHeap a h' al' aux v current HV').
        pose proof (frameER_heap (A:=nat * nat) fr _ _ HRw) as HE; response_log HE HRw.
      * apply frame_resp_stuck; now apply heap_handlerW_wr_none.
    + destruct (managed_free (h,al) a) as [memory|] eqn:HM.
      * destruct HR as [[HD HW] [_ HE]].
        destruct (managed_free_pop _ _ _ _ HD HW HM) as [[mf [HF HEf]] HDf].
        destruct (managed_free_peq _ _ _ _ (peq_sym _ _ HE) HF) as [mb [HB HEb]].
        assert (HRf : frame_rel fr (memory,aux) (mb,aux)).
        { split; [split; [exact HDf|eapply managed_free_preserves_wf; eauto]|].
          split; [reflexivity|eapply peq_trans; [apply peq_sym; exact HEb|exact HEf]]. }
        rewrite (heap_handlerW_free CSLHeap a (h,al) memory aux HM),
          (heap_handlerW_free CSLHeap a (h',al') mb aux HB).
        destruct a.
        -- eapply frame_resp_ret; [exact HRf|reflexivity|reflexivity].
        -- pose proof (frameER_heap (A:=nat * nat) fr _ _ HRf) as Hlog; response_log Hlog HRf.
      * apply frame_resp_stuck; now apply heap_handlerW_free_invalid.
    + destruct (h a) as [current|] eqn:HV.
      * pose proof (frame_rel_read fr ((h,al),aux) ((h',al'),aux) a current HR HV) as HV'.
        destruct (Nat.eqb current expected) eqn:HC.
        -- apply Nat.eqb_eq in HC; subst current.
           pose proof (frame_rel_write fr ((h,al),aux) ((h',al'),aux) a desired HR
             ltac:(change (h a <> None); congruence)) as HRw.
           rewrite (heap_handlerW_cas_success CSLHeap a expected desired h al aux HV),
             (heap_handlerW_cas_success CSLHeap a expected desired h' al' aux HV').
           pose proof (frameER_heap (A:=nat * nat) fr _ _ HRw) as HE; response_log HE HRw.
        -- apply Nat.eqb_neq in HC.
           rewrite (heap_handlerW_cas_failure CSLHeap a expected desired current h al aux HV HC),
             (heap_handlerW_cas_failure CSLHeap a expected desired current h' al' aux HV' HC).
           eapply frame_resp_ret; [exact HR|reflexivity|reflexivity].
      * apply frame_resp_stuck; now apply heap_handlerW_cas_missing.
  - destruct e as [|ctx]; cbn [sh h_sum csl_context_handler].
    + eapply frame_resp_ret; [exact HR|reflexivity|reflexivity].
    + pose proof (frame_rel_aux fr ((h,al),aux) ((h',al'),aux) (ctx, snd aux) HR) as HRctx.
      pose proof (frameER_context (A:=nat * nat) fr ctx) as HE; response_log HE HRctx.
  - destruct e as [a]; cbn [sh h_sum csl_emit_handler].
    pose proof (frame_rel_aux fr ((h,al),aux) ((h',al'),aux) (fst aux, S (snd aux)) HR) as HRemit.
    pose proof (frameER_emit fr (stamp a (snd aux))) as HE; response_log HE HRemit.
Qed.

Theorem csim_interp_sh_frame {X} (fr : ManagedHeap) :
  forall (u : ctree sE Bn X) (s s' : SSig), Framable no_alloc_sE u -> frame_rel fr s s' ->
    csim (frameER fr) (frameRV fr) (interp_state sh u s) (interp_state sh u s').
Proof. apply (csim_interp_frame sh no_alloc_sE frameER sh_frame_handler). Qed.

Theorem ticl_csl_frame_log {X b} (fr : ManagedHeap)
  (u : ctree sE Bn X) (s s' : SSig) (o o' : CSLObs (nat * nat))
  (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * X) b) w w' :
  Framable no_alloc_sE u -> frame_rel fr s s' ->
  frameER fr unit (Log o) (Log o') -> simW (frameER fr) (@frameRV X fr) w w' ->
  entails (SSig * X) b p (log o ;; interp_state sh u s) w ->
  entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) p)
    (log o' ;; interp_state sh u s') w'.
Proof.
  intros HF HR HE HW HP.
  exact (ticl_interp_frame_log sh no_alloc_sE frameER sh_frame_handler
    fr u s s' o o' p w w' (frameER_right_unique fr) HF HR HE HW HP).
Qed.

(** Any instrumented policy, including ordinary RR, shares this handler. *)
Theorem ticl_csl_frameW {X b} (fr : ManagedHeap)
  (u : ctree (sE +' schedE) Bn X) (s s' : SSig)
  (HF : Framable (okE_policy no_alloc_sE) u) (HR : frame_rel fr s s')
  (p : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * X) b) w w' :
  simW (frameERW fr) (@frameRV X fr) w w' ->
  entails (SSig * X) b p (interp_state (policy_handler sh) u s) w ->
  entails (SSig * X) b (framer (SSig * X) b (frameERW fr) (frameRV fr) p)
    (interp_state (policy_handler sh) u s') w'.
Proof.
  intros HW HP.
  exact (ticl_interp_frame (policy_handler sh) (okE_policy no_alloc_sE) frameERW
    (policy_handler_frame sh no_alloc_sE frameER sh_frame_handler)
    fr u s s' p w w' (frameERW_right_unique fr) HF HR HW HP).
Qed.

Theorem ticl_csl_frameW_log {X b} (fr : ManagedHeap)
  (u : ctree (sE +' schedE) Bn X) (s s' : SSig) (o o' : CSLObs (nat * nat) + nat)
  (p : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * X) b) w w' :
  Framable (okE_policy no_alloc_sE) u -> frame_rel fr s s' ->
  frameERW fr unit (Log o) (Log o') -> simW (frameERW fr) (@frameRV X fr) w w' ->
  entails (SSig * X) b p (log o ;; interp_state (policy_handler sh) u s) w ->
  entails (SSig * X) b (framer (SSig * X) b (frameERW fr) (frameRV fr) p)
    (log o' ;; interp_state (policy_handler sh) u s') w'.
Proof.
  intros HF HR HE HW HP.
  exact (ticl_interp_frame_log (policy_handler sh) (okE_policy no_alloc_sE) frameERW
    (policy_handler_frame sh no_alloc_sE frameER sh_frame_handler)
    fr u s s' o o' p w w' (frameERW_right_unique fr) HF HR HE HW HP).
Qed.

Theorem ticl_csl_frameW_stable {X} (fr : ManagedHeap)
  (u : ctree (sE +' schedE) Bn X) (s s' : SSig)
  (HF : Framable (okE_policy no_alloc_sE) u) (HR : frame_rel fr s s')
  (p : ticll (writerE (CSLObs (nat * nat) + nat))) w w' :
  prefix_stable (frameERW fr) (@frameRV X fr) p ->
  simW (frameERW fr) (@frameRV X fr) w w' ->
  entails (SSig * X) false p (interp_state (policy_handler sh) u s) w ->
  entails (SSig * X) false p (interp_state (policy_handler sh) u s') w'.
Proof.
  intros HS HW H; eapply prefix_stable_framer; [exact HS|].
  eapply ticl_csl_frameW; eauto.
Qed.


(** All-formula transport requires related histories; stable prefixes may
    retain their original syntax. *)
Section FrameLogic.
  Context {X : Type} (fr : ManagedHeap) (u : ctree sE Bn X) (s s' : SSig).
  Hypothesis HF : Framable no_alloc_sE u.
  Hypothesis HR : frame_rel fr s s'.

  Theorem ticl_csl_frame {b : bool}
    (p : ticl (writerE (CSLObs (nat * nat))) (if b then Some (SSig * X)%type else None)) w w' :
    simW (frameER fr) (frameRV (X:=X) fr) w w' ->
    entails (SSig * X) b p (interp_state sh u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) p)
      (interp_state sh u s') w'.
  Proof.
    intros HW H; eapply (ticl_csim b (frameER fr) (frameRV fr) p).
    - destruct b; [split; [apply frameER_right_unique|apply frameRV_right_unique]|exact I].
    - exact (csim_interp_sh_frame fr u s s' HF HR).
    - exact HW.
    - exact H.
  Qed.

  Corollary an_csl_frame {b : bool}
    (phi : ticll (writerE (CSLObs (nat * nat))))
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * X) b) w w' :
    simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) b (Cx Q_A phi psi) (interp_state sh u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) (Cx Q_A phi psi))
      (interp_state sh u s') w'.
  Proof. apply ticl_csl_frame. Qed.

  Corollary en_csl_frame {b : bool}
    (phi : ticll (writerE (CSLObs (nat * nat))))
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * X) b) w w' :
    simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) b (Cx Q_E phi psi) (interp_state sh u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) (Cx Q_E phi psi))
      (interp_state sh u s') w'.
  Proof. apply ticl_csl_frame. Qed.

  Corollary au_csl_frame {b : bool}
    (phi : ticll (writerE (CSLObs (nat * nat))))
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * X) b) w w' :
    simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) b (Cu Q_A phi psi) (interp_state sh u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) (Cu Q_A phi psi))
      (interp_state sh u s') w'.
  Proof. apply ticl_csl_frame. Qed.

  Corollary eu_csl_frame {b : bool}
    (phi : ticll (writerE (CSLObs (nat * nat))))
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * X) b) w w' :
    simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) b (Cu Q_E phi psi) (interp_state sh u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) (Cu Q_E phi psi))
      (interp_state sh u s') w'.
  Proof. apply ticl_csl_frame. Qed.

  Corollary ag_csl_frame (phi : ticll (writerE (CSLObs (nat * nat)))) w w' :
    simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) false (Cg Q_A phi) (interp_state sh u s) w ->
    entails (SSig * X) false
      (framer (SSig * X) false (frameER fr) (frameRV fr) (Cg Q_A phi))
      (interp_state sh u s') w'.
  Proof. apply ticl_csl_frame. Qed.

  Corollary eg_csl_frame (phi : ticll (writerE (CSLObs (nat * nat)))) w w' :
    simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) false (Cg Q_E phi) (interp_state sh u s) w ->
    entails (SSig * X) false
      (framer (SSig * X) false (frameER fr) (frameRV fr) (Cg Q_E phi))
      (interp_state sh u s') w'.
  Proof. apply ticl_csl_frame. Qed.

  Corollary ax_csl_frame {b : bool}
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * X) b) w w' :
    simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) b <( AX {psi} )> (interp_state sh u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) <( AX {psi} )>)
      (interp_state sh u s') w'.
  Proof. apply ticl_csl_frame. Qed.

  Corollary ex_csl_frame {b : bool}
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * X) b) w w' :
    simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) b <( EX {psi} )> (interp_state sh u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) <( EX {psi} )>)
      (interp_state sh u s') w'.
  Proof. apply ticl_csl_frame. Qed.

  Corollary af_csl_frame {b : bool}
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * X) b) w w' :
    simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) b <( AF {psi} )> (interp_state sh u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) <( AF {psi} )>)
      (interp_state sh u s') w'.
  Proof. apply ticl_csl_frame. Qed.

  Corollary ef_csl_frame {b : bool}
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * X) b) w w' :
    simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) b <( EF {psi} )> (interp_state sh u s) w ->
    entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) <( EF {psi} )>)
      (interp_state sh u s') w'.
  Proof. apply ticl_csl_frame. Qed.

  Theorem ticl_csl_frame_stable (p : ticl (writerE (CSLObs (nat * nat))) None) w w' :
    prefix_stable (frameER fr) (@frameRV X fr) p ->
    simW (frameER fr) (frameRV (X:=X) fr) w w' ->
    entails (SSig * X) false p (interp_state sh u s) w ->
    entails (SSig * X) false p (interp_state sh u s') w'.
  Proof.
    intros HS HW H; eapply prefix_stable_framer; [exact HS|].
    eapply ticl_csl_frame; eauto.
  Qed.

  Corollary anr_csl_frame_ret (phi : ticl (writerE (CSLObs (nat * nat))) None) P w w' :
    not_done w -> simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) true (Cx Q_A phi (CRet P)) (interp_state sh u s) w ->
    entails (SSig * X) true
      (Cx Q_A (framer (SSig * X) false (frameER fr) (frameRV fr) phi) (CRet (frame_post fr P)))
      (interp_state sh u s') w'.
  Proof. intros _ HW H; exact (ticl_csl_frame (b:=true) (Cx Q_A phi (CRet P)) w w' HW H). Qed.

  Corollary aur_csl_frame_ret (phi : ticl (writerE (CSLObs (nat * nat))) None) P w w' :
    not_done w -> simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) true (Cu Q_A phi (CRet P)) (interp_state sh u s) w ->
    entails (SSig * X) true
      (Cu Q_A (framer (SSig * X) false (frameER fr) (frameRV fr) phi) (CRet (frame_post fr P)))
      (interp_state sh u s') w'.
  Proof. intros _ HW H; exact (ticl_csl_frame (b:=true) (Cu Q_A phi (CRet P)) w w' HW H). Qed.

  Corollary enr_csl_frame_ret (phi : ticll (writerE (CSLObs (nat * nat)))) P w w' :
    not_done w -> simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) true (Cx Q_E phi (CRet P)) (interp_state sh u s) w ->
    entails (SSig * X) true
      (Cx Q_E (framer (SSig * X) false (frameER fr) (frameRV fr) phi) (CRet (frame_post fr P)))
      (interp_state sh u s') w'.
  Proof. intros _ HW H; exact (ticl_csl_frame (b:=true) (Cx Q_E phi (CRet P)) w w' HW H). Qed.

  Corollary eur_csl_frame_ret (phi : ticll (writerE (CSLObs (nat * nat)))) P w w' :
    not_done w -> simW (frameER fr) (@frameRV X fr) w w' ->
    entails (SSig * X) true (Cu Q_E phi (CRet P)) (interp_state sh u s) w ->
    entails (SSig * X) true
      (Cu Q_E (framer (SSig * X) false (frameER fr) (frameRV fr) phi) (CRet (frame_post fr P)))
      (interp_state sh u s') w'.
  Proof. intros _ HW H; exact (ticl_csl_frame (b:=true) (Cu Q_E phi (CRet P)) w w' HW H). Qed.

  Corollary anr_csl_frame_done phi
    (P : SSig * X -> World (writerE (CSLObs (nat * nat))) -> Prop) w w' :
    not_done w -> simW (frameER fr) (@frameRV X fr) w w' ->
    anc (entails (SSig * X) false phi) (fun _ wd => done_with P wd)
      (interp_state sh u s) w ->
    anc (entails (SSig * X) false (framer (SSig * X) false (frameER fr) (frameRV fr) phi))
      (fun _ wd => done_with (frame_post fr P) wd) (interp_state sh u s') w'.
  Proof.
    intros _ HW H.
    eapply sim_anc with (ER := frameER fr) (RV := frameRV fr)
      (Fr := csim (frameER fr) (frameRV fr)).
    - apply csim_ktrans_l.
    - apply csim_ktrans_r.
    - intros t t' z z' HS HZ HP; eapply (ticl_csim false (frameER fr) (frameRV fr) phi); eauto.
    - intros t t' z z' HS HZ HP; exact (sim_done_with (frameER fr) (frameRV fr) P z z' HZ HP).
    - exact (csim_interp_sh_frame fr u s s' HF HR).
    - exact HW.
    - exact H.
  Qed.

  Corollary aur_csl_frame_done phi
    (P : SSig * X -> World (writerE (CSLObs (nat * nat))) -> Prop) w w' :
    not_done w -> simW (frameER fr) (@frameRV X fr) w w' ->
    auc (entails (SSig * X) false phi) (fun _ wd => done_with P wd)
      (interp_state sh u s) w ->
    auc (entails (SSig * X) false (framer (SSig * X) false (frameER fr) (frameRV fr) phi))
      (fun _ wd => done_with (frame_post fr P) wd) (interp_state sh u s') w'.
  Proof.
    intros _ HW H.
    eapply sim_auc with (ER := frameER fr) (RV := frameRV fr)
      (Fr := csim (frameER fr) (frameRV fr)).
    - apply csim_ktrans_l.
    - apply csim_ktrans_r.
    - intros t t' z z' HS HZ HP; eapply (ticl_csim false (frameER fr) (frameRV fr) phi); eauto.
    - intros t t' z z' HS HZ HP; exact (sim_done_with (frameER fr) (frameRV fr) P z z' HZ HP).
    - exact (csim_interp_sh_frame fr u s s' HF HR).
    - exact HW.
    - exact H.
  Qed.

  Corollary enr_csl_frame_done phi
    (P : SSig * X -> World (writerE (CSLObs (nat * nat))) -> Prop) w w' :
    not_done w -> simW (frameER fr) (@frameRV X fr) w w' ->
    enc (entails (SSig * X) false phi) (fun _ wd => done_with P wd)
      (interp_state sh u s) w ->
    enc (entails (SSig * X) false (framer (SSig * X) false (frameER fr) (frameRV fr) phi))
      (fun _ wd => done_with (frame_post fr P) wd) (interp_state sh u s') w'.
  Proof.
    intros _ HW H.
    eapply sim_enc with (ER := frameER fr) (RV := frameRV fr)
      (Fr := csim (frameER fr) (frameRV fr)).
    - apply csim_ktrans_l.
    - intros t t' z z' HS HZ HP; eapply (ticl_csim false (frameER fr) (frameRV fr) phi); eauto.
    - intros t t' z z' HS HZ HP; exact (sim_done_with (frameER fr) (frameRV fr) P z z' HZ HP).
    - exact (csim_interp_sh_frame fr u s s' HF HR).
    - exact HW.
    - exact H.
  Qed.

  Corollary eur_csl_frame_done phi
    (P : SSig * X -> World (writerE (CSLObs (nat * nat))) -> Prop) w w' :
    not_done w -> simW (frameER fr) (@frameRV X fr) w w' ->
    euc (entails (SSig * X) false phi) (fun _ wd => done_with P wd)
      (interp_state sh u s) w ->
    euc (entails (SSig * X) false (framer (SSig * X) false (frameER fr) (frameRV fr) phi))
      (fun _ wd => done_with (frame_post fr P) wd) (interp_state sh u s') w'.
  Proof.
    intros _ HW H.
    eapply sim_euc with (ER := frameER fr) (RV := frameRV fr)
      (Fr := csim (frameER fr) (frameRV fr)).
    - apply csim_ktrans_l.
    - intros t t' z z' HS HZ HP; eapply (ticl_csim false (frameER fr) (frameRV fr) phi); eauto.
    - intros t t' z z' HS HZ HP; exact (sim_done_with (frameER fr) (frameRV fr) P z z' HZ HP).
    - exact (csim_interp_sh_frame fr u s s' HF HR).
    - exact HW.
    - exact H.
  Qed.
End FrameLogic.

(** A single absolute allocation frames only when both heaps have the same
    first-fit witness and their complete managed post-states remain related. *)
Theorem ticl_csl_alloc_frame_at {X b} (fr : ManagedHeap) (size base : nat)
  (K : nat -> ctree sE Bn X) (s s' : SSig)
  (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * X) b) w w' :
  frame_rel fr s s' ->
  0 < size -> 0 < base ->
  block_free (fst (csl_memory s)) base size ->
  block_free (fst (csl_memory s')) base size ->
  (forall j, 0 < j -> j < base -> ~ block_free (fst (csl_memory s)) j size) ->
  (forall j, 0 < j -> j < base -> ~ block_free (fst (csl_memory s')) j size) ->
  frame_rel fr (managed_alloc (csl_memory s) base size, snd s)
    (managed_alloc (csl_memory s') base size, snd s') ->
  Framable no_alloc_sE (K base) ->
  simW (frameER fr) (@frameRV X fr) w w' ->
  entails (SSig * X) b p (interp_state sh (a <- heap_alloc size ;; K a) s) w ->
  entails (SSig * X) b (framer (SSig * X) b (frameER fr) (frameRV fr) p)
    (interp_state sh (a <- heap_alloc size ;; K a) s') w'.
Proof.
  destruct s as [[h allocs] aux], s' as [[h' allocs'] aux']; cbn [csl_memory].
  intros HR Pos Base Free Free' First First' HRpost HF HW H.
  pose proof (interp_heapW_alloc_first CSLHeap
    (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))
    h allocs size base aux K Pos Base Free First) as Ealloc.
  pose proof (interp_heapW_alloc_first CSLHeap
    (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))
    h' allocs' size base aux' K Pos Base Free' First') as Ealloc'.
  rewrite Ealloc in H; rewrite Ealloc'.
  eapply ticl_csl_frame_log; [exact HF|exact HRpost| |exact HW|exact H].
  exact (frameER_heap fr _ _ HRpost).
Qed.
