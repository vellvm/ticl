(** * First-yield thread segments, parameterized by handler and response relation.

    One finite derivation stops at the first source yield.  The handler premise
    of [segment_user] is the handler's ACTUAL effect semantics, related to a
    finite emission prefix by an arbitrary relation [R]; raw thread endpoints
    still use [equ eq].  Exactly two instances are used downstream:

      [fun X (t u : ictreeW W X) => t ~ u]   (bisimulation mode)
      [fun X (t u : ictreeW W X) => t ≅ u]   (exact mode)

    and [ThreadSegment_mono] transports between them.  There is no relation
    class or typeclass inference layer, and no second segment inductive. *)

From Stdlib Require Import List Arith.PeanoNat Fin Vector
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From ExtLib Require Import Data.Monads.StateMonad.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Trans ICTree.Trace
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Interp.State.Mod
  ICTree.Interp.Refine ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin ICTree.Interp.Yield.Nondeterministic
  Utils.Vectors.

Import ICtree ICTreeNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope list_scope.

Section ThreadSegments.
  Context {E W Sigma : Type} {HE : Encode E}
    (handler : E ~> stateT Sigma (ictreeW W))
    (R : forall X : Type, ictreeW W X -> ictreeW W X -> Prop).

  Inductive ThreadSegment :
    thread E -> Sigma -> list W -> thread E -> Sigma -> Prop :=
  | segment_yield (k : unit -> thread E) sigma :
      ThreadSegment (Vis (inl Yield) k) sigma [] (k tt) sigma
  | segment_guard t sigma logs t' sigma' :
      ThreadSegment t sigma logs t' sigma' ->
      ThreadSegment (Guard t) sigma logs t' sigma'
  | segment_user (e : E) (k : encode e -> thread E) sigma result sigma1
      before after t' sigma' :
      R _ (runStateT (handler e) sigma) (emit_list before (Ret (result,sigma1))) ->
      ThreadSegment (k result) sigma1 after t' sigma' ->
      ThreadSegment
        (@go (yieldE + (forkE + E)) _ unit (VisF (inr (inr e) : yieldE + (forkE + E)) k))
        sigma (before ++ after) t' sigma'
  | segment_equ t u sigma logs u' t' sigma' :
      t ≅ u -> ThreadSegment u sigma logs u' sigma' -> u' ≅ t' ->
      ThreadSegment t sigma logs t' sigma'.

  (** Raw congruence is allowed on both ends, but no source-side [sbisim]
      congruence is used. *)
  Lemma ThreadSegment_equ_input t u sigma xs residual sigma' :
    t ≅ u -> ThreadSegment t sigma xs residual sigma' ->
    ThreadSegment u sigma xs residual sigma'.
  Proof.
    intros Eq H; eapply segment_equ; [symmetry; exact Eq|exact H|reflexivity].
  Qed.

  Lemma ThreadSegment_equ_output t sigma xs residual residual' sigma' :
    ThreadSegment t sigma xs residual sigma' -> residual ≅ residual' ->
    ThreadSegment t sigma xs residual' sigma'.
  Proof. intros H Eq; eapply segment_equ; [reflexivity|exact H|exact Eq]. Qed.

  Lemma ThreadSegment_yield_inv_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    forall k : unit -> thread E,
      t ≅ Vis (inl Yield) k ->
      xs = [] /\ sigma' = sigma /\ k tt ≅ residual.
  Proof.
    intro H; induction H as
      [k0 sigma
      |t sigma xs residual sigma' H IH
      |e k0 sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout].
    - intros k Eq; split; [reflexivity|]; split; [reflexivity|].
      symmetry; exact (equ_vis_invE Eq tt).
    - intros k Eq; step in Eq; cbn in Eq; inversion Eq.
    - intros k Eq; pose proof (equ_vis_invT Eq) as [_ Ebad]; discriminate.
    - intros k Eq.
      assert (Eu : u ≅ Vis (inl Yield) k).
      { transitivity t; [symmetry; exact Etu|exact Eq]. }
      destruct (IH k Eu) as [Ex [Es Ek]].
      split; [exact Ex|]; split; [exact Es|].
      transitivity u'; assumption.
  Qed.

  Lemma ThreadSegment_yield_inv k sigma xs residual sigma' :
    ThreadSegment (Vis (inl Yield) k) sigma xs residual sigma' ->
    xs = [] /\ sigma' = sigma /\ k tt ≅ residual.
  Proof. intro H; eapply ThreadSegment_yield_inv_equ; [exact H|reflexivity]. Qed.

  Lemma ThreadSegment_guard_inv_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    forall u, t ≅ Guard u -> ThreadSegment u sigma xs residual sigma'.
  Proof.
    intro H; induction H as
      [k sigma
      |t sigma xs residual sigma' H IH
      |e k sigma result sigma1 before after residual sigma' Eh H IH
      |t v sigma xs v' residual sigma' Etv H IH Eout].
    - intros u Eq; step in Eq; cbn in Eq; inversion Eq.
    - intros u Eq; apply equ_guard_invE in Eq.
      eapply ThreadSegment_equ_input; [exact Eq|exact H].
    - intros u Eq; step in Eq; cbn in Eq; inversion Eq.
    - intros u Eq.
      eapply ThreadSegment_equ_output; [|exact Eout].
      apply IH; transitivity t; [symmetry; exact Etv|exact Eq].
  Qed.

  Lemma ThreadSegment_guard_inv t sigma xs residual sigma' :
    ThreadSegment (Guard t) sigma xs residual sigma' ->
    ThreadSegment t sigma xs residual sigma'.
  Proof. intro H; eapply ThreadSegment_guard_inv_equ; [exact H|reflexivity]. Qed.

  Lemma ThreadSegment_guard_iff t sigma xs residual sigma' :
    ThreadSegment (Guard t) sigma xs residual sigma' <->
    ThreadSegment t sigma xs residual sigma'.
  Proof. split; [apply ThreadSegment_guard_inv|apply segment_guard]. Qed.

  Lemma ThreadSegment_user_inv_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    forall (e : E) (k : encode e -> thread E),
      t ≅ (@go (yieldE + (forkE + E)) _ unit
             (VisF (inr (inr e) : yieldE + (forkE + E)) k)) ->
      exists result sigma1 before after,
        xs = before ++ after /\
        R _ (runStateT (handler e) sigma) (emit_list before (Ret (result,sigma1))) /\
        ThreadSegment (k result) sigma1 after residual sigma'.
  Proof.
    intro H; induction H as
      [k0 sigma
      |t sigma xs residual sigma' H IH
      |e0 k0 sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout].
    - intros e k Eq; pose proof (equ_vis_invT Eq) as [_ Ebad]; discriminate.
    - intros e k Eq; step in Eq; cbn in Eq; inversion Eq.
    - intros e k Eq.
      pose proof (equ_vis_invT Eq) as [_ Ee].
      assert (Eevent : e0 = e) by congruence; subst e.
      exists result, sigma1, before, after.
      split; [reflexivity|]; split; [exact Eh|].
      eapply ThreadSegment_equ_input; [exact (equ_vis_invE Eq result)|exact H].
    - intros e k Eq.
      assert (Eu : u ≅ (@go (yieldE + (forkE + E)) _ unit
                          (VisF (inr (inr e) : yieldE + (forkE + E)) k))).
      { transitivity t; [symmetry; exact Etu|exact Eq]. }
      destruct (IH e k Eu) as [r [sigma1 [before [after [Ex [Eh Htail]]]]]].
      exists r, sigma1, before, after; split; [exact Ex|]; split; [exact Eh|].
      eapply ThreadSegment_equ_output; eassumption.
  Qed.

  Lemma ThreadSegment_user_inv (e : E) (k : encode e -> thread E)
    sigma xs residual sigma' :
    ThreadSegment (@go (yieldE + (forkE + E)) _ unit
                     (VisF (inr (inr e) : yieldE + (forkE + E)) k))
      sigma xs residual sigma' ->
    exists result sigma1 before after,
      xs = before ++ after /\
      R _ (runStateT (handler e) sigma) (emit_list before (Ret (result,sigma1))) /\
      ThreadSegment (k result) sigma1 after residual sigma'.
  Proof. intro H; eapply ThreadSegment_user_inv_equ; [exact H|reflexivity]. Qed.

  Lemma ThreadSegment_ret_absurd_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' -> ~ (t ≅ Ret tt).
  Proof.
    intro H; induction H as
      [k sigma
      |t sigma xs residual sigma' H IH
      |e k sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout]; intro Eq.
    - step in Eq; cbn in Eq; inversion Eq.
    - step in Eq; cbn in Eq; inversion Eq.
    - step in Eq; cbn in Eq; inversion Eq.
    - apply IH; transitivity t; [symmetry; exact Etu|exact Eq].
  Qed.

  Lemma ThreadSegment_ret_absurd sigma xs residual sigma' :
    ~ ThreadSegment (Ret tt) sigma xs residual sigma'.
  Proof. intro H; eapply ThreadSegment_ret_absurd_equ; [exact H|reflexivity]. Qed.

  Lemma ThreadSegment_fork_absurd_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    forall k : bool -> thread E, ~ (t ≅ Vis (inr (inl Fork)) k).
  Proof.
    intro H; induction H as
      [k0 sigma
      |t sigma xs residual sigma' H IH
      |e k0 sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout]; intros k Eq.
    - pose proof (equ_vis_invT Eq) as [_ Ebad]; discriminate.
    - step in Eq; cbn in Eq; inversion Eq.
    - pose proof (equ_vis_invT Eq) as [_ Ebad]; discriminate.
    - apply (IH k); transitivity t; [symmetry; exact Etu|exact Eq].
  Qed.

  Lemma ThreadSegment_fork_absurd k sigma xs residual sigma' :
    ~ ThreadSegment (Vis (inr (inl Fork)) k) sigma xs residual sigma'.
  Proof. intro H; eapply ThreadSegment_fork_absurd_equ; [exact H|reflexivity]. Qed.

  Lemma ThreadSegment_br_absurd_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    forall n (k : Fin.t (S n) -> thread E), ~ (t ≅ Br n k).
  Proof.
    intro H; induction H as
      [k0 sigma
      |t sigma xs residual sigma' H IH
      |e k0 sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout]; intros n k Eq.
    - step in Eq; cbn in Eq; inversion Eq.
    - step in Eq; cbn in Eq; inversion Eq.
    - step in Eq; cbn in Eq; inversion Eq.
    - apply (IH n k); transitivity t; [symmetry; exact Etu|exact Eq].
  Qed.

  Lemma ThreadSegment_br_absurd n k sigma xs residual sigma' :
    ~ ThreadSegment (Br n k) sigma xs residual sigma'.
  Proof. intro H; eapply ThreadSegment_br_absurd_equ; [exact H|reflexivity]. Qed.

  (** A finite first-yield derivation cannot be manufactured by repeatedly
      unfolding a divergent guard.  A user case provides its actual response as
      the witness needed for the first visible raw transition. *)
  Lemma ThreadSegment_can_step t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' -> exists l u, trans l t u.
  Proof.
    intro H; induction H as
      [k sigma
      |t sigma xs residual sigma' H IH
      |e k sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout].
    - exists (obs (inl Yield) tt), (k tt); apply trans_vis.
    - destruct IH as [l [u Hstep]]; exists l, u; now apply trans_guard.
    - exists (obs (inr (inr e) : yieldE + (forkE + E)) result), (k result);
        apply trans_vis.
    - destruct IH as [l [v Hstep]]; exists l, v; rewrite Etu; exact Hstep.
  Qed.

  Lemma ThreadSegment_divergent_absurd t sigma xs residual sigma' :
    is_stuck t -> ~ ThreadSegment t sigma xs residual sigma'.
  Proof. intros Hdiv Hseg; apply Hdiv; eapply ThreadSegment_can_step; exact Hseg. Qed.

  Lemma ThreadSegment_stuck_absurd sigma xs residual sigma' :
    ~ ThreadSegment (stuck : thread E) sigma xs residual sigma'.
  Proof. apply ThreadSegment_divergent_absurd, stuck_is_stuck. Qed.

  Lemma ThreadSegment_spin_absurd sigma xs residual sigma' :
    ~ ThreadSegment (spin : thread E) sigma xs residual sigma'.
  Proof.
    intro H; eapply ThreadSegment_br_absurd_equ; [exact H|].
    apply unfold_spin.
  Qed.

  Lemma ThreadSegment_branchfree t sigma logs residual sigma' :
    ThreadSegment t sigma logs residual sigma' ->
    BranchFree t -> BranchFree residual.
  Proof.
    intro H; induction H as
      [k sigma|t sigma logs residual sigma' H IH
      |e k sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma logs u' residual sigma' Etu H IH Eout]; intro Hbf.
    - apply branchfree_unfold in Hbf; cbn in Hbf.
      dependent destruction Hbf; auto.
    - apply IH; apply branchfree_unfold in Hbf; cbn in Hbf.
      dependent destruction Hbf; assumption.
    - apply IH; apply branchfree_unfold in Hbf; cbn in Hbf.
      dependent destruction Hbf; auto.
    - eapply branchfree_equ_impl; [exact Eout|].
      apply IH; eapply branchfree_equ_impl; eassumption.
  Qed.

  (** Guard transport: the closure that forgets finitely many leading guards
      preserves segments in both directions.  Symmetry is handled by proving
      both directions together, not by assuming a reverse simulation. *)
  Lemma guard_equ_segment_iff t u : guard_equ t u ->
    forall sigma xs residual sigma',
      ThreadSegment t sigma xs residual sigma' <->
      ThreadSegment u sigma xs residual sigma'.
  Proof.
    intro H; induction H as
      [t u [Eq|Eg]|t|t u H IH|t u v H1 IH1 H2 IH2];
      intros sigma xs residual sigma'.
    - split; intro Hseg.
      + eapply ThreadSegment_equ_input; [exact Eq|exact Hseg].
      + eapply ThreadSegment_equ_input; [symmetry; exact Eq|exact Hseg].
    - split; intro Hseg.
      + apply ThreadSegment_guard_inv.
        eapply ThreadSegment_equ_input; [exact Eg|exact Hseg].
      + eapply ThreadSegment_equ_input; [symmetry; exact Eg|].
        apply segment_guard; exact Hseg.
    - reflexivity.
    - symmetry; apply IH.
    - transitivity (ThreadSegment u sigma xs residual sigma'); [apply IH1|apply IH2].
  Qed.

  Lemma guard_equ_segment t u sigma xs t' sigma' :
    guard_equ t u -> ThreadSegment t sigma xs t' sigma' ->
    exists u', ThreadSegment u sigma xs u' sigma' /\ guard_equ t' u'.
  Proof.
    intros Eq Hseg; exists t'; split.
    - apply (proj1 (guard_equ_segment_iff t u Eq sigma xs t' sigma')); exact Hseg.
    - apply guard_equ_equ; reflexivity.
  Qed.

  (** An exact segment may end at a residual differing from its target only by
      finite leading guards and raw tree equivalence. *)
  Definition segment_to (t : thread E) (sigma : Sigma)
    (logs : list W) (target : thread E) (sigma' : Sigma) : Prop :=
    exists residual, ThreadSegment t sigma logs residual sigma' /\
      guard_equ residual target.

  Lemma segment_to_equ t u sigma logs target sigma' :
    t ≅ u -> segment_to u sigma logs target sigma' ->
    segment_to t sigma logs target sigma'.
  Proof.
    intros Htu (residual & Hseg & Htail); exists residual; split; [|exact Htail].
    eapply segment_equ; [exact Htu|exact Hseg|reflexivity].
  Qed.
End ThreadSegments.

Arguments ThreadSegment {E W Sigma HE} handler R.
Arguments segment_to {E W Sigma HE} handler R.

(** A branch node can never be a yield up to finite guard removal. *)
Lemma guard_equ_br_yield_absurd {E} {HE : Encode E} n
  (k : Fin.t (S n) -> thread E) (ky : unit -> thread E) :
  ~ guard_equ (Br n k) (Vis (inl Yield) ky).
Proof.
  intro Eq; apply guard_equ_sbisim in Eq.
  eapply (@sbisim_vis_br_inv (yieldE + (forkE + E)) _ unit n (inl Yield) ky k);
    symmetry; exact Eq.
Qed.

(** Weakening the response relation weakens the segment.  This is how an exact
    segment becomes a bisimulation-mode segment; [equ_sbisim] supplies the
    premise for the two instances actually used. *)
Lemma ThreadSegment_mono {E W Sigma} {HE : Encode E}
  (handler : E ~> stateT Sigma (ictreeW W))
  (R R' : forall X : Type, ictreeW W X -> ictreeW W X -> Prop)
  (Hmono : forall X t u, R X t u -> R' X t u) :
  forall t sigma logs residual sigma',
    ThreadSegment handler R t sigma logs residual sigma' ->
    ThreadSegment handler R' t sigma logs residual sigma'.
Proof.
  intros t sigma logs residual sigma' H; induction H as
    [k sigma
    |t sigma logs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma logs u' residual sigma' Etu H IH Eout].
  - apply segment_yield.
  - apply segment_guard; exact IH.
  - eapply segment_user; [apply Hmono; exact Eh|exact IH].
  - eapply segment_equ; eassumption.
Qed.

Lemma segment_to_mono {E W Sigma} {HE : Encode E}
  (handler : E ~> stateT Sigma (ictreeW W))
  (R R' : forall X : Type, ictreeW W X -> ictreeW W X -> Prop)
  (Hmono : forall X t u, R X t u -> R' X t u) :
  forall t sigma logs target sigma',
    segment_to handler R t sigma logs target sigma' ->
    segment_to handler R' t sigma logs target sigma'.
Proof.
  intros t sigma logs target sigma' (residual & Hseg & Htail).
  exists residual; split; [|exact Htail].
  eapply ThreadSegment_mono; eauto.
Qed.

(** ** Scheduling laws.

    Response uniqueness, determinism, handler-fault exclusion, and the
    bisimulation-based scheduling equations additionally need that the
    response relation implies strong bisimulation. *)
Section SegmentScheduling.
  Context {E W Sigma : Type} {HE : Encode E}
    (handler : E ~> stateT Sigma (ictreeW W))
    (R : forall X : Type, ictreeW W X -> ictreeW W X -> Prop)
    (HR : forall X (t u : ictreeW W X), R X t u -> t ~ u).

  Lemma handler_response_unique (e : E) (sigma : Sigma)
    (result : encode e) (sigma1 : Sigma) (before : list W)
    (result' : encode e) (sigma2 : Sigma) (before' : list W) :
    R _ (runStateT (handler e) sigma) (emit_list before (Ret (result,sigma1))) ->
    R _ (runStateT (handler e) sigma) (emit_list before' (Ret (result',sigma2))) ->
    before = before' /\ result = result' /\ sigma1 = sigma2.
  Proof.
    intros E1 E2; apply HR in E1; apply HR in E2.
    assert (Eq : emit_list before (Ret (result,sigma1)) ~
                 emit_list before' (Ret (result',sigma2))).
    { transitivity (runStateT (handler e) sigma); [symmetry; exact E1|exact E2]. }
    destruct (emit_list_ret_injective _ _ _ _ Eq) as [Ex Er].
    inversion Er; subst; auto.
  Qed.

  Lemma ThreadSegment_fault_absurd (e : E) (k : encode e -> thread E)
    sigma xs residual sigma' :
    runStateT (handler e) sigma ~ (stuck : ictreeW W (encode e * Sigma)) ->
    ~ ThreadSegment handler R
        (@go (yieldE + (forkE + E)) _ unit
           (VisF (inr (inr e) : yieldE + (forkE + E)) k))
        sigma xs residual sigma'.
  Proof.
    intros Ef Hseg.
    destruct (ThreadSegment_user_inv handler R e k sigma xs residual sigma' Hseg)
      as [result [sigma1 [before [after [_ [Eh _]]]]]].
    apply HR in Eh.
    apply (emit_list_ret_not_stuck before (result,sigma1)).
    transitivity (runStateT (handler e) sigma); [symmetry; exact Eh|exact Ef].
  Qed.

  Lemma ThreadSegment_deterministic t sigma xs u sigma1 ys v sigma2 :
    ThreadSegment handler R t sigma xs u sigma1 ->
    ThreadSegment handler R t sigma ys v sigma2 ->
    xs = ys /\ sigma1 = sigma2 /\ u ≅ v.
  Proof.
    intros H1; revert ys v sigma2.
    induction H1 as
      [k sigma
      |t sigma xs residual sigma' H IH
      |e k sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout]; intros ys v sigma2 H2.
    - destruct (ThreadSegment_yield_inv handler R k sigma ys v sigma2 H2)
        as [Ex [Es Ek]].
      split; [symmetry; exact Ex|]; split; [symmetry; exact Es|exact Ek].
    - apply IH; now apply ThreadSegment_guard_inv in H2.
    - destruct (ThreadSegment_user_inv handler R e k sigma ys v sigma2 H2)
        as [r [sigma0 [before0 [after0 [Ey [Eh0 Htail]]]]]].
      destruct (handler_response_unique e sigma result sigma1 before
        r sigma0 before0 Eh Eh0) as [Eb [Er Es]].
      subst before0; subst r; subst sigma0.
      destruct (IH after0 v sigma2 Htail) as [Ea [Es Er]].
      split; [subst ys; now rewrite Ea|]; split; assumption.
    - assert (H2u : ThreadSegment handler R u sigma ys v sigma2).
      { eapply ThreadSegment_equ_input; [exact Etu|exact H2]. }
      destruct (IH ys v sigma2 H2u) as [Ex [Es Er]].
      split; [exact Ex|]; split; [exact Es|].
      transitivity u'; [symmetry; exact Eout|exact Er].
  Qed.
End SegmentScheduling.

(** ** Pool congruence for the focused slot.

    Pool equivalence is used only for genuine raw [equ].  Guard removal below
    is deliberately restricted to the focused slot. *)
Section FocusedCongruence.
  Context {E W Sigma : Type} {HE : Encode E}
    (handler : E ~> stateT Sigma (ictreeW W)).

  Lemma segment_nd_replace_equ n (ts : pool E (S n)) (i : Fin.t (S n))
    t u focus sigma :
    t ≅ u ->
    interp_schedule_nd handler (S n) (ts @ i := t) focus sigma ~
    interp_schedule_nd handler (S n) (ts @ i := u) focus sigma.
  Proof.
    intro Eq.
    pose proof (interp_schedule_nd_equ handler (S n) (ts @ i := t) (ts @ i := u)
      focus sigma (replace_pool_equ ts ts i t u (pool_equ_refl ts) Eq)) as Ep.
    rewrite Ep; reflexivity.
  Qed.

  Lemma segment_rr_replace_equ n (ts : pool E (S n)) (i : Fin.t (S n))
    t u focus m sigma :
    t ≅ u ->
    interp_schedule_rr handler (S n) (ts @ i := t) focus m sigma ~
    interp_schedule_rr handler (S n) (ts @ i := u) focus m sigma.
  Proof.
    intro Eq.
    pose proof (interp_schedule_rr_equ handler (S n) (ts @ i := t) (ts @ i := u)
      focus m sigma (replace_pool_equ ts ts i t u (pool_equ_refl ts) Eq)) as Ep.
    rewrite Ep; reflexivity.
  Qed.

  Lemma segment_nd_focused_guard n (ts : pool E (S n)) (i : Fin.t (S n)) t sigma :
    interp_schedule_nd handler (S n) (ts @ i := Guard t) (Some i) sigma ~
    interp_schedule_nd handler (S n) (ts @ i := t) (Some i) sigma.
  Proof.
    erewrite interp_schedule_nd_guard
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  Lemma segment_rr_focused_guard n (ts : pool E (S n)) (i : Fin.t (S n)) t m sigma :
    interp_schedule_rr handler (S n) (ts @ i := Guard t) (Some i) m sigma ~
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m sigma.
  Proof.
    erewrite interp_schedule_rr_guard
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  Lemma guard_equ_focused_nd n (ts : pool E (S n)) (i : Fin.t (S n)) t u sigma :
    guard_equ t u ->
    interp_schedule_nd handler (S n) (ts @ i := t) (Some i) sigma ~
    interp_schedule_nd handler (S n) (ts @ i := u) (Some i) sigma.
  Proof.
    intro H; induction H as [t u [Eq|Eg]|t|t u H IH|t u v H1 IH1 H2 IH2].
    - apply segment_nd_replace_equ; exact Eq.
    - etransitivity; [apply segment_nd_replace_equ; exact Eg|].
      apply segment_nd_focused_guard.
    - reflexivity.
    - symmetry; exact IH.
    - etransitivity; [exact IH1|exact IH2].
  Qed.

  Lemma guard_equ_focused_rr n (ts : pool E (S n)) (i : Fin.t (S n)) t u m sigma :
    guard_equ t u ->
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m sigma ~
    interp_schedule_rr handler (S n) (ts @ i := u) (Some i) m sigma.
  Proof.
    intro H; induction H as [t u [Eq|Eg]|t|t u H IH|t u v H1 IH1 H2 IH2].
    - apply segment_rr_replace_equ; exact Eq.
    - etransitivity; [apply segment_rr_replace_equ; exact Eg|].
      apply segment_rr_focused_guard.
    - reflexivity.
    - symmetry; exact IH.
    - etransitivity; [exact IH1|exact IH2].
  Qed.

  Lemma segment_nd_focused_user n (ts : pool E (S n)) (i : Fin.t (S n))
    (e : E) (k : encode e -> thread E) sigma :
    interp_schedule_nd handler (S n)
      (ts @ i := (@go (yieldE + (forkE + E)) _ unit
                    (VisF (inr (inr e) : yieldE + (forkE + E)) k))) (Some i) sigma ~
    (runStateT (handler e) sigma >>= fun '(x,sigma') =>
      interp_schedule_nd handler (S n) (ts @ i := k x) (Some i) sigma').
  Proof.
    erewrite interp_schedule_nd_user
      by (rewrite Vector.nth_replace_eq; reflexivity).
    apply sbisim_clo_bind_eq; [reflexivity|].
    intros [x sigma']; rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  Lemma segment_rr_focused_user n (ts : pool E (S n)) (i : Fin.t (S n))
    (e : E) (k : encode e -> thread E) m sigma :
    interp_schedule_rr handler (S n)
      (ts @ i := (@go (yieldE + (forkE + E)) _ unit
                    (VisF (inr (inr e) : yieldE + (forkE + E)) k))) (Some i) m sigma ~
    (runStateT (handler e) sigma >>= fun '(x,sigma') =>
      interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m sigma').
  Proof.
    erewrite interp_schedule_rr_user
      by (rewrite Vector.nth_replace_eq; reflexivity).
    apply sbisim_clo_bind_eq; [reflexivity|].
    intros [x sigma']; rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  (** Exact equations retain the finite administrative guard path.  RR
      selection is NOT a visible branch after refinement: its three guards must
      not be used as a guarded [sbisim] coinduction hypothesis. *)
  Lemma segment_rr_guard_exact n (ts : pool E (S n)) (i : Fin.t (S n)) t m sigma :
    observe (ts $ i) = GuardF t ->
    interp_schedule_rr handler (S n) ts (Some i) m sigma ≅
    Guard (interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m sigma).
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_guard n ts i t Hobs).
    rewrite interp_erase_guard, interp_state_tau; reflexivity.
  Qed.

  Lemma segment_rr_yield_exact n (ts : pool E (S n)) (i : Fin.t (S n)) k m sigma :
    observe (ts $ i) = VisF (inl Yield) k ->
    interp_schedule_rr handler (S n) ts (Some i) m sigma ≅
    Guard (interp_schedule_rr handler (S n) (ts @ i := k tt) None m sigma).
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_yield n ts i k Hobs).
    rewrite interp_erase_guard, interp_state_tau; reflexivity.
  Qed.

  Lemma segment_rr_user_exact n (ts : pool E (S n)) (i : Fin.t (S n))
    (e : E) (k : encode e -> thread E) m sigma :
    observe (ts $ i) = VisF (inr (inr e)) k ->
    interp_schedule_rr handler (S n) ts (Some i) m sigma ≅
    (runStateT (handler e) sigma >>= fun '(x,sigma') =>
      Guard (Guard (Guard
        (interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m sigma')))).
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_user_event n ts i e k Hobs).
    rewrite interp_erase_user, interp_state_vis.
    apply equ_clo_bind with (S := eq); [reflexivity|].
    intros [x sigma'] r <-; apply guard_equ_node.
    etransitivity; [apply interp_state_tau|].
    apply guard_equ_node, interp_state_tau.
  Qed.

  Lemma segment_rr_select_exact n (ts : pool E (S n)) m sigma :
    interp_schedule_rr handler (S n) ts None m sigma ≅
    Guard (Guard (Guard
      (interp_schedule_rr handler (S n) ts (Some (rr_pick n m)) (S m) sigma))).
  Proof.
    unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, schedule_no_focus_nonempty.
    rewrite interp_erase_yield.
    etransitivity; [apply interp_state_tau|].
    apply guard_equ_node.
    etransitivity; [apply interp_state_tau|].
    apply guard_equ_node.
    rewrite (unfold_run_round_robin
      (Br n (fun i => schedule (S n) ts (Some i))) m).
    change (interp_state handler
      (interp_yield (interp_spawn
        (Guard (run_round_robin (schedule (S n) ts (Some (rr_pick n m))) (S m))))) sigma ≅
      Guard (interp_schedule_rr handler (S n) ts (Some (rr_pick n m)) (S m) sigma)).
    rewrite interp_erase_guard, interp_state_tau; reflexivity.
  Qed.

  Lemma exact_rr_user_replaced n (ts : pool E (S n)) (i : Fin.t (S n))
    (e : E) (k : encode e -> thread E) m sigma :
    interp_schedule_rr handler (S n)
      (ts @ i := (@go (yieldE + (forkE + E)) _ unit
                    (VisF (inr (inr e) : yieldE + (forkE + E)) k))) (Some i) m sigma ≅
    (runStateT (handler e) sigma >>= fun '(x,sigma') =>
      rr_guards 3 (interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m sigma')).
  Proof.
    etransitivity.
    - eapply segment_rr_user_exact; rewrite Vector.nth_replace_eq; reflexivity.
    - apply equ_clo_bind with (S := eq); [reflexivity|].
      intros [x sigma'] y <-; rewrite Vector.replace_replace_eq; reflexivity.
  Qed.
End FocusedCongruence.

(** ** Segment-driven scheduling.

    These need the response relation to imply strong bisimulation. *)
Section SegmentInterpretation.
  Context {E W Sigma : Type} {HE : Encode E}
    (handler : E ~> stateT Sigma (ictreeW W))
    (R : forall X : Type, ictreeW W X -> ictreeW W X -> Prop)
    (HR : forall X (t u : ictreeW W X), R X t u -> t ~ u).

  Lemma segment_interp_nd n (ts : pool E (S n)) (i : Fin.t (S n))
    t sigma xs residual sigma' :
    ThreadSegment handler R t sigma xs residual sigma' ->
    interp_schedule_nd handler (S n) (ts @ i := t) (Some i) sigma ~
    emit_list xs (interp_schedule_nd handler (S n) (ts @ i := residual) None sigma').
  Proof.
    intro H; revert n ts i.
    induction H as
      [k sigma
      |t sigma xs residual sigma' H IH
      |e k sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout]; intros n ts i.
    - cbn [emit_list].
      erewrite interp_schedule_nd_yield
        by (rewrite Vector.nth_replace_eq; reflexivity).
      rewrite Vector.replace_replace_eq; reflexivity.
    - etransitivity; [apply segment_nd_focused_guard|apply IH].
    - etransitivity; [apply segment_nd_focused_user|].
      transitivity (emit_list before (Ret (result,sigma1)) >>=
        fun '(x,sigma0) =>
          interp_schedule_nd handler (S n) (ts @ i := k x) (Some i) sigma0).
      + apply sbisim_clo_bind_eq; [apply HR; exact Eh|intro r; reflexivity].
      + rewrite emit_list_ret_bind, emit_list_app.
        apply emit_list_sbisim; apply IH.
    - etransitivity; [apply segment_nd_replace_equ; exact Etu|].
      etransitivity; [apply IH|].
      apply emit_list_sbisim, segment_nd_replace_equ; exact Eout.
  Qed.

  Lemma segment_interp_rr n (ts : pool E (S n)) (i : Fin.t (S n))
    t m sigma xs residual sigma' :
    ThreadSegment handler R t sigma xs residual sigma' ->
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m sigma ~
    emit_list xs
      (interp_schedule_rr handler (S n) (ts @ i := residual) None m sigma').
  Proof.
    intro H; revert n ts i m.
    induction H as
      [k sigma
      |t sigma xs residual sigma' H IH
      |e k sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout]; intros n ts i m.
    - cbn [emit_list].
      erewrite interp_schedule_rr_yield
        by (rewrite Vector.nth_replace_eq; reflexivity).
      rewrite Vector.replace_replace_eq; reflexivity.
    - etransitivity; [apply segment_rr_focused_guard|apply IH].
    - etransitivity; [apply segment_rr_focused_user|].
      transitivity (emit_list before (Ret (result,sigma1)) >>=
        fun '(x,sigma0) =>
          interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m sigma0).
      + apply sbisim_clo_bind_eq; [apply HR; exact Eh|intro r; reflexivity].
      + rewrite emit_list_ret_bind, emit_list_app.
        apply emit_list_sbisim; apply IH.
    - etransitivity; [apply segment_rr_replace_equ; exact Etu|].
      etransitivity; [apply IH|].
      apply emit_list_sbisim, segment_rr_replace_equ; exact Eout.
  Qed.

  Theorem segment_scheduler_steps {n} (ts : pool E (S n)) sigma i
    logs residual sigma' ts' :
    ThreadSegment handler R (ts $ i) sigma logs residual sigma' ->
    pool_equ ts' (ts @ i := residual) ->
    exists next,
      finite_steps (interp_schedule_nd handler (S n) ts None sigma)
        (tau :: List.map (fun o => obs (Log o) tt) logs) next /\
      next ~ interp_schedule_nd handler (S n) ts' None sigma'.
  Proof.
    intros Hseg Epool.
    assert (Efocused : interp_schedule_nd handler (S n) ts (Some i) sigma ~
      emit_list logs (interp_schedule_nd handler (S n) ts' None sigma')).
    {
      transitivity
        (interp_schedule_nd handler (S n) (ts @ i := (ts $ i)) (Some i) sigma).
      - rewrite (interp_schedule_nd_equ handler (S n) _ _ (Some i) sigma
          (pool_replace_current ts i)); reflexivity.
      - transitivity (emit_list logs
          (interp_schedule_nd handler (S n) (ts @ i := residual) None sigma')).
        + eapply segment_interp_nd; exact Hseg.
        + apply emit_list_sbisim.
          rewrite <- (interp_schedule_nd_equ handler (S n) _ _ None sigma' Epool);
            reflexivity.
    }
    assert (Hbranch : trans tau
      (Br n (fun j => interp_schedule_nd handler (S n) ts (Some j) sigma))
      (interp_schedule_nd handler (S n) ts (Some i) sigma)).
    { eapply trans_br with (x := i); reflexivity. }
    pose proof (interp_schedule_nd_select handler n ts sigma) as Eselect;
      symmetry in Eselect.
    destruct (sbisim_trans _ _ _ tau eq Eselect Hbranch)
      as (l & focused & Hchoose & El & Efocus); subst l.
    assert (Eemit : emit_list logs
      (interp_schedule_nd handler (S n) ts' None sigma') ~ focused).
    { transitivity (interp_schedule_nd handler (S n) ts (Some i) sigma);
        [symmetry; exact Efocused|exact Efocus]. }
    destruct (finite_steps_sbisim _ _ _
      (finite_steps_emit_list logs
        (interp_schedule_nd handler (S n) ts' None sigma')) focused Eemit)
      as (next & Hlogs & Enext).
    exists next; split; [econstructor; eassumption|symmetry; exact Enext].
  Qed.
End SegmentInterpretation.

(** ** Exact-mode round-robin prefixes.

    Restricted to the [equ] instance: the administrative guard path is real
    and must not be weakened to [sbisim]. *)
Section ExactRoundRobinPrefix.
  Context {E W Sigma : Type} {HE : Encode E}
    (handler : E ~> stateT Sigma (ictreeW W)).

  Notation Rexact := (fun X (t u : ictreeW W X) => t ≅ u).

  Lemma exact_segment_rr_prefix n (ts : pool E (S n)) (i : Fin.t (S n))
    t m sigma logs residual sigma' :
    ThreadSegment handler Rexact t sigma logs residual sigma' ->
    exists word, rr_prefix_events word = logs /\
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m sigma ≅
      rr_prefix word (Guard
        (interp_schedule_rr handler (S n) (ts @ i := residual) None m sigma')).
  Proof.
    intro H; revert n ts i m.
    induction H as
      [k sigma
      |t sigma logs residual sigma' H IH
      |e k sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma logs u' residual sigma' Etu H IH Eout]; intros n ts i m.
    - exists []; split; [reflexivity|]; cbn [rr_prefix].
      etransitivity.
      + eapply segment_rr_yield_exact; rewrite Vector.nth_replace_eq; reflexivity.
      + rewrite Vector.replace_replace_eq; reflexivity.
    - destruct (IH n ts i m) as (word & Ew & Et).
      exists (RRGuard :: word); split; [exact Ew|]; cbn [rr_prefix].
      etransitivity.
      + eapply segment_rr_guard_exact; rewrite Vector.nth_replace_eq; reflexivity.
      + apply guard_equ_node; rewrite Vector.replace_replace_eq; exact Et.
    - destruct (IH n ts i m) as (word & Ew & Et).
      exists (List.map RRLog before ++ RRGuard :: RRGuard :: RRGuard :: word); split.
      + rewrite rr_prefix_events_app, rr_prefix_events_logs; cbn [rr_prefix_events].
        now rewrite Ew.
      + etransitivity; [apply exact_rr_user_replaced|].
        set (resume := fun response : (encode e * Sigma)%type =>
          let '(x,sigma0) := response in
          rr_guards 3
            (interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m sigma0)).
        transitivity (emit_list before (Ret (result,sigma1)) >>= resume).
        * apply equ_clo_bind with (S := eq); [exact Eh|intros x y <-; reflexivity].
        * etransitivity; [apply emit_list_ret_bind|]; unfold resume.
          transitivity (emit_list before
            (rr_guards 3 (rr_prefix word (Guard
              (interp_schedule_rr handler (S n)
                 (ts @ i := residual) None m sigma'))))).
          -- apply emit_list_equ, rr_guards_equ; exact Et.
          -- rewrite rr_prefix_app; cbn [rr_prefix rr_guards].
             symmetry; apply rr_prefix_emit.
    - destruct (IH n ts i m) as (word & Ew & Et).
      exists word; split; [exact Ew|].
      etransitivity.
      + apply interp_schedule_rr_equ, replace_pool_equ;
          [apply pool_equ_refl|exact Etu].
      + etransitivity; [exact Et|].
        apply rr_prefix_equ, guard_equ_node, interp_schedule_rr_equ,
          replace_pool_equ; [apply pool_equ_refl|exact Eout].
  Qed.
End ExactRoundRobinPrefix.
