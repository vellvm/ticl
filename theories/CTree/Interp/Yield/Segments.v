(** * First-yield thread segments, parameterized by handler and response relation.

    One finite derivation stops at the first source yield.  The handler premise
    of [segment_user] is the handler's ACTUAL effect semantics, related to a
    finite emission prefix by an arbitrary relation [R]; raw thread endpoints
    still use [equ eq].  Exactly two instances are used downstream:

      [fun X (t u : ctreeW W B X) => t ~ u]   (bisimulation mode)
      [fun X (t u : ctreeW W B X) => t ≅ u]   (exact mode)

    and [ThreadSegment_mono] transports between them.  There is no relation
    class or typeclass inference layer, and no second segment inductive. *)

From Stdlib Require Import List Arith.PeanoNat Fin Vector
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From TICL Require Import
  CTree.Core
  CTree.Trace
  CTree.Events.Writer
  CTree.Events.Yield
  CTree.Interp.State.Mod
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.Nondeterministic
  Utils.Vectors.

Import CTreeNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope list_scope.

(** Raw equivalence is bisimilarity. *)
Lemma equ_sbisim {E B : Type -> Type} {X : Type} (t u : ctree E B X) :
  t ≅ u -> t ~ u.
Proof. intro H; now rewrite H. Qed.

Lemma unfold_spinS {E B : Type -> Type} {X : Type} :
  (CTree.spinS : ctree E B X) ≅ Step CTree.spinS.
Proof. rewrite ctree_eta at 1; reflexivity. Qed.

Lemma step_equ_node {E B : Type -> Type} {X : Type} (t u : ctree E B X) :
  t ≅ u -> Step t ≅ Step u.
Proof. intro H; step; constructor; exact H. Qed.

(** [Fork] answers in [bool], [Yield] in [unit]: the two index types differ. *)
Lemma bool_neq_unit : @eq Type bool unit -> False.
Proof.
  intro H.
  assert (C : exists x y : bool, x <> y) by (exists true, false; discriminate).
  rewrite H in C; destruct C as (x & y & Hxy); apply Hxy; destruct x, y; reflexivity.
Qed.

(** Two [Vis] nodes with different events are not raw-equivalent. *)
Local Ltac vis_mismatch Eq :=
  let HT := fresh "HT" in
  pose proof (equ_vis_invT _ _ _ _ Eq) as HT;
  first [exact (bool_neq_unit HT) | exact (bool_neq_unit (eq_sym HT))
        | subst;
          let HE := fresh "HE" in
          pose proof (proj1 (equ_vis_invE _ _ _ _ Eq)) as HE; discriminate HE].

Section ThreadSegments.
  Context {E B : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W B))
    (R : forall X : Type, ctreeW W B X -> ctreeW W B X -> Prop).

  Inductive ThreadSegment :
    thread E B -> Sigma -> list W -> thread E B -> Sigma -> Prop :=
  | segment_yield (k : unit -> thread E B) sigma :
      ThreadSegment (Vis (inl1 Yield) k) sigma [] (k tt) sigma
  | segment_guard t sigma logs t' sigma' :
      ThreadSegment t sigma logs t' sigma' ->
      ThreadSegment (Guard t) sigma logs t' sigma'
  | segment_user {Y} (e : E Y) (k : Y -> thread E B) sigma result sigma1
      before after t' sigma' :
      R _ (handler _ e sigma) (emit_list before (Ret (sigma1,result))) ->
      ThreadSegment (k result) sigma1 after t' sigma' ->
      ThreadSegment (Vis (inr1 (inr1 e)) k) sigma (before ++ after) t' sigma'
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
    forall k : unit -> thread E B,
      t ≅ Vis (inl1 Yield) k ->
      xs = [] /\ sigma' = sigma /\ k tt ≅ residual.
  Proof.
    intro H; induction H as
      [k0 sigma
      |t sigma xs residual sigma' H IH
      |Y e k0 sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout].
    - intros k Eq; split; [reflexivity|]; split; [reflexivity|].
      symmetry; exact (proj2 (equ_vis_invE _ _ _ _ Eq) tt).
    - intros k Eq; step in Eq; cbn in Eq; inversion Eq.
    - intros k Eq; vis_mismatch Eq.
    - intros k Eq.
      assert (Eu : u ≅ Vis (inl1 Yield) k).
      { transitivity t; [symmetry; exact Etu|exact Eq]. }
      destruct (IH k Eu) as [Ex [Es Ek]].
      split; [exact Ex|]; split; [exact Es|].
      transitivity u'; assumption.
  Qed.

  Lemma ThreadSegment_yield_inv k sigma xs residual sigma' :
    ThreadSegment (Vis (inl1 Yield) k) sigma xs residual sigma' ->
    xs = [] /\ sigma' = sigma /\ k tt ≅ residual.
  Proof. intro H; eapply ThreadSegment_yield_inv_equ; [exact H|reflexivity]. Qed.

  Lemma ThreadSegment_guard_inv_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    forall u, t ≅ Guard u -> ThreadSegment u sigma xs residual sigma'.
  Proof.
    intro H; induction H as
      [k sigma
      |t sigma xs residual sigma' H IH
      |Y e k sigma result sigma1 before after residual sigma' Eh H IH
      |t v sigma xs v' residual sigma' Etv H IH Eout].
    - intros u Eq; step in Eq; cbn in Eq; inversion Eq.
    - intros u Eq; apply equ_guard_inv in Eq.
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

  Lemma ThreadSegment_user_inv_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    forall {Y} (e : E Y) (k : Y -> thread E B),
      t ≅ Vis (inr1 (inr1 e)) k ->
      exists result sigma1 before after,
        xs = before ++ after /\
        R _ (handler _ e sigma) (emit_list before (Ret (sigma1,result))) /\
        ThreadSegment (k result) sigma1 after residual sigma'.
  Proof.
    intro H; induction H as
      [k0 sigma
      |t sigma xs residual sigma' H IH
      |Y0 e0 k0 sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout].
    - intros Y e k Eq; vis_mismatch Eq.
    - intros Y e k Eq; step in Eq; cbn in Eq; inversion Eq.
    - intros Y e k Eq.
      pose proof (equ_vis_invT _ _ _ _ Eq) as HT; subst Y0.
      destruct (equ_vis_invE _ _ _ _ Eq) as [HE Hk].
      injection HE as <-.
      exists result, sigma1, before, after.
      split; [reflexivity|]; split; [exact Eh|].
      eapply ThreadSegment_equ_input; [exact (Hk result)|exact H].
    - intros Y e k Eq.
      assert (Eu : u ≅ Vis (inr1 (inr1 e)) k).
      { transitivity t; [symmetry; exact Etu|exact Eq]. }
      destruct (IH Y e k Eu) as [r [sigma1 [before [after [Ex [Eh Htail]]]]]].
      exists r, sigma1, before, after; split; [exact Ex|]; split; [exact Eh|].
      eapply ThreadSegment_equ_output; eassumption.
  Qed.

  Lemma ThreadSegment_user_inv {Y} (e : E Y) (k : Y -> thread E B)
    sigma xs residual sigma' :
    ThreadSegment (Vis (inr1 (inr1 e)) k) sigma xs residual sigma' ->
    exists result sigma1 before after,
      xs = before ++ after /\
      R _ (handler _ e sigma) (emit_list before (Ret (sigma1,result))) /\
      ThreadSegment (k result) sigma1 after residual sigma'.
  Proof. intro H; eapply ThreadSegment_user_inv_equ; [exact H|reflexivity]. Qed.

  (** A derivation starts at a yield, a guard or a user event. *)
  Lemma ThreadSegment_head t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    (exists k : unit -> thread E B, t ≅ Vis (inl1 Yield) k) \/
    (exists u, t ≅ Guard u) \/
    (exists Y (e : E Y) (k : Y -> thread E B), t ≅ Vis (inr1 (inr1 e)) k).
  Proof.
    intro H; induction H as
      [k0 sigma
      |t sigma xs residual sigma' H IH
      |Y e k0 sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout].
    - left; exists k0; reflexivity.
    - right; left; exists t; reflexivity.
    - right; right; exists Y, e, k0; reflexivity.
    - destruct IH as [(k & Eq)|[(v & Eq)|(Y & e & k & Eq)]].
      + left; exists k; transitivity u; assumption.
      + right; left; exists v; transitivity u; assumption.
      + right; right; exists Y, e, k; transitivity u; assumption.
  Qed.

  (** Hence a derivation never starts at a return, a fork, a branch, a
      visible step or a stuck node. *)
  Local Ltac head_absurd Hseg Heq :=
    let Eq := fresh "Eq" in
    destruct (ThreadSegment_head _ _ _ _ _ Hseg)
      as [(? & Eq)|[(? & Eq)|(? & ? & ? & Eq)]];
    rewrite Heq in Eq;
    first [solve [step in Eq; cbn in Eq; inversion Eq] | vis_mismatch Eq].

  Lemma ThreadSegment_ret_absurd_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' -> ~ (t ≅ Ret tt).
  Proof. intros Hseg Heq; head_absurd Hseg Heq. Qed.

  Lemma ThreadSegment_ret_absurd sigma xs residual sigma' :
    ~ ThreadSegment (Ret tt) sigma xs residual sigma'.
  Proof. intro H; eapply ThreadSegment_ret_absurd_equ; [exact H|reflexivity]. Qed.

  Lemma ThreadSegment_fork_absurd_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    forall k : bool -> thread E B, ~ (t ≅ Vis (inr1 (inl1 Fork)) k).
  Proof. intros Hseg k Heq; head_absurd Hseg Heq. Qed.

  Lemma ThreadSegment_fork_absurd k sigma xs residual sigma' :
    ~ ThreadSegment (Vis (inr1 (inl1 Fork)) k) sigma xs residual sigma'.
  Proof. intro H; eapply ThreadSegment_fork_absurd_equ; [exact H|reflexivity]. Qed.

  Lemma ThreadSegment_br_absurd_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    forall {Y} (c : B Y) (k : Y -> thread E B), ~ (t ≅ Br c k).
  Proof. intros Hseg Y c k Heq; head_absurd Hseg Heq. Qed.

  Lemma ThreadSegment_br_absurd {Y} (c : B Y) k sigma xs residual sigma' :
    ~ ThreadSegment (Br c k) sigma xs residual sigma'.
  Proof. intro H; eapply ThreadSegment_br_absurd_equ; [exact H|reflexivity]. Qed.

  Lemma ThreadSegment_step_absurd_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' ->
    forall u, ~ (t ≅ Step u).
  Proof. intros Hseg u Heq; head_absurd Hseg Heq. Qed.

  Lemma ThreadSegment_step_absurd u sigma xs residual sigma' :
    ~ ThreadSegment (Step u) sigma xs residual sigma'.
  Proof. intro H; eapply ThreadSegment_step_absurd_equ; [exact H|reflexivity]. Qed.

  Lemma ThreadSegment_stuck_absurd_equ t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' -> ~ (t ≅ Stuck).
  Proof. intros Hseg Heq; head_absurd Hseg Heq. Qed.

  Lemma ThreadSegment_stuck_absurd sigma xs residual sigma' :
    ~ ThreadSegment (Stuck : thread E B) sigma xs residual sigma'.
  Proof. intro H; eapply ThreadSegment_stuck_absurd_equ; [exact H|reflexivity]. Qed.

  (** A finite first-yield derivation cannot be manufactured by repeatedly
      unfolding a divergent guard.  A user case provides its actual response as
      the witness needed for the first visible raw transition. *)
  Lemma ThreadSegment_can_step t sigma xs residual sigma' :
    ThreadSegment t sigma xs residual sigma' -> exists l u, trans l t u.
  Proof.
    intro H; induction H as
      [k sigma
      |t sigma xs residual sigma' H IH
      |Y e k sigma result sigma1 before after residual sigma' Eh H IH
      |t u sigma xs u' residual sigma' Etu H IH Eout].
    - exists (obs (inl1 Yield) tt), (k tt); apply trans_vis.
    - destruct IH as [l [u Hstep]]; exists l, u; now apply trans_guard.
    - exists (obs (inr1 (inr1 e)) result), (k result); apply trans_vis.
    - destruct IH as [l [v Hstep]]; exists l, v; rewrite Etu; exact Hstep.
  Qed.

  Lemma ThreadSegment_divergent_absurd t sigma xs residual sigma' :
    is_stuck t -> ~ ThreadSegment t sigma xs residual sigma'.
  Proof.
    intros Hdiv Hseg.
    destruct (ThreadSegment_can_step _ _ _ _ _ Hseg) as (l & u & TR).
    exact (Hdiv l u TR).
  Qed.

  Lemma ThreadSegment_spin_absurd sigma xs residual sigma' :
    ~ ThreadSegment (CTree.spinS : thread E B) sigma xs residual sigma'.
  Proof.
    intro H; eapply ThreadSegment_step_absurd_equ; [exact H|].
    apply unfold_spinS.
  Qed.

  Lemma ThreadSegment_branchfree t sigma logs residual sigma' :
    ThreadSegment t sigma logs residual sigma' ->
    BranchFree t -> BranchFree residual.
  Proof.
    intro H; induction H as
      [k sigma|t sigma logs residual sigma' H IH
      |Y e k sigma result sigma1 before after residual sigma' Eh H IH
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
  Definition segment_to (t : thread E B) (sigma : Sigma)
    (logs : list W) (target : thread E B) (sigma' : Sigma) : Prop :=
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

Arguments ThreadSegment {E B W Sigma} handler R.
Arguments segment_to {E B W Sigma} handler R.

(** Weakening the response relation weakens the segment.  This is how an exact
    segment becomes a bisimulation-mode segment; [equ_sbisim] supplies the
    premise for the two instances actually used. *)
Lemma ThreadSegment_mono {E B : Type -> Type} {W Sigma : Type}
  (handler : E ~> stateT Sigma (ctreeW W B))
  (R R' : forall X : Type, ctreeW W B X -> ctreeW W B X -> Prop)
  (Hmono : forall X t u, R X t u -> R' X t u) :
  forall t sigma logs residual sigma',
    ThreadSegment handler R t sigma logs residual sigma' ->
    ThreadSegment handler R' t sigma logs residual sigma'.
Proof.
  intros t sigma logs residual sigma' H; induction H as
    [k sigma
    |t sigma logs residual sigma' H IH
    |Y e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma logs u' residual sigma' Etu H IH Eout].
  - apply segment_yield.
  - apply segment_guard; exact IH.
  - eapply segment_user; [apply Hmono; exact Eh|exact IH].
  - eapply segment_equ; eassumption.
Qed.

(** ** Scheduling laws.

    Response uniqueness, determinism, handler-fault exclusion, and the
    bisimulation-based scheduling equations additionally need that the
    response relation implies strong bisimulation. *)
Section SegmentScheduling.
  Context {E B : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W B))
    (R : forall X : Type, ctreeW W B X -> ctreeW W B X -> Prop)
    (HR : forall X (t u : ctreeW W B X), R X t u -> t ~ u).

  Lemma handler_response_unique {Y} (e : E Y) (sigma : Sigma)
    (result : Y) (sigma1 : Sigma) (before : list W)
    (result' : Y) (sigma2 : Sigma) (before' : list W) :
    R _ (handler _ e sigma) (emit_list before (Ret (sigma1,result))) ->
    R _ (handler _ e sigma) (emit_list before' (Ret (sigma2,result'))) ->
    before = before' /\ result = result' /\ sigma1 = sigma2.
  Proof.
    intros E1 E2; apply HR in E1; apply HR in E2.
    assert (Eq : emit_list (B := B) before (Ret (sigma1,result)) ~
                 emit_list (B := B) before' (Ret (sigma2,result'))).
    { transitivity (handler _ e sigma); [symmetry; exact E1|exact E2]. }
    destruct (emit_list_ret_injective _ _ _ _ Eq) as [Ex Er].
    inversion Er; subst; auto.
  Qed.

  Lemma ThreadSegment_fault_absurd {Y} (e : E Y) (k : Y -> thread E B)
    sigma xs residual sigma' :
    handler _ e sigma ~ (Stuck : ctreeW W B (Sigma * Y)) ->
    ~ ThreadSegment handler R (Vis (inr1 (inr1 e)) k) sigma xs residual sigma'.
  Proof.
    intros Ef Hseg.
    destruct (ThreadSegment_user_inv handler R e k sigma xs residual sigma' Hseg)
      as [result [sigma1 [before [after [_ [Eh _]]]]]].
    apply HR in Eh.
    apply (emit_list_ret_not_stuck (B := B) before (sigma1,result)).
    transitivity (handler _ e sigma); [symmetry; exact Eh|exact Ef].
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
      |Y e k sigma result sigma1 before after residual sigma' Eh H IH
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
Section FocusedCongruenceND.
  Context {E B : Type -> Type} `{Bn -< B} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W B)).

  Lemma segment_nd_replace_equ n (ts : pool E B (S n)) (i : Fin.t (S n))
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

  Lemma segment_nd_focused_guard n (ts : pool E B (S n)) (i : Fin.t (S n)) t sigma :
    interp_schedule_nd handler (S n) (ts @ i := Guard t) (Some i) sigma ~
    interp_schedule_nd handler (S n) (ts @ i := t) (Some i) sigma.
  Proof.
    erewrite interp_schedule_nd_guard
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  Lemma segment_nd_focused_user n (ts : pool E B (S n)) (i : Fin.t (S n))
    {Y} (e : E Y) (k : Y -> thread E B) sigma :
    interp_schedule_nd handler (S n) (ts @ i := Vis (inr1 (inr1 e)) k) (Some i) sigma ~
    (handler _ e sigma >>= fun '(sigma',x) =>
      interp_schedule_nd handler (S n) (ts @ i := k x) (Some i) sigma').
  Proof.
    erewrite interp_schedule_nd_user
      by (rewrite Vector.nth_replace_eq; reflexivity).
    __upto_bind_sbisim_eq; intros [sigma' x].
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.
End FocusedCongruenceND.

Section FocusedCongruenceRR.
  Context {E : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W Bn)).

  Lemma segment_rr_replace_equ n (ts : pool E Bn (S n)) (i : Fin.t (S n))
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

  Lemma segment_rr_focused_guard n (ts : pool E Bn (S n)) (i : Fin.t (S n)) t m sigma :
    interp_schedule_rr handler (S n) (ts @ i := Guard t) (Some i) m sigma ~
    interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m sigma.
  Proof.
    erewrite interp_schedule_rr_guard
      by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  Lemma segment_rr_focused_user n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    {Y} (e : E Y) (k : Y -> thread E Bn) m sigma :
    interp_schedule_rr handler (S n) (ts @ i := Vis (inr1 (inr1 e)) k) (Some i) m sigma ~
    (handler _ e sigma >>= fun '(sigma',x) =>
      interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m sigma').
  Proof.
    erewrite interp_schedule_rr_user
      by (rewrite Vector.nth_replace_eq; reflexivity).
    __upto_bind_sbisim_eq; intros [sigma' x].
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  (** Exact equations retain the finite administrative guard path.  RR
      selection is one visible step surrounded by administrative guards. *)
  Lemma segment_rr_guard_exact n (ts : pool E Bn (S n)) (i : Fin.t (S n)) t m sigma :
    observe (ts $ i) = GuardF t ->
    interp_schedule_rr handler (S n) ts (Some i) m sigma ≅
    Guard (interp_schedule_rr handler (S n) (ts @ i := t) (Some i) m sigma).
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_guard n ts i t Hobs).
    rewrite interp_erase_guard, interp_state_guard; reflexivity.
  Qed.

  Lemma segment_rr_yield_exact n (ts : pool E Bn (S n)) (i : Fin.t (S n)) k m sigma :
    observe (ts $ i) = VisF (inl1 Yield) k ->
    interp_schedule_rr handler (S n) ts (Some i) m sigma ≅
    Guard (interp_schedule_rr handler (S n) (ts @ i := k tt) None m sigma).
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_yield n ts i k Hobs).
    rewrite interp_erase_guard, interp_state_guard; reflexivity.
  Qed.

  Lemma segment_rr_user_exact n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    {Y} (e : E Y) (k : Y -> thread E Bn) m sigma :
    observe (ts $ i) = VisF (inr1 (inr1 e)) k ->
    interp_schedule_rr handler (S n) ts (Some i) m sigma ≅
    (handler _ e sigma >>= fun '(sigma',x) =>
      rr_guards 3 (interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m sigma')).
  Proof.
    intro Hobs; unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, (schedule_focused_user_event n ts i e k Hobs).
    rewrite interp_erase_user, interp_state_vis.
    apply equ_clo_bind with (S := eq); [reflexivity|].
    intros [sigma' x] r <-; cbn [fst snd rr_guards]; apply guard_equ_node.
    etransitivity; [apply interp_state_guard|].
    apply guard_equ_node, interp_state_guard.
  Qed.

  Lemma segment_rr_select_exact n (ts : pool E Bn (S n)) m sigma :
    interp_schedule_rr handler (S n) ts None m sigma ≅
    rr_guards 3 (Step (rr_guards 3
      (interp_schedule_rr handler (S n) ts (Some (rr_pick n m)) (S m) sigma))).
  Proof.
    unfold interp_schedule_rr at 1.
    rewrite unfold_run_round_robin, schedule_no_focus_nonempty.
    rewrite interp_erase_yield, interp_state_guard, interp_state_guard.
    cbn [rr_guards]; do 2 apply guard_equ_node.
    rewrite (unfold_run_round_robin
      (brS (branchn (S n)) (fun i => schedule (S n) ts (Some i))) m).
    cbn [observe _observe subevent CategoryOps.resum CategoryOps.ReSum_id
         CategoryOps.id_ Id_IFun].
    rewrite interp_erase_guard, interp_state_guard; apply guard_equ_node.
    rewrite unfold_run_round_robin; cbn [observe _observe].
    rewrite interp_erase_step, interp_state_step.
    apply step_equ_node.
    apply guard_equ_node.
    rewrite interp_state_guard; apply guard_equ_node.
    rewrite interp_state_guard; reflexivity.
  Qed.

  Lemma exact_rr_user_replaced n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    {Y} (e : E Y) (k : Y -> thread E Bn) m sigma :
    interp_schedule_rr handler (S n) (ts @ i := Vis (inr1 (inr1 e)) k) (Some i) m sigma ≅
    (handler _ e sigma >>= fun '(sigma',x) =>
      rr_guards 3 (interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m sigma')).
  Proof.
    etransitivity.
    - eapply segment_rr_user_exact; rewrite Vector.nth_replace_eq; reflexivity.
    - apply equ_clo_bind with (S := eq); [reflexivity|].
      intros [sigma' x] y <-; rewrite Vector.replace_replace_eq; reflexivity.
  Qed.
End FocusedCongruenceRR.

(** ** Segment-driven scheduling.

    These need the response relation to imply strong bisimulation. *)
Section SegmentInterpretationND.
  Context {E B : Type -> Type} `{Bn -< B} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W B))
    (R : forall X : Type, ctreeW W B X -> ctreeW W B X -> Prop)
    (HR : forall X (t u : ctreeW W B X), R X t u -> t ~ u).

  Lemma segment_interp_nd n (ts : pool E B (S n)) (i : Fin.t (S n))
    sigma xs residual sigma' :
    ThreadSegment handler R (ts $ i) sigma xs residual sigma' ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
    emit_list xs (interp_schedule_nd handler (S n) (ts @ i := residual) None sigma').
  Proof.
    intro Hseg.
    assert (Hgen : forall t s0 ys r0 s1,
      ThreadSegment handler R t s0 ys r0 s1 ->
      forall p (us : pool E B (S p)) (j : Fin.t (S p)),
        interp_schedule_nd handler (S p) (us @ j := t) (Some j) s0 ~
        emit_list ys (interp_schedule_nd handler (S p) (us @ j := r0) None s1)).
    {
      intros t s0 ys r0 s1 H'; induction H' as
        [k sigma0
        |t0 sigma0 xs0 residual0 sigma0' H' IH
        |Y e k sigma0 result sigma1 before after residual0 sigma0' Eh H' IH
        |t0 u sigma0 xs0 u' residual0 sigma0' Etu H' IH Eout]; intros p us j.
      - cbn [emit_list List.fold_right].
        erewrite interp_schedule_nd_yield
          by (rewrite Vector.nth_replace_eq; reflexivity).
        rewrite Vector.replace_replace_eq; reflexivity.
      - etransitivity; [apply segment_nd_focused_guard|apply IH].
      - etransitivity; [apply segment_nd_focused_user|].
        transitivity (emit_list before (Ret (sigma1,result)) >>=
          fun '(sigma2,x) =>
            interp_schedule_nd handler (S p) (us @ j := k x) (Some j) sigma2).
        + apply HR in Eh; rewrite Eh; reflexivity.
        + rewrite emit_list_ret_bind, emit_list_app.
          apply emit_list_sbisim; apply IH.
      - etransitivity; [apply segment_nd_replace_equ; exact Etu|].
        etransitivity; [apply IH|].
        apply emit_list_sbisim, segment_nd_replace_equ; exact Eout.
    }
    transitivity
      (interp_schedule_nd handler (S n) (ts @ i := (ts $ i)) (Some i) sigma).
    - symmetry; apply equ_sbisim;
        exact (interp_schedule_nd_equ handler (S n) (ts @ i := (ts $ i)) ts
          (Some i) sigma (pool_replace_current ts i)).
    - apply Hgen; exact Hseg.
  Qed.

  Theorem segment_scheduler_steps {n} (ts : pool E B (S n)) sigma i
    logs residual sigma' ts' :
    ThreadSegment handler R (ts $ i) sigma logs residual sigma' ->
    pool_equ ts' (ts @ i := residual) ->
    exists next,
      finite_steps (interp_schedule_nd handler (S n) ts None sigma)
        (τ :: List.map (fun o => obs (Log o) tt) logs) next /\
      next ~ interp_schedule_nd handler (S n) ts' None sigma'.
  Proof.
    intros Hseg Epool.
    assert (Efocused : interp_schedule_nd handler (S n) ts (Some i) sigma ~
      emit_list logs (interp_schedule_nd handler (S n) ts' None sigma')).
    {
      etransitivity;
        [exact (segment_interp_nd n ts i sigma logs residual sigma' Hseg)|].
      apply emit_list_sbisim.
      rewrite <- (interp_schedule_nd_equ handler (S n) _ _ None sigma' Epool);
        reflexivity.
    }
    assert (Hbranch : trans τ
      (brS (branchn (S n)) (fun j => interp_schedule_nd handler (S n) ts (Some j) sigma))
      (interp_schedule_nd handler (S n) ts (Some i) sigma)).
    { exact (trans_brS _ _ i). }
    pose proof (interp_schedule_nd_select handler n ts sigma) as Eselect;
      symmetry in Eselect.
    destruct (sbisim_trans_l _ _ _ τ Eselect Hbranch)
      as (focused & Hchoose & Efocus).
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
End SegmentInterpretationND.

Section SegmentInterpretationRR.
  Context {E : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W Bn))
    (R : forall X : Type, ctreeW W Bn X -> ctreeW W Bn X -> Prop)
    (HR : forall X (t u : ctreeW W Bn X), R X t u -> t ~ u).

  Lemma segment_interp_rr n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    m sigma xs residual sigma' :
    ThreadSegment handler R (ts $ i) sigma xs residual sigma' ->
    interp_schedule_rr handler (S n) ts (Some i) m sigma ~
    emit_list xs
      (interp_schedule_rr handler (S n) (ts @ i := residual) None m sigma').
  Proof.
    intro Hseg.
    assert (Hgen : forall t s0 ys r0 s1,
      ThreadSegment handler R t s0 ys r0 s1 ->
      forall p (us : pool E Bn (S p)) (j : Fin.t (S p)) c,
        interp_schedule_rr handler (S p) (us @ j := t) (Some j) c s0 ~
        emit_list ys (interp_schedule_rr handler (S p) (us @ j := r0) None c s1)).
    {
      intros t s0 ys r0 s1 H; induction H as
        [k sigma0
        |t0 sigma0 xs0 residual0 sigma0' H IH
        |Y e k sigma0 result sigma1 before after residual0 sigma0' Eh H IH
        |t0 u sigma0 xs0 u' residual0 sigma0' Etu H IH Eout]; intros p us j c.
      - cbn [emit_list List.fold_right].
        erewrite interp_schedule_rr_yield
          by (rewrite Vector.nth_replace_eq; reflexivity).
        rewrite Vector.replace_replace_eq; reflexivity.
      - etransitivity; [apply segment_rr_focused_guard|apply IH].
      - etransitivity; [apply segment_rr_focused_user|].
        transitivity (emit_list before (Ret (sigma1,result)) >>=
          fun '(sigma2,x) =>
            interp_schedule_rr handler (S p) (us @ j := k x) (Some j) c sigma2).
        + apply HR in Eh; rewrite Eh; reflexivity.
        + rewrite emit_list_ret_bind, emit_list_app.
          apply emit_list_sbisim; apply IH.
      - etransitivity; [apply segment_rr_replace_equ; exact Etu|].
        etransitivity; [apply IH|].
        apply emit_list_sbisim, segment_rr_replace_equ; exact Eout.
    }
    transitivity
      (interp_schedule_rr handler (S n) (ts @ i := (ts $ i)) (Some i) m sigma).
    - symmetry; apply equ_sbisim;
        exact (interp_schedule_rr_equ handler (S n) (ts @ i := (ts $ i)) ts
          (Some i) m sigma (pool_replace_current ts i)).
    - apply Hgen; exact Hseg.
  Qed.
End SegmentInterpretationRR.

(** ** Exact-mode round-robin prefixes.

    Restricted to the [equ] instance: the administrative guard path is real
    and must not be weakened to [sbisim]. *)
Section ExactRoundRobinPrefix.
  Context {E : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W Bn)).

  Abbreviation Rexact := (fun X (t u : ctreeW W Bn X) => t ≅ u).

  Lemma exact_segment_rr_prefix n (ts : pool E Bn (S n)) (i : Fin.t (S n))
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
      |Y e k sigma result sigma1 before after residual sigma' Eh H IH
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
        set (resume := fun response : (Sigma * Y)%type =>
          let '(sigma0,x) := response in
          rr_guards 3
            (interp_schedule_rr handler (S n) (ts @ i := k x) (Some i) m sigma0)).
        transitivity (emit_list before (Ret (sigma1,result)) >>= resume).
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


(** ** Closed turns.

    A focused first-yield segment that returns its slot to the SAME thread
    (up to finitely many leading guards) leaves the same pool behind:
    the focused interpreted pool is its logs followed by the unfocused pool
    at the final state. *)
Lemma closed_pool_guard_equ {E B : Type -> Type} {n} (ts : pool E B n) i residual :
  guard_equ residual (ts $ i) -> pool_guard_equ (ts @ i := residual) ts.
Proof.
  intros Htail j; destruct (Fin.eq_dec j i) as [->|Hne].
  - rewrite Vector.nth_replace_eq; exact Htail.
  - rewrite Vector.nth_replace_neq by congruence; reflexivity.
Qed.

Section SegmentPoolLoopND.
  Context {E B : Type -> Type} `{Bn -< B} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W B)).

  Abbreviation Rexact := (fun X (t u : ctreeW W B X) => t ≅ u).
  Abbreviation Rsb := (fun X (t u : ctreeW W B X) => t ~ u).

  Lemma segment_pool_nd_loop n (ts : pool E B (S n)) (i : Fin.t (S n))
    sigma logs sigma' :
    segment_to handler Rexact (ts $ i) sigma logs (ts $ i) sigma' ->
    interp_schedule_nd handler (S n) ts (Some i) sigma ~
    emit_list logs (interp_schedule_nd handler (S n) ts None sigma').
  Proof.
    intros (residual & Hseg & Htail).
    etransitivity.
    - apply (segment_interp_nd handler Rsb (fun Y t u (H' : t ~ u) => H')).
      exact (ThreadSegment_mono handler Rexact Rsb (fun Y t u => equ_sbisim t u)
        _ _ _ _ _ Hseg).
    - apply emit_list_sbisim, interp_schedule_nd_guard_equ.
      apply closed_pool_guard_equ, Htail.
  Qed.
End SegmentPoolLoopND.

Section SegmentPoolLoopRR.
  Context {E : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W Bn)).

  Abbreviation Rexact := (fun X (t u : ctreeW W Bn X) => t ≅ u).
  Abbreviation Rsb := (fun X (t u : ctreeW W Bn X) => t ~ u).

  Lemma segment_pool_rr_loop n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    m sigma logs sigma' :
    segment_to handler Rexact (ts $ i) sigma logs (ts $ i) sigma' ->
    interp_schedule_rr handler (S n) ts (Some i) m sigma ~
    emit_list logs (interp_schedule_rr handler (S n) ts None m sigma').
  Proof.
    intros (residual & Hseg & Htail).
    etransitivity.
    - apply (segment_interp_rr handler Rsb (fun Y t u (H : t ~ u) => H)).
      exact (ThreadSegment_mono handler Rexact Rsb (fun Y t u => equ_sbisim t u)
        _ _ _ _ _ Hseg).
    - apply emit_list_sbisim, interp_schedule_rr_guard_equ.
      apply closed_pool_guard_equ, Htail.
  Qed.
End SegmentPoolLoopRR.
