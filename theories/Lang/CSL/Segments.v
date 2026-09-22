From Stdlib Require Import List Arith.PeanoNat Fin Vector
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From ExtLib Require Import Data.Monads.StateMonad.
From TICL Require Import
  Lang.CSL.Syntax Lang.CSL.Heap Lang.CSL.Denote Lang.CSL.Interp
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Trans ICTree.Trace
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Interp.State.Mod
  ICTree.Interp.Refine ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin Utils.Vectors.

Import ICtree ICTreeNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope list_scope.

(** A finite derivation stops at the first source yield.  The handler premise
    is its actual effect semantics, not an allocator transition assumption. *)
Inductive ThreadSegment : thread sE -> SSig -> list SObs -> thread sE -> SSig -> Prop :=
| segment_yield (k : unit -> thread sE) sigma :
    ThreadSegment (Vis (inl Yield) k) sigma [] (k tt) sigma
| segment_guard t sigma logs t' sigma' :
    ThreadSegment t sigma logs t' sigma' ->
    ThreadSegment (Guard t) sigma logs t' sigma'
| segment_user (e : sE) (k : encode e -> thread sE) sigma result sigma1
    before after t' sigma' :
    runStateT (sh e) sigma ~ emit_list before (Ret (result,sigma1)) ->
    ThreadSegment (k result) sigma1 after t' sigma' ->
    ThreadSegment (@go CEff _ unit (VisF (inr (inr e) : CEff) k))
      sigma (before ++ after) t' sigma'
| segment_equ t u sigma logs u' t' sigma' :
    t ≅ u -> ThreadSegment u sigma logs u' sigma' -> u' ≅ t' ->
    ThreadSegment t sigma logs t' sigma'.

Definition pool_guard_equ {n} (ts us : pool sE n) : Prop :=
  forall i, guard_equ (ts $ i) (us $ i).

Lemma execution_pool_guard_equ {n} (ts us : pool sE n) :
  pool_equ ts us -> pool_guard_equ ts us.
Proof. intros H i; apply guard_equ_equ, H. Qed.

Lemma execution_pool_guard_replace {n} (ts us : pool sE n)
  (i : Fin.t n) t u :
  pool_guard_equ ts us -> guard_equ t u ->
  pool_guard_equ (ts @ i := t) (us @ i := u).
Proof.
  intros Hpool Htu j; destruct (Fin.eq_dec j i) as [->|Hneq].
  - rewrite !Vector.nth_replace_eq; exact Htu.
  - rewrite !Vector.nth_replace_neq by congruence; apply Hpool.
Qed.

Lemma source_replace_current n (ts : pool sE n) (i : Fin.t n) :
  pool_equ (ts @ i := (ts $ i)) ts.
Proof.
  intro j; destruct (Fin.eq_dec j i) as [->|Hne].
  - rewrite Vector.nth_replace_eq; reflexivity.
  - rewrite Vector.nth_replace_neq by congruence; reflexivity.
Qed.

Lemma source_pool_equ_guard_trans {n} (ts us vs : pool sE n) :
  pool_equ ts us -> pool_guard_equ us vs -> pool_guard_equ ts vs.
Proof.
  intros E H i; eapply guard_equ_trans; [apply guard_equ_equ, E|apply H].
Qed.

Lemma handler_response_unique (e : sE) (sigma : SSig)
  (result : encode e) (sigma1 : SSig) (before : list SObs)
  (result' : encode e) (sigma2 : SSig) (before' : list SObs) :
  runStateT (sh e) sigma ~ emit_list before (Ret (result,sigma1)) ->
  runStateT (sh e) sigma ~ emit_list before' (Ret (result',sigma2)) ->
  before = before' /\ result = result' /\ sigma1 = sigma2.
Proof.
  intros E1 E2.
  assert (E : emit_list before (Ret (result,sigma1)) ~
              emit_list before' (Ret (result',sigma2))).
  { transitivity (runStateT (sh e) sigma); [symmetry; exact E1|exact E2]. }
  destruct (emit_list_ret_injective _ _ _ _ E) as [Ex Er].
  inversion Er; subst; auto.
Qed.

(** Raw congruence is allowed on both ends, but no source-side [sbisim]
    congruence is used. *)
Lemma ThreadSegment_equ_input t u sigma xs residual sigma' :
  t ≅ u -> ThreadSegment t sigma xs residual sigma' ->
  ThreadSegment u sigma xs residual sigma'.
Proof.
  intros E H; eapply segment_equ; [symmetry; exact E|exact H|reflexivity].
Qed.

Lemma ThreadSegment_equ_output t sigma xs residual residual' sigma' :
  ThreadSegment t sigma xs residual sigma' -> residual ≅ residual' ->
  ThreadSegment t sigma xs residual' sigma'.
Proof. intros H E; eapply segment_equ; [reflexivity|exact H|exact E]. Qed.

Lemma ThreadSegment_yield_inv_equ t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  forall k : unit -> thread sE,
    t ≅ Vis (inl Yield) k ->
    xs = [] /\ sigma' = sigma /\ k tt ≅ residual.
Proof.
  intro H; induction H as
    [k0 sigma
    |t sigma xs residual sigma' H IH
    |e k0 sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout].
  - intros k E; split; [reflexivity|]; split; [reflexivity|].
    symmetry; exact (equ_vis_invE E tt).
  - intros k E; step in E; cbn in E; inversion E.
  - intros k E; pose proof (equ_vis_invT E) as [_ Ebad]; discriminate.
  - intros k E.
    assert (Eu : u ≅ Vis (inl Yield) k).
    { transitivity t; [symmetry; exact Etu|exact E]. }
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
  - intros u E; step in E; cbn in E; inversion E.
  - intros u E; apply equ_guard_invE in E.
    eapply ThreadSegment_equ_input; [exact E|exact H].
  - intros u E; step in E; cbn in E; inversion E.
  - intros u E.
    eapply ThreadSegment_equ_output; [|exact Eout].
    apply IH; transitivity t; [symmetry; exact Etv|exact E].
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
  forall (e : sE) (k : encode e -> thread sE),
    t ≅ (@go CEff _ unit (VisF (inr (inr e) : CEff) k)) ->
    exists result sigma1 before after,
      xs = before ++ after /\
      runStateT (sh e) sigma ~ emit_list before (Ret (result,sigma1)) /\
      ThreadSegment (k result) sigma1 after residual sigma'.
Proof.
  intro H; induction H as
    [k0 sigma
    |t sigma xs residual sigma' H IH
    |e0 k0 sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout].
  - intros e k E; pose proof (equ_vis_invT E) as [_ Ebad]; discriminate.
  - intros e k E; step in E; cbn in E; inversion E.
  - intros e k E.
    pose proof (equ_vis_invT E) as [_ Ee].
    assert (Eevent : e0 = e) by congruence; subst e.
    exists result, sigma1, before, after.
    split; [reflexivity|]; split; [exact Eh|].
    eapply ThreadSegment_equ_input; [exact (equ_vis_invE E result)|exact H].
  - intros e k E.
    assert (Eu : u ≅ (@go CEff _ unit (VisF (inr (inr e) : CEff) k))).
    { transitivity t; [symmetry; exact Etu|exact E]. }
    destruct (IH e k Eu) as [r [sigma1 [before [after [Ex [Eh Htail]]]]]].
    exists r, sigma1, before, after; split; [exact Ex|]; split; [exact Eh|].
    eapply ThreadSegment_equ_output; eassumption.
Qed.

Lemma ThreadSegment_user_inv (e : sE) (k : encode e -> thread sE)
  sigma xs residual sigma' :
  ThreadSegment ((@go CEff _ unit (VisF (inr (inr e) : CEff) k))) sigma xs residual sigma' ->
  exists result sigma1 before after,
    xs = before ++ after /\
    runStateT (sh e) sigma ~ emit_list before (Ret (result,sigma1)) /\
    ThreadSegment (k result) sigma1 after residual sigma'.
Proof. intro H; eapply ThreadSegment_user_inv_equ; [exact H|reflexivity]. Qed.

Lemma ThreadSegment_ret_absurd_equ t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' -> ~ (t ≅ Ret tt).
Proof.
  intro H; induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intro E.
  - step in E; cbn in E; inversion E.
  - step in E; cbn in E; inversion E.
  - step in E; cbn in E; inversion E.
  - apply IH; transitivity t; [symmetry; exact Etu|exact E].
Qed.

Lemma ThreadSegment_ret_absurd sigma xs residual sigma' :
  ~ ThreadSegment (Ret tt) sigma xs residual sigma'.
Proof. intro H; eapply ThreadSegment_ret_absurd_equ; [exact H|reflexivity]. Qed.

Lemma ThreadSegment_fork_absurd_equ t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  forall k : bool -> thread sE, ~ (t ≅ Vis (inr (inl Fork)) k).
Proof.
  intro H; induction H as
    [k0 sigma
    |t sigma xs residual sigma' H IH
    |e k0 sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intros k E.
  - pose proof (equ_vis_invT E) as [_ Ebad]; discriminate.
  - step in E; cbn in E; inversion E.
  - pose proof (equ_vis_invT E) as [_ Ebad]; discriminate.
  - apply (IH k); transitivity t; [symmetry; exact Etu|exact E].
Qed.

Lemma ThreadSegment_fork_absurd k sigma xs residual sigma' :
  ~ ThreadSegment (Vis (inr (inl Fork)) k) sigma xs residual sigma'.
Proof. intro H; eapply ThreadSegment_fork_absurd_equ; [exact H|reflexivity]. Qed.

Lemma ThreadSegment_br_absurd_equ t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  forall n (k : Fin.t (S n) -> thread sE), ~ (t ≅ Br n k).
Proof.
  intro H; induction H as
    [k0 sigma
    |t sigma xs residual sigma' H IH
    |e k0 sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intros n k E.
  - step in E; cbn in E; inversion E.
  - step in E; cbn in E; inversion E.
  - step in E; cbn in E; inversion E.
  - apply (IH n k); transitivity t; [symmetry; exact Etu|exact E].
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
  - exists (obs (inr (inr e) : CEff) result), (k result); apply trans_vis.
  - destruct IH as [l [v Hstep]]; exists l, v; rewrite Etu; exact Hstep.
Qed.

Lemma ThreadSegment_divergent_absurd t sigma xs residual sigma' :
  is_stuck t -> ~ ThreadSegment t sigma xs residual sigma'.
Proof. intros Hdiv Hseg; apply Hdiv; eapply ThreadSegment_can_step; exact Hseg. Qed.

Lemma ThreadSegment_stuck_absurd sigma xs residual sigma' :
  ~ ThreadSegment (stuck : thread sE) sigma xs residual sigma'.
Proof. apply ThreadSegment_divergent_absurd, stuck_is_stuck. Qed.

Lemma ThreadSegment_spin_absurd sigma xs residual sigma' :
  ~ ThreadSegment (spin : thread sE) sigma xs residual sigma'.
Proof.
  intro H; eapply ThreadSegment_br_absurd_equ; [exact H|].
  apply unfold_spin.
Qed.

Lemma ThreadSegment_fault_absurd (e : sE) (k : encode e -> thread sE)
  sigma xs residual sigma' :
  runStateT (sh e) sigma ~ (stuck : ictreeW SObs (encode e * SSig)) ->
  ~ ThreadSegment ((@go CEff _ unit (VisF (inr (inr e) : CEff) k))) sigma xs residual sigma'.
Proof.
  intros Ef Hseg.
  destruct (ThreadSegment_user_inv e k sigma xs residual sigma' Hseg)
    as [result [sigma1 [before [after [_ [Eh _]]]]]].
  apply (emit_list_ret_not_stuck before (result,sigma1)).
  transitivity (runStateT (sh e) sigma); [symmetry; exact Eh|exact Ef].
Qed.

Lemma ThreadSegment_deterministic t sigma xs u sigma1 ys v sigma2 :
  ThreadSegment t sigma xs u sigma1 ->
  ThreadSegment t sigma ys v sigma2 ->
  xs = ys /\ sigma1 = sigma2 /\ u ≅ v.
Proof.
  intros H1; revert ys v sigma2.
  induction H1 as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intros ys v sigma2 H2.
  - destruct (ThreadSegment_yield_inv k sigma ys v sigma2 H2)
      as [Ex [Es Ek]].
    split; [symmetry; exact Ex|]; split; [symmetry; exact Es|exact Ek].
  - apply IH; now apply ThreadSegment_guard_inv in H2.
  - destruct (ThreadSegment_user_inv e k sigma ys v sigma2 H2)
      as [r [sigma0 [before0 [after0 [Ey [Eh0 Htail]]]]]].
    destruct (handler_response_unique e sigma result sigma1 before
      r sigma0 before0 Eh Eh0) as [Eb [Er Es]].
    subst before0; subst r; subst sigma0.
    destruct (IH after0 v sigma2 Htail) as [Ea [Es Er]].
    split; [subst ys; now rewrite Ea|]; split; assumption.
  - assert (H2u : ThreadSegment u sigma ys v sigma2).
    { eapply ThreadSegment_equ_input; [exact Etu|exact H2]. }
    destruct (IH ys v sigma2 H2u) as [Ex [Es Er]].
    split; [exact Ex|]; split; [exact Es|].
    transitivity u'; [symmetry; exact Eout|exact Er].
Qed.

#[global] Instance guard_equ_Equivalence : Equivalence guard_equ.
Proof.
  split.
  - intro t; apply guard_equ_equ; reflexivity.
  - intros t u; apply guard_equ_sym.
  - intros t u v; apply guard_equ_trans.
Qed.

Lemma guard_equ_sbisim t u : guard_equ t u -> t ~ u.
Proof.
  intro H; induction H as [t u E|t u H IH|t u H IH|t u H IH|t u v H1 IH1 H2 IH2].
  - rewrite E; reflexivity.
  - rewrite sb_guard; exact IH.
  - rewrite sb_guard; exact IH.
  - symmetry; exact IH.
  - transitivity u; assumption.
Qed.

(** This stronger same-residual transport follows from the output-equ rule.
    Symmetry in the finite guard closure is handled by proving both directions
    together, rather than assuming a reverse simulation. *)
Lemma guard_equ_segment_iff t u : guard_equ t u ->
  forall sigma xs residual sigma',
    ThreadSegment t sigma xs residual sigma' <->
    ThreadSegment u sigma xs residual sigma'.
Proof.
  intro H; induction H as [t u E|t u H IH|t u H IH|t u H IH|t u v H1 IH1 H2 IH2];
    intros sigma xs residual sigma'.
  - split; intro Hseg.
    + eapply ThreadSegment_equ_input; [exact E|exact Hseg].
    + eapply ThreadSegment_equ_input; [symmetry; exact E|exact Hseg].
  - rewrite ThreadSegment_guard_iff; apply IH.
  - rewrite ThreadSegment_guard_iff; apply IH.
  - symmetry; apply IH.
  - transitivity (ThreadSegment u sigma xs residual sigma'); [apply IH1|apply IH2].
Qed.

Lemma guard_equ_segment t u sigma xs t' sigma' :
  guard_equ t u -> ThreadSegment t sigma xs t' sigma' ->
  exists u', ThreadSegment u sigma xs u' sigma' /\ guard_equ t' u'.
Proof.
  intros E Hseg; exists t'; split.
  - apply (proj1 (guard_equ_segment_iff t u E sigma xs t' sigma')); exact Hseg.
  - apply guard_equ_equ; reflexivity.
Qed.

Lemma guard_equ_br_yield_absurd n (k : Fin.t (S n) -> thread sE)
  (ky : unit -> thread sE) : ~ guard_equ (Br n k) (Vis (inl Yield) ky).
Proof.
  intro E; apply guard_equ_sbisim in E.
  eapply (@sbisim_vis_br_inv CEff _ unit n (inl Yield) ky k); symmetry; exact E.
Qed.

(** Equivalence of pools is used only for genuine raw [equ].  Guard removal
    below is deliberately restricted to the focused slot. *)
Lemma segment_nd_replace_equ n (ts : pool sE (S n)) (i : Fin.t (S n))
  t u focus sigma :
  t ≅ u ->
  interp_nd (S n) (ts @ i := t) focus sigma ~
  interp_nd (S n) (ts @ i := u) focus sigma.
Proof.
  intro E.
  pose proof (interp_nd_equ (S n) (ts @ i := t) (ts @ i := u)
    focus sigma (replace_pool_equ ts ts i t u (pool_equ_refl ts) E)) as Ep.
  rewrite Ep; reflexivity.
Qed.

Lemma segment_rr_replace_equ n (ts : pool sE (S n)) (i : Fin.t (S n))
  t u focus m sigma :
  t ≅ u ->
  interp_schedule_rr sh (S n) (ts @ i := t) focus m sigma ~
  interp_schedule_rr sh (S n) (ts @ i := u) focus m sigma.
Proof.
  intro E.
  pose proof (interp_schedule_rr_equ sh (S n) (ts @ i := t) (ts @ i := u)
    focus m sigma (replace_pool_equ ts ts i t u (pool_equ_refl ts) E)) as Ep.
  rewrite Ep; reflexivity.
Qed.

Lemma segment_nd_focused_guard n (ts : pool sE (S n)) (i : Fin.t (S n)) t sigma :
  interp_nd (S n) (ts @ i := Guard t) (Some i) sigma ~
  interp_nd (S n) (ts @ i := t) (Some i) sigma.
Proof.
  erewrite interp_nd_guard by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma segment_rr_focused_guard n (ts : pool sE (S n)) (i : Fin.t (S n)) t m sigma :
  interp_schedule_rr sh (S n) (ts @ i := Guard t) (Some i) m sigma ~
  interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma.
Proof.
  erewrite interp_schedule_rr_guard by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma guard_equ_focused_nd n (ts : pool sE (S n)) (i : Fin.t (S n)) t u sigma :
  guard_equ t u ->
  interp_nd (S n) (ts @ i := t) (Some i) sigma ~
  interp_nd (S n) (ts @ i := u) (Some i) sigma.
Proof.
  intro H; induction H as [t u E|t u H IH|t u H IH|t u H IH|t u v H1 IH1 H2 IH2].
  - apply segment_nd_replace_equ; exact E.
  - etransitivity; [apply segment_nd_focused_guard|exact IH].
  - etransitivity; [exact IH|symmetry; apply segment_nd_focused_guard].
  - symmetry; exact IH.
  - etransitivity; [exact IH1|exact IH2].
Qed.

Lemma guard_equ_focused_rr n (ts : pool sE (S n)) (i : Fin.t (S n)) t u m sigma :
  guard_equ t u ->
  interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma ~
  interp_schedule_rr sh (S n) (ts @ i := u) (Some i) m sigma.
Proof.
  intro H; induction H as [t u E|t u H IH|t u H IH|t u H IH|t u v H1 IH1 H2 IH2].
  - apply segment_rr_replace_equ; exact E.
  - etransitivity; [apply segment_rr_focused_guard|exact IH].
  - etransitivity; [exact IH|symmetry; apply segment_rr_focused_guard].
  - symmetry; exact IH.
  - etransitivity; [exact IH1|exact IH2].
Qed.

Lemma segment_nd_focused_user n (ts : pool sE (S n)) (i : Fin.t (S n))
  (e : sE) (k : encode e -> thread sE) sigma :
  interp_nd (S n) (ts @ i := (@go CEff _ unit (VisF (inr (inr e) : CEff) k))) (Some i) sigma ~
  (runStateT (sh e) sigma >>= fun '(x,sigma') =>
    interp_nd (S n) (ts @ i := k x) (Some i) sigma').
Proof.
  erewrite interp_nd_user by (rewrite Vector.nth_replace_eq; reflexivity).
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [x sigma']; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma segment_rr_focused_user n (ts : pool sE (S n)) (i : Fin.t (S n))
  (e : sE) (k : encode e -> thread sE) m sigma :
  interp_schedule_rr sh (S n) (ts @ i := (@go CEff _ unit (VisF (inr (inr e) : CEff) k))) (Some i) m sigma ~
  (runStateT (sh e) sigma >>= fun '(x,sigma') =>
    interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma').
Proof.
  erewrite interp_schedule_rr_user by (rewrite Vector.nth_replace_eq; reflexivity).
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [x sigma']; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma segment_interp_nd n (ts : pool sE (S n)) (i : Fin.t (S n))
  t sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  interp_nd (S n) (ts @ i := t) (Some i) sigma ~
  emit_list xs (interp_nd (S n) (ts @ i := residual) None sigma').
Proof.
  intro H; revert n ts i.
  induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intros n ts i.
  - cbn [emit_list].
    erewrite interp_nd_yield by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq; reflexivity.
  - etransitivity; [apply segment_nd_focused_guard|apply IH].
  - etransitivity; [apply segment_nd_focused_user|].
    transitivity (emit_list before (Ret (result,sigma1)) >>=
      fun '(x,sigma0) => interp_nd (S n) (ts @ i := k x) (Some i) sigma0).
    + apply sbisim_clo_bind_eq; [exact Eh|intro r; reflexivity].
    + rewrite emit_list_ret_bind, emit_list_app.
      apply emit_list_sbisim; apply IH.
  - etransitivity; [apply segment_nd_replace_equ; exact Etu|].
    etransitivity; [apply IH|].
    apply emit_list_sbisim, segment_nd_replace_equ; exact Eout.
Qed.

Lemma segment_interp_rr n (ts : pool sE (S n)) (i : Fin.t (S n))
  t m sigma xs residual sigma' :
  ThreadSegment t sigma xs residual sigma' ->
  interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma ~
  emit_list xs (interp_schedule_rr sh (S n) (ts @ i := residual) None m sigma').
Proof.
  intro H; revert n ts i m.
  induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout]; intros n ts i m.
  - cbn [emit_list].
    erewrite interp_schedule_rr_yield by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq; reflexivity.
  - etransitivity; [apply segment_rr_focused_guard|apply IH].
  - etransitivity; [apply segment_rr_focused_user|].
    transitivity (emit_list before (Ret (result,sigma1)) >>=
      fun '(x,sigma0) => interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma0).
    + apply sbisim_clo_bind_eq; [exact Eh|intro r; reflexivity].
    + rewrite emit_list_ret_bind, emit_list_app.
      apply emit_list_sbisim; apply IH.
  - etransitivity; [apply segment_rr_replace_equ; exact Etu|].
    etransitivity; [apply IH|].
    apply emit_list_sbisim, segment_rr_replace_equ; exact Eout.
Qed.

(** Exact equations retain the finite administrative guard path.  In particular
    RR selection is not a visible branch after refinement: its three guards
    must not be used as a guarded [sbisim] coinduction hypothesis.  These laws
    expose them for induction on an actual [trans_] derivation instead. *)
Lemma segment_rr_guard_exact n (ts : pool sE (S n)) (i : Fin.t (S n))
  t m sigma :
  observe (ts $ i) = GuardF t ->
  interp_schedule_rr sh (S n) ts (Some i) m sigma ≅
  Guard (interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma).
Proof.
  intro Hobs; unfold interp_schedule_rr at 1.
  rewrite unfold_run_round_robin, (schedule_focused_guard n ts i t Hobs).
  rewrite interp_erase_guard, interp_state_tau; reflexivity.
Qed.

Lemma segment_rr_yield_exact n (ts : pool sE (S n)) (i : Fin.t (S n))
  k m sigma :
  observe (ts $ i) = VisF (inl Yield) k ->
  interp_schedule_rr sh (S n) ts (Some i) m sigma ≅
  Guard (interp_schedule_rr sh (S n) (ts @ i := k tt) None m sigma).
Proof.
  intro Hobs; unfold interp_schedule_rr at 1.
  rewrite unfold_run_round_robin, (schedule_focused_yield n ts i k Hobs).
  rewrite interp_erase_guard, interp_state_tau; reflexivity.
Qed.

Lemma segment_rr_user_exact n (ts : pool sE (S n)) (i : Fin.t (S n))
  (e : sE) (k : encode e -> thread sE) m sigma :
  observe (ts $ i) = VisF (inr (inr e)) k ->
  interp_schedule_rr sh (S n) ts (Some i) m sigma ≅
  (runStateT (sh e) sigma >>= fun '(x,sigma') =>
    Guard (Guard (Guard
      (interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma')))).
Proof.
  intro Hobs; unfold interp_schedule_rr at 1.
  rewrite unfold_run_round_robin, (schedule_focused_user_event n ts i e k Hobs).
  rewrite interp_erase_user, interp_state_vis.
  apply equ_clo_bind with (S := eq); [reflexivity|].
  intros [x sigma'] r <-; apply guard_equ_node.
  etransitivity; [apply interp_state_tau|].
  apply guard_equ_node, interp_state_tau.
Qed.

Lemma segment_rr_select_exact n (ts : pool sE (S n)) m sigma :
  interp_schedule_rr sh (S n) ts None m sigma ≅
  Guard (Guard (Guard
    (interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) sigma))).
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
  change (interp_state sh
    (interp_yield (interp_spawn
      (Guard (run_round_robin (schedule (S n) ts (Some (rr_pick n m))) (S m))))) sigma ≅
    Guard (interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) sigma)).
  rewrite interp_erase_guard, interp_state_tau; reflexivity.
Qed.

(** Primitive handlers return by raw equivalence in this stronger certificate.
    Unlike [ThreadSegment], it retains the finite administrative guard path
    needed for exact round-robin prefix alignment. *)
Inductive ExactThreadSegment : thread sE -> SSig -> list SObs -> thread sE -> SSig -> Prop :=
| exact_segment_yield (k : unit -> thread sE) sigma :
    ExactThreadSegment (Vis (inl Yield) k) sigma [] (k tt) sigma
| exact_segment_guard t sigma logs t' sigma' :
    ExactThreadSegment t sigma logs t' sigma' ->
    ExactThreadSegment (Guard t) sigma logs t' sigma'
| exact_segment_user (e : sE) (k : encode e -> thread sE) sigma result sigma1
    before after t' sigma' :
    runStateT (sh e) sigma ≅ emit_list before (Ret (result,sigma1)) ->
    ExactThreadSegment (k result) sigma1 after t' sigma' ->
    ExactThreadSegment (@go CEff _ unit (VisF (inr (inr e) : CEff) k))
      sigma (before ++ after) t' sigma'
| exact_segment_equ t u sigma logs u' t' sigma' :
    t ≅ u -> ExactThreadSegment u sigma logs u' sigma' -> u' ≅ t' ->
    ExactThreadSegment t sigma logs t' sigma'.

Lemma ExactThreadSegment_segment t sigma xs residual sigma' :
  ExactThreadSegment t sigma xs residual sigma' ->
  ThreadSegment t sigma xs residual sigma'.
Proof.
  intro H; induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t u sigma xs u' residual sigma' Etu H IH Eout].
  - apply segment_yield.
  - apply segment_guard; exact IH.
  - eapply segment_user; [|exact IH].
    eapply equ_clos_sbisim_goal; [exact Eh|reflexivity|reflexivity].
  - eapply segment_equ; eassumption.
Qed.

Lemma ExactThreadSegment_equ_input t u sigma xs residual sigma' :
  t ≅ u -> ExactThreadSegment t sigma xs residual sigma' ->
  ExactThreadSegment u sigma xs residual sigma'.
Proof.
  intros E H; eapply exact_segment_equ; [symmetry; exact E|exact H|reflexivity].
Qed.

Lemma ExactThreadSegment_equ_output t sigma xs residual residual' sigma' :
  ExactThreadSegment t sigma xs residual sigma' -> residual ≅ residual' ->
  ExactThreadSegment t sigma xs residual' sigma'.
Proof. intros H E; eapply exact_segment_equ; [reflexivity|exact H|exact E]. Qed.

Lemma ExactThreadSegment_guard_inv_equ t sigma xs residual sigma' :
  ExactThreadSegment t sigma xs residual sigma' ->
  forall u, t ≅ Guard u -> ExactThreadSegment u sigma xs residual sigma'.
Proof.
  intro H; induction H as
    [k sigma
    |t sigma xs residual sigma' H IH
    |e k sigma result sigma1 before after residual sigma' Eh H IH
    |t v sigma xs v' residual sigma' Etv H IH Eout].
  - intros u E; step in E; cbn in E; inversion E.
  - intros u E; apply equ_guard_invE in E.
    eapply ExactThreadSegment_equ_input; [exact E|exact H].
  - intros u E; step in E; cbn in E; inversion E.
  - intros u E.
    eapply ExactThreadSegment_equ_output; [|exact Eout].
    apply IH; transitivity t; [symmetry; exact Etv|exact E].
Qed.

Lemma ExactThreadSegment_guard_inv t sigma xs residual sigma' :
  ExactThreadSegment (Guard t) sigma xs residual sigma' ->
  ExactThreadSegment t sigma xs residual sigma'.
Proof. intro H; eapply ExactThreadSegment_guard_inv_equ; [exact H|reflexivity]. Qed.

Lemma ExactThreadSegment_guard_iff t sigma xs residual sigma' :
  ExactThreadSegment (Guard t) sigma xs residual sigma' <->
  ExactThreadSegment t sigma xs residual sigma'.
Proof. split; [apply ExactThreadSegment_guard_inv|apply exact_segment_guard]. Qed.

Lemma guard_equ_exact_segment_iff t u : guard_equ t u ->
  forall sigma xs residual sigma',
    ExactThreadSegment t sigma xs residual sigma' <->
    ExactThreadSegment u sigma xs residual sigma'.
Proof.
  intro H; induction H as [t u E|t u H IH|t u H IH|t u H IH|t u v H1 IH1 H2 IH2];
    intros sigma xs residual sigma'.
  - split; intro Hseg.
    + eapply ExactThreadSegment_equ_input; [exact E|exact Hseg].
    + eapply ExactThreadSegment_equ_input; [symmetry; exact E|exact Hseg].
  - rewrite ExactThreadSegment_guard_iff; apply IH.
  - rewrite ExactThreadSegment_guard_iff; apply IH.
  - symmetry; apply IH.
  - transitivity (ExactThreadSegment u sigma xs residual sigma'); [apply IH1|apply IH2].
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

(** An exact segment may end at a residual differing from its target only by
    finite leading guards and raw tree equivalence. *)
Definition exact_source_segment_to (t : thread sE) (sigma : SSig)
  (logs : list SObs) (target : thread sE) (sigma' : SSig) : Prop :=
  exists residual, ExactThreadSegment t sigma logs residual sigma' /\
    guard_equ residual target.

Lemma exact_source_equ t u sigma logs target sigma' :
  t ≅ u -> exact_source_segment_to u sigma logs target sigma' ->
  exact_source_segment_to t sigma logs target sigma'.
Proof.
  intros Htu (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply exact_segment_equ; [exact Htu|exact Hseg|reflexivity].
Qed.

Lemma exact_source_bind {A B} (p : CProg A) (next : A -> CProg B)
  (K : option B -> thread sE) sigma logs target sigma' :
  exact_source_segment_to (denote_flow p >>= fun flow =>
    match flow with None => K None | Some x => denote_flow (next x) >>= K end)
    sigma logs target sigma' ->
  exact_source_segment_to (denote_flow (CBind p next) >>= K) sigma logs target sigma'.
Proof.
  intro H; eapply exact_source_equ; [apply source_raw_bind|exact H].
Qed.

Lemma exact_source_ret {A} (x : A) (K : option A -> thread sE)
  sigma logs target sigma' :
  exact_source_segment_to (K (Some x)) sigma logs target sigma' ->
  exact_source_segment_to (denote_flow (CRet x) >>= K) sigma logs target sigma'.
Proof.
  intro H; eapply exact_source_equ; [apply source_raw_ret|exact H].
Qed.

Lemma exact_source_until {A} (body : CProg (option A))
  (K : option unit -> thread sE) sigma logs target sigma' :
  exact_source_segment_to (denote_flow body >>= until_tail body K)
    sigma logs target sigma' ->
  exact_source_segment_to (denote_flow (CUntilNone body) >>= K)
    sigma logs target sigma'.
Proof.
  intro H; eapply exact_source_equ; [apply source_raw_until|exact H].
Qed.

Lemma exact_source_read a v (K : option nat -> thread sE)
  h c logs target sigma' :
  h a = Some v ->
  exact_source_segment_to (K (Some v)) (h,c) logs target sigma' ->
  exact_source_segment_to (denote_flow (CRead a) >>= K) (h,c) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply exact_segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HRead a)))) (fun v => K (Some v))).
  - apply source_raw_read_head.
  - change (ExactThreadSegment (Vis (inr (inr (inl (HRead a)))) (fun v => K (Some v)))
      (h,c) ([] ++ logs) residual sigma').
    eapply exact_segment_user; [|exact Hseg].
    cbn [emit_list]; rewrite (sh_rd_some a h c v Hr); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_write a v (K : option unit -> thread sE)
  h c logs target sigma' :
  h a <> None ->
  exact_source_segment_to (K (Some tt)) (upd h a v,c) logs target sigma' ->
  exact_source_segment_to (denote_flow (CWrite a v) >>= K) (h,c) logs target sigma'.
Proof.
  intros Hp (residual & Hseg & Htail).
  destruct (h a) as [w|] eqn:Hw; [|contradiction].
  exists residual; split; [|exact Htail].
  eapply exact_segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HWrite a v)))) (fun _ => K (Some tt))).
  - apply source_raw_write_head.
  - change (ExactThreadSegment (Vis (inr (inr (inl (HWrite a v)))) (fun _ => K (Some tt)))
      (h,c) ([] ++ logs) residual sigma').
    eapply exact_segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite (sh_wr_some a h c v w Hw); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_emit tag block (K : option unit -> thread sE)
  h c logs target sigma' :
  exact_source_segment_to (K (Some tt)) (h,S c) logs target sigma' ->
  exact_source_segment_to (denote_flow (CEmit tag block) >>= K) (h,c)
    (SPop tag block c :: logs) target sigma'.
Proof.
  intros (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply exact_segment_equ with (u' := residual)
    (u := Vis (inr (inr (inr (Log (tag,block))))) (fun _ => K (Some tt))).
  - apply source_raw_emit_head.
  - change (ExactThreadSegment
      (Vis (inr (inr (inr (Log (tag,block))))) (fun _ => K (Some tt)))
      (h,c) ([SPop tag block c] ++ logs) residual sigma').
    eapply exact_segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite sh_emit; reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_cas_success a expected desired
  (K : option bool -> thread sE) h c logs target sigma' :
  h a = Some expected ->
  exact_source_segment_to (K (Some true)) (upd h a desired,c) logs target sigma' ->
  exact_source_segment_to (denote_flow (CCAS a expected desired) >>= K)
    (h,c) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply exact_segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b))).
  - apply source_raw_cas_head.
  - change (ExactThreadSegment
      (Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b)))
      (h,c) ([] ++ logs) residual sigma').
    eapply exact_segment_user; [|exact Hseg].
    cbn [emit_list]; rewrite (sh_cas_success a expected desired h c Hr); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_cas_failure a expected desired current
  (K : option bool -> thread sE) h c logs target sigma' :
  h a = Some current -> current <> expected ->
  exact_source_segment_to (K (Some false)) (h,c) logs target sigma' ->
  exact_source_segment_to (denote_flow (CCAS a expected desired) >>= K)
    (h,c) logs target sigma'.
Proof.
  intros Hr Hne (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply exact_segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b))).
  - apply source_raw_cas_head.
  - change (ExactThreadSegment
      (Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b)))
      (h,c) ([] ++ logs) residual sigma').
    eapply exact_segment_user; [|exact Hseg].
    cbn [emit_list]; rewrite (sh_cas_failure a expected desired current h c Hr Hne);
      reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_yield (K : option unit -> thread sE) sigma target :
  guard_equ (K (Some tt)) target ->
  exact_source_segment_to (denote_flow CYield >>= K) sigma [] target sigma.
Proof.
  intro Htail; exists (K (Some tt)); split; [|exact Htail].
  eapply exact_segment_equ with (u := Vis (inl Yield) (fun _ => K (Some tt))).
  - apply source_raw_yield_head.
  - apply exact_segment_yield.
  - reflexivity.
Qed.

(** Finite syntax normalization is used only for raw equ and leading guards.
    It never changes a scheduler focus or invokes pool sbisim congruence. *)
Ltac csl_raw_equ :=
  cbn beta iota zeta;
  first [reflexivity |
    lazymatch goal with
    | |- (denote_flow (CBind _ _) >>= _) ≅ _ =>
        etransitivity; [apply source_raw_bind|]; csl_raw_equ
    | |- (denote_flow (CRet _) >>= _) ≅ _ =>
        etransitivity; [apply source_raw_ret|]; csl_raw_equ
    | |- ((?t >>= ?k) >>= ?j) ≅ _ =>
        etransitivity; [apply bind_bind|]; csl_raw_equ
    | |- (Ret _ >>= _) ≅ _ =>
        etransitivity; [apply bind_ret_l|]; csl_raw_equ
    | |- _ ≅ (denote_flow (CBind _ _) >>= _) => symmetry; csl_raw_equ
    | |- _ ≅ (denote_flow (CRet _) >>= _) => symmetry; csl_raw_equ
    | |- _ ≅ ((_ >>= _) >>= _) => symmetry; csl_raw_equ
    | |- _ ≅ (Ret _ >>= _) => symmetry; csl_raw_equ
    | |- Guard _ ≅ Guard _ => apply guard_equ_node; csl_raw_equ
    end].

#[global] Instance source_guard_equ_proper :
  Proper (equ eq ==> equ eq ==> iff) guard_equ.
Proof.
  intros t t' Ht u u' Hu; split; intro H.
  - eapply guard_equ_trans; [apply guard_equ_equ; symmetry; exact Ht|].
    eapply guard_equ_trans; [exact H|apply guard_equ_equ; exact Hu].
  - eapply guard_equ_trans; [apply guard_equ_equ; exact Ht|].
    eapply guard_equ_trans; [exact H|apply guard_equ_equ; symmetry; exact Hu].
Qed.

Lemma exact_rr_user_replaced n (ts : pool sE (S n)) (i : Fin.t (S n))
  (e : sE) (k : encode e -> thread sE) m sigma :
  interp_schedule_rr sh (S n)
    (ts @ i := (@go CEff _ unit (VisF (inr (inr e) : CEff) k))) (Some i) m sigma ≅
  (runStateT (sh e) sigma >>= fun '(x,sigma') =>
    rr_guards 3 (interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma')).
Proof.
  etransitivity.
  - eapply segment_rr_user_exact; rewrite Vector.nth_replace_eq; reflexivity.
  - apply equ_clo_bind with (S := eq); [reflexivity|].
    intros [x sigma'] y <-; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma exact_segment_rr_prefix n (ts : pool sE (S n)) (i : Fin.t (S n))
  t m sigma logs residual sigma' :
  ExactThreadSegment t sigma logs residual sigma' ->
  exists word, rr_prefix_events word = logs /\
  interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma ≅
    rr_prefix word (Guard
      (interp_schedule_rr sh (S n) (ts @ i := residual) None m sigma')).
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
      set (resume := fun response : (encode e * SSig)%type =>
        let '(x,sigma0) := response in
        rr_guards 3 (interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma0)).
      transitivity (emit_list before (Ret (result,sigma1)) >>= resume).
      * apply equ_clo_bind with (S := eq); [exact Eh|intros x y <-; reflexivity].
      * etransitivity; [apply emit_list_ret_bind|]; unfold resume.
        transitivity (emit_list before
          (rr_guards 3 (rr_prefix word (Guard
            (interp_schedule_rr sh (S n) (ts @ i := residual) None m sigma'))))).
        -- apply emit_list_equ, rr_guards_equ; exact Et.
        -- rewrite rr_prefix_app; cbn [rr_prefix rr_guards].
           symmetry; apply rr_prefix_emit.
  - destruct (IH n ts i m) as (word & Ew & Et).
    exists word; split; [exact Ew|].
    etransitivity.
    + apply interp_schedule_rr_equ, replace_pool_equ; [apply pool_equ_refl|exact Etu].
    + etransitivity; [exact Et|].
      apply rr_prefix_equ, guard_equ_node, interp_schedule_rr_equ, replace_pool_equ;
        [apply pool_equ_refl|exact Eout].
Qed.

Theorem source_segment_scheduler_steps {n} (ts : pool sE (S n)) sigma i logs residual sigma' ts' :
  ThreadSegment (ts $ i) sigma logs residual sigma' ->
  pool_equ ts' (ts @ i := residual) ->
  exists next,
    finite_steps (interp_nd (S n) ts None sigma)
      (tau :: List.map (fun o => obs (Log o) tt) logs) next /\
    next ~ interp_nd (S n) ts' None sigma'.
Proof.
  intros Hseg Epool.
  assert (Efocused : interp_nd (S n) ts (Some i) sigma ~
    emit_list logs (interp_nd (S n) ts' None sigma')).
  {
    transitivity (interp_nd (S n) (ts @ i := (ts $ i)) (Some i) sigma).
    - rewrite (interp_nd_equ (S n) _ _ (Some i) sigma (source_replace_current (S n) ts i));
        reflexivity.
    - transitivity (emit_list logs (interp_nd (S n) (ts @ i := residual) None sigma')).
      + eapply segment_interp_nd; exact Hseg.
      + apply emit_list_sbisim.
        rewrite <- (interp_nd_equ (S n) _ _ None sigma' Epool); reflexivity.
  }
  assert (Hbranch : trans tau (Br n (fun j => interp_nd (S n) ts (Some j) sigma))
    (interp_nd (S n) ts (Some i) sigma)).
  { eapply trans_br with (x := i); reflexivity. }
  pose proof (interp_nd_select n ts sigma) as Eselect; symmetry in Eselect.
  destruct (sbisim_trans _ _ _ tau eq Eselect Hbranch)
    as (l & focused & Hchoose & El & Efocus); subst l.
  assert (Eemit : emit_list logs (interp_nd (S n) ts' None sigma') ~ focused).
  { transitivity (interp_nd (S n) ts (Some i) sigma); [symmetry; exact Efocused|exact Efocus]. }
  destruct (finite_steps_sbisim _ _ _
    (finite_steps_emit_list logs (interp_nd (S n) ts' None sigma')) focused Eemit)
    as (next & Hlogs & Enext).
  exists next; split; [econstructor; eassumption|symmetry; exact Enext].
Qed.
