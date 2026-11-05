(** * The policy-scheduled, instrumented runner.

    [schedule_with sch] is the event-only pool scheduler: it never inspects a
    thread's [Br] nodes, interprets [Yield]/[Fork] itself, and leaves a
    [Scheduled i] event at every scheduling decision.  Here the decision is
    logged as [Log (inr i)] next to the program's own observations
    ([Log (inl _)]), so the interpreted runner has observation type [W + nat].
    Round robin is the [rr_scheduler] instance ([RoundRobin.v]); fairness
    certificates live in [Fair.v]. *)

From Stdlib Require Import Fin Vector Morphisms Program.Equality.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Events.Writer
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.State.Mod
  CTree.Trace
  Utils.Vectors.

Import CTreeNotations CoindNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

Generalizable All Variables.

(** * Handlers and the instrumented runner *)

Definition relabel_log {W} : writerE W ~> writerE (W + nat) :=
  fun _ e => match e in writerE _ X return writerE (W + nat) X with
             | Log w => Log (inl w) end.

Definition sched_handler {W Σ} : schedE ~> stateT Σ (ctreeW (W + nat) Bn) :=
  fun _ e σ => match e in schedE X return ctreeW (W + nat) Bn (Σ * X) with
               | Scheduled i => Vis (Log (inr i)) (fun _ => Ret (σ, tt)) end.

Definition policy_handler {E W Σ} (h : E ~> stateT Σ (ctreeW W Bn))
  : (schedE +' E) ~> stateT Σ (ctreeW (W + nat) Bn) :=
  h_sum sched_handler (fun _ e σ => translate relabel_log (h _ e σ)).

Definition interp_schedule_fair {E W Σ} (sch : Scheduler) (h : E ~> stateT Σ (ctreeW W Bn))
    (n : nat) (ts : pool E Bn n) (focus : option (Fin.t n)) (st : sched_state sch) (σ : Σ)
    : ctreeW (W + nat) Bn (Σ * unit) :=
  interp_state (policy_handler h) (schedule_with sch n ts focus st) σ.

(** Program observations only: scheduling logs never satisfy [fair_obs P]. *)
Definition fair_obs {W} (P : W -> Prop) (o : W + nat) : Prop :=
  match o with inl w => P w | inr _ => False end.

(** * [translate] helpers *)

Lemma translate_stuck_node {E F B : Type -> Type} {X : Type} (f : E ~> F) :
  translate f (Stuck : ctree E B X) ≅ Stuck.
Proof. rewrite unfold_translate; reflexivity. Qed.

Lemma translate_bind {E F B : Type -> Type} {X Y : Type} (f : E ~> F)
    (t : ctree E B X) (k : X -> ctree E B Y) :
  translate f (t >>= k) ≅ (translate f t >>= fun x => translate f (k x)).
Proof.
  revert t; __coinduction_equ R IH; intro t.
  rewrite (ctree_eta t); destruct (observe t) as [x| |u|u|Z e kk|Z c kk].
  - rewrite bind_ret_l, translate_ret, bind_ret_l; reflexivity.
  - rewrite (bind_stuck k), !translate_stuck_node, (bind_stuck (fun x => translate f (k x))); reflexivity.
  - rewrite bind_step, !translate_step, bind_step; constructor; apply IH.
  - rewrite bind_guard, !translate_guard, bind_guard; constructor; apply IH.
  - rewrite bind_vis, !translate_vis, bind_vis; constructor; intro z; apply IH.
  - rewrite bind_br, !translate_br, bind_br; constructor; intro z; apply IH.
Qed.

Lemma translate_emit_list {W : Type} {X : Type} (os : list W) (t : ctreeW W Bn X) :
  translate relabel_log (emit_list os t) ≅ emit_list (List.map inl os) (translate relabel_log t).
Proof.
  induction os as [|o os IH]; [reflexivity|].
  cbn [List.map]; rewrite !emit_list_cons, translate_vis; cbn [relabel_log].
  apply vis_equ_node; intros _; exact IH.
Qed.

Lemma translate_log_bind {W : Type} {X : Type} (o : W) (t : ctreeW W Bn X) :
  translate relabel_log (log o;; t) ≅ (log (inl o);; translate relabel_log t).
Proof.
  unfold log; rewrite !bind_trigger, translate_vis; cbn [relabel_log].
  apply vis_equ_node; intros []; reflexivity.
Qed.

Lemma translate_guards {E F B : Type -> Type} {X : Type} (f : E ~> F) k (t : ctree E B X) :
  translate f (guards k t) ≅ guards k (translate f t).
Proof.
  induction k as [|k IH]; cbn [guards]; [reflexivity|].
  rewrite translate_guard; apply guard_equ_node; exact IH.
Qed.

(** A relabelled trigger interpretation is the relabelled handler response up
    to the trigger's administrative guard. *)
Lemma translate_interp_state_trigger_bind {E W Σ} (h : E ~> stateT Σ (ctreeW W Bn))
    {X Y} (e : E Y) (k : Σ * Y -> ctreeW (W + nat) Bn X) (σ : Σ) :
  (translate relabel_log (interp_state h (CTree.trigger e : ctree E Bn Y) σ) >>= k) ~
  (translate relabel_log (h _ e σ) >>= k).
Proof.
  rewrite interp_state_trigger.
  change (Monad.bind ?a ?b) with (CTree.bind a b).
  rewrite translate_bind, bind_bind.
  __upto_bind_sbisim_eq; intro x.
  rewrite translate_guard, translate_ret, bind_guard, sb_guard, bind_ret_l; reflexivity.
Qed.

(** [translate] preserves strong bisimulation: transitions are translated
    along [f] in both directions. *)
Section TranslateSBisim.
  Context {E F B : Type -> Type} {X : Type} (f : E ~> F).

  Definition translate_label (l : @label E) : @label F :=
    match l with
    | τ => τ
    | obs e x => obs (f _ e) x
    | val x => val x
    end.

  Lemma trans_translate_ l T U :
    trans_ l T U ->
    forall (t t' : ctree E B X), T = observe t -> U = observe t' ->
    trans (translate_label l) (translate f t) (translate f t').
  Proof.
    intro TR; induction TR as [Y c x k l u TR IH|u v l TR IH|u v Hv|Y e k x u Hu|r];
      intros t0 t0' HT HU.
    - rewrite (unfold_translate t0), <- HT; cbn.
      eapply trans_br; [apply (IH (k x) t0' eq_refl HU)|reflexivity].
    - rewrite (unfold_translate t0), <- HT; cbn.
      apply trans_guard, (IH u t0' eq_refl HU).
    - rewrite (unfold_translate t0), <- HT; cbn.
      rewrite <- (observe_eq_equ v t0' HU), Hv.
      apply trans_step.
    - rewrite (unfold_translate t0), <- HT; cbn.
      rewrite <- (observe_eq_equ u t0' HU), <- Hu.
      apply (trans_vis (f _ e) x (fun x => translate f (k x))).
    - rewrite (unfold_translate t0), <- HT; cbn.
      rewrite <- (observe_eq_equ Stuck t0' HU), translate_stuck_node.
      apply trans_ret.
  Qed.

  Lemma trans_translate l (t t' : ctree E B X) :
    trans l t t' -> trans (translate_label l) (translate f t) (translate f t').
  Proof. intro TR; exact (trans_translate_ l _ _ TR t t' eq_refl eq_refl). Qed.

  Lemma trans_translate_inv_ l' T U' :
    trans_ l' T U' ->
    forall (t : ctree E B X) u', go T ≅ translate f t -> go U' ≅ u' ->
    exists l t', l' = translate_label l /\ trans l t t' /\ u' ≅ translate f t'.
  Proof.
    intro TR; induction TR as [Y c x k l u TR IH|u v l TR IH|u v Hv|Y e k x u Hu|r];
      intros t0 u0 HT HU; rewrite (unfold_translate t0) in HT;
      destruct (observe t0) as [r0| |t1|t1|Y0 e0 k0|Y0 c0 k0] eqn:Ht0;
      try (step in HT; cbn in HT; inversion HT; fail).
    - pose proof (equ_br_invT _ _ _ _ HT) as HY; subst Y0.
      pose proof (equ_br_invE _ _ _ _ HT) as [Hc Hk]; subst c0.
      destruct (IH (k0 x) u0 ltac:(rewrite <- ctree_eta; apply Hk) HU) as (l0 & t' & -> & TR0 & Eu).
      exists l0, t'; split; [reflexivity|]; split; [|exact Eu].
      rewrite (ctree_eta t0), Ht0; eapply trans_br; [exact TR0|reflexivity].
    - apply equ_guard_inv in HT.
      destruct (IH t1 u0 ltac:(rewrite <- ctree_eta; exact HT) HU) as (l0 & t' & -> & TR0 & Eu).
      exists l0, t'; split; [reflexivity|]; split; [|exact Eu].
      rewrite (ctree_eta t0), Ht0; apply trans_guard; exact TR0.
    - apply equ_step_inv in HT.
      exists τ, t1; split; [reflexivity|]; split; [rewrite (ctree_eta t0), Ht0; apply trans_step|].
      rewrite <- HU, <- ctree_eta, Hv, HT; reflexivity.
    - pose proof (equ_vis_invT _ _ _ _ HT) as HY; subst Y0.
      pose proof (equ_vis_invE _ _ _ _ HT) as [He Hk]; subst e.
      exists (obs e0 x), (k0 x); split; [reflexivity|]; split; [rewrite (ctree_eta t0), Ht0; apply trans_vis|].
      rewrite <- HU, <- ctree_eta, <- Hu, Hk; reflexivity.
    - apply equ_ret_inv in HT; subst r0.
      exists (val r), Stuck; split; [reflexivity|]; split; [rewrite (ctree_eta t0), Ht0; apply trans_ret|].
      rewrite <- HU, translate_stuck_node; reflexivity.
  Qed.

  Lemma trans_translate_inv l' (t : ctree E B X) u' :
    trans l' (translate f t) u' ->
    exists l t', l' = translate_label l /\ trans l t t' /\ u' ≅ translate f t'.
  Proof. intro TR; apply (trans_translate_inv_ l' _ _ TR t u'); symmetry; apply ctree_eta. Qed.

  #[global] Instance translate_sbisim : Proper (sbisim eq ==> sbisim eq) (@translate E F B f X).
  Proof.
    unfold Proper, respectful; coinduction R IH.
    intros t u Htu; split; intros l' next TR.
    - apply trans_translate_inv in TR as (l & t' & -> & TRt & Enext).
      step in Htu; destruct Htu as [Hf _].
      destruct (Hf l t' TRt) as (l2 & u' & TRu & Htu' & <-).
      exists (translate_label l), (translate f u'); split; [apply trans_translate; exact TRu|].
      split; [rewrite Enext; apply IH; exact Htu'|reflexivity].
    - apply trans_translate_inv in TR as (l & u' & -> & TRu & Enext).
      step in Htu; destruct Htu as [_ Hb].
      destruct (Hb l u' TRu) as (l2 & t' & TRt & Htu' & ->).
      exists (translate_label l), (translate f t'); split; [apply trans_translate; exact TRt|].
      split; [rewrite Enext; apply IH; exact Htu'|reflexivity].
  Qed.
End TranslateSBisim.

(** * Structural equations of the instrumented runner *)
Section FairInterpretation.
  Context {E : Type -> Type} {W Σ : Type} (sch : Scheduler)
    (h : E ~> stateT Σ (ctreeW W Bn)).

  #[local] Abbreviation fair := (interp_schedule_fair sch h).

  Lemma interp_schedule_fair_equ n (ts ts' : pool E Bn n) focus st σ :
    pool_equ ts ts' ->
    fair n ts focus st σ ≅ fair n ts' focus st σ.
  Proof.
    intro Hts; unfold interp_schedule_fair.
    now rewrite (schedule_with_pool_proper sch n ts ts' focus st Hts).
  Qed.

  Lemma interp_schedule_fair_empty (ts : pool E Bn 0) st σ :
    fair 0 ts None st σ ~ (Ret (σ,tt) : ctreeW (W + nat) Bn (Σ * unit)).
  Proof.
    unfold interp_schedule_fair.
    rewrite (observe_equ_go _ _ (schedule_with_empty_none sch ts st)), interp_state_ret.
    reflexivity.
  Qed.

  (** ** Exact ([≅]) node equations *)

  Lemma interp_schedule_fair_ret_exact n (ts : pool E Bn (S n)) (i : Fin.t (S n)) st σ :
    observe (ts $ i) = RetF tt ->
    fair (S n) ts (Some i) st σ ≅ Guard (fair n (ts -- i) None st σ).
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    rewrite (observe_equ_go _ _ (schedule_with_focused_ret sch n ts i st Hobs)).
    apply interp_state_guard.
  Qed.

  Lemma interp_schedule_fair_guard_exact n (ts : pool E Bn (S n)) (i : Fin.t (S n)) t st σ :
    observe (ts $ i) = GuardF t ->
    fair (S n) ts (Some i) st σ ≅ Guard (fair (S n) (ts @ i := t) (Some i) st σ).
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    rewrite (observe_equ_go _ _ (schedule_with_focused_guard sch n ts i t st Hobs)).
    apply interp_state_guard.
  Qed.

  Lemma interp_schedule_fair_step_exact n (ts : pool E Bn (S n)) (i : Fin.t (S n)) t st σ :
    observe (ts $ i) = StepF t ->
    fair (S n) ts (Some i) st σ ≅ Step (Guard (fair (S n) (ts @ i := t) (Some i) st σ)).
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    rewrite (observe_equ_go _ _ (schedule_with_focused_step sch n ts i t st Hobs)).
    apply interp_state_step.
  Qed.

  (** The event-only property: a thread-internal branch is kept as is. *)
  Lemma interp_schedule_fair_br n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    {Y} (c : Bn Y) k st σ :
    observe (ts $ i) = BrF c k ->
    fair (S n) ts (Some i) st σ ≅
    Br c (fun j => Guard (fair (S n) (ts @ i := k j) (Some i) st σ)).
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    rewrite (observe_equ_go _ _ (schedule_with_focused_br sch n ts i c k st Hobs)).
    apply interp_state_br_node.
  Qed.

  Lemma interp_schedule_fair_yield_exact n (ts : pool E Bn (S n)) (i : Fin.t (S n)) k st σ :
    observe (ts $ i) = VisF (inl1 Yield) k ->
    fair (S n) ts (Some i) st σ ≅ Guard (fair (S n) (ts @ i := k tt) None st σ).
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    rewrite (observe_equ_go _ _ (schedule_with_focused_yield sch n ts i k st Hobs)).
    apply interp_state_guard.
  Qed.

  Lemma interp_schedule_fair_fork_exact n (ts : pool E Bn (S n)) (i : Fin.t (S n)) k st σ :
    observe (ts $ i) = VisF (inr1 (inl1 Fork)) k ->
    fair (S n) ts (Some i) st σ ≅
    Guard (fair (S (S n)) (k true :: (ts @ i := k false)) (Some (Fin.FS i)) st σ).
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    rewrite (observe_equ_go _ _ (schedule_with_focused_fork sch n ts i k st Hobs)).
    apply interp_state_guard.
  Qed.

  Lemma interp_schedule_fair_user_exact n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    {Y} (e : E Y) k st σ :
    observe (ts $ i) = VisF (inr1 (inr1 e)) k ->
    fair (S n) ts (Some i) st σ ≅
    (translate relabel_log (h _ e σ) >>= fun '(σ',x) =>
       Guard (fair (S n) (ts @ i := k x) (Some i) st σ')).
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    rewrite (observe_equ_go _ _ (schedule_with_focused_user_event sch n ts i e k st Hobs)).
    rewrite interp_state_vis; cbn [policy_handler h_sum].
    upto_bind_eq; intros [σ' x]; reflexivity.
  Qed.

  Lemma interp_schedule_fair_stuck n (ts : pool E Bn (S n)) (i : Fin.t (S n)) st σ :
    (ts $ i) ≅ Stuck ->
    fair (S n) ts (Some i) st σ ≅ Stuck.
  Proof.
    intro Hstuck.
    rewrite (interp_schedule_fair_equ (S n) ts (ts @ i := Stuck) (Some i) st σ)
      by (intro j; destruct (Fin.eq_dec j i) as [->|Hne];
          [rewrite Vector.nth_replace_eq; exact Hstuck
          |rewrite Vector.nth_replace_neq by congruence; reflexivity]).
    unfold interp_schedule_fair.
    rewrite (observe_equ_go _ _ (schedule_with_focused_stuck sch n (ts @ i := Stuck) i st
      ltac:(rewrite Vector.nth_replace_eq; reflexivity))).
    apply interp_state_stuck.
  Qed.

  (** ** Node equations up to strong bisimulation *)

  Lemma interp_schedule_fair_ret n (ts : pool E Bn (S n)) (i : Fin.t (S n)) st σ :
    observe (ts $ i) = RetF tt ->
    fair (S n) ts (Some i) st σ ~ fair n (ts -- i) None st σ.
  Proof. intro Hobs; rewrite (interp_schedule_fair_ret_exact n ts i st σ Hobs), sb_guard; reflexivity. Qed.

  Lemma interp_schedule_fair_guard n (ts : pool E Bn (S n)) (i : Fin.t (S n)) t st σ :
    observe (ts $ i) = GuardF t ->
    fair (S n) ts (Some i) st σ ~ fair (S n) (ts @ i := t) (Some i) st σ.
  Proof. intro Hobs; rewrite (interp_schedule_fair_guard_exact n ts i t st σ Hobs), sb_guard; reflexivity. Qed.

  Lemma interp_schedule_fair_step n (ts : pool E Bn (S n)) (i : Fin.t (S n)) t st σ :
    observe (ts $ i) = StepF t ->
    fair (S n) ts (Some i) st σ ~ Step (fair (S n) (ts @ i := t) (Some i) st σ).
  Proof.
    intro Hobs; rewrite (interp_schedule_fair_step_exact n ts i t st σ Hobs).
    apply sb_step; rewrite sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_fair_yield n (ts : pool E Bn (S n)) (i : Fin.t (S n)) k st σ :
    observe (ts $ i) = VisF (inl1 Yield) k ->
    fair (S n) ts (Some i) st σ ~ fair (S n) (ts @ i := k tt) None st σ.
  Proof. intro Hobs; rewrite (interp_schedule_fair_yield_exact n ts i k st σ Hobs), sb_guard; reflexivity. Qed.

  Lemma interp_schedule_fair_fork n (ts : pool E Bn (S n)) (i : Fin.t (S n)) k st σ :
    observe (ts $ i) = VisF (inr1 (inl1 Fork)) k ->
    fair (S n) ts (Some i) st σ ~
    fair (S (S n)) (k true :: (ts @ i := k false)) (Some (Fin.FS i)) st σ.
  Proof. intro Hobs; rewrite (interp_schedule_fair_fork_exact n ts i k st σ Hobs), sb_guard; reflexivity. Qed.

  Lemma interp_schedule_fair_user n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    {Y} (e : E Y) k st σ :
    observe (ts $ i) = VisF (inr1 (inr1 e)) k ->
    fair (S n) ts (Some i) st σ ~
    (translate relabel_log (h _ e σ) >>= fun '(σ',x) =>
       fair (S n) (ts @ i := k x) (Some i) st σ').
  Proof.
    intro Hobs; rewrite (interp_schedule_fair_user_exact n ts i e k st σ Hobs).
    __upto_bind_sbisim_eq; intros [σ' x]; rewrite sb_guard; reflexivity.
  Qed.

  (** The scheduling point: the policy's alternatives, each logging its slot
      and continuing in the focused pool. *)
  Lemma interp_schedule_fair_select n (ts : pool E Bn (S n)) st σ :
    fair (S n) ts None st σ ~
    br_alts (sched_arity sch n st) (fun a =>
      Vis (Log (inr (slot_index (fst (sched_pick sch n st a)))))
        (fun _ => fair (S n) ts (Some (fst (sched_pick sch n st a))) (snd (sched_pick sch n st a)) σ)).
  Proof.
    unfold interp_schedule_fair at 1.
    rewrite (schedule_with_no_focus_nonempty sch n ts st), interp_state_br_alts_sb.
    apply br_alts_sbisim; intro a.
    rewrite interp_state_vis; cbn [policy_handler h_sum sched_handler].
    change (Monad.bind ?a ?b) with (CTree.bind a b); rewrite bind_vis.
    apply sb_vis; intros _.
    rewrite bind_ret_l; cbn [fst snd]; rewrite sb_guard; reflexivity.
  Qed.

  (** Keep one scheduler continuation fixed while interpreting a raw user
      event; stated on the handler itself so client handler equations
      ([≅]) apply under [translate] directly. *)
  Lemma interp_schedule_fair_user_bind n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    (t : thread E Bn) {Y} (e : E Y) (k : Y -> thread E Bn) st σ :
    t ≅ Vis (inr1 (inr1 e)) k ->
    fair (S n) (ts @ i := t) (Some i) st σ ~
    (translate relabel_log (h _ e σ) >>=
      fun '(σ',x) => fair (S n) (ts @ i := k x) (Some i) st σ').
  Proof.
    intro Hnode.
    rewrite (interp_schedule_fair_equ (S n)
      (ts @ i := t) (ts @ i := Vis (inr1 (inr1 e)) k) (Some i) st σ
      (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)).
    erewrite interp_schedule_fair_user with (e:=e) (k:=k)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    __upto_bind_sbisim_eq; intros [σ' x].
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  Lemma interp_schedule_fair_guard_equ n (ts us : pool E Bn n) focus st σ :
    pool_guard_equ ts us ->
    fair n ts focus st σ ~ fair n us focus st σ.
  Proof.
    intro H'; unfold interp_schedule_fair.
    apply galigned_sbisim, interp_state_galigned, schedule_with_galigned, H'.
  Qed.

  (** ** Focused-slot congruence *)

  Lemma segment_fair_replace_equ n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    t u focus st σ :
    t ≅ u ->
    fair (S n) (ts @ i := t) focus st σ ~ fair (S n) (ts @ i := u) focus st σ.
  Proof.
    intro Eq.
    rewrite (interp_schedule_fair_equ (S n) (ts @ i := t) (ts @ i := u)
      focus st σ (replace_pool_equ ts ts i t u (pool_equ_refl ts) Eq)); reflexivity.
  Qed.

  Lemma segment_fair_focused_guard n (ts : pool E Bn (S n)) (i : Fin.t (S n)) t st σ :
    fair (S n) (ts @ i := Guard t) (Some i) st σ ~ fair (S n) (ts @ i := t) (Some i) st σ.
  Proof.
    erewrite interp_schedule_fair_guard by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.
End FairInterpretation.

(** A standalone thread interpreted through the policy handler is the
    relabelled plain interpretation: the policy handler only relabels
    user-event responses. *)
Lemma interp_state_policy_translate {E W Σ} (h : E ~> stateT Σ (ctreeW W Bn)) {X} :
  forall (u : ctree E Bn X) σ,
    interp_state (policy_handler h) (translate inr1 u) σ ≅
    translate relabel_log (interp_state h u σ).
Proof.
  __coinduction_equ R IH; intros u σ.
  rewrite (ctree_eta u); destruct (observe u) as [x| |t|t|Y e k|Y c k].
  - rewrite translate_ret, !interp_state_ret, translate_ret; reflexivity.
  - rewrite translate_stuck_node, !interp_state_stuck, translate_stuck_node; reflexivity.
  - rewrite translate_step, !interp_state_step, translate_step, translate_guard.
    constructor; step; constructor; apply IH.
  - rewrite translate_guard, !interp_state_guard, translate_guard.
    constructor; apply IH.
  - rewrite translate_vis, !interp_state_vis; cbn [policy_handler h_sum].
    change (Monad.bind ?a ?b) with (CTree.bind a b); rewrite translate_bind.
    upto_bind_eq; intros [σ' x]; cbn [fst snd].
    rewrite translate_guard; constructor; apply IH.
  - rewrite translate_br, !interp_state_br.
    change (Monad.bind (mbr ?c) ?f) with (CTree.bind (branch c : ctree (writerE _) Bn _) f).
    rewrite !bind_branch, translate_br.
    constructor; intro y.
    rewrite translate_guard; step; constructor; apply IH.
Qed.
