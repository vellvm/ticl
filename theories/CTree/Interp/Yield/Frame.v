From Stdlib Require Import Fin Vector.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Interp.Refine
  CTree.Interp.Yield.Policy
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.State.Mod
  CTree.Logic.Sim
  Utils.Vectors.

Import CTreeNotations VectorNotations CoindNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** Lift an event predicate through a left summand; scheduler events are always admitted. *)
Definition okE_lift {F E} (okE : forall Y, E Y -> Prop) : forall Y, (F +' E) Y -> Prop :=
  fun Y e => match e with inr1 e => okE Y e | inl1 _ => True end.
(** Source thread signatures nest two event lifts. *)
Definition okE_thread {F G E} (okE : forall Y, E Y -> Prop) : forall Y, (F +' (G +' E)) Y -> Prop :=
  okE_lift (okE_lift okE).

(** Raw policies preserve left-injected source events and admit selections. *)
Definition okE_policy {E} (okE : forall Y, E Y -> Prop)
  : forall Y, (E +' schedE) Y -> Prop :=
  fun Y e => match e with inl1 e => okE Y e | inr1 _ => True end.

Section InterpFramable.
  Universe r.
  Context {E F B: Type -> Type} (h: E ~> ctree@{_ _ _ _ r _} F B).

(** Interpretation preserves finite guarded-step prefixes. *)
Lemma guards_to_step_interp {X} (t: ctree E B X) :
  guards_to_step t -> guards_to_step (interp (M := ctree F B) h t).
Proof.
  induction 1.
  - eapply guards_to_step_equ; [symmetry; apply unfold_interp|].
    eapply GtsStep; cbn; now rewrite H.
  - eapply guards_to_step_equ; [symmetry; apply unfold_interp|].
    eapply GtsGuard; [cbn; now rewrite H|exact IHguards_to_step].
Qed.

(** Framability survives interpretation with framable handler responses; the [ctree@{_ _ _ _ r _}] universe annotation is required (see [Yield/Mod.v]). *)
Lemma framable_interp {X}
  (okE: forall Y, E Y -> Prop) (okF: forall Y, F Y -> Prop) :
  (forall Y e, okE Y e -> Framable okF (h Y e)) ->
  forall t: ctree E B X, Framable okE t -> Framable okF (interp (M := ctree F B) h t).
Proof.
  intro Hh; unfold Framable at 2; coinduction R IH; intros t Ht.
  apply framable_unfold in Ht.
  rewrite unfold_interp; cbn; destruct Ht; cbn.
  - constructor.
  - constructor.
  - constructor; apply (b_chain R); cbn; constructor; apply IH, H.
  - constructor; apply IH, H.
  - apply (framable_bind_chain okF (R := chain_b R)); [now apply Hh|].
    intro x; cbn; constructor; apply IH, H0.
  - constructor; intro y;
      change (CTree.subst ?f (Ret y)) with (CTree.bind (Ret y) f).
    + eapply guards_to_step_equ; [symmetry; apply bind_ret_l|].
      apply guards_to_step_guard, guards_to_step_interp, H.
    + rewrite bind_ret_l; apply (b_chain R); cbn; constructor; apply IH, H0.
Qed.
End InterpFramable.


(** Handler responses are [Ret] or a trigger; proved by a tactic rather than
    lemmas so each use elaborates at the universes of the erasure it refines. *)
Ltac framable_handler :=
  let e := fresh "e" in let H := fresh "H" in
  intros ? e H; repeat (destruct e as [e|e]); try destruct e; cbn in *;
  first [apply fr_ret
        | unfold CTree.trigger; apply fr_vis; [first [exact I|exact H]|intro; apply fr_ret]].

(** Erasing thread yield/fork events preserves framability. *)
Lemma framable_thread {E B X} (okE: forall Y, E Y -> Prop)
  (t: ctree (yieldE +' (forkE +' E)) B X) :
  Framable (okE_thread okE) t -> Framable okE (interp_thread t).
Proof.
  intro H; unfold interp_thread, interp_yield.
  apply (framable_interp _ (okE_lift okE)); [framable_handler|].
  apply (framable_interp _ (okE_thread okE)); [framable_handler|exact H].
Qed.

Section PoolFramable.
  Context {E B: Type -> Type} `{Bn -< B} (okE: forall Y, E Y -> Prop).

  (** Every thread in the pool is framable. *)
  Definition pool_framable {n} (v: pool E B n) : Prop :=
    forall i, Framable (okE_thread okE) (v $ i).

  (** Replacing a slot with a framable thread preserves pool framability. *)
  Lemma pool_framable_replace {n} (v: pool E B n) (i: Fin.t n) (t: thread E B) :
    pool_framable v -> Framable (okE_thread okE) t -> pool_framable (v @ i := t).
  Proof.
    intros Hv Ht.
    exact (vector_replace_pointwise (fun a _ : thread E B => Framable (okE_thread okE) a)
      v v i t t (fun j _ => Hv j) Ht).
  Qed.

  (** Removing a slot preserves pool framability. *)
  Lemma pool_framable_remove {n} (v: pool E B (S n)) (i: Fin.t (S n)) :
    pool_framable v -> pool_framable (v -- i).
  Proof.
    intros Hv.
    exact (vector_remove_pointwise (fun a _ : thread E B => Framable (okE_thread okE) a)
      v v i (fun j _ => Hv j)).
  Qed.

  (** Prepending a framable thread preserves pool framability. *)
  Lemma pool_framable_cons {n} (t: thread E B) (v: pool E B n) :
    Framable (okE_thread okE) t -> pool_framable v -> pool_framable ((t :: v)%vector).
  Proof.
    exact (vector_cons_pointwise (fun a _ : thread E B => Framable (okE_thread okE) a) t t v v).
  Qed.

  (** Every policy preserves framability after projecting selections to steps. *)
  Lemma framable_schedule (sch : Scheduler) :
    forall n (ts: pool E B n) focus (st : sched_state sch),
    pool_branchfree ts -> pool_framable ts ->
    Framable okE (project_scheduled (schedule_policy sch n ts focus st)).
  Proof.
    unfold Framable; coinduction R IH; intros n ts focus st Hbf Hfr.
    destruct focus as [i|].
    - destruct n as [|n]; [inversion i|].
      pose proof (Hbf i) as Hi; apply branchfree_unfold in Hi.
      pose proof (Hfr i) as Hfi; apply framable_unfold in Hfi.
      destruct (observe (ts $ i)) eqn:Hobs.
      + destruct r.
        rewrite (observe_equ_go _ _ (schedule_policy_focused_ret sch n ts i st Hobs)),
          project_scheduled_guard; constructor.
        apply IH; auto using pool_branchfree_remove, pool_framable_remove.
      + rewrite (observe_equ_go _ _ (schedule_policy_focused_stuck sch n ts i st Hobs)),
          project_scheduled_stuck; constructor.
      + rewrite (observe_equ_go _ _ (schedule_policy_focused_step sch n ts i t st Hobs)),
          project_scheduled_step; constructor.
        apply (b_chain R); cbn; constructor.
        inversion Hi; inversion Hfi; subst.
        apply IH; auto using pool_branchfree_replace, pool_framable_replace.
      + rewrite (observe_equ_go _ _ (schedule_policy_focused_guard sch n ts i t st Hobs)),
          project_scheduled_guard; constructor.
        inversion Hi; inversion Hfi; subst.
        apply IH; auto using pool_branchfree_replace, pool_framable_replace.
      + ddestruction Hi; ddestruction Hfi.
        destruct e as [y|[f|e]]; [destruct y|destruct f|].
        * rewrite (observe_equ_go _ _ (schedule_policy_focused_yield sch n ts i k st Hobs)),
            project_scheduled_guard; constructor.
          apply IH; auto using pool_branchfree_replace, pool_framable_replace.
        * rewrite (observe_equ_go _ _ (schedule_policy_focused_fork sch n ts i k st Hobs)),
            project_scheduled_guard; constructor.
          apply IH; auto using pool_branchfree_replace, pool_branchfree_cons,
            pool_framable_replace, pool_framable_cons.
        * rewrite (observe_equ_go _ _ (schedule_policy_focused_user_event sch n ts i e k st Hobs)),
            project_scheduled_user.
          constructor; [exact H1|].
          intro x; apply (b_chain R); cbn; constructor.
          apply IH; auto using pool_branchfree_replace, pool_framable_replace.
      + inversion Hi.
    - destruct n as [|n].
      + rewrite (observe_equ_go _ _ (schedule_policy_empty_none sch ts st)),
          project_scheduled_ret; constructor.
      + rewrite unfold_schedule_policy; cbn beta iota zeta.
        generalize (sched_pick sch n st); destruct (sched_arity sch n st) as [|a]; intro pick.
        * destruct (pick Fin.F1) as [j st']; rewrite project_scheduled_scheduled; constructor.
          apply (b_chain R); cbn; constructor; apply IH; assumption.
        * rewrite project_scheduled_br; constructor.
          -- intro x; destruct (pick x) as [j st']; apply guards_to_step_guard.
             eapply guards_to_step_equ; [symmetry; apply project_scheduled_scheduled|].
             eapply GtsStep; reflexivity.
          -- intro x; destruct (pick x) as [j st'].
             apply (b_chain R); cbn; constructor.
             rewrite project_scheduled_scheduled; apply (b_chain R); cbn; constructor.
             apply (b_chain R); cbn; constructor; apply IH; assumption.
  Qed.
End PoolFramable.

(** Deterministic RR adds admissible selections and preserves source nodes. *)
Lemma framable_schedule_rr {E} (okE : forall Y, E Y -> Prop) :
  forall n (ts : pool E Bn n) focus cursor,
    pool_branchfree ts -> pool_framable okE ts ->
    Framable (okE_policy okE) (schedule_policy rr_scheduler n ts focus cursor).
Proof.
  unfold Framable; coinduction R IH; intros n ts focus cursor Hbf Hfr.
  change (framableF (okE_policy okE) `R
    (observe (schedule_policy rr_scheduler n ts focus cursor))).
  destruct focus as [i|].
  - destruct n as [|n]; [inversion i|].
    pose proof (Hbf i) as Hi; apply branchfree_unfold in Hi.
    pose proof (Hfr i) as Hfi; apply framable_unfold in Hfi.
    destruct (observe (ts $ i)) eqn:Hobs.
    + destruct r.
      rewrite (schedule_policy_focused_ret rr_scheduler n ts i cursor Hobs); constructor.
      apply IH; auto using pool_branchfree_remove, pool_framable_remove.
    + rewrite (schedule_policy_focused_stuck rr_scheduler n ts i cursor Hobs); constructor.
    + rewrite (schedule_policy_focused_step rr_scheduler n ts i t cursor Hobs); constructor.
      inversion Hi; inversion Hfi; subst.
      apply IH; auto using pool_branchfree_replace, pool_framable_replace.
    + rewrite (schedule_policy_focused_guard rr_scheduler n ts i t cursor Hobs); constructor.
      inversion Hi; inversion Hfi; subst.
      apply IH; auto using pool_branchfree_replace, pool_framable_replace.
    + ddestruction Hi; ddestruction Hfi.
      destruct e as [y|[f|e]]; [destruct y|destruct f|].
      * rewrite (schedule_policy_focused_yield rr_scheduler n ts i k cursor Hobs); constructor.
        apply IH; auto using pool_branchfree_replace, pool_framable_replace.
      * rewrite (schedule_policy_focused_fork rr_scheduler n ts i k cursor Hobs); constructor.
        apply IH; auto using pool_branchfree_replace, pool_branchfree_cons,
          pool_framable_replace, pool_framable_cons.
      * rewrite (schedule_policy_focused_user_event rr_scheduler n ts i e k cursor Hobs).
        apply FrVisF; [assumption|].
        intro x; apply IH; auto using pool_branchfree_replace, pool_framable_replace.
    + inversion Hi.
  - destruct n as [|n].
    + rewrite (schedule_policy_empty_none rr_scheduler ts cursor); constructor.
    + change (framableF (okE_policy okE) `R (observe (schedule_rr (S n) ts None cursor))).
      rewrite schedule_rr_no_focus_nonempty; constructor; [exact I|].
      intros []; apply IH; assumption.
Qed.

(** Translation preserves finite guarded-step prefixes. *)
Lemma guards_to_step_translate {E F B X} (f: E ~> F) (t: ctree E B X) :
  guards_to_step t -> guards_to_step (translate f t).
Proof.
  induction 1.
  - eapply guards_to_step_equ; [symmetry; apply unfold_translate|].
    eapply GtsStep; cbn; now rewrite H.
  - eapply guards_to_step_equ; [symmetry; apply unfold_translate|].
    eapply GtsGuard; [cbn; now rewrite H|exact IHguards_to_step].
Qed.

(** Embedding a tree's events under a right summand preserves framability. *)
Lemma framable_translate_inr1 {F E B X} (okE: forall Y, E Y -> Prop) :
  forall (t: ctree E B X), Framable okE t -> Framable (okE_lift (F:=F) okE) (translate inr1 t).
Proof.
  unfold Framable at 2; coinduction R IH; intros t Ht.
  apply framable_unfold in Ht.
  rewrite unfold_translate; cbn; destruct Ht; cbn.
  - constructor.
  - constructor.
  - constructor; apply IH, H.
  - constructor; apply IH, H.
  - constructor; [exact H|intro; apply IH, H0].
  - constructor; [intro; apply guards_to_step_translate, H|intro; apply IH, H0].
Qed.

(** Embedding source events under the policy's left summand frames. *)
Lemma framable_translate_inl1 {E B X} (okE : forall Y, E Y -> Prop) :
  forall (t : ctree E B X), Framable okE t ->
    Framable (okE_policy okE) (translate inl1 t).
Proof.
  unfold Framable at 2; coinduction R IH; intros t Ht.
  apply framable_unfold in Ht.
  rewrite unfold_translate; cbn; destruct Ht; cbn.
  - constructor.
  - constructor.
  - constructor; apply IH, H.
  - constructor; apply IH, H.
  - constructor; [exact H|intro; apply IH, H0].
  - constructor; [intro; apply guards_to_step_translate, H|intro; apply IH, H0].
Qed.


(** Nondeterministic scheduler erasure preserves framability. *)
Lemma framable_erased_nd {E B} `{Bn -< B} (okE: forall Y, E Y -> Prop)
  n (ts: pool E B n) focus :
  pool_branchfree ts -> pool_framable okE ts ->
  Framable okE (project_scheduled (schedule n ts focus)).
Proof.
  unfold schedule; apply framable_schedule.
Qed.

(** Round-robin scheduler erasure preserves framability. *)
Lemma framable_erased_rr {E} (okE: forall Y, E Y -> Prop)
  n (ts: pool E Bn n) focus cursor :
  pool_branchfree ts -> pool_framable okE ts ->
  Framable okE (project_scheduled (schedule_rr n ts focus cursor)).
Proof.
  unfold schedule_rr; apply framable_schedule.
Qed.
