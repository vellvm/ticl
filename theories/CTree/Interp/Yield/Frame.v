From Stdlib Require Import Fin Vector.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Interp.Refine
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
(** Thread and scheduler signatures nest two event lifts. *)
Definition okE_thread {F G E} (okE : forall Y, E Y -> Prop) : forall Y, (F +' (G +' E)) Y -> Prop :=
  okE_lift (okE_lift okE).

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

  (** Scheduling only introduces guarded hidden branches: [schedule_no_focus_nonempty] picks under [Br] with [Step] children. *)
  Lemma framable_schedule : forall n (ts: pool E B n) focus,
    pool_branchfree ts -> pool_framable ts ->
    Framable (okE_thread okE) (schedule n ts focus).
  Proof.
    unfold Framable; coinduction R IH; intros n ts focus Hbf Hfr.
    destruct focus as [i|].
    - destruct n as [|n]; [inversion i|].
      pose proof (Hbf i) as Hi; apply branchfree_unfold in Hi.
      pose proof (Hfr i) as Hfi; apply framable_unfold in Hfi.
      destruct (observe (ts $ i)) eqn:Hobs; cbn.
      + destruct r.
        rewrite (schedule_focused_ret n ts i Hobs); constructor.
        apply IH; auto using pool_branchfree_remove, pool_framable_remove.
      + rewrite (schedule_focused_stuck n ts i Hobs); constructor.
      + rewrite (schedule_focused_step n ts i t Hobs); constructor.
        inversion Hi; inversion Hfi; subst.
        apply IH; auto using pool_branchfree_replace, pool_framable_replace.
      + rewrite (schedule_focused_guard n ts i t Hobs); constructor.
        inversion Hi; inversion Hfi; subst.
        apply IH; auto using pool_branchfree_replace, pool_framable_replace.
      + ddestruction Hi; ddestruction Hfi.
        destruct e as [y|[f|e]]; [destruct y|destruct f|].
        * rewrite (schedule_focused_yield n ts i k Hobs); constructor.
          apply IH; auto using pool_branchfree_replace, pool_framable_replace.
        * rewrite (schedule_focused_fork n ts i k Hobs); constructor; [exact I|].
          intros _; apply IH;
            auto using pool_branchfree_replace, pool_branchfree_cons,
              pool_framable_replace, pool_framable_cons.
        * rewrite (schedule_focused_user_event n ts i e k Hobs); apply FrVisF; [exact H1|].
          intro x; apply IH; auto using pool_branchfree_replace, pool_framable_replace.
      + inversion Hi.
    - destruct n as [|n].
      + cbn; constructor.
      + change (framableF (okE_thread okE) `R (observe (schedule (S n) ts None)));
          rewrite schedule_no_focus_nonempty; constructor; [exact I|].
        intros _; apply (b_chain R); cbn; constructor.
        * intro j; eapply GtsStep; reflexivity.
        * intro j; apply (b_chain R); cbn; constructor; apply IH; auto.
  Qed.
End PoolFramable.

(** Round-robin refinement preserves framability. *)
Lemma framable_refine_rr {E X} (okE: forall Y, E Y -> Prop) :
  forall (t: ctree E Bn X) cursor, Framable okE t -> Framable okE (refine_rr t cursor).
Proof.
  unfold Framable at 2; coinduction R IH; intros t cursor Ht.
  apply framable_unfold in Ht.
  rewrite unfold_refine_rr; cbn; destruct Ht; cbn.
  - constructor.
  - constructor.
  - constructor; apply IH, H.
  - constructor; apply IH, H.
  - constructor; [exact H|intro; apply IH, H0].
  - destruct c as [[|n]]; constructor; apply IH, H0.
Qed.


(** Nondeterministic scheduler erasure preserves framability. *)
Lemma framable_erased_nd {E B} `{Bn -< B} (okE: forall Y, E Y -> Prop)
  n (ts: pool E B n) focus :
  pool_branchfree ts -> pool_framable okE ts ->
  Framable okE (interp_yield (interp_spawn (schedule n ts focus))).
Proof.
  intros Hbf Hfr; unfold interp_yield, interp_spawn.
  apply (framable_interp _ (okE_lift okE)); [framable_handler|].
  apply (framable_interp _ (okE_thread okE)); [framable_handler|].
  now apply framable_schedule.
Qed.

(** Round-robin scheduler erasure preserves framability. *)
Lemma framable_erased_rr {E} (okE: forall Y, E Y -> Prop)
  n (ts: pool E Bn n) focus cursor :
  pool_branchfree ts -> pool_framable okE ts ->
  Framable okE (interp_yield (interp_spawn (run_round_robin (schedule n ts focus) cursor))).
Proof.
  intros Hbf Hfr; unfold interp_yield, interp_spawn.
  apply (framable_interp _ (okE_lift okE)); [framable_handler|].
  apply (framable_interp _ (okE_thread okE)); [framable_handler|].
  unfold run_round_robin, CTree.map.
  apply framable_bind; [apply framable_refine_rr; now apply framable_schedule|intro; apply fr_ret].
Qed.
