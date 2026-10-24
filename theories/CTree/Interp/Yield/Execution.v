(** * Abstract turn models and pool simulation.

    The bridge between an ABSTRACT stepping model (a partial transition on an
    opaque state, emitting at most one observation per turn) and the CONCRETE
    scheduled interpretation of a thread pool.

    Nothing here mentions a particular source language.  [Execution] and
    [ThreadSegment] stay output/list polymorphic; only these two models fix
    the zero-or-one-observation turn shape.

    Every scheduling decision of the concrete schedulers is one visible step
    ([brS] under nondeterministic scheduling, its round-robin refinement
    [Step]); both models begin every turn with that step. *)

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector
  Classes.Morphisms Classes.RelationClasses Classes.RelationPairs.
From ExtLib Require Import Data.Option.
From Coinduction Require Import all.
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
  CTree.Interp.Yield.Segments
  Utils.Vectors
  Utils.Execution.

Import CTreeNotations CoindNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(** ** Turn-structured emission.

    A finite list of turns, each one visible step followed by its (at most
    one) observation. *)
Fixpoint emit_turns {W : Type} {B : Type -> Type} {X : Type}
  (turns : list (option W)) (t : ctreeW W B X) : ctreeW W B X :=
  match turns with
  | [] => t
  | ev :: rest => Step (emit_list (event_obs ev) (emit_turns rest t))
  end.

Lemma emit_turns_app {W : Type} {B : Type -> Type} {X : Type} xs ys (t : ctreeW W B X) :
  emit_turns (xs ++ ys) t = emit_turns xs (emit_turns ys t).
Proof. induction xs as [|ev xs IH]; cbn [emit_turns List.app]; [reflexivity|now rewrite IH]. Qed.

Lemma emit_turns_equ {W : Type} {B : Type -> Type} {X : Type} turns (t u : ctreeW W B X) :
  t ≅ u -> emit_turns turns t ≅ emit_turns turns u.
Proof.
  intro E; induction turns as [|ev rest IH]; cbn [emit_turns]; [exact E|].
  apply step_equ_node, emit_list_equ, IH.
Qed.

Lemma emit_turns_chain {W : Type} {B : Type -> Type} {X : Type}
  {R : Chain (@sb (writerE W) (writerE W) B B X X eq)} turns (t u : ctreeW W B X) :
  `R t u -> `R (emit_turns turns t) (emit_turns turns u).
Proof.
  intro H; induction turns as [|ev rest IH]; cbn [emit_turns]; [exact H|].
  apply (b_chain R), step_sb_step; [reflexivity|].
  apply emit_list_chain, IH.
Qed.

Lemma emit_turns_sbisim {W : Type} {B : Type -> Type} {X : Type} turns (t u : ctreeW W B X) :
  t ~ u -> emit_turns turns t ~ emit_turns turns u.
Proof. apply (emit_turns_chain (R := chain_gfp _)). Qed.

Lemma emit_turns_bind {W : Type} {B : Type -> Type} {X Y : Type} turns (t : ctreeW W B X)
  (k : X -> ctreeW W B Y) :
  emit_turns turns t >>= k ≅ emit_turns turns (t >>= k).
Proof.
  induction turns as [|ev rest IH]; cbn [emit_turns]; [reflexivity|].
  rewrite bind_step, emit_list_bind; apply step_equ_node, emit_list_equ, IH.
Qed.

Lemma emit_turns_ret_bind {W : Type} {B : Type -> Type} {X Y : Type} turns (x : X)
  (k : X -> ctreeW W B Y) :
  emit_turns turns (Ret x) >>= k ≅ emit_turns turns (k x).
Proof. rewrite emit_turns_bind; apply emit_turns_equ, bind_ret_l. Qed.

(** Finitely many leading guards are invisible. *)
Lemma rr_guards_sbisim {W : Type} {B : Type -> Type} {X : Type} k (t : ctreeW W B X) :
  rr_guards k t ~ t.
Proof. induction k; cbn [rr_guards]; [reflexivity|rewrite sb_guard; exact IHk]. Qed.

Lemma sb_chain_guards_l {W : Type} {B : Type -> Type} {X : Type}
  {R : Chain (@sb (writerE W) (writerE W) B B X X eq)} k (t u : ctreeW W B X) :
  `R t u -> `R (rr_guards k t) u.
Proof. intro H; transitivity t; [apply (gfp_chain R), rr_guards_sbisim|exact H]. Qed.

Lemma sb_chain_guards_r {W : Type} {B : Type -> Type} {X : Type}
  {R : Chain (@sb (writerE W) (writerE W) B B X X eq)} k (t u : ctreeW W B X) :
  `R t u -> `R t (rr_guards k u).
Proof.
  intro H; transitivity u; [exact H|apply (gfp_chain R); symmetry; apply rr_guards_sbisim].
Qed.

(** Repeating turn batches: the turn-structured twin of [emit_batches]. *)
Definition emit_turn_batches {W : Type} {B : Type -> Type} {I X : Type}
  (batch : I -> list (option W)) (next : I -> I) (i : I) : ctreeW W B X :=
  CTree.iter (fun j => emit_turns (batch j) (Ret (@inl I X (next j)))) i.

Lemma emit_turn_batches_unfold {W : Type} {B : Type -> Type} {I X : Type}
  (batch : I -> list (option W)) (next : I -> I) i :
  (emit_turn_batches batch next i : ctreeW W B X) ≅
    emit_turns (batch i) (Guard (emit_turn_batches batch next (next i))).
Proof.
  unfold emit_turn_batches at 1; rewrite unfold_iter.
  rewrite emit_turns_ret_bind; reflexivity.
Qed.

Lemma emit_turn_batches_unfold_sbisim {W : Type} {B : Type -> Type} {I X : Type}
  (batch : I -> list (option W)) (next : I -> I) i :
  (emit_turn_batches batch next i : ctreeW W B X) ~
    emit_turns (batch i) (emit_turn_batches batch next (next i) : ctreeW W B X).
Proof.
  rewrite emit_turn_batches_unfold.
  apply emit_turns_sbisim, sb_guard.
Qed.

(** A root family that runs its own turn batch each round IS the batch loop.
    A nonempty batch always begins with a visible step, which is what makes
    the coinduction productive. *)
Lemma emit_turn_batches_bisim {W : Type} {B : Type -> Type} {I X : Type}
  (batch : I -> list (option W)) (next : I -> I)
  (Inv : I -> Prop) (root : I -> ctreeW W B X)
  (Hnext : forall i, Inv i -> Inv (next i))
  (Hnonempty : forall i, Inv i -> batch i <> [])
  (Hroot : forall i, Inv i -> root i ~ emit_turns (batch i) (root (next i))) :
  forall i, Inv i -> root i ~ (emit_turn_batches batch next i : ctreeW W B X).
Proof.
  unfold sbisim; coinduction R IH; intros i Hi.
  assert (Hstep : sb eq `R
      (emit_turns (batch i) (root (next i)))
      (emit_turns (batch i) (emit_turn_batches batch next (next i) : ctreeW W B X))).
  { destruct (batch i) as [|ev rest] eqn:Eb;
      [exfalso; exact (Hnonempty i Hi Eb) |].
    cbn [emit_turns]; apply step_sb_step; [reflexivity|].
    apply emit_list_chain, emit_turns_chain, IH, Hnext, Hi. }
  transitivity (emit_turns (batch i) (root (next i)));
    [apply (gfp_bchain R), (Hroot i Hi) |].
  transitivity (emit_turns (batch i) (emit_turn_batches batch next (next i) : ctreeW W B X));
    [exact Hstep |].
  apply (gfp_bchain R); symmetry.
  exact (emit_turn_batches_unfold_sbisim batch next i).
Qed.

(** ** The two models *)
Section ModelND.
  Context {St Act W X : Type} {B : Type -> Type} {HB : Bn -< B} (n : nat)
    (actor : Fin.t (S n) -> Act)
    (step : Act -> St -> option (St * option W)).

  (** Every nondeterministic turn begins with exactly one visible branch.
      The post-effect guards are invisible, not additional choices. *)
  CoFixpoint model_nd (s : St) : ctreeW W B X :=
    brS (branchn (S n)) (fun i =>
      match step (actor i) s with
      | None => Stuck
      | Some (next,None) => Guard (model_nd next)
      | Some (next,Some event) =>
          Vis (Log event) (fun _ => Guard (model_nd next))
      end).

  Lemma unfold_model_nd s :
    (model_nd s : ctreeW W B X) ≅
    brS (branchn (S n)) (fun i =>
      match step (actor i) s with
      | None => Stuck
      | Some (next,None) => Guard (model_nd next)
      | Some (next,Some event) =>
          Vis (Log event) (fun _ => Guard (model_nd next))
      end).
  Proof. step; now cbn. Qed.

  (** Index-first: no assumption that every abstract action occurs in
      [actor]. *)
  Lemma model_turn_finite_steps (i : Fin.t (S n)) s next event :
    step (actor i) s = Some (next,event) ->
    finite_steps (model_nd s : ctreeW W B X) (turn_labels event)
      (Guard (model_nd next)).
  Proof.
    intro Hstep; destruct event as [o|]; cbn [turn_labels].
    - eapply finite_steps_cons with
        (u := Vis (Log o) (fun _ => Guard (model_nd next))).
      + rewrite (unfold_model_nd s).
        eapply trans_br with (x := i); [apply trans_step|].
        cbn beta; rewrite Hstep; reflexivity.
      + econstructor;
          [exact (trans_vis (Log o) tt (fun _ => Guard (model_nd next)))|constructor].
    - econstructor; [|constructor].
      rewrite (unfold_model_nd s).
      eapply trans_br with (x := i); [apply trans_step|].
      cbn beta; rewrite Hstep; reflexivity.
  Qed.
End ModelND.

Arguments model_nd {St Act W X B HB} n actor step s.

Section ModelRR.
  Context {St Act W X : Type} {B : Type -> Type} (n : nat)
    (actor : Fin.t (S n) -> Act)
    (step : Act -> St -> option (St * option W)).

  (** Every round-robin turn begins with the one visible step of the
      scheduler's (refined) selection. *)
  CoFixpoint model_rr (s : St) (cursor : nat) : ctreeW W B X :=
    Step
      (match step (actor (rr_pick n cursor)) s with
       | None => Stuck
       | Some (next,None) => Guard (model_rr next (S cursor))
       | Some (next,Some event) =>
           Vis (Log event) (fun _ => Guard (model_rr next (S cursor)))
       end).

  Lemma unfold_model_rr s cursor :
    (model_rr s cursor : ctreeW W B X) ≅
    Step
      (match step (actor (rr_pick n cursor)) s with
       | None => Stuck
       | Some (next,None) => Guard (model_rr next (S cursor))
       | Some (next,Some event) =>
           Vis (Log event) (fun _ => Guard (model_rr next (S cursor)))
       end).
  Proof. step; now cbn. Qed.
End ModelRR.

Arguments model_rr {St Act W X B} n actor step s cursor.

(** ** Round-robin model congruence in the state and the cursor. *)
Section ModelRRCongruence.
  Context {St Act W X : Type} {B : Type -> Type} (n : nat)
    (actor : Fin.t (S n) -> Act)
    (step : Act -> St -> option (St * option W))
    (R : St -> St -> Prop)
    (Requiv : Equivalence R)
    (Hstep : Proper (eq ==> R ==> Roption (RelProd R eq)) step).

  Lemma model_rr_equ : forall s t cursor cursor',
    R s t -> cursor mod (S n) = cursor' mod (S n) ->
    (model_rr n actor step s cursor : ctreeW W B X) ≅
      model_rr n actor step t cursor'.
  Proof.
    coinduction Rc IH; intros s t cursor cursor' Hst Hmod.
    assert (Hnextmod : S cursor mod (S n) = S cursor' mod (S n)).
    { replace (S cursor) with (cursor + 1) by lia.
      replace (S cursor') with (cursor' + 1) by lia.
      rewrite (Nat.Div0.add_mod cursor 1 (S n)),
        (Nat.Div0.add_mod cursor' 1 (S n)), Hmod.
      reflexivity. }
    rewrite (unfold_model_rr n actor step s cursor),
      (unfold_model_rr n actor step t cursor').
    cbn -[rr_pick]; constructor.
    rewrite <- (rr_pick_mod_congr n cursor cursor' Hmod).
    pose proof (Hstep (actor (rr_pick n cursor)) _ eq_refl s t Hst) as Hturn.
    destruct (step (actor (rr_pick n cursor)) s) as [[s' event]|];
      destruct (step (actor (rr_pick n cursor)) t) as [[t' event']|];
      inversion Hturn as [|p q Hpair]; subst.
    - unfold RelProd, RelCompFun in Hpair.
      destruct Hpair as [Hnext Hevent]; cbn in Hnext, Hevent; subst event'.
      destruct event as [o|].
      + step; constructor; intros [].
        step; constructor; apply IH; [exact Hnext|exact Hnextmod].
      + step; constructor; apply IH; [exact Hnext|exact Hnextmod].
    - step; constructor.
  Qed.
End ModelRRCongruence.

(** ** Finite replay against the models. *)
Definition rr_script {Act} (n : nat) (actor : Fin.t (S n) -> Act)
  (cursor len : nat) : list Act :=
  List.map (fun k => actor (rr_pick n k)) (List.seq cursor len).

(** One turn per script entry: the turn list of a run. *)
Definition turn_list {W} (event : option W) : list (option W) := [event].

Section ModelReplay.
  Context {St Act W X : Type} {B : Type -> Type} (n : nat)
    (actor : Fin.t (S n) -> Act)
    (step : Act -> St -> option (St * option W)).

  Lemma model_rr_run_turns : forall len cursor s last turns,
    run_turns step turn_list (rr_script n actor cursor len) s = Some (last,turns) ->
    (model_rr n actor step s cursor : ctreeW W B X) ~
      emit_turns turns (model_rr n actor step last (cursor + len) : ctreeW W B X).
  Proof.
    induction len as [|len IH]; intros cursor s last turns Hrun.
    - cbn [rr_script List.seq List.map run_turns] in Hrun.
      inversion Hrun; subst; cbn [emit_turns].
      now rewrite Nat.add_0_r.
    - unfold rr_script in Hrun; cbn [List.seq List.map run_turns] in Hrun.
      destruct (step (actor (rr_pick n cursor)) s) as [[next event]|] eqn:Hstep;
        [|discriminate].
      destruct (run_turns step turn_list
        (List.map (fun k => actor (rr_pick n k)) (List.seq (S cursor) len)) next)
        as [[last' tail]|] eqn:Hrest; [|discriminate].
      inversion Hrun; subst last turns; clear Hrun.
      specialize (IH (S cursor) next last' tail Hrest).
      rewrite (unfold_model_rr n actor step s cursor), Hstep.
      replace (cursor + S len) with (S cursor + len) by lia.
      cbn [turn_list List.app emit_turns].
      apply sb_step.
      destruct event as [o|]; cbn [event_obs].
      + rewrite emit_list_cons.
        apply sb_vis; intros []; rewrite sb_guard; exact IH.
      + cbn [emit_list List.fold_right]; rewrite sb_guard; exact IH.
  Qed.
End ModelReplay.

Lemma label_logs_app {W} (xs ys : list (@label (writerE W))) :
  label_logs (xs ++ ys) = label_logs xs ++ label_logs ys.
Proof. unfold label_logs; apply List.flat_map_app. Qed.

Lemma label_taus_app {W} (xs ys : list (@label (writerE W))) :
  label_taus (xs ++ ys) = label_taus xs + label_taus ys.
Proof. unfold label_taus; rewrite List.filter_app; apply List.length_app. Qed.

Section ModelReplayND.
  Context {St Act W X : Type} {B : Type -> Type} {HB : Bn -< B} (n : nat)
    (actor : Fin.t (S n) -> Act)
    (step : Act -> St -> option (St * option W)).

  (** Realizing every abstract action needs the two inverse slot laws. *)
  Context (slot : Act -> Fin.t (S n))
    (actor_slot : forall who, actor (slot who) = who).

  Lemma model_run_turns_labels : forall script s last logs,
    run_turns step event_obs script s = Some (last,logs) ->
    exists labels residual,
      run_turns step turn_labels script s = Some (last,labels) /\
      label_logs labels = logs /\
      label_taus labels = List.length script /\
      finite_steps (model_nd n actor step s : ctreeW W B X) labels residual /\
      residual ~ (model_nd n actor step last : ctreeW W B X).
  Proof.
    induction script as [|who rest IH]; intros s last logs Hrun.
    - cbn [run_turns] in Hrun; inversion Hrun; subst last logs.
      exists [], (model_nd n actor step s); repeat split;
        try reflexivity; constructor.
    - cbn [run_turns] in Hrun.
      destruct (step who s) as [[next event]|] eqn:Hstep; [|discriminate].
      destruct (run_turns step event_obs rest next) as [[last' logs']|] eqn:Hrest;
        [|discriminate].
      inversion Hrun; subst last logs; clear Hrun.
      destruct (IH next last' logs' Hrest)
        as (labels & residual & Hlabels & Hlogs & Htaus & Hsteps & Eresidual).
      exists (turn_labels event ++ labels).
      assert (Eguard : (model_nd n actor step next : ctreeW W B X) ~
        Guard (model_nd n actor step next)) by (symmetry; apply sb_guard).
      destruct (finite_steps_sbisim _ _ _ Hsteps _ Eguard)
        as (residual' & Hsteps' & Eresidual').
      exists residual'; split.
      + cbn [run_turns]; rewrite Hstep, Hlabels; reflexivity.
      + split.
        * rewrite label_logs_app, Hlogs.
          destruct event; reflexivity.
        * split.
          -- rewrite label_taus_app, Htaus.
             destruct event; reflexivity.
          -- split.
             ++ eapply finite_steps_app; [|exact Hsteps'].
                rewrite <- (actor_slot who) in Hstep.
                eapply model_turn_finite_steps; exact Hstep.
             ++ transitivity residual;
                  [symmetry; exact Eresidual'|exact Eresidual].
  Qed.
End ModelReplayND.

(** ** Round-robin recurrence from finite cycle certificates.

    A family of boundaries, each of whose RR cycle actually runs to a state
    related to the next boundary while producing a nonempty turn batch, makes
    the RR model bisimilar to the turn batch loop [emit_turn_batches].  A
    failed turn cannot supply a certificate, and the batch comes from the
    actual run; no observation is synthesized and no state is reset. *)
Section ModelRRBatches.
  Context {St Act W X I : Type} {B : Type -> Type}
    (n : nat) (actor : Fin.t (S n) -> Act)
    (step : Act -> St -> option (St * option W))
    (R : St -> St -> Prop)
    (Hstep : Proper (eq ==> R ==> Roption (RelProd R eq)) step)
    (boundary : I -> St) (batch : I -> list (option W)) (next : I -> I)
    (Inv : I -> Prop) (cursor period : nat)
    (Hcursor : (cursor + period) mod (S n) = cursor mod (S n))
    (Hnext : forall i, Inv i -> Inv (next i))
    (Hnonempty : forall i, Inv i -> batch i <> [])
    (Hcycle : forall i, Inv i -> exists last,
      run_turns step turn_list (rr_script n actor cursor period) (boundary i) =
        Some (last,batch i) /\ R last (boundary (next i))).

  Lemma model_rr_emit_batches : forall i, Inv i ->
    (model_rr n actor step (boundary i) cursor : ctreeW W B X) ~
      (emit_turn_batches batch next i : ctreeW W B X).
  Proof.
    apply (emit_turn_batches_bisim batch next Inv
      (fun i => model_rr n actor step (boundary i) cursor : ctreeW W B X)
      Hnext Hnonempty).
    intros i Hi.
    destruct (Hcycle i Hi) as (last & Hrun & Hlast).
    etransitivity;
      [exact (model_rr_run_turns n actor step period cursor (boundary i) last
                (batch i) Hrun)|].
    apply emit_turns_sbisim, equ_sbisim.
    exact (model_rr_equ n actor step R Hstep last (boundary (next i))
      (cursor + period) cursor Hlast Hcursor).
  Qed.
End ModelRRBatches.

(** ** Realizing an abstract execution by its model. *)
Section ModelRealization.
  Context {St Act W X : Type} {B : Type -> Type} {HB : Bn -< B} (n : nat)
    (actor : Fin.t (S n) -> Act)
    (step : Act -> St -> option (St * option W))
    (slot : Act -> Fin.t (S n))
    (actor_slot : forall who, actor (slot who) = who)
    (initial : St -> Prop).

  Lemma valid_execution_realizes_model (e : Execution St Act (option W)) :
    execution_valid (fun a s o s' => step a s = Some (s',o)) initial e ->
    forall k (t : ctreeW W B X),
      t ~ (model_nd n actor step (states e k) : ctreeW W B X) ->
      realizes (fun j => turn_labels (emitted e j)) k t.
  Proof.
    intro Hvalid.
    apply (realizes_from_steps (fun j => turn_labels (emitted e j))
      (fun j => model_nd n actor step (states e j) : ctreeW W B X)).
    - intro j; apply turn_labels_nonempty.
    - intro j; exists (Guard (model_nd n actor step (states e (S j)))); split.
      + pose proof (execution_step step initial e j Hvalid) as Hstep.
        rewrite <- (actor_slot (selected e j)) in Hstep.
        eapply model_turn_finite_steps; exact Hstep.
      + apply sb_guard.
  Qed.
End ModelRealization.

(** ** Raw scheduled executions.

    A raw execution is the SAME [Execution] record, at state
    [pool E B (S n) * Sigma], action [Act], output [list W]. *)
Section RawExecution.
  Context {E B : Type -> Type} {W Sigma Act : Type}
    (n : nat)
    (handler : E ~> stateT Sigma (ctreeW W B))
    (slot : Act -> Fin.t (S n)).

  Notation Rsb := (fun Y (t u : ctreeW W B Y) => t ~ u).

  Definition pool_step (who : Act) (p : pool E B (S n) * Sigma) (logs : list W)
    (q : pool E B (S n) * Sigma) : Prop :=
    let '(ts,sigma) := p in
    let '(ts',sigma') := q in
    exists residual,
      ThreadSegment handler Rsb (ts $ slot who) sigma logs residual sigma' /\
      pool_equ ts' (ts @ slot who := residual).

  Definition pool_execution_valid (ts0 : pool E B (S n)) (sigma0 : Sigma)
    (se : Execution (pool E B (S n) * Sigma) Act (list W)) : Prop :=
    execution_valid pool_step
      (fun p => pool_equ (fst p) ts0 /\ snd p = sigma0) se.

  Lemma pool_step_branchfree who ts sigma logs ts' sigma' :
    pool_step who (ts,sigma) logs (ts',sigma') ->
    (forall j, BranchFree (ts $ j)) -> forall j, BranchFree (ts' $ j).
  Proof.
    intros (residual & Hseg & Epool) Hbf j.
    eapply branchfree_equ_impl; [symmetry; apply Epool|].
    destruct (Fin.eq_dec j (slot who)) as [->|Hne].
    - rewrite Vector.nth_replace_eq.
      eapply ThreadSegment_branchfree; [exact Hseg|apply Hbf].
    - rewrite Vector.nth_replace_neq by congruence; apply Hbf.
  Qed.
End RawExecution.

Arguments pool_step {E B W Sigma Act} n handler slot who p logs q.
Arguments pool_execution_valid {E B W Sigma Act} n handler slot ts0 sigma0 se.

Section RawExecutionND.
  Context {E B : Type -> Type} {HB : Bn -< B} {W Sigma Act : Type}
    (n : nat)
    (handler : E ~> stateT Sigma (ctreeW W B))
    (slot : Act -> Fin.t (S n)).

  Notation Rsb := (fun Y (t u : ctreeW W B Y) => t ~ u).

  Theorem valid_pool_execution_scheduler_steps
    (se : Execution (pool E B (S n) * Sigma) Act (list W)) ts0 sigma0 k :
    pool_execution_valid n handler slot ts0 sigma0 se ->
    exists next,
      finite_steps
        (interp_schedule_nd handler (S n) (fst (states se k)) None
          (snd (states se k)))
        (τ :: List.map (fun o => obs (Log o) tt) (emitted se k)) next /\
      next ~ interp_schedule_nd handler (S n) (fst (states se (S k))) None
        (snd (states se (S k))).
  Proof.
    intros [_ Hsteps]; specialize (Hsteps k).
    destruct (states se k) as [ts sigma] eqn:Ek.
    destruct (states se (S k)) as [ts' sigma'] eqn:Ek'.
    destruct Hsteps as (residual & Hseg & Epool).
    cbn [fst snd].
    eapply (segment_scheduler_steps handler Rsb (fun Y t u (H : t ~ u) => H));
      eassumption.
  Qed.
End RawExecutionND.

(** ** Pool simulation.

    A proof-only certificate (not a typeclass) packaging exactly: executable
    totality and invariant preservation, the actual handler-backed first-yield
    segment of the selected slot, and stability of the unselected slots.  It
    assumes NO liveness, fairness, model trace, global bisimulation, or
    function equality of states. *)
Section PoolSimulation.
  Context {E B : Type -> Type} {HB : Bn -< B} {W Sigma St Act : Type}
    {n : nat}
    {handler : E ~> stateT Sigma (ctreeW W B)}
    (actor : Fin.t (S n) -> Act) {slot : Act -> Fin.t (S n)}
    (slot_actor : forall i, slot (actor i) = i)
    {step : Act -> St -> option (St * option W)}
    {pool_of : St -> pool E B (S n)}
    {agree : Sigma -> St -> Prop}
    {Inv : St -> Prop}.

  Notation Rexact := (fun Y (t u : ctreeW W B Y) => t ≅ u).
  Notation Rsb := (fun Y (t u : ctreeW W B Y) => t ~ u).

  Record PoolSimulation : Prop := {
    simulation_total : forall who s, Inv s ->
      exists s' event, step who s = Some (s',event) /\ Inv s';
    simulation_segment : forall who s s' event sigma,
      Inv s -> agree sigma s -> step who s = Some (s',event) ->
      exists residual sigma',
        ThreadSegment handler Rexact
          (pool_of s $ slot who) sigma (event_obs event) residual sigma' /\
        agree sigma' s' /\
        guard_equ residual (pool_of s' $ slot who) /\
        (forall j, j <> slot who -> (pool_of s $ j) ≅ (pool_of s' $ j))
  }.

  Context (Hsim : PoolSimulation).

  (** The same certificate transported to any pool aligned up to finitely
      many leading guards. *)
  Lemma selected_turn_segment (ts : pool E B (S n)) s who s' event sigma :
    Inv s -> agree sigma s -> pool_guard_equ ts (pool_of s) ->
    step who s = Some (s',event) ->
    exists residual sigma',
      ThreadSegment handler Rexact (ts $ slot who) sigma
        (event_obs event) residual sigma' /\
      agree sigma' s' /\
      pool_guard_equ (ts @ slot who := residual) (pool_of s').
  Proof.
    intros Hinv Hagree Hpool Hstep.
    destruct (simulation_segment Hsim who s s' event sigma Hinv Hagree Hstep)
      as (residual & sigma' & Hseg & Hagree' & Htail & Hframe).
    exists residual, sigma'; split; [|split; [exact Hagree'|]].
    - apply (proj2 (guard_equ_segment_iff handler Rexact
        (ts $ slot who) (pool_of s $ slot who) (Hpool (slot who))
        sigma (event_obs event) residual sigma')); exact Hseg.
    - intro j; destruct (Fin.eq_dec j (slot who)) as [->|Hne].
      + rewrite Vector.nth_replace_eq; exact Htail.
      + rewrite Vector.nth_replace_neq by congruence.
        eapply guard_equ_trans; [apply Hpool|].
        apply guard_equ_equ, Hframe; exact Hne.
  Qed.

  (** One model turn at a guard-aligned pool, run by the ND scheduler focused
      on the selected slot. *)
  Lemma pool_simulation_turn_nd (ts : pool E B (S n)) s who s' event sigma :
    Inv s -> agree sigma s -> pool_guard_equ ts (pool_of s) ->
    step who s = Some (s',event) ->
    exists residual sigma',
      agree sigma' s' /\
      pool_guard_equ (ts @ slot who := residual) (pool_of s') /\
      interp_schedule_nd handler (S n) ts (Some (slot who)) sigma ~
        emit_list (event_obs event)
          (interp_schedule_nd handler (S n) (ts @ slot who := residual) None sigma').
  Proof.
    intros Hinv Hagree Hpool Hstep.
    destruct (selected_turn_segment ts s who s' event sigma
      Hinv Hagree Hpool Hstep) as (residual & sigma' & Hseg & Hagree' & Hpool').
    exists residual, sigma'; split; [exact Hagree'|split; [exact Hpool'|]].
    apply (segment_interp_nd handler Rsb (fun Y t u (H : t ~ u) => H)).
    apply (ThreadSegment_mono handler Rexact Rsb
      (fun Y t u => equ_sbisim t u)); exact Hseg.
  Qed.

  (** Completeness of the abstract model relative to the source: the segment
      is unique, so the abstract turn determines its logs, its final handler
      state (relationally), and the updated pool alignment. *)
  Lemma selected_segment_deterministic (ts : pool E B (S n)) s who s' event
    sigma logs residual sigma' :
    Inv s -> agree sigma s -> pool_guard_equ ts (pool_of s) ->
    step who s = Some (s',event) ->
    ThreadSegment handler Rsb (ts $ slot who) sigma logs residual sigma' ->
    logs = event_obs event /\ agree sigma' s' /\
    pool_guard_equ (ts @ slot who := residual) (pool_of s').
  Proof.
    intros Hinv Hagree Hpool Hstep Hseg.
    destruct (selected_turn_segment ts s who s' event sigma
      Hinv Hagree Hpool Hstep) as (residual0 & sigma0 & Hseg0 & Hagree0 & Hpool0).
    apply (ThreadSegment_mono handler Rexact Rsb
      (fun Y t u => equ_sbisim t u)) in Hseg0.
    destruct (ThreadSegment_deterministic handler Rsb
      (fun Y t u (H : t ~ u) => H) (ts $ slot who) sigma
      logs residual sigma' (event_obs event) residual0 sigma0 Hseg Hseg0)
      as (Elogs & Esigma & Eresidual).
    subst sigma0; split; [exact Elogs|]; split; [exact Hagree0|].
    eapply pool_equ_guard_trans; [|exact Hpool0].
    apply replace_pool_equ; [apply pool_equ_refl|exact Eresidual].
  Qed.

  (** Every raw segment of the selected slot is some model turn. *)
  Lemma selected_segment_complete (ts : pool E B (S n)) s who
    sigma logs residual sigma' :
    Inv s -> agree sigma s -> pool_guard_equ ts (pool_of s) ->
    ThreadSegment handler Rsb (ts $ slot who) sigma logs residual sigma' ->
    exists s' event, step who s = Some (s',event) /\ Inv s' /\
      logs = event_obs event /\ agree sigma' s' /\
      pool_guard_equ (ts @ slot who := residual) (pool_of s').
  Proof.
    intros Hinv Hagree Hpool Hseg.
    destruct (simulation_total Hsim who s Hinv) as (s' & event & Hstep & Hinv').
    exists s', event; split; [exact Hstep|]; split; [exact Hinv'|].
    exact (selected_segment_deterministic ts s who s' event sigma logs residual
      sigma' Hinv Hagree Hpool Hstep Hseg).
  Qed.

  (** *** Worker guarantees of an aligned pool.

      Every slot reaches its next yield; no slot is finished, forking,
      branching, stepping, stuck, divergent, or at a faulting handler call. *)
  Lemma pool_simulation_worker_segment (ts : pool E B (S n)) s who sigma :
    Inv s -> agree sigma s -> pool_guard_equ ts (pool_of s) ->
    exists event residual sigma',
      ThreadSegment handler Rsb (ts $ slot who) sigma
        (event_obs event) residual sigma'.
  Proof.
    intros Hinv Hagree Hpool.
    destruct (simulation_total Hsim who s Hinv) as (s' & event & Hstep & _).
    destruct (selected_turn_segment ts s who s' event sigma Hinv Hagree Hpool Hstep)
      as (residual & sigma' & Hseg & _ & _).
    exists event, residual, sigma'.
    apply (ThreadSegment_mono handler Rexact Rsb (fun Y t u => equ_sbisim t u));
      exact Hseg.
  Qed.

  Lemma pool_simulation_no_terminal_prefix (ts : pool E B (S n)) s who sigma :
    Inv s -> agree sigma s -> pool_guard_equ ts (pool_of s) ->
    ~ guard_equ (ts $ slot who) (Ret tt) /\
    (forall k : bool -> thread E B,
      ~ guard_equ (ts $ slot who) (Vis (inr1 (inl1 Fork)) k)) /\
    (forall Y (c : B Y) (k : Y -> thread E B),
      ~ guard_equ (ts $ slot who) (Br c k)) /\
    (forall u, ~ guard_equ (ts $ slot who) (Step u)) /\
    ~ guard_equ (ts $ slot who) (Stuck : thread E B).
  Proof.
    intros Hinv Hagree Hpool.
    destruct (pool_simulation_worker_segment ts s who sigma Hinv Hagree Hpool)
      as (event & residual & sigma' & Hseg).
    repeat split.
    - intro Hbad.
      destruct (guard_equ_segment handler Rsb _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
      exact (ThreadSegment_ret_absurd handler Rsb sigma _ u sigma' Hfalse).
    - intros k Hbad.
      destruct (guard_equ_segment handler Rsb _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
      exact (ThreadSegment_fork_absurd handler Rsb k sigma _ u sigma' Hfalse).
    - intros Y c k Hbad.
      destruct (guard_equ_segment handler Rsb _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
      exact (ThreadSegment_br_absurd handler Rsb c k sigma _ u sigma' Hfalse).
    - intros v Hbad.
      destruct (guard_equ_segment handler Rsb _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
      exact (ThreadSegment_step_absurd handler Rsb v sigma _ u sigma' Hfalse).
    - intro Hbad.
      destruct (guard_equ_segment handler Rsb _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
      exact (ThreadSegment_stuck_absurd handler Rsb sigma _ u sigma' Hfalse).
  Qed.

  Lemma pool_simulation_no_fault_or_divergence
    (ts : pool E B (S n)) s who sigma :
    Inv s -> agree sigma s -> pool_guard_equ ts (pool_of s) ->
    ~ is_stuck (ts $ slot who) /\
    ~ guard_equ (ts $ slot who) (CTree.spinS : thread E B) /\
    (forall Y (e : E Y) (k : Y -> thread E B),
      guard_equ (ts $ slot who) (Vis (inr1 (inr1 e)) k) ->
      ~ (handler _ e sigma ~ (Stuck : ctreeW W B (Sigma * Y)))).
  Proof.
    intros Hinv Hagree Hpool.
    destruct (pool_simulation_worker_segment ts s who sigma Hinv Hagree Hpool)
      as (event & residual & sigma' & Hseg).
    split.
    - intro Hstuck; exact (ThreadSegment_divergent_absurd handler Rsb _ _ _ _ _ Hstuck Hseg).
    - split.
      + intro Hbad.
        destruct (guard_equ_segment handler Rsb _ _ _ _ _ _ Hbad Hseg) as (u & Hfalse & _).
        exact (ThreadSegment_spin_absurd handler Rsb sigma _ u sigma' Hfalse).
      + intros Y e k Hhead Hfault.
        destruct (guard_equ_segment handler Rsb _ _ _ _ _ _ Hhead Hseg) as (u & Hfalse & _).
        exact (ThreadSegment_fault_absurd handler Rsb (fun Y t u (H : t ~ u) => H)
          e k sigma _ u sigma' Hfault Hfalse).
  Qed.

  (** *** Alignment of raw executions with model executions.

      Any valid raw execution and any valid model execution making the same
      selections stay aligned at every index: invariant, relational state
      agreement, guard-aligned pools, and equal observations. *)
  Theorem source_execution_complete ts0 sigma0 s0
    (se : Execution (pool E B (S n) * Sigma) Act (list W))
    (e : Execution St Act (option W)) :
    Inv s0 -> agree sigma0 s0 -> pool_guard_equ ts0 (pool_of s0) ->
    pool_execution_valid n handler slot ts0 sigma0 se ->
    execution_valid (fun a s o s' => step a s = Some (s',o))
      (fun s => s = s0) e ->
    (forall k, selected e k = selected se k) ->
    forall k, Inv (states e k) /\
      agree (snd (states se k)) (states e k) /\
      pool_guard_equ (fst (states se k)) (pool_of (states e k)) /\
      emitted se k = event_obs (emitted e k).
  Proof.
    intros Hinv0 Hagree0 Hpool0 [Hinit Hsteps] [He0 Hestep] Hsel.
    assert (Haligned : forall k, Inv (states e k) /\
      agree (snd (states se k)) (states e k) /\
      pool_guard_equ (fst (states se k)) (pool_of (states e k))).
    { induction k as [|k (Hinv & Hagree & Hpool)].
      - destruct Hinit as [Hp Hs]; cbn beta in He0; rewrite He0, Hs.
        split; [exact Hinv0|]; split; [exact Hagree0|].
        eapply pool_equ_guard_trans; [exact Hp|exact Hpool0].
      - specialize (Hsteps k); pose proof (Hestep k) as Hturn.
        destruct (states se k) as [ts sigma];
          destruct (states se (S k)) as [ts' sigma'].
        destruct Hsteps as (residual & Hseg & Epool); cbn [fst snd] in *.
        destruct (selected_segment_complete ts (states e k) (selected se k)
          sigma (emitted se k) residual sigma' Hinv Hagree Hpool Hseg)
          as (s' & event & Hstep & Hinv' & _ & Hagree' & Hpool').
        rewrite <- (Hsel k), Hturn in Hstep; injection Hstep as <- <-.
        split; [exact Hinv'|]; split; [exact Hagree'|].
        eapply pool_equ_guard_trans; [exact Epool|exact Hpool']. }
    intro k; destruct (Haligned k) as (Hinv & Hagree & Hpool).
    split; [exact Hinv|]; split; [exact Hagree|]; split; [exact Hpool|].
    specialize (Hsteps k); pose proof (Hestep k) as Hturn.
    destruct (states se k) as [ts sigma];
      destruct (states se (S k)) as [ts' sigma'].
    destruct Hsteps as (residual & Hseg & _); cbn [fst snd] in *.
    rewrite (Hsel k) in Hturn.
    exact (proj1 (selected_segment_deterministic ts (states e k) (selected se k)
      (states e (S k)) (emitted e k) sigma (emitted se k) residual sigma'
      Hinv Hagree Hpool Hturn Hseg)).
  Qed.

  (** Every finitely reachable raw configuration is aligned with some model
      state; reachability is the library closure, not a second inductive. *)
  Lemma pool_simulation_reachable ts0 sigma0 s0 :
    Inv s0 -> agree sigma0 s0 -> pool_guard_equ ts0 (pool_of s0) ->
    forall ts sigma,
      reachable (pool_step n handler slot)
        (fun p => pool_equ (fst p) ts0 /\ snd p = sigma0) (ts,sigma) ->
      exists s, Inv s /\ agree sigma s /\ pool_guard_equ ts (pool_of s).
  Proof.
    intros Hinv0 Hagree0 Hpool0 ts sigma.
    apply (reachable_inv (pool_step n handler slot)
      (fun p => pool_equ (fst p) ts0 /\ snd p = sigma0)
      (fun p => exists s, Inv s /\ agree (snd p) s /\
        pool_guard_equ (fst p) (pool_of s))).
    - intros [ts1 sigma1] [Hp Hs]; cbn [fst snd] in *; subst sigma1.
      exists s0; split; [exact Hinv0|]; split; [exact Hagree0|].
      eapply pool_equ_guard_trans; [exact Hp|exact Hpool0].
    - intros a [ts1 sigma1] o [ts2 sigma2] (s & Hinv & Hagree & Hpool) Hstep;
        cbn [fst snd] in *.
      destruct Hstep as (residual & Hseg & Epool).
      destruct (selected_segment_complete ts1 s a sigma1 o residual sigma2
        Hinv Hagree Hpool Hseg)
        as (s' & event & _ & Hinv' & _ & Hagree' & Hpool').
      exists s'; split; [exact Hinv'|]; split; [exact Hagree'|].
      eapply pool_equ_guard_trans; [exact Epool|exact Hpool'].
  Qed.

  (** *** Nondeterministic scheduling agrees with the ND model. *)
  Lemma pool_simulation_nd_bisim : forall s ts sigma,
    Inv s -> agree sigma s -> pool_guard_equ ts (pool_of s) ->
    interp_schedule_nd handler (S n) ts None sigma ~
      (model_nd n actor step s : ctreeW W B (Sigma * unit)).
  Proof.
    unfold sbisim; coinduction R IH.
    intros s ts sigma Hinv Hagree Hpool.
    transitivity (brS (branchn (S n))
      (fun i => interp_schedule_nd handler (S n) ts (Some i) sigma));
      [apply (gfp_bchain R); exact (interp_schedule_nd_select handler n ts sigma)|].
    rewrite (unfold_model_nd n actor step s).
    apply step_sb_brS_id; [reflexivity|]; intro i; cbn beta.
    destruct (simulation_total Hsim (actor i) s Hinv)
      as (next & event & Hstep & Hnextinv).
    rewrite Hstep.
    destruct (pool_simulation_turn_nd ts s (actor i) next event sigma
      Hinv Hagree Hpool Hstep)
      as (residual & sigma' & Hagree' & Hnextpool & Efocus).
    rewrite slot_actor in Hnextpool, Efocus.
    transitivity (emit_list (event_obs event)
      (interp_schedule_nd handler (S n) (ts @ i := residual) None sigma'));
      [apply (gfp_chain R); exact Efocus|].
    assert (Hcontinue : `R
      (interp_schedule_nd handler (S n) (ts @ i := residual) None sigma')
      (Guard (model_nd n actor step next))).
    { transitivity (model_nd n actor step next : ctreeW W B (Sigma * unit));
        [exact (IH next (ts @ i := residual) sigma' Hnextinv Hagree' Hnextpool)|].
      apply (gfp_chain R); symmetry;
        exact (sb_guard (model_nd n actor step next : ctreeW W B (Sigma * unit))). }
    destruct event as [o|]; cbn [event_obs].
    - rewrite emit_list_cons.
      apply vis_chain; intros []; exact Hcontinue.
    - exact Hcontinue.
  Qed.
End PoolSimulation.

Arguments PoolSimulation {E B W Sigma St Act} n handler slot step
  pool_of agree Inv.

(** *** Round-robin scheduling agrees with the RR model.

    Round-robin refinement is fixed to the finite branch signature [Bn]. *)
Section PoolSimulationRR.
  Context {E : Type -> Type} {W Sigma St Act : Type}
    {n : nat}
    {handler : E ~> stateT Sigma (ctreeW W Bn)}
    (actor : Fin.t (S n) -> Act) {slot : Act -> Fin.t (S n)}
    (slot_actor : forall i, slot (actor i) = i)
    {step : Act -> St -> option (St * option W)}
    {pool_of : St -> pool E Bn (S n)}
    {agree : Sigma -> St -> Prop}
    {Inv : St -> Prop}
    (Hsim : PoolSimulation n handler slot step pool_of agree Inv).

  Lemma pool_simulation_rr_bisim : forall s ts sigma cursor,
    Inv s -> agree sigma s -> pool_guard_equ ts (pool_of s) ->
    interp_schedule_rr handler (S n) ts None cursor sigma ~
      (model_rr n actor step s cursor : ctreeW W Bn (Sigma * unit)).
  Proof.
    unfold sbisim; coinduction R IH.
    intros s ts sigma cursor Hinv Hagree Hpool.
    set (who := actor (rr_pick n cursor)).
    assert (Eslot : slot who = rr_pick n cursor) by apply slot_actor.
    destruct (simulation_total Hsim who s Hinv)
      as (next & event & Hstep & Hnextinv).
    destruct (selected_turn_segment Hsim ts s who next event sigma
      Hinv Hagree Hpool Hstep) as (residual & sigma' & Hseg & Hagree' & Hnextpool).
    destruct (exact_segment_rr_prefix handler n ts (slot who)
      (ts $ slot who) (S cursor) sigma (event_obs event) residual sigma' Hseg)
      as (word & Ew & Et).
    set (next_tree := interp_schedule_rr handler (S n)
      (ts @ slot who := residual) None (S cursor) sigma').
    set (next_model :=
      (model_rr n actor step next (S cursor) : ctreeW W Bn (Sigma * unit))).
    assert (Eprefix : interp_schedule_rr handler (S n) ts
      (Some (slot who)) (S cursor) sigma ≅ rr_prefix word (Guard next_tree)).
    { etransitivity; [| exact Et].
      symmetry;
      exact (interp_schedule_rr_equ handler (S n)
        (ts @ slot who := (ts $ slot who)) ts (Some (slot who)) (S cursor) sigma
        (pool_replace_current ts (slot who))). }
    assert (Hcontinue : `R next_tree next_model).
    { apply IH; assumption. }
    rewrite (segment_rr_select_exact handler n ts cursor sigma).
    rewrite (unfold_model_rr n actor step s cursor); fold who; rewrite Hstep.
    transitivity (Step (rr_guards 3 (interp_schedule_rr handler (S n) ts
      (Some (rr_pick n cursor)) (S cursor) sigma)));
      [apply (gfp_bchain R), rr_guards_sbisim|].
    apply step_sb_step; [reflexivity|].
    apply sb_chain_guards_l.
    rewrite <- Eslot, Eprefix.
    destruct event as [o|]; cbn [event_obs] in Ew.
    - destruct (rr_prefix_one_event word o (Guard next_tree) Ew) as (a & b & Eword).
      rewrite Eword.
      apply sb_chain_guards_l.
      apply vis_chain; intros [].
      rewrite rr_guards_guard.
      apply sb_chain_guards_l, (sb_chain_guards_r 1), Hcontinue.
    - rewrite (rr_prefix_no_events word (Guard next_tree) Ew), rr_guards_guard.
      apply sb_chain_guards_l, (sb_chain_guards_r 1), Hcontinue.
  Qed.
End PoolSimulationRR.
