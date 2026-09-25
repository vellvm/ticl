From Stdlib Require Import List Lia Arith.PeanoNat.
From TICL Require Import ICTree.Interp.Yield.Execution.
From TICL Require Import Utils.Execution.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Trans ICTree.Events.Writer ICTree.Events.Yield ICTree.Logic.Trace Utils.Relations.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Program
  CSL.Allocator.Model CSL.Allocator.Execution.

Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(** Executions are the library record [Utils.Execution.Execution] at the
    allocator's state/actor/output types; validity and construction are the
    two [Model.v] instantiations.  No example-local execution record,
    constructor or replay induction remains. *)
(** One observation's tag, one actor's pending remote phase, and owner
    selection: each predicate is stated on the actual turn data, so an idle
    turn, an owner turn, and a polling remote are all explicit cases. *)
Definition event_is (tag : nat) (event : option (indexed (nat * nat))) : bool :=
  match event with None => false
  | Some o => Nat.eqb (fst (indexed_value o)) tag end.
Definition remote_pending (who : Actor) (s : AState) : bool :=
  match who with
  | Owner => false
  | Remote0 => match remote0_state s with RPoll => false | _ => true end
  | Remote1 => match remote1_state s with RPoll => false | _ => true end
  end.
Definition owner_selected (who : Actor) : bool :=
  match who with Owner => true | _ => false end.

Lemma owner_selected_spec who : owner_selected who = true <-> who = Owner.
Proof. destruct who; cbn [owner_selected]; split; intro H; congruence. Qed.
Lemma event_is_spec tag event :
  event_is tag event = true <->
  exists block idx, event = Some (stamp (tag,block) idx).
Proof.
  unfold event_is; destruct event as [[[kind block] idx]|]; cbn.
  - rewrite Nat.eqb_eq; split.
    + intro H; subst kind; now exists block, idx.
    + intros (b & i & H); inversion H; reflexivity.
  - split; [discriminate|intros (b & i & H); discriminate].
Qed.

From Stdlib Require Import List Lia Arith.PeanoNat.
From TICL Require Import Lang.CSL.
From TICL Require Import Lang.CSL.Queue.Representation.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Model.

Import ListNotations.
Local Open Scope nat_scope.

(** These are ghost potentials, not execution states.  The default head is
    immaterial on an invariant state, where the remote header is present. *)
Definition contention_head (s : AState) : nat :=
  match aheap s (remote_head 1) with Some current => current | None => 0 end.
Definition contention_stale (current : nat) (pc : remote_pc) : nat :=
  match pc with
  | RLink _ old | RCAS _ old => if Nat.eqb current old then 0 else 1
  | _ => 0
  end.
Definition contention_phase (pc : remote_pc) : nat :=
  match pc with RPoll | RRead _ => 3 | RLink _ _ => 2 | RCAS _ _ => 1 end.
Definition contention_cost (current : nat) (pc : remote_pc) : nat :=
  contention_phase pc + 3 * contention_stale current pc.
Definition contention_pending_potential (current : nat) (p0 p1 : remote_pc) : nat :=
  contention_cost current p0 + contention_cost current p1 +
    (if Nat.eqb current 0 then 0 else 6).
Definition contention_failure_potential (current : nat) (p0 p1 : remote_pc) : nat :=
  contention_stale current p0 + contention_stale current p1 +
    (if Nat.eqb current 0 then 0 else 2).
Definition contention_pending_rank (s : AState) : nat :=
  contention_pending_potential (contention_head s) (remote0_state s) (remote1_state s).
Definition contention_failure_rank (s : AState) : nat :=
  contention_failure_potential (contention_head s) (remote0_state s) (remote1_state s).

Lemma contention_stale_bound current pc : contention_stale current pc <= 1.
Proof.
  destruct pc; cbn [contention_stale];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.
Lemma contention_cost_bound current pc : contention_cost current pc <= 5.
Proof.
  destruct pc; unfold contention_cost; cbn [contention_phase contention_stale];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.
Lemma contention_pending_rank_bound s : contention_pending_rank s <= 16.
Proof.
  unfold contention_pending_rank, contention_pending_potential.
  pose proof (contention_cost_bound (contention_head s) (remote0_state s)).
  pose proof (contention_cost_bound (contention_head s) (remote1_state s)).
  destruct (Nat.eqb (contention_head s) 0); lia.
Qed.
Lemma contention_failure_rank_bound s : contention_failure_rank s <= 4.
Proof.
  unfold contention_failure_rank, contention_failure_potential.
  pose proof (contention_stale_bound (contention_head s) (remote0_state s)).
  pose proof (contention_stale_bound (contention_head s) (remote1_state s)).
  destruct (Nat.eqb (contention_head s) 0); lia.
Qed.

Lemma contention_stale_reset current pc :
  contention_stale 0 pc <= contention_stale current pc + 1.
Proof. pose proof (contention_stale_bound 0 pc); lia. Qed.
Lemma contention_cost_reset current pc :
  contention_cost 0 pc <= contention_cost current pc + 3.
Proof.
  unfold contention_cost; pose proof (contention_stale_reset current pc); lia.
Qed.
Lemma contention_reset_ranks current p0 p1 :
  contention_pending_potential 0 p0 p1 <= contention_pending_potential current p0 p1 /\
  contention_failure_potential 0 p0 p1 <= contention_failure_potential current p0 p1.
Proof.
  destruct (Nat.eqb current 0) eqn:Hcurrent.
  - apply Nat.eqb_eq in Hcurrent; subst current; split; lia.
  - unfold contention_pending_potential, contention_failure_potential.
    rewrite Hcurrent; cbn [Nat.eqb].
    pose proof (contention_cost_reset current p0).
    pose proof (contention_cost_reset current p1).
    pose proof (contention_stale_reset current p0).
    pose proof (contention_stale_reset current p1).
    split; lia.
Qed.

(** The separation side conditions below use the same partition/address
    lemmas as invariant preservation.  In particular no cached-head freshness
    assumption is used: resetting a nonzero head pays for both stale bits. *)
Local Ltac contention_reduce_turn Hturn :=
  cbn [turn aheap acount owner_state remote0_state remote1_state] in Hturn.
Local Ltac contention_finish Hturn Hnoret Hr target event :=
  inversion Hturn; subst target event; clear Hturn;
  cbn [remote_pending event_is indexed_value fst tag_alloc tag_retire
    tag_reclaim tag_retry aheap remote0_state remote1_state] in Hnoret |- *;
  try discriminate;
  unfold contention_pending_rank, contention_failure_rank, contention_head;
  cbn [aheap remote0_state remote1_state];
  repeat first [rewrite upd_eq | rewrite upd_neq by ai_distinct];
  repeat rewrite Hr;
  cbn.
Local Ltac contention_arithmetic :=
  unfold contention_pending_potential, contention_failure_potential, contention_cost;
  cbn [contention_phase contention_stale];
  repeat match goal with
  | E : Nat.eqb _ _ = _ |- _ => progress rewrite E
  end;
  repeat rewrite Nat.eqb_refl;
  split; lia.

Lemma turn_contention_ranks capacity who s t event :
  allocator_inv 1 capacity s ->
  turn 1 who s = Some (t,event) ->
  event_is tag_retire event = false ->
  (if remote_pending who s then 1 else 0) + contention_pending_rank t <=
    contention_pending_rank s /\
  (if event_is tag_retry event then 1 else 0) + contention_failure_rank t <=
    contention_failure_rank s.
Proof.
  destruct s as [h count op p0 p1].
  cbn [allocator_inv aheap acount owner_state remote0_state remote1_state].
  intros (L & R & D & Hbase & Hback & m0 & m1 & Hr & Hl & Hd & CL & CR & CD &
    Hm0 & Hm1 & Hp & Hop & Ho & Hc0 & Hc1) Hturn Hnoret.
  cbn [aheap acount owner_state remote0_state remote1_state] in *.
  destruct who.
  - destruct op as [|old| |client].
    + contention_reduce_turn Hturn; rewrite Hr in Hturn.
      contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
    + contention_reduce_turn Hturn; rewrite Hr in Hturn.
      destruct (Nat.eqb (hd 0 R) old) eqn:Ecas.
      * rewrite upd_neq in Hturn by ai_distinct; rewrite Hd in Hturn.
        contention_finish Hturn Hnoret Hr t event; apply contention_reset_ranks.
      * contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
    + destruct D as [|b D].
      * contention_reduce_turn Hturn; rewrite Hd in Hturn; cbn [hd Nat.eqb] in Hturn.
        contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
      * cbn [linked] in CD; destruct CD as [Hnext CD].
        assert (Eb : Nat.eqb b 0 = false) by (apply Nat.eqb_neq; ai_distinct).
        contention_reduce_turn Hturn; rewrite Hd in Hturn; cbn [hd] in Hturn.
        rewrite Eb, Hnext, Hl in Hturn.
        contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
    + destruct client.
      * destruct m1 as [|m1].
        -- destruct L as [|b L ].
           ++ contention_reduce_turn Hturn; rewrite Hm1 in Hturn; cbn [Nat.eqb] in Hturn.
              rewrite Hl in Hturn; cbn [hd Nat.eqb] in Hturn.
              contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
           ++ cbn [linked] in CL; destruct CL as [Hnext CL].
              assert (Eb : Nat.eqb b 0 = false) by (apply Nat.eqb_neq; ai_distinct).
              contention_reduce_turn Hturn; rewrite Hm1 in Hturn; cbn [Nat.eqb] in Hturn.
              rewrite Hl in Hturn; cbn [hd] in Hturn; rewrite Eb, Hnext in Hturn.
              contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
        -- contention_reduce_turn Hturn; rewrite Hm1 in Hturn; cbn [Nat.eqb] in Hturn.
           contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
      * destruct m0 as [|m0].
        -- destruct L as [|b L ].
           ++ contention_reduce_turn Hturn; rewrite Hm0 in Hturn; cbn [Nat.eqb] in Hturn.
              rewrite Hl in Hturn; cbn [hd Nat.eqb] in Hturn.
              contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
           ++ cbn [linked] in CL; destruct CL as [Hnext CL].
              assert (Eb : Nat.eqb b 0 = false) by (apply Nat.eqb_neq; ai_distinct).
              contention_reduce_turn Hturn; rewrite Hm0 in Hturn; cbn [Nat.eqb] in Hturn.
              rewrite Hl in Hturn; cbn [hd] in Hturn; rewrite Eb, Hnext in Hturn.
              contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
        -- contention_reduce_turn Hturn; rewrite Hm0 in Hturn; cbn [Nat.eqb] in Hturn.
           contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
  - destruct p0 as [|b|b old|b old].
    + destruct m0 as [|m0].
      * contention_reduce_turn Hturn; rewrite Hm0 in Hturn; cbn [Nat.eqb] in Hturn.
        contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
      * contention_reduce_turn Hturn; rewrite Hm0 in Hturn; cbn [Nat.eqb] in Hturn.
        rewrite upd_neq in Hturn by ai_distinct.
        destruct (h (S (S m0))) eqn:Hpayload; [|discriminate].
        contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
    + contention_reduce_turn Hturn; rewrite Hr in Hturn.
      contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
    + contention_reduce_turn Hturn; destruct (h b) eqn:Hlink; [|discriminate].
      contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
    + contention_reduce_turn Hturn; rewrite Hr in Hturn.
      destruct (Nat.eqb (hd 0 R) old) eqn:Ecas;
        contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
  - destruct p1 as [|b|b old|b old].
    + destruct m1 as [|m1].
      * contention_reduce_turn Hturn; rewrite Hm1 in Hturn; cbn [Nat.eqb] in Hturn.
        contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
      * contention_reduce_turn Hturn; rewrite Hm1 in Hturn; cbn [Nat.eqb] in Hturn.
        rewrite upd_neq in Hturn by ai_distinct.
        destruct (h (S (S m1))) eqn:Hpayload; [|discriminate].
        contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
    + contention_reduce_turn Hturn; rewrite Hr in Hturn.
      contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
    + contention_reduce_turn Hturn; destruct (h b) eqn:Hlink; [|discriminate].
      contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
    + contention_reduce_turn Hturn; rewrite Hr in Hturn.
      destruct (Nat.eqb (hd 0 R) old) eqn:Ecas;
        contention_finish Hturn Hnoret Hr t event; contention_arithmetic.
Qed.

Lemma execution_contention_ranks capacity c e k :
  allocator_valid capacity c e -> event_is tag_retire (emitted e k) = false ->
  (if remote_pending (selected e k) (states e k) then 1 else 0) + contention_pending_rank (states e (S k)) <=
    contention_pending_rank (states e k) /\
  (if event_is tag_retry (emitted e k) then 1 else 0) + contention_failure_rank (states e (S k)) <=
    contention_failure_rank (states e k).
Proof.
  intros Hvalid Hnone.
  exact (turn_contention_ranks capacity (selected e k) (states e k)
    (states e (S k)) (emitted e k) (execution_inv (turn 1) (allocator_inv 1 capacity)
      (fun s => s = initial_state capacity c) e (allocator_initial_inv capacity c)
      (turn_preserves_inv 1 capacity) k Hvalid)
    (execution_step (turn 1) (fun s => s = initial_state capacity c) e k Hvalid) Hnone).
Qed.

(** Both budgets are instances of [Utils.Relations.credit_interval]: the
    [Credit] relation is the corresponding rank at the execution's state,
    the charge is the pending remote turn (respectively [tag_retry]), and the
    goal is publication of [tag_retire].  The interval induction itself is
    the library's. *)
Corollary no_publication_contention_potential capacity c e lo len :
  allocator_valid capacity c e ->
  (forall k, lo <= k < lo + len -> event_is tag_retire (emitted e k) = false) ->
  count_if (fun k => remote_pending (selected e k) (states e k)) lo len + contention_pending_rank (states e (lo + len)) <=
    contention_pending_rank (states e lo) /\
  count_if (fun k => event_is tag_retry (emitted e k)) lo len + contention_failure_rank (states e (lo + len)) <=
    contention_failure_rank (states e lo).
Proof.
  intros Hvalid Hnone.
  assert (Hbool : forall b : bool, ~ b = true -> b = false)
    by (intros [|] H; [exfalso; exact (H eq_refl) | reflexivity]).
  split.
  - destruct (credit_interval
      (fun k r => r = contention_pending_rank (states e k))
      (fun k => remote_pending (selected e k) (states e k)) (fun k => event_is tag_retire (emitted e k) = true))
      with (lo := lo) (len := len)
           (credit := contention_pending_rank (states e lo))
      as (r & Hr & Hbound).
    + intros k r Hr Hgoal; subst r.
      exists (contention_pending_rank (states e (S k))); split; [reflexivity |].
      exact (proj1 (execution_contention_ranks capacity c e k Hvalid
        (Hbool _ Hgoal))).
    + reflexivity.
    + intros k Hk Hgoal; rewrite (Hnone k Hk) in Hgoal; discriminate.
    + rewrite <- Hr; exact Hbound.
  - destruct (credit_interval
      (fun k r => r = contention_failure_rank (states e k))
      (fun k => event_is tag_retry (emitted e k)) (fun k => event_is tag_retire (emitted e k) = true))
      with (lo := lo) (len := len)
           (credit := contention_failure_rank (states e lo))
      as (r & Hr & Hbound).
    + intros k r Hr Hgoal; subst r.
      exists (contention_failure_rank (states e (S k))); split; [reflexivity |].
      exact (proj2 (execution_contention_ranks capacity c e k Hvalid
        (Hbool _ Hgoal))).
    + reflexivity.
    + intros k Hk Hgoal; rewrite (Hnone k Hk) in Hgoal; discriminate.
    + rewrite <- Hr; exact Hbound.
Qed.

(** Only a failed remote CAS emits [tag_retry].  Its unit stale-bit charge
    proves the four-failure bound independently of the number of idle turns. *)
Theorem no_publication_failed_cas_bound capacity c e lo len :
  allocator_valid capacity c e ->
  (forall k, lo <= k < lo + len -> event_is tag_retire (emitted e k) = false) ->
  count_if (fun k => event_is tag_retry (emitted e k)) lo len <= 4.
Proof.
  intros Hvalid Hnone.
  destruct (no_publication_contention_potential capacity c e lo len Hvalid Hnone)
    as [_ Hbound].
  pose proof (contention_failure_rank_bound (states e lo)); lia.
Qed.

Theorem no_publication_pending_bound capacity c e lo len :
  allocator_valid capacity c e ->
  (forall k, lo <= k < lo + len -> event_is tag_retire (emitted e k) = false) ->
  count_if (fun k => remote_pending (selected e k) (states e k)) lo len <= 16.
Proof.
  intros Hvalid Hnone.
  destruct (no_publication_contention_potential capacity c e lo len Hvalid Hnone)
    as [Hbound _].
  pose proof (contention_pending_rank_bound (states e lo)); lia.
Qed.



Theorem remote_free_lockfree capacity c e :
  allocator_valid capacity c e ->
  infinitely (fun k => remote_pending (selected e k) (states e k) = true) ->
  infinitely (fun k => event_is tag_retire (emitted e k) = true).
Proof.
  intros Hvalid Hpending lo.
  destruct (infinitely_count_if (fun k => remote_pending (selected e k) (states e k)) Hpending 17 lo) as [len Hmany].
  destruct (finite_bool_search (fun k => event_is tag_retire (emitted e k)) lo len)
    as [[k [Hk Hevent]]|Hnone].
  - exists k; split; [lia|exact Hevent].
  - pose proof (no_publication_pending_bound capacity c e lo len Hvalid Hnone); lia.
Qed.

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Program.Equality.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Trans ICTree.Events.Writer ICTree.Events.Yield
  ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim ICTree.Interp.Refine
  Utils.Vectors.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Program
  CSL.Allocator.Model CSL.Allocator.Execution.

Import ICtree ICTreeNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(** ** Raw source executions.

    A raw source execution is the library [Execution] at state
    [pool sE 3 * SSig], valid by [allocator_source_valid].  Its alignment
    with the model execution making the same physical selections is the
    library's [source_execution_complete] at [allocator_simulation]; its
    finite reachability is the library closure [reachable]. *)

Lemma source_pool0_branchfree i : BranchFree (source_pool0 1 $ i).
Proof.
  rewrite <- (slot_of_actor_of_slot i); destruct (actor_of_slot i);
    cbn [source_pool0 slot_of_actor Vector.nth]; apply denote_branchfree.
Qed.

(** Finite raw-source reachability has no model premise.  It is useful before
    an infinite schedule is supplied: every physical slot remains selectable. *)
Theorem every_reachable_source_slot_yields capacity c ts sigma (i : Fin.t 3) :
  reachable (pool_step 2 sh slot_of_actor)
    (fun p => pool_equ (fst p) (source_pool0 1) /\ snd p = (page_heap 1 capacity hemp,c))
    (ts,sigma) ->
  BranchFree (ts $ i) /\
  (exists logs residual sigma', (ThreadSegment sh csl_sb) (ts $ i) sigma logs residual sigma') /\
  not (guard_equ (ts $ i) (Ret tt)) /\
  (forall k : bool -> thread sE, ~ guard_equ (ts $ i) (Vis (inr (inl Fork)) k)) /\
  (forall n (k : Fin.t (S n) -> thread sE), ~ guard_equ (ts $ i) (Br n k)) /\
  not (guard_equ (ts $ i) (stuck : thread sE)) /\
  not (guard_equ (ts $ i) (spin : thread sE)).
Proof.
  intro Hreach.
  assert (Hbf : forall j, BranchFree (ts $ j)).
  { refine (reachable_inv (pool_step 2 sh slot_of_actor) _
      (fun p => forall j, BranchFree (fst p $ j)) _ _ (ts,sigma) Hreach).
    - intros [ts0 sigma0] [E _] j; cbn [fst] in *.
      eapply branchfree_equ_impl; [symmetry; apply E|apply source_pool0_branchfree].
    - intros who [ts1 sigma1] logs [ts2 sigma2] H Hstep; cbn [fst] in *.
      exact (pool_step_branchfree 2 sh slot_of_actor who ts1 sigma1 logs ts2 sigma2
        Hstep H). }
  split; [apply Hbf|].
  destruct (pool_simulation_reachable 2 sh slot_of_actor (turn 1) (allocator_pool 1)
    state_agrees (allocator_inv 1 capacity) (allocator_simulation 1 capacity)
    (source_pool0 1) (page_heap 1 capacity hemp,c) (initial_state capacity c)
    (initial_state_inv capacity c) (conj (heq_refl _) eq_refl)
    (pool_equ_guard _ _ (source_pool0_initial capacity c)) ts sigma Hreach)
    as (s & Hinv & Hagree & Hpool).
  rewrite <- (slot_of_actor_of_slot i).
  split.
  - destruct (pool_simulation_worker_segment 2 sh slot_of_actor (turn 1)
      (allocator_pool 1) state_agrees (allocator_inv 1 capacity)
      (allocator_simulation 1 capacity) ts s (actor_of_slot i) sigma
      Hinv Hagree Hpool) as (event & residual & sigma' & Hseg).
    exists (event_obs event), residual, sigma'; exact Hseg.
  - destruct (pool_simulation_no_terminal_prefix 2 sh slot_of_actor (turn 1)
      (allocator_pool 1) state_agrees (allocator_inv 1 capacity)
      (allocator_simulation 1 capacity) ts s (actor_of_slot i) sigma
      Hinv Hagree Hpool) as (Hr & Hf & Hb & Hstuck).
    destruct (pool_simulation_no_fault_or_divergence 2 sh slot_of_actor (turn 1)
      (allocator_pool 1) state_agrees (allocator_inv 1 capacity)
      (allocator_simulation 1 capacity) ts s (actor_of_slot i) sigma
      Hinv Hagree Hpool) as (_ & Hspin & _).
    repeat split; assumption.
Qed.

(** Realization is the library coinductive [ICTree.Trace.realizes] at the
    allocator's per-turn chunking; the model application is the library's
    [valid_execution_realizes_model] at [step := turn 1].  No allocator-local
    cofixpoint remains. *)
Theorem valid_execution_realizes_source capacity c e :
  allocator_valid capacity c e ->
  realizes (fun j => turn_labels (emitted e j)) 0
    (run_nd (allocator_program capacity) hemp c).
Proof.
  intro Hvalid.
  apply (valid_execution_realizes_model 2 actor_of_slot (turn 1) slot_of_actor
    actor_of_slot_of_actor (fun s => s = initial_state capacity c) e Hvalid 0).
  rewrite (proj1 Hvalid); apply run_nd_allocator_bisim.
Qed.

(** Labels retain their interleaving: exactly one scheduling tau per actual
    turn, followed by its zero or one source observation. *)
Theorem run_turns_realizes_source capacity c script last logs :
  run_turns (turn 1) event_obs script (initial_state capacity c) = Some (last,logs) ->
  exists labels residual,
    option_map snd (run_turns (turn 1) turn_labels script (initial_state capacity c)) =
      Some labels /\
    label_logs labels = logs /\ label_taus labels = List.length script /\
    finite_steps (run_nd (allocator_program capacity) hemp c) labels residual /\
    residual ~ (model_nd 2 actor_of_slot (turn 1) last
                  : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Hrun.
  destruct (model_run_turns_labels (X := (unit * SSig)%type)
    2 actor_of_slot (turn 1) slot_of_actor actor_of_slot_of_actor
    script (initial_state capacity c) last logs Hrun)
    as (labels & model & Hlabels & Hlogs & Htaus & Hsteps & Emodel).
  pose proof (run_nd_allocator_bisim capacity c) as Esource; symmetry in Esource.
  destruct (finite_steps_sbisim _ _ _ Hsteps _ Esource)
    as (residual & Hsource & Eresidual).
  exists labels, residual; split; [rewrite Hlabels; reflexivity|].
  repeat split; try assumption.
  transitivity model; [symmetry; exact Eresidual|exact Emodel].
Qed.

(** A pending raw remote is one of the actual continuations after mailbox
    pickup, and before remote_free returns through the successful CAS path.
    This predicate mentions neither a model execution nor future publication. *)
Definition raw_remote_pending base client (t : thread sE) : Prop :=
  exists pc, pc <> RPoll /\ guard_equ t (remote_residual base client pc).
Definition selected_source_pending
  (se : Execution (pool sE 3 * SSig) Actor (list (indexed (nat * nat)))) k : Prop :=
  match selected se k with
  | Owner => False
  | Remote0 => raw_remote_pending 1 false (fst (states se k) $ slot_of_actor Remote0)
  | Remote1 => raw_remote_pending 1 true (fst (states se k) $ slot_of_actor Remote1)
  end.

Definition remote_first_event base client pc : sE :=
  match pc with
  | RPoll => inl (HRead (mailbox base client))
  | RRead _ => inl (HRead (remote_head base))
  | RLink block old => inl (HWrite block old)
  | RCAS block old => inl (HCAS (remote_head base) old block)
  end.

Lemma remote_residual_first_event base client pc :
  exists k : encode (remote_first_event base client pc) -> thread sE,
    remote_residual base client pc ≅
      @go CEff _ unit (VisF (inr (inr (remote_first_event base client pc)) : CEff) k).
Proof.
  destruct pc; cbn [remote_first_event remote_residual].
  - unfold denote, remote_client; eexists.
    etransitivity; [apply source_raw_until|].
    unfold client_round; etransitivity; [apply source_raw_bind|].
    apply source_raw_read_head.
  - unfold remote_free; eexists.
    etransitivity; [apply source_raw_until|].
    unfold remote_attempt; etransitivity; [apply source_raw_bind|].
    apply source_raw_read_head.
  - unfold remote_link_tail; eexists.
    etransitivity; [apply source_raw_bind|]; apply source_raw_write_head.
  - unfold remote_cas_tail; eexists.
    etransitivity; [apply source_raw_bind|]; apply source_raw_cas_head.
Qed.

Lemma remote_poll_not_pending base client pc :
  pc <> RPoll ->
  not (guard_equ (remote_residual base client RPoll) (remote_residual base client pc)).
Proof.
  intros Hpc E; apply guard_equ_sbisim in E.
  destruct (remote_residual_first_event base client RPoll) as [kp Ep].
  destruct (remote_residual_first_event base client pc) as [kq Eq].
  rewrite Ep, Eq in E.
  pose proof (@sbisim_vis_invT CEff _ unit
    (inr (inr (remote_first_event base client RPoll)))
    (inr (inr (remote_first_event base client pc))) kp kq 0 E) as [_ Eevent].
  destruct pc; cbn [remote_first_event] in Eevent; try contradiction; try discriminate.
  unfold remote_head, mailbox in Eevent; destruct client; inversion Eevent; lia.
Qed.

Lemma raw_remote_pending_alignment base client t pc :
  guard_equ t (remote_residual base client pc) ->
  (raw_remote_pending base client t <->
    match pc with RPoll => false | _ => true end = true).
Proof.
  intro E; destruct pc as [|block|block old|block old].
  - split; [|discriminate].
    intros (pc & Hpc & Hraw); exfalso; apply (remote_poll_not_pending base client pc Hpc).
    eapply guard_equ_trans; [apply guard_equ_sym; exact E|exact Hraw].
  - split; [reflexivity|intros _; exists (RRead block); split; [discriminate|exact E]].
  - split; [reflexivity|intros _; exists (RLink block old); split; [discriminate|exact E]].
  - split; [reflexivity|intros _; exists (RCAS block old); split; [discriminate|exact E]].
Qed.


(** On a valid raw execution the raw pending predicate is exactly the model's
    pending-remote predicate at the model execution of the same selections. *)
Lemma selected_source_pending_alignment capacity c se k :
  allocator_source_valid capacity c se ->
  (selected_source_pending se k <->
    remote_pending (selected se k)
      (states (allocator_execution capacity c (selected se)) k) = true).
Proof.
  intro Hvalid.
  assert (Hmodel : allocator_valid capacity c (allocator_execution capacity c (selected se)))
    by apply execution_of_choices_valid.
  destruct (source_execution_complete 2 sh slot_of_actor (turn 1) (allocator_pool 1)
    state_agrees (allocator_inv 1 capacity) (allocator_simulation 1 capacity)
    (source_pool0 1) (page_heap 1 capacity hemp,c) (initial_state capacity c) se (allocator_execution capacity c (selected se))
    (initial_state_inv capacity c) (conj (heq_refl _) eq_refl)
    (pool_equ_guard _ _ (source_pool0_initial capacity c)) Hvalid Hmodel
    (execution_of_choices_selected _ _ _ _ _ _ (selected se)) k)
    as (_ & _ & Hpool & _).
  unfold selected_source_pending; destruct (selected se k); cbn [remote_pending].
  - split; [contradiction|discriminate].
  - apply raw_remote_pending_alignment; exact (Hpool (slot_of_actor Remote0)).
  - apply raw_remote_pending_alignment; exact (Hpool (slot_of_actor Remote1)).
Qed.

Definition source_has_event (kind block : nat)
  (se : Execution (pool sE 3 * SSig) Actor (list (indexed (nat * nat)))) (k : nat) : Prop :=
  exists idx, List.In (stamp (kind,block) idx) (emitted se k).

Theorem source_remote_free_lockfree capacity c se :
  allocator_source_valid capacity c se ->
  infinitely (selected_source_pending se) ->
  infinitely (fun k => exists block, source_has_event tag_retire block se k).
Proof.
  intros Hvalid Hpending.
  set (e := allocator_execution capacity c (selected se)).
  assert (Hmodel : allocator_valid capacity c e) by apply execution_of_choices_valid.
  pose proof (source_execution_complete 2 sh slot_of_actor (turn 1) (allocator_pool 1)
    state_agrees (allocator_inv 1 capacity) (allocator_simulation 1 capacity)
    (source_pool0 1) (page_heap 1 capacity hemp,c) (initial_state capacity c) se e
    (initial_state_inv capacity c) (conj (heq_refl _) eq_refl)
    (pool_equ_guard _ _ (source_pool0_initial capacity c)) Hvalid Hmodel
    (execution_of_choices_selected _ _ _ _ _ _ (selected se))) as Halign.
  assert (Hpend : infinitely (fun k => remote_pending (selected e k) (states e k) = true)).
  { intro n; destruct (Hpending n) as (k & Hnk & Hk); exists k; split; [exact Hnk|].
    exact (proj1 (selected_source_pending_alignment capacity c se k Hvalid) Hk). }
  pose proof (remote_free_lockfree capacity c e Hmodel Hpend) as Hlive.
  intro n; destruct (Hlive n) as (k & Hnk & Hevent).
  apply event_is_spec in Hevent as (block & idx & Hevent).
  exists k; split; [exact Hnk|]; exists block, idx.
  destruct (Halign k) as (_ & _ & _ & Hlogs).
  rewrite Hlogs, Hevent; cbn [event_obs]; now left.
Qed.

From Stdlib Require Import List Lia Arith.PeanoNat Sorting.Permutation.
From TICL Require Import Lang.CSL.
From TICL Require Import Lang.CSL.Queue.Representation.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Model
  CSL.Allocator.Execution.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(** The ownership view, its existential closure, and the ownership change
    of one turn ([turn_view_step]) are owned by [Model.v]; the ghost lists
    are witnesses of the existing invariant, used only inside propositions. *)
Lemma owner_lists_lengths capacity s L R D :
  allocator_view 1 capacity s L R D -> List.length L + List.length R + List.length D <= capacity.
Proof.
  intros (_ & _ & m0 & m1 & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
  apply Permutation_length in Hp.
  repeat rewrite List.length_app in Hp.
  rewrite page_blocks_length in Hp; lia.
Qed.
Lemma owner_lists_disjoint capacity s L R D b :
  allocator_view 1 capacity s L R D -> In b (R ++ D) -> ~ In b L.
Proof.
  intros (_ & _ & m0 & m1 & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _) Hrd Hl.
  assert (Hcount : List.count_occ Nat.eq_dec
    (L ++ R ++ D ++ mailbox_nodes m0 ++ mailbox_nodes m1 ++
      held (remote0_state s) ++ held (remote1_state s)) b <= 1)
    by (apply (proj1 (List.NoDup_count_occ Nat.eq_dec _));
        eapply Permutation_NoDup;
          [apply Permutation_sym, Hp | apply page_blocks_nodup]).
  repeat rewrite List.count_occ_app in Hcount.
  apply (proj1 (List.count_occ_In Nat.eq_dec L b)) in Hl.
  rewrite List.in_app_iff in Hrd; destruct Hrd as [Hr|Hd].
  - apply (proj1 (List.count_occ_In Nat.eq_dec R b)) in Hr; lia.
  - apply (proj1 (List.count_occ_In Nat.eq_dec D b)) in Hd; lia.
Qed.

Definition owner_boundary (who : Actor) (pc : owner_pc) : bool :=
  match who, pc with Owner, OOffer true => true | _, _ => false end.
Definition collection_phase (pc : owner_pc) : bool :=
  match pc with ORead | OCAS _ => true | _ => false end.
Definition owner_rank (capacity : nat) (pc : owner_pc) (R D : list nat) : nat :=
  match pc with
  | ORead => 2 * (capacity - List.length R) + capacity + 5
  | OCAS old => 2 * (capacity - List.length R) + capacity +
      (if Nat.eqb (List.hd 0 R) old then 4 else 6)
  | ODrain => List.length D + 3
  | OOffer false => 2
  | OOffer true => 1
  end.
Definition owner_round_bound capacity := 3 * capacity + 5.
Definition block_event (tag block : nat) (event : option (indexed (nat * nat))) : Prop :=
  exists idx, event = Some (stamp (tag,block) idx).

Lemma ownership_rank_step capacity who pc pc' event L R D L' R' D' :
  ownership_transition who pc pc' event L R D L' R' D' ->
  List.length R <= capacity -> List.length D <= capacity ->
  List.length R' <= capacity -> List.length D' <= capacity ->
  if owner_boundary who pc
  then owner_rank capacity pc' R' D' <= owner_round_bound capacity
  else (if owner_selected who then 1 else 0) + owner_rank capacity pc' R' D' <= owner_rank capacity pc R D.
Proof.
  intros Hstep Hr Hd Hr' Hd'; destruct Hstep;
    cbn [owner_boundary owner_selected owner_rank owner_after_offer List.length List.hd] in *.
  - rewrite Nat.eqb_refl; lia.
  - assert (E : Nat.eqb (List.hd 0 R) old = false) by now apply Nat.eqb_neq.
    rewrite E; lia.
  - rewrite Nat.eqb_refl; lia.
  - lia.
  - lia.
  - destruct client; cbn [owner_boundary owner_selected owner_rank owner_after_offer];
      unfold owner_round_bound; lia.
  - destruct client; cbn [owner_boundary owner_selected owner_rank owner_after_offer];
      unfold owner_round_bound; lia.
  - destruct who; [contradiction| |]; cbn [owner_boundary owner_selected]; lia.
  - destruct who; [contradiction| |]; cbn [owner_boundary owner_selected];
      destruct pc; cbn [owner_rank List.length List.hd] in *;
      repeat match goal with
      | |- context [if ?b then _ else _] => destruct b eqn:?
      end; lia.
Qed.
Lemma owner_rank_positive capacity pc R D : 0 < owner_rank capacity pc R D.
Proof.
  destruct pc as [|old| |client]; cbn [owner_rank];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.

Lemma owner_lists_step_bounded capacity who s t event L R D :
  allocator_view 1 capacity s L R D ->
  owner_rank capacity (owner_state s) R D <= owner_round_bound capacity ->
  turn 1 who s = Some (t,event) ->
  exists L' R' D', allocator_view 1 capacity t L' R' D' /\
    owner_rank capacity (owner_state t) R' D' <= owner_round_bound capacity /\
    ownership_transition who (owner_state s) (owner_state t) event L R D L' R' D'.
Proof.
  intros Hview Hbound Hturn.
  destruct (turn_view_step 1 capacity who s t event L R D Hview Hturn)
    as (L' & R' & D' & Hview' & Hstep).
  pose proof (owner_lists_lengths capacity s L R D Hview) as Hlen.
  pose proof (owner_lists_lengths capacity t L' R' D' Hview') as Hlen'.
  pose proof (ownership_rank_step capacity who (owner_state s) (owner_state t)
    event L R D L' R' D' Hstep ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hrank.
  exists L', R', D'; split; [exact Hview'|]; split; [|exact Hstep].
  destruct (owner_boundary who (owner_state s)); lia.
Qed.
Lemma execution_owner_rank capacity c e k :
  allocator_valid capacity c e -> exists L R D,
    allocator_view 1 capacity (states e k) L R D /\
    owner_rank capacity (owner_state (states e k)) R D <= owner_round_bound capacity.
Proof.
  intro Hv; induction k as [|k IH].
  - destruct (execution_inv (turn 1) (allocator_inv 1 capacity)
      (fun s => s = initial_state capacity c) e (allocator_initial_inv capacity c)
      (turn_preserves_inv 1 capacity) 0 Hv) as (L & R & D & Hview).
    exists L, R, D; split; [exact Hview|].
    rewrite (proj1 Hv); cbn [initial_state owner_state owner_rank].
    unfold owner_round_bound; lia.
  - destruct IH as (L & R & D & Hview & Hrank).
    destruct (owner_lists_step_bounded capacity (selected e k) (states e k)
      (states e (S k)) (emitted e k) L R D Hview Hrank
      (execution_step (turn 1) (fun s => s = initial_state capacity c) e k Hv)) as (L' & R' & D' & Hview' & Hrank' & _).
    now exists L', R', D'.
Qed.

Definition round_completion (e : (Execution AState Actor (option (indexed (nat * nat))))) k :=
  owner_boundary (selected e k) (owner_state (states e k)) = true.

(** The owner round budget is [credit_interval] at the existentially-bounded
    ownership view: [Credit k r] says the view holds at [states e k] with
    rank [r].  Keeping the witnesses in [Prop] is what lets a heap-related
    ghost list serve as the potential. *)
Corollary owner_round_interval_descent capacity c e lo len L R D :
  allocator_valid capacity c e -> allocator_view 1 capacity (states e lo) L R D ->
  (forall j, lo <= j < lo + len -> ~ round_completion e j) ->
  exists L' R' D', allocator_view 1 capacity (states e (lo + len)) L' R' D' /\
    count_if (fun k => owner_selected (selected e k)) lo len +
      owner_rank capacity (owner_state (states e (lo + len))) R' D' <=
      owner_rank capacity (owner_state (states e lo)) R D.
Proof.
  intros Hv Hview Hnone.
  destruct (credit_interval
    (fun k r => exists L1 R1 D1, allocator_view 1 capacity (states e k) L1 R1 D1 /\
       r = owner_rank capacity (owner_state (states e k)) R1 D1)
    (fun k => owner_selected (selected e k)) (round_completion e))
    with (lo := lo) (len := len)
         (credit := owner_rank capacity (owner_state (states e lo)) R D)
    as (r & (L' & R' & D' & Hview' & Hr) & Hbound).
  - intros k r (L1 & R1 & D1 & Hview1 & ->) Hgoal.
    destruct (turn_view_step 1 capacity (selected e k) (states e k)
      (states e (S k)) (emitted e k) L1 R1 D1 Hview1
      (execution_step (turn 1) (fun s => s = initial_state capacity c) e k Hv)) as (L2 & R2 & D2 & Hview2 & Hstep).
    exists (owner_rank capacity (owner_state (states e (S k))) R2 D2); split.
    + exists L2, R2, D2; split; [exact Hview2 | reflexivity].
    + pose proof (owner_lists_lengths capacity _ _ _ _ Hview1) as Hlen.
      pose proof (owner_lists_lengths capacity _ _ _ _ Hview2) as Hlen2.
      pose proof (ownership_rank_step capacity _ _ _ _ _ _ _ _ _ _ Hstep
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hrank.
      assert (Hnb : owner_boundary (selected e k) (owner_state (states e k)) = false).
      { destruct (owner_boundary (selected e k) (owner_state (states e k))) eqn:E;
          [exfalso; apply Hgoal; exact E | reflexivity]. }
      rewrite Hnb in Hrank; cbv beta; lia.
  - exists L, R, D; split; [exact Hview | reflexivity].
  - exact Hnone.
  - exists L', R', D'; split; [exact Hview' |]; rewrite <- Hr; exact Hbound.
Qed.

Theorem no_round_completion_owner_bound capacity c e lo len :
  allocator_valid capacity c e ->
  (forall j, lo <= j < lo + len -> ~ round_completion e j) ->
  count_if (fun k => owner_selected (selected e k)) lo len < 3 * capacity + 5.
Proof.
  intros Hv Hnone.
  destruct (execution_owner_rank capacity c e lo Hv) as (L & R & D & Hview & Hbound).
  destruct (owner_round_interval_descent capacity c e lo len L R D Hv Hview Hnone)
    as (L' & R' & D' & _ & Hrank).
  pose proof (owner_rank_positive capacity (owner_state (states e (lo + len))) R' D').
  unfold owner_round_bound in Hbound; lia.
Qed.

Definition round_completion_dec e k :
  sumbool (round_completion e k) (not (round_completion e k)).
Proof.
  unfold round_completion; destruct (owner_boundary (selected e k) (owner_state (states e k)));
    [left; reflexivity|right; discriminate].
Defined.

Theorem owner_round_selection_bound capacity c e lo len :
  allocator_valid capacity c e -> 3 * capacity + 5 <= count_if (fun k => owner_selected (selected e k)) lo len ->
  exists j, lo <= j < lo + len /\ round_completion e j /\
    count_if (fun k => owner_selected (selected e k)) lo (S j - lo) <= 3 * capacity + 5.
Proof.
  intros Hv Hcount.
  destruct (finite_first (round_completion e) (round_completion_dec e) lo len)
    as [Hnone|(j & Hj & Hdone & Hfirst)].
  - pose proof (no_round_completion_owner_bound capacity c e lo len Hv Hnone); lia.
  - exists j; split; [exact Hj|]; split; [exact Hdone|].
    pose proof (no_round_completion_owner_bound capacity c e lo (j-lo) Hv
      ltac:(intros i Hi; apply Hfirst; lia)) as Hbefore.
    replace (S j-lo) with ((j-lo)+1) by lia.
    rewrite count_if_add, count_if_succ, count_if_zero.
    cbv beta; destruct (owner_selected (selected e (lo + (j-lo)))); lia.
Qed.

Inductive reclaim_credit (capacity block : nat) (pc : owner_pc) (R D : list nat) : nat -> Prop :=
| reclaim_remote : In block R ->
    reclaim_credit capacity block pc R D
      (owner_rank capacity pc R D +
        (if collection_phase pc then 0 else owner_round_bound capacity))
| reclaim_detached : In block D ->
    reclaim_credit capacity block pc R D (List.length D).

Lemma reclaim_credit_positive capacity block pc R D credit :
  reclaim_credit capacity block pc R D credit -> 0 < credit.
Proof.
  intro H; inversion H; subst.
  - pose proof (owner_rank_positive capacity pc R D);
      destruct (collection_phase pc); lia.
  - destruct D; cbn in *; [contradiction|lia].
Qed.
Lemma reclaim_credit_member capacity block pc R D credit :
  reclaim_credit capacity block pc R D credit -> In block (R ++ D).
Proof. intro H; inversion H; subst; apply List.in_app_iff; auto. Qed.
Lemma reclaim_credit_bound capacity block pc R D credit :
  reclaim_credit capacity block pc R D credit ->
  owner_rank capacity pc R D <= owner_round_bound capacity ->
  List.length D <= capacity -> credit <= 2 * owner_round_bound capacity.
Proof.
  intros Hcredit Hrank Hd; inversion Hcredit; subst;
    unfold owner_round_bound in *; destruct (collection_phase pc); lia.
Qed.

Lemma ownership_retire_member who pc pc' event L R D L' R' D' block :
  ownership_transition who pc pc' event L R D L' R' D' ->
  block_event tag_retire block event -> In block R'.
Proof.
  intros Hstep [idx Hevent]; destruct Hstep; try discriminate.
  - destruct H0 as [Hnone|(b & i & Hretry)]; rewrite Hnone in Hevent ||
      rewrite Hretry in Hevent; discriminate.
  - inversion Hevent; subst; now left.
Qed.
Lemma ownership_no_premature_alloc who pc pc' event L R D L' R' D' block :
  ownership_transition who pc pc' event L R D L' R' D' ->
  ~ In block L -> ~ block_event tag_alloc block event.
Proof.
  intros Hstep Hnot [idx Hevent]; destruct Hstep; try discriminate.
  - inversion Hevent; subst; apply Hnot; now left.
  - destruct H0 as [Hnone|(b & i & Hretry)]; rewrite Hnone in Hevent ||
      rewrite Hretry in Hevent; discriminate.
Qed.

Lemma ownership_reclaim_credit_step capacity who pc pc' event L R D L' R' D' block credit :
  ownership_transition who pc pc' event L R D L' R' D' ->
  List.length R <= capacity -> List.length D <= capacity ->
  List.length R' <= capacity -> List.length D' <= capacity ->
  reclaim_credit capacity block pc R D credit ->
  ~ block_event tag_reclaim block event ->
  exists credit', reclaim_credit capacity block pc' R' D' credit' /\
    (if owner_selected who then 1 else 0) + credit' <= credit.
Proof.
  intros Hstep Hr Hd Hr' Hd' Hcredit Hno.
  destruct Hstep.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_remote; eassumption|].
    cbn [owner_selected owner_rank collection_phase]; rewrite Nat.eqb_refl; lia.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_remote; eassumption|].
    assert (E : Nat.eqb (List.hd 0 R) old = false) by now apply Nat.eqb_neq.
    cbn [owner_selected owner_rank collection_phase]; rewrite E; lia.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_detached; eassumption|].
    cbn [owner_selected owner_rank collection_phase]; rewrite Nat.eqb_refl; lia.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_remote; eassumption|].
    cbn [owner_selected owner_rank collection_phase]; lia.
  - inversion Hcredit; subst.
    + eexists; split; [apply reclaim_remote; eassumption|].
      cbn [owner_selected owner_rank collection_phase List.length]; lia.
    + assert (Htail : In block D).
      { match goal with Hin : In block (_ :: D) |- _ => destruct Hin as [Heq|Hin] end.
        - subst; exfalso; apply Hno; eexists; reflexivity.
        - assumption. }
      eexists; split; [apply reclaim_detached; exact Htail|].
      cbn [owner_selected List.length]; lia.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_remote; eassumption|].
    destruct client; cbn [owner_selected owner_rank collection_phase owner_after_offer];
      unfold owner_round_bound; lia.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_remote; eassumption|].
    destruct client; cbn [owner_selected owner_rank collection_phase owner_after_offer];
      unfold owner_round_bound; lia.
  - exists credit; split; [exact Hcredit|].
    destruct who; cbn [owner_selected]; [contradiction|lia|lia].
  - inversion Hcredit; subst.
    + eexists; split; [apply reclaim_remote; now right|].
      destruct who; [contradiction| |]; cbn [owner_selected];
        destruct pc; cbn [owner_rank collection_phase List.length List.hd] in *;
        repeat match goal with
        | |- context [if ?b then _ else _] => destruct b eqn:?
        end; lia.
    + eexists; split; [apply reclaim_detached; eassumption|].
      destruct who; cbn [owner_selected]; [contradiction|lia|lia].
Qed.

Lemma execution_retired_credit capacity c e k block idx :
  allocator_valid capacity c e -> emitted e k = Some (stamp (tag_retire,block) idx) ->
  exists L R D credit,
    allocator_view 1 capacity (states e (S k)) L R D /\
    reclaim_credit capacity block (owner_state (states e (S k))) R D credit /\
    credit <= 2 * owner_round_bound capacity.
Proof.
  intros Hv Hevent.
  destruct (execution_owner_rank capacity c e k Hv) as (L & R & D & Hview & Hrank).
  destruct (owner_lists_step_bounded capacity (selected e k) (states e k)
    (states e (S k)) (emitted e k) L R D Hview Hrank (execution_step (turn 1) (fun s => s = initial_state capacity c) e k Hv))
    as (L' & R' & D' & Hview' & Hrank' & Hstep).
  pose proof (ownership_retire_member _ _ _ _ _ _ _ _ _ _ block Hstep
    ltac:(exists idx; exact Hevent)) as Hin.
  pose proof (reclaim_remote capacity block (owner_state (states e (S k))) R' D' Hin) as Hcredit.
  exists L', R', D', (owner_rank capacity (owner_state (states e (S k))) R' D' +
    (if collection_phase (owner_state (states e (S k))) then 0 else owner_round_bound capacity)).
  split; [exact Hview'|]; split; [exact Hcredit|].
  eapply reclaim_credit_bound; [exact Hcredit|exact Hrank'|].
  pose proof (owner_lists_lengths capacity _ _ _ _ Hview'); lia.
Qed.

(** Reclamation is the same interval theorem at the reclaim credit; the
    one-step obligation is [ownership_reclaim_credit_step]. *)
Corollary reclaim_interval_descent capacity c e lo len L R D block credit :
  allocator_valid capacity c e -> allocator_view 1 capacity (states e lo) L R D ->
  reclaim_credit capacity block (owner_state (states e lo)) R D credit ->
  (forall j, lo <= j < lo + len -> ~ block_event tag_reclaim block (emitted e j)) ->
  exists L' R' D' credit',
    allocator_view 1 capacity (states e (lo + len)) L' R' D' /\
    reclaim_credit capacity block (owner_state (states e (lo + len))) R' D' credit' /\
    count_if (fun k => owner_selected (selected e k)) lo len + credit' <= credit.
Proof.
  intros Hv Hview Hcredit Hnone.
  destruct (credit_interval
    (fun k r => exists L1 R1 D1, allocator_view 1 capacity (states e k) L1 R1 D1 /\
       reclaim_credit capacity block (owner_state (states e k)) R1 D1 r)
    (fun k => owner_selected (selected e k)) (fun j => block_event tag_reclaim block (emitted e j)))
    with (lo := lo) (len := len) (credit := credit)
    as (r & (L' & R' & D' & Hview' & Hcredit') & Hbound).
  - intros k r (L1 & R1 & D1 & Hview1 & Hr) Hgoal.
    destruct (turn_view_step 1 capacity (selected e k) (states e k)
      (states e (S k)) (emitted e k) L1 R1 D1 Hview1
      (execution_step (turn 1) (fun s => s = initial_state capacity c) e k Hv)) as (L2 & R2 & D2 & Hview2 & Hstep).
    pose proof (owner_lists_lengths capacity _ _ _ _ Hview1) as Hlen.
    pose proof (owner_lists_lengths capacity _ _ _ _ Hview2) as Hlen2.
    destruct (ownership_reclaim_credit_step capacity _ _ _ _ _ _ _ _ _ _ block r
      Hstep ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hr Hgoal)
      as (r1 & Hcredit1 & Hrank).
    exists r1; split.
    + exists L2, R2, D2; split; [exact Hview2 | exact Hcredit1].
    + cbv beta; lia.
  - exists L, R, D; split; [exact Hview | exact Hcredit].
  - exact Hnone.
  - exists L', R', D', r; split; [exact Hview' |]; split; [exact Hcredit' | exact Hbound].
Qed.

Definition block_event_dec tag block event :
  sumbool (block_event tag block event) (not (block_event tag block event)).
Proof.
  destruct event as [[[kind b] idx]|].
  - destruct (Nat.eq_dec kind tag) as [->|Hkind];
      destruct (Nat.eq_dec b block) as [->|Hb].
    + left; exists idx; reflexivity.
    + right; intros [i H]; inversion H; contradiction.
    + right; intros [i H]; inversion H; contradiction.
    + right; intros [i H]; inversion H; contradiction.
  - right; intros [i H]; discriminate.
Defined.

Theorem no_reclaim_owner_bound capacity c e k block idx len :
  allocator_valid capacity c e -> emitted e k = Some (stamp (tag_retire,block) idx) ->
  (forall j, S k <= j < S k + len -> ~ block_event tag_reclaim block (emitted e j)) ->
  count_if (fun k => owner_selected (selected e k)) (S k) len < 6 * capacity + 10.
Proof.
  intros Hv Hevent Hnone.
  destruct (execution_retired_credit capacity c e k block idx Hv Hevent)
    as (L & R & D & credit & Hview & Hcredit & Hbound).
  destruct (reclaim_interval_descent capacity c e (S k) len L R D block credit
    Hv Hview Hcredit Hnone) as (L' & R' & D' & credit' & _ & Hcredit' & Hrank).
  pose proof (reclaim_credit_positive _ _ _ _ _ _ Hcredit').
  unfold owner_round_bound in Hbound; lia.
Qed.

Theorem retired_reclaimed_owner_selection_bound capacity c e k block idx len :
  allocator_valid capacity c e -> emitted e k = Some (stamp (tag_retire,block) idx) ->
  6 * capacity + 10 <= count_if (fun k => owner_selected (selected e k)) (S k) len ->
  exists j idx', k < j /\ j < S k + len /\ idx < idx' /\
    emitted e j = Some (stamp (tag_reclaim,block) idx') /\
    count_if (fun k => owner_selected (selected e k)) (S k) (j-k) <= 6 * capacity + 10.
Proof.
  intros Hv Hret Hcount.
  destruct (finite_first (fun j => block_event tag_reclaim block (emitted e j))
    (fun j => block_event_dec tag_reclaim block (emitted e j)) (S k) len)
    as [Hnone|(j & Hj & [idx' Hreclaim] & Hfirst)].
  - pose proof (no_reclaim_owner_bound capacity c e k block idx len Hv Hret Hnone); lia.
  - exists j, idx'; split; [lia|]; split; [lia|]; split.
    + exact (execution_event_order (turn 1)
      (fun s => s = initial_state capacity c) acount indexed_index (turn_counter 1) e k j _ _ Hv ltac:(lia) Hret Hreclaim).
    + split; [exact Hreclaim|].
      pose proof (no_reclaim_owner_bound capacity c e k block idx (j-S k) Hv Hret
        ltac:(intros q Hq; apply Hfirst; lia)) as Hbefore.
      replace (j-k) with ((j-S k)+1) by lia.
      rewrite count_if_add, count_if_succ, count_if_zero.
      cbv beta; destruct (owner_selected (selected e (S k + (j-S k)))); lia.
Qed.

Lemma infinitely_owner_count (e : Execution AState Actor (option (indexed (nat * nat)))) :
  infinitely (fun k => selected e k = Owner) ->
  forall lo n, exists len, n <= count_if (fun k => owner_selected (selected e k)) lo len.
Proof.
  intros Hinf lo n.
  apply infinitely_count_if.
  intro start.
  destruct (Hinf start) as (k & Hk & Howner).
  exists k; split; [exact Hk|].
  apply owner_selected_spec; exact Howner.
Qed.

Theorem retired_eventually_reclaimed capacity c e :
  allocator_valid capacity c e ->
  infinitely (fun k => selected e k = Owner) ->
  forall k block idx,
    emitted e k = Some (stamp (tag_retire,block) idx) ->
    exists j idx', k < j /\ idx < idx' /\
      emitted e j = Some (stamp (tag_reclaim,block) idx').
Proof.
  intros Hv Howner k block idx Hret.
  destruct (infinitely_owner_count e Howner (S k) (6*capacity+10)) as [len Hlen].
  destruct (retired_reclaimed_owner_selection_bound capacity c e k block idx len
    Hv Hret Hlen) as (j & idx' & Hkj & _ & Hidx & Hevent & _).
  now exists j, idx'.
Qed.

Theorem retired_not_reallocated_before_reclaim capacity c e k block idx j :
  allocator_valid capacity c e ->
  emitted e k = Some (stamp (tag_retire,block) idx) -> k < j ->
  (forall q idx', k < q < j -> emitted e q <> Some (stamp (tag_reclaim,block) idx')) ->
  forall idx', emitted e j <> Some (stamp (tag_alloc,block) idx').
Proof.
  intros Hv Hret Hkj Hnone idx' Halloc.
  destruct (execution_retired_credit capacity c e k block idx Hv Hret)
    as (L & R & D & credit & Hview & Hcredit & Hbound).
  destruct (reclaim_interval_descent capacity c e (S k) (j-S k) L R D block credit
    Hv Hview Hcredit ltac:(intros q Hq [i Hi]; apply (Hnone q i); [lia|exact Hi]))
    as (Lj & Rj & Dj & creditj & Hviewj & Hcreditj & _).
  replace (S k + (j-S k)) with j in Hviewj, Hcreditj by lia.
  pose proof (reclaim_credit_member _ _ _ _ _ _ Hcreditj) as Hin.
  pose proof (owner_lists_disjoint capacity (states e j) Lj Rj Dj block Hviewj Hin) as Hnot.
  destruct (turn_view_step 1 capacity (selected e j) (states e j)
    (states e (S j)) (emitted e j) Lj Rj Dj Hviewj (execution_step (turn 1) (fun s => s = initial_state capacity c) e j Hv))
    as (L' & R' & D' & _ & Hstep).
  eapply (ownership_no_premature_alloc _ _ _ _ _ _ _ _ _ _ block Hstep Hnot).
  exists idx'; exact Halloc.
Qed.

Theorem retired_reallocation_requires_reclaim capacity c e k j block idx alloc_idx :
  allocator_valid capacity c e -> k < j ->
  emitted e k = Some (stamp (tag_retire,block) idx) ->
  emitted e j = Some (stamp (tag_alloc,block) alloc_idx) ->
  exists q reclaim_idx, k < q /\ q < j /\ idx < reclaim_idx /\
    reclaim_idx < alloc_idx /\ emitted e q = Some (stamp (tag_reclaim,block) reclaim_idx).
Proof.
  intros Hv Hkj Hret Halloc.
  destruct (finite_first (fun q => block_event tag_reclaim block (emitted e q))
    (fun q => block_event_dec tag_reclaim block (emitted e q)) (S k) (j-S k))
    as [Hnone|(q & Hq & [qi Hreclaim] & _)].
  - exfalso; eapply retired_not_reallocated_before_reclaim;
      [exact Hv|exact Hret|exact Hkj| |exact Halloc].
    intros q qi Hq Hreclaim; apply (Hnone q ltac:(lia)); now exists qi.
  - exists q, qi; split; [lia|]; split; [lia|]; split.
    + exact (execution_event_order (turn 1)
      (fun s => s = initial_state capacity c) acount indexed_index (turn_counter 1) e k q _ _ Hv ltac:(lia) Hret Hreclaim).
    + split; [|exact Hreclaim].
      exact (execution_event_order (turn 1)
      (fun s => s = initial_state capacity c) acount indexed_index (turn_counter 1) e q j _ _ Hv ltac:(lia) Hreclaim Halloc).
Qed.

Theorem source_retired_eventually_reclaimed capacity c se :
  allocator_source_valid capacity c se ->
  infinitely (fun k => selected se k = Owner) ->
  forall k block idx,
    List.In (stamp (tag_retire,block) idx) (emitted se k) ->
    exists j idx', k < j /\ idx < idx' /\
      List.In (stamp (tag_reclaim,block) idx') (emitted se j).
Proof.
  intros Hvalid Howner k block idx Hretire.
  set (e := allocator_execution capacity c (selected se)).
  assert (Hmodel : allocator_valid capacity c e) by apply execution_of_choices_valid.
  pose proof (source_execution_complete 2 sh slot_of_actor (turn 1) (allocator_pool 1)
    state_agrees (allocator_inv 1 capacity) (allocator_simulation 1 capacity)
    (source_pool0 1) (page_heap 1 capacity hemp,c) (initial_state capacity c) se e
    (initial_state_inv capacity c) (conj (heq_refl _) eq_refl)
    (pool_equ_guard _ _ (source_pool0_initial capacity c)) Hvalid Hmodel
    (execution_of_choices_selected _ _ _ _ _ _ (selected se))) as Halign.
  assert (Howner' : infinitely (fun j => selected e j = Owner)) by exact Howner.
  assert (Eretire : emitted e k = Some (stamp (tag_retire,block) idx)).
  {
    destruct (Halign k) as (_ & _ & _ & Hlogs); rewrite Hlogs in Hretire.
    destruct (emitted e k) as [o|] eqn:E; cbn [event_obs] in Hretire;
      [destruct Hretire as [<-|[]]; reflexivity|contradiction].
  }
  destruct (retired_eventually_reclaimed capacity c e Hmodel Howner'
    k block idx Eretire) as (j & idx' & Hkj & Hij & Ereclaim).
  exists j, idx'; repeat split; try assumption.
  destruct (Halign j) as (_ & _ & _ & Hlogs).
  rewrite Hlogs, Ereclaim; cbn [event_obs]; now left.
Qed.

From Stdlib Require Import List Lia Arith.PeanoNat.
From Coinduction Require Import coinduction rel tactics.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Eq.Bind ICTree.Logic.AF ICTree.Logic.AG
  ICTree.Logic.AX ICTree.Logic.Bind ICTree.Logic.Iter ICTree.Logic.State
  ICTree.Logic.Trace ICTree.Logic.Yield Logic.Core.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Program
  CSL.Allocator.Model CSL.Allocator.Execution.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Typeclasses Transparent equ sbisim.

(** ** Round-robin recurrence of the two-client demo.

    The prefix of 57 turns and the repeating 42-turn cycle are executable
    certificates for [model_rr_emit_batches] / [model_rr_agaf]; the logs,
    boundary heap and boundary state are section-local witnesses. *)
Section AllocatorRecurrence.

(** These lists use left numerals so that symbolic counters compute without
    inspecting the counter.  [n+c] is, of course, the prescribed [c+n]. *)
Let demo_prefix (c : nat) : list (indexed (nat * nat)) :=
  [stamp (tag_alloc,6) c; stamp (tag_alloc,8) (1+c);
   stamp (tag_retire,6) (2+c); stamp (tag_retry,8) (3+c);
   stamp (tag_retire,8) (4+c); stamp (tag_reclaim,8) (5+c);
   stamp (tag_reclaim,6) (6+c); stamp (tag_alloc,6) (7+c);
   stamp (tag_alloc,8) (8+c)].

Let demo_cycle_logs (c : nat) : list (indexed (nat * nat)) :=
  [stamp (tag_retire,6) c; stamp (tag_retry,8) (1+c);
   stamp (tag_retire,8) (2+c); stamp (tag_reclaim,8) (3+c);
   stamp (tag_reclaim,6) (4+c); stamp (tag_alloc,6) (5+c);
   stamp (tag_alloc,8) (6+c)].

(** Only a pointwise representative; no execution ever resets its heap to it. *)
Let demo_boundary_heap : Heap := fun x =>
  match x with
  | 1 => Some 0 | 2 => Some 0 | 3 => Some 0 | 4 => Some 0
  | 5 => Some 8 | 6 => Some 8 | 7 => Some 1 | 8 => Some 0
  | 9 => Some 2 | _ => None
  end.
Let demo_boundary (c : nat) : AState :=
  {| aheap := demo_boundary_heap; acount := c;
     owner_state := ORead; remote0_state := RRead 6;
     remote1_state := RPoll |}.

Local Lemma demo_prefix_run c : exists last,
  run_turns (turn 1) event_obs (rr_script 2 actor_of_slot 0 57) (initial_state 2 c) =
    Some (last,demo_prefix c) /\
  state_equiv last (demo_boundary (c+9)).
Proof.
  replace (c+9) with (9+c) by lia.
  eexists; split; [vm_compute; reflexivity|].
  unfold state_equiv; split.
  - intro x.
    do 10 (destruct x as [|x]; [vm_compute; reflexivity|]).
    vm_compute; reflexivity.
  - vm_compute; repeat split; reflexivity.
Qed.

Local Lemma demo_cycle_run c : exists last,
  run_turns (turn 1) event_obs (rr_script 2 actor_of_slot 0 42) (demo_boundary c) =
    Some (last,demo_cycle_logs c) /\
  state_equiv last (demo_boundary (c+7)).
Proof.
  replace (c+7) with (7+c) by lia.
  eexists; split; [vm_compute; reflexivity|].
  unfold state_equiv; split.
  - intro x.
    do 10 (destruct x as [|x]; [vm_compute; reflexivity|]).
    vm_compute; reflexivity.
  - vm_compute; repeat split; reflexivity.
Qed.

Local Lemma demo_cycle_fresh_member c kind :
  List.In kind [tag_alloc;tag_retire;tag_reclaim] ->
  exists o, List.In o (demo_cycle_logs c) /\ (fst (indexed_value o)) = kind /\ c <= indexed_index o.
Proof.
  intros [<-|[<-|[<-|[]]]].
  - exists (stamp (tag_alloc,6) (5+c)); cbn [demo_cycle_logs List.In indexed_value indexed_index fst];
      repeat split; intuition lia.
  - exists (stamp (tag_retire,6) c); cbn [demo_cycle_logs List.In indexed_value indexed_index fst];
      repeat split; intuition lia.
  - exists (stamp (tag_reclaim,8) (3+c)); cbn [demo_cycle_logs List.In indexed_value indexed_index fst];
      repeat split; intuition lia.
Qed.

Local Lemma demo_cycle_logs_nonempty : forall n : nat, True -> demo_cycle_logs n <> [].
Proof. intros n _; unfold demo_cycle_logs; discriminate. Qed.

(** The actual source is the 57-turn prefix followed by the repeating cycle,
    each cycle a genuine 42-turn round-robin run from the actual state. *)
Theorem run_rr_allocator_demo_bisim c :
  run_rr (allocator_program 2) hemp c ~
  emit_list (demo_prefix c)
    (emit_batches demo_cycle_logs (fun n => n+7) (c+9)
       : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  rewrite run_rr_allocator_bisim.
  destruct (demo_prefix_run c) as (last & Hrun & Hlast).
  etransitivity;
    [exact (model_rr_run_turns 2 actor_of_slot (turn 1) 57 0 _ _ _ Hrun)|].
  apply emit_list_sbisim.
  etransitivity; [apply equ_sbisim; exact (model_rr_equ 2 actor_of_slot (turn 1)
    state_equiv (turn_proper 1) last (demo_boundary (c+9)) (0+57) 0 Hlast eq_refl)|].
  exact (model_rr_emit_batches 2 actor_of_slot (turn 1) state_equiv (turn_proper 1)
    demo_boundary demo_cycle_logs (fun n => n+7) (fun _ => True) 0 42 eq_refl
    (fun _ _ => I) demo_cycle_logs_nonempty (fun n _ => demo_cycle_run n) (c+9) I).
Qed.

(** Recurrence is [model_rr_agaf] at [rank := fun c => kb - c] and
    [P o := fst (indexed_value o) = kind /\ kb <= indexed_index o].  The
    concrete tag premise is retained: the generic rule accepts arbitrary
    predicates, but this proof must not claim recurrence of arbitrary tags. *)
Theorem allocator_demo_agaf_fresh c kind kb :
  List.In kind [tag_alloc;tag_retire;tag_reclaim] ->
  <( {run_rr (allocator_program 2) hemp c}, Pure
      |= AG (AF visW {fun o => (fst (indexed_value o)) = kind /\ kb <= indexed_index o}) )>.
Proof.
  intro Hkind.
  assert (Hprogress : forall n : nat, True ->
    (exists o, List.In o (demo_cycle_logs n) /\
       ((fst (indexed_value o)) = kind /\ kb <= indexed_index o))
    \/ kb - (n+7) < kb - n).
  { intros n _; destruct (Nat.le_gt_cases kb n) as [Hle|Hlt].
    - left; destruct (demo_cycle_fresh_member n kind Hkind) as (o & Hin & Htag & Hidx).
      exists o; split; [exact Hin |]; split; [exact Htag | lia].
    - right; lia. }
  rewrite run_rr_allocator_bisim.
  destruct (demo_prefix_run c) as (last & Hrun & Hlast).
  rewrite (model_rr_run_turns 2 actor_of_slot (turn 1) 57 0 _ _ _ Hrun).
  apply agaf_emit_list; [constructor|].
  rewrite (model_rr_equ 2 actor_of_slot (turn 1) state_equiv (turn_proper 1)
    last (demo_boundary (c+9)) (0+57) 0 Hlast eq_refl).
  apply (model_rr_agaf 2 actor_of_slot (turn 1) state_equiv (turn_proper 1)
    demo_boundary demo_cycle_logs (fun n => n+7) (fun _ => True) 0 42 eq_refl
    (fun _ _ => I) demo_cycle_logs_nonempty (fun n _ => demo_cycle_run n)
    (fun n => kb - n) (fun o => (fst (indexed_value o)) = kind /\ kb <= indexed_index o)
    Hprogress (c+9)); [exact I|].
  apply after_logs_not_done; constructor.
Qed.

End AllocatorRecurrence.

(** ** ABA robustness.

    Remote 1 snapshots head 6 and prepares to publish block 8 with link 6;
    before its CAS commits, block 6 is reclaimed, reallocated and retired
    again, so the head is once more 6.  The stale snapshot still matches, and
    the successful CAS loses nothing: the remote list is exactly [8;6]. *)
Section ABASafety.

Let aba_before_reuse :=
  List.repeat Owner 5 ++ List.repeat Remote0 4 ++ List.repeat Remote1 3.
Let aba_before_commit :=
  aba_before_reuse ++ List.repeat Owner 6 ++ List.repeat Remote0 4.
Let aba_script := aba_before_commit ++ [Remote1].
Let aba_logs : list (indexed (nat * nat)) :=
  [stamp (0,6) 0; stamp (0,8) 1; stamp (1,6) 2; stamp (2,6) 3;
   stamp (0,6) 4; stamp (1,6) 5; stamp (1,8) 6].

Theorem aba_snapshot_survives_reuse :
  option_map (fun result => (owner_state (fst result), remote0_state (fst result),
      remote1_state (fst result)))
    (run_turns (turn 1) event_obs aba_before_reuse (initial_state 2 0)) =
    Some (ORead,RPoll,RCAS 8 6) /\
  option_map (fun result => (owner_state (fst result), remote0_state (fst result),
      remote1_state (fst result)))
    (run_turns (turn 1) event_obs aba_before_commit (initial_state 2 0)) =
    Some (ORead,RPoll,RCAS 8 6) /\
  option_map (fun result => [aheap (fst result) 1])
    (run_turns (turn 1) event_obs aba_before_reuse (initial_state 2 0)) = Some [Some 6] /\
  option_map (fun result => [aheap (fst result) 1])
    (run_turns (turn 1) event_obs aba_before_commit (initial_state 2 0)) = Some [Some 6].
Proof. vm_compute; repeat split; reflexivity. Qed.

Lemma aba_run_no_loss : exists last,
  run_turns (turn 1) event_obs aba_script (initial_state 2 0) = Some (last,aba_logs) /\
  allocator_inv 1 2 last /\
  aheap last (remote_head 1) = Some 8 /\ linked (fun a next => aheap last a = Some next) [8;6] 0 /\
  NoDup [8;6] /\ Permutation [8;6] (page_blocks 1 2).
Proof.
  assert (Hrun : exists last,
    run_turns (turn 1) event_obs aba_script (initial_state 2 0) = Some (last,aba_logs)).
  { eexists; vm_compute; reflexivity. }
  destruct Hrun as [last Hrun]; exists last; split; [exact Hrun|]; split.
  - exact (run_turns_preserves_inv (turn 1) event_obs
      (allocator_inv 1 2) (turn_preserves_inv 1 2) aba_script (initial_state 2 0)
      last aba_logs (initial_state_inv 2 0) Hrun).
  - vm_compute in Hrun; inversion Hrun; subst last.
    split; [reflexivity|]; split; [repeat split; reflexivity|]; split.
    + repeat constructor; cbn; intuition congruence.
    + change (Permutation [8;6] [6;8]); apply perm_swap.
Qed.

Theorem aba_actual_source_no_loss : exists last labels residual,
  run_turns (turn 1) event_obs aba_script (initial_state 2 0) = Some (last,aba_logs) /\
  allocator_inv 1 2 last /\
  aheap last (remote_head 1) = Some 8 /\ linked (fun a next => aheap last a = Some next) [8;6] 0 /\
  label_logs labels = aba_logs /\ label_taus labels = 23 /\
  finite_steps (run_nd (allocator_program 2) hemp 0) labels residual /\
  residual ~ (model_nd 2 actor_of_slot (turn 1) last
                : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  destruct aba_run_no_loss as (last & Hrun & Hinv & Hhead & Hchain & Hnd & Hp).
  destruct (run_turns_realizes_source 2 0 aba_script last aba_logs Hrun)
    as (labels & residual & Hlabels & Hlogs & Htaus & Hsteps & Htail).
  exists last, labels, residual; repeat first [assumption | split].
Qed.

End ABASafety.
