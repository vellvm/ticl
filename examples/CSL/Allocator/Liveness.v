From Stdlib Require Import List Lia Arith.PeanoNat.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Trans ICTree.Events.Writer ICTree.Events.Yield ICTree.Logic.Trace Utils.Relations.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Program
  CSL.Allocator.Model CSL.Allocator.Execution.

Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Record AExecution := {
  states : nat -> AState;
  selected : nat -> Actor;
  emitted : nat -> option SObs
}.
Definition valid_execution (capacity c : nat) (e : AExecution) : Prop :=
  states e 0 = initial_state capacity c /\
  forall k, turn 1 (selected e k) (states e k) = Some (states e (S k),emitted e k).
Definition event_is (tag : nat) (e : AExecution) (k : nat) : bool :=
  match emitted e k with None => false | Some o => Nat.eqb (stag o) tag end.
Definition pending_turn (e : AExecution) (k : nat) : bool :=
  match selected e k with
  | Owner => false
  | Remote0 => match remote0_state (states e k) with RPoll => false | _ => true end
  | Remote1 => match remote1_state (states e k) with RPoll => false | _ => true end
  end.
Definition fair (e : AExecution) : Prop :=
  forall actor, infinitely (fun k => selected e k = actor).
Definition actor_eqb (a b : Actor) : bool :=
  match a,b with Owner,Owner | Remote0,Remote0 | Remote1,Remote1 => true | _,_ => false end.
Definition owner_turn (e : AExecution) (k : nat) : bool := actor_eqb (selected e k) Owner.

(** The impossible branch is eliminated in Prop, then by False elimination.
    No existential proof is eliminated into state data and there is no fallback. *)
Definition next_valid base capacity who s (Hinv : allocator_inv base capacity s)
  : { result : (AState * option SObs)%type |
      turn base who s = Some result /\ allocator_inv base capacity (fst result) }.
Proof.
  destruct (turn base who s) as [[next event]|] eqn:Hturn.
  - exists (next,event); split; [reflexivity|].
    eapply turn_preserves_inv; eauto.
  - exfalso; destruct (turn_total base capacity who s Hinv) as (next & event & H).
    rewrite Hturn in H; discriminate.
Defined.

Fixpoint chosen_state (capacity c : nat) (picks : nat -> Actor) (k : nat)
  : { s : AState | allocator_inv 1 capacity s } :=
  match k with
  | 0 => exist _ (initial_state capacity c) (initial_state_inv capacity c)
  | S j =>
      let prior := chosen_state capacity c picks j in
      let next := next_valid 1 capacity (picks j) (proj1_sig prior) (proj2_sig prior) in
      exist _ (fst (proj1_sig next)) (proj2 (proj2_sig next))
  end.
Definition execution_of_choices (capacity c : nat) (picks : nat -> Actor) : AExecution :=
  {| states := fun k => proj1_sig (chosen_state capacity c picks k);
     selected := picks;
     emitted := fun k =>
       let prior := chosen_state capacity c picks k in
       snd (proj1_sig (next_valid 1 capacity (picks k) (proj1_sig prior) (proj2_sig prior))) |}.

Lemma execution_of_choices_valid capacity c picks :
  valid_execution capacity c (execution_of_choices capacity c picks).
Proof.
  split; [reflexivity|]; intro k.
  unfold execution_of_choices; cbn [states selected emitted chosen_state].
  destruct (next_valid 1 capacity (picks k)
    (proj1_sig (chosen_state capacity c picks k))
    (proj2_sig (chosen_state capacity c picks k))) as [[next event] [Hturn Hinv]].
  exact Hturn.
Qed.
Lemma execution_of_choices_selected capacity c picks k :
  selected (execution_of_choices capacity c picks) k = picks k.
Proof. reflexivity. Qed.

Lemma execution_inv capacity c e k :
  valid_execution capacity c e -> allocator_inv 1 capacity (states e k).
Proof.
  intros [Hinit Hstep]; induction k as [|k IH].
  - rewrite Hinit; apply initial_state_inv.
  - eapply turn_preserves_inv; [exact IH|apply Hstep].
Qed.
Lemma execution_step capacity c e k :
  valid_execution capacity c e ->
  turn 1 (selected e k) (states e k) = Some (states e (S k),emitted e k).
Proof. intros [_ H]; apply H. Qed.

Lemma actor_eqb_spec a b : actor_eqb a b = true <-> a = b.
Proof. destruct a,b; cbn [actor_eqb]; split; intro H; congruence. Qed.
Lemma owner_turn_spec e k : owner_turn e k = true <-> selected e k = Owner.
Proof. apply actor_eqb_spec. Qed.
Lemma event_is_spec tag e k :
  event_is tag e k = true <-> exists block idx, emitted e k = Some (SPop tag block idx).
Proof.
  unfold event_is; destruct (emitted e k) as [[kind block idx]|] eqn:E; cbn.
  - rewrite Nat.eqb_eq; split.
    + intro H; subst kind; now exists block, idx.
    + intros (b & i & H); inversion H; reflexivity.
  - split; [discriminate|intros (b & i & H); discriminate].
Qed.

Lemma execution_event_index capacity c e k o :
  valid_execution capacity c e -> emitted e k = Some o ->
  acount (states e (S k)) = S (acount (states e k)) /\ sidx o = acount (states e k).
Proof.
  intros Hvalid Hobs.
  pose proof (turn_counter 1 (selected e k) (states e k) (states e (S k))
    (emitted e k) (execution_step capacity c e k Hvalid)) as H.
  now rewrite Hobs in H.
Qed.
Lemma execution_counter_mono capacity c e lo hi :
  valid_execution capacity c e -> lo <= hi -> acount (states e lo) <= acount (states e hi).
Proof.
  intros Hvalid Hle.
  assert (Hstep : forall k, acount (states e k) <= acount (states e (S k))).
  {
    intro k; pose proof (turn_counter 1 (selected e k) (states e k) (states e (S k))
      (emitted e k) (execution_step capacity c e k Hvalid)) as H.
    destruct (emitted e k); cbn in H; intuition lia.
  }
  induction Hle as [|hi Hle IH]; [lia|specialize (Hstep hi); lia].
Qed.
Lemma execution_event_order capacity c e k j o p :
  valid_execution capacity c e -> k < j ->
  emitted e k = Some o -> emitted e j = Some p -> sidx o < sidx p.
Proof.
  intros Hvalid Hkj Ho Hp.
  pose proof (execution_event_index capacity c e k o Hvalid Ho) as [Hk Hi].
  pose proof (execution_event_index capacity c e j p Hvalid Hp) as [Hj Hjidx].
  pose proof (execution_counter_mono capacity c e (S k) j Hvalid ltac:(lia)); lia.
Qed.

Lemma execution_run_turns capacity c e lo len :
  valid_execution capacity c e ->
  run_turns 1 (List.map (selected e) (List.seq lo len)) (states e lo) =
    Some (states e (lo + len),
      List.flat_map (fun k => event_obs (emitted e k)) (List.seq lo len)).
Proof.
  intro Hvalid; revert lo; induction len as [|len IH]; intro lo.
  - cbn [List.seq List.map run_turns List.flat_map]; now rewrite Nat.add_0_r.
  - cbn [List.seq List.map run_turns List.flat_map].
    rewrite (execution_step capacity c e lo Hvalid), IH.
    replace (S lo + len) with (lo + S len) by lia.
    destruct (emitted e lo); reflexivity.
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
Definition contention_pending (who : Actor) (s : AState) : bool :=
  match who with
  | Owner => false
  | Remote0 => match remote0_state s with RPoll => false | _ => true end
  | Remote1 => match remote1_state s with RPoll => false | _ => true end
  end.
Definition contention_tag (kind : nat) (event : option SObs) : bool :=
  match event with None => false | Some o => Nat.eqb (stag o) kind end.

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
  cbn [contention_pending contention_tag stag tag_alloc tag_retire
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
  contention_tag tag_retire event = false ->
  (if contention_pending who s then 1 else 0) + contention_pending_rank t <=
    contention_pending_rank s /\
  (if contention_tag tag_retry event then 1 else 0) + contention_failure_rank t <=
    contention_failure_rank s.
Proof.
  destruct s as [h count op p0 p1].
  cbn [allocator_inv aheap acount owner_state remote0_state remote1_state].
  intros (Hbase & Hback & L & R & D & m0 & m1 & Hr & Hl & Hd & CL & CR & CD &
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
      * cbn [free_chain] in CD; destruct CD as [Hnext CD].
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
           ++ cbn [free_chain] in CL; destruct CL as [Hnext CL].
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
           ++ cbn [free_chain] in CL; destruct CL as [Hnext CL].
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
  valid_execution capacity c e -> event_is tag_retire e k = false ->
  (if pending_turn e k then 1 else 0) + contention_pending_rank (states e (S k)) <=
    contention_pending_rank (states e k) /\
  (if event_is tag_retry e k then 1 else 0) + contention_failure_rank (states e (S k)) <=
    contention_failure_rank (states e k).
Proof.
  intros Hvalid Hnone.
  exact (turn_contention_ranks capacity (selected e k) (states e k)
    (states e (S k)) (emitted e k) (execution_inv capacity c e k Hvalid)
    (execution_step capacity c e k Hvalid) Hnone).
Qed.

Lemma no_publication_contention_potential capacity c e lo len :
  valid_execution capacity c e ->
  (forall k, lo <= k < lo + len -> event_is tag_retire e k = false) ->
  count_if (pending_turn e) lo len + contention_pending_rank (states e (lo + len)) <=
    contention_pending_rank (states e lo) /\
  count_if (event_is tag_retry e) lo len + contention_failure_rank (states e (lo + len)) <=
    contention_failure_rank (states e lo).
Proof.
  intros Hvalid; revert lo; induction len as [|len IH]; intros lo Hnone.
  - rewrite !count_if_zero, Nat.add_0_r; cbn; split; lia.
  - destruct (execution_contention_ranks capacity c e lo Hvalid
      (Hnone lo ltac:(lia))) as [Hpending Hfailure].
    destruct (IH (S lo) ltac:(intros k Hk; apply Hnone; lia)) as [IHpending IHfailure].
    rewrite !count_if_succ.
    replace (lo + S len) with (S lo + len) by lia.
    split; lia.
Qed.

(** Only a failed remote CAS emits [tag_retry].  Its unit stale-bit charge
    proves the four-failure bound independently of the number of idle turns. *)
Theorem no_publication_failed_cas_bound capacity c e lo len :
  valid_execution capacity c e ->
  (forall k, lo <= k < lo + len -> event_is tag_retire e k = false) ->
  count_if (event_is tag_retry e) lo len <= 4.
Proof.
  intros Hvalid Hnone.
  destruct (no_publication_contention_potential capacity c e lo len Hvalid Hnone)
    as [_ Hbound].
  pose proof (contention_failure_rank_bound (states e lo)); lia.
Qed.

Theorem no_publication_pending_bound capacity c e lo len :
  valid_execution capacity c e ->
  (forall k, lo <= k < lo + len -> event_is tag_retire e k = false) ->
  count_if (pending_turn e) lo len <= 16.
Proof.
  intros Hvalid Hnone.
  destruct (no_publication_contention_potential capacity c e lo len Hvalid Hnone)
    as [Hbound _].
  pose proof (contention_pending_rank_bound (states e lo)); lia.
Qed.



Theorem remote_free_lockfree capacity c e :
  valid_execution capacity c e ->
  infinitely (fun k => pending_turn e k = true) ->
  infinitely (fun k => event_is tag_retire e k = true).
Proof.
  intros Hvalid Hpending lo.
  destruct (infinitely_count_if (pending_turn e) Hpending 17 lo) as [len Hmany].
  destruct (finite_bool_search (event_is tag_retire e) lo len)
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

Record SourceExecution := {
  source_pools : nat -> pool sE 3;
  source_states : nat -> SSig;
  source_selected : nat -> Actor;
  source_emitted : nat -> list SObs
}.
Definition valid_source_execution (capacity c : nat) (se : SourceExecution) : Prop :=
  pool_equ (source_pools se 0) (source_pool0 1) /\
  source_states se 0 = (page_heap 1 capacity hemp,c) /\
  forall k, exists residual,
    ThreadSegment (source_pools se k $ slot_of_actor (source_selected se k))
      (source_states se k) (source_emitted se k) residual (source_states se (S k)) /\
    pool_equ (source_pools se (S k))
      (source_pools se k @ slot_of_actor (source_selected se k) := residual).

(** A source scheduler records a physical branch slot, not an observation
    guessed to identify its actor.  Both inverse laws preserve that witness. *)
Definition source_execution_of_slots
  (pools : nat -> pool sE 3) (sigmas : nat -> SSig)
  (slots : nat -> Fin.t 3) (logs : nat -> list SObs) : SourceExecution :=
  {| source_pools := pools; source_states := sigmas;
     source_selected := fun k => actor_of_slot (slots k); source_emitted := logs |}.

Lemma source_execution_of_slots_selected pools sigmas slots logs k :
  slot_of_actor (source_selected (source_execution_of_slots pools sigmas slots logs) k) = slots k.
Proof. apply slot_of_actor_of_slot. Qed.

Theorem source_execution_of_slots_valid capacity c pools sigmas slots logs :
  pool_equ (pools 0) (source_pool0 1) ->
  sigmas 0 = (page_heap 1 capacity hemp,c) ->
  (forall k, exists residual,
    ThreadSegment (pools k $ slots k) (sigmas k) (logs k) residual (sigmas (S k)) /\
    pool_equ (pools (S k)) (pools k @ slots k := residual)) ->
  valid_source_execution capacity c (source_execution_of_slots pools sigmas slots logs).
Proof.
  intros Hpool Hstate Hsteps; split; [exact Hpool|]; split; [exact Hstate|].
  intro k; cbn [source_execution_of_slots source_selected source_pools source_states source_emitted].
  rewrite slot_of_actor_of_slot; apply Hsteps.
Qed.


Theorem source_execution_complete capacity c se :
  valid_source_execution capacity c se ->
  let e := execution_of_choices capacity c (source_selected se) in
  valid_execution capacity c e /\
  (forall k, state_agrees (source_states se k) (states e k) /\
    pool_guard_equ (source_pools se k) (allocator_pool 1 (states e k))) /\
  (forall k, source_emitted se k = event_obs (emitted e k)) /\
  (forall k, selected e k = source_selected se k).
Proof.
  intros (Hpool0 & Hstate0 & Hsegments) e.
  pose proof (execution_of_choices_valid capacity c (source_selected se)) as Hvalid.
  change (valid_execution capacity c e) in Hvalid.
  assert (Haligned : forall k,
    state_agrees (source_states se k) (states e k) /\
    pool_guard_equ (source_pools se k) (allocator_pool 1 (states e k))).
  {
    intro k; induction k as [|k [Hstate Hpool]].
    - split.
      + rewrite Hstate0; split; [apply heq_refl|reflexivity].
      + eapply source_pool_equ_guard_trans; [exact Hpool0|].
        apply execution_pool_guard_equ, source_pool0_initial.
    - destruct (Hsegments k) as (residual & Hsegment & Hnextpool).
      pose proof (execution_step capacity c e k Hvalid) as Hturn.
      change (turn 1 (source_selected se k) (states e k) =
        Some (states e (S k),emitted e k)) in Hturn.
      destruct (selected_source_segment_exact 1 capacity (source_pools se k)
        (source_states se k) (states e k) (source_selected se k)
        (states e (S k)) (emitted e k) (source_emitted se k)
        residual (source_states se (S k)) Hpool Hstate
        (execution_inv capacity c e k Hvalid) Hturn Hsegment)
        as (_ & Hstate' & Hresidual).
      split; [exact Hstate'|].
      eapply source_pool_equ_guard_trans; [exact Hnextpool|].
      eapply selected_source_pool_update; eassumption.
  }
  split; [exact Hvalid|]; split; [exact Haligned|]; split.
  - intro k; destruct (Haligned k) as [Hstate Hpool].
    destruct (Hsegments k) as (residual & Hsegment & _).
    pose proof (execution_step capacity c e k Hvalid) as Hturn.
    change (turn 1 (source_selected se k) (states e k) =
      Some (states e (S k),emitted e k)) in Hturn.
    exact (proj1 (selected_source_segment_exact 1 capacity (source_pools se k)
      (source_states se k) (states e k) (source_selected se k)
      (states e (S k)) (emitted e k) (source_emitted se k)
      residual (source_states se (S k)) Hpool Hstate
      (execution_inv capacity c e k Hvalid) Hturn Hsegment)).
  - intro k; reflexivity.
Qed.

(** Finite raw-source reachability has no model premise.  It is useful before
    an infinite schedule is supplied: every physical slot remains selectable. *)
Inductive ReachableSourcePool (capacity c : nat) : pool sE 3 -> SSig -> Prop :=
| source_reachable_initial ts :
    pool_equ ts (source_pool0 1) ->
    ReachableSourcePool capacity c ts (page_heap 1 capacity hemp,c)
| source_reachable_step ts sigma (i : Fin.t 3) logs residual sigma' ts' :
    ReachableSourcePool capacity c ts sigma ->
    ThreadSegment (ts $ i) sigma logs residual sigma' ->
    pool_equ ts' (ts @ i := residual) ->
    ReachableSourcePool capacity c ts' sigma'.

Lemma reachable_source_alignment capacity c ts sigma :
  ReachableSourcePool capacity c ts sigma ->
  exists s, allocator_inv 1 capacity s /\ state_agrees sigma s /\
    pool_guard_equ ts (allocator_pool 1 s).
Proof.
  intro H; induction H as
    [ts E|ts sigma i logs residual sigma' ts' Hreach IH Hseg E].
  - exists (initial_state capacity c); split; [apply initial_state_inv|]; split.
    + split; [apply heq_refl|reflexivity].
    + eapply source_pool_equ_guard_trans; [exact E|].
      apply execution_pool_guard_equ, source_pool0_initial.
  - destruct IH as (s & Hinv & Hagree & Hpool).
    rewrite <- (slot_of_actor_of_slot i) in Hseg, E.
    destruct (selected_source_segment_turn 1 capacity ts sigma s (actor_of_slot i)
      logs residual sigma' Hpool Hagree Hinv Hseg)
      as (next & event & Hturn & Hlogs & Hstate & Htail).
    exists next; split; [eapply turn_preserves_inv; eassumption|]; split;
      [exact Hstate|].
    eapply source_pool_equ_guard_trans; [exact E|].
    eapply selected_source_pool_update; eassumption.
Qed.

Lemma source_execution_reachable capacity c se k :
  valid_source_execution capacity c se ->
  ReachableSourcePool capacity c (source_pools se k) (source_states se k).
Proof.
  intros (Hp & Hs & Hsteps); induction k as [|k IH].
  - rewrite Hs; now apply source_reachable_initial.
  - destruct (Hsteps k) as (residual & Hseg & E).
    eapply source_reachable_step; eassumption.
Qed.


Lemma source_pool0_branchfree i : BranchFree (source_pool0 1 $ i).
Proof.
  rewrite <- (slot_of_actor_of_slot i); destruct (actor_of_slot i);
    cbn [source_pool0 slot_of_actor Vector.nth]; apply denote_branchfree.
Qed.

Lemma reachable_source_branchfree capacity c ts sigma :
  ReachableSourcePool capacity c ts sigma -> forall i, BranchFree (ts $ i).
Proof.
  intro H; induction H as
    [ts E|ts sigma i logs residual sigma' ts' Hreach IH Hseg E]; intro j.
  - eapply branchfree_equ_impl; [symmetry; apply E|apply source_pool0_branchfree].
  - eapply branchfree_equ_impl; [symmetry; apply E|].
    destruct (Fin.eq_dec j i) as [->|Hne].
    + rewrite Vector.nth_replace_eq; eapply ThreadSegment_branchfree; eauto.
    + rewrite Vector.nth_replace_neq by congruence; apply IH.
Qed.

Theorem every_reachable_source_slot_yields capacity c ts sigma (i : Fin.t 3) :
  ReachableSourcePool capacity c ts sigma ->
  BranchFree (ts $ i) /\
  (exists logs residual sigma', ThreadSegment (ts $ i) sigma logs residual sigma') /\
  not (guard_equ (ts $ i) (Ret tt)) /\
  (forall k : bool -> thread sE, ~ guard_equ (ts $ i) (Vis (inr (inl Fork)) k)) /\
  (forall n (k : Fin.t (S n) -> thread sE), ~ guard_equ (ts $ i) (Br n k)) /\
  not (guard_equ (ts $ i) (stuck : thread sE)) /\
  not (guard_equ (ts $ i) (spin : thread sE)).
Proof.
  intro Hreach; split; [eapply reachable_source_branchfree; exact Hreach|].
  destruct (reachable_source_alignment capacity c ts sigma Hreach)
    as (s & Hinv & Hstate & Hpool).
  rewrite <- (slot_of_actor_of_slot i).
  split; [eapply initialized_worker_next_yield; eassumption|].
  destruct (initialized_worker_no_terminal_prefix 1 capacity ts sigma s
    (actor_of_slot i) Hpool Hstate Hinv) as (Hr & Hf & Hb & Hstuck).
  destruct (initialized_worker_no_fault_or_divergence 1 capacity ts sigma s
    (actor_of_slot i) Hpool Hstate Hinv) as (_ & Hspin & _).
  repeat split; assumption.
Qed.

(** The raw scheduler presents all three physical choices, including idle
    polls.  Its scheduling Yield is erased, whereas the following Br contributes
    a genuine tau transition.  Focus is retained through all source effects. *)

Lemma source_scheduler_choice_inv (ts : pool sE 3) l next :
  trans l (Br 2 (fun i => schedule 3 ts (Some i))) next ->
  exists who, l = tau /\ next ≅ schedule 3 ts (Some (slot_of_actor who)).
Proof.
  intro H; apply trans_br_inv in H as (i & E & ->).
  exists (actor_of_slot i); split; [reflexivity|].
  rewrite slot_of_actor_of_slot; exact E.
Qed.








Lemma model_turn_finite_steps base who s next event :
  turn base who s = Some (next,event) ->
  finite_steps (model_nd base s) (turn_labels event) (Guard (model_nd base next)).
Proof.
  intro Hturn; destruct event as [o|]; cbn [turn_labels].
  - eapply finite_steps_cons with
      (u := Vis (Log o) (fun _ => Guard (model_nd base next))).
    + rewrite (unfold_model_nd base s).
      eapply trans_br with (x := slot_of_actor who).
      rewrite actor_of_slot_of_actor, Hturn; reflexivity.
    + econstructor;
        [exact (@trans_vis (writerE SObs) _ (unit * SSig) (Log o) tt
          (fun _ => Guard (model_nd base next)))|constructor].
  - econstructor; [|constructor].
    rewrite (unfold_model_nd base s).
    eapply trans_br with (x := slot_of_actor who).
    rewrite actor_of_slot_of_actor, Hturn; reflexivity.
Qed.

CoInductive realizes (e : AExecution) (k : nat)
  (t : ictreeW SObs (unit * SSig)) : Prop :=
| realizes_next next :
    finite_steps t (turn_labels (emitted e k)) next ->
    realizes e (S k) next -> realizes e k t.

Lemma valid_execution_realizes_model capacity c e :
  valid_execution capacity c e ->
  forall k t, t ~ model_nd 1 (states e k) -> realizes e k t.
Proof.
  intro Hvalid; cofix CIH; intros k t E.
  pose proof (model_turn_finite_steps 1 (selected e k) (states e k)
    (states e (S k)) (emitted e k)
    (execution_step capacity c e k Hvalid)) as Hmodel.
  assert (Esym : model_nd 1 (states e k) ~ t) by (symmetry; exact E).
  destruct (finite_steps_sbisim _ _ _ Hmodel t Esym)
    as (next & Hsteps & Enext).
  eapply realizes_next; [exact Hsteps|].
  apply CIH; transitivity (Guard (model_nd 1 (states e (S k))));
    [symmetry; exact Enext|apply sb_guard].
Qed.

Theorem valid_execution_realizes_source capacity c e :
  valid_execution capacity c e ->
  realizes e 0 (run_nd (allocator_program capacity) hemp c).
Proof.
  intro Hvalid; eapply valid_execution_realizes_model; [exact Hvalid|].
  rewrite (proj1 Hvalid); apply run_nd_allocator_bisim.
Qed.

(** Labels retain their interleaving: exactly one scheduling tau per actual
    turn, followed by its zero or one source observation. *)
Fixpoint run_turn_labels (base : nat) (script : list Actor) (s : AState)
  : option (list (@label (writerE SObs) _)) :=
  match script with
  | [] => Some []
  | who :: rest =>
      match turn base who s with
      | None => None
      | Some (next,event) =>
          match run_turn_labels base rest next with
          | None => None
          | Some labels => Some (turn_labels event ++ labels)
          end
      end
  end.

Lemma run_turns_labels base script : forall s last logs,
  run_turns base script s = Some (last,logs) ->
  exists labels, run_turn_labels base script s = Some labels /\
    label_logs labels = logs /\ label_taus labels = List.length script /\
    exists residual, finite_steps (model_nd base s) labels residual /\
      residual ~ model_nd base last.
Proof.
  induction script as [|who rest IH]; intros s last logs Hrun.
  - cbn [run_turns] in Hrun; inversion Hrun; subst last logs.
    exists []; repeat split; try reflexivity.
    exists (model_nd base s); split; [constructor|reflexivity].
  - cbn [run_turns] in Hrun.
    destruct (turn base who s) as [[next event]|] eqn:Hturn; [|discriminate].
    destruct (run_turns base rest next) as [[last' logs']|] eqn:Hrest; [|discriminate].
    inversion Hrun; subst last logs; clear Hrun.
    destruct (IH next last' logs' Hrest)
      as (labels & Hlabels & Hlogs & Htaus & residual & Hsteps & Eresidual).
    exists (turn_labels event ++ labels); split.
    + cbn [run_turn_labels]; rewrite Hturn, Hlabels; reflexivity.
    + split.
      * unfold label_logs in *; rewrite List.flat_map_app, Hlogs.
        destruct event; reflexivity.
      * split.
        -- unfold label_taus in *; rewrite List.filter_app, List.length_app, Htaus.
           destruct event; reflexivity.
        -- assert (Eguard : model_nd base next ~ Guard (model_nd base next)).
           { symmetry; apply sb_guard. }
           destruct (finite_steps_sbisim _ _ _ Hsteps _ Eguard)
             as (residual' & Hsteps' & Eresidual').
           exists residual'; split.
           ++ eapply finite_steps_app; [eapply model_turn_finite_steps; exact Hturn|exact Hsteps'].
           ++ transitivity residual; [symmetry; exact Eresidual'|exact Eresidual].
Qed.

Theorem run_turns_realizes_source capacity c script last logs :
  run_turns 1 script (initial_state capacity c) = Some (last,logs) ->
  exists labels residual,
    run_turn_labels 1 script (initial_state capacity c) = Some labels /\
    label_logs labels = logs /\ label_taus labels = List.length script /\
    finite_steps (run_nd (allocator_program capacity) hemp c) labels residual /\
    residual ~ model_nd 1 last.
Proof.
  intro Hrun; destruct (run_turns_labels 1 script (initial_state capacity c)
    last logs Hrun) as (labels & Hlabels & Hlogs & Htaus & model & Hsteps & Emodel).
  pose proof (run_nd_allocator_bisim capacity c) as Esource; symmetry in Esource.
  destruct (finite_steps_sbisim _ _ _ Hsteps _ Esource)
    as (residual & Hsource & Eresidual).
  exists labels, residual; repeat split; try assumption.
  transitivity model; [symmetry; exact Eresidual|exact Emodel].
Qed.


Theorem valid_source_execution_scheduler_steps capacity c se k :
  valid_source_execution capacity c se ->
  exists next,
    finite_steps (interp_nd 3 (source_pools se k) None (source_states se k))
      (tau :: List.map (fun o => obs (Log o) tt) (source_emitted se k)) next /\
    next ~ interp_nd 3 (source_pools se (S k)) None (source_states se (S k)).
Proof.
  intros (_ & _ & Hsteps); destruct (Hsteps k) as (residual & Hseg & Epool).
  eapply source_segment_scheduler_steps; eassumption.
Qed.

Definition source_pending capacity c se k : bool :=
  pending_turn (execution_of_choices capacity c (source_selected se)) k.

(** A pending raw remote is one of the actual continuations after mailbox
    pickup, and before remote_free returns through the successful CAS path.
    This predicate mentions neither a model execution nor future publication. *)
Definition raw_remote_pending base client (t : thread sE) : Prop :=
  exists pc, pc <> RPoll /\ guard_equ t (remote_residual base client pc).
Definition selected_source_pending (se : SourceExecution) k : Prop :=
  match source_selected se k with
  | Owner => False
  | Remote0 => raw_remote_pending 1 false (source_pools se k $ slot_of_actor Remote0)
  | Remote1 => raw_remote_pending 1 true (source_pools se k $ slot_of_actor Remote1)
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

Theorem source_pending_raw_spec capacity c se k :
  valid_source_execution capacity c se ->
  (source_pending capacity c se k = true <-> selected_source_pending se k).
Proof.
  intro Hvalid; destruct (source_execution_complete capacity c se Hvalid)
    as (_ & Haligned & _).
  destruct (Haligned k) as [_ Hpool].
  unfold source_pending, pending_turn; rewrite execution_of_choices_selected.
  unfold selected_source_pending; destruct (source_selected se k).
  - split; [discriminate|contradiction].
  - symmetry; apply raw_remote_pending_alignment.
    exact (Hpool (slot_of_actor Remote0)).
  - symmetry; apply raw_remote_pending_alignment.
    exact (Hpool (slot_of_actor Remote1)).
Qed.

Lemma execution_of_choices_prefix capacity c picks other k :
  (forall j, j < k -> picks j = other j) ->
  states (execution_of_choices capacity c picks) k =
    states (execution_of_choices capacity c other) k.
Proof.
  induction k as [|k IH]; intro Hprefix; [reflexivity|].
  assert (E : states (execution_of_choices capacity c picks) k =
    states (execution_of_choices capacity c other) k).
  { apply IH; intros j Hj; apply Hprefix; lia. }
  pose proof (execution_step capacity c (execution_of_choices capacity c picks) k
    (execution_of_choices_valid capacity c picks)) as Hp.
  pose proof (execution_step capacity c (execution_of_choices capacity c other) k
    (execution_of_choices_valid capacity c other)) as Hq.
  rewrite execution_of_choices_selected in Hp, Hq.
  rewrite E, (Hprefix k ltac:(lia)), Hq in Hp; now inversion Hp.
Qed.

Lemma source_pending_finite_history capacity c se other k :
  (forall j, j <= k -> source_selected se j = source_selected other j) ->
  source_pending capacity c se k = source_pending capacity c other k.
Proof.
  intro Hprefix; unfold source_pending, pending_turn.
  rewrite !execution_of_choices_selected.
  rewrite (Hprefix k ltac:(lia)).
  rewrite (execution_of_choices_prefix capacity c (source_selected se)
    (source_selected other) k ltac:(intros j Hj; apply Hprefix; lia)).
  reflexivity.
Qed.

Definition source_has_event (kind block : nat) (se : SourceExecution) (k : nat) : Prop :=
  exists idx, List.In (SPop kind block idx) (source_emitted se k).

Theorem source_remote_free_lockfree capacity c se :
  valid_source_execution capacity c se ->
  infinitely (fun k => source_pending capacity c se k = true) ->
  infinitely (fun k => exists block, source_has_event tag_retire block se k).
Proof.
  intros Hvalid Hpending.
  destruct (source_execution_complete capacity c se Hvalid)
    as (Hmodel & Haligned & Hlogs & Hselected).
  pose proof (remote_free_lockfree capacity c
    (execution_of_choices capacity c (source_selected se)) Hmodel Hpending) as Hlive.
  intro n; destruct (Hlive n) as (k & Hnk & Hevent).
  apply event_is_spec in Hevent as (block & idx & Hevent).
  exists k; split; [exact Hnk|]; exists block, idx.
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

(* The ghost lists are witnesses of the existing invariant, not additional
   executable state.  They are used only inside propositions. *)
Definition owner_lists (capacity : nat) (s : AState) (L R D : list nat) : Prop :=
  0 < 1 /\ backing 1 capacity (aheap s) /\
  exists m0 m1,
    aheap s (remote_head 1) = Some (List.hd 0 R) /\
    aheap s (local_head 1) = Some (List.hd 0 L) /\
    aheap s (drain_head 1) = Some (List.hd 0 D) /\
    free_chain (aheap s) L /\ free_chain (aheap s) R /\ free_chain (aheap s) D /\
    aheap s (mailbox 1 false) = Some m0 /\
    aheap s (mailbox 1 true) = Some m1 /\
    Permutation (L ++ R ++ D ++ mailbox_nodes m0 ++ mailbox_nodes m1 ++
      held (remote0_state s) ++ held (remote1_state s)) (page_blocks 1 capacity) /\
    (match owner_state s with ODrain => True | _ => D = [] end) /\
    (match owner_state s with OCAS old => old = 0 \/ In old (page_blocks 1 capacity)
       | _ => True end) /\
    cached_remote 1 capacity (aheap s) (remote0_state s) /\
    cached_remote 1 capacity (aheap s) (remote1_state s).

Lemma owner_lists_inv capacity s L R D :
  owner_lists capacity s L R D -> allocator_inv 1 capacity s.
Proof.
  intros (Hb & Hback & m0 & m1 & H).
  split; [exact Hb|]; split; [exact Hback|].
  exists L, R, D, m0, m1; exact H.
Qed.
Lemma inv_owner_lists capacity s :
  allocator_inv 1 capacity s -> exists L R D, owner_lists capacity s L R D.
Proof.
  intros (Hb & Hback & L & R & D & m0 & m1 & H).
  exists L, R, D; split; [exact Hb|]; split; [exact Hback|].
  exists m0, m1; exact H.
Qed.
Lemma owner_lists_lengths capacity s L R D :
  owner_lists capacity s L R D -> List.length L + List.length R + List.length D <= capacity.
Proof.
  intros (_ & _ & m0 & m1 & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
  apply Permutation_length in Hp.
  repeat rewrite List.length_app in Hp.
  rewrite page_blocks_length in Hp; lia.
Qed.
Lemma owner_lists_disjoint capacity s L R D b :
  owner_lists capacity s L R D -> In b (R ++ D) -> ~ In b L.
Proof.
  intros (_ & _ & m0 & m1 & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _) Hrd Hl.
  pose proof (ai_partition_count 1 capacity _ Hp b) as Hcount.
  repeat rewrite List.count_occ_app in Hcount.
  apply (proj1 (List.count_occ_In Nat.eq_dec L b)) in Hl.
  rewrite List.in_app_iff in Hrd; destruct Hrd as [Hr|Hd].
  - apply (proj1 (List.count_occ_In Nat.eq_dec R b)) in Hr; lia.
  - apply (proj1 (List.count_occ_In Nat.eq_dec D b)) in Hd; lia.
Qed.

Definition owner_after_offer (client : bool) := if client then ORead else OOffer true.
Definition owner_weight (who : Actor) : nat := match who with Owner => 1 | _ => 0 end.
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
Definition block_event (tag block : nat) (event : option SObs) : Prop :=
  exists idx, event = Some (SPop tag block idx).

(* Every constructor below is a projection of an actual executable turn.
   In particular detach uses the current R, and publication prepends to R. *)
Inductive ownership_transition :
  Actor -> owner_pc -> owner_pc -> option SObs ->
  list nat -> list nat -> list nat -> list nat -> list nat -> list nat -> Prop :=
| ownership_read L R :
    ownership_transition Owner ORead (OCAS (List.hd 0 R)) None L R [] L R []
| ownership_cas_fail old L R :
    List.hd 0 R <> old ->
    ownership_transition Owner (OCAS old) ORead None L R [] L R []
| ownership_detach L R :
    ownership_transition Owner (OCAS (List.hd 0 R)) ODrain None L R [] L [] R
| ownership_drain_empty L R :
    ownership_transition Owner ODrain (OOffer false) None L R [] L R []
| ownership_drain L R b D idx :
    ownership_transition Owner ODrain ODrain (Some (SPop tag_reclaim b idx))
      L R (b :: D) (b :: L) R D
| ownership_offer_empty client L R :
    ownership_transition Owner (OOffer client) (owner_after_offer client) None
      L R [] L R []
| ownership_offer client L R b idx :
    ownership_transition Owner (OOffer client) (owner_after_offer client)
      (Some (SPop tag_alloc b idx)) (b :: L) R [] L R []
| ownership_remote who pc event L R D :
    who <> Owner ->
    (event = None \/ exists b idx, event = Some (SPop tag_retry b idx)) ->
    ownership_transition who pc pc event L R D L R D
| ownership_publish who pc L R D b idx :
    who <> Owner ->
    ownership_transition who pc pc (Some (SPop tag_retire b idx))
      L R D L (b :: R) D.

Local Ltac owner_finish T h L R D m0 m1 :=
  cbn [aheap acount owner_state remote0_state remote1_state] in *;
  try rewrite Nat.eqb_refl in T;
  repeat match goal with
  | E : Nat.eqb _ _ = _ |- _ => progress rewrite E in T
  end;
  inversion T; subst; clear T;
  exists L, R, D; split;
  [ unfold owner_lists;
    cbn [aheap acount owner_state remote0_state remote1_state];
    split; [assumption|]; split; [ai_backing|];
    exists m0, m1; cbn [List.hd held]; repeat split; ai_obligation h
  | cbn [owner_state];
    first [apply ownership_read | apply ownership_detach |
      apply ownership_drain_empty | apply ownership_drain |
      apply ownership_offer_empty | apply ownership_offer |
      apply ownership_cas_fail; now apply Nat.eqb_neq |
      apply ownership_publish; discriminate |
      apply ownership_remote; [discriminate|left; reflexivity] |
      apply ownership_remote; [discriminate|right; do 2 eexists; reflexivity]] ].

Lemma owner_lists_step capacity who s t event L R D :
  owner_lists capacity s L R D -> turn 1 who s = Some (t,event) ->
  exists L' R' D', owner_lists capacity t L' R' D' /\
    ownership_transition who (owner_state s) (owner_state t) event L R D L' R' D'.
Proof.
  destruct s as [h count op p0 p1].
  cbn [owner_lists aheap acount owner_state remote0_state remote1_state].
  intros (Hbase & Hback & m0 & m1 & Hr & Hl & Hd & CL & CR & CD &
    Hm0 & Hm1 & Hp & Hop & Ho & Hc0 & Hc1) T.
  cbn [aheap acount owner_state remote0_state remote1_state] in *.
  destruct who.
  - destruct op as [|old| |client].
    + cbn in Hop; subst D. contention_reduce_turn T; rewrite Hr in T.
      owner_finish T h L R (@nil nat) m0 m1.
    + cbn in Hop; subst D. contention_reduce_turn T; rewrite Hr in T.
      destruct (Nat.eqb (List.hd 0 R) old) eqn:Ecas.
      * apply Nat.eqb_eq in Ecas; subst old.
        try rewrite Nat.eqb_refl in T.
        rewrite upd_neq in T by ai_distinct; rewrite Hd in T.
        owner_finish T h L (@nil nat) R m0 m1.
      * try rewrite Ecas in T. owner_finish T h L R (@nil nat) m0 m1.
    + destruct D as [|b D].
      * contention_reduce_turn T; rewrite Hd in T; cbn [List.hd Nat.eqb] in T.
        owner_finish T h L R (@nil nat) m0 m1.
      * cbn [free_chain] in CD; destruct CD as [Hnext CD].
        assert (Eb : Nat.eqb b 0 = false) by (apply Nat.eqb_neq; ai_distinct).
        contention_reduce_turn T; rewrite Hd in T; cbn [List.hd] in T;
          rewrite Eb, Hnext, Hl in T.
        owner_finish T h (b :: L) R D m0 m1.
    + cbn in Hop; subst D; destruct client.
      * destruct m1 as [|m1].
        -- destruct L as [|b L ].
           ++ contention_reduce_turn T; rewrite Hm1 in T; cbn [Nat.eqb] in T;
                rewrite Hl in T; cbn [List.hd Nat.eqb] in T.
              owner_finish T h (@nil nat) R (@nil nat) m0 0.
           ++ cbn [free_chain] in CL; destruct CL as [Hnext CL].
              assert (Eb : Nat.eqb b 0 = false) by (apply Nat.eqb_neq; ai_distinct).
              contention_reduce_turn T; rewrite Hm1 in T; cbn [Nat.eqb] in T;
                rewrite Hl in T; cbn [List.hd] in T; rewrite Eb, Hnext in T.
              owner_finish T h L R (@nil nat) m0 b.
        -- contention_reduce_turn T; rewrite Hm1 in T; cbn [Nat.eqb] in T.
           owner_finish T h L R (@nil nat) m0 (S m1).
      * destruct m0 as [|m0].
        -- destruct L as [|b L ].
           ++ contention_reduce_turn T; rewrite Hm0 in T; cbn [Nat.eqb] in T;
                rewrite Hl in T; cbn [List.hd Nat.eqb] in T.
              owner_finish T h (@nil nat) R (@nil nat) 0 m1.
           ++ cbn [free_chain] in CL; destruct CL as [Hnext CL].
              assert (Eb : Nat.eqb b 0 = false) by (apply Nat.eqb_neq; ai_distinct).
              contention_reduce_turn T; rewrite Hm0 in T; cbn [Nat.eqb] in T;
                rewrite Hl in T; cbn [List.hd] in T; rewrite Eb, Hnext in T.
              owner_finish T h L R (@nil nat) b m1.
        -- contention_reduce_turn T; rewrite Hm0 in T; cbn [Nat.eqb] in T.
           owner_finish T h L R (@nil nat) (S m0) m1.
  - destruct p0 as [|b|b old|b old].
    + destruct m0 as [|m0].
      * contention_reduce_turn T; rewrite Hm0 in T; cbn [Nat.eqb] in T.
        owner_finish T h L R D 0 m1.
      * assert (Hcell : exists v, h (S (S m0)) = Some v).
        { eapply ai_backing_present; [exact Hback|ai_interval]. }
        destruct Hcell as [v Hv].
        contention_reduce_turn T; rewrite Hm0 in T; cbn [Nat.eqb] in T.
        rewrite upd_neq in T by ai_distinct; rewrite Hv in T.
        owner_finish T h L R D 0 m1.
    + contention_reduce_turn T; rewrite Hr in T. owner_finish T h L R D m0 m1.
    + cbn [cached_remote] in Hc0; destruct Hc0 as [Hbound Hneq].
      assert (Hcell : exists v, h b = Some v).
      { eapply ai_backing_present; [exact Hback|ai_interval]. }
      destruct Hcell as [v Hv]. contention_reduce_turn T; rewrite Hv in T.
      owner_finish T h L R D m0 m1.
    + cbn [cached_remote] in Hc0; destruct Hc0 as [Hbound [Hneq Hlink]].
      contention_reduce_turn T; rewrite Hr in T.
      destruct (Nat.eqb (List.hd 0 R) old) eqn:Ecas.
      * apply Nat.eqb_eq in Ecas; subst old; try rewrite Nat.eqb_refl in T.
        owner_finish T h L (b :: R) D m0 m1.
      * try rewrite Ecas in T. owner_finish T h L R D m0 m1.
  - destruct p1 as [|b|b old|b old].
    + destruct m1 as [|m1].
      * contention_reduce_turn T; rewrite Hm1 in T; cbn [Nat.eqb] in T.
        owner_finish T h L R D m0 0.
      * assert (Hcell : exists v, h (S (S m1)) = Some v).
        { eapply ai_backing_present; [exact Hback|ai_interval]. }
        destruct Hcell as [v Hv].
        contention_reduce_turn T; rewrite Hm1 in T; cbn [Nat.eqb] in T.
        rewrite upd_neq in T by ai_distinct; rewrite Hv in T.
        owner_finish T h L R D m0 0.
    + contention_reduce_turn T; rewrite Hr in T. owner_finish T h L R D m0 m1.
    + cbn [cached_remote] in Hc1; destruct Hc1 as [Hbound Hneq].
      assert (Hcell : exists v, h b = Some v).
      { eapply ai_backing_present; [exact Hback|ai_interval]. }
      destruct Hcell as [v Hv]. contention_reduce_turn T; rewrite Hv in T.
      owner_finish T h L R D m0 m1.
    + cbn [cached_remote] in Hc1; destruct Hc1 as [Hbound [Hneq Hlink]].
      contention_reduce_turn T; rewrite Hr in T.
      destruct (Nat.eqb (List.hd 0 R) old) eqn:Ecas.
      * apply Nat.eqb_eq in Ecas; subst old; try rewrite Nat.eqb_refl in T.
        owner_finish T h L (b :: R) D m0 m1.
      * try rewrite Ecas in T. owner_finish T h L R D m0 m1.
Qed.

Lemma ownership_rank_step capacity who pc pc' event L R D L' R' D' :
  ownership_transition who pc pc' event L R D L' R' D' ->
  List.length R <= capacity -> List.length D <= capacity ->
  List.length R' <= capacity -> List.length D' <= capacity ->
  if owner_boundary who pc
  then owner_rank capacity pc' R' D' <= owner_round_bound capacity
  else owner_weight who + owner_rank capacity pc' R' D' <= owner_rank capacity pc R D.
Proof.
  intros Hstep Hr Hd Hr' Hd'; destruct Hstep;
    cbn [owner_boundary owner_weight owner_rank owner_after_offer List.length List.hd] in *.
  - rewrite Nat.eqb_refl; lia.
  - assert (E : Nat.eqb (List.hd 0 R) old = false) by now apply Nat.eqb_neq.
    rewrite E; lia.
  - rewrite Nat.eqb_refl; lia.
  - lia.
  - lia.
  - destruct client; cbn [owner_boundary owner_weight owner_rank owner_after_offer];
      unfold owner_round_bound; lia.
  - destruct client; cbn [owner_boundary owner_weight owner_rank owner_after_offer];
      unfold owner_round_bound; lia.
  - destruct who; [contradiction| |]; cbn [owner_boundary owner_weight]; lia.
  - destruct who; [contradiction| |]; cbn [owner_boundary owner_weight];
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
Lemma owner_weight_count e k :
  (if owner_turn e k then 1 else 0) = owner_weight (selected e k).
Proof. unfold owner_turn; destruct (selected e k); reflexivity. Qed.

Lemma owner_lists_step_bounded capacity who s t event L R D :
  owner_lists capacity s L R D ->
  owner_rank capacity (owner_state s) R D <= owner_round_bound capacity ->
  turn 1 who s = Some (t,event) ->
  exists L' R' D', owner_lists capacity t L' R' D' /\
    owner_rank capacity (owner_state t) R' D' <= owner_round_bound capacity /\
    ownership_transition who (owner_state s) (owner_state t) event L R D L' R' D'.
Proof.
  intros Hview Hbound Hturn.
  destruct (owner_lists_step capacity who s t event L R D Hview Hturn)
    as (L' & R' & D' & Hview' & Hstep).
  pose proof (owner_lists_lengths capacity s L R D Hview) as Hlen.
  pose proof (owner_lists_lengths capacity t L' R' D' Hview') as Hlen'.
  pose proof (ownership_rank_step capacity who (owner_state s) (owner_state t)
    event L R D L' R' D' Hstep ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hrank.
  exists L', R', D'; split; [exact Hview'|]; split; [|exact Hstep].
  destruct (owner_boundary who (owner_state s)); lia.
Qed.
Lemma execution_owner_rank capacity c e k :
  valid_execution capacity c e -> exists L R D,
    owner_lists capacity (states e k) L R D /\
    owner_rank capacity (owner_state (states e k)) R D <= owner_round_bound capacity.
Proof.
  intro Hv; induction k as [|k IH].
  - destruct (inv_owner_lists capacity (states e 0) (execution_inv capacity c e 0 Hv))
      as (L & R & D & Hview).
    exists L, R, D; split; [exact Hview|].
    rewrite (proj1 Hv); cbn [initial_state owner_state owner_rank].
    unfold owner_round_bound; lia.
  - destruct IH as (L & R & D & Hview & Hrank).
    destruct (owner_lists_step_bounded capacity (selected e k) (states e k)
      (states e (S k)) (emitted e k) L R D Hview Hrank
      (execution_step capacity c e k Hv)) as (L' & R' & D' & Hview' & Hrank' & _).
    now exists L', R', D'.
Qed.

Definition round_completion (e : AExecution) k :=
  owner_boundary (selected e k) (owner_state (states e k)) = true.

Lemma owner_round_interval_descent capacity c e lo len L R D :
  valid_execution capacity c e -> owner_lists capacity (states e lo) L R D ->
  (forall j, lo <= j < lo + len -> ~ round_completion e j) ->
  exists L' R' D', owner_lists capacity (states e (lo + len)) L' R' D' /\
    count_if (owner_turn e) lo len +
      owner_rank capacity (owner_state (states e (lo + len))) R' D' <=
      owner_rank capacity (owner_state (states e lo)) R D.
Proof.
  revert lo L R D; induction len as [|len IH]; intros lo L R D Hv Hview Hnone.
  - rewrite Nat.add_0_r, count_if_zero; now exists L, R, D.
  - destruct (owner_lists_step capacity (selected e lo) (states e lo)
      (states e (S lo)) (emitted e lo) L R D Hview
      (execution_step capacity c e lo Hv)) as (L1 & R1 & D1 & Hview1 & Hstep).
    destruct (IH (S lo) L1 R1 D1 Hv Hview1 ltac:(intros j Hj; apply Hnone; lia))
      as (L' & R' & D' & Hview' & Hrest).
    pose proof (owner_lists_lengths capacity _ _ _ _ Hview) as Hlen.
    pose proof (owner_lists_lengths capacity _ _ _ _ Hview1) as Hlen1.
    pose proof (ownership_rank_step capacity _ _ _ _ _ _ _ _ _ _ Hstep
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hrank.
    assert (Hnb : owner_boundary (selected e lo) (owner_state (states e lo)) = false).
    { destruct (owner_boundary (selected e lo) (owner_state (states e lo))) eqn:E;
        [exfalso; apply (Hnone lo ltac:(lia)); exact E|reflexivity]. }
    rewrite Hnb in Hrank.
    replace (lo + S len) with (S lo + len) by lia.
    exists L', R', D'; split; [exact Hview'|].
    rewrite count_if_succ, owner_weight_count; lia.
Qed.

Theorem no_round_completion_owner_bound capacity c e lo len :
  valid_execution capacity c e ->
  (forall j, lo <= j < lo + len -> ~ round_completion e j) ->
  count_if (owner_turn e) lo len < 3 * capacity + 5.
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
  valid_execution capacity c e -> 3 * capacity + 5 <= count_if (owner_turn e) lo len ->
  exists j, lo <= j < lo + len /\ round_completion e j /\
    count_if (owner_turn e) lo (S j - lo) <= 3 * capacity + 5.
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
    destruct (owner_turn e (lo + (j-lo))); lia.
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
    owner_weight who + credit' <= credit.
Proof.
  intros Hstep Hr Hd Hr' Hd' Hcredit Hno.
  destruct Hstep.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_remote; eassumption|].
    cbn [owner_weight owner_rank collection_phase]; rewrite Nat.eqb_refl; lia.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_remote; eassumption|].
    assert (E : Nat.eqb (List.hd 0 R) old = false) by now apply Nat.eqb_neq.
    cbn [owner_weight owner_rank collection_phase]; rewrite E; lia.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_detached; eassumption|].
    cbn [owner_weight owner_rank collection_phase]; rewrite Nat.eqb_refl; lia.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_remote; eassumption|].
    cbn [owner_weight owner_rank collection_phase]; lia.
  - inversion Hcredit; subst.
    + eexists; split; [apply reclaim_remote; eassumption|].
      cbn [owner_weight owner_rank collection_phase List.length]; lia.
    + assert (Htail : In block D).
      { match goal with Hin : In block (_ :: D) |- _ => destruct Hin as [Heq|Hin] end.
        - subst; exfalso; apply Hno; eexists; reflexivity.
        - assumption. }
      eexists; split; [apply reclaim_detached; exact Htail|].
      cbn [owner_weight List.length]; lia.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_remote; eassumption|].
    destruct client; cbn [owner_weight owner_rank collection_phase owner_after_offer];
      unfold owner_round_bound; lia.
  - inversion Hcredit; subst; cbn [List.In] in *; try contradiction.
    eexists; split; [apply reclaim_remote; eassumption|].
    destruct client; cbn [owner_weight owner_rank collection_phase owner_after_offer];
      unfold owner_round_bound; lia.
  - exists credit; split; [exact Hcredit|].
    destruct who; cbn [owner_weight]; [contradiction|lia|lia].
  - inversion Hcredit; subst.
    + eexists; split; [apply reclaim_remote; now right|].
      destruct who; [contradiction| |]; cbn [owner_weight];
        destruct pc; cbn [owner_rank collection_phase List.length List.hd] in *;
        repeat match goal with
        | |- context [if ?b then _ else _] => destruct b eqn:?
        end; lia.
    + eexists; split; [apply reclaim_detached; eassumption|].
      destruct who; cbn [owner_weight]; [contradiction|lia|lia].
Qed.

Lemma execution_retired_credit capacity c e k block idx :
  valid_execution capacity c e -> emitted e k = Some (SPop tag_retire block idx) ->
  exists L R D credit,
    owner_lists capacity (states e (S k)) L R D /\
    reclaim_credit capacity block (owner_state (states e (S k))) R D credit /\
    credit <= 2 * owner_round_bound capacity.
Proof.
  intros Hv Hevent.
  destruct (execution_owner_rank capacity c e k Hv) as (L & R & D & Hview & Hrank).
  destruct (owner_lists_step_bounded capacity (selected e k) (states e k)
    (states e (S k)) (emitted e k) L R D Hview Hrank (execution_step capacity c e k Hv))
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

Lemma reclaim_interval_descent capacity c e lo len L R D block credit :
  valid_execution capacity c e -> owner_lists capacity (states e lo) L R D ->
  reclaim_credit capacity block (owner_state (states e lo)) R D credit ->
  (forall j, lo <= j < lo + len -> ~ block_event tag_reclaim block (emitted e j)) ->
  exists L' R' D' credit',
    owner_lists capacity (states e (lo + len)) L' R' D' /\
    reclaim_credit capacity block (owner_state (states e (lo + len))) R' D' credit' /\
    count_if (owner_turn e) lo len + credit' <= credit.
Proof.
  revert lo L R D credit; induction len as [|len IH];
    intros lo L R D credit Hv Hview Hcredit Hnone.
  - rewrite Nat.add_0_r, count_if_zero; exists L, R, D, credit; auto.
  - destruct (owner_lists_step capacity (selected e lo) (states e lo)
      (states e (S lo)) (emitted e lo) L R D Hview (execution_step capacity c e lo Hv))
      as (L1 & R1 & D1 & Hview1 & Hstep).
    pose proof (owner_lists_lengths capacity _ _ _ _ Hview) as Hlen.
    pose proof (owner_lists_lengths capacity _ _ _ _ Hview1) as Hlen1.
    destruct (ownership_reclaim_credit_step capacity _ _ _ _ _ _ _ _ _ _ block credit Hstep
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hcredit (Hnone lo ltac:(lia)))
      as [credit1 [Hcredit1 Hrank]].
    destruct (IH (S lo) L1 R1 D1 credit1 Hv Hview1 Hcredit1
      ltac:(intros j Hj; apply Hnone; lia)) as (L' & R' & D' & credit' & Hview' & Hcredit' & Hrest).
    replace (lo + S len) with (S lo + len) by lia.
    exists L', R', D', credit'; split; [exact Hview'|]; split; [exact Hcredit'|].
    rewrite count_if_succ, owner_weight_count; lia.
Qed.

Definition block_event_dec tag block event :
  sumbool (block_event tag block event) (not (block_event tag block event)).
Proof.
  destruct event as [[kind b idx]|].
  - destruct (Nat.eq_dec kind tag) as [->|Hkind];
      destruct (Nat.eq_dec b block) as [->|Hb].
    + left; exists idx; reflexivity.
    + right; intros [i H]; inversion H; contradiction.
    + right; intros [i H]; inversion H; contradiction.
    + right; intros [i H]; inversion H; contradiction.
  - right; intros [i H]; discriminate.
Defined.

Theorem no_reclaim_owner_bound capacity c e k block idx len :
  valid_execution capacity c e -> emitted e k = Some (SPop tag_retire block idx) ->
  (forall j, S k <= j < S k + len -> ~ block_event tag_reclaim block (emitted e j)) ->
  count_if (owner_turn e) (S k) len < 6 * capacity + 10.
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
  valid_execution capacity c e -> emitted e k = Some (SPop tag_retire block idx) ->
  6 * capacity + 10 <= count_if (owner_turn e) (S k) len ->
  exists j idx', k < j /\ j < S k + len /\ idx < idx' /\
    emitted e j = Some (SPop tag_reclaim block idx') /\
    count_if (owner_turn e) (S k) (j-k) <= 6 * capacity + 10.
Proof.
  intros Hv Hret Hcount.
  destruct (finite_first (fun j => block_event tag_reclaim block (emitted e j))
    (fun j => block_event_dec tag_reclaim block (emitted e j)) (S k) len)
    as [Hnone|(j & Hj & [idx' Hreclaim] & Hfirst)].
  - pose proof (no_reclaim_owner_bound capacity c e k block idx len Hv Hret Hnone); lia.
  - exists j, idx'; split; [lia|]; split; [lia|]; split.
    + exact (execution_event_order capacity c e k j _ _ Hv ltac:(lia) Hret Hreclaim).
    + split; [exact Hreclaim|].
      pose proof (no_reclaim_owner_bound capacity c e k block idx (j-S k) Hv Hret
        ltac:(intros q Hq; apply Hfirst; lia)) as Hbefore.
      replace (j-k) with ((j-S k)+1) by lia.
      rewrite count_if_add, count_if_succ, count_if_zero.
      destruct (owner_turn e (S k + (j-S k))); lia.
Qed.

Lemma infinitely_owner_count e :
  infinitely (fun k => selected e k = Owner) ->
  forall lo n, exists len, n <= count_if (owner_turn e) lo len.
Proof.
  intros Hinf lo n.
  apply infinitely_count_if.
  intro start.
  destruct (Hinf start) as (k & Hk & Howner).
  exists k; split; [exact Hk|].
  apply owner_turn_spec; exact Howner.
Qed.

Theorem retired_eventually_reclaimed capacity c e :
  valid_execution capacity c e ->
  infinitely (fun k => selected e k = Owner) ->
  forall k block idx,
    emitted e k = Some (SPop tag_retire block idx) ->
    exists j idx', k < j /\ idx < idx' /\
      emitted e j = Some (SPop tag_reclaim block idx').
Proof.
  intros Hv Howner k block idx Hret.
  destruct (infinitely_owner_count e Howner (S k) (6*capacity+10)) as [len Hlen].
  destruct (retired_reclaimed_owner_selection_bound capacity c e k block idx len
    Hv Hret Hlen) as (j & idx' & Hkj & _ & Hidx & Hevent & _).
  now exists j, idx'.
Qed.

Theorem retired_not_reallocated_before_reclaim capacity c e k block idx j :
  valid_execution capacity c e ->
  emitted e k = Some (SPop tag_retire block idx) -> k < j ->
  (forall q idx', k < q < j -> emitted e q <> Some (SPop tag_reclaim block idx')) ->
  forall idx', emitted e j <> Some (SPop tag_alloc block idx').
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
  destruct (owner_lists_step capacity (selected e j) (states e j)
    (states e (S j)) (emitted e j) Lj Rj Dj Hviewj (execution_step capacity c e j Hv))
    as (L' & R' & D' & _ & Hstep).
  eapply (ownership_no_premature_alloc _ _ _ _ _ _ _ _ _ _ block Hstep Hnot).
  exists idx'; exact Halloc.
Qed.

Theorem retired_reallocation_requires_reclaim capacity c e k j block idx alloc_idx :
  valid_execution capacity c e -> k < j ->
  emitted e k = Some (SPop tag_retire block idx) ->
  emitted e j = Some (SPop tag_alloc block alloc_idx) ->
  exists q reclaim_idx, k < q /\ q < j /\ idx < reclaim_idx /\
    reclaim_idx < alloc_idx /\ emitted e q = Some (SPop tag_reclaim block reclaim_idx).
Proof.
  intros Hv Hkj Hret Halloc.
  destruct (finite_first (fun q => block_event tag_reclaim block (emitted e q))
    (fun q => block_event_dec tag_reclaim block (emitted e q)) (S k) (j-S k))
    as [Hnone|(q & Hq & [qi Hreclaim] & _)].
  - exfalso; eapply retired_not_reallocated_before_reclaim;
      [exact Hv|exact Hret|exact Hkj| |exact Halloc].
    intros q qi Hq Hreclaim; apply (Hnone q ltac:(lia)); now exists qi.
  - exists q, qi; split; [lia|]; split; [lia|]; split.
    + exact (execution_event_order capacity c e k q _ _ Hv ltac:(lia) Hret Hreclaim).
    + split; [|exact Hreclaim].
      exact (execution_event_order capacity c e q j _ _ Hv ltac:(lia) Hreclaim Halloc).
Qed.

Theorem source_retired_eventually_reclaimed capacity c se :
  valid_source_execution capacity c se ->
  infinitely (fun k => source_selected se k = Owner) ->
  forall k block idx,
    List.In (SPop tag_retire block idx) (source_emitted se k) ->
    exists j idx', k < j /\ idx < idx' /\
      List.In (SPop tag_reclaim block idx') (source_emitted se j).
Proof.
  intros Hvalid Howner k block idx Hretire.
  destruct (source_execution_complete capacity c se Hvalid)
    as (Hmodel & Haligned & Hlogs & Hselected).
  set (e := execution_of_choices capacity c (source_selected se)) in *.
  assert (Howner' : infinitely (fun j => selected e j = Owner)).
  {
    intro n; destruct (Howner n) as (j & Hnj & Hwho).
    exists j; split; [exact Hnj|now rewrite Hselected].
  }
  assert (Eretire : emitted e k = Some (SPop tag_retire block idx)).
  {
    rewrite Hlogs in Hretire.
    destruct (emitted e k) as [o|] eqn:E; cbn [event_obs] in Hretire;
      [destruct Hretire as [<-|[]]; reflexivity|contradiction].
  }
  destruct (retired_eventually_reclaimed capacity c e Hmodel Howner'
    k block idx Eretire) as (j & idx' & Hkj & Hij & Ereclaim).
  exists j, idx'; repeat split; try assumption.
  rewrite Hlogs, Ereclaim; cbn [event_obs]; now left.
Qed.

From Stdlib Require Import List Lia Arith.PeanoNat.
From Coinduction Require Import coinduction rel tactics.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Eq.Bind ICTree.Logic.AF ICTree.Logic.AG
  ICTree.Logic.AX ICTree.Logic.Bind ICTree.Logic.Iter ICTree.Logic.State Logic.Core.
From examples Require Import CSL.Allocator.Layout CSL.Allocator.Program
  CSL.Allocator.Model CSL.Allocator.Execution.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Typeclasses Transparent equ sbisim.

(** These lists use left numerals so that symbolic counters compute without
    inspecting the counter.  [n+c] is, of course, the prescribed [c+n]. *)
Definition demo_prefix (c : nat) : list SObs :=
  [SPop tag_alloc 6 c; SPop tag_alloc 8 (1+c);
   SPop tag_retire 6 (2+c); SPop tag_retry 8 (3+c);
   SPop tag_retire 8 (4+c); SPop tag_reclaim 8 (5+c);
   SPop tag_reclaim 6 (6+c); SPop tag_alloc 6 (7+c);
   SPop tag_alloc 8 (8+c)].

Definition demo_cycle_logs (c : nat) : list SObs :=
  [SPop tag_retire 6 c; SPop tag_retry 8 (1+c);
   SPop tag_retire 8 (2+c); SPop tag_reclaim 8 (3+c);
   SPop tag_reclaim 6 (4+c); SPop tag_alloc 6 (5+c);
   SPop tag_alloc 8 (6+c)].

Definition demo_rr_script (cursor len : nat) : list Actor :=
  List.map (fun k => actor_of_slot (rr_pick 2 k)) (List.seq cursor len).

(** Only a pointwise representative; no execution ever resets its heap to it. *)
Definition demo_boundary_heap : Heap := fun x =>
  match x with
  | 1 => Some 0 | 2 => Some 0 | 3 => Some 0 | 4 => Some 0
  | 5 => Some 8 | 6 => Some 8 | 7 => Some 1 | 8 => Some 0
  | 9 => Some 2 | _ => None
  end.
Definition demo_boundary (c : nat) : AState :=
  {| aheap := demo_boundary_heap; acount := c;
     owner_state := ORead; remote0_state := RRead 6;
     remote1_state := RPoll |}.

Lemma demo_prefix_run c : exists last,
  run_turns 1 (demo_rr_script 0 57) (initial_state 2 c) =
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

Lemma demo_cycle_run c : exists last,
  run_turns 1 (demo_rr_script 0 42) (demo_boundary c) =
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

(** The actual returned heap is passed to the following cycle. *)
Lemma demo_cycle_run_actual c s :
  state_equiv s (demo_boundary c) ->
  exists last,
    run_turns 1 (demo_rr_script 0 42) s = Some (last,demo_cycle_logs c) /\
    state_equiv last (demo_boundary (c+7)).
Proof.
  intro Hs; destruct (demo_cycle_run c) as (last & Hrun & Hlast).
  destruct (run_turns_respects_heq_some 1 (demo_rr_script 0 42)
    (demo_boundary c) s last (demo_cycle_logs c)
    (state_equiv_sym _ _ Hs) Hrun) as (actual & Hactual & Heq).
  exists actual; split; [exact Hactual|].
  eapply state_equiv_trans; [apply state_equiv_sym; exact Heq|exact Hlast].
Qed.

Lemma demo_cycle_cursor cursor : (cursor+42) mod 3 = cursor mod 3.
Proof.
  rewrite Nat.Div0.add_mod.
  change ((cursor mod 3 + 0) mod 3 = cursor mod 3).
  rewrite Nat.add_0_r, Nat.Div0.mod_mod; reflexivity.
Qed.

Lemma demo_rr_run_turns base len cursor s last logs :
  run_turns base (demo_rr_script cursor len) s = Some (last,logs) ->
  model_rr base s cursor ~ emit_list logs (model_rr base last (cursor+len)).
Proof.
  revert cursor s last logs.
  induction len as [|len IH]; intros cursor s last logs Hrun.
  - cbn [demo_rr_script List.seq List.map run_turns] in Hrun.
    inversion Hrun; subst; rewrite Nat.add_0_r; reflexivity.
  - cbn [demo_rr_script List.seq List.map run_turns] in Hrun.
    destruct (turn base (actor_of_slot (rr_pick 2 cursor)) s)
      as [[next event]|] eqn:Hturn; [|discriminate].
    destruct (run_turns base
      (List.map (fun k => actor_of_slot (rr_pick 2 k)) (List.seq (S cursor) len)) next)
      as [[last' suffix]|] eqn:Hrest; [|discriminate].
    inversion Hrun; subst last' logs.
    replace (cursor+S len) with (S cursor+len) by lia.
    rewrite unfold_model_rr, Hturn.
    destruct event as [o|].
    + rewrite emit_list_cons; apply sb_vis; intros [].
      rewrite sb_guard; eapply IH; exact Hrest.
    + rewrite sb_guard; eapply IH; exact Hrest.
Qed.

Lemma demo_rr_period c :
  model_rr 1 (demo_boundary c) 0 ~
  emit_list (demo_cycle_logs c) (model_rr 1 (demo_boundary (c+7)) 0).
Proof.
  destruct (demo_cycle_run c) as (last & Hrun & Hlast).
  etransitivity; [exact (demo_rr_run_turns 1 42 0 _ _ _ Hrun)|].
  apply emit_list_sbisim, model_rr_respects_heq; [exact Hlast|reflexivity].
Qed.

Definition demo_cycle (c : nat) : ictreeW SObs (unit * SSig) :=
  ICtree.iter (fun n => emit_list (demo_cycle_logs n)
    (Ret (@inl nat (unit * SSig) (n+7)))) c.

Lemma demo_cycle_unfold c :
  demo_cycle c ~ emit_list (demo_cycle_logs c) (demo_cycle (c+7)).
Proof.
  unfold demo_cycle at 1; rewrite sb_unfold_iter.
  rewrite emit_list_ret_bind; reflexivity.
Qed.

Lemma demo_rr_cycle_bisim : forall c,
  model_rr 1 (demo_boundary c) 0 ~ demo_cycle c.
Proof.
  unfold sbisim; apply_coinduction; fold_sbisim; intros R IH c.
  etransitivity; [apply (coinduction.gfp_bt (sb eq) R), demo_rr_period|].
  etransitivity; [|apply (coinduction.gfp_bt (sb eq) R); symmetry;
    apply demo_cycle_unfold].
  change (coinduction.bt (sb eq) R
    (emit_list (SPop tag_retire 6 c :: List.tl (demo_cycle_logs c))
      (model_rr 1 (demo_boundary (c+7)) 0))
    (emit_list (SPop tag_retire 6 c :: List.tl (demo_cycle_logs c))
      (demo_cycle (c+7)))).
  eapply equ_sbt_closed_goal; [apply emit_list_cons|apply emit_list_cons|].
  apply step_sb_vis.
  - intros []; exists tt; split; [|reflexivity].
    apply emit_list_st; apply IH.
  - intros []; exists tt; split; [|reflexivity].
    apply emit_list_st; apply IH.
Qed.

Theorem run_rr_allocator_demo_bisim c :
  run_rr (allocator_program 2) hemp c ~
  emit_list (demo_prefix c) (demo_cycle (c+9)).
Proof.
  rewrite run_rr_allocator_bisim.
  destruct (demo_prefix_run c) as (last & Hrun & Hlast).
  etransitivity; [exact (demo_rr_run_turns 1 57 0 _ _ _ Hrun)|].
  apply emit_list_sbisim.
  etransitivity; [apply (model_rr_respects_heq 1 last (demo_boundary (c+9)) 57 0);
    [exact Hlast|reflexivity]|].
  apply demo_rr_cycle_bisim.
Qed.






Lemma demo_cycle_fresh_member c kind :
  List.In kind [tag_alloc;tag_retire;tag_reclaim] ->
  exists o, List.In o (demo_cycle_logs c) /\ stag o = kind /\ c <= sidx o.
Proof.
  intros [<-|[<-|[<-|[]]]].
  - exists (SPop tag_alloc 6 (5+c)); cbn [demo_cycle_logs List.In stag sidx];
      repeat split; intuition lia.
  - exists (SPop tag_retire 6 c); cbn [demo_cycle_logs List.In stag sidx];
      repeat split; intuition lia.
  - exists (SPop tag_reclaim 8 (3+c)); cbn [demo_cycle_logs List.In stag sidx];
      repeat split; intuition lia.
Qed.

Lemma demo_cycle_af c kind kb w :
  List.In kind [tag_alloc;tag_retire;tag_reclaim] -> not_done w ->
  <( {demo_cycle c}, w |= AF visW {fun o => stag o = kind /\ kb <= sidx o} )>.
Proof.
  intros Hkind Hd; unfold demo_cycle.
  eapply aul_iter_nat with (Ri := fun (_ : nat) (_ : WorldW SObs) => True)
    (f := fun n (_ : WorldW SObs) => kb-n).
  - exact Hd.
  - exact I.
  - intros n v Hv _; destruct (Nat.le_gt_cases kb n) as [Hle|Hlt].
    + left; destruct (demo_cycle_fresh_member n kind Hkind) as (o & Hin & Htag & Hidx).
      eapply af_emit_list_member; [exact Hv|exact Hin|].
      split; [exact Htag|lia].
    + right; apply af_emit_list_ret; [exact Hv|].
      exists (n+7); split; [reflexivity|].
      split; [apply after_logs_not_done; exact Hv|].
      split; [exact I|lia].
Qed.

(** A proof-only presentation which exposes a single observation per body.
    [ag_iter] requires its invariant at *finite-body* residuals.  Splitting the
    body at logs allows their eventuality proof to use the next complete cycle,
    instead of incorrectly asking the finite seven-log body to publish again. *)
Definition demo_log_body (p : list SObs * nat)
  : ictreeW SObs ((list SObs * nat) + (unit * SSig)) :=
  let '(xs,c) := p in
  match xs with
  | [] => log (SPop tag_retire 6 c);;
      Ret (inl (List.tl (demo_cycle_logs c),c+7))
  | o :: rest => log o;; Ret (inl (rest,c))
  end.
Definition demo_log_loop (xs : list SObs) (c : nat)
  : ictreeW SObs (unit * SSig) := ICtree.iter demo_log_body (xs,c).

Lemma demo_log_loop_unfold xs c :
  demo_log_loop xs c ~
  match xs with
  | [] => log (SPop tag_retire 6 c);;
      demo_log_loop (List.tl (demo_cycle_logs c)) (c+7)
  | o :: rest => log o;; demo_log_loop rest c
  end.
Proof.
  unfold demo_log_loop at 1; rewrite sb_unfold_iter.
  unfold demo_log_body; destruct xs as [|o rest]; cbn beta iota zeta.
  all: rewrite bind_bind; apply sbisim_clo_bind_eq; [reflexivity|].
  all: intros []; rewrite bind_ret_l; reflexivity.
Qed.

Lemma demo_log_loop_bisim : forall xs c,
  demo_log_loop xs c ~ emit_list xs (demo_cycle c).
Proof.
  unfold sbisim; apply_coinduction; fold_sbisim; intros R IH xs c.
  etransitivity; [apply (coinduction.gfp_bt (sb eq) R), demo_log_loop_unfold|].
  destruct xs as [|o rest].
  - cbn [emit_list List.fold_right].
    etransitivity; [|apply (coinduction.gfp_bt (sb eq) R); symmetry;
      apply demo_cycle_unfold].
    change (coinduction.bt (sb eq) R
      (log (SPop tag_retire 6 c);;
        demo_log_loop (List.tl (demo_cycle_logs c)) (c+7))
      (emit_list (SPop tag_retire 6 c :: List.tl (demo_cycle_logs c))
        (demo_cycle (c+7)))).
    eapply equ_sbt_closed_goal;
      [apply (emit_list_cons (SPop tag_retire 6 c) [] _)|apply emit_list_cons|].
    apply step_sb_vis.
    + intros []; exists tt; split; [apply IH|reflexivity].
    + intros []; exists tt; split; [apply IH|reflexivity].
  - eapply equ_sbt_closed_goal;
      [apply (emit_list_cons o [] _)|apply emit_list_cons|].
    apply step_sb_vis.
    + intros []; exists tt; split; [apply IH|reflexivity].
    + intros []; exists tt; split; [apply IH|reflexivity].
Qed.

Lemma demo_log_loop_af xs c kind kb w :
  List.In kind [tag_alloc;tag_retire;tag_reclaim] -> not_done w ->
  <( {demo_log_loop xs c}, w |= AF visW {fun o => stag o = kind /\ kb <= sidx o} )>.
Proof.
  intros Hkind Hd; rewrite demo_log_loop_bisim.
  apply af_emit_list; [exact Hd|].
  apply demo_cycle_af; [exact Hkind|].
  apply after_logs_not_done; exact Hd.
Qed.

Lemma demo_log_loop_agaf xs c kind kb w :
  List.In kind [tag_alloc;tag_retire;tag_reclaim] -> not_done w ->
  <( {demo_log_loop xs c}, w |= AG (AF visW {fun o => stag o = kind /\ kb <= sidx o}) )>.
Proof.
  intros Hkind Hd; unfold demo_log_loop.
  eapply ag_iter with (R := fun (_ : list SObs * nat) v => not_done v).
  - exact Hd.
  - intros [ys n] v Hv; split.
    + change <( {demo_log_loop ys n}, v
        |= AF visW {fun o => stag o = kind /\ kb <= sidx o} )>.
      apply demo_log_loop_af; assumption.
    + unfold demo_log_body; cbn beta iota zeta.
      destruct ys as [|o rest].
      * apply axr_log; [exact Hv|].
        cleft; apply axr_ret; [constructor|].
        exists (List.tl (demo_cycle_logs n),n+7); split; [reflexivity|constructor].
      * apply axr_log; [exact Hv|].
        cleft; apply axr_ret; [constructor|].
        exists (rest,n); split; [reflexivity|constructor].
Qed.

Lemma demo_cycle_agaf c kind kb w :
  List.In kind [tag_alloc;tag_retire;tag_reclaim] -> not_done w ->
  <( {demo_cycle c}, w |= AG (AF visW {fun o => stag o = kind /\ kb <= sidx o}) )>.
Proof.
  intros Hkind Hd.
  change <( {emit_list [] (demo_cycle c)}, w
    |= AG (AF visW {fun o => stag o = kind /\ kb <= sidx o}) )>.
  rewrite <- (demo_log_loop_bisim [] c).
  apply demo_log_loop_agaf; assumption.
Qed.

Theorem allocator_demo_agaf_fresh c kind kb :
  List.In kind [tag_alloc;tag_retire;tag_reclaim] ->
  <( {run_rr (allocator_program 2) hemp c}, Pure
      |= AG (AF visW {fun o => stag o = kind /\ kb <= sidx o}) )>.
Proof.
  intro Hkind; rewrite run_rr_allocator_demo_bisim.
  apply agaf_emit_list; [constructor|].
  apply demo_cycle_agaf; [exact Hkind|].
  apply after_logs_not_done; constructor.
Qed.
