(** * Infinite executions and finite replay.

    A reusable, language-independent execution record with:

      - a finite script runner [run_turns] over a partial transition,
      - a constructive builder of an infinite execution from a choice
        sequence and a total, invariant-preserving transition,
      - counter/index bookkeeping,
      - reachability through the Stdlib reflexive-transitive closure.

    Periodic choice sequences and window list facts live in [Utils.Lists].

    This module imports only Stdlib, ExtLib and [Utils]; it never mentions
    ictrees, schedulers, or any example. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat
  Relations
  Classes.Morphisms
  Classes.RelationClasses
  Classes.RelationPairs.

From ExtLib Require Import Data.Option.

From TICL Require Import Utils.Relations Utils.Lists.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(** ** The record *)
Record Execution (St Act Out : Type) := {
  states : nat -> St;
  selected : nat -> Act;
  emitted : nat -> Out
}.

Arguments states {St Act Out} _ _.
Arguments selected {St Act Out} _ _.
Arguments emitted {St Act Out} _ _.

Definition execution_valid {St Act Out}
  (step : Act -> St -> Out -> St -> Prop) (initial : St -> Prop)
  (e : Execution St Act Out) : Prop :=
  initial (states e 0) /\
  forall k, step (selected e k) (states e k) (emitted e k) (states e (S k)).

(** Every action is chosen infinitely often. *)
Definition fair_choices {Act} (pick : nat -> Act) : Prop :=
  forall a, infinitely (fun k => pick k = a).

(** Result relations are ExtLib's inductive [Roption] and Stdlib's
    [RelProd]; no client writes its own match-encoded result relation. *)

(** ** Finite replay of a script *)
Section RunTurns.
  Context {St Act Out W : Type}
    (step : Act -> St -> option (St * Out))
    (logs : Out -> list W).

  Fixpoint run_turns (script : list Act) (s : St) : option (St * list W) :=
    match script with
    | [] => Some (s,[])
    | who :: rest =>
        match step who s with
        | None => None
        | Some (next,output) =>
            match run_turns rest next with
            | None => None
            | Some (last,tail) => Some (last,logs output ++ tail)
            end
        end
    end.

  Lemma run_turns_append left right s :
    run_turns (left ++ right) s =
    match run_turns left s with
    | None => None
    | Some (middle,first) =>
        match run_turns right middle with
        | None => None
        | Some (last,second) => Some (last,first ++ second)
        end
    end.
  Proof.
    revert s; induction left as [|who left IH]; intro s.
    - cbn [run_turns app].
      destruct (run_turns right s) as [[last ws]|]; reflexivity.
    - cbn [run_turns app].
      destruct (step who s) as [[next output]|]; [|reflexivity].
      rewrite IH.
      destruct (run_turns left next) as [[middle first]|]; [|reflexivity].
      destruct (run_turns right middle) as [[last second]|]; [|reflexivity].
      now rewrite app_assoc.
  Qed.

  Corollary run_turns_compose left right s middle last first second :
    run_turns left s = Some (middle,first) ->
    run_turns right middle = Some (last,second) ->
    run_turns (left ++ right) s = Some (last,first ++ second).
  Proof.
    intros Hleft Hright; rewrite run_turns_append, Hleft, Hright; reflexivity.
  Qed.

  (** An invariant preserved by one transition is preserved by a whole run. *)
  Lemma run_turns_preserves_inv (Inv : St -> Prop)
    (preserves : forall a s s' o, Inv s -> step a s = Some (s',o) -> Inv s') :
    forall script s last ws,
      Inv s -> run_turns script s = Some (last,ws) -> Inv last.
  Proof.
    induction script as [|who rest IH]; intros s last ws Hinv Hrun.
    - cbn [run_turns] in Hrun; inversion Hrun; subst; exact Hinv.
    - cbn [run_turns] in Hrun.
      destruct (step who s) as [[next output]|] eqn:Hstep; [|discriminate].
      destruct (run_turns rest next) as [[last' tail]|] eqn:Hrest; [|discriminate].
      inversion Hrun; subst.
      eapply IH; [eapply preserves; eauto|exact Hrest].
  Qed.

End RunTurns.

Arguments run_turns {St Act Out W} step logs script s.

(** ** Congruence in the state, through an arbitrary state relation. *)
Section RunTurnsProper.
  Context {St Act Out W : Type}
    (step : Act -> St -> option (St * Out))
    (logs : Out -> list W)
    (R : St -> St -> Prop)
    (Hstep : Proper (eq ==> R ==> Roption (RelProd R eq)) step).

  Lemma step_some_compatible a s t s' o :
    R s t -> step a s = Some (s',o) ->
    exists t', step a t = Some (t',o) /\ R s' t'.
  Proof.
    intros Hst Hrun.
    pose proof (Hstep a a eq_refl s t Hst) as H.
    rewrite Hrun in H.
    destruct (step a t) as [[t' o']|]; inversion H as [|p q Hpq]; subst.
    unfold RelProd, RelCompFun in Hpq.
    destruct Hpq as [Hnext Hobs]; cbn in Hnext, Hobs; subst o'.
    exists t'; split; [reflexivity|exact Hnext].
  Qed.

  Lemma run_turns_proper script :
    Proper (R ==> Roption (RelProd R eq)) (run_turns step logs script).
  Proof.
    revert script; intros script s t Hst; revert s t Hst.
    induction script as [|who rest IH]; intros s t Hst.
    - cbn [run_turns]; constructor; split; [exact Hst|exact eq_refl].
    - cbn [run_turns].
      pose proof (Hstep who who eq_refl s t Hst) as Hone.
      destruct (step who s) as [[next output]|];
        destruct (step who t) as [[next' output']|];
        inversion Hone as [|p q Hpair]; subst; [|constructor].
      unfold RelProd, RelCompFun in Hpair.
      destruct Hpair as [Hnext Hobs]; cbn in Hnext, Hobs; subst output'.
      specialize (IH next next' Hnext).
      destruct (run_turns step logs rest next) as [[last ws]|];
        destruct (run_turns step logs rest next') as [[last' ws']|];
        inversion IH as [|p q Hlast]; subst; [|constructor].
      unfold RelProd, RelCompFun in Hlast.
      destruct Hlast as [Hlast Hlogs]; cbn in Hlast, Hlogs; subst ws'.
      constructor; split; [exact Hlast|exact eq_refl].
  Qed.

  Corollary run_turns_some_compatible script s t last observations :
    R s t -> run_turns step logs script s = Some (last,observations) ->
    exists last', run_turns step logs script t = Some (last',observations) /\
      R last last'.
  Proof.
    intros Hst Hrun.
    pose proof (run_turns_proper script s t Hst) as H.
    rewrite Hrun in H.
    destruct (run_turns step logs script t) as [[last' ws']|];
      inversion H as [|p q Hpq]; subst.
    unfold RelProd, RelCompFun in Hpq.
    destruct Hpq as [Hlast Hlogs]; cbn in Hlast, Hlogs; subst ws'.
    exists last'; split; [reflexivity|exact Hlast].
  Qed.

End RunTurnsProper.

(** ** Constructing an infinite execution from a choice sequence.

    The impossible branch is eliminated in [Prop] using totality; no
    existential witness is extracted into executable state, no classical
    choice is used, and no initial/default state is manufactured on failure. *)
Section OfChoices.
  Context {St Act Out : Type}
    (step : Act -> St -> option (St * Out))
    (Inv : St -> Prop)
    (total : forall a s, Inv s -> exists r, step a s = Some r)
    (preserves : forall a s s' o, Inv s -> step a s = Some (s',o) -> Inv s').

  Definition next_valid (a : Act) (s : St) (Hinv : Inv s)
    : { result : (St * Out)%type | step a s = Some result /\ Inv (fst result) }.
  Proof.
    destruct (step a s) as [[next output]|] eqn:Hstep.
    - exists (next,output); split; [reflexivity|].
      eapply preserves; eauto.
    - exfalso; destruct (total a s Hinv) as (r & H).
      rewrite Hstep in H; discriminate.
  Defined.

  Fixpoint chosen_state (s0 : St) (H0 : Inv s0) (picks : nat -> Act) (k : nat)
    : { s : St | Inv s } :=
    match k with
    | 0 => exist _ s0 H0
    | S j =>
        let prior := chosen_state s0 H0 picks j in
        let next := next_valid (picks j) (proj1_sig prior) (proj2_sig prior) in
        exist _ (fst (proj1_sig next)) (proj2 (proj2_sig next))
    end.

  Definition execution_of_choices (s0 : St) (H0 : Inv s0) (picks : nat -> Act)
    : Execution St Act Out :=
    {| states := fun k => proj1_sig (chosen_state s0 H0 picks k);
       selected := picks;
       emitted := fun k =>
         let prior := chosen_state s0 H0 picks k in
         snd (proj1_sig (next_valid (picks k)
           (proj1_sig prior) (proj2_sig prior))) |}.

  Lemma execution_of_choices_valid s0 H0 picks :
    execution_valid (fun a s o s' => step a s = Some (s',o))
      (fun s => s = s0) (execution_of_choices s0 H0 picks).
  Proof.
    split; [reflexivity|]; intro k.
    unfold execution_of_choices; cbn [states selected emitted chosen_state].
    destruct (next_valid (picks k)
      (proj1_sig (chosen_state s0 H0 picks k))
      (proj2_sig (chosen_state s0 H0 picks k))) as [[next output] [Hstep Hinv]].
    exact Hstep.
  Qed.

  Lemma execution_of_choices_selected s0 H0 picks k :
    selected (execution_of_choices s0 H0 picks) k = picks k.
  Proof. reflexivity. Qed.

End OfChoices.

Arguments next_valid {St Act Out} step Inv total preserves a s Hinv.
Arguments chosen_state {St Act Out} step Inv total preserves s0 H0 picks k.
Arguments execution_of_choices {St Act Out} step Inv total preserves s0 H0 picks.

(** ** Reading an execution *)
Section ExecutionFacts.
  Context {St Act Out : Type}
    (step : Act -> St -> option (St * Out))
    (Inv : St -> Prop) (initial : St -> Prop).

  Notation valid := (execution_valid (fun a s o s' => step a s = Some (s',o)) initial).

  Lemma execution_step (e : Execution St Act Out) k :
    valid e -> step (selected e k) (states e k) = Some (states e (S k),emitted e k).
  Proof. intros [_ H]; apply H. Qed.

  Lemma execution_inv (e : Execution St Act Out)
    (Hinit : forall s, initial s -> Inv s)
    (preserves : forall a s s' o, Inv s -> step a s = Some (s',o) -> Inv s') k :
    valid e -> Inv (states e k).
  Proof.
    intros [Hi Hstep]; induction k as [|k IH].
    - now apply Hinit.
    - eapply preserves; [exact IH|apply Hstep].
  Qed.
End ExecutionFacts.

Section ExecutionRun.
  Context {St Act Out W : Type}
    (step : Act -> St -> option (St * Out))
    (logs : Out -> list W)
    (initial : St -> Prop).

  Lemma execution_run_turns (e : Execution St Act Out) lo len :
    execution_valid (fun a s o s' => step a s = Some (s',o)) initial e ->
    run_turns step logs (List.map (selected e) (List.seq lo len)) (states e lo) =
      Some (states e (lo + len),
        List.flat_map (fun k => logs (emitted e k)) (List.seq lo len)).
  Proof.
    intro Hvalid; revert lo; induction len as [|len IH]; intro lo.
    - cbn [List.seq List.map run_turns List.flat_map]; now rewrite Nat.add_0_r.
    - cbn [List.seq List.map run_turns List.flat_map].
      rewrite (execution_step step initial e lo Hvalid), IH.
      now replace (S lo + len) with (lo + S len) by lia.
  Qed.
End ExecutionRun.

(** Endpoint relatedness and exact output equality of one window, under a
    state equivalence. *)
Section ExecutionWindow.
  Context {St Act Out W : Type}
    (step : Act -> St -> option (St * Out))
    (logs : Out -> list W)
    (initial : St -> Prop)
    (R : St -> St -> Prop)
    (Hstep : Proper (eq ==> R ==> Roption (RelProd R eq)) step).

  Notation valid := (execution_valid (fun a s o s' => step a s = Some (s',o)) initial).

  Lemma execution_window_state (e : Execution St Act Out) lo len s :
    valid e -> R (states e lo) s ->
    exists last, run_turns step logs
      (List.map (selected e) (List.seq lo len)) s = Some (last,
        List.flat_map (fun k => logs (emitted e k)) (List.seq lo len)) /\
      R (states e (lo + len)) last.
  Proof.
    intros Hvalid Hs.
    eapply run_turns_some_compatible; [exact Hstep|exact Hs|].
    eapply execution_run_turns; exact Hvalid.
  Qed.

  Lemma execution_turn_observation (e : Execution St Act Out) k s :
    valid e -> R (states e k) s ->
    exists next, step (selected e k) s = Some (next,emitted e k) /\
      R (states e (S k)) next.
  Proof.
    intros Hvalid Hs.
    eapply step_some_compatible; [exact Hstep|exact Hs|].
    eapply execution_step; exact Hvalid.
  Qed.

  (** A window whose script is fixed pointwise: the endpoint state after
      replaying it, and the state and output at any position inside it. *)
  Lemma execution_script_state (e : Execution St Act Out) lo script s last ws :
    valid e -> R (states e lo) s ->
    List.map (selected e) (List.seq lo (List.length script)) = script ->
    run_turns step logs script s = Some (last,ws) ->
    R (states e (lo + List.length script)) last.
  Proof.
    intros Hvalid Hs Hscript Hrun.
    destruct (execution_window_state e lo (List.length script) s Hvalid Hs)
      as (actual & Hactual & Hstate).
    rewrite Hscript, Hrun in Hactual.
    assert (Elast : actual = last) by congruence; subst actual; exact Hstate.
  Qed.

  Lemma execution_script_emitted (e : Execution St Act Out) lo script i d
    s middle ws next out :
    valid e -> R (states e lo) s ->
    List.map (selected e) (List.seq lo (List.length script)) = script ->
    i < List.length script ->
    run_turns step logs (List.firstn i script) s = Some (middle,ws) ->
    step (List.nth i script d) middle = Some (next,out) ->
    R (states e (lo + i)) middle /\ emitted e (lo + i) = out.
  Proof.
    intros Hvalid Hs Hscript Hi Hrun Hturn.
    assert (Hpre : List.map (selected e) (List.seq lo i) = List.firstn i script).
    { rewrite <- (map_seq_firstn (selected e) lo (List.length script) i
        ltac:(lia)); rewrite Hscript; reflexivity. }
    assert (Hsel : selected e (lo + i) = List.nth i script d).
    { rewrite <- Hscript.
      rewrite (List.nth_indep _ d (selected e lo))
        by (rewrite List.length_map, List.length_seq; exact Hi).
      rewrite List.map_nth, (List.seq_nth lo lo Hi); reflexivity. }
    destruct (execution_window_state e lo i s Hvalid Hs)
      as (actual & Hactual & Hstate).
    rewrite Hpre, Hrun in Hactual.
    assert (Emiddle : actual = middle) by congruence; subst actual.
    split; [exact Hstate|].
    destruct (execution_turn_observation e (lo + i) middle Hvalid Hstate)
      as (next' & Hturn' & _).
    rewrite Hsel, Hturn in Hturn'; congruence.
  Qed.
End ExecutionWindow.

(** ** Counters and observation indices.

    Generic over a state counter and an observation index, for executions
    whose output is an optional observation. *)
Section ExecutionCounter.
  Context {St Act W : Type}
    (step : Act -> St -> option (St * option W))
    (initial : St -> Prop)
    (counter : St -> nat) (index : W -> nat).

  Notation valid := (execution_valid (fun a s o s' => step a s = Some (s',o)) initial).

  Context (Hcounter : forall a s s' o, step a s = Some (s',o) ->
    match o with
    | None => counter s' = counter s
    | Some w => counter s' = S (counter s) /\ index w = counter s
    end).

  Lemma execution_event_index (e : Execution St Act (option W)) k w :
    valid e -> emitted e k = Some w ->
    counter (states e (S k)) = S (counter (states e k)) /\
    index w = counter (states e k).
  Proof.
    intros Hvalid Hobs.
    pose proof (Hcounter (selected e k) (states e k) (states e (S k))
      (emitted e k) (execution_step step initial e k Hvalid)) as H.
    now rewrite Hobs in H.
  Qed.

  Lemma execution_counter_mono (e : Execution St Act (option W)) lo hi :
    valid e -> lo <= hi -> counter (states e lo) <= counter (states e hi).
  Proof.
    intros Hvalid Hle.
    assert (Hstep : forall k, counter (states e k) <= counter (states e (S k))).
    { intro k; pose proof (Hcounter (selected e k) (states e k) (states e (S k))
        (emitted e k) (execution_step step initial e k Hvalid)) as H.
      destruct (emitted e k); cbn in H; intuition lia. }
    induction Hle as [|hi Hle IH]; [lia|specialize (Hstep hi); lia].
  Qed.

  Lemma execution_event_order (e : Execution St Act (option W)) k j w p :
    valid e -> k < j ->
    emitted e k = Some w -> emitted e j = Some p -> index w < index p.
  Proof.
    intros Hvalid Hkj Hw Hp.
    pose proof (execution_event_index e k w Hvalid Hw) as [Hk Hi].
    pose proof (execution_event_index e j p Hvalid Hp) as [Hj Hjidx].
    pose proof (execution_counter_mono e (S k) j Hvalid ltac:(lia)); lia.
  Qed.
End ExecutionCounter.

(** ** Reachability, through the Stdlib closure. *)
Definition reachable {St Act Out}
  (step : Act -> St -> Out -> St -> Prop) (initial : St -> Prop) (s : St) : Prop :=
  exists s0, initial s0 /\
    clos_refl_trans_1n St (fun x y => exists a o, step a x o y) s0 s.

Lemma reachable_inv {St Act Out}
  (step : Act -> St -> Out -> St -> Prop) (initial : St -> Prop)
  (Inv : St -> Prop)
  (Hinit : forall s, initial s -> Inv s)
  (preserves : forall a s o s', Inv s -> step a s o s' -> Inv s') s :
  reachable step initial s -> Inv s.
Proof.
  intros (s0 & H0 & Hclos).
  apply Hinit in H0; revert H0.
  induction Hclos as [x|x y z Hxy Hyz IH]; intro Hx; [exact Hx|].
  apply IH; destruct Hxy as (a & o & Hstep); eapply preserves; eauto.
Qed.
