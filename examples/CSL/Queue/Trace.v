(** * Trace: the state trajectory of the rotating queue.

    SHARED between the two proof families.  Nothing here is a separation-logic
    notion: [qstepN] is the heap after [n] rotations, and [run_stepN]
    exposes the corresponding [5 * n] observations, including intermediate
    post-write snapshots. Both proof families import this file. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.
From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Interp.State.Mod
  CTree.Events.State
  CTree.Events.Writer
  CTree.Trace
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.Bind
  CTree.Logic.Iter
  CTree.Logic.State
  Utils.Relations
  Logic.Core.

From examples Require Import CSL.Queue.Representation CSL.Queue.Operations CSL.Queue.Sequential.

Import CTree CTreeNotations TiclNotations ListNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

(** One completed rotation exposes its payload and four post-write heaps.
    The administrative iteration guard is discharged by [sb_guard]. *)
Lemma run_step: forall hdr a ns v vs h allocs ctx c,
    qrep hdr (a :: ns) (v :: vs) h ->
    run hdr ((h, allocs), (ctx, c))
    ~ emit_list (queue_turn_logs (CSLEmit (stamp v c)) hdr a
        (List.hd 0 ns) (last (a :: ns) 0) (h,allocs))
       (run hdr ((rot_heap hdr a (List.hd 0 ns) (zof hdr ns) h, allocs), (ctx, S c))).
Proof.
  intros hdr a ns v vs h allocs ctx c Hq.
  unfold run, rotate.
  rewrite interp_state_unfold_iter.
  cbv beta.
  rewrite (rot_body_spec hdr a ns v vs h allocs ctx c Hq).
  rewrite emit_list_ret_bind; apply emit_list_sbisim.
  apply sb_guard.
Qed.

(** The heap after one rotation, and after [n] of them. *)
Definition qstep (hdr: nat) (ns: list nat) (h: Heap) : Heap :=
  match ns with
  | [] => h
  | a :: ns' => rot_heap hdr a (List.hd 0 ns') (zof hdr ns') h
  end.

Definition qstepN (hdr: nat) (n: nat) (ns: list nat) (h: Heap) : Heap :=
  snd (Nat.iter n (fun '(nodes,heap) => (rotl nodes,qstep hdr nodes heap)) (ns,h)).


(** The observation prefix is a flat sequence of chronological batches. The
    continuation follows the final snapshot without an administrative bind. *)
Definition runN (hdr: nat) (n: nat) (ns vs: list nat) (memory: ManagedHeap) (c: nat)
              (k: ctreeW (CSLObs nat) Bn (SSig * unit)) : ctreeW (CSLObs nat) Bn (SSig * unit) :=
  emit_list
    (List.flat_map
      (fun j =>
        let '(nodes,values,mem,counter) :=
          Nat.iter j
            (fun '(nodes,values,mem,counter) =>
              (rotl nodes,rotl values,(qstep hdr nodes (fst mem),snd mem),S counter))
            (ns,vs,memory,c) in
        queue_turn_logs (CSLEmit (stamp (hd 0 values) counter)) hdr
          (hd 0 nodes) (hd 0 (tl nodes)) (last nodes 0) mem)
      (List.seq 0 n)) k.


Lemma qstep_qrep: forall hdr ns vs h,
    qrep hdr ns vs h -> ns <> [] ->
    qrep hdr (rotl ns) (rotl vs) (qstep hdr ns h).
Proof.
  intros hdr ns vs h Hq Hne.
  destruct ns as [| a ns']; [contradiction |].
  destruct vs as [| v vs']; [apply qrep_len in Hq; cbn in Hq; discriminate |].
  cbn [qstep rotl].
  apply (rot_heap_spec hdr a ns' v vs' h Hq).
Qed.

Lemma qstepN_qrep: forall n hdr ns vs h,
    qrep hdr ns vs h -> ns <> [] ->
    qrep hdr (rotlN n ns) (rotlN n vs) (qstepN hdr n ns h) /\ rotlN n ns <> [].
Proof.
  intros n hdr ns vs h Hq Hne.
  set (next := fun state : list nat * list nat * Heap =>
    let '(nodes,values,heap) := state in
    (rotl nodes,rotl values,qstep hdr nodes heap)).
  set (Inv := fun state : list nat * list nat * Heap =>
    qrep hdr (fst (fst state)) (snd (fst state)) (snd state) /\
    fst (fst state) <> []).
  assert (Hnext : forall state, Inv state -> Inv (next state)).
  { intros [[nodes values] heap] [Hrep Hnodes]; cbn [Inv next] in *.
    split; [now apply qstep_qrep | now apply rotl_nonnil]. }
  pose proof (@Nat.iter_invariant n _ next Inv Hnext (ns,vs,h)
    (conj Hq Hne)) as Hiter.
  pose proof (@Nat.iter_swap_gen _ _ (fun state => fst (fst state))
    next rotl ltac:(intros [[nodes values] heap]; reflexivity)
    n (ns,vs,h)) as Enodes.
  pose proof (@Nat.iter_swap_gen _ _ (fun state => snd (fst state))
    next rotl ltac:(intros [[nodes values] heap]; reflexivity)
    n (ns,vs,h)) as Evalues.
  cbn [fst snd] in Enodes, Evalues.
  pose proof (@Nat.iter_swap_gen _ _
    (fun state => (fst (fst state),snd state)) next
    (fun '(nodes,heap) => (rotl nodes,qstep hdr nodes heap))
    ltac:(intros [[nodes values] heap]; reflexivity) n (ns,vs,h)) as Eheap.
  apply (f_equal (@snd (list nat) Heap)) in Eheap; cbn [fst snd] in Eheap.
  unfold rotlN, qstepN.
  rewrite <- Enodes, <- Evalues, <- Eheap.
  exact Hiter.
Qed.

(** [n] rotations expose all five observations per turn before the run from
    the [n]-times-rotated heap. *)
Theorem run_stepN: forall n hdr ns vs h allocs ctx c,
    qrep hdr ns vs h -> ns <> [] ->
    run hdr ((h, allocs), (ctx, c))
    ~ runN hdr n ns vs (h,allocs) c (run hdr ((qstepN hdr n ns h, allocs), (ctx, (c + n)%nat))).
Proof.
  intros n hdr ns vs h allocs ctx c Hq Hne.
  set (next := fun state : list nat * list nat * ManagedHeap * nat =>
    let '(nodes,values,memory,counter) := state in
    (rotl nodes,rotl values,(qstep hdr nodes (fst memory),snd memory),S counter)).
  set (batch := fun state : list nat * list nat * ManagedHeap * nat =>
    let '(nodes,values,memory,counter) := state in
    queue_turn_logs (CSLEmit (stamp (hd 0 values) counter)) hdr
      (hd 0 nodes) (hd 0 (tl nodes)) (last nodes 0) memory).
  set (root := fun state : list nat * list nat * ManagedHeap * nat =>
    let '(nodes,values,memory,counter) := state in run hdr (memory,(ctx,counter))).
  set (Inv := fun state : list nat * list nat * ManagedHeap * nat =>
    qrep hdr (fst (fst (fst state))) (snd (fst (fst state))) (fst (snd (fst state))) /\
    fst (fst (fst state)) <> [] /\ snd (snd (fst state)) = allocs).
  assert (Hnext : forall state, Inv state -> Inv (next state)).
  { intros [[[nodes values] [heap allocations]] counter] (Hrep & Hnodes & Halloc).
    cbn [Inv next] in *.
    split; [now apply qstep_qrep |].
    split; [now apply rotl_nonnil | exact Halloc]. }
  assert (Hnonempty : forall state, Inv state -> batch state <> []).
  { intros [[[nodes values] [heap allocations]] counter] _.
    cbn [batch queue_turn_logs]; discriminate. }
  assert (Hroot : forall state, Inv state ->
    root state ~ emit_list (batch state) (root (next state))).
  { intros [[[nodes values] [heap allocations]] counter] (Hrep & Hnodes & Halloc).
    cbn [Inv] in Hrep, Hnodes.
    destruct nodes as [|a nodes]; [contradiction |].
    destruct values as [|v values];
      [apply qrep_len in Hrep; cbn in Hrep; discriminate |].
    cbn [root batch next qstep hd tl fst snd].
    exact (run_step hdr a nodes v values heap allocations ctx counter Hrep). }
  assert (Eroot : forall state, Inv state -> root state ~
    (emit_batches batch next state : ctreeW (CSLObs nat) Bn (SSig * unit))).
  { apply emit_batches_bisim; assumption. }
  assert (Hinitial : Inv (ns,vs,(h,allocs),c)).
  { split; [exact Hq |]; split; [exact Hne | reflexivity]. }
  pose proof (@Nat.iter_invariant n _ next Inv Hnext
    (ns,vs,(h,allocs),c) Hinitial) as Hfinal.
  pose proof (@Nat.iter_swap_gen _ _
    (fun state => (fst (fst (fst state)),fst (snd (fst state)))) next
    (fun '(nodes,heap) => (rotl nodes,qstep hdr nodes heap))
    ltac:(intros [[[nodes values] [heap allocations]] counter]; reflexivity)
    n (ns,vs,(h,allocs),c)) as Eheap.
  apply (f_equal (@snd (list nat) Heap)) in Eheap.
  change (fst (snd (fst (Nat.iter n next (ns,vs,(h,allocs),c)))) =
    qstepN hdr n ns h) in Eheap.
  pose proof (@Nat.iter_swap_gen _ _ (@snd _ nat) next (Nat.add 1)
    ltac:(intros [[[nodes values] [heap allocations]] counter]; reflexivity)
    n (ns,vs,(h,allocs),c)) as Ecounter.
  cbn [fst snd] in Ecounter.
  rewrite nat_iter_add_const, Nat.mul_1_r, Nat.add_comm in Ecounter.
  transitivity (emit_batches batch next (ns,vs,(h,allocs),c) :
    ctreeW (CSLObs nat) Bn (SSig * unit)).
  - exact (Eroot _ Hinitial).
  - rewrite (emit_batches_prefix_sbisim batch next n (ns,vs,(h,allocs),c)).
    transitivity (emit_list
      (List.flat_map (fun j => batch (Nat.iter j next (ns,vs,(h,allocs),c))) (List.seq 0 n))
      (root (Nat.iter n next (ns,vs,(h,allocs),c)))).
    + apply emit_list_sbisim; symmetry; exact (Eroot _ Hfinal).
    + unfold runN; apply emit_list_sbisim.
      destruct (Nat.iter n next (ns,vs,(h,allocs),c)) as
        [[[nodes values] [heap allocations]] counter].
      unfold Inv in Hfinal; destruct Hfinal as (Hrep & Hnodes & Halloc).
      cbn [fst snd] in Hrep, Hnodes, Halloc, Eheap, Ecounter.
      cbn [root]; rewrite Eheap, Ecounter, Halloc; reflexivity.
Qed.
