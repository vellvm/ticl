(** * Trace: the state trajectory of the rotating queue.

    SHARED between the two proof families.  Nothing here is a separation-logic
    notion: [qstepN] is just "the heap after [n] rotations", and [run_stepN]
    says that this is the same thing as "[n] observations into the run".  Both
    families need to talk about reachable states, so both import this file. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Interp.State.Mod
  ICTree.Events.State
  ICTree.Events.Writer
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.State
  Logic.Core.

From examples Require Import CSL.HeapQ CSL.QLang.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.

(** One completed rotation of the run: a single logged pop, then the run from
    the rotated heap.  This is [QLang.rot_body_spec] lifted through the
    iteration; the [Guard] is discharged by [sb_guard], so no stuttering
    theory is needed. *)
Lemma run_step: forall hdr a ns v vs h c,
    qrep hdr (a :: ns) (v :: vs) h ->
    run hdr h c
    ~ (log (Pop v c) ;; run hdr (rot_heap hdr a (hdf ns 0) (zof hdr ns) h) (S c)).
Proof.
  intros hdr a ns v vs h c Hq.
  unfold run, rotate.
  rewrite interp_state_unfold_iter.
  cbv beta.
  rewrite (rot_body_spec hdr a ns v vs h c Hq).
  rewrite bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l.
  apply sb_guard.
Qed.

(** The heap after one rotation, and after [n] of them. *)
Definition qstep (hdr: nat) (ns: list nat) (h: Heap) : Heap :=
  match ns with
  | [] => h
  | a :: ns' => rot_heap hdr a (hdf ns' 0) (zof hdr ns') h
  end.

Fixpoint qstepN (hdr: nat) (n: nat) (ns: list nat) (h: Heap) : Heap :=
  match n with
  | 0 => h
  | S k => qstepN hdr k (rotl ns) (qstep hdr ns h)
  end.

Fixpoint rotlN {A} (n: nat) (l: list A) : list A :=
  match n with 0 => l | S k => rotlN k (rotl l) end.

(** The observation prefix of [n] rotations, with the continuation threaded so
    that no [bind]-associativity reasoning is needed. *)
Fixpoint runN (hdr: nat) (n: nat) (ns vs: list nat) (h: Heap) (c: nat)
              (k: ictreeW QObs (unit * Sig)) : ictreeW QObs (unit * Sig) :=
  match n with
  | 0 => k
  | S m => log (Pop (hd 0 vs) c) ;;
           runN hdr m (rotl ns) (rotl vs) (qstep hdr ns h) (S c) k
  end.

Lemma rotl_nonnil: forall (l: list nat), l <> [] -> rotl l <> [].
Proof.
  intros [| a l] H; [contradiction |]; cbn.
  intro C; apply app_eq_nil in C as (_ & C); discriminate.
Qed.

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
  induction n as [| n IH]; intros hdr ns vs h Hq Hne; [split; assumption |].
  cbn [qstepN rotlN].
  apply (IH hdr (rotl ns) (rotl vs));
    [now apply qstep_qrep | now apply rotl_nonnil].
Qed.

(** [n] rotations of the run are [n] logged pops followed by the run from the
    [n]-times-rotated heap. *)
Theorem run_stepN: forall n hdr ns vs h c,
    qrep hdr ns vs h -> ns <> [] ->
    run hdr h c ~ runN hdr n ns vs h c (run hdr (qstepN hdr n ns h) (c + n)).
Proof.
  induction n as [| n IH]; intros hdr ns vs h c Hq Hne.
  - cbn [runN qstepN]; rewrite Nat.add_0_r; reflexivity.
  - destruct ns as [| a ns']; [contradiction |].
    destruct vs as [| v vs']; [apply qrep_len in Hq; cbn in Hq; discriminate |].
    cbn [runN qstepN qstep hd].
    rewrite (run_step hdr a ns' v vs' h c Hq).
    apply sbisim_clo_bind_eq; [reflexivity | intros []].
    rewrite <- Nat.add_succ_comm.
    apply (IH hdr (rotl (a :: ns')) (rotl (v :: vs'))).
    + cbn [rotl]; apply (rot_heap_spec hdr a ns' v vs' h Hq).
    + apply rotl_nonnil; discriminate.
Qed.
