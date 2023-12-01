From CTree Require Import
  KTree.Core
  KTree.Trans
  Logic.Kripke
  Logic.Ctl
  KTree.Events.Net.

From Coq Require Import
  List
  Fin
  Classes.SetoidClass
  Classes.SetoidDec.

From RelationAlgebra Require Import rel srel monoid.

Set Implicit Arguments.

Import KTreeNotations ListNotations IOQueues CtlNotations.
Local Open Scope ktree_scope.
Local Open Scope list_scope.
Local Open Scope ctl_scope.

Section Election.
  Context (n: nat).
  Notation uid := (uid n).
  Variant message :=
    | Candidate (u: uid)
    | Elected (u: uid).

  Notation netE := (netE n).

  Definition msg_id(m: message): uid :=
    match m with
    | Candidate u => u
    | Elected u => u
    end.

  Definition eqb_message(a b: message): bool :=
    match a, b with
    | Candidate a, Candidate b => Fin.eqb a b
    | Elected a, Elected b => Fin.eqb a b
    | _, _ => false
    end.

  Definition proc(id: uid)(right: uid): ktree (netE message) unit :=
    Ktree.iter
      (fun _ =>
         m <- recv id;;
         match m with
         | Some (Candidate candidate) =>
             match Fin_compare candidate id with (* candidate < id *)
             (* My [left] neighbor proposed a candidate, I support that candidate *)
             | Gt => send id right (Candidate candidate) ;; Ret (inl tt)
             (* My left neighbor proposed a candidate, I do not support him *)
             | Lt => Ret (inl tt)
             (* I am the leader, but only I know *)
             | Datatypes.Eq => send id right (Elected id) ;; Ret (inr tt)
             end
         | Some (Elected x) =>
             (* I know [x] is the leader *)
             send id right (Elected x) ;; Ret (inr tt)
         | None => Ret (inl tt) (* Didn't receive anything *)
         end) tt.

  Notation Qs := (list message * (list (uid * message)))%type  (only parsing).

  Definition QS : EqType :=
    {| type_of := Qs ; Eq := eq |}.

  Lemma candidate_left_gt: forall id right left out,
      Fin_compare left id = Gt ->
      <( {(proc id right, ([Candidate left], out))} |= AF (now {fun '(inp', out') => inp' = [] /\ out' = out ++ [(id, Candidate left)]}) )>.
  Proof.
    intros.
    apply ctl_af_star_det.
    apply trans_det.
    eexists.
    setoid_rewrite transF_trans_star_iff.
    split.
    exists 2.
    Opaque Eq.
    unfold proc.
    simpl.
    reflexivity.
    cbn.
    unfold Ktree.subst'.

    reflexivity.
    reflexivity.
    cbn.
    next.
    right.
    next.
    intros [p' σ'] TRp.
    cbn in TRp.

(** Equivalence of queues.
    Qs are pairwise either
    1. equal (no diff)
    2. their diff is messages from i -> j, where i < j
 *)
Inductive qequiv(i: uid): list message -> list message -> Prop :=
| QRefl: forall l,
    qequiv i l l
| QNoProgressL: forall h ts l,
  msg_id h < i ->
  qequiv i ts l ->
  qequiv i (h::ts) l
| QNoProgressR: forall h ts l,
  msg_id h < i ->
  qequiv i l ts ->
  qequiv i l (h::ts).
Hint Constructors qequiv: core.

(** Lift an index relation [nat -> rel T] to a [nat -> rel (list T)] *)
Inductive pairwisei T (p: nat -> T -> T -> Prop): nat -> list T -> list T -> Prop :=
| QDone: pairwisei p 0 [] []
| QStep: forall h h' ts ts' n,
  p n h h' ->
  pairwisei p n ts ts' ->
  pairwisei p (S n) (h::ts) (h'::ts').
Hint Constructors pairwisei: core.

(** Lists must be equal size *)
Lemma pairwisei_length: forall T p n (l l': list T),
    pairwisei p n l l' -> length l = length l'.
Proof. induction 1; cbn; auto. Qed.

(** Now define equivalence of queues *)
Definition qsequiv a b := pairwisei qequiv (length a) a b.
Notation "a ⩸ b" := (qsequiv a b) (at level 52, left associativity).
Hint Unfold qsequiv: core.
Arguments qsequiv _ _ /.
Ltac inv H := inversion H; subst; clear H.

#[global] Instance Equivalence_qequiv n: Equivalence (qequiv n).
Proof.
  constructor; red.
  - apply QRefl.
  - induction 1; auto.
  - intros.
    generalize dependent x.
    induction H0; intros; auto.
    apply IHqequiv.
    admit.
Admitted.

#[global] Instance Equivalence_qsequiv: Equivalence qsequiv.
Proof.
  constructor.
  - red; induction x; auto.
    unfold qsequiv; cbn.
    apply QStep; auto.
  - red; intros x y H. cbn in *.
    assert(EqLen:length x = length y) by (now apply pairwisei_length in H).
    rewrite <- EqLen; clear EqLen.
    remember (length x).
    induction H; cbn in *; auto.
    apply QStep; auto.
    inv Heqn.
    now symmetry.
  - red; intros.
Admitted.

(** This the "no constraint" relation # of Event structures.
    It means those messages have no causal order and could be scheduled in any way *)
Reserved Notation "a # b" (at level 52, left associativity).
Inductive netE_noconflict: forall {X Y}, netE message X -> netE message Y -> Prop :=
| RecvAnyOrder: forall from to,
    Recv from # Recv to
| SendAnyOrder: forall from from' to to' m m',
    Send from to m # Send from' to' m'
where "a # b" := (netE_noconflict a b).

#[global] Instance Equivalence_netE {X}: Equivalence (@netE_noconflict X X).
Proof.
  constructor; red.
  - intros.
    constructor.
Reserved Notation "a ⪯ b" (at level 52, left associativity).
Inductive netE_order: netE message -> netE message -> Prop :=
| SendRecvLt: forall from to m,
    Send from to m ⪯ Recv to
where "a ⪯ b" := (netE_order a b).


    length qs = length qs' ->
    Forall (fun '(l, l') =>
              let d = diff l l' in
              d = [] \/ Forall (fun msg => diff l l'combine qs qs'
    Forall (fun l => forall i, In l i -> diff l l'
    msg_id msg < i ->
    qequiv l l'
| NoMsg:
| BadMsg:
  msg_id
  qequiv h :: ts h' :: ts'
