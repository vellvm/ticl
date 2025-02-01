From TICL Require Import
  ICTree.Core
  Logic.Core
  Utils.Vectors
  ICTree.Equ
  ICTree.SBisim
  ICTree.Logic.AG
  ICTree.Logic.AF
  ICTree.Logic.AX
  ICTree.Logic.State
  ICTree.Logic.Iter
  ICTree.Logic.Bind
  ICTree.Interp.State
  ICTree.Events.Writer.

From Coq Require Import
  Lia
  Fin
  Vector
  Classes.SetoidClass.

From ExtLib Require Import
  Data.Monads.StateMonad.

From Equations Require Import Equations.

Set Implicit Arguments.

Import TiclNotations ICTreeNotations ICtree.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

Module Type Cyclic.
  Parameter (n: nat) (next: fin' n -> fin' n).
End Cyclic.

Module ElectionDefs(C: Cyclic).
  Import C.
  Notation Id := (fin' n). 
  
  (*| Message passing in unidirectional ring |*)
  Variant msg :=
    | Candidate (u: Id)
    | Elected   (u: Id).

  Notation Mails := (vec' n msg).
  
  Variant netE: Type :=
    | Recv (from: Id)
    | Send (from: Id) (m: msg).

  Global Instance encode_netE: Encode netE :=
    fun e => match e with
          | Recv _ => msg
          | Send _ _ => unit
          end.

  Definition send: Id -> msg -> ictree netE unit :=
    fun i p => trigger (Send i p).

  Definition recv: Id -> ictree netE msg :=
    fun i => trigger (Recv i).

  (* Local network instrumented semantics, instrument [Send] *)
  Definition h_netE
    : netE ~> stateT Mails (ictreeW msg) :=
    fun e =>
      mkStateT
        (fun mails =>
           match e return ictreeW msg (encode e * Mails) with
           | Send id msg =>
               let next := next id in
               Ret (tt, mails @ next := msg)
           | Recv id =>
               let msg := mails $ id in
               log msg ;;
               Ret (msg, mails)
           end).
  
  Lemma aur_recv: forall (x: Id) (ms: Mails) w,
      not_done w ->
      <[ {interp_state h_netE (recv x) ms}, w |=
           AF (AX (done= {(ms $ x, ms)} {Obs (Log (ms $ x)) tt})) ]>.
  Proof with eauto with ticl.
    intros.
    unfold recv, trigger.
    rewrite interp_state_vis; cbn.
    rewrite bind_bind.
    apply aur_log.
    - rewrite bind_ret_l, sb_guard, interp_state_ret.
      cleft.
      apply axr_ret...
    - csplit...
  Qed.

  Lemma aur_send: forall (x: Id) (ms: Mails) (m: msg) w,
    not_done w ->
     <[ {interp_state h_netE (send x m) ms}, w |=
         AF (AX (done= {(tt, ms @ (next x) := m)} w)) ]>.
  Proof with eauto with ticl.
    intros.
    unfold send, trigger.
    rewrite interp_state_vis; cbn.
    rewrite bind_ret_l, sb_guard, interp_state_ret.
    cleft.
    apply axr_ret...
  Qed.
  
  (* Always terminates, conditional on receiving either:
     1. (Candidate candidate), where candidate = id -- I received my own [id] back
     2. (Elected leader) -- Someone else was elected [leader]
   *)
  Definition elect(id: Id): ictree netE unit :=
    m <- recv id ;;
    match m with
    | Candidate candidate =>
        match Fin_compare candidate id with (* candidate < id *)
        (* [left] neighbor proposed candidate, support her to [right]. *)
        | Gt => send id (Candidate candidate)
        (* [left] neighbor proposed a candidate, do not support her. *)
        | Lt => Ret tt
        (* I am the leader, but only I know. Tell my [right] and return. *)
        | Eq => send id (Elected id)
        end
    | Elected leader =>
        (* I am a follower and know the [leader] *)
        send id (Elected leader)
    end.

  (* Uniring scheduler, picks initial [i] nondeterministically, then runs forever *)
  Definition elect_sched: ictree netE void :=
    i <- branch n ;;
    iter (fun i =>
            elect i ;;
            Ret (inl (next i))
      ) i.

End ElectionDefs.

Module Cyclic3 <: Cyclic.
  Definition n:=2.
  (* It is really hard to write [(a + 1) % n] with dependent fin for any n. *)
  Equations next(i: fin' 2) : fin' 2 :=
    next Fin.F1 := Fin.FS Fin.F1;
    next (Fin.FS Fin.F1) := Fin.FS (Fin.FS Fin.F1);
    next (Fin.FS (Fin.FS Fin.F1)) := Fin.F1.
End Cyclic3.

(* Run election for 3 workers *)
Import VectorNotations Vectors.
Open Scope vector_scope.

Module Election3.
  Module E := ElectionDefs(Cyclic3).
  Import E Cyclic3.

  Notation id1 := Fin.F1.
  Notation id2 := (Fin.FS (Fin.F1)).
  Notation id3 := (Fin.FS (Fin.FS (Fin.F1))).

  Notation "{{ a , b , c }}" :=
    (Vector.cons _ a _
       (Vector.cons _ b _
          (Vector.cons _ c _
             (Vector.nil _)))).

  Ltac ddestruction3 x :=
    dependent destruction x;
    [| dependent destruction x;
       [| dependent destruction x;
          [| dependent destruction x]]].

  Lemma next_neq: forall x,
      next x <> x.
  Proof.
    intros.
    ddestruction3 x; simp next; intros Hcontra; inv Hcontra.
  Qed.

  Lemma mget_mset_eq: forall (ms: Mails) (x: Id) m,
      ((ms @ x := m) $ x) = m.
  Proof.
    intros.
    repeat dependent destruction ms.
    ddestruction3 x; simp next; cbn; reflexivity.
  Qed.
  
  Lemma mget_mset_neq: forall (ms: Mails) (x: Id) m,
      ((ms @ next x := m) $ x) = (ms $ x).
  Proof.
    intros.
    repeat dependent destruction ms.
    ddestruction3 x; simp next; cbn; reflexivity.
  Qed.

  Definition ranking (id: Id) (mailboxes: Mails) :=
    match id, mailboxes with
    | id1, {{ Candidate id3, Candidate id1, Candidate id2 }} => 2
    | id2, {{ Candidate id3, Candidate id3, Candidate id2 }} => 1
    | id3, {{ Candidate id3, Candidate id3, Candidate id3 }} => 0
    | id2, {{ Candidate id3, Candidate id1, Candidate id2 }} => 4
    | id3, {{ Candidate id3, Candidate id1, Candidate id2 }} => 3
    | _, _ => 10
    end.

  (* Initial mailboxes are [F3, F1, F2] *)
  Definition mailboxes: Mails :=
    {{ Candidate id3, Candidate id1, Candidate id2 }}.

  Lemma aur_elect: forall w (m' m: Mails) (i: Id) m',
    not_done w ->
    match m $ i with
    | Candidate candidate =>
        match Fin_compare candidate i with (* candidate < id *)
        (* [left] neighbor proposed candidate, support her to [right]. *)
        | Gt => m' = (m @ (next i) := (Candidate candidate))
        (* [left] neighbor proposed a candidate, do not support her. *)
        | Lt => m' = m
        (* I am the leader, but only I know. Tell my [right] and return. *)
        | Eq => m' = (m @ (next i) := (Elected i))
        end
    | Elected leader => m' = (m @ (next i) := (Elected leader))
    end ->
    <[ {interp_state h_netE (elect i) m}, {w} |= AF (AX (done= {(tt, m')} {Obs (Log (m $ i)) tt})) ]>.
  Proof with eauto with ticl.
    intros.
    unfold elect.
    eapply aur_state_bind_r_eq.
    - eapply aur_recv...
    - destruct (m $ i) eqn:Hm.
      + destruct (Fin_compare u i) eqn:Hcomp; subst.
        * apply aur_send...
        * cleft.
          apply axr_state_ret...
        * apply aur_send...
      + subst.
        apply aur_send...
  Qed.

  Ltac vroom :=
    eapply aur_state_bind_r_eq;
    [apply aur_elect; eauto with ticl; try exact mailboxes 
    | cleft; apply axr_state_ret; eauto with ticl; eexists; intuition; simp next; eauto with ticl].

  Local Typeclasses Transparent equ.
  Local Typeclasses Transparent sbisim.
  Lemma election3_liveness:
    <( {interp_state h_netE elect_sched mailboxes}, Pure |= AF visW {fun msg => msg = Elected id3} )>.
  Proof with eauto with ticl.
    intros.
    unfold elect_sched, mailboxes.
    eapply aul_state_bind_r with (R:=fun _ σ' w' => σ' = mailboxes /\ w' = Pure).
    - cright.
    apply anr_state_br; split.
      + csplit...
      + intros.
        apply aur_state_ret...
    - intros * (-> & ->).
      unfold mailboxes.
      (* iter loop *)
      eapply aul_state_iter_split_nat
        with (Ri:=fun i ms w => (* Intermediate goal, full [Candidate id3] propagation *)
                    w = Obs (Log (Candidate id3)) tt /\
                      i = id3 /\
                      ms = {{ Candidate id3, Candidate id3, Candidate id3 }})
             (R:=fun (i: Id) (ms: Mails) (w: WorldW msg) =>
                   match w with
                   | Pure => i = x /\ ms = mailboxes
                   | Obs (Log (Candidate p)) tt => 
                       match (i, p) return _ = fin' 2 -> _ = fin' 2 -> Prop with
                       | (id2, id3) => fun _ _ => ms = {{ Candidate id3, Candidate id3, Candidate id2 }}
                       | (id3, id1) => fun _ _ => ms = {{ Candidate id3, Candidate id1, Candidate id2 }}
                       | (id1, id2) => fun _ _ => ms = {{ Candidate id3, Candidate id1, Candidate id2 }}
                       | _ => fun _ _ => False (* Only when w = Pure *)
                       end eq_refl eq_refl
                 | _ => False
                 end)
           (f:=fun id ms _ => ranking id ms)...
    + (* Prove it gets to the intermediate state *)
      intros; intuition; subst.
      rename σ into m.
      unfold mailboxes.
      inv H.
      * destruct H0 as (-> & ->).
        unfold mailboxes.
        ddestruction3 x; right.
        -- (* x = 1 *) vroom.
        -- (* x = 2 *) vroom.
        -- (* x = 3 *) vroom.
      * destruct e, v.
        repeat ddestruction m.
        destruct m0; try contradiction.
        ddestruction3 i; ddestruction3 u; inv H0. 
        -- (* i = 1, p = 3 *)
          right. vroom.
        -- (* i = 2, p = 3 *)
          left. (* bingo! *)
          vroom.
        -- right. vroom.
    + (* At checkpoint, now everything is deterministic *)
      intros i w m _ (-> & ? & ->); subst.
      eapply aul_state_iter_next_eq...
      * vroom.
      * do 2 (eapply aul_state_iter_next_eq; eauto with ticl; [vroom|simp next; cbn]).
        cleft.
        csplit...
  Qed.
  Print Assumptions election3_liveness.
End Election3.
