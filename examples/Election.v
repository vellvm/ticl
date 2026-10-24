From TICL Require Import
  CTree.Core
  Logic.Core
  Utils.Vectors
  CTree.Logic.AG
  CTree.Logic.AF
  CTree.Logic.AX
  CTree.Logic.State
  CTree.Logic.Iter
  CTree.Logic.Bind
  CTree.Interp.State.Mod
  CTree.Events.Writer.

From Stdlib Require Import
  Lia
  Fin
  Vector
  Classes.SetoidClass.

From Equations Require Import Equations.

Set Implicit Arguments.

Import TiclNotations CTreeNotations CTree.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

Module Type Cyclic.
  Parameter (n: nat) (next: fin' n -> fin' n).
End Cyclic.

Module ElectionDefs(C: Cyclic).
  Import C.
  Abbreviation Id := (fin' n). 
  
  (*| Message passing in unidirectional ring |*)
  Variant msg :=
    | Candidate (u: Id)
    | Elected   (u: Id).

  Abbreviation Mails := (vec' n msg).
  
  Variant netE: Type -> Type :=
    | Recv (from: Id): netE msg
    | Send (from: Id) (m: msg): netE unit.

  (** The scheduler's initial pick is a visible finite choice, so the branch signature is [Bn]. *)
  Definition send: Id -> msg -> ctree netE Bn unit :=
    fun i p => CTree.trigger (Send i p).

  Definition recv: Id -> ctree netE Bn msg :=
    fun i => CTree.trigger (Recv i).

  (* Local network instrumented semantics, instrument [Send] *)
  Definition h_netE
    : netE ~> stateT Mails (ctreeW msg Bn) :=
    fun _ e mails =>
      match e in netE X return ctreeW msg Bn (Mails * X) with
      | Send id msg =>
          let next := next id in
          Ret (mails @ next := msg, tt)
      | Recv id =>
          let msg := mails $ id in
          log msg ;;
          Ret (mails, msg)
      end.
  
  Lemma aur_recv: forall (x: Id) (ms: Mails) w,
      not_done w ->
      <[ {interp_state h_netE (recv x) ms}, w |=
           AF (AX (done= {(ms, ms $ x)} {Obs (Log (ms $ x)) tt})) ]>.
  Proof.
    intros.
    unfold recv.
    rewrite interp_state_trigger; cbn.
    rewrite bind_bind.
    apply aur_log.
    - rewrite bind_ret_l, sb_guard.
      cleft.
      apply axr_ret; eauto with ticl.
    - csplit; eauto with ticl.
  Qed.

  Lemma aur_send: forall (x: Id) (ms: Mails) (m: msg) w,
    not_done w ->
     <[ {interp_state h_netE (send x m) ms}, w |=
         AF (AX (done= {(ms @ (next x) := m, tt)} w)) ]>.
  Proof.
    intros.
    unfold send.
    rewrite interp_state_trigger; cbn.
    rewrite bind_ret_l, sb_guard.
    cleft.
    apply axr_ret; eauto with ticl.
  Qed.
  
  (* Always terminates, conditional on receiving either:
     1. (Candidate candidate), where candidate = id -- I received my own [id] back
     2. (Elected leader) -- Someone else was elected [leader]
   *)
  Definition elect(id: Id): ctree netE Bn unit :=
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

  (* Uniring scheduler, picks initial [i] nondeterministically (visible choice), then runs forever *)
  Definition elect_sched: ctree netE Bn void :=
    i <- branchS (branchn (S n)) ;;
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

  Abbreviation id1 := Fin.F1.
  Abbreviation id2 := (Fin.FS (Fin.F1)).
  Abbreviation id3 := (Fin.FS (Fin.FS (Fin.F1))).

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

  Definition ranking (id: Id) (mailboxes: Mails) :=
    match id, mailboxes with
    | id2, {{ Candidate id3, Candidate id3, Candidate id2 }} => 0
    | id1, {{ Candidate id3, Candidate id1, Candidate id2 }} => 1
    | id3, {{ Candidate id3, Candidate id1, Candidate id2 }} => 2
    | id2, {{ Candidate id3, Candidate id1, Candidate id2 }} => 3
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
    <[ {interp_state h_netE (elect i) m}, {w} |= AF (AX (done= {(m', tt)} {Obs (Log (m $ i)) tt})) ]>.
  Proof.
    intros.
    unfold elect.
    eapply aur_state_bind_r_eq.
    - eapply aur_recv; eauto with ticl.
    - destruct (m $ i) eqn:Hm.
      + destruct (Fin_compare u i) eqn:Hcomp; subst.
        * apply aur_send; eauto with ticl.
        * cleft.
          rewrite interp_state_ret.
          apply axr_ret; eauto with ticl.
        * apply aur_send; eauto with ticl.
      + subst.
        apply aur_send; eauto with ticl.
  Qed.

  Ltac vroom :=
    eapply aur_state_bind_r_eq;
    [apply aur_elect; eauto with ticl; try exact mailboxes 
    | cleft; first [apply axr_state_ret | rewrite interp_state_ret; apply axr_ret];
      eauto with ticl; try eexists; intuition; try simp next; eauto with ticl].

  Lemma election3_liveness:
    <( {interp_state h_netE elect_sched mailboxes}, Pure |= AF visW {fun msg => msg = Elected id3} )>.
  Proof.
    intros.
    unfold elect_sched, mailboxes.
    eapply aul_state_bind_r with (R:=fun _ σ' w' => σ' = mailboxes /\ w' = Pure).
    - cright.
      unfold branchS; apply anr_state_brS with (y:=Fin.F1); split.
      + csplit; eauto with ticl.
      + intros.
        apply aur_state_ret; eauto with ticl.
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
                       | _ => fun _ _ => False 
                       end eq_refl eq_refl
                   | _ => False
                   end)
           (f:=fun id ms _ => ranking id ms); eauto with ticl.
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
      eapply aul_state_iter_next_eq; eauto with ticl.
      * vroom.
      * do 2 (eapply aul_state_iter_next_eq; eauto with ticl; [vroom|simp next; cbn]).
        cleft. csplit; eauto with ticl.
  Qed.
  Print Assumptions election3_liveness.
End Election3.
