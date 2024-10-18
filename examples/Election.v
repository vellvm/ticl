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
  Fin
  Vector
  List
  Classes.SetoidClass.

From ExtLib Require Import
  Data.Monads.StateMonad.

Set Implicit Arguments.

Import TiclNotations ICTreeNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

Section Election.
  Context {n: nat}.
  Notation Id := (fin' n).

  (*| Message passing in unidirectional ring |*)
  Variant msg :=
    | Candidate (u: Id)
    | Elected   (u: Id).

  Variant netE: Type :=
    | Recv
    | Send (m: msg).

  Variant memE: Type :=
    | Put (id: Id)
    | Get.

  Global Instance encode_netE: Encode netE :=
    fun e => match e with
          | Recv => msg
          | Send _ => unit
          end.

  Global Instance encode_idE: Encode memE :=
    fun e => match e with
          | Put _ => unit
          | Get => Id
          end.

  Definition send: msg -> ictree netE unit :=
    fun p => ICtree.trigger (Send p).

  Definition recv: ictree netE msg :=
    ICtree.trigger Recv.

  Notation sysE := (netE + memE).

  Definition put: Id -> ictree sysE unit :=
    fun id => ICtree.trigger (Put id).

  Definition get: ictree sysE Id :=
    ICtree.trigger Get.

  Notation Mails := (vec' n msg).
  Notation NetObs := (Id * msg).

  (* Local network instrumented semantics, write to [Mails] *)
  Definition h_sysE'(cycle: fin' n -> fin' n)
    : sysE ~> stateT (Id * Mails) (ictreeW (Id * msg)) :=
    fun e =>
      mkStateT
        (fun '(id, mail) =>
           match e return ictreeW (Id * msg) (encode e * (fin' n * vec' n msg)) with
           | inl (Send msg) =>
               log (id, msg) ;;
               Ret (tt, (id, mail @ cycle id := msg))
           | inl Recv =>
               log (id, mail $ id) ;;
               Ret (mail $ id, (id, mail))
           | inr Get =>
               Ret (id, (id, mail))
           | inr (Put id) =>
               Ret (tt, (id, mail))
           end).

  (* Always terminates, conditional on receiving either:
     1. (Candidate candidate), where candidate = id -- I received my own [id] back
     2. (Elected leader) -- Someone else was elected [leader]
   *)
  Definition elect(id: fin' n): ictree netE unit :=
    m <- recv ;;
    match m with
    | Candidate candidate =>
        match Fin_compare candidate id with (* candidate < id *)
        (* [left] neighbor proposed candidate, support her to [right]. *)
        | Gt => send (Candidate candidate)
        (* [left] neighbor proposed a candidate, do not support her. *)
        | Lt => Ret tt
        (* I am the leader, but only I know. Tell my [right] and return. *)
        | Eq => send (Elected id)
        end
    | Elected leader =>
        (* I am a follower and know the [leader] *)
        send (Elected leader)
    end.

  (* Uniring scheduler, picks initial [i] nondeterministically, then runs forever *)
  Definition elect_sched'(cycle: fin' n -> fin' n): ictree sysE _ :=
    i <- ICtree.branch n ;;
    put i ;;
    loop (
        i <- get ;;
        resumICtree (elect i) ;;
        put (cycle i);;
        continue
      ).

End Election.

From Equations Require Import Equations.
(* Run election for 3 workers *)
Import Fin.
Import VectorNotations.
Open Scope vector_scope.

Equations cycle(i: fin' 2) : fin' 2 :=
  cycle Fin.F1 := Fin.FS Fin.F1;
  cycle (Fin.FS Fin.F1) := Fin.FS (Fin.FS Fin.F1);
  cycle (Fin.FS (Fin.FS Fin.F1)) := Fin.F1.

Definition elect_sched := elect_sched' cycle.
Definition h_sysE := h_sysE' cycle.

(* Initial mailboxes are [F3, F1, F2] *)
Definition mailboxes: vec' 2 (fin' 2) :=
  Vector.cons _ (FS (FS F1)) _ (Vector.cons _ F1 _ (Vector.cons _ (FS F1) _ (Vector.nil _))).

Import Vectors.
Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.

Ltac run_head :=
  unfold iter, MonadIter_ictree;
  rewrite interp_state_unfold_iter, interp_state_bind, bind_bind,
    interp_state_vis, bind_bind;
  cbn;
  rewrite bind_ret_l, sb_guard, interp_state_ret, bind_ret_l, interp_state_bind, bind_bind,
    interp_state_resumICtree, bind_vis, interp_state_vis, bind_bind;
  cbn;
  repeat setoid_rewrite bind_bind;
  apply afl_log; eauto with ticl;
  rewrite ?bind_ret_l, sb_guard, interp_state_bind, bind_bind,
    interp_state_ret, bind_ret_l;
  unfold resum_ret, ReSumRet_refl, ReSumRet_inr;
  simp cycle; cbn.

Ltac run_body :=
  rewrite interp_state_vis; cbn;
  repeat setoid_rewrite bind_bind;
  eapply afl_log; eauto with ticl;
  rewrite ?bind_ret_l, sb_guard,
        interp_state_ret, bind_ret_l, interp_state_bind, bind_bind,
        interp_state_vis, bind_bind;
  cbn;
  rewrite bind_ret_l, sb_guard, interp_state_ret, bind_ret_l, interp_state_ret,
    bind_ret_l, sb_guard;
  simp cycle; cbn.

Ltac run_sched :=
  rewrite interp_state_ret, bind_ret_l, interp_state_bind,
    bind_bind, interp_state_vis, bind_bind;
  cbn;
  rewrite bind_ret_l, sb_guard,  interp_state_ret, bind_ret_l, interp_state_ret,
    bind_ret_l, sb_guard;
  simp cycle; cbn.

Lemma election3_liveness:
  <( {interp_state h_sysE elect_sched (F1, Vector.map Candidate mailboxes)}, Pure |=
          AF visW {fun '(id, msg) => exists e, msg = Elected e /\ id = e /\ e = FS (FS F1)} )>.
Proof with auto with ticl.
  intros.
  unfold elect_sched, elect_sched', ICtree.forever.
  cbn.
  rewrite interp_state_bind.
  unfold ICtree.branch.
  rewrite interp_state_br, bind_br.
  apply aul_br; right; split.
  - csplit...
  - intros i.
    unfold send, recv, put, get, ICtree.trigger.
    rewrite sb_guard, interp_state_ret, bind_ret_l, interp_state_bind,
      interp_state_vis, bind_bind.
    cbn.
    rewrite bind_ret_l, bind_guard, sb_guard, interp_state_ret, bind_ret_l,
      interp_state_unfold_iter, interp_state_bind, bind_bind,
      interp_state_vis, bind_bind.
    cbn.
    rewrite bind_ret_l, bind_guard, sb_guard, interp_state_ret, bind_ret_l,
      interp_state_bind, bind_bind, interp_state_resumICtree.
    (* Get into [elect] *)
    unfold elect.
    unfold send, recv, put, get, ICtree.trigger.
    rewrite interp_state_bind, bind_bind, interp_state_vis, bind_bind.
    cbn.
    repeat setoid_rewrite bind_bind.
    eapply afl_log...
    rewrite ?bind_ret_l, sb_guard, interp_state_ret, bind_ret_l.
    unfold resum_ret, ReSumRet_refl, ReSumRet_inl.
    ddestruction i; [|ddestruction i; [|ddestruction i]]; simpl; simp cycle.
    + (* Start with F1 *)
      rewrite interp_state_vis, bind_bind.
      cbn.
      repeat setoid_rewrite bind_bind.
      apply afl_log...
      rewrite ?bind_ret_l, sb_guard.
      (* sched *)
      run_sched.
      simp cycle; cbn.
      (* F2 *)
      run_head; run_body.
      (* F3 *)
      run_head; run_body.
      (* Done *)
      cleft; csplit.
      eexists; intuition.
    + (* sched *)
      run_sched.
      (* F3 *)
      run_head; run_sched.
      (* F1 *)
      run_head; run_body.
      (* F2 *)
      run_head; run_body.
      (* F3 *)
      run_head; run_body.
      (* Done *)
      cleft; csplit.
      eexists; intuition.
    + (* F3 *)
      run_sched.
      (* F1 *)
      run_head; run_body.
      (* F2 *)
      run_head; run_body.
      (* F3 *)
      run_head; run_body.
      (* Done *)
      cleft; csplit.
      eexists; intuition.
    + ddestruction i.
Qed.
Print Assumptions election3_liveness.
