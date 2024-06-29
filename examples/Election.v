From CTree Require Import
  CTree.Core
  Logic.Ctl
  Utils.Vectors
  CTree.Equ
  CTree.SBisim
  CTree.Logic.AG
  CTree.Logic.AF
  CTree.Logic.AX
  CTree.Logic.State
  CTree.Logic.Iter
  CTree.Logic.Bind
  CTree.Interp.State
  CTree.Events.Writer.

From Coq Require Import
  Fin
  Vector
  List
  Classes.SetoidClass.

From ExtLib Require Import
  Data.Monads.StateMonad.

Set Implicit Arguments.

Import CtlNotations CTreeNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ctl_scope.

Section Election.
  Context {n: nat}.
  Notation Id := (fin' n).
  
  (*| Message passing in unidirectional ring |*)
  Variant msg :=
    | Candidate (u: Id)
    | Elected   (u: Id).

  Variant netE: Type :=
    | Recv
    | Send (m: msg)
    | Seti (id: Id)
    | Geti.
  
  Global Instance encode_netE: Encode netE :=
    fun e => match e with
          | Recv => msg
          | Send _ => unit
          | Seti _ => unit
          | Geti => Id
          end.
  
  Definition send: msg -> ctree netE unit :=
    fun p => Ctree.trigger (Send p).
  
  Definition recv: ctree netE msg :=
    Ctree.trigger Recv.

  Definition set: Id -> ctree netE unit :=
    fun id => Ctree.trigger (Seti id).

  Definition get: ctree netE Id :=
    Ctree.trigger Geti. 
    
  Notation Mails := (vec' n msg).
  Notation NetObs := (Id * msg).
  
  (* Local network instrumented semantics, write to [Mails] *)
  Definition h_netE'(cycle: fin' n -> fin' n): netE ~> stateT (Id * Mails) (ctreeW NetObs) := 
    fun e =>
      mkStateT
        (fun '(id, mail) =>
           match e return ctreeW NetObs (encode e * (fin' n * vec' n msg)) with
           | Send msg =>
               log (id, msg) ;;
               Ret (tt, (id, mail @ cycle id := msg))
           | Recv =>
               log (id, mail $ id) ;;
               Ret (mail $ id, (id, mail))
           | Geti =>
               Ret (id, (id, mail))
           | Seti id =>
               Ret (tt, (id, mail))
           end).
    
  (* Always terminates, conditional on receiving either:
     1. (Candidate candidate), where candidate = id -- I received my own [id] back 
     2. (Elected leader) -- Someone else was elected [leader]
   *)
  Definition elect(id: fin' n): ctree netE unit :=
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
  Definition elect_sched'(cycle: fin' n -> fin' n): ctree netE void :=
    i <- Ctree.branch n ;;
    set i ;;
    Ctree.forever void
      (fun _ =>
         i <- get ;;
         elect i ;;
         set (cycle i)
      ) tt.

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
Definition h_netE := h_netE' cycle.

(* Initial mailboxes are [F3, F1, F2] *)
Definition mailboxes: vec' 2 (fin' 2) := 
  Vector.cons _ (FS (FS F1)) _ (Vector.cons _ F1 _ (Vector.cons _ (FS F1) _ (Vector.nil _))).

Import Vectors.
Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.

Ltac run_elect :=
  unfold iter, MonadIter_ctree;
  rewrite interp_state_unfold_iter, interp_state_map, bind_map;
  rewrite interp_state_bind, bind_bind;
  rewrite (@interp_state_trigger _ _ _ _ _ _ Geti _); cbn;
  rewrite bind_bind, bind_ret_l, sb_guard, bind_ret_l, interp_state_bind, bind_bind,
    interp_state_bind, bind_bind;
  setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ Recv _); cbn;
  repeat setoid_rewrite bind_bind;
  apply aul_log_r; eauto with ctl;
  rewrite bind_ret_l, sb_guard, bind_ret_l; cbn;
  setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Send _) _); simpl;
  repeat setoid_rewrite bind_bind;
  eapply aul_log_r; eauto with ctl;
  rewrite bind_ret_l, sb_guard, bind_ret_l;
  setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Seti _) _); simpl;
  setoid_rewrite bind_bind;
  rewrite bind_ret_l, sb_guard, bind_ret_l, sb_guard;
  simp cycle; cbn.

Ltac run_elect' :=
  unfold iter, MonadIter_ctree;
  rewrite interp_state_unfold_iter, interp_state_map, bind_map;
  rewrite interp_state_bind, bind_bind;
  rewrite (@interp_state_trigger _ _ _ _ _ _ Geti _); cbn;
  rewrite bind_bind, bind_ret_l, sb_guard, bind_ret_l, interp_state_bind, bind_bind,
    interp_state_bind, bind_bind;
  setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ Recv _); cbn;
  repeat setoid_rewrite bind_bind;
  apply aul_log_r; eauto with ctl;
  rewrite bind_ret_l, sb_guard, bind_ret_l; cbn;
  rewrite interp_state_ret, bind_ret_l;
  setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Seti _) _); simpl;
  setoid_rewrite bind_bind;
  rewrite bind_ret_l, sb_guard, bind_ret_l, sb_guard;
  simp cycle; cbn.

Lemma election3_liveness:
  <( {interp_state h_netE elect_sched (F1, Vector.map Candidate mailboxes)}, Pure |=
          AF visW {fun '(id, msg) => exists e, msg = Elected e /\ id = e /\ e = FS (FS F1)} )>.
Proof with auto with ctl.
  intros.
  unfold elect_sched, elect_sched', Ctree.forever.  
  cbn.
  rewrite interp_state_bind.
  unfold Ctree.branch.
  rewrite interp_state_br, bind_br.
  apply aul_br; right; split.
  - csplit...
  - intros i.
    rewrite sb_guard, interp_state_ret, bind_ret_l, interp_state_bind.
    setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Seti _) _); cbn.
    rewrite bind_bind, bind_ret_l, bind_guard, sb_guard, bind_ret_l.
    rewrite interp_state_unfold_iter, interp_state_map, bind_map.
    rewrite interp_state_bind, bind_bind.
    setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ Geti _); cbn.
    rewrite bind_bind, bind_ret_l, sb_guard, bind_ret_, interp_state_bind, bind_bind.
    (* Get into [elect] *)
    unfold elect.
    rewrite interp_state_bind, bind_bind. 
    rewrite (@interp_state_trigger _ _ _ _ _ _ Recv _); cbn.             
    repeat setoid_rewrite bind_bind.
    eapply aul_log_r...
    rewrite bind_ret_, sb_guard, bind_ret_l.
    ddestruction i; [|ddestruction i; [|ddestruction i]]; simpl; simp cycle.
    + (* Start with F1 *)
      setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Send (Candidate _)) _); simpl.   
      repeat setoid_rewrite bind_bind.
      apply aul_log_r...
      rewrite bind_ret_l, sb_guard, bind_ret_l.
      setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Seti _) _); simpl.
      setoid_rewrite bind_bind.
      rewrite bind_ret_l, sb_guard, bind_ret_l, sb_guard.
      simp cycle; cbn.
      (* F2 *)
      run_elect.
      (* F3 *)
      run_elect.
      (* Done *)
      cleft.
      csplit.
      eexists; intuition.
    + (* F2 *)
      rewrite interp_state_ret, bind_ret_l.
      setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Seti _) _); simpl.
      rewrite bind_bind, bind_ret_l, sb_guard, bind_ret_l, sb_guard.
      (* F3 *)
      run_elect'.
      (* F1 *)
      run_elect.
      (* F2 *)
      run_elect.
      (* F3 *)
      run_elect.
      (* Done *)
      cleft.
      csplit.
      eexists; intuition.
    + (* F3 *)
      rewrite interp_state_ret, bind_ret_l.
      setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Seti _) _); simpl.
      rewrite bind_bind, bind_ret_l, sb_guard, bind_ret_l, sb_guard.
      (* F1 *)
      run_elect.
      (* F2 *)
      run_elect.
      (* F3 *)
      run_elect.
      (* Done *)
      cleft.
      csplit.
      eexists; intuition.
    + ddestruction i.  
Qed.
Print Assumptions election3_liveness.
