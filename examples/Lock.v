From CTree Require Import
  CTree.Core
  Logic.Ctl
  Utils.Vectors
  CTree.Equ
  Events.Core
  CTree.SBisim
  CTree.Logic.AG
  CTree.Logic.AF
  CTree.Logic.AX
  CTree.Logic.State
  CTree.Logic.Iter
  CTree.Logic.Bind
  CTree.Events.Writer
  CTree.Events.State
  CTree.Interp.State.

From Coq Require Import
  Classes.SetoidClass.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad.

Import CTreeNotations CtlNotations.
Local Open Scope fin_vector_scope.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.

Section Lock.

  (* Assume a finite critical section *)
  Context {T: Type} {critical: ctree (stateE T) unit} {R: unit -> World (stateE T) -> Prop}
    {Hfin: <[ critical, Pure |= AF done R ]>} (init: T).   

  Notation "=?" := Fin.eq_dec.
  
  Record St := {
      state: T;
      flags: vec' 1 bool;
      turn: fin' 1
    }.

  (* Preemption *)
  Variant yieldE := Yield.
  
  Global Instance encode_yieldE : Encode yieldE :=
    fun 'Yield => unit.
  
  Notation lockE := (yieldE + stateE St).

  Definition get: ctree lockE St :=
    @Ctree.trigger (stateE St) (lockE) _ _ (ReSum_inr) (ReSumRet_inr) Get.

  Definition put: St -> ctree lockE unit :=
    fun x => @Ctree.trigger (stateE St) (lockE) _ _ (ReSum_inr) (ReSumRet_inr) (Put x).

  
  Definition set_flag(st: St)(i: fin' 1)(b: bool) : ctree lockE unit :=
    put {|
        state := st.(state);
        flags := (Vector.replace st.(flags) i b);
        turn := st.(turn);
      |}.

  Definition set_turn(st: St)(i: fin' 1)(b: bool) : ctree lockE unit :=
    put {|
        state := st.(state);
        flags := (Vector.replace st.(flags) i b);
        turn := st.(turn);
      |}.
  
  Definition yield: ctree lockE unit :=
    @Ctree.trigger yieldE (lockE) _ _ (ReSum_inl) (ReSumRet_inl) Yield.

  Definition while{E} `{Encode E}(c: ctree E bool) (body: ctree E unit): ctree E unit :=
    Ctree.iter
      (fun _ =>
         cond <- c;;
         if cond then
           body ;;
           Ret (inl tt)
         else
           Ret (inr tt)
      ) tt.

  Definition check(b: St -> bool): ctree lockE bool :=
    st <- get ;; Ret (b st).

  Check @resumCtree.
  Definition crit: ctree lockE unit :=
    
    @resumCtree (stateE St) lockE _ _ ReSum_inr ReSumRet_inr critical.
  Notation continue := (Ret (inl tt)).
  Notation stop := (Ret (inr tt)).
  
  Definition lock (id: fin' 1): ctree lockE unit :=
    st <- get ;;
    put (set_flag st id true) ;;
    put (set_turn st id) ;;
    yield ;;
    while (check (fun st => st.(turn) =? id && st.(flag) $ id))
      (yield) ;;
    
    (* Spin loop *)
    Ctree.iter
      (fun _ =>
         m <- acq ;;
         if PeanoNat.Nat.eq_dec m id then
           b <- enter ;;           
           if b then
             (* success *)
             stop
           else
             (* fail *)
             continue
         else
           continue) tt ;;
    (* critical section *)
    execute ;;
    leave.

  (* Spinlock instrumented semantics: (counter, lock state, shared state) *)
  Program Definition h_lockE: spinE ~> stateT (nat * bool * T) (ctreeW lockE) := 
    fun e =>
      mkStateT (fun (p: nat * bool * T) =>
                  let '(cnt, lk, st) := p in
                  match e return ctreeW lockE (encode e * (nat * bool * T)) with
                  | inl Acq =>
                      log Acq;;
                      Ret (cnt, (S cnt, lk, st))
                  | inl Enter =>
                      if lk then
                        Ret (false, (cnt, lk, st))
                      else
                        log Enter;;
                        Ret (true, (cnt, true, st))
                  | inl Leave =>
                      log Leave ;;
                      Ret (tt, (cnt, false, st))
                  | inr (Put s) =>
                      Ret (tt, (cnt, lk, s))
                  | inr Get =>
                      Ret (st, (cnt, lk, st))                          
                  end).

  Definition spinlock2: ctree spinE unit :=
    Ctree.br2
      (spinlock 0 ;; spinlock 1)
      (spinlock 1 ;; spinlock 0).
       
  Lemma spinlock_live: forall (id: nat),
      id = 0 \/ id = 1 
      <( {interp_state h_lockE spinlock2 (0, false, init)} |=
           AF visW {fun obs => obs.(id) = i} )>.
  Proof with eauto with ctl.
    intros.
    unfold election_proto, uring_sched. 
    unfold Ctree.branch.
    rewrite bind_br.
    cright.
    apply axl_br; split; [csplit; split; auto with ctl|].
    intro c. (* Nondeterministic pick *)
    rewrite bind_ret_l.
    unfold Ctree.forever.    
    eapply aul_iter_nat with (Ri:= fun _ _ => True)...
    clear c.
    intros (j, sys) w Hd [].
    destruct (Fin.eq_dec i j).
    - (* i = j *)
      subst.
      simp uring_sched_one'; cbn.
      desobs (proc (sys $ j)); setoid_rewrite Heqt.
      + (* Ret *)
        left.
        destruct x.
        unfold Ctree.map; rewrite bind_vis;
          setoid_rewrite bind_ret_l.
        apply aul_vis...
        right; split.
        * csplit...
        * intros [].
          cleft.
          csplit.
          reflexivity.
      + (* Br *)
        unfold Ctree.map; rewrite bind_br;
          setoid_rewrite bind_ret_l.
        right.
        apply aur_br; right.
        split.
        * csplit...
        * intros i_.
          cleft.
          apply anr_ret...
          eexists; intuition.
          
          exists (j, ). eexists.
        cbn.
        rewrite Heqt.
      with (f:=fun 'tt l _ => List.length l)
           (Ri:=fun 'tt l w => not_done w /\
                  match w with
                  | Obs (Log s') tt =>
                      match l with
                      | nil => nl = s'
                      | h :: ts => exists hs, h :: ts = hs ++ [nl]
                      end
                  | _ => exists hs, l = hs ++ [nl]
                  end)... 
    intros [] l w (Hd & Hw).
  Admitted.    
End Election.
