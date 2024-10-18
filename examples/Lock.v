From TICL Require Import
  ICTree.Core
  Logic.Core
  Utils.Vectors
  ICTree.Equ
  Events.Core
  ICTree.SBisim
  ICTree.Logic.AG
  ICTree.Logic.AF
  ICTree.Logic.AX
  ICTree.Logic.State
  ICTree.Logic.Iter
  ICTree.Logic.Bind
  ICTree.Events.Writer
  ICTree.Events.State
  ICTree.Interp.State.

From Coq Require Import
  Classes.SetoidClass.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad.

Import ICTreeNotations TiclNotations.
Local Open Scope fin_vector_scope.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.

Section Lock.

  (* Assume a finite critical section *)
  Context {T: Type} {critical: ictree (stateE T) unit} {R: unit -> World (stateE T) -> Prop}
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

  Definition get: ictree lockE St :=
    @ICtree.trigger (stateE St) (lockE) _ _ (ReSum_inr) (ReSumRet_inr) Get.

  Definition put: St -> ictree lockE unit :=
    fun x => @ICtree.trigger (stateE St) (lockE) _ _ (ReSum_inr) (ReSumRet_inr) (Put x).


  Definition set_flag(st: St)(i: fin' 1)(b: bool) : ictree lockE unit :=
    put {|
        state := st.(state);
        flags := (Vector.replace st.(flags) i b);
        turn := st.(turn);
      |}.

  Definition set_turn(st: St)(i: fin' 1)(b: bool) : ictree lockE unit :=
    put {|
        state := st.(state);
        flags := (Vector.replace st.(flags) i b);
        turn := st.(turn);
      |}.

  Definition yield: ictree lockE unit :=
    @ICtree.trigger yieldE (lockE) _ _ (ReSum_inl) (ReSumRet_inl) Yield.

  Definition while{E} `{Encode E}(c: ictree E bool) (body: ictree E unit): ictree E unit :=
    ICtree.iter
      (fun _ =>
         cond <- c;;
         if cond then
           body ;;
           Ret (inl tt)
         else
           Ret (inr tt)
      ) tt.

  Definition check(b: St -> bool): ictree lockE bool :=
    st <- get ;; Ret (b st).

  Check @resumICtree.
  Definition crit: ictree lockE unit :=

    @resumICtree (stateE St) lockE _ _ ReSum_inr ReSumRet_inr critical.
  Notation continue := (Ret (inl tt)).
  Notation stop := (Ret (inr tt)).

  Definition lock (id: fin' 1): ictree lockE unit :=
    st <- get ;;
    put (set_flag st id true) ;;
    put (set_turn st id) ;;
    yield ;;
    while (check (fun st => st.(turn) =? id && st.(flag) $ id))
      (yield) ;;

    (* Spin loop *)
    ICtree.iter
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
  Program Definition h_lockE: spinE ~> stateT (nat * bool * T) (ictreeW lockE) :=
    fun e =>
      mkStateT (fun (p: nat * bool * T) =>
                  let '(cnt, lk, st) := p in
                  match e return ictreeW lockE (encode e * (nat * bool * T)) with
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

  Definition spinlock2: ictree spinE unit :=
    ICtree.br2
      (spinlock 0 ;; spinlock 1)
      (spinlock 1 ;; spinlock 0).

  Lemma spinlock_live: forall (id: nat),
      id = 0 \/ id = 1
      <( {interp_state h_lockE spinlock2 (0, false, init)} |=
           AF visW {fun obs => obs.(id) = i} )>.
  Proof with eauto with ticl.
    intros.
    unfold election_proto, uring_sched.
    unfold ICtree.branch.
    rewrite bind_br.
    cright.
    apply axl_br; split; [csplit; split; auto with ticl|].
    intro c. (* Nondeterministic pick *)
    rewrite bind_ret_l.
    unfold ICtree.forever.
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
        unfold ICtree.map; rewrite bind_vis;
          setoid_rewrite bind_ret_l.
        apply aul_vis...
        right; split.
        * csplit...
        * intros [].
          cleft.
          csplit.
          reflexivity.
      + (* Br *)
        unfold ICtree.map; rewrite bind_br;
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
