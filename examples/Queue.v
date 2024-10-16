From ICTL Require Import
  ICTree.Core
  Events.Writer
  Logic.Ctl
  ICTree.Equ
  ICTree.SBisim
  ICTree.Logic.Trans
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.Bind
  ICTree.Logic.State
  ICTree.Logic.CanStep
  ICTree.Interp.State
  ICTree.Events.State
  ICTree.Events.Writer.

From ExtLib Require Export
  Structures.MonadState
  Data.Monads.StateMonad.

From Coq Require Import
  Lia
  List.

From ExtLib Require Import RelDec.

Generalizable All Variables.

Import ICtree ICTreeNotations CtlNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ctl_scope.
Local Open Scope list_scope.

Variant queueE (S: Type): Type :=
  | Push (s: S)
  | Pop.

Arguments Push {S} s.
Arguments Pop {S}.

Global Instance encode_queueE{S}: Encode (queueE S) :=
    fun e => match e with
          | Push s => unit
          | Pop => option S
          end.

Definition push {S}: S -> ictree (queueE S) unit :=
  fun (s: S) => @ICtree.trigger (queueE S) (queueE S) _ _ (ReSum_refl) (ReSumRet_refl) (Push s).

Definition pop {S}: ictree (queueE S) (option S) :=
  ICtree.trigger Pop.

Arguments push /.
Arguments pop /.

Section QueueEx.
  Context {T: Type} {HDec: RelDec (@eq T)} {HCor: RelDec_Correct HDec}.
  Infix "=?" := (rel_dec) (at level 75).

  (* Queue instrumented semantics *)
  Definition h_queueE: queueE T ~> stateT (list T) (ictreeW T) := 
    fun e =>
      mkStateT (fun q =>
                 match e return ictreeW T (encode e * list T) with
                 | Push v => Ret (tt, q ++ [v])
                 | Pop => match q with
                         | nil => Ret (None, nil)
                         | h :: ts =>
                             log h ;; (* Instrument the head of the queue [h] *)
                             Ret (Some h, ts)
                         end
                 end).

  Local Open Scope ictree_scope.
  (* Ex1: Drain a queue until there is nothing left *)
  Definition drain: ictree (queueE T) unit :=
    loop
      (x <- pop ;;
       continue).

  Lemma list_app_nil: forall (s: T) hs,
      ~ [] = hs ++ [s].  
  Proof. destruct hs; intros * H; inv H; auto. Qed.

  Lemma list_app_cons: forall (h s: T) ts hs,
      h :: ts = hs ++ [s] ->
      match hs with
      | nil => h = s /\ ts = nil
      | h' :: ts' => h = h' /\ ts = ts' ++ [s]
      end.  
  Proof. destruct hs; intros; cbn in *; inv H; auto. Qed.
    
  (*| Eventually we get [nl] (needle) to show up
    in the instrumentation. |*)
  Example drain_af_pop: forall (nl: T) (q: list T),
      <( {interp_state h_queueE drain (q ++ [nl])}, Pure |=
         AF visW {fun w => w = nl })>.
  Proof with eauto with ctl.    
    intros.
    apply aul_state_iter_nat
      with (f:=fun 'tt l _ => List.length l)
           (Ri:=fun 'tt l w => 
                  match w with
                  | Obs (Log s') tt =>
                      match l with
                      | nil => nl = s'
                      | h :: ts => exists hs, h :: ts = hs ++ [nl]
                      end
                  | _ => exists hs, l = hs ++ [nl]
                  end)... 
    intros [] l w Hd Hw.
    destruct l as [|h ts] eqn:Hl; subst.
    - (* l = [] *)
      inv Hd.
      + (* w = Pure *)
        destruct Hw.
        now apply list_app_nil in H.
      + (* w = Obs e v *)
        destruct e, v. subst.
        left.
        cleft.
        now csplit.         
    - (* l = h :: ts *)
      right.
      eapply aur_state_bind_r_eq.
      + rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
        rewrite bind_bind.
        eapply afr_log...
        rewrite bind_ret_l, sb_guard.
        cleft.
        apply axr_ret...
      + cbn.
        rewrite interp_state_ret.
        cleft.        
        apply axr_ret...
        exists tt; intuition.
        cbn.
        * inv Hd.
          -- destruct Hw.
             apply list_app_cons in H.
             destruct x; intuition; subst...
             destruct x; intuition; cbn.
             ++ now (exists []).
             ++ now (exists (t0 ::x)).
          -- destruct e, v, Hw.
             apply list_app_cons in H.
             destruct x; intuition; subst...
             destruct x; intuition; cbn.
             ++ now (exists []).
             ++ now (exists (t1 ::x)).
  Qed.
  Print Assumptions drain_af_pop.
  
  (* Ex2: Rotate a queue (pop an element from head, add it to tail) *)
  Definition rotate: ictree (queueE T) unit :=
    loop 
      (x <- pop ;;
       match x with
       | Some v =>
           push v;;
           continue
       | None => continue
       end).

  (* Element [t] appears unique in [l] in some position *)
  Fixpoint find(t: T) (l: list T): option nat :=
    match l with
    | nil => None
    | h :: ts => if h =? t then
                 Some 0
               else
                 option_map S (find t ts)
    end.

  Lemma unfold_find_hd: forall t h ts,
      find t (h :: ts) =
        (if h =? t then
           Some 0
         else
           option_map S (find t ts)).
  Proof. reflexivity. Qed.

  Lemma find_last_ex: forall nl ts,
    exists i0 : nat, find nl (ts ++ [nl]) = Some i0.
  Proof with eauto with ctl.
    induction ts.
    - exists 0; cbn.
      rewrite rel_dec_eq_true...
    - destruct IHts.
      destruct (a =? nl) eqn:Hnl.
      + rewrite rel_dec_correct in Hnl; subst.
        exists 0; cbn.
        rewrite rel_dec_eq_true...
      + exists (S x); cbn.
        rewrite Hnl, H.
        reflexivity.
  Qed.

  Lemma find_app_l: forall nl ts n l,
    find nl ts = Some n ->
    find nl (ts ++ l) = Some n.
  Proof with eauto.
    induction ts; intros.
    - inv H.
    - cbn.
      rewrite unfold_find_hd in H.
      destruct (a =? nl) eqn:Hnl...
      destruct (find nl ts); inv H.
      rewrite IHts with (n:=n0)...
  Qed.
  
  Lemma nat_eqb_S: forall n,
      Nat.eqb n (S n) = false.
  Proof. induction n; auto. Qed.

  Variable (nl: T).
  Typeclasses Transparent equ.
  Typeclasses Transparent sbisim.
  
  Theorem rotate_agaf_pop: forall q i,
      find nl q = Some i ->
      <( {interp_state h_queueE rotate q}, Pure |=
                       AG AF visW {fun h => h = nl} )>.
  Proof with eauto with ctl.
    intros.
    unfold rotate, forever, Classes.iter, MonadIter_ictree.
    apply ag_state_iter with
      (R:= fun 'tt q w => exists h ts, q = h :: ts /\ (h = nl \/ (h <> nl /\ exists i, find nl ts = Some i)))...
    - destruct q; try solve [ inv H ].
      exists t, q; intuition.
      rewrite unfold_find_hd in H.
      destruct (t =? nl) eqn:Hnl; inv H.
      + apply rel_dec_correct in Hnl.
        left...
      + right.
        destruct (find nl q) eqn:Hq, i; inv H1.
        apply neg_rel_dec_correct in Hnl; split...
    - clear H q.
      unfold Classes.iter, MonadIter_ictree.
      intros [] q w Hd (h & ts & -> & [-> | (Hnl & Hi)]).
      + (* t = nl *)
        split.
        * (* iter |= AF *)
          rewrite interp_state_unfold_iter.
          apply ctll_bind_l.
          rewrite interp_state_bind.
          setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
          rewrite ?bind_bind.
          apply afl_log...
          cleft.
          csplit...
        * (* body variant/invariant *)
          rewrite interp_state_bind.
          setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
          rewrite ?bind_bind.
          apply axr_log...
          rewrite bind_ret_l, sb_guard, bind_ret_l, interp_state_bind.          
          setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Push nl) _); cbn.
          rewrite ?bind_bind.
          rewrite bind_ret_l, sb_guard, bind_ret_l.
          cleft.
          rewrite interp_state_ret.
          apply axr_ret...
          exists tt; split2...
          destruct ts.
          -- exists nl, []...
          -- exists t, (ts ++ [nl]); split...
             destruct (t =? nl) eqn:Hnl.
             ++ left.
                now apply rel_dec_correct.
             ++ right.
                apply neg_rel_dec_correct in Hnl; split...
                apply find_last_ex.
      + (* t <> nl *)
        split.
        * clear i.
          destruct Hi as (i & Hi).
          eapply aul_state_iter_nat with
            (Ri:=fun 'tt q _ =>
                   exists h ts, q = h :: ts /\ (h = nl \/ (h <> nl /\ exists i, find nl ts = Some i)))
            (f:=fun 'tt q _ =>
                  match find nl q with
                  | None => length q
                  | Some v => v
                  end)...
          -- exists h, ts; split...
          -- intros [] q w' Hw' (h' & ts' & -> & [-> | (Hnl' & ?)]).
             ++ left.
                rewrite interp_state_bind.
                setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
                rewrite ?bind_bind.
                apply afl_log...
                rewrite bind_ret_l, sb_guard, bind_ret_l, interp_state_bind.
                setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Push nl) _); cbn.
                rewrite ?bind_bind, bind_ret_l, sb_guard, bind_ret_l, interp_state_ret.
                cleft.
                csplit...
             ++ right.
                rewrite interp_state_bind.
                setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
                rewrite ?bind_bind.
                apply afr_log...
                rewrite bind_ret_l, sb_guard, bind_ret_l, interp_state_bind.
                setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Push h') _); cbn.
                rewrite ?bind_bind, bind_ret_l, sb_guard, bind_ret_l, interp_state_ret.
                apply aur_ret.
                cleft.
                apply axr_ret...
                exists tt; intuition.
                ** destruct ts'; cbn.
                   --- exists h', []...
                   --- exists t, (ts' ++ [h']); split... 
                       destruct H as (j & H1).
                       rewrite unfold_find_hd in H1.
                       destruct (t =? nl) eqn:Hnl''; inv H1.
                       +++ apply rel_dec_correct in Hnl''.
                           now left.
                       +++ right; split.
                           now apply neg_rel_dec_correct in Hnl''.
                           destruct (find nl ts') eqn:Hts'; inv H0.
                           exists n.
                           now apply find_app_l.
                ** (* variant *)
                  cbn.
                  eapply rel_dec_neq_false in Hnl'...
                  destruct H.
                  rewrite Hnl', H.
                  cbn.
                  erewrite find_app_l...
        * rewrite interp_state_bind.
          setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
          rewrite ?bind_bind.
          apply axr_log...
          rewrite bind_ret_l, sb_guard, bind_ret_l, interp_state_bind.
          setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Push h) _); cbn.
          rewrite ?bind_bind, bind_ret_l, sb_guard, bind_ret_l, interp_state_ret.
          apply aur_ret; cleft.
          apply axr_ret...
          exists tt; intuition...
          destruct Hi.
          destruct ts; try solve [inv H].
          exists t, (ts ++ [h]); intuition.
          destruct (t =? nl) eqn:Hnl'; inv H.
          -- apply rel_dec_correct in Hnl'.
             now left.
          -- right.                
             rewrite Hnl' in H1.
             destruct (find nl ts) eqn:Hts; inv H1.
             split.
             ++ now apply neg_rel_dec_correct.
             ++ exists n.
                now apply find_app_l.
  Qed.
End QueueEx.
  
