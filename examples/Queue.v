From CTree Require Import
  CTree.Core
  Events.Writer
  Logic.Ctl
  CTree.Equ
  CTree.SBisim
  CTree.Logic.Trans
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.Bind
  CTree.Logic.State
  CTree.Logic.CanStep
  CTree.Interp.State
  CTree.Events.State
  CTree.Events.Writer.

From ExtLib Require Export
  Structures.MonadState
  Data.Monads.StateMonad.

From Coq Require Import
  Lia
  List.

From ExtLib Require Import RelDec.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations ListNotations.
Local Open Scope ctree_scope.
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

Definition push {S}: S -> ctree (queueE S) unit :=
  fun (s: S) => @Ctree.trigger (queueE S) (queueE S) _ _ (ReSum_refl) (ReSumRet_refl) (Push s).

Definition pop {S}: ctree (queueE S) (option S) :=
  Ctree.trigger Pop.

Arguments push /.
Arguments pop /.

Section QueueEx.
  Context {T: Type} {HDec: RelDec (@eq T)} {HCor: RelDec_Correct HDec}.
  Infix "=?" := (rel_dec) (at level 75).

  (* Queue instrumented semantics *)
  Definition h_queueE: queueE T ~> stateT (list T) (ctreeW T) := 
    fun e =>
      mkStateT (fun q =>
                 match e return ctreeW T (encode e * list T) with
                 | Push v => Ret (tt, q ++ [v])
                 | Pop => match q with
                         | nil => Ret (None, nil)
                         | h :: ts =>
                             log h ;; (* Instrument the head of the queue [h] *)
                             Ret (Some h, ts)
                         end
                 end).

  Local Open Scope ctree_scope.
  (* Ex1: Drain a queue until there is nothing left *)
  Definition drain: ctree (queueE T) unit :=
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
        eapply aur_log_r...
        rewrite bind_ret_l, sb_guard.
        cleft.
        apply anr_ret...
      + cbn.
        rewrite interp_state_ret.
        cleft.        
        apply anr_ret...
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
  Definition rotate: ctree (queueE T) unit :=
    loop 
      (x <- pop ;;
       match x with
       | Some v =>
           push v;;
           continue
       | None => continue
       end).

  (* Element [t] does not appear in [l] *)
  Fixpoint not_inb(t: T)(l: list T): bool :=
    match l with
    | nil => true
    | h :: ts =>
        if h =? t then
          false
        else
          not_inb t ts
    end.

  (* Element [t] appears unique in [l] in some position *)
  Fixpoint unique(t: T) (l: list T): option nat :=
    match l with
    | nil => None
    | h :: ts => if h =? t then
                 if not_inb t ts then
                   Some 0
                 else
                   None
               else
                 option_map S (unique t ts)
    end.

  Fixpoint last_error(l: list T): option T :=
    match l with
    | nil => None
    | v :: nil => Some v
    | _ :: ts => last_error ts
    end.
  
  Lemma unfold_unique_hd: forall t h ts,
      unique t (h :: ts) =
        (if h =? t then
                 if not_inb t ts then
                   Some 0
                 else
                   None
               else
                 option_map S (unique t ts)).
  Proof.
    reflexivity.
  Qed.
  
  Lemma unique_head_eq': forall nl q,
      not_inb nl q = true ->
      unique nl (nl :: q) = Some 0.
  Proof with auto.
    intros; cbn.
    rewrite rel_dec_eq_true...
    now rewrite H.
  Qed.
  
  Lemma unique_head_eq: forall nl t q i,      
      unique nl (t :: q) = Some i ->
      (t =? nl) = true ->
      not_inb nl q = true.
  Proof.
    intros.
    cbn in H.
    rewrite H0 in H.
    destruct (not_inb nl q); inv H.
    reflexivity.
  Qed.

  Lemma unique_head_neq': forall nl t q i,
      (t =? nl) = false ->
      unique nl q = Some i ->
      unique nl (t :: q) = Some (S i).
  Proof.
    intros.
    cbn.
    rewrite H, H0.
    reflexivity.
  Qed.
  
  Lemma unique_head_neq: forall nl t q i,
      unique nl (t :: q) = Some i ->
      (t =? nl) = false ->      
      unique nl q = Some (i - 1).
  Proof.
    induction q; cbn; intros;
      rewrite H0 in *.
    inv H.
    destruct (a =? nl) eqn:Ha.
    - apply rel_dec_correct in Ha; subst.
      destruct (not_inb nl q); inv H.
      reflexivity. 
    - destruct (unique nl q) eqn:Hnl; cbn in *; inv H.
      rewrite H0 in IHq.
      reflexivity.
  Qed.
  
  Lemma unique_last_eq: forall q nl,
      not_inb nl q = true ->
      unique nl (q ++ [nl]) = Some (List.length q).
  Proof with auto.
    induction q; cbn; intros.
    - rewrite rel_dec_eq_true...
    - destruct (a =? nl); inv H.
      rewrite IHq...
  Qed.

  Lemma not_inb_last_false: forall q nl,
      not_inb nl (q ++ [nl]) = false.
  Proof with auto.
    induction q; cbn; intros.
    - rewrite rel_dec_eq_true...
    - destruct (a =? nl)...
  Qed.
  
  Lemma unique_last_none: forall q nl i,
      unique nl q = Some i ->
      unique nl (q ++ [nl]) = None.
  Proof with auto.
    induction q; cbn; intros.
    - inv H.
    - destruct (a =? nl) eqn:Hnl, (not_inb nl q) eqn:Hin; inv H.
      + rewrite not_inb_last_false...
      + destruct (unique nl q) eqn:Hnl'; inv H1.
        erewrite IHq with (i:=n)...
      + destruct (unique nl q) eqn:Hnl'; inv H1.
        erewrite IHq with (i:=n)...
  Qed.
  
  Lemma not_inb_unique_none: forall q nl,
      not_inb nl q = true ->
      unique nl q = None.
  Proof with auto.
    induction q; intros; cbn...
    cbn in H.
    destruct (a =? nl); inv H.
    rewrite IHq...
  Qed.

  Lemma not_inb_app_true: forall nl q q',
      not_inb nl q = true ->
      not_inb nl q' = true ->
      not_inb nl (q ++ q') = true.
  Proof with auto.
    induction q; intros; cbn in *...
    destruct (a =? nl); inv H.
    rewrite H2...
  Qed.

  Lemma not_inb_app_false_l: forall nl q q',
      not_inb nl q = false ->
      not_inb nl (q ++ q') = false.
  Proof with auto.
    induction q; intros; cbn in *...
    inv H.
    destruct (a =? nl); inv H...
    rewrite IHq...
  Qed.

  Lemma not_inb_app_false_r: forall nl q q',
      not_inb nl q' = false ->
      not_inb nl (q ++ q') = false.
  Proof with auto.
    induction q; intros; cbn in *...
    inv H.
    destruct (a =? nl)... 
    rewrite IHq...
  Qed.
  
  Lemma unique_app_l: forall q q' nl n,
      unique nl q = Some n ->
      not_inb nl q' = true ->
      unique nl (q ++ q') = Some n.
  Proof with auto.
    induction q; intros; cbn...
    - inv H.
    - cbn in H.
      destruct (a =? nl).
      destruct (not_inb nl q) eqn:Hin; inv H.
      rewrite not_inb_app_true...
      destruct (unique nl q) eqn:Hq.
      + rewrite IHq with (n:=n0)...
      + inv H.
  Qed.

  Lemma unique_last_neq: forall q t nl n,
      (t =? nl) = false ->
      unique nl q = Some n ->
      unique nl (q ++ [t]) = Some n.
  Proof with auto.
    induction q; cbn; intros.
    - inv H0.
    - destruct (a =? nl) eqn:Ha...
      + destruct (not_inb nl q) eqn:Hnl; inv H0.
        rewrite rel_dec_correct in Ha; subst.
        rewrite not_inb_app_true...
        cbn.
        now rewrite H.
      + destruct (unique nl q) eqn:Hnl; inv H0.
        rewrite IHq with (n:=n0)...
  Qed.
  Arguments unique: simpl never.

  Lemma nat_eqb_S: forall n,
      Nat.eqb n (S n) = false.
  Proof. induction n; auto. Qed.
  
  Typeclasses Transparent equ.
  Typeclasses Transparent sbisim.
  Theorem rotate_agaf_pop: forall q nl i,
      unique nl q = Some i ->
      List.length q > 1 ->
      <( {interp_state h_queueE rotate q}, Pure |= AG AF visW {fun h => h = nl} )>.
  Proof with eauto with ctl.
    intros.
    unfold rotate, forever. 
    apply ag_state_iter with
      (R:= fun _ q _ => List.length q > 1 /\ exists i, unique nl q = Some i). 
    - constructor.
    - split... 
    - clear H H0 q i.
      intros [] q w Hd (Hlen & i & Hi).
      split.
      + (* Eventually *)
        eapply aul_state_iter_nat with
          (Ri:= fun _ q _ => List.length q > 1 /\ exists i, unique nl q = Some i)
          (f:= fun 'tt q (w: WorldW T) =>
                 match unique nl q with
                 | Some n => length q - n
                 | None => length q
                 end)...
        * clear Hlen Hi q w Hd i.
          intros [] q w Hd (Hlen & i & Hi).
          rewrite interp_state_bind. 
          setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
          rewrite bind_bind.
          setoid_rewrite sb_guard.
          setoid_rewrite bind_ret_l.
          destruct q.
          -- (* q' = nl :: ts *)
            left.
            inv Hi.
          -- (* q' = h :: ts, index ts nl n *)
            right.
            rewrite bind_bind.
            eapply aur_bind_r_eq.
            ++ eapply aur_vis...
               right; split.
               ** csplit...
               ** intros [].
                  cleft.
                  apply anr_ret...
            ++ rewrite bind_ret_l.
               rewrite interp_state_bind.
               setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ (Push t) _);
                 simpl runStateT.
               rewrite bind_bind, bind_ret_l, sb_guard, bind_ret_l,
                 interp_state_ret.
               cleft.
               apply anr_ret...
               exists tt; intuition.
               ** rewrite app_length.
                  cbn in *.
                  lia.
               ** cbn in Hi; destruct (t =? nl) eqn:Hnl;
                    destruct (not_inb nl q) eqn:Hinb; inv Hi...
                  --- (* t = nl, nl not in q *)
                    apply rel_dec_correct in Hnl; subst.
                    exists (List.length q).
                    now apply unique_last_eq.
                  --- (* t = nl, nl in q *)
                    apply rel_dec_correct in Hnl; subst.
                    unfold unique in H0; cbn in H0.
                    rewrite rel_dec_eq_true in H0...
                    rewrite Hinb in H0; inv H0.
                  --- (* t <> nl, nl not in q *)
                    apply not_inb_unique_none in Hinb.
                    apply unique_head_neq in H0...
                    rewrite Hinb in H0; inv H0.
                  --- (* t <> nl, nl in q *)
                    apply unique_head_neq in H0...
                    exists (i - 1).
                    apply unique_app_l; auto.
                    cbn; now rewrite Hnl.
               ** cbn in *.
                  rename q into q'.
                  destruct (t =? nl) eqn:Hnl.
                  --- (* t = nl *)
                    apply unique_head_eq in Hi...
                    rewrite rel_dec_correct in Hnl; subst.
                    rewrite unique_last_eq...
                    rewrite unfold_unique_hd.
                    rewrite rel_dec_eq_true, Hi...
                    rewrite app_length; cbn.
                    lia.
                  --- (* t <> nl *)
                    rewrite unfold_unique_hd, Hnl in Hi.
                    destruct (unique nl q') eqn:Hnl'; inv Hi.
                    rewrite unfold_unique_hd, Hnl, Hnl'.
                    rewrite app_length; cbn.
                    rewrite PeanoNat.Nat.add_comm.
                    cbn.
                    rewrite unique_app_l with (n:=n); auto.
                    +++ admit.
                    +++ cbn; now rewrite Hnl.
      + (* Loop invariant *)
        rewrite interp_state_bind,
          (@interp_state_trigger _ _ _ _ _ _ Pop _), bind_bind; cbn...
        setoid_rewrite sb_guard.
        setoid_rewrite bind_ret_l.
        destruct q; cbn in Hlen; try lia.
        rewrite unfold_unique_hd in Hi.
        destruct (t =? nl) eqn:Ht.
        destruct (not_inb nl q) eqn:Hinb; inv Hi.
        * (* q = nl :: ts *)
          rewrite bind_bind.
          unfold log, trigger.
          rewrite bind_vis.
          apply axr_vis...
          split.
          -- csplit...
          -- intros [].
             rewrite ?bind_ret_l.
             rewrite interp_state_bind, interp_state_vis, bind_bind.
             cbn.
             rewrite bind_ret_l, sb_guard, interp_state_ret, bind_ret_l,
               interp_state_ret.
             cleft.
             apply anr_ret...
             exists tt; intuition.
             ++ rewrite app_length; cbn; lia.
             ++ exists (List.length q).
                rewrite rel_dec_correct in Ht; subst.
                now apply unique_last_eq.
        * (* q = h :: ts *)          
          rewrite bind_bind.
          unfold log, trigger.
          rewrite bind_vis.
          apply axr_vis...
          split.
          -- csplit...
          -- intros [].
             rewrite ?bind_ret_l.
             rewrite interp_state_bind, interp_state_vis, bind_bind.
             cbn.
             rewrite bind_ret_l, sb_guard, interp_state_ret, bind_ret_l,
               interp_state_ret.
             cleft.
             apply anr_ret...
             exists tt; intuition.
             ++ rewrite app_length; cbn; lia.
             ++ destruct (unique nl q) eqn:Hnl; inv Hi.
                exists n.
                now apply unique_last_neq...
  Admitted.
End QueueEx.
  
