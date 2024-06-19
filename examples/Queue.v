From CTree Require Import
  CTree.Core
  Events.Writer
  Logic.Ctl
  CTree.Equ
  CTree.SBisim  
  CTree.Logic.AF
  CTree.Logic.AX
  CTree.Logic.State
  CTree.Logic.Bind
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
  Context {S: Type} {HDec: RelDec (@eq S)} {HCor: RelDec_Correct HDec}.
  Infix "=?" := (rel_dec) (at level 75).

  (* Queue instrumented semantics *)
  Definition h_queueE: queueE S ~> stateT (list S) (ctreeW S) := 
    fun e =>
      mkStateT (fun q =>
                 match e return ctreeW S (encode e * list S) with
                 | Push v => Ret (tt, q ++ [v])
                 | Pop => match q with
                         | nil => Ret (None, nil)
                         | h :: ts =>
                             log h ;; (* Instrument the head of the queue [h] *)
                             Ret (Some h, ts)
                         end
                 end).
  
  (* Ex1: Drain a queue until there is nothing left, you should get a needle in the end eventually. *)
  Definition drain: ctree (queueE S) unit :=
    iter (fun _ =>
            x <- pop ;;
            match x with
            | Some v => Ret (inl tt) (* keep popping *)
            | None => Ret (inr tt)   (* done *)
            end) tt.        

  Lemma list_app_nil: forall (s: S) hs,
      ~ [] = hs ++ [s].  
  Proof. destruct hs; intros * H; inv H; auto. Qed.

  Lemma list_app_cons: forall (h s: S) ts hs,
      h :: ts = hs ++ [s] ->
      match hs with
      | nil => h = s /\ ts = nil
      | h' :: ts' => h = h' /\ ts = ts' ++ [s]
      end.  
  Proof. destruct hs; intros; cbn in *; inv H; auto. Qed.
    
  (*| Eventually we get [nl] (needle) to show up
    in the instrumentation. |*)
  Example drain_af_pop: forall (nl: S) (q: list S),
      <[ {interp_state h_queueE drain (q ++ [nl])}, Pure |=
         AF finishW {fun 'tt l w => w = nl /\ l = @nil S }]>.
  Proof with eauto with ctl.    
    intros.
    apply aur_state_iter_nat
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
    destruct l as [|h ts] eqn:Hl; subst.
    - (* l = [] *)
      inv Hd.
      + (* w = Pure *)
        destruct Hw.
        now apply list_app_nil in H.
      + (* w = Obs e v *)
        destruct e, v.
        subst.
        eapply aur_state_bind_r_eq.
        * rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
          rewrite bind_ret_l, sb_guard.        
          cleft; apply ax_done; split...
          csplit...
        * cbn.
          rewrite interp_state_ret.
          cleft; apply ax_done; split; try csplit...
          eexists; intuition.
          cright.
          apply ax_done; split; try csplit...
          eexists; intuition...
          econstructor.
          eexists; intuition...          
    - (* l = h :: ts *)
      eapply aur_state_bind_r_eq.
      + inv Hd.
        * (* w = Pure *)
          rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
          rewrite bind_bind.
          eapply aur_bind_r_eq.
          -- unfold log, trigger.
             apply aur_vis...
             right; split; try csplit...
             intros [].
             cleft; apply ax_done; intuition...
             csplit...
          -- rewrite bind_ret_l, sb_guard.
             cleft; apply ax_done; split; try csplit...
        * (* w = Obs e v *)
          rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
          rewrite bind_bind.
          eapply aur_bind_r_eq.
          -- unfold log, trigger.
             apply aur_vis...
             right; split; try csplit...
             intros [].
             cleft; apply ax_done; intuition...
             csplit...
          -- rewrite bind_ret_l, sb_guard.
             cleft; apply ax_done; split; try csplit...
      + cbn.
        rewrite interp_state_ret.
        cleft; apply ax_done; split; try csplit...
        eexists; intuition...
        split.
        * split...
          cbn.
          inv Hd.
          -- destruct Hw.
             apply list_app_cons in H.
             destruct x; intuition; subst...
             destruct x; intuition; cbn.
             ++ now (exists []).
             ++ now (exists (s0 ::x)).
          -- destruct e, v, Hw.
             apply list_app_cons in H.
             destruct x; intuition; subst...
             destruct x; intuition; cbn.
             ++ now (exists []).
             ++ now (exists (s1 ::x)).
        * apply PeanoNat.Nat.lt_succ_diag_r.
  Qed.

  (* Ex2: Rotate a queue (pop an element from head, add it to tail) *)
  Definition rotate: ctree (queueE S) unit :=
    iter (fun _ =>
            x <- pop ;;
            match x with
            | Some v =>
                push v;;
                Ret (inl tt)
            | None =>
                (* If queue is empty to begin with, return [tt] *)
                Ret (inr tt)
            end) tt.
  
  Inductive index: list S -> S -> nat -> Prop :=
  | IndexFound: forall h ts,
    index (h :: ts) h 0
  | IndexSucc: forall h ts x n,
    index ts x n ->
    index (h :: ts) x (1+ n)%nat.
  Hint Constructors index: core.

  Lemma index_last_eq: forall q (nl: S),
      index (q ++ [nl]) nl (length q).
  Proof with auto.
    induction q; intros; cbn; auto.
  Qed.
  
  Theorem rotate_agaf_pop: forall q nl,
      <( {interp_state h_queueE rotate (q ++ [nl])}, Pure |=
           AG AF visW {fun h => h = nl} )>.
  Proof with eauto with ctl.
    intros.
    eapply ag_state_iter with (R:=fun _ q _ => exists i, index q nl i).
    exists (List.length q).
    apply index_last_eq.
    clear q.
    intros [] q w (i & Hi).
    
    rewrite interp_state_bind.
    unfold pop, push, trigger.
    rewrite interp_state_vis, bind_bind.
    unfold runStateT, h_queueE; cbn.
    rewrite bind_bind.
    resum.
    rewrite ?bind_ret_l, bind_guard.
    apply af_guard.
    rewrite interp_state_ret, bind_ret_l.
    rewrite interp_state_bind, interp_state_vis.
    rewrite bind_bind.
    unfold runStateT; cbn.
    rewrite bind_bind.
    resum.
    rewrite bind_ret_l.
    destruct l as [|h ts]; cbn.
    - (* l = [] *)
      rewrite bind_ret_l, bind_guard.
      apply af_guard.
      rewrite interp_state_ret, bind_ret_l.
      cbn.
      rewrite interp_state_ret.
      next; left.
      apply ax_done.
      intuition.
      inv Hw.
      + destruct H'; cbn in *.
        inv H0.
      + destruct v, e.
        cbn in *.
        destruct H'; inv H0.
    - (* l = h::ts *)
      cbn.
      rewrite index_last_S.
      inv Hw; cbn in H'.
      + destruct H'.
        destruct (h =? t) eqn:Hh.
        * inv H0; lia.
        * rewrite H0; cbn.
          rewrite bind_trigger, bind_vis.
          next; right.
          next; split.
          -- apply can_step_vis...
          -- intros t' w' TR.
             apply ktrans_vis in TR as ([] & -> & <- & _).
             rewrite bind_ret_l, bind_guard, af_guard,
               interp_state_ret, bind_ret_l. 
             cbn.
             rewrite interp_state_ret.
  Admitted.
End QueueEx.
  
