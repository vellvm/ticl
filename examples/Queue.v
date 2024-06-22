From CTree Require Import
  CTree.Core
  Events.Writer
  Logic.Ctl
  CTree.Equ
  CTree.SBisim
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
          cleft.
          apply anr_ret...
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
             cleft.
             apply anr_ret...
          -- rewrite bind_ret_l, sb_guard.
             cleft.
             apply anr_ret...
        * (* w = Obs e v *)
          rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
          rewrite bind_bind.
          eapply aur_bind_r_eq.
          -- unfold log, trigger.
             apply aur_vis...
             right; split; try csplit...
             intros [].
             cleft.
             apply anr_ret...
          -- rewrite bind_ret_l, sb_guard.
             cleft.
             apply anr_ret...
      + cbn.
        rewrite interp_state_ret.
        cleft.        
        apply anr_ret; [constructor |split;[split; cbn|]]...
        inv Hd.
        * destruct Hw.
          apply list_app_cons in H.
          destruct x; intuition; subst...
          destruct x; intuition; cbn.
          ++ now (exists []).
          ++ now (exists (s0 ::x)).
        * destruct e, v, Hw.
          apply list_app_cons in H.
          destruct x; intuition; subst...
          destruct x; intuition; cbn.
          ++ now (exists []).
          ++ now (exists (s1 ::x)).
  Qed.

  Definition while{E} `{HE: Encode E}(k: ctree E (unit + unit)): ctree E unit :=
    Ctree.iter (fun _ => k tt) tt.
  
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
  | IndexFound: forall h h' ts,
      h = h' ->
      index (h :: ts) h' 0
  | IndexSucc: forall h ts x n,
    index ts x n ->
    index (h :: ts) x (1+ n)%nat.
  Hint Constructors index: core.

  Lemma index_last_eq: forall q (nl: S),
      index (q ++ [nl]) nl (length q).
  Proof with auto.
    induction q; intros; cbn; auto.
  Qed.

  Typeclasses Transparent equ.
  Typeclasses Transparent sbisim.

  Lemma sb_iter_iter: forall (k: I -> ctree E (I + R)) (x: I),
      Ctree.iter (fun x => Ctree.map inl (Ctree.iter k x)) x ~
        Ctree.iter (fun x =>
    
  Theorem rotate_agaf_pop: forall q nl,
      <( {interp_state h_queueE rotate (q ++ [nl])}, Pure |=
           AG AF visW {fun h => h = nl} )>.
  Proof with eauto with ctl.
    intros.
    eapply ag_state_iter with (R:=fun _ q _ => exists i, index q nl i).
    - exists (List.length q).
      apply index_last_eq.
    - constructor.
    - clear q.
      intros [] q w (i & Hi) Hd.
      rewrite interp_state_bind.
      setoid_rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
      rewrite bind_bind.
      setoid_rewrite sb_guard.
      setoid_rewrite bind_ret_l.
      destruct q.
      + inv Hi.
      + rewrite bind_bind.
        setoid_rewrite bind_ret_l.
        unfold log, trigger.
        (* Without this it's impossible to prove *)
        rewrite bind_vis.
        eapply axr_vis...
        split.
        * eapply afl_vis...
          right.
          split...
          intros [].
          rewrite bind_ret_l.
          rewrite interp_state_bind, interp_state_vis, bind_bind.
          cbn.
          rewrite bind_ret_l, sb_guard, interp_state_ret, bind_ret_l,
            interp_state_ret.          
          dependent induction Hi. 
          -- cleft.
             csplit...
          -- admit.
        * intros [].
          rewrite bind_ret_l, interp_state_bind, interp_state_vis.
          cbn.
          rewrite bind_bind, bind_ret_l, sb_guard, interp_state_ret,
            bind_ret_l, interp_state_ret.
          cleft.
          apply anr_ret...
          exists tt; split2...
          exists (List.length q).
          admit.
  Admitted.
End QueueEx.
  
