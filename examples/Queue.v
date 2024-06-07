From CTree Require Import
  CTree.Core
  Events.Writer
  Logic.Ctl
  CTree.Equ
  CTree.SBisim
  CTree.Logic.Trans
  Logic.Kripke
  CTree.Interp.Core
  CTree.Logic.AF
  CTree.Logic.AX
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
  
  (* Ex1: Drain a queue until there is nothing left, you should get a needle in the end eventually. *)
  Definition drain: ctree (queueE S) unit :=
    iter (fun _ =>
            x <- pop ;;
            match x with
            | Some v => Ret (inl tt) (* keep popping *)
            | None => Ret (inr tt)   (* done *)
            end) tt.

  (* Ex2: Rotate (pop an element, add an element [a]) a queue (a ≠ b) *)
  Definition rotate(a: S): ctree (queueE S) unit :=
    iter (fun _ =>
            push a ;;
            x <- pop ;;
            match x with
            | Some v => Ret (inl tt)
            | None => Ret (inr tt) (* should never return *)
            end) tt.            

  (* Queue instrumented semantics *)
  Definition h_queueE: queueE S ~> stateT (list S) (ctreeW S) := 
    fun e =>
      mkStateT (fun q =>
                 match e return ctreeW S (encode e * list S) with
                 | Push v => Ret (tt, q ++ [v])
                 | Pop => match q with
                         | nil => Ret (None, nil)
                         | h :: ts =>
                             log h ;;
                             Ret (Some h, ts)
                         end
                 end).

  Lemma list_app_cons: forall (h s: S) ts hs,
      h :: ts = hs ++ [s] ->
      match hs with
      | nil => h = s /\ ts = nil
      | h' :: ts' => h = h' /\ ts = ts' ++ [s]
      end.  
  Proof. destruct hs; intros; cbn in *; inv H; auto. Qed.
  
  (*| Eventually we get [nl] (needle) to show up in the instrumentation. |*)
  Typeclasses Transparent equ.
  Theorem drain_af_pop: forall (nl: S) (q: list S),
      <( {interp_state h_queueE drain (q ++ [nl])}, Pure |=
         AF finishW {fun 'tt l w => w = nl /\ l = @nil S })>.
  Proof with eauto with ctl.
    intros.
    apply au_state_iter_list
      with (Ri:=fun 'tt w l =>
                  match w with
                  | Obs (Log s') tt =>
                      match l with
                      | nil => nl = s'
                      | h :: ts => exists hs, h :: ts = hs ++ [nl]
                      end
                  | _ => exists hs, l = hs ++ [nl]
                  end)... 
    intros [] w l Hw Hd.    
    rewrite interp_state_bind.
    rewrite (@interp_state_trigger _ _ _ _ _ _ Pop _); cbn.
    rewrite bind_bind.
    destruct l as [|h ts] eqn:Hl; inv Hd. 
    - (* l = [], w = Pure *)
      destruct Hw, x; cbn in *; inv H.
    - (* l = [], w = Obs e v *)
      destruct e, v.
      subst.
      rewrite bind_ret_l, bind_guard, sb_guard, bind_ret_l, interp_state_ret.
      cright; apply ax_done; split...
      eexists; intuition...
      intuition...
      exists (Log s), tt...
    - (* l = h :: ts, w = Pure *)
      rewrite bind_bind.
      eapply au_bind_r_eq.
      + unfold log, trigger.
        apply au_vis_l...
        intros [].
        cright; apply ax_done...
      + rewrite bind_ret_l, bind_guard, sb_guard, bind_ret_l, interp_state_ret.
        cright; apply ax_done; split...
        eexists; intuition...
        cbn; intuition...
        destruct Hw as (hs & H).
        destruct ts...
        * apply list_app_cons in H; destruct hs; intuition.
          exfalso.
          now apply app_cons_not_nil with (x:=hs) (a:=nl) (y:=nil).
        * apply list_app_cons in H; destruct hs; intuition; subst.
          -- ddestruction H1.
          -- now (exists hs).
    - (* l = h :: ts, w = Obs e v *)
      rewrite bind_bind.
      eapply au_bind_r_eq.
      + unfold log, trigger.
        apply au_vis_l...
        intros [].
        cright; apply ax_done...
      + rewrite bind_ret_l, bind_guard, sb_guard, bind_ret_l, interp_state_ret.
        cright; apply ax_done...
        split; intuition...
        eexists; split...
        cbn; split...
        destruct v, e.
        destruct Hw as (hs & H).
        destruct ts...
        * apply list_app_cons in H; destruct hs; intuition.
          exfalso.
          now apply app_cons_not_nil with (x:=hs) (a:=nl) (y:=nil).
        * apply list_app_cons in H; destruct hs; intuition; subst.
          -- ddestruction H1.
          -- now (exists hs).
  Qed.

  (* Ex2: Now the program is [rotate], which pushes hay [hy]
     into a [q], we will eventually get the needle [nl] out *)
  Fixpoint index(l: list S)(s: S): option nat :=
    match l with
    | h :: ts =>
        if h =? s then
          Some (List.length ts)
        else
          index ts s
    | nil => None
    end.

  (* Needle to look for is [gd], all other hay is [hy] *)
  Lemma index_last_S(nl hy: S) (Hnl: hy <> nl): forall l,
      index (l ++ [hy]) nl = option_map Datatypes.S (index l nl).
  Proof.
    induction l; cbn.
    - eapply rel_dec_neq_false in Hnl; eauto.
      now rewrite Hnl.
    - destruct (a =? nl) eqn:Ha.
      + rewrite app_length; cbn.
        rewrite PeanoNat.Nat.add_1_r.
        reflexivity.
      + apply IHl.
  Qed.

  (* queue instrumentation, observe final queue. *)
  Definition h_ghostE: queueE S ~> stateT (list S) (ctreeW (list S)) := 
    fun e =>
      mkStateT (fun q =>
                 match e return ctreeW (list S) (encode e * list S) with
                 | Push v =>
                     log (q ++ [v]);;
                     Ret (tt, q ++ [v])
                 | Pop => match q with
                         | nil => Ret (None, nil)
                         | h :: ts =>
                             log ts ;;
                             Ret (Some h, ts)
                         end
                 end).

  Theorem rotate_af_pop: forall q nl hy (Hnl: nl <> hy),      
      <( {interp_state h_ghostE (rotate hy) (q ++ [nl])}, Pure |=
           AF visW {fun l => exists ts, l = nl :: ts /\ Forall (eq hy) ts} )>.
  Proof with eauto with ctl.
    intros.
    apply af_iter_state_list
      with (Ri:=fun '(tt) w l =>
                  not_done w /\
                  match w with
                  | Obs (Log g) tt =>
                      length l = length q /\
                        index l t = Some g.(dist)
                  | _ => length l = length q /\
                          index l t = Some (length l)
                  end); [|eauto with ctl].
    intros [] w l [Hw H'].    
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
  
