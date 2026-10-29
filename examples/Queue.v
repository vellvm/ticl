From TICL Require Import
  CTree.Core
  Logic.Core
  CTree.Logic.Trans
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.Bind
  CTree.Logic.State
  CTree.Logic.CanStep
  CTree.Interp.State.Mod
  CTree.Events.State
  CTree.Events.Writer
  Lang.MeQ
  Utils.Lists.

From ExtLib Require Export
  Structures.MonadState
  Data.Monads.StateMonad.

From Stdlib Require Import
  Lia
  List.

From ExtLib Require Import RelDec.

Generalizable All Variables.

Import CTree CTreeNotations TiclNotations ListNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Module Queue.
  Include ME.
  Infix "=?" := (rel_dec) (at level 75).

  (* Ex2: Rotate a queue (pop an element from head, add it to tail) *)
  Definition rotate: CProg unit :=
    CUntilNone
      (CBind CPop
         (fun opt =>
            CBind
              (CIfSome opt (fun x => CPush x))
              (fun 'tt => CRet (Some tt)))).
              

  Theorem rotate_agaf_pop {B: Type -> Type}: forall q i (nl: T),
      find_index (@rel_dec T eq HDec) nl q = Some i ->
      <( {instr_prog (B:=B) rotate q}, Pure |= AG AF visW {fun h => h = nl} )>.
  Proof.
    intros.
    unfold rotate; cbn. 
    apply ag_qprog_invariance with
      (R:= fun q w => exists h ts, q = h :: ts /\ (h = nl \/ (h <> nl /\ exists i, find_index (@rel_dec T eq HDec) nl ts = Some i))); eauto with ticl.
    - destruct q; try solve [ inv H ].
      exists t, q; intuition.
      rewrite find_index_cons in H.
      destruct (t =? nl) eqn:Hnl; inv H.
      + rewrite rel_dec_correct in Hnl.
        left; eauto with ticl.
      + right.
        destruct (find_index (@rel_dec T eq HDec) nl q) eqn:Hq, i; inv H1.
        apply neg_rel_dec_correct in Hnl; split; eauto with ticl.
    - clear H q.
      intros q w (h & ts & -> & [-> | (Hnl & Hi)]) Hd.
      + (* h = nl *)
        split.
        * (* iter |= AF *)
          apply aul_qprog_until_now.
          eapply aul_qprog_bind.
          -- eapply aur_pop_cons; eauto with ticl.
             csplit; eauto with ticl.
          -- cleft.
             apply ticll_vis; eauto with ticl.
        * (* body variant/invariant *)
          eapply anr_qprog_bind_l.
          -- apply anr_pop_cons; eauto with ticl.
             csplit; eauto with ticl.
          -- eapply aur_qprog_bind_r.
             ++ apply equivr_ifsome_some.
                cleft.
                apply axr_push; eauto with ticl.
             ++ cbn; cleft.
                apply axr_qprog_ret; eauto with ticl.
                split2; [reflexivity | constructor |].
                (* Low-level list proof starts here *)
                destruct ts.
                ** exists nl, []; eauto with ticl.
                ** exists t, (ts ++ [nl]); split; eauto with ticl.
                   destruct (t =? nl) eqn:Hnl.
                   --- left.
                       now apply rel_dec_correct.
                   --- right.
                       apply neg_rel_dec_correct in Hnl; split; eauto with ticl.
                       apply (find_index_last_ex (@rel_dec T eq HDec) rel_dec_correct).
      + (* h <> nl *)
        clear i.
        destruct Hi as (i & Hi).
        split.
        * eapply aul_qprog_eventually with
            (Ri:=fun q _ =>
                   exists h ts, q = h :: ts /\ (h = nl \/ (h <> nl /\ exists i, find_index (@rel_dec T eq HDec) nl ts = Some i)))
            (f:=fun q =>
                  match find_index (@rel_dec T eq HDec) nl q with
                  | None => length q
                  | Some v => v
                  end); eauto with ticl.
          -- exists h, ts; split; eauto with ticl.
          -- intros q w' (h' & ts' & -> & [-> | (Hnl' & ?)]) Hd'.
             ++ right.
                eapply aul_qprog_bind.
                ** apply aur_pop_cons; eauto with ticl.
                   csplit; eauto with ticl.
                ** eapply aul_qprog_bind.
                   --- apply equivr_ifsome_some.
                       cleft.
                       apply axr_push; eauto with ticl.
                   --- cleft.
                       csplit; eauto with ticl.
             ++ left.
                destruct H as (i' & Hi').
                eapply aur_qprog_bind_r.
                ** apply aur_pop_cons; eauto with ticl.
                   csplit; eauto with ticl.
                ** eapply aur_qprog_bind_r.
                   --- apply equivr_ifsome_some.
                       cleft.
                       apply axr_push; eauto with ticl.
                   --- cbn.
                       cleft.
                       apply axr_qprog_ret; eauto with ticl.
                       exists tt; split2; eauto with ticl.
                       split.
                       +++ destruct ts'; cbn; try solve [inv Hi'].
                           exists t, (ts' ++ [h']); split; eauto with ticl.
                           rewrite find_index_cons in Hi'.
                           destruct (t =? nl) eqn:Hnl''; inv Hi'.
                           *** rewrite rel_dec_correct in Hnl''; subst.
                               now left.
                           *** right; split.
                               ---- now apply neg_rel_dec_correct in Hnl''.
                               ---- destruct (find_index (@rel_dec T eq HDec) nl ts') eqn:Hts'; inv H0.
                                    exists n.
                                    now apply find_index_app_l.
                       +++ (* variant *)
                         apply rel_dec_neq_false with (r:=HDec) in Hnl'; [|typeclasses eauto].
                         rewrite Hnl', Hi'; cbn.
                         erewrite find_index_app_l; eauto with ticl.
        * eapply anr_qprog_bind_l.
          -- apply anr_pop_cons; eauto with ticl.
             csplit; eauto with ticl.
          -- eapply aur_qprog_bind_r.
             ++ eapply equivr_ifsome_some.
                cleft.
                eapply axr_push; eauto with ticl.
             ++ cbn.
                cleft.
                apply axr_qprog_ret; eauto with ticl.
                split2; [reflexivity | constructor |].
                destruct ts; try solve [inv Hi].
                exists t, (ts ++ [h]); intuition.
                destruct (t =? nl) eqn:Hnl'; inv Hi.
                ** rewrite rel_dec_correct in Hnl'; subst; eauto with ticl.
                ** right.
                   rewrite Hnl' in H0.
                   destruct (find_index (@rel_dec T eq HDec) nl ts) eqn:Hts; inv H0.
                   split.
                   --- now apply neg_rel_dec_correct.
                   --- exists n.
                       now apply find_index_app_l.
  Qed.
End Queue.

