From TICL Require Import
  ICTree.Core
  Events.Writer
  Logic.Core
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
  ICTree.Events.Writer
  Lang.MeQ.

From ExtLib Require Export
  Structures.MonadState
  Data.Monads.StateMonad.

From Coq Require Import
  Lia
  List.

From ExtLib Require Import RelDec.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Module Queue.
  Include ME.
  Infix "=?" := (rel_dec) (at level 75).

  (* Ex1: Drain a queue until there is nothing left *)
  Definition drain: CProg unit :=
    CUntilNone CPop.

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

  (*| Eventually we get [nl] (needle) to show up |*)
  Example drain_af_pop: forall (nl: T) (q: list T),
      <[ {instr_prog drain (q ++ [nl])}, Pure |= AF finishW= tt [] nl ]>.
  Proof with eauto with ticl.
    intros; unfold drain.
    eapply aur_qprog_termination
      with (f:=fun q => List.length q)
           (Ri:=fun l w =>
                  match w with
                  | Obs (Log s') tt =>
                      match l with
                      | nil => nl = s'
                      | h :: ts => exists hs, h :: ts = hs ++ [nl]
                      end
                  | _ => exists hs, l = hs ++ [nl]
                  end)...
    intros l w Hw Hd.
    destruct l as [|h ts] eqn:Hl; subst.
    - (* l = [] *)
      inv Hd.
      + (* w = Pure *)
        destruct Hw.
        now apply list_app_nil in H.
      + (* w = Obs e v *)
        destruct e, v; subst.
        exists None, [], (Obs (Log t) tt); intuition.
        * cleft.
          apply axr_pop_nil...
        * apply axr_ret...
          econstructor.
          exists tt; intuition.
    - (* l = h :: ts *)
      exists (Some h), ts, (Obs (Log h) tt); intuition.
      + apply aur_pop_cons...
        csplit...
      + inv Hd.
        * destruct Hw.
          apply list_app_cons in H.
          destruct x; intuition; subst...
          destruct x; intuition; cbn.
          -- now (exists []).
          -- now (exists (t0 ::x)).
        * destruct e, v, Hw.
          apply list_app_cons in H.
          destruct x; intuition; subst...
          destruct x; intuition; cbn.
          -- now (exists []).
          -- now (exists (t1 ::x)).
  Qed.
  Print Assumptions drain_af_pop.

  (* Ex2: Rotate a queue (pop an element from head, add it to tail) *)
  Definition rotate: CProg unit :=
    CUntilNone
      (CBind CPop
         (fun opt =>
            CBind
              (CIfSome opt (fun x => CPush x))
              (fun 'tt => CRet (Some tt)))).
              
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
  Proof with eauto with ticl.
    induction ts.
    - exists 0; cbn.
      rewrite rel_dec_eq_true...
      typeclasses eauto.
    - destruct IHts.
      destruct (a =? nl) eqn:Hnl.
      + rewrite rel_dec_correct in Hnl; subst.
        exists 0; cbn.
        rewrite rel_dec_eq_true...
        typeclasses eauto.
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
  Local Typeclasses Transparent equ.
  Local Typeclasses Transparent sbisim.

  Theorem rotate_agaf_pop: forall q i,
      find nl q = Some i ->
      <( {instr_prog rotate q}, Pure |= AG AF visW {fun h => h = nl} )>.
  Proof with eauto with ticl.
    intros.
    unfold rotate; cbn. 
    apply ag_qprog_invariance with
      (R:= fun q w => exists h ts, q = h :: ts /\ (h = nl \/ (h <> nl /\ exists i, find nl ts = Some i)))...
    - destruct q; try solve [ inv H ].
      exists t, q; intuition.
      rewrite unfold_find_hd in H.
      destruct (t =? nl) eqn:Hnl; inv H.
      + rewrite rel_dec_correct in Hnl.
        left...
      + right.
        destruct (find nl q) eqn:Hq, i; inv H1.
        apply neg_rel_dec_correct in Hnl; split...
    - clear H q.
      intros q w (h & ts & -> & [-> | (Hnl & Hi)]) Hd.
      + (* h = nl *)
        split.
        * (* iter |= AF *)
          apply aul_qprog_until_now.
          eapply aul_qprog_bind.
          -- eapply aur_pop_cons...
             csplit...
          -- cleft.
             apply ticll_vis...
        * (* body variant/invariant *)
          eapply anr_qprog_bind_l.
          -- apply anr_pop_cons...
             csplit...
          -- eapply aur_qprog_bind_r.
             ++ apply ticlr_ifsome_some.
                cleft.
                apply axr_push...
             ++ cbn; cleft.
                apply axr_qprog_ret...
                intuition.
                (* Low-level list proof starts here *)
                destruct ts.
                ** exists nl, []...
                ** exists t, (ts ++ [nl]); split...
                   destruct (t =? nl) eqn:Hnl.
                   --- left.
                       now apply rel_dec_correct.
                   --- right.
                       apply neg_rel_dec_correct in Hnl; split...
                       apply find_last_ex.
      + (* h <> nl *)
        clear i.
        destruct Hi as (i & Hi).
        split.
        * eapply aul_qprog_eventually with
            (Ri:=fun q _ =>
                   exists h ts, q = h :: ts /\ (h = nl \/ (h <> nl /\ exists i, find nl ts = Some i)))
            (f:=fun q =>
                  match find nl q with
                  | None => length q
                  | Some v => v
                  end)...
          -- exists h, ts; split...
          -- intros q w' (h' & ts' & -> & [-> | (Hnl' & ?)]) Hd'.
             ++ right.
                eapply aul_qprog_bind.
                ** apply aur_pop_cons...
                   csplit...
                ** eapply aul_qprog_bind.
                   --- apply ticlr_ifsome_some.
                       cleft.
                       apply axr_push...
                   --- cleft.
                       csplit...
             ++ left.
                destruct H as (i' & Hi').
                eapply aur_qprog_bind_r.
                ** apply aur_pop_cons...
                   csplit...
                ** eapply aur_qprog_bind_r.
                   --- apply ticlr_ifsome_some.
                       cleft.
                       apply axr_push...
                   --- cbn.
                       cleft.
                       apply axr_qprog_ret...
                       exists tt; split2...
                       split.
                       +++ destruct ts'; cbn; try solve [inv Hi'].
                           exists t, (ts' ++ [h']); split...
                           rewrite unfold_find_hd in Hi'.
                           destruct (t =? nl) eqn:Hnl''; inv Hi'.
                           *** rewrite rel_dec_correct in Hnl''; subst.
                               now left.
                           *** right; split.
                               ---- now apply neg_rel_dec_correct in Hnl''.
                               ---- destruct (find nl ts') eqn:Hts'; inv H0.
                                    exists n.
                                    now apply find_app_l.
                       +++ (* variant *)
                         apply rel_dec_neq_false with (r:=HDec) in Hnl'; [|typeclasses eauto].
                         rewrite Hnl', Hi'; cbn.
                         erewrite find_app_l...
        * eapply anr_qprog_bind_l.
          -- apply anr_pop_cons...
             csplit...
          -- eapply aur_qprog_bind_r.
             ++ eapply ticlr_ifsome_some.
                cleft.
                eapply axr_push...
             ++ cbn.
                cleft.
                apply axr_qprog_ret...
                intuition.
                destruct ts; try solve [inv Hi].
                exists t, (ts ++ [h]); intuition.
                destruct (t =? nl) eqn:Hnl'; inv Hi.
                ** rewrite rel_dec_correct in Hnl'; subst...
                ** right.
                   rewrite Hnl' in H0.
                   destruct (find nl ts) eqn:Hts; inv H0.
                   split.
                   --- now apply neg_rel_dec_correct.
                   --- exists n.
                       now apply find_app_l.
  Qed.
End Queue.

