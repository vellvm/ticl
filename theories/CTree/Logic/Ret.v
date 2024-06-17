From CTree Require Import
  Events.Core
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.EG
  Logic.Ctl.

Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

Section RetLemmas.
  Context {E: Type} {HE: Encode E}.

  Theorem ctll_ret_equiv{X Y}: forall (x: X) (y: Y) (φ: ctll E) w,
      <( {Ret x}, w |= φ )> <-> <( {Ret y}, w |= φ )>.
  Proof with auto with ctl.    
    split; intros * H.
    - assert (Hd: not_done w) by now apply ctll_not_done in H.
      assert (Hs: can_step (Ret y) w) by now apply can_step_ret; auto.      
      generalize dependent w; revert x y.
      induction φ; intros.
      + (* now *) cdestruct H; csplit...
      + (* U *) destruct q.
        * eapply aul_ret.
          eapply aul_ret in H.
          cdestruct H.
          -- cleft; apply IHφ2 with x...
          -- cright; now apply axl_ret in H.
        * apply eul_ret.
          apply eul_ret in H.
          cdestruct H.
          -- cleft; apply IHφ2 with x...
          -- cright; now apply exl_ret in H.
      + (* X *) destruct q.
        * now apply axl_ret in H.
        * now apply exl_ret in H.
      + (* G *) destruct q.
        * now apply ag_ret in H.
        * now apply eg_ret in H.
      + cdestruct H; csplit.
        * apply IHφ1 with x...
        * apply IHφ2 with x...
      + cdestruct H.
        * cleft.
          apply IHφ1 with x...
        * cright.
          apply IHφ2 with x...
    - assert (Hd: not_done w) by now apply ctll_not_done in H.
      assert (Hs: can_step (Ret x) w) by now apply can_step_ret; auto.      
      generalize dependent w; revert x y.
      induction φ; intros.
      + (* now *) cdestruct H; csplit...
      + (* U *) destruct q.
        * eapply aul_ret.
          eapply aul_ret in H.
          cdestruct H.
          -- cleft; apply IHφ2 with y...
          -- cright; now apply axl_ret in H.
        * apply eul_ret.
          apply eul_ret in H.
          cdestruct H.
          -- cleft; apply IHφ2 with y...
          -- cright; now apply exl_ret in H.
      + (* X *) destruct q.
        * now apply axl_ret in H.
        * now apply exl_ret in H.
      + (* G *) destruct q.
        * now apply ag_ret in H.
        * now apply eg_ret in H.
      + cdestruct H; csplit.
        * apply IHφ1 with y...
        * apply IHφ2 with y...
      + cdestruct H.
        * cleft.
          apply IHφ1 with y...
        * cright.
          apply IHφ2 with y...
  Qed.
End RetLemmas.
