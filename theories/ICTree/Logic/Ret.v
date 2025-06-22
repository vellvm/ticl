From TICL Require Import
  Events.Core
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.EX
  ICTree.Logic.EF
  ICTree.Logic.EG
  Logic.Core.

Generalizable All Variables.

Import ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.

(** * Ret lemma for prefix formulas *)
Section RetLemmas.
  Context {E: Type} {HE: Encode E}.

  (** [Ret] nodes are prefix formula equivalent, regardless of the return value.
      Proof is by induction on the formula. *)
  Theorem ticll_ret_equiv{X Y}: forall (x: X) (y: Y) (φ: ticll E) w,
      <( {Ret x}, w |= φ )> <-> <( {Ret y}, w |= φ )>.
  Proof with auto with ticl.    
    split; intros * H.
    - assert (Hd: not_done w) by now apply ticll_not_done in H.
      assert (Hs: can_step (Ret y) w) by now apply can_step_ret; auto.      
      generalize dependent w; revert x y.
      induction φ; intros.
      + (* now *) cdestruct H; csplit...
      + (* U *) destruct q.
        * eapply aul_ret.
          eapply aul_ret in H.
          cdestruct H.
          -- cleft; apply IHφ2 with x...
          -- cright; now apply anl_ret in H.
        * apply eul_ret.
          apply eul_ret in H.
          cdestruct H.
          -- cleft; apply IHφ2 with x...
          -- cright; now apply enl_ret in H.
      + (* X *) destruct q.
        * now apply anl_ret in H.
        * now apply enl_ret in H.
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
    - assert (Hd: not_done w) by now apply ticll_not_done in H.
      assert (Hs: can_step (Ret x) w) by now apply can_step_ret; auto.      
      generalize dependent w; revert x y.
      induction φ; intros.
      + (* now *) cdestruct H; csplit...
      + (* U *) destruct q.
        * eapply aul_ret.
          eapply aul_ret in H.
          cdestruct H.
          -- cleft; apply IHφ2 with y...
          -- cright; now apply anl_ret in H.
        * apply eul_ret.
          apply eul_ret in H.
          cdestruct H.
          -- cleft; apply IHφ2 with y...
          -- cright; now apply enl_ret in H.
      + (* X *) destruct q.
        * now apply anl_ret in H.
        * now apply enl_ret in H.
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
