From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.EG
  Logic.Core.

Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** * Ret lemma for prefix formulas *)
Section RetLemmas.
  Context {E B: Type -> Type}.

  (** [Ret] nodes are prefix formula equivalent, regardless of the return value.
      Proof is by induction on the formula. *)
  Theorem ticll_ret_equiv{X Y}: forall (x: X) (y: Y) (φ: ticll E) w,
      <( {Ret x: ctree E B X}, w |= φ )> <-> <( {Ret y: ctree E B Y}, w |= φ )>.
  Proof with auto with ticl.
    assert (ret_impl :
      forall (A C : Type) (a : A) (c : C) (φ : ticll E) w,
        <( {Ret a: ctree E B A}, w |= φ )> -> <( {Ret c: ctree E B C}, w |= φ )>) by
      (intros A C a c φ w H;
       assert (Hd : not_done w) by (now apply ticll_not_done in H);
       assert (Hs : can_step (Ret c: ctree E B C) w) by (now apply can_step_ret);
       generalize dependent w; revert a c; induction φ; intros;
       [ cdestruct H; csplit; auto with ticl
       | destruct q;
         [ eapply aul_ret; eapply aul_ret in H; cdestruct H;
           [ cleft; apply IHφ2 with a; auto with ticl | cright; now apply anl_ret in H ]
         | apply eul_ret; apply eul_ret in H; cdestruct H;
           [ cleft; apply IHφ2 with a; auto with ticl | cright; now apply enl_ret in H ] ]
       | destruct q; [now apply anl_ret in H | now apply enl_ret in H]
       | destruct q; [now apply ag_ret in H | now apply eg_ret in H]
       | cdestruct H; csplit; [apply IHφ1 with a; auto with ticl | apply IHφ2 with a; auto with ticl]
       | cdestruct H; [cleft; apply IHφ1 with a; auto with ticl | cright; apply IHφ2 with a; auto with ticl] ]).
    intros x y φ w; split; intro H.
    - exact (ret_impl X Y x y φ w H).
    - exact (ret_impl Y X y x φ w H).
  Qed.
End RetLemmas.
