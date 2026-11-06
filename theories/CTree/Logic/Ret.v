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
      <( {Ret x: ctree E B X}, w |=L φ )> <-> <( {Ret y: ctree E B Y}, w |=L φ )>.
  Proof with auto with ticl.
    assert (ret_impl :
      forall (A C : Type) (a : A) (c : C) (φ : ticll E) w,
        <( {Ret a: ctree E B A}, w |=L φ )> -> <( {Ret c: ctree E B C}, w |=L φ )>) by
      (intros A C a c φ w H;
       assert (Hd : not_done w) by (now apply ticl_not_done in H);
       assert (Hs : can_step (Ret c: ctree E B C) w) by (now apply can_step_ret);
       generalize dependent w; revert a c; induction φ as [p | q φ1 IHφ1 φ2 IHφ2 | q φ1 IHφ1 φ2 IHφ2 | q φ IHφ | φ1 IHφ1 φ2 IHφ2 | φ1 IHφ1 φ2 IHφ2] using ticll_ind; intros;
       [ cdestruct H; csplit; auto with ticl
       | destruct q;
         [ eapply (au_ret (b:=false)); eapply (au_ret (b:=false)) in H; cdestruct H;
           [ cleft; apply IHφ2 with a; auto with ticl | cright; now apply (an_ret (b:=false)) in H ]
         | apply (eu_ret (b:=false)); apply (eu_ret (b:=false)) in H; cdestruct H;
           [ cleft; apply IHφ2 with a; auto with ticl | cright; now apply (en_ret (b:=false)) in H ] ]
       | destruct q; [now apply (an_ret (b:=false)) in H | now apply (en_ret (b:=false)) in H]
       | destruct q; [now apply ag_ret in H | now apply eg_ret in H]
       | cdestruct H; csplit; [apply IHφ1 with a; auto with ticl | apply IHφ2 with a; auto with ticl]
       | cdestruct H; [cleft; apply IHφ1 with a; auto with ticl | cright; apply IHφ2 with a; auto with ticl] ]).
    intros x y φ w; split; intro H.
    - exact (ret_impl X Y x y φ w H).
    - exact (ret_impl Y X y x φ w H).
  Qed.
End RetLemmas.
