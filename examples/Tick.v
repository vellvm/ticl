From TICL Require Import
  CTree.Core
  Logic.Core
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.EG
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.Trans
  CTree.Logic.Bind
  CTree.Logic.Iter
  CTree.Logic.CanStep.

From Coinduction Require Import all.

Generalizable All Variables.

Import CTree CTreeNotations TiclNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.

Variant tickE: Type -> Type :=
  | Tick : tickE unit
  | Tock : tickE unit.

Definition tick: ctree tickE B2 unit := CTree.trigger Tick.
Definition tock: ctree tickE B2 unit := CTree.trigger Tock.

Section TickTock.
  (** * Example 1: Non-det loop calling tick *)
  (** The choices are observable scheduling choices, hence visible ([brS2]). *)
  Definition tocker: ctree tickE B2 unit :=
    CTree.iter
      (fun _ : unit =>
         CTree.map inl
           (brS2
              (brS2 tick tock)
              tick))
      tt.

  (** * Specification *)
  (** There exists an infinite path that will allways [tock]. *)
  Example eg_tock:
    <( tocker, {Obs Tock tt} |= EG vis {fun _ e _ => existT _ _ e = existT _ _ Tock} )>.
  Proof.
    unfold tocker.
    apply eg_iter with (R:=fun 'tt w => w = Obs Tock tt); auto with ticl.
    intros [] w ->.
    split.
    - csplit; auto with ticl.
    - unfold CTree.map, brS2.
      rewrite bind_br; setoid_rewrite bind_step.
      apply enr_brS; split; [csplit; eauto with ticl|].
      exists true; cbn.
      rewrite bind_br; setoid_rewrite bind_step.
      apply eur_brS.
      right; split.
      + csplit; auto with ticl.
      + exists false; cbn.
        unfold tock, CTree.trigger.
        rewrite bind_vis.
        apply eur_vis.
        right.
        split.
        * csplit; auto with ticl.
        * exists tt.
          rewrite bind_ret_l.
          apply eur_ret.
          cleft.
          apply ret_ret; [constructor |].
          exists tt; intuition.
  Qed.
End TickTock.
