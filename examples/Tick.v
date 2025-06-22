From TICL Require Import
  ICTree.Core
  Logic.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Logic.EX
  ICTree.Logic.EF
  ICTree.Logic.EG
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.Trans
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.CanStep.

From Coinduction Require Import coinduction tactics.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.

Variant tickE: Type :=
  | Tick
  | Tock.

Global Instance encode_tickE: Encode tickE :=
  fun e => match e with
        | Tick | Tock => unit
        end.

Definition tick: ictree tickE unit :=
  @ICtree.trigger tickE tickE _ _ (ReSum_refl) (ReSumRet_refl) Tick.

Definition tock: ictree tickE unit :=
  @ICtree.trigger tickE tickE _ _ (ReSum_refl) (ReSumRet_refl) Tock.

Section TickTock.
  (** * Example 1: Non-det loop calling tick *)
  Definition tocker: ictree tickE unit :=
    forever unit
      (fun _ =>
         ICtree.br2
           (ICtree.br2 tick tock)
           tick)
      tt.

  (** * Specification *)
  (** There exists an infinite path that will allways [tock]. *)
  Example eg_tock:
    <( tocker, {Obs Tock tt} |= EG vis {fun e _ => e = Tock} )>.
  Proof with auto with ticl.
    unfold tocker, forever.
    apply eg_iter with (R:=fun 'tt w => w = Obs Tock tt)...
    intros [] w ->.
    split.
    - csplit...
    - unfold map, br2.
      rewrite bind_br.
      apply enr_br; split; [csplit; eauto with ticl|].
      exists Fin.F1.
      rewrite bind_br.
      apply eur_br.
      right; split.
      + csplit...
      + exists (Fin.FS Fin.F1).
        unfold tock.
        setoid_rewrite (@bind_trigger (unit + unit) tickE tickE _ _
                          ReSum_refl ReSumRet_refl
                          Tock _).
        apply eur_vis...
        right.
        split.
        * csplit...
        * exists tt.
          apply eur_ret.
          cleft.
          apply enr_done; split.
          -- csplit...
          -- eexists; intuition.
             exists tt; intuition.
  Qed.
End TickTock.
