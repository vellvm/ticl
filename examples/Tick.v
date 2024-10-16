From ICTL Require Import
  ICTree.Core
  Logic.Ctl
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

Import ICtree ICTreeNotations CtlNotations.
Local Open Scope ictree_scope.
Local Open Scope ctl_scope.

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
  (* Ex1: Non-det loop calling tick *)
  Definition ticker: ictree tickE unit :=
    forever unit
      (fun _ =>
         ICtree.br2
           (forever unit (fun _ => tick) tt)
           tick)
      tt.

  (* This requires the AR iter lemma, it's something like this

  Lemma ag_iter_or{X I} (R: rel I (World E)) (i: I) w (k: I -> ictree E (I + X)) φ:
    R i w ->
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |= φ)> \/
          <[ {k i}, w |= φ AN (φ AR AX done
                      {fun (lr: I + X) (w': World E) =>
                         exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
    <( {iter k i}, w |= AG φ )>.
  Typeclasses Transparent equ.
  Example ag_tick:
    <( ticker, {Obs Tick tt} |= AG vis {fun e _ => e = Tick} )>.
   *)
    
  (* Ex2: Non-det loop calling tick *)
  Definition tocker: ictree tickE unit :=
    forever unit
      (fun _ =>
         ICtree.br2
           (ICtree.br2 tick tock)
           tick)
      tt.

  Example eg_tock:
    <( tocker, {Obs Tock tt} |= EG vis {fun e _ => e = Tock} )>.
  Proof with auto with ctl.
    unfold tocker, forever.
    apply eg_iter with (R:=fun 'tt w => w = Obs Tock tt)...
    intros [] w ->.
    split.
    - csplit...
    - unfold map, br2.
      rewrite bind_br.
      apply exr_br; split; [csplit; eauto with ctl|].
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
          apply ex_done; split.
          -- csplit...
          -- eexists; intuition.
             exists tt; intuition.
  Qed.
End TickTock.
