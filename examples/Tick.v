From CTree Require Import
  CTree.Core
  Logic.Ctl
  CTree.Equ
  CTree.SBisim
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

From Coinduction Require Import coinduction tactics.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.

Variant tickE: Type :=
  | Tick
  | Tock.

Global Instance encode_tickE: Encode tickE :=
  fun e => match e with
        | Tick | Tock => unit
        end.

Definition tick: ctree tickE unit :=
  @Ctree.trigger tickE tickE _ _ (ReSum_refl) (ReSumRet_refl) Tick.

Definition tock: ctree tickE unit :=
  @Ctree.trigger tickE tickE _ _ (ReSum_refl) (ReSumRet_refl) Tock.

Section TickTock.
  (* Ex1: Non-det loop calling tick *)
  Definition ticker: ctree tickE unit :=
    forever unit
      (fun _ =>
         Ctree.br2
           (forever unit (fun _ => tick) tt)
           tick)
      tt.

  (* This requires the AR iter lemma, it's something like this

  Lemma ag_iter_or{X I} (R: rel I (World E)) (i: I) w (k: I -> ctree E (I + X)) φ:
    R i w ->
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |= φ)> \/
          <[ {k i}, w |= φ AX (φ AR AN done
                      {fun (lr: I + X) (w': World E) =>
                         exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
    <( {iter k i}, w |= AG φ )>.
  Typeclasses Transparent equ.
  Example ag_tick:
    <( ticker, {Obs Tick tt} |= AG vis {fun e _ => e = Tick} )>.
   *)
    
  (* Ex2: Non-det loop calling tick *)
  Definition tocker: ctree tickE unit :=
    forever unit
      (fun _ =>
         Ctree.br2
           (Ctree.br2 tick tock)
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
