From TICL Require Import
  CTree.Core
  Logic.Core
  CTree.Logic.Trans
  Logic.Kripke
  CTree.Logic.AF
  CTree.Logic.AX
  CTree.Logic.Bind
  CTree.Logic.Iter
  CTree.Logic.State
  CTree.Logic.CanStep
  CTree.Interp.State.Mod
  CTree.Events.State
  CTree.Events.Writer
  Utils.Maps
  Lang.StImp.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList.

From Stdlib Require Import
  Lia
  Strings.String.

Generalizable All Variables.

Import CTree CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.
Local Open Scope nat_scope.

Module P25.
  Import StImp.StImp Ctx.
  Local Open Scope stimp_scope.

  Definition c: string := "c".
  Definition r: string := "r".

  Definition toy: CProg :=
    [[
        r := 0 ;;;
        while 0 <? c do
          c := c - 1 ;;;
          r := r + 1
        done
    ]].

  (** StImp is deterministic: the branch signature [B] is arbitrary. *)
  Lemma toy_spec {B: Type -> Type}: forall cval N,
      let init := add c cval empty in
      <( {instr_prog (B:=B) toy init}, {Obs (Log init) tt} |= var c <= N \/ AF (var r >= N) )>.
  Proof.
    intros.
    assert (Hcr: c<>r) by (intro Hcontra; inv Hcontra).
    unfold toy, init.
    destruct (Compare_dec.le_gt_dec cval N).
    - cleft. (* cval <= N *)
      eapply var_le with cval; eauto with ticl; try lia.
    - cright. (* cval > N *)
      eapply aul_cprog_seq.
      + eapply aur_cprog_assgn_eq; eauto with ticl; try lia.
        * apply axr_cexp_const; eauto with ticl; try lia.
        * csplit; eauto with ticl; try lia.
      + eapply aul_cprog_while with (Ri:=fun ctx => assert1 c ctx (fun x => x <= cval)
                                                 /\ assert2 r c ctx (fun a b => a + b = cval))
                                    (f:=fun ctx => match lookup r ctx with
                                                | Some rv => cval - rv
                                                | _ => 0
                                                end); eauto with ticl; try lia.
        * intuition.
          -- apply assert1_add_neq; eauto with ticl; try lia.
             apply assert1_add_eq; eauto with ticl; try lia.
          -- apply assert2_add_l; eauto with ticl; try lia.
        * eapply axr_ccomp_lt; eauto with ticl; try lia.
          cbn; destruct cval; eauto with ticl; try lia. 
        * intros ctx ((vc & Hc & Hvc) & (vr & vc' & Hr & Hc' & Hsum)).
          rewrite Hc' in Hc; inv Hc.
          destruct vc eqn:Hceq.
          -- (* c = 0 *)
            exists false; split.
            ++ eapply axr_ccomp_lt; eauto with ticl; try lia.
            ++ eapply var_ge with vr; eauto with ticl; try lia. 
          -- (* c = S n *)
            exists true; split.
            ++ eapply axr_ccomp_lt; eauto with ticl; try lia.
            ++ destruct n eqn:Hn.
               ** (* n = 0, c = 1 *)
                 left.
                 eapply aul_cprog_seq.
                 --- eapply aur_cprog_assgn_eq; eauto with ticl; try lia.
                     +++ eapply axr_cexp_sub; eauto with ticl; try lia.
                     +++ csplit; eauto with ticl; try lia.
                 --- eapply aul_cprog_assgn.
                     +++ eapply axr_cexp_add; eauto with ticl; try lia.
                         rewrite lookup_add_neq; eauto with ticl; try lia.
                     +++ csplit; eauto with ticl; try lia.
                     +++ eapply var_ge with (vr+1); eauto with ticl; try lia.
               ** (* n = S n0, c > 1 *)
                 right.
                 eapply aur_cprog_seq.
                 --- eapply aur_cprog_assgn_eq; eauto with ticl; try lia.
                     +++ eapply axr_cexp_sub; eauto with ticl; try lia.
                     +++ csplit; eauto with ticl; try lia.
                 --- eapply aur_cprog_assgn; eauto with ticl; try lia.
                     +++ eapply axr_cexp_add; eauto with ticl; try lia.
                         rewrite lookup_add_neq; eauto with ticl; try lia.
                     +++ csplit; eauto with ticl; try lia.
                     +++ intuition.
                         *** apply assert1_add_neq; eauto with ticl; try lia.
                             apply assert1_add_eq; eauto with ticl; try lia.
                         *** apply assert2_add_l; eauto with ticl; try lia.
                         *** rewrite lookup_add_eq; eauto with ticl; try lia.
                             rewrite Hr; eauto with ticl; try lia.
  Qed.

End P25.
