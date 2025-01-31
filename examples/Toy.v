
From TICL Require Import
  ICTree.Core
  Events.State
  Events.Writer
  Logic.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Logic.Trans
  Logic.Kripke
  ICTree.Interp.Core
  ICTree.Logic.AF
  ICTree.Logic.AX
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.State
  ICTree.Logic.CanStep
  ICTree.Interp.State
  ICTree.Events.State
  ICTree.Events.Writer
  Lang.Maps
  Lang.StImp.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList.

From Coq Require Import
  Lia
  Strings.String.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.
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

  Lemma toy_spec: forall cval N,
      let init := add c cval empty in
      <( {instr_prog toy init}, {Obs (Log init) tt} |= var c <= N \/ AF (var r >= N) )>.
  Proof with (eauto with ticl; try lia).
    intros.
    assert (Hcr: c<>r) by (intro Hcontra; inv Hcontra).
    unfold toy, init.
    destruct (Compare_dec.le_gt_dec cval N).
    - cleft. (* cval <= N *)
      eapply var_le with cval...
    - cright. (* cval > N *)
      eapply aul_cprog_seq.
      + eapply aur_cprog_assgn...
        * apply axr_cexp_const...
        * csplit...
      + eapply aul_cprog_while with (Ri:=fun ctx => assert1 c ctx (fun x => x <= cval)
                                                 /\ assert2 r c ctx (fun a b => a + b = cval))
                                    (f:=fun ctx => match lookup r ctx with
                                                | Some rv => cval - rv
                                                | _ => 0
                                                end)...
        * intuition.
          -- apply assert1_add_neq...
             apply assert1_add_eq...
          -- apply assert2_add_l...
        * eapply axr_ccomp_lt...
          cbn; destruct cval... 
        * intros ctx ((vc & Hc & Hvc) & (vr & vc' & Hr & Hc' & Hsum)).
          rewrite Hc' in Hc; inv Hc.
          destruct vc eqn:Hceq.
          -- (* c = 0 *)
            exists false; split.
            ++ eapply axr_ccomp_lt...
            ++ eapply var_ge with vr... 
          -- (* c = S n *)
            exists true; split.
            ++ eapply axr_ccomp_lt...
            ++ destruct n eqn:Hn.
               ** (* n = 0, c = 1 *)
                 left.
                 eapply aul_cprog_seq.
                 --- eapply aur_cprog_assgn...
                     +++ eapply axr_cexp_sub...
                     +++ csplit...
                 --- eapply aul_cprog_assgn.
                     +++ eapply axr_cexp_add...
                         rewrite lookup_add_neq...
                     +++ csplit...
                     +++ eapply var_ge with (vr+1)...
               ** (* n = S n0, c > 1 *)
                 right.
                 eapply aur_cprog_seq.
                 --- eapply aur_cprog_assgn...
                     +++ eapply axr_cexp_sub...
                     +++ csplit...
                 --- eapply aur_cprog_assgn...
                     +++ eapply axr_cexp_add...
                         rewrite lookup_add_neq...
                     +++ csplit...
                     +++ intuition.
                         *** apply assert1_add_neq...
                             apply assert1_add_eq...
                         *** apply assert2_add_l...
                         *** rewrite lookup_add_eq...
                             rewrite Hr...
  Qed.
 

End P25.        
