
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
(*
void main() {

    int varC; // assume varC >= 1 (LEF: looks like this isn't needed?)
    int varR = 0;
    int varCS = 8;

    while (varCS > 0) {
        if (varC >= varCS) {
            varC = varC - 1;
            varR = varR + 1;
            varCS = varCS - 1;
        } else {
            varC = varC - 1; 
            varR = varR + 1; 
            varCS = varCS - 1;
        }
    }

}
 *)

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

  Lemma toy_spec: forall cval,
      let init := add c cval empty in
      <( {instr_prog toy init}, {Obs (Log init) tt} |= var c <= 5 \/ AF (var r >= 5) )>.
  Proof with eauto with ticl.
    intros.
    assert (Hcr: c<>r) by (intro Hcontra; inv Hcontra).
    unfold toy, init.
    destruct (Compare_dec.le_gt_dec cval 5).
    - cleft. (* cval <= 5 *)
      eapply var_le with cval...
    - cright. (* cval > 5 *)
      eapply aul_cprog_seq.
      + eapply aur_cprog_assgn...
        * apply axr_cexp_const...
        * csplit...
      + eapply aul_cprog_while with (Ri:=fun ctx => assert1 r ctx (fun x => x >= 0)
                                                 /\ assert1 c ctx (fun x => x <= cval)
                                                 /\ assert2 r c ctx (fun a b => a + b = cval))
                                    (f:=fun ctx => match lookup r ctx with
                                                | Some rv => cval - rv
                                                | _ => 0
                                                end)...
        * intuition.
          -- apply assert1_add_eq...
          -- apply assert1_add_neq...
             apply assert1_add_eq...
          -- apply assert2_add_l...
        * eapply axr_ccomp_lt...
          cbn; destruct cval; lia.
        * intros ctx ((vr & Hr & Hvr) & (vc & Hc & Hvc) & (vr' & vc' & Hr' & Hc' & Hsum)).
          rewrite Hc' in Hc; inv Hc.
          rewrite Hr' in Hr; inv Hr.
          destruct vc eqn:Hceq.
          -- (* c = 0 *)
            exists false; split.
            ++ eapply axr_ccomp_lt...
            ++ eapply var_ge with vr... 
               lia.
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
                         lia.
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
                         *** apply assert1_add_eq...
                             lia.
                         *** apply assert1_add_neq...
                             apply assert1_add_eq...
                             lia.
                         *** apply assert2_add_l...
                             lia.
                         *** rewrite lookup_add_eq...
                             rewrite Hr'.
                             lia.
  Qed.
 

End P25.        
