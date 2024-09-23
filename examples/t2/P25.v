
From CTree Require Import
  CTree.Core
  Events.State
  Events.Writer
  Logic.Ctl
  CTree.Equ
  CTree.SBisim
  CTree.Logic.Trans
  Logic.Kripke
  CTree.Interp.Core
  CTree.Logic.AF
  CTree.Logic.AX
  CTree.Logic.Bind
  CTree.Logic.Iter
  CTree.Logic.State
  CTree.Logic.CanStep
  CTree.Interp.State
  CTree.Events.State
  CTree.Events.Writer
  Lang.Clang.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList.

From Coq Require Import
  Strings.String
  ZArith.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
Local Open Scope Z_scope.

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
  Import Clang.Clang.
  Local Open Scope clang_scope.

  Definition c: string := "c".
  Definition r: string := "r".
  Definition cs: string := "cs".
  
  Definition p25: CProg :=
    [[
        r := 0 ;;;
        cs := 8 ;;;
        while cs > 0 do
          c := c - 1 ;;;
          r := r + 1
    ]].

  (* // (varC <= 5) || ([AF](varR > 5)) *)
  Lemma p25_spec: forall cval,
      let init := add c cval empty in
      <( {instr_cprog p25 init}, {Obs (Log init) tt} |=
           (visW {assert c (fun cv => cv <= 5)} \/ AF visW {assert r (fun rv => rv > 5)}) )>.
  Proof with eauto with ctl.
    intros.
    unfold p25, init.
    destruct (Z.le_gt_cases cval 5).
    - cleft. (* cv <= 5 *)
      now eapply vis_c_assert.
    - cright. (* cv > 5 *)
      eapply aul_cprog_seq.
      + eapply afr_cprog_assgn...
      + eapply aul_cprog_seq.
        * eapply afr_cprog_assgn...
        * do 6 (
              eapply afl_cprog_while_unfold; auto with ctl;
              [eapply aur_cprog_seq; eapply afr_cprog_assgn; auto with ctl|]; cbn
            ).
          cleft.
          apply vis_c_assert...
  Qed.

End P25.        
