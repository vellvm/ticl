
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
  Lang.Clang.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList.

From Coq Require Import
  Strings.String
  ZArith.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.
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
        done
    ]].

  (* // (varC <= 5) || ([AF](varR > 5)) *)
  Lemma p25_spec: forall cval,
      let init := add c cval empty in
      <( {instr_cprog p25 init}, {Obs (Log init) tt} |=
           (visW {assert c (fun cv => cv <= 5)} \/ AF visW {assert r (fun rv => rv > 5)}) )>.
  Proof with eauto with ticl.
    intros.
    unfold p25, init.
    destruct (Z.le_gt_cases cval 5).
    - cleft. (* cv <= 5 *)
      now eapply vis_c_assert.
    - cright. (* cv > 5 *)
      eapply aul_cprog_seq.
      + eapply aur_cprog_assgn...
        csplit...
      + eapply aul_cprog_seq.
        * eapply aur_cprog_assgn...
          csplit...
        * do 6 (
              eapply afl_cprog_while_unfold; auto with ticl;
              [eapply aur_cprog_seq; eapply aur_cprog_assgn; auto with ticl;
               csplit; auto with ticl|]; cbn
            ).
          cleft.
          apply vis_c_assert...
  Qed.

End P25.        
