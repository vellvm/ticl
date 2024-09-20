
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
  Structures.Maps.

From Coq Require Import
  ZArith.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
Local Open Scope Z_scope.

(*
void main() {

    int varC; // assume varC >= 1
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

From ExtLib Require Import String.
From Coq Require Import Strings.String.

Module P25.
  Include Clang.Clang.
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

  Ltac p25_unfold := rewrite instr_cprog_while_unfold;
          eapply aul_cprog_ite_gt;
            [ solve [eapply axr_cexp_var; auto with ctl; mapsto_tac]
            | solve [eapply axr_cexp_const; auto with ctl]
            | cbn; eapply aul_cprog_seq];
            [eapply aur_cprog_seq|];          
            [eapply afr_cprog_assgn_decr; auto with ctl; mapsto_tac
            |eapply afr_cprog_assgn_incr; auto with ctl; mapsto_tac
            |].
  
  (* // (varC <= 5) || ([AF](varR > 5)) *)
  Definition init cval := add c cval empty.
  
  Lemma p25_spec: forall cval,
      cval >= 1%Z ->
      <( {instr_cprog p25 (init cval)}, {Obs (Log (init cval)) tt} |=
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
        eapply axr_cexp_const...
      + eapply aul_cprog_seq.
        * eapply afr_cprog_assgn...
          eapply axr_cexp_const...
        * do 7 p25_unfold.
          cleft.
          apply vis_c_assert...
  Qed.

End P25.        
