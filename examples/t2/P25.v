
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
  Import Clang.Clang.
  Local Open Scope clang_scope.
  Definition c: string := "c".
  Definition r: string := "r".
  Definition cs: string := "cs".
  
  Definition p25: ctree Mem unit :=
    [[
        r := 0 ;;;
        cs := 8 ;;;
        while cs ?> 0 do
          c ::= c - 1 ;;;
          r ::= r + 1
          done
    ]].


  (* // (varC <= 5) || ([AF](varR > 5)) *)
  Lemma p25_spec: forall cval,
      cval >= 1%Z ->
      <( {instr_stateE p25 (M.add c cval M.empty)}, Pure |=
           (visW {assert c (fun cv => cv <= 5)} \/ AF visW {assert r (fun rv => rv > 5)}) )>.
  Proof with eauto with ctl.
    intros.
    unfold p25.
    
  Admitted.
End P25.        
