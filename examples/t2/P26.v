
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
  String
  Data.Map.FMapAList
  Structures.Maps.

From Coq Require Import
  Strings.String
  Lia
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
    int varCS = 4;


    while (varCS > 0) {
        if (varC >= varCS) {
            varC = varC - 1;
            varR = varR + 1;
            varCS = varCS - 1;
        } else {
            /* varC = varC - 1; */ 
            /* varR = varR + 1; */ 
            varCS = varCS - 1;
        }
    }
}
 *)

Module P26.
  Include Clang.Clang.
  Local Open Scope clang_scope.

  Definition c: string := "c".
  Definition r: string := "r".
  Definition cs: string := "cs".
  
  Definition p26: CProg :=
    [[
        r := 0 ;;;
        cs := 4 ;;;
        while cs > 0 do
          if c >= cs then
            c := c - 1 ;;;
            r := r + 1 ;;;
            cs := cs - 1
          else
            cs := cs - 1
    ]].

  Arguments alist_add /.

  (* // (varC > 5) || [EG](varR <= 5) *)
  Lemma p26_spec: forall cval,
      let init := add r 0 (add c cval empty) in
      <( {instr_cprog p26 init}, {Obs (Log init) tt} |=
           (visW {assert c (fun cv => cv > 5)} \/ EG visW {assert r (fun rv => rv <= 5)}) )>.
  Proof with eauto with ctl.
    intros.
    unfold p26, init.
    destruct (Z.le_gt_cases cval 5).
    - cright. (* cv <= 5 *)      
      eapply eg_cprog_seq.
      + eapply eur_cprog_assgn_eq...
        constructor; cbn; lia.
      + eapply eg_cprog_seq.
        * eapply eur_cprog_assgn_eq...
          constructor; cbn; lia.
        * (* unfolding doesn't work, need [eg_iter] lemma *)
          cbn.
          evar (RR: Ctx -> Prop).
          eapply eg_cprog_while_gt with (R:= fun ctx' => assert r (fun rv => rv <= 5) ctx' /\ RR ctx')...
          -- split.
             ++ cbn; lia.
             ++ admit. 
          -- intros ctx' (Hr & HR); split. 
             ++ apply ctll_vis; constructor...
             ++ apply enr_cprog_ite_gte.
             apply mapsto_lookup in Hr. rewrite Hr.
             apply vis_c_assert.
          -- right; reflexivity. cbn; lia.
          -- eapply eur_cprog_ite_gte; cbn.
             pose proof (Zge_cases cval 4); destruct (cval >=? 4).
             ++ eapply eur_cprog_seq.
                ** eapply eur_cprog_assgn_eq...
                   constructor; cbn; lia.
                ** eapply eur_cprog_seq.
                   --- eapply eur_cprog_assgn_eq...
                       constructor; cbn; lia.
                   --- cbn.
                       eapply eur_cprog_assgn...
                       +++ constructor; cbn; lia.
             ++ eapply eur_cprog_assgn...
                constructor; cbn; lia.
          -- intros ctx [-> | ->].
             ++ 
      + eapply aul_cprog_seq.
        * eapply afr_cprog_assgn...
          eapply axr_cexp_const...
        * do 7 p25_unfold.
          cleft.
          apply vis_c_assert... *)
  Qed.

End P25.        
