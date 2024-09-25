
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
// -ctl "AND{AG{AF{n==1}}}{AF{n==0}}"
// -precondition n > 0

void main() {
    int n;  //assume n > 0

    while (n > 0) {
        n--;
    }

    while (n == 0) {
        n++;
        n--;
    }
}
 *)

Module And_test.
  Include Clang.Clang.
  Local Open Scope clang_scope.

  Definition n: string := "n".

  Definition and_test: CProg :=
    [[
        while n > 0 do
           n := n - 1
        done;;;
                      
        while n = 0 do
          n := n + 1;;;                                
          n := n - 1                       
        done
    ]].

  Arguments alist_add /.

  (* // AG{AF{n==1}} /\ AF{n==0} *)
  Lemma and_test_spec: forall nval,
      nval > 0 ->
      let init := add n nval empty in
      <( {instr_cprog and_test init}, {Obs (Log init) tt} |=
                    (AG AF (visW {assert n (fun n_ => n_ = 1)} ))
                     /\ AF visW {assert n (fun n_ => n_ = 0)} )>.
  Proof with eauto with ctl.
    intros.    
    csplit.
    - unfold and_test.
      eapply ag_cprog_seq.
      + eapply aur_cprog_while; cbn.
        * apply Z.gtb_gt in H.
          rewrite H...
        * cbn; intros.
          assert (Hd: not_done w').
          { destruct (load n ctx >? 0) eqn:Hv...          
            cdestruct H0.
            now apply can_step_not_done in Hs.
          }.
          eapply aur_cprog_assgn...
          -- eapply aul_cprog_assgn...
             ++ csplit...
             ++ apply vis_c_assert.
                cbn.
                admit.
          -- unfold instr_cprog, instr_stateE.
             cbn.
             rewrite interp_state_ret.
             apply axr_ret...
             split.
             eapply aul_cprog_assgn...
             csplit...
             ++ destruct (match alist_find RelDec_string n ctx with
                          | Some v => v
                          | None => 0
                          end >? 0) eqn:Hv...
                cdestruct H0.
                now apply can_step_not_done in Hs.
             ++ admit.
          -- unfold instr_cprog, instr_stateE; cbn.
             eapply can_step_state_bind_r.
             ++ rewrite interp_state_get.
                cleft.
                apply axr_ret...
                destruct (match alist_find RelDec_string n ctx with
                          | Some v => v
                          | None => 0
                          end >? 0) eqn:Hv...
                cdestruct H0.
                now apply can_step_not_done in Hs.
             ++ rewrite interp_state_put.
                eapply can_step_bind_l...              
                apply ktrans_vis.
                exists tt; intuition...
                destruct (match alist_find RelDec_string n ctx with
                          | Some v => v
                          | None => 0
                          end >? 0) eqn:Hv...
                cdestruct H0.
                now apply can_step_not_done in Hs.
          -- intros.
             
               apply vis_c_assert.
                cbn.
          eapply aur_cprog_assgn...
          cright.
          apply anl_cprog_assgn.

End And_test.        
