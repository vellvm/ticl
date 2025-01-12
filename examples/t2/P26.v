
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
  Lang.StImp.

From ExtLib Require Import
  String
  Data.Map.FMapAList
  Structures.Maps.

From Coq Require Import
  Strings.String
  Lia.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.

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
  Include StImp.StImp. 
  Local Open Scope stimp_scope.

  Definition c: string := "c".
  Definition r: string := "r".
  Definition cs: string := "cs".

  Definition p26: CProg :=
    [[
        r := 0 ;;;
        cs := 4 ;;;
        while cs >? 0 do
          if c >=? cs then
            c := c - 1 ;;;
            r := r + 1 ;;;
            cs := cs - 1
          else
            cs := cs - 1
        done
    ]].

  Arguments alist_add /.

  (* // (varC > 5) || [EG](varR <= 5) *)
  Lemma p26_spec: forall cval,
      let init := add r 0 (add c cval empty) in
      <( {instr_prog p26 init}, {Obs (Log init) tt} |=
           (var c > 5 \/ {assert c (fun cv => cv > 5)} \/ EG visW {assert r (fun rv => rv <= 5)}) )>.
  Proof with eauto with ticl.
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
          eapply eg_cprog_while_gt with
            (R:= fun ctx' =>
                   assert r (fun rv => rv + 1 <= 5) ctx'
                   /\ assert c (fun cv => cv <= 5) ctx'
                   /\ RR ctx')...
          -- split.
             ++ cbn; lia.
             ++ split; cbn; try lia.
                admit. 
          -- intros ctx' (Hr & Hc & HR); split. 
             ++ apply ticll_vis; constructor...
                unfold assert in *.
                destruct (lookup r ctx'); lia.
             ++ apply eur_cprog_ite_gte.
                pose proof (Zge_cases (cdenote_exp c ctx') (cdenote_exp cs ctx')).
                destruct (cdenote_exp c ctx' >=? cdenote_exp cs ctx') eqn:Hab.
                assert (impl_ticll (unit*Ctx) <( visW {assert r (fun rv : Z => rv <= 5)} )> <( ⊤ )>).
                { unfold impl_ticll; intros; csplit; intuition. }
                ** eapply (impl_ticlr_next Q_E _ _ _ _ H1); [reflexivity|]; clear H1.
                   apply ticlr_euex_exeu.
                   eapply eur_cprog_seq.
                   --- eapply eur_cprog_assgn_eq...
                       constructor.
                       unfold assert in *.
                       destruct (lookup r ctx'); lia.
                   --- eapply eur_cprog_seq.
                       +++ eapply eur_cprog_assgn_eq...
                           constructor; unfold assert.
                           cbn.
                           rewrite remove_neq_alist; intuition.
                           inv H1.
                       +++ cleft.
                           apply enr_cprog_assgn...
                           *** constructor; unfold assert, lookup in *; cbn.
                               rewrite remove_neq_alist; intuition; cbn in Hr.
                               destruct (alist_find RelDec_string r ctx') eqn:Hr';
                                 intuition.
                               inv H1.
                           *** Opaque alist_remove.
                               cbn.
                               split.
                               
                           constructor.
                           
                   unfold instr_cprog, instr_stateE.
                - rewrite H1.
                
                   cbn.
                   setoid_rewrite bind_bind.
                   rewrite interp_state_bind.
                   unfold State.get, ICtree.trigger.
                   setoid_rewrite interp_state_vis.
CC                   setoid_rewrite interp_state_get.
                   apply exr_cprog_assgn.
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
