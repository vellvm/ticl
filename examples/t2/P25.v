
From CTree Require Import
  CTree.Core
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
  CTree.Events.Writer.

From Coq Require Import
  ZArith.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.
Local Open Scope Z_scope.


(*
// OK
// (varC <= 5) || ([AF](varR > 5))
// -ctl "OR{varC <= 5}{AF{varR > 5}}
// -joinbwd 6

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

Module Clang.

  Record Mem := { varC : Z; varR : Z; varCS: Z }.

  Definition setC (c: Z): ctree (stateE Mem) unit :=
    m <- get ;;
    put {| varC := c; varR := m.(varR); varCS := m.(varCS) |}.
  
  Definition setR (r: Z): ctree (stateE Mem) unit :=
    m <- get ;;
    put {| varC := m.(varC); varR := r; varCS := m.(varCS) |}.

  Definition setCS (cs: Z): ctree (stateE Mem) unit :=
    m <- get ;;
    put {| varC := m.(varC); varR := m.(varR); varCS := cs |}.

  Definition p25: ctree (stateE Mem) unit :=
    setR 0%Z ;;
    setCS 8%Z ;;
    iter (fun _ =>
            m <- get;;
            if (0%Z <? m.(varCS)) then (
                   setC (m.(varC) - 1) ;;
                   setR (m.(varR) + 1) ;;
                   setCS (m.(varCS) - 1) ;;
                   continue
                 )
            else break) tt.

  (* // (varC <= 5) || ([AF](varR > 5)) *)
  Lemma p25_spec: forall c r cs,
      c >= 1%Z ->
      <( {instr_stateE p25 {| varC := c; varR := r; varCS := cs |} }, Pure |=
           (visW {fun m => m.(varC) <= 5%Z} \/ AF visW {fun m => m.(varR) > 5}) )>.
  Proof with eauto with ctl.
    intros.
    unfold p25.
    cright.
    eapply aul_state_bind_r_eq.
    - cleft.
      csplit...
      + csplit...
      + eapply can_step_state_bind_l.
        * unfold get, trigger; rewrite interp_state_vis.
          cbn; apply ktrans_vis.
          exists tt; intuition.
        * constructor.
      + intros.
        
