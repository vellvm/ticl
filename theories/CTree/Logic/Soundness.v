From Coq Require Import
  Basics
  Classes.Morphisms.

From CTree Require Import
  Events.Core
  Events.WriterE
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Interp.Core
  CTree.Interp.State
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.AX
  Logic.AF
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

Section SyntacticEntailment.
  Context {E: Type} {HE: Encode E}.

  Inductive syntails{X}: ctree E X -> World E -> ctlf E X -> Prop :=
  (* All formulas are invariant to [Guard] *)
  | SynGuard: forall w φ t,
      syntails t w φ ->
      syntails (Guard t) w φ
  (* Base predicates (ignore t) *)
  | SynNow: forall w φ t,
      φ w ->
      syntails t w <( base φ )>
  | SynDone: forall w φ t,
      done_with φ w ->
      syntails t w <( done φ )>
  (* ψ AU φ *)
  | SynAuStuck: forall w φ ψ,
    syntails (Ctree.stuck) w ψ ->
    syntails (Ctree.stuck) w <( φ AU ψ )>
  | SynAuRet: forall w w' φ ψ r,
      done_with (fun r' w' => w' = w /\ r' = r) w' ->
      syntails (Ctree.stuck) w' <( ψ )> ->
      syntails (Ret r) w <( φ )> ->
      syntails (Ret r) w <( φ AU ψ )>
  | SynAuBrR: forall w n (k: fin' n -> _) φ ψ,
      not_done w ->
      syntails (Br n k) w φ ->
      syntails (Br n k) w <( ψ AU φ )>
  | SynAuBrL: forall w n (k: fin' n -> _) φ ψ,
      not_done w ->      
      syntails (Br n k) w ψ ->
      (forall (i: fin' n), syntails (k i) w <( ψ AU φ )>) ->
      syntails (Br n k) w <( ψ AU φ )>
  | SynAuVisR: forall w (e: E) (k: encode e -> _) φ ψ,
      not_done w ->
      syntails (Vis e k) w φ ->
      syntails (Vis e k) w <( ψ AU φ )>
  | SynAuVisL: forall w (e: E) (k: encode e -> _) (wit: encode e) φ ψ,
      not_done w ->
      syntails (Vis e k) w ψ ->
      (forall (x: encode e), syntails (k x) (Obs e x) <( ψ AU φ )>) ->
      syntails (Vis e k) w <( ψ AU φ )>
  | SynAuBindL: forall {Y} (t: ctree E Y) (k: Y -> ctree E X) φ ψ w,
      syntails t w <(base φ AU now ψ )> ->
      syntails (x <- t ;; k x) w <( base φ AU now ψ )>
  | SynAuBindR: forall {Y} (t: ctree E Y) (k: Y -> ctree E X) w ψ φ R,
      syntails t w <( base ψ AU AX done R )> ->
      (forall r w', R r w' -> syntails (k r)  w' <( base ψ AU φ )>) ->
      syntails (x <- t ;; k x) w <( base ψ AU φ )>
  | SynAuIter: forall {I} Ri Rr Rv (i: I) w (k: I -> ctree E (I + X)) φ,
      (forall (i: I) w,
          Ri i w ->
          syntails (k i) w <( base φ AU AX done
                      {fun (x: I + X) w' =>
                         match x with
                         | inl i' => Ri i' w' /\
                                      Rv (i', w') (i, w)
                         | inr r' => not_done w' /\ φ w' /\ Rr r' w'
                         end})>) ->
      well_founded Rv ->
      Ri i w ->
      syntails (iter k i) w <( base φ AU done Rr )>.
  
  (* Define a second "deterministic entailment" for this 
  | SynAuBindDetR: forall {Y} (t: ctree E Y)
                   (k: Y -> ctree E X) w w' r ψ φ,
      syntails t w <( vis ψ AU AX done= r w' )> ->
      syntails (k r)  w' <( vis ψ AU φ )> ->
      syntails (x <- t ;; k x) w <( vis ψ AU φ )>. *)

  Lemma soundness{X}: forall (t: ctree E X) (w: World E) (φ: ctlf E X),
      syntails t w φ -> <( t, w |= φ )>.
  Proof with auto with ctl.
    intros.
    induction H.
    - rewrite sb_guard...
    - apply ctl_base...
    - apply ctl_done...
    - apply au_stuck...
    - apply au_ret with w'...
    - apply au_br...
    - apply au_br...
    - apply au_vis_r... 
    - apply au_vis_l...
    - apply au_bind_l...
    - apply au_bind_r with (R:=R)...
    - apply au_iter with Ri Rv...
  Qed.
End SyntacticEntailment.
    
