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
  CTree.Logic.Bind
  CTree.Logic.Iter
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.AX
  Logic.AF
  Logic.EX
  Logic.EF
  Logic.AG
  Logic.EG
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.

Section SyntacticEntailment.
  Context {E: Type} {HE: Encode E}.

  Inductive syntailsL{X}: ctree E X -> World E -> ctll E -> Prop :=
  (* All formulas are invariant to [Guard] *)
  | SynGuard: forall w φ t,
      syntailsL t w φ ->
      syntailsL (Guard t) w φ
  (* Base predicate *)
  | SynNow: forall w φ t,
      φ w ->
      not_done w ->
      syntailsL t w <( now φ )>
  (* Boolean *)
  | SynAnd: forall t w φ ψ,
      syntailsL t w φ ->
      syntailsL t w ψ ->
      syntailsL t w <( φ /\ ψ )>
  | SynOrL: forall t w φ ψ,
      syntailsL t w φ ->
      syntailsL t w <( φ \/ ψ )>
  | SynOrR: forall t w φ ψ,
      syntailsL t w ψ ->
      syntailsL t w <( φ \/ ψ )>
  (* BindL *)
  | SynBindL: forall {Y} (t: ctree E Y) (k: Y -> ctree E X) φ w,
      syntailsL t w φ ->
      syntailsL (x <- t ;; k x) w φ
  (* ψ AU φ *)
  | SynAuStuck: forall w φ ψ,
    syntailsL (Ctree.stuck) w ψ ->
    syntailsL (Ctree.stuck) w <( φ AU ψ )>
  | SynAuRetL: forall w φ ψ r,
      syntailsL (Ret r) w <( ψ )> ->
      syntailsL (Ret r) w <( φ AU ψ )>
  | SynAuRetR: forall w φ ψ r,
      syntailsL (Ret r) w <( φ AN ψ )> ->
      syntailsL (Ret r) w <( φ AU ψ )>
  | SynAuBrR: forall w n (k: fin' n -> _) φ ψ,
      not_done w ->
      syntailsL (Br n k) w ψ ->
      syntailsL (Br n k) w <( φ AU ψ )>
  | SynAuBrL: forall w n (k: fin' n -> _) φ ψ,
      not_done w ->
      syntailsL (Br n k) w φ ->
      (forall (i: fin' n), syntailsL (k i) w <( φ AU ψ )>) ->
      syntailsL (Br n k) w <( φ AU ψ )>
  | SynAuVisR: forall w (e: E) (k: encode e -> _) (wit: encode e) φ ψ,
      not_done w ->
      syntailsL (Vis e k) w ψ ->
      syntailsL (Vis e k) w <( φ AU ψ )>
  | SynAuVisL: forall w (e: E) (k: encode e -> _) (wit: encode e) φ ψ,
      not_done w ->
      syntailsL (Vis e k) w φ ->
      (forall (x: encode e), syntailsL (k x) (Obs e x) <( φ AU ψ )>) ->
      syntailsL (Vis e k) w <( ψ AU φ )>
  | SynAuBindR: forall {Y} (t: ctree E Y) (k: Y -> ctree E X) φ ψ w R,
      <[ t, w |= φ AU AX done R ]> ->
      (forall r w', R r w' -> syntailsL (k r)  w' <( φ AU ψ )>) ->
      syntailsL (x <- t ;; k x) w <( φ AU ψ )>
  | SynAuIter: forall {I} Ri Rv (i: I) w (k: I -> ctree E (I + X)) φ ψ,
      well_founded Rv ->
      not_done w ->
      Ri i w ->
      (forall (i: I) w,
          not_done w ->
          Ri i w ->
          <( {k i}, w |= φ AU ψ )> \/
            <[ {k i}, w |= φ AU AX done
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i'
                                 /\ not_done w'
                                 /\ Ri i' w'
                                 /\ Rv (i', w') (i, w)}]>) ->
      syntailsL (iter k i) w <( φ AU ψ )>
  (* φ EU ψ *)
  | SynEuStuck: forall w φ ψ,
      syntailsL (Ctree.stuck) w ψ ->
      syntailsL (Ctree.stuck) w <( φ EU ψ )>
  | SynEuRetL: forall w φ ψ r,
      syntailsL (Ret r) w <( ψ )> ->
      syntailsL (Ret r) w <( φ EU ψ )>
  | SynEuRetR: forall w φ ψ r,
      syntailsL (Ret r) w <( φ EN ψ )> ->
      syntailsL (Ret r) w <( φ EU ψ )>
  | SynEuBrR: forall w n (k: fin' n -> _) φ ψ,
      not_done w ->
      syntailsL (Br n k) w ψ ->
      syntailsL (Br n k) w <( φ EU ψ )>
  | SynEuBrL: forall w n (k: fin' n -> _) φ ψ,
      not_done w ->
      syntailsL (Br n k) w φ ->
      (exists (i: fin' n), <( {k i}, w |= φ EU ψ )>) ->
      syntailsL (Br n k) w <( φ EU ψ )>
  | SynEuVisR: forall w (e: E) (k: encode e -> _) (wit: encode e) φ ψ,
      not_done w ->
      syntailsL (Vis e k) w ψ ->
      syntailsL (Vis e k) w <( φ EU ψ )>
  | SynEuVisL: forall w (e: E) (k: encode e -> _) φ ψ,
      not_done w ->
      syntailsL (Vis e k) w φ ->
      (exists (x: encode e), <( {k x}, {Obs e x} |= φ EU ψ )>) ->
      syntailsL (Vis e k) w <( φ EU ψ )>
  | SynEuBindR: forall {Y} (t: ctree E Y) (k: Y -> ctree E X) φ ψ w R,
      <[ t, w |= φ EU EX done R ]> ->
      (forall r w', R r w' -> syntailsL (k r)  w' <( φ EU ψ )>) ->
      syntailsL (x <- t ;; k x) w <( φ EU ψ )>
  | SynEuIter: forall {I} Ri Rv (i: I) w (k: I -> ctree E (I + X)) φ ψ,
      well_founded Rv ->
      not_done w ->
      Ri i w ->
      (forall (i: I) w,
          not_done w ->
          Ri i w ->
          <( {k i}, w |= φ EU ψ )> \/
            <[ {k i}, w |= φ EU EX done
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i'
                                 /\ not_done w'
                                 /\ Ri i' w'
                                 /\ Rv (i', w') (i, w)}]>) ->
      syntailsL (iter k i) w <( φ EU ψ )>
  (* ψ AN φ *)
  | SynAnStuck: forall w φ ψ,
      False ->
      syntailsL (Ctree.stuck) w <( φ AN ψ )>
  | SynAnRetL: forall w φ ψ r,
      False ->
      syntailsL (Ret r) w <( φ AN ψ )>
  | SynAnBr: forall w n (k: fin' n -> _) φ ψ,
      not_done w ->
      syntailsL (Br n k) w φ ->
      (forall (i: fin' n), syntailsL (k i) w ψ) ->
      syntailsL (Br n k) w <( φ AN ψ )>
  | SynAnVisR: forall w (e: E) (k: encode e -> _) (wit: encode e) φ ψ,
      not_done w ->
      syntailsL (Vis e k) w φ ->
      (forall (x: encode e), syntailsL (k x) (Obs e x) ψ) ->
      syntailsL (Vis e k) w <( φ AN ψ )>
  | SynAnBindR: forall {Y} (t: ctree E Y) (k: Y -> ctree E X) φ ψ w R,
      <[ t, w |= φ AN done R ]> ->
      (forall r w', R r w' -> syntailsL (k r)  w' <( φ AN ψ )>) ->
      syntailsL (x <- t ;; k x) w <( φ AN ψ )>
  | SynAnIter: forall {I} Ri Rv (i: I) w (k: I -> ctree E (I + X)) φ ψ,
      well_founded Rv ->
      Ri i w ->
      (forall (i: I) w,
          Ri i w ->
          <( {k i}, w |= φ AN ψ )> \/
            <[ {k i}, w |= φ AN done
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i}]>) ->
      syntailsL (iter k i) w <( φ AN ψ )>
  (* ψ EN φ *)
  | SynEnStuck: forall w φ ψ,
      False ->
      syntailsL (Ctree.stuck) w <( φ EN ψ )>
  | SynEnRetL: forall w φ ψ r,
      False ->
      syntailsL (Ret r) w <( φ EN ψ )>
  | SynEnBr: forall w n (k: fin' n -> _) φ ψ,
      not_done w ->
      syntailsL (Br n k) w φ ->
      (exists (i: fin' n), <( {k i}, w |=  ψ )>) ->
      syntailsL (Br n k) w <( φ EN ψ )>
  | SynEnVisR: forall w (e: E) (k: encode e -> _) φ ψ,
      not_done w ->
      syntailsL (Vis e k) w φ ->
      (exists (x: encode e), <( {k x}, {Obs e x} |= ψ )>) ->
      syntailsL (Vis e k) w <( φ EN ψ )>
  | SynEnBindR: forall {Y} (t: ctree E Y) (k: Y -> ctree E X) φ ψ w R,
      <[ t, w |= φ EN done R ]> ->
      (forall r w', R r w' -> syntailsL (k r)  w' <( φ EN ψ )>) ->
      syntailsL (x <- t ;; k x) w <( φ EN ψ )>
  | SynEnIter: forall {I} Ri Rv (i: I) w (k: I -> ctree E (I + X)) φ ψ,
      well_founded Rv ->
      Ri i w ->
      (forall (i: I) w,
          Ri i w ->
          <( {k i}, w |= φ EN ψ )> \/
            <[ {k i}, w |= φ EN done
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i}]>) ->
      syntailsL (iter k i) w <( φ EN ψ )>
  (* AG φ *)
  | SynAgStuck: forall w φ,
      False ->
      syntailsL (Ctree.stuck) w <( AG φ )>
  | SynAgRetL: forall w φ r,
      False ->
      syntailsL (Ret r) w <( AG φ )>
  | SynAgBr: forall w n (k: fin' n -> _) φ,
      not_done w ->
      syntailsL (Br n k) w φ ->
      (forall (i: fin' n), syntailsL (k i) w <( AG φ )>) ->
      syntailsL (Br n k) w <( AG φ )>
  | SynAgVisR: forall w (e: E) (k: encode e -> _) (wit: encode e) φ,
      not_done w ->
      syntailsL (Vis e k) w φ ->
      (forall (x: encode e), syntailsL (k x) (Obs e x) <( AG φ )>) ->
      syntailsL (Vis e k) w <( AG φ )>
  | SynAgBindR: forall {Y} (t: ctree E Y) (k: Y -> ctree E X) φ w R,
      <[ t, w |= φ AU AX done R ]> ->
      (forall r w', R r w' -> syntailsL (k r)  w' <( AG φ )>) ->
      syntailsL (x <- t ;; k x) w <( AG φ )>
  | SynAgIter: forall {I} R (i: I) w (k: I -> ctree E (I + X)) φ,
      R i w ->
      (forall (i: I) w,
          R i w ->
          <( {iter k i}, w |= φ)> /\
            <[ {k i}, w |= AX (φ AU AX done
                                 {fun (lr: I + X) (w': World E) =>
                                    exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
      syntailsL (iter k i) w <( AG φ )>
  (* EG φ *)
  | SynEgStuck: forall w φ,
      False ->
      syntailsL (Ctree.stuck) w <( EG φ )>
  | SynEgRetL: forall w φ r,
      False ->
      syntailsL (Ret r) w <( EG φ )>
  | SynEgBr: forall w n (k: fin' n -> _) φ,
      not_done w ->
      syntailsL (Br n k) w φ ->
      (exists (i: fin' n), <( {k i}, w |= EG φ )>) ->
      syntailsL (Br n k) w <( EG φ )>
  | SynEgVisR: forall w (e: E) (k: encode e -> _) (wit: encode e) φ,
      not_done w ->
      syntailsL (Vis e k) w φ ->
      (exists (x: encode e), <( {k x}, {Obs e x} |= EG φ )>) ->
      syntailsL (Vis e k) w <( EG φ )>
  | SynEgBindR: forall {Y} (t: ctree E Y) (k: Y -> ctree E X) φ w R,
      <[ t, w |= φ EU EX done R ]> ->
      (forall r w', R r w' -> syntailsL (k r)  w' <( EG φ )>) ->
      syntailsL (x <- t ;; k x) w <( EG φ )>
  | SynEgIter: forall {I} R (i: I) w (k: I -> ctree E (I + X)) φ,
      R i w ->
      (forall (i: I) w,
          R i w ->
          <( {iter k i}, w |= φ)> /\
            <[ {k i}, w |= EX (φ EU EX done
                                 {fun (lr: I + X) (w': World E) =>
                                    exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
      syntailsL (iter k i) w <( EG φ )>.

  Lemma soundnessL{X}: forall (t: ctree E X) (w: World E) (φ: ctll E),
      syntailsL t w φ -> <( t, w |= φ )>.
  Proof with eauto with ctl.
    intros.
    induction H.
    - rewrite sb_guard...
    - csplit...
    - csplit...
    - cleft...
    - cright...
    - apply ctll_bind_l...
    - apply aul_stuck...
    - apply aul_ret; cleft...
    - apply aul_ret; cright...
    - apply aul_br...
    - apply aul_br...
    - apply aul_vis...
    - apply aul_vis...
    - apply aul_bind_r with (R:=R)...
    - apply aul_iter with Ri Rv...
    - apply eul_stuck...
    - apply eul_ret; cleft...
    - apply eul_ret; cright...
    - apply eul_br...
    - apply eul_br...
    - apply eul_vis...
    - destruct H1; apply eul_vis...
    - apply eul_bind_r with R...
    - apply eul_iter with Ri Rv...
    - contradiction.
    - contradiction.
    - apply anl_br...
    - apply anl_vis...
    - apply anl_bind_r with R...
    - apply anl_iter with Ri Rv...
    - contradiction.
    - contradiction.
    - apply enl_br...
    - destruct H1; apply enl_vis...
    - apply enl_bind_r with R...
    - apply enl_iter with Ri Rv...
    - contradiction.
    - contradiction.
    - rewrite <- ag_br...
    - rewrite <- ag_vis...
    - apply ag_bind_r with R...
    - apply ag_iter with R...
    - contradiction.
    - contradiction.
    - rewrite <- eg_br...
    - rewrite <- eg_vis...
    - apply eg_bind_r with R...
    - apply eg_iter with R...
  Qed.

End SyntacticEntailment.

