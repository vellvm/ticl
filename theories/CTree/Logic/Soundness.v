From Stdlib Require Import
  Basics
  Classes.Morphisms.

From TICL Require Import
  Events.WriterE
  CTree.Core
  CTree.Interp.State.Mod
  CTree.Logic.Trans
  CTree.Logic.Bind
  CTree.Logic.Iter
  CTree.Logic.CanStep
  Logic.Core
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.AG
  CTree.Logic.EG
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** * Syntactic entailment proof *)
(** In this section we package the prefix lemmas for all operators [AN, AU, EN, EU, AG, EG]
    into a single inductive relation [syntailsL] that we prove sound with respect to the
    semantic entailment relation [|=]. Visible branching is [BrS c k]/[Step t]; hidden
    branching [Br c k] has no syntactic rule (its lemmas have [ktrans]-level premises).
*)
Section SyntacticEntailment.
  Context {E B: Type -> Type}.

  Inductive syntailsL{X}: ctree E B X -> World E -> ticll E -> Prop :=
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
  | SynBindL: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ w,
      syntailsL t w φ ->
      syntailsL (x <- t ;; k x) w φ
  (* φ AU ψ *)
  | SynAuStuck: forall w φ ψ,
      syntailsL Stuck w ψ ->
      syntailsL Stuck w <( φ AU ψ )>
  | SynAuRetL: forall w φ ψ r,
      syntailsL (Ret r) w ψ ->
      syntailsL (Ret r) w <( φ AU ψ )>
  | SynAuRetR: forall w φ ψ r,
      syntailsL (Ret r) w <( φ AN ψ )> ->
      syntailsL (Ret r) w <( φ AU ψ )>
  | SynAuBrSR: forall w {Y} (c: B Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (BrS c k) w ψ ->
      syntailsL (BrS c k) w <( φ AU ψ )>
  | SynAuBrSL: forall w {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) φ ψ,
      syntailsL (BrS c k) w φ ->
      (forall (y: Y), syntailsL (k y) w <( φ AU ψ )>) ->
      syntailsL (BrS c k) w <( φ AU ψ )>
  | SynAuStepR: forall w t φ ψ,
      syntailsL (Step t) w ψ ->
      syntailsL (Step t) w <( φ AU ψ )>
  | SynAuStepL: forall w t φ ψ,
      syntailsL (Step t) w φ ->
      syntailsL t w <( φ AU ψ )> ->
      syntailsL (Step t) w <( φ AU ψ )>
  | SynAuVisR: forall w {Y} (e: E Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (Vis e k) w ψ ->
      syntailsL (Vis e k) w <( φ AU ψ )>
  | SynAuVisL: forall w {Y} (e: E Y) (k: Y -> ctree E B X) (wit: Y) φ ψ,
      syntailsL (Vis e k) w φ ->
      (forall (v: Y), syntailsL (k v) (Obs e v) <( φ AU ψ )>) ->
      syntailsL (Vis e k) w <( φ AU ψ )>
  | SynAuBindR: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ ψ w R,
      <[ t, w |= φ AU ret R ]> ->
      (forall r w', R r w' -> syntailsL (k r) w' <( φ AU ψ )>) ->
      syntailsL (x <- t ;; k x) w <( φ AU ψ )>
  | SynAuIter: forall {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) φ ψ,
      well_founded Rv ->
      not_done w ->
      Ri i w ->
      (forall (i: I) w,
          not_done w ->
          Ri i w ->
          <( {k i}, w |= φ AU ψ )> \/
            <[ {k i}, w |= φ AU ret
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i'
                                 /\ not_done w'
                                 /\ Ri i' w'
                                 /\ Rv (i', w') (i, w)}]>) ->
      syntailsL (iter k i) w <( φ AU ψ )>
  (* φ EU ψ *)
  | SynEuStuck: forall w φ ψ,
      syntailsL Stuck w ψ ->
      syntailsL Stuck w <( φ EU ψ )>
  | SynEuRetL: forall w φ ψ r,
      syntailsL (Ret r) w ψ ->
      syntailsL (Ret r) w <( φ EU ψ )>
  | SynEuRetR: forall w φ ψ r,
      syntailsL (Ret r) w <( φ EN ψ )> ->
      syntailsL (Ret r) w <( φ EU ψ )>
  | SynEuBrSR: forall w {Y} (c: B Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (BrS c k) w ψ ->
      syntailsL (BrS c k) w <( φ EU ψ )>
  | SynEuBrSL: forall w {Y} (c: B Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (BrS c k) w φ ->
      (exists (y: Y), <( {k y}, w |= φ EU ψ )>) ->
      syntailsL (BrS c k) w <( φ EU ψ )>
  | SynEuStepR: forall w t φ ψ,
      syntailsL (Step t) w ψ ->
      syntailsL (Step t) w <( φ EU ψ )>
  | SynEuStepL: forall w t φ ψ,
      syntailsL (Step t) w φ ->
      syntailsL t w <( φ EU ψ )> ->
      syntailsL (Step t) w <( φ EU ψ )>
  | SynEuVisR: forall w {Y} (e: E Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (Vis e k) w ψ ->
      syntailsL (Vis e k) w <( φ EU ψ )>
  | SynEuVisL: forall w {Y} (e: E Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (Vis e k) w φ ->
      (exists (v: Y), <( {k v}, {Obs e v} |= φ EU ψ )>) ->
      syntailsL (Vis e k) w <( φ EU ψ )>
  | SynEuBindR: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ ψ w R,
      <[ t, w |= φ EU ret R ]> ->
      (forall r w', R r w' -> syntailsL (k r) w' <( φ EU ψ )>) ->
      syntailsL (x <- t ;; k x) w <( φ EU ψ )>
  | SynEuIter: forall {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) φ ψ,
      well_founded Rv ->
      not_done w ->
      Ri i w ->
      (forall (i: I) w,
          not_done w ->
          Ri i w ->
          <( {k i}, w |= φ EU ψ )> \/
            <[ {k i}, w |= φ EU ret
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i'
                                 /\ not_done w'
                                 /\ Ri i' w'
                                 /\ Rv (i', w') (i, w)}]>) ->
      syntailsL (iter k i) w <( φ EU ψ )>
  (* φ AN ψ *)
  | SynAnStuck: forall w φ ψ,
      False ->
      syntailsL Stuck w <( φ AN ψ )>
  | SynAnRetL: forall w φ ψ r,
      False ->
      syntailsL (Ret r) w <( φ AN ψ )>
  | SynAnBrS: forall w {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) φ ψ,
      syntailsL (BrS c k) w φ ->
      (forall (y: Y), syntailsL (k y) w ψ) ->
      syntailsL (BrS c k) w <( φ AN ψ )>
  | SynAnStep: forall w t φ ψ,
      syntailsL (Step t) w φ ->
      syntailsL t w ψ ->
      syntailsL (Step t) w <( φ AN ψ )>
  | SynAnVis: forall w {Y} (e: E Y) (k: Y -> ctree E B X) (wit: Y) φ ψ,
      syntailsL (Vis e k) w φ ->
      (forall (v: Y), syntailsL (k v) (Obs e v) ψ) ->
      syntailsL (Vis e k) w <( φ AN ψ )>
  | SynAnBindR: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ ψ w R,
      <[ t, w |= ret R ]> ->
      (forall r w', R r w' -> syntailsL (k r) w' <( φ AN ψ )>) ->
      syntailsL (x <- t ;; k x) w <( φ AN ψ )>
  | SynAnIter: forall {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) φ ψ,
      well_founded Rv ->
      Ri i w ->
      (forall (i: I) w,
          Ri i w ->
          <( {k i}, w |= φ AN ψ )> \/
            <[ {k i}, w |= ret
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i}]>) ->
      syntailsL (iter k i) w <( φ AN ψ )>
  (* φ EN ψ *)
  | SynEnStuck: forall w φ ψ,
      False ->
      syntailsL Stuck w <( φ EN ψ )>
  | SynEnRetL: forall w φ ψ r,
      False ->
      syntailsL (Ret r) w <( φ EN ψ )>
  | SynEnBrS: forall w {Y} (c: B Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (BrS c k) w φ ->
      (exists (y: Y), <( {k y}, w |= ψ )>) ->
      syntailsL (BrS c k) w <( φ EN ψ )>
  | SynEnStep: forall w t φ ψ,
      syntailsL (Step t) w φ ->
      syntailsL t w ψ ->
      syntailsL (Step t) w <( φ EN ψ )>
  | SynEnVis: forall w {Y} (e: E Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (Vis e k) w φ ->
      (exists (v: Y), <( {k v}, {Obs e v} |= ψ )>) ->
      syntailsL (Vis e k) w <( φ EN ψ )>
  | SynEnBindR: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ ψ w R,
      <[ t, w |= ret R ]> ->
      (forall r w', R r w' -> syntailsL (k r) w' <( φ EN ψ )>) ->
      syntailsL (x <- t ;; k x) w <( φ EN ψ )>
  | SynEnIter: forall {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) φ ψ,
      well_founded Rv ->
      Ri i w ->
      (forall (i: I) w,
          Ri i w ->
          <( {k i}, w |= φ EN ψ )> \/
            <[ {k i}, w |= ret
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i}]>) ->
      syntailsL (iter k i) w <( φ EN ψ )>
  (* AG φ *)
  | SynAgStuck: forall w φ,
      False ->
      syntailsL Stuck w <( AG φ )>
  | SynAgRetL: forall w φ r,
      False ->
      syntailsL (Ret r) w <( AG φ )>
  | SynAgBrS: forall w {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) φ,
      syntailsL (BrS c k) w φ ->
      (forall (y: Y), syntailsL (k y) w <( AG φ )>) ->
      syntailsL (BrS c k) w <( AG φ )>
  | SynAgStep: forall w t φ,
      syntailsL (Step t) w φ ->
      syntailsL t w <( AG φ )> ->
      syntailsL (Step t) w <( AG φ )>
  | SynAgVis: forall w {Y} (e: E Y) (k: Y -> ctree E B X) (wit: Y) φ,
      syntailsL (Vis e k) w φ ->
      (forall (v: Y), syntailsL (k v) (Obs e v) <( AG φ )>) ->
      syntailsL (Vis e k) w <( AG φ )>
  | SynAgBindR: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ w R,
      <[ t, w |= φ AU ret R ]> ->
      (forall r w', R r w' -> syntailsL (k r) w' <( AG φ )>) ->
      syntailsL (x <- t ;; k x) w <( AG φ )>
  | SynAgIter: forall {I} R (i: I) w (k: I -> ctree E B (I + X)) φ,
      R i w ->
      (forall (i: I) w,
          R i w ->
          <( {iter k i}, w |= φ)> /\
            <[ {k i}, w |= AX (φ AU ret
                                 {fun (lr: I + X) (w': World E) =>
                                    exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
      syntailsL (iter k i) w <( AG φ )>
  (* EG φ *)
  | SynEgStuck: forall w φ,
      False ->
      syntailsL Stuck w <( EG φ )>
  | SynEgRetL: forall w φ r,
      False ->
      syntailsL (Ret r) w <( EG φ )>
  | SynEgBrS: forall w {Y} (c: B Y) (k: Y -> ctree E B X) φ,
      syntailsL (BrS c k) w φ ->
      (exists (y: Y), <( {k y}, w |= EG φ )>) ->
      syntailsL (BrS c k) w <( EG φ )>
  | SynEgStep: forall w t φ,
      syntailsL (Step t) w φ ->
      syntailsL t w <( EG φ )> ->
      syntailsL (Step t) w <( EG φ )>
  | SynEgVis: forall w {Y} (e: E Y) (k: Y -> ctree E B X) φ,
      syntailsL (Vis e k) w φ ->
      (exists (v: Y), <( {k v}, {Obs e v} |= EG φ )>) ->
      syntailsL (Vis e k) w <( EG φ )>
  | SynEgBindR: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ w R,
      <[ t, w |= φ EU ret R ]> ->
      (forall r w', R r w' -> syntailsL (k r) w' <( EG φ )>) ->
      syntailsL (x <- t ;; k x) w <( EG φ )>
  | SynEgIter: forall {I} R (i: I) w (k: I -> ctree E B (I + X)) φ,
      R i w ->
      (forall (i: I) w,
          R i w ->
          <( {iter k i}, w |= φ)> /\
            <[ {k i}, w |= EX (φ EU ret
                                 {fun (lr: I + X) (w': World E) =>
                                    exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
      syntailsL (iter k i) w <( EG φ )>.

  Lemma soundnessL{X}: forall (t: ctree E B X) (w: World E) (φ: ticll E),
      syntailsL t w φ -> <( t, w |= φ )>.
  Proof.
    intros.
    induction H.
    - rewrite sb_guard; eauto with ticl.
    - csplit; eauto with ticl.
    - csplit; eauto with ticl.
    - cleft; eauto with ticl.
    - cright; eauto with ticl.
    - apply ticll_bind_l; eauto with ticl.
    - apply aul_stuck; eauto with ticl.
    - apply aul_ret; cleft; eauto with ticl.
    - apply aul_ret; cright; eauto with ticl.
    - cleft; eauto with ticl.
    - apply (aul_brS c k y); right; eauto with ticl.
    - cleft; eauto with ticl.
    - apply aul_step; right; eauto with ticl.
    - cleft; eauto with ticl.
    - apply (aul_vis e k wit); right; eauto with ticl.
    - apply aul_bind_r with (R:=R); eauto with ticl.
    - apply aul_iter with Ri Rv; eauto with ticl.
    - apply eul_stuck; eauto with ticl.
    - apply eul_ret; cleft; eauto with ticl.
    - apply eul_ret; cright; eauto with ticl.
    - cleft; eauto with ticl.
    - apply eul_brS; right; eauto with ticl.
    - cleft; eauto with ticl.
    - apply eul_step; right; eauto with ticl.
    - cleft; eauto with ticl.
    - apply eul_vis; right; eauto with ticl.
    - apply eul_bind_r with R; eauto with ticl.
    - apply eul_iter with Ri Rv; eauto with ticl.
    - contradiction.
    - contradiction.
    - apply (anl_brS c k y); eauto with ticl.
    - apply anl_step; eauto with ticl.
    - apply (anl_vis e k wit); eauto with ticl.
    - apply anl_bind_r with R; eauto with ticl.
    - apply anl_iter with Ri Rv; eauto with ticl.
    - contradiction.
    - contradiction.
    - apply enl_brS; eauto with ticl.
    - apply enl_step; eauto with ticl.
    - apply enl_vis; eauto with ticl.
    - apply enl_bind_r with R; eauto with ticl.
    - apply enl_iter with Ri Rv; eauto with ticl.
    - contradiction.
    - contradiction.
    - rewrite <- (ag_brS c k y); eauto with ticl.
    - rewrite <- ag_step; eauto with ticl.
    - rewrite <- (ag_vis e k wit); eauto with ticl.
    - apply ag_bind_r with R; eauto with ticl.
    - apply ag_iter with R; eauto with ticl.
    - contradiction.
    - contradiction.
    - rewrite <- eg_brS; eauto with ticl.
    - rewrite <- eg_step; eauto with ticl.
    - rewrite <- eg_vis; eauto with ticl.
    - apply eg_bind_r with R; eauto with ticl.
    - apply eg_iter with R; eauto with ticl.
  Qed.

  (** Syntactic entailment for suffix formulas [<[ ]>]. Left premises reuse [syntailsL]. *)
  Inductive syntailsR{X}: ctree E B X -> World E -> ticlr E X -> Prop :=
  | SynRGuard: forall w φ t,
      syntailsR t w φ ->
      syntailsR (Guard t) w φ
  (* The [ret] atom: [Ret x] returns [x], deterministically *)
  | SynRet: forall w (R: rel X (World E)) (x: X),
      R x w ->
      not_done w ->
      syntailsR (Ret x) w <[ ret R ]>
  (* Boolean *)
  | SynRAnd: forall t w φ ψ,
      syntailsR t w φ ->
      syntailsR t w ψ ->
      syntailsR t w <[ φ /\ ψ ]>
  | SynROrL: forall t w φ ψ,
      syntailsR t w φ ->
      syntailsR t w <[ φ \/ ψ ]>
  | SynROrR: forall t w φ ψ,
      syntailsR t w ψ ->
      syntailsR t w <[ φ \/ ψ ]>
  (* φ AU ψ *)
  | SynRAuStuck: forall w φ ψ,
      syntailsR Stuck w ψ ->
      syntailsR Stuck w <[ φ AU ψ ]>
  | SynRAuRetL: forall w φ ψ r,
      syntailsR (Ret r) w ψ ->
      syntailsR (Ret r) w <[ φ AU ψ ]>
  | SynRAuRetR: forall w φ ψ r,
      syntailsR (Ret r) w <[ φ AN ψ ]> ->
      syntailsR (Ret r) w <[ φ AU ψ ]>
  | SynRAuBrSR: forall w {Y} (c: B Y) (k: Y -> ctree E B X) φ ψ,
      syntailsR (BrS c k) w ψ ->
      syntailsR (BrS c k) w <[ φ AU ψ ]>
  | SynRAuBrSL: forall w {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) φ ψ,
      syntailsL (BrS c k) w φ ->
      (forall (y: Y), syntailsR (k y) w <[ φ AU ψ ]>) ->
      syntailsR (BrS c k) w <[ φ AU ψ ]>
  | SynRAuStepR: forall w t φ ψ,
      syntailsR (Step t) w ψ ->
      syntailsR (Step t) w <[ φ AU ψ ]>
  | SynRAuStepL: forall w t φ ψ,
      syntailsL (Step t) w φ ->
      syntailsR t w <[ φ AU ψ ]> ->
      syntailsR (Step t) w <[ φ AU ψ ]>
  | SynRAuVisR: forall w {Y} (e: E Y) (k: Y -> ctree E B X) φ ψ,
      syntailsR (Vis e k) w ψ ->
      syntailsR (Vis e k) w <[ φ AU ψ ]>
  | SynRAuVisL: forall w {Y} (e: E Y) (k: Y -> ctree E B X) (wit: Y) φ ψ,
      syntailsL (Vis e k) w φ ->
      (forall (v: Y), syntailsR (k v) (Obs e v) <[ φ AU ψ ]>) ->
      syntailsR (Vis e k) w <[ φ AU ψ ]>
  | SynRAuBindR: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ ψ w R,
      <[ t, w |= φ AU ret R ]> ->
      (forall r w', R r w' -> syntailsR (k r) w' <[ φ AU ψ ]>) ->
      syntailsR (x <- t ;; k x) w <[ φ AU ψ ]>
  | SynRAuIter: forall {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) φ ψ,
      well_founded Rv ->
      Ri i w ->
      (forall (i: I) w,
          Ri i w ->
          <[ {k i}, w |= φ AU ret
                      {fun (lr: I + X) (w': World E) =>
                         match lr with
                         | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                         | inr r => <[ {Ret r: ctree E B X}, w' |= ψ ]>
                         end} ]>) ->
      syntailsR (iter k i) w <[ φ AU ψ ]>
  (* φ EU ψ *)
  | SynREuStuck: forall w φ ψ,
      syntailsR Stuck w ψ ->
      syntailsR Stuck w <[ φ EU ψ ]>
  | SynREuRetL: forall w φ ψ r,
      syntailsR (Ret r) w ψ ->
      syntailsR (Ret r) w <[ φ EU ψ ]>
  | SynREuRetR: forall w φ ψ r,
      syntailsR (Ret r) w <[ φ EN ψ ]> ->
      syntailsR (Ret r) w <[ φ EU ψ ]>
  | SynREuBrSR: forall w {Y} (c: B Y) (k: Y -> ctree E B X) φ ψ,
      syntailsR (BrS c k) w ψ ->
      syntailsR (BrS c k) w <[ φ EU ψ ]>
  | SynREuBrSL: forall w {Y} (c: B Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (BrS c k) w φ ->
      (exists (y: Y), <[ {k y}, w |= φ EU ψ ]>) ->
      syntailsR (BrS c k) w <[ φ EU ψ ]>
  | SynREuStepR: forall w t φ ψ,
      syntailsR (Step t) w ψ ->
      syntailsR (Step t) w <[ φ EU ψ ]>
  | SynREuStepL: forall w t φ ψ,
      syntailsL (Step t) w φ ->
      syntailsR t w <[ φ EU ψ ]> ->
      syntailsR (Step t) w <[ φ EU ψ ]>
  | SynREuVisR: forall w {Y} (e: E Y) (k: Y -> ctree E B X) φ ψ,
      syntailsR (Vis e k) w ψ ->
      syntailsR (Vis e k) w <[ φ EU ψ ]>
  | SynREuVisL: forall w {Y} (e: E Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (Vis e k) w φ ->
      (exists (v: Y), <[ {k v}, {Obs e v} |= φ EU ψ ]>) ->
      syntailsR (Vis e k) w <[ φ EU ψ ]>
  | SynREuBindR: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ ψ w R,
      <[ t, w |= φ EU ret R ]> ->
      (forall r w', R r w' -> syntailsR (k r) w' <[ φ EU ψ ]>) ->
      syntailsR (x <- t ;; k x) w <[ φ EU ψ ]>
  | SynREuIter: forall {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) φ ψ,
      well_founded Rv ->
      Ri i w ->
      not_done w ->
      (forall (i: I) w,
          Ri i w ->
          not_done w ->
          <[ {k i}, w |= φ EU ret
                      {fun (lr: I + X) (w': World E) =>
                         match lr with
                         | inl i' => not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)
                         | inr r => <[ {Ret r: ctree E B X}, w' |= ψ ]>
                         end} ]>) ->
      syntailsR (iter k i) w <[ φ EU ψ ]>
  (* φ AN ψ *)
  | SynRAnStuck: forall w φ ψ,
      False ->
      syntailsR Stuck w <[ φ AN ψ ]>
  | SynRAnBrS: forall w {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) φ ψ,
      syntailsL (BrS c k) w φ ->
      (forall (y: Y), syntailsR (k y) w ψ) ->
      syntailsR (BrS c k) w <[ φ AN ψ ]>
  | SynRAnStep: forall w t φ ψ,
      syntailsL (Step t) w φ ->
      syntailsR t w ψ ->
      syntailsR (Step t) w <[ φ AN ψ ]>
  | SynRAnVis: forall w {Y} (e: E Y) (k: Y -> ctree E B X) (wit: Y) φ ψ,
      syntailsL (Vis e k) w φ ->
      (forall (v: Y), syntailsR (k v) (Obs e v) ψ) ->
      syntailsR (Vis e k) w <[ φ AN ψ ]>
  | SynRAnBindL: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ ψ w R,
      <[ t, w |= φ AN ret R ]> ->
      (forall r w', R r w' -> syntailsR (k r) w' ψ) ->
      syntailsR (x <- t ;; k x) w <[ φ AN ψ ]>
  | SynRAnBindR: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ ψ w R,
      <[ t, w |= ret R ]> ->
      (forall r w', R r w' -> syntailsR (k r) w' <[ φ AN ψ ]>) ->
      syntailsR (x <- t ;; k x) w <[ φ AN ψ ]>
  (* φ EN ψ *)
  | SynREnStuck: forall w φ ψ,
      False ->
      syntailsR Stuck w <[ φ EN ψ ]>
  | SynREnBrS: forall w {Y} (c: B Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (BrS c k) w φ ->
      (exists (y: Y), <[ {k y}, w |= ψ ]>) ->
      syntailsR (BrS c k) w <[ φ EN ψ ]>
  | SynREnStep: forall w t φ ψ,
      syntailsL (Step t) w φ ->
      syntailsR t w ψ ->
      syntailsR (Step t) w <[ φ EN ψ ]>
  | SynREnVis: forall w {Y} (e: E Y) (k: Y -> ctree E B X) φ ψ,
      syntailsL (Vis e k) w φ ->
      (exists (v: Y), <[ {k v}, {Obs e v} |= ψ ]>) ->
      syntailsR (Vis e k) w <[ φ EN ψ ]>
  | SynREnBindR: forall {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ ψ w R,
      <[ t, w |= ret R ]> ->
      (forall r w', R r w' -> syntailsR (k r) w' <[ φ EN ψ ]>) ->
      syntailsR (x <- t ;; k x) w <[ φ EN ψ ]>.

  Lemma soundnessR{X}: forall (t: ctree E B X) (w: World E) (φ: ticlr E X),
      syntailsR t w φ -> <[ t, w |= φ ]>.
  Proof.
    intros.
    induction H.
    - rewrite sb_guard; eauto with ticl.
    - apply ret_ret; eauto with ticl.
    - csplit; eauto with ticl.
    - cleft; eauto with ticl.
    - cright; eauto with ticl.
    - apply aur_stuck; eauto with ticl.
    - apply aur_ret; cleft; eauto with ticl.
    - apply aur_ret; cright; eauto with ticl.
    - cleft; eauto with ticl.
    - apply (aur_brS c k y); right; split; auto; now apply soundnessL.
    - cleft; eauto with ticl.
    - apply aur_step; right; split; auto; now apply soundnessL.
    - cleft; eauto with ticl.
    - apply (aur_vis e k wit); right; split; auto; now apply soundnessL.
    - apply aur_bind_r with (R:=R); eauto with ticl.
    - apply aur_iter with Ri Rv; eauto with ticl.
    - apply eur_stuck; eauto with ticl.
    - apply eur_ret; cleft; eauto with ticl.
    - apply eur_ret; cright; eauto with ticl.
    - cleft; eauto with ticl.
    - apply eur_brS; right; split; auto; now apply soundnessL.
    - cleft; eauto with ticl.
    - apply eur_step; right; split; auto; now apply soundnessL.
    - cleft; eauto with ticl.
    - apply eur_vis; right; split; auto; now apply soundnessL.
    - apply eur_bind_r with R; eauto with ticl.
    - apply eur_iter with Ri Rv; eauto with ticl.
    - contradiction.
    - apply (anr_brS c k y); split; auto; now apply soundnessL.
    - apply anr_step; split; auto; now apply soundnessL.
    - apply (anr_vis e k wit); split; auto; now apply soundnessL.
    - apply anr_bind_l with R; eauto with ticl.
    - apply anr_bind_r with R; eauto with ticl.
    - contradiction.
    - apply enr_brS; split; auto; now apply soundnessL.
    - apply enr_step; split; auto; now apply soundnessL.
    - apply enr_vis; split; auto; now apply soundnessL.
    - apply enr_bind_r with R; eauto with ticl.
  Qed.

End SyntacticEntailment.
