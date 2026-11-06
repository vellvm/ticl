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

(** * Syntactic entailment and soundness
    A single indexed derivation family shares prefix guards and indexed targets.
    Visible branching has structural rules; hidden branching is handled only by
    transition-level semantic lemmas. *)
Section SyntacticEntailment.
  Context {E B: Type -> Type}.

  Unset Implicit Arguments.
  Inductive syntails : forall (X: Type) (b: bool),
      ctree E B X -> World E -> ticl_at E X b -> Prop :=
  | SynGuard: forall {X b} w (φ: ticl_at E X b) t,
      syntails X b t w φ ->
      syntails X b (Guard t) w φ
  | SynNow: forall {X} w φ t,
      φ w ->
      not_done w ->
      syntails X false t w <( now φ )>
  | SynRet: forall {X} w (R: rel X (World E)) (x: X),
      R x w ->
      not_done w ->
      syntails X true (Ret x) w <( ret R )>
  | SynAnd: forall {X b} t w (φ ψ: ticl_at E X b),
      syntails X b t w φ ->
      syntails X b t w ψ ->
      syntails X b t w <( φ /\ ψ )>
  | SynOrL: forall {X b} t w (φ ψ: ticl_at E X b),
      syntails X b t w φ ->
      syntails X b t w <( φ \/ ψ )>
  | SynOrR: forall {X b} t w (φ ψ: ticl_at E X b),
      syntails X b t w ψ ->
      syntails X b t w <( φ \/ ψ )>
  | SynBindL: forall {X} {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ w,
      syntails Y false t w φ ->
      syntails X false (x <- t ;; k x) w φ
  | SynAuStuck: forall {X b} w (φ: ticll E) (ψ: ticl_at E X b),
      syntails X b Stuck w ψ ->
      syntails X b Stuck w <( φ AU ψ )>
  | SynAuRetL: forall {X b} w (φ: ticll E) (ψ: ticl_at E X b) r,
      syntails X b (Ret r) w ψ ->
      syntails X b (Ret r) w <( φ AU ψ )>
  | SynAuRetR: forall {X b} w (φ: ticll E) (ψ: ticl_at E X b) r,
      syntails X b (Ret r) w <( φ AN ψ )> ->
      syntails X b (Ret r) w <( φ AU ψ )>
  | SynAuBrSR: forall {X b} w {Y} (c: B Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X b (BrS c k) w ψ ->
      syntails X b (BrS c k) w <( φ AU ψ )>
  | SynAuBrSL: forall {X b} w {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (BrS c k) w φ ->
      (forall (y: Y), syntails X b (k y) w <( φ AU ψ )>) ->
      syntails X b (BrS c k) w <( φ AU ψ )>
  | SynAuStepR: forall {X b} w t (φ: ticll E) (ψ: ticl_at E X b),
      syntails X b (Step t) w ψ ->
      syntails X b (Step t) w <( φ AU ψ )>
  | SynAuStepL: forall {X b} w t (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (Step t) w φ ->
      syntails X b t w <( φ AU ψ )> ->
      syntails X b (Step t) w <( φ AU ψ )>
  | SynAuVisR: forall {X b} w {Y} (e: E Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X b (Vis e k) w ψ ->
      syntails X b (Vis e k) w <( φ AU ψ )>
  | SynAuVisL: forall {X b} w {Y} (e: E Y) (k: Y -> ctree E B X) (wit: Y) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (Vis e k) w φ ->
      (forall (v: Y), syntails X b (k v) (Obs e v) <( φ AU ψ )>) ->
      syntails X b (Vis e k) w <( φ AU ψ )>
  | SynAuBindR: forall {X b} {Y} (t: ctree E B Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b) w R,
      entails Y true (Cu Q_A φ (CRet R)) t w ->
      (forall r w', R r w' -> syntails X b (k r) w' <( φ AU ψ )>) ->
      syntails X b (x <- t ;; k x) w <( φ AU ψ )>
  | SynAuIterPrefix: forall {X} {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) (φ ψ: ticll E),
      well_founded Rv ->
      not_done w ->
      Ri i w ->
      (forall (i: I) w,
          not_done w ->
          Ri i w ->
          entails (I + X) false <( φ AU ψ )> (k i) (w) \/
            entails (I + X) true <( φ AU ret
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i'
                                 /\ not_done w'
                                 /\ Ri i' w'
                                 /\ Rv (i', w') (i, w)} )> (k i) (w)) ->
      syntails X false (iter k i) w <( φ AU ψ )>
  | SynAuIter: forall {X b} {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E) (ψ: ticl_at E X b),
      well_founded Rv ->
      Ri i w ->
      (forall (i: I) w,
          Ri i w ->
          entails (I + X) true <( φ AU ret
                      {fun (lr: I + X) (w': World E) =>
                         match lr with
                         | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                         | inr r => entails X b ψ (Ret r : ctree E B X) w'
                         end} )> (k i) (w)) ->
      syntails X b (iter k i) w <( φ AU ψ )>
  | SynEuStuck: forall {X b} w (φ: ticll E) (ψ: ticl_at E X b),
      syntails X b Stuck w ψ ->
      syntails X b Stuck w <( φ EU ψ )>
  | SynEuRetL: forall {X b} w (φ: ticll E) (ψ: ticl_at E X b) r,
      syntails X b (Ret r) w ψ ->
      syntails X b (Ret r) w <( φ EU ψ )>
  | SynEuRetR: forall {X b} w (φ: ticll E) (ψ: ticl_at E X b) r,
      syntails X b (Ret r) w <( φ EN ψ )> ->
      syntails X b (Ret r) w <( φ EU ψ )>
  | SynEuBrSR: forall {X b} w {Y} (c: B Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X b (BrS c k) w ψ ->
      syntails X b (BrS c k) w <( φ EU ψ )>
  | SynEuBrSL: forall {X b} w {Y} (c: B Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (BrS c k) w φ ->
      (exists (y: Y), entails X b <( φ EU ψ )> (k y) (w)) ->
      syntails X b (BrS c k) w <( φ EU ψ )>
  | SynEuStepR: forall {X b} w t (φ: ticll E) (ψ: ticl_at E X b),
      syntails X b (Step t) w ψ ->
      syntails X b (Step t) w <( φ EU ψ )>
  | SynEuStepL: forall {X b} w t (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (Step t) w φ ->
      syntails X b t w <( φ EU ψ )> ->
      syntails X b (Step t) w <( φ EU ψ )>
  | SynEuVisR: forall {X b} w {Y} (e: E Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X b (Vis e k) w ψ ->
      syntails X b (Vis e k) w <( φ EU ψ )>
  | SynEuVisL: forall {X b} w {Y} (e: E Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (Vis e k) w φ ->
      (exists (v: Y), entails X b <( φ EU ψ )> (k v) (Obs e v)) ->
      syntails X b (Vis e k) w <( φ EU ψ )>
  | SynEuBindR: forall {X b} {Y} (t: ctree E B Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b) w R,
      entails Y true (Cu Q_E φ (CRet R)) t w ->
      (forall r w', R r w' -> syntails X b (k r) w' <( φ EU ψ )>) ->
      syntails X b (x <- t ;; k x) w <( φ EU ψ )>
  | SynEuIterPrefix: forall {X} {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) (φ ψ: ticll E),
      well_founded Rv ->
      not_done w ->
      Ri i w ->
      (forall (i: I) w,
          not_done w ->
          Ri i w ->
          entails (I + X) false <( φ EU ψ )> (k i) (w) \/
            entails (I + X) true <( φ EU ret
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i'
                                 /\ not_done w'
                                 /\ Ri i' w'
                                 /\ Rv (i', w') (i, w)} )> (k i) (w)) ->
      syntails X false (iter k i) w <( φ EU ψ )>
  | SynEuIter: forall {X b} {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E) (ψ: ticl_at E X b),
      well_founded Rv ->
      Ri i w ->
      not_done w ->
      (forall (i: I) w,
          Ri i w ->
          not_done w ->
          entails (I + X) true <( φ EU ret
                      {fun (lr: I + X) (w': World E) =>
                         match lr with
                         | inl i' => not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)
                         | inr r => entails X b ψ (Ret r : ctree E B X) w'
                         end} )> (k i) (w)) ->
      syntails X b (iter k i) w <( φ EU ψ )>
  | SynAnBrS: forall {X b} w {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (BrS c k) w φ ->
      (forall (y: Y), syntails X b (k y) w ψ) ->
      syntails X b (BrS c k) w <( φ AN ψ )>
  | SynAnStep: forall {X b} w t (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (Step t) w φ ->
      syntails X b t w ψ ->
      syntails X b (Step t) w <( φ AN ψ )>
  | SynAnVis: forall {X b} w {Y} (e: E Y) (k: Y -> ctree E B X) (wit: Y) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (Vis e k) w φ ->
      (forall (v: Y), syntails X b (k v) (Obs e v) ψ) ->
      syntails X b (Vis e k) w <( φ AN ψ )>
  | SynAnBindL: forall {X b} {Y} (t: ctree E B Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b) w R,
      entails Y true (Cx Q_A φ (CRet R)) t w ->
      (forall r w', R r w' -> syntails X b (k r) w' ψ) ->
      syntails X b (x <- t ;; k x) w <( φ AN ψ )>
  | SynAnBindR: forall {X b} {Y} (t: ctree E B Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b) w R,
      entails Y true (CRet R) t w ->
      (forall r w', R r w' -> syntails X b (k r) w' <( φ AN ψ )>) ->
      syntails X b (x <- t ;; k x) w <( φ AN ψ )>
  | SynAnIter: forall {X} {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) (φ ψ: ticll E),
      well_founded Rv ->
      Ri i w ->
      (forall (i: I) w,
          Ri i w ->
          entails (I + X) false <( φ AN ψ )> (k i) (w) \/
            entails (I + X) true <( ret
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i} )> (k i) (w)) ->
      syntails X false (iter k i) w <( φ AN ψ )>
  | SynEnBrS: forall {X b} w {Y} (c: B Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (BrS c k) w φ ->
      (exists (y: Y), entails X b <( ψ )> (k y) (w)) ->
      syntails X b (BrS c k) w <( φ EN ψ )>
  | SynEnStep: forall {X b} w t (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (Step t) w φ ->
      syntails X b t w ψ ->
      syntails X b (Step t) w <( φ EN ψ )>
  | SynEnVis: forall {X b} w {Y} (e: E Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b),
      syntails X false (Vis e k) w φ ->
      (exists (v: Y), entails X b <( ψ )> (k v) (Obs e v)) ->
      syntails X b (Vis e k) w <( φ EN ψ )>
  | SynEnBindR: forall {X b} {Y} (t: ctree E B Y) (k: Y -> ctree E B X) (φ: ticll E) (ψ: ticl_at E X b) w R,
      entails Y true (CRet R) t w ->
      (forall r w', R r w' -> syntails X b (k r) w' <( φ EN ψ )>) ->
      syntails X b (x <- t ;; k x) w <( φ EN ψ )>
  | SynEnIter: forall {X} {I} Ri Rv (i: I) w (k: I -> ctree E B (I + X)) (φ ψ: ticll E),
      well_founded Rv ->
      Ri i w ->
      (forall (i: I) w,
          Ri i w ->
          entails (I + X) false <( φ EN ψ )> (k i) (w) \/
            entails (I + X) true <( ret
                        {fun (lr: I + X) (w': World E) =>
                           exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i} )> (k i) (w)) ->
      syntails X false (iter k i) w <( φ EN ψ )>
  | SynAgBrS: forall {X} w {Y} (c: B Y) (k: Y -> ctree E B X) (y: Y) φ,
      syntails X false (BrS c k) w φ ->
      (forall (y: Y), syntails X false (k y) w <( AG φ )>) ->
      syntails X false (BrS c k) w <( AG φ )>
  | SynAgStep: forall {X} w t φ,
      syntails X false (Step t) w φ ->
      syntails X false t w <( AG φ )> ->
      syntails X false (Step t) w <( AG φ )>
  | SynAgVis: forall {X} w {Y} (e: E Y) (k: Y -> ctree E B X) (wit: Y) φ,
      syntails X false (Vis e k) w φ ->
      (forall (v: Y), syntails X false (k v) (Obs e v) <( AG φ )>) ->
      syntails X false (Vis e k) w <( AG φ )>
  | SynAgBindR: forall {X} {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ w R,
      entails Y true (Cu Q_A φ (CRet R)) t w ->
      (forall r w', R r w' -> syntails X false (k r) w' <( AG φ )>) ->
      syntails X false (x <- t ;; k x) w <( AG φ )>
  | SynAgIter: forall {X} {I} R (i: I) w (k: I -> ctree E B (I + X)) φ,
      R i w ->
      (forall (i: I) w,
          R i w ->
          entails X false <( φ )> (iter k i) (w) /\
            entails (I + X) true <( AX (φ AU ret
                                 {fun (lr: I + X) (w': World E) =>
                                    exists (i': I), lr = inl i' /\ R i' w'}) )> (k i) (w)) ->
      syntails X false (iter k i) w <( AG φ )>
  | SynEgBrS: forall {X} w {Y} (c: B Y) (k: Y -> ctree E B X) φ,
      syntails X false (BrS c k) w φ ->
      (exists (y: Y), entails X false <( EG φ )> (k y) (w)) ->
      syntails X false (BrS c k) w <( EG φ )>
  | SynEgStep: forall {X} w t φ,
      syntails X false (Step t) w φ ->
      syntails X false t w <( EG φ )> ->
      syntails X false (Step t) w <( EG φ )>
  | SynEgVis: forall {X} w {Y} (e: E Y) (k: Y -> ctree E B X) φ,
      syntails X false (Vis e k) w φ ->
      (exists (v: Y), entails X false <( EG φ )> (k v) (Obs e v)) ->
      syntails X false (Vis e k) w <( EG φ )>
  | SynEgBindR: forall {X} {Y} (t: ctree E B Y) (k: Y -> ctree E B X) φ w R,
      entails Y true (Cu Q_E φ (CRet R)) t w ->
      (forall r w', R r w' -> syntails X false (k r) w' <( EG φ )>) ->
      syntails X false (x <- t ;; k x) w <( EG φ )>
  | SynEgIter: forall {X} {I} R (i: I) w (k: I -> ctree E B (I + X)) φ,
      R i w ->
      (forall (i: I) w,
          R i w ->
          entails X false <( φ )> (iter k i) (w) /\
            entails (I + X) true <( EX (φ EU ret
                                 {fun (lr: I + X) (w': World E) =>
                                    exists (i': I), lr = inl i' /\ R i' w'}) )> (k i) (w)) ->
      syntails X false (iter k i) w <( EG φ )>.

  Arguments syntails X b _ _ _ : clear implicits.
  Set Implicit Arguments.

  (** Soundness follows the derivation, including its prefix-guard evidence. *)
  Theorem soundness : forall X b (t: ctree E B X) w (p: ticl_at E X b),
      syntails X b t w p -> entails X b p t w.
  Proof.
    intros X b t w p H; induction H.
    - rewrite sb_guard; eauto with ticl.
    - csplit; eauto with ticl.
    - apply ret_ret; eauto with ticl.
    - csplit; eauto with ticl.
    - cleft; eauto with ticl.
    - cright; eauto with ticl.
    - apply ticll_bind_l; eauto with ticl.
    - apply (au_stuck (b:=b)); eauto with ticl.
    - apply (au_ret (b:=b)); cleft; eauto with ticl.
    - apply (au_ret (b:=b)); cright; eauto with ticl.
    - cleft; eauto with ticl.
    - apply (au_brS (b:=b) c k y); right; split; eauto with ticl.
    - cleft; eauto with ticl.
    - apply (au_step (b:=b)); right; split; eauto with ticl.
    - cleft; eauto with ticl.
    - apply (au_vis (b:=b) e k wit); right; split; eauto with ticl.
    - eapply (u_bind_r (b:=b) Q_A) with (R:=R); eauto with ticl.
    - eapply (u_iter_prefix Q_A Ri Rv); eauto with ticl.
    - eapply (u_iter (b:=b) Q_A Ri Rv); eauto with ticl.
    - apply (eu_stuck (b:=b)); eauto with ticl.
    - apply (eu_ret (b:=b)); cleft; eauto with ticl.
    - apply (eu_ret (b:=b)); cright; eauto with ticl.
    - cleft; eauto with ticl.
    - apply (eu_brS (b:=b) c k); right; split; eauto with ticl.
    - cleft; eauto with ticl.
    - apply (eu_step (b:=b)); right; split; eauto with ticl.
    - cleft; eauto with ticl.
    - apply (eu_vis (b:=b) e k); right; split; eauto with ticl.
    - eapply (u_bind_r (b:=b) Q_E) with (R:=R); eauto with ticl.
    - eapply (u_iter_prefix Q_E Ri Rv); eauto with ticl.
    - eapply (u_iter (b:=b) Q_E (fun i w => not_done w /\ Ri i w) Rv).
      + assumption.
      + split; assumption.
      + intros s z [Hd Hi].
        match goal with
        | Hbody : forall i w, Ri i w -> not_done w -> _ |- _ =>
            pose proof (Hbody s z Hi Hd) as Hb
        end.
        unshelve refine (impl_ticl_until Q_E Q_E eq_refl φ φ
          (fun _ _ Hphi => Hphi) _ _ _ (k s) z Hb).
        apply ret_impl_ticl.
        intros [j|r] z' Hj; simpl in *; tauto.
    - apply (an_brS (b:=b) c k y); split; eauto with ticl.
    - apply (an_step (b:=b)); split; eauto with ticl.
    - apply (an_vis (b:=b) e k wit); split; eauto with ticl.
    - eapply (an_bind_l (b:=b)) with (R:=R); eauto with ticl.
    - eapply (ticl_bind_ret (b:=b)) with (R:=R); eauto with ticl.
    - eapply (n_iter_prefix Q_A Ri Rv); eauto with ticl.
    - apply (en_brS (b:=b) c k); split; eauto with ticl.
    - apply (en_step (b:=b)); split; eauto with ticl.
    - apply (en_vis (b:=b) e k); split; eauto with ticl.
    - eapply (ticl_bind_ret (b:=b)) with (R:=R); eauto with ticl.
    - eapply (n_iter_prefix Q_E Ri Rv); eauto with ticl.
    - change <( {BrS c k}, w |=L AG φ )>; rewrite <- (ag_brS c k y); eauto with ticl.
    - change <( {Step t}, w |=L AG φ )>; rewrite <- ag_step; eauto with ticl.
    - change <( {Vis e k}, w |=L AG φ )>; rewrite <- (ag_vis e k wit); eauto with ticl.
    - apply ag_bind_r with R; eauto with ticl.
    - apply ag_iter with R; eauto with ticl.
    - change <( {BrS c k}, w |=L EG φ )>; rewrite <- (eg_brS c k); eauto with ticl.
    - change <( {Step t}, w |=L EG φ )>; rewrite <- eg_step; eauto with ticl.
    - change <( {Vis e k}, w |=L EG φ )>; rewrite <- (eg_vis e k); eauto with ticl.
    - apply eg_bind_r with R; eauto with ticl.
    - apply eg_iter with R; eauto with ticl.
  Qed.

  Arguments soundness X b t w p _ : clear implicits.
End SyntacticEntailment.
