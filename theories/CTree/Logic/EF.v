From Coq Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

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
  Logic.EX
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
  
(*| CTL logic lemmas on c/itrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma ef_done: forall (t: ctree E X) φ w,
      is_done w ->
      <( t, w |= EF now φ )> ->
      φ w.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra.
    - now rewrite ctl_now in H.
    - destruct H0 as (? & ? & ? & ?).
      exfalso.
      eapply done_not_ktrans with (t:=t); eauto.
  Qed.

  Lemma ef_stuck: forall w φ,
      <( {Ctree.stuck: ctree E X}, w |= EF φ )> <->
      <( {Ctree.stuck: ctree E X}, w |= φ )>.
  Proof.
    split; intros.
    - cbn in H; rewrite unfold_stuck; dependent induction H; auto.
      + now rewrite unfold_stuck in H.
      + destruct H0 as (? & ? & ? & ?).
        now apply ktrans_stuck in H0.
    - now next; left.
  Qed.

  Lemma ef_ret: forall r w (Rr: rel X (World E)),      
      Rr r w ->
      not_done w ->
      <( {Ret r}, w |= EF done Rr )>.
  Proof.
    intros * Hr Hd.
    next; right.
    next; inv Hd.
    - exists (Ctree.stuck), (Done r); split.
      + apply ktrans_done; auto.
      + apply ef_stuck. now constructor.
    - exists (Ctree.stuck), (Finish e v r); split.
      + apply ktrans_finish; auto.
      + apply ef_stuck; now constructor.
  Qed.

  Lemma not_done_vis_ef: forall (t: ctree E X) φ w,
      <( t, w |= EF vis φ )> ->
      not_done w.
  Proof with eauto with ctl.
    intros * Hf.
    next in Hf ; destruct Hf.
    - rewrite ctl_vis in H; inv H...
    - destruct H as (? & ? & ? & ?).
      now apply ktrans_not_done with t x x0.
  Qed.

  Lemma not_done_pure_ef: forall (t: ctree E X) w,
      <( t, w |= EF pure )> ->
      not_done w.
  Proof with eauto with ctl.
    intros * Hf.
    next in Hf ; destruct Hf.
    - rewrite ctl_pure in H; subst...
    - destruct H as (? & ? & ? & ?).
      now apply ktrans_not_done with t x x0.
  Qed.

  Lemma ef_guard: forall (t: ctree E X) w φ,
      <( {Guard t}, w |= EF φ )> <->
      <( t, w |= EF φ )>.
  Proof.
    intros.
    now rewrite sb_guard.
  Qed.

  Lemma ef_br: forall n (k: fin' n -> ctree E X) w φ,
      <( {Br n k}, w |= EF now φ )> <->
        (exists (i: fin' n), <( {k i}, w |= EF now φ )>).
  Proof.
    split; intros.
    - next in H; destruct H.
      + exists Fin.F1.
        next; left.
        now rewrite ctl_now in *.
      + destruct H as (? & ? & ? & ?).
        apply ktrans_br in H as (i & ? & -> & ?).
        rewrite H in H0.
        now (exists i).
    - destruct H as (i & ?).
      next in H; destruct H.
      + next; left.
        now rewrite ctl_now in *.
      + next; right; next.
        destruct H as (? & ? & ? & ?).
        exists (k i), w; split; auto with ctl.
        * apply ktrans_br.
          exists i; intuition.
        * next; right; next.
          exists x, x0; intuition.
  Qed.

  Lemma ef_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ,
      (φ w \/ (not_done w /\ exists (x: encode e),
                 <( {k x}, {Obs e x} |= EF now φ )>)) ->
      <( {Vis e k}, w |= EF now φ )>.        
  Proof.
    intros.
    destruct H as [H | [Hd (v & ?)]].
    - now next; left.
    - next; right; next.
      + exists (k v), (Obs e v); split; auto.
        apply ktrans_vis.
        exists v; intuition.
  Qed.

  Lemma ef_ret_inv: forall (x: X) w R,
      <( {Ret x}, w |= EF (EX done R) )> ->
      R x w.
  Proof.
    intros.
    next in H; destruct H.
    - destruct H as (? & ? & ? & ?).
      ddestruction H; now ddestruction H0.
    - next in H; destruct H as (? & ? & ? & ?).
      ddestruction H; observe_equ x; next in H0; destruct H0;
        rewrite <- Eqt, H in H0;
        destruct H0 as (? & ? & ? & ?);
        now apply ktrans_stuck in H0.
  Qed.

End BasicLemmas.

(* TODO: WIP here copied from AF.v *)
Section CtlEfBind.
  Context {E: Type} {HE: Encode E}.

  Typeclasses Transparent equ.
  Theorem ef_bind_vis{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
      <( t, w |= EF vis φ )> ->
      <( {x <- t ;; k x}, w |= EF vis φ )>.
  Proof.
    intros * Haf.
    revert X k.
    induction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn.
      apply ctl_vis in H; inv H; now constructor.
    - (* StepA *)
      destruct H0 as (t' & w' & TR' & H0).
      destruct H1 as (t_ & w_ & TR_ & H1).
      clear H.
      next; right; next. 
      exists (x <- t_;; k x), w_.
      split.
      + apply ktrans_bind_l; auto.          
        eapply not_done_vis_ef with (t:=x <- t_ ;; k x).
        now apply H1.
      + apply H1.
  Qed.

  Theorem ef_bind_pure{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      <( t, w |= EF pure )> ->
      <( {x <- t ;; k x}, w |= EF pure )>.
  Proof.
    intros * Haf.
    revert X k.
    induction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn.
      apply ctl_pure in H; inv H; now constructor.
    - (* StepA *)
      destruct H0 as (t' & w' & TR' & H0).
      destruct H1 as (t_ & w_ & TR_ & H1).
      clear H.
      next; right; next. 
      exists (x <- t_;; k x), w_.
      split.
      + apply ktrans_bind_l; auto.          
        eapply not_done_pure_ef with (t:=x <- t_ ;; k x).
        now apply H1.
      + apply H1.
  Qed.

  Theorem ef_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w w' φ r,
      <( t, w |= EF EX done= r w' )> ->
      not_done w' ->
      <( {k r}, w' |= EF now φ )> ->
      <( {x <- t ;; k x}, w |= EF now φ )>.
  Proof.
    intros.
    revert H0 H1.
    induction H; intros.
    - apply ex_done in H as (Hd & y & Heqy & -> & ->).
      assert (Hk: x <- t ;; k x ~  x <- Ret y ;; k x) by (__upto_bind_sbisim; auto).
      rewrite Hk, bind_ret_l.
      apply H1.
    - destruct H0 as (t0 & w0 & TR0 & H0).
      destruct H1 as (t1 & w1 & TR1 & H1).
      specialize (H1 H2 H3).
      clear H.
      next; right; next.
      (* Here, whatever I chose is wrong :( *)
  Admitted.

End CtlEfBind.

Section CtlAfIter.
  Context {E: Type} {HE: Encode E}.

  (* Total correctness lemma for [iter] *)
  (* [Ri: I -> World E -> Prop] loop invariant (left).
     [Rr: X -> World E -> Prop] loop postcondition (right).
     [Rv: (I * World E) -> (I * World E) -> Prop)] loop variant (left). *)
  Lemma af_iter{X I} Ri Rr (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= AF AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => Ri i' w' /\
                                    Rv (i', w') (i, w)
                       | inr r' => Rr r' w'
                       end})>) ->
    well_founded Rv ->
    Ri i w ->
    <( {iter k i}, w |= AF done Rr )>.
  Proof.      
    intros H WfR Hi.
    generalize dependent k.
    revert Hi.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    Opaque entailsF.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    eapply af_bind_r with
      (R:=fun (x : I + X) (w' : World E) =>
            match x with
            | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
            | inr r' => Rr r' w'
            end); auto.
    intros [i' | r] w'.
    - intros (Hi' & Hv) Hd.
      apply af_guard.
      remember (i', w') as y.
      replace i' with (fst y) by now subst.
      replace w' with (snd y) by now subst.      
      apply HindWf; inv Heqy; auto.
    - apply af_ret. 
  Qed.

  (*| Instead of a WF relation [Rv] provide a "ranking" function [f] |*)
  Lemma af_iter_nat{X I} Ri Rr (f: I -> World E -> nat) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= AF AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => Ri i' w' /\ f i' w' < f i w
                       | inr r' => Rr r' w'
                       end})>) ->
    Ri i w ->
    <( {iter k i}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter with Ri (ltof _ (fun '(i, w) => f i w));
      auto.
    apply well_founded_ltof.
  Qed.

  Lemma af_iter_nat'{X I} Rr (f: I -> World E -> nat) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w,
        not_done w ->
        <( {k i}, w |= AF AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => not_done w' /\ f i' w' < f i w
                       | inr r' => Rr r' w'
                       end})>) ->
    not_done w ->
    <( {iter k i}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_nat with
      (Ri:=fun _ => not_done) (f:=f); intros; auto.
  Qed.

  (* Well-founded induction on length of lists *)
  Lemma af_iter_list{A X I} Ri Rr (f: I -> World E -> list A) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= AF AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => Ri i' w' /\ length (f i' w') < length (f i w)
                       | inr r' => Rr r' w'
                       end})>) ->
    Ri i w ->
    <( {iter k i}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_nat with
      Ri (fun i w => length (f i w)); auto.
  Qed.

  Lemma af_iter_list'{A X I} Rr (f: I -> World E -> list A) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w,
        not_done w ->
        <( {k i}, w |= AF AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => not_done w' /\
                                    length (f i' w') < length (f i w)
                       | inr r' => Rr r' w'
                       end})>) ->
    not_done w ->
    <( {iter k i}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_list with
      (Ri:=fun _ => not_done) (f:=f); intros; auto.
  Qed.  
End CtlAfIter.

(*| Combinators for [interp_state] |*)
Section CtlAfState.
  Context {E F S: Type} {HE: Encode E} {HF: Encode F}
    (h: E ~> stateT S (ctree F)).

  Theorem af_bind_state_vis{X Y}: forall s w (t: ctree E Y) (k: Y -> ctree E X) φ,
      <( {interp_state h t s}, w |= AF vis φ )> ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AF vis φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    now apply af_bind_vis.
  Qed.
  
  Theorem af_bind_state_pure{X Y}: forall s w (t: ctree E Y) (k: Y -> ctree E X),
      <( {interp_state h t s}, w |= AF pure )> ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AF pure )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    now apply af_bind_pure.
  Qed.

  Theorem af_bind_state_r{X Y}: forall s (t: ctree E Y) (k: Y -> ctree E X) w φ (R: Y * S -> World F -> Prop),
      <( {interp_state h t s}, w |= AF AX done R )> ->
      (forall (y: Y) (s: S) w, R (y,s) w ->
                    not_done w ->
                    <( {interp_state h (k y) s}, w |= AF now φ )>) ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AF now φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply af_bind_r with (R:=R); auto.
    intros [y s'] w' Hr Hd; auto.
  Qed.
     
  Theorem af_iter_state{X I} s Ri (Rr: rel (X * S) (World F))  Rv (i: I) (k: I -> ctree E (I + X)) w:
    (forall (i: I) w s,
        Ri i w s ->
        <( {interp_state h (k i) s}, w |= AF AX done
          {fun '(x, s') w' =>
             match x with
             | inl i' => Ri i' w' s'
                        /\ Rv (i', w', s') (i, w, s)
             | inr r' => Rr (r',s') w'
             end})>) ->
    well_founded Rv ->
    Ri i w s ->
    <( {interp_state h (Ctree.iter k i) s}, w |= AF done Rr )>.
  Proof.
    intros H WfR Hi.
    generalize dependent k.
    revert Hi.
    remember (i, w, s) as P.
    replace i with (fst (fst P)) by now subst.
    replace w with (snd (fst P)) by now subst.
    replace s with (snd P) by now subst.
    clear HeqP i w s.
    Opaque entailsF.
    induction P using (well_founded_induction WfR);
      destruct P as ((i, w), s); cbn in *. 
    rename H into HindWf.
    intros.
    rewrite interp_state_unfold_iter.
    eapply af_bind_r with (R:=fun '(r, s0) (w0 : World F) =>
                      match r with
                      | inl i' => Ri i' w0 s0 /\ Rv (i', w0, s0) (i, w, s)
                      | inr r' => Rr (r',s0) w0
                      end); auto.
    intros ([i' | r] & s') w'; cbn.
    - intros (Hi' & Hv) Hd.
      apply af_guard.
      remember (i', w',s') as y.
      replace i' with (fst (fst y)) by now subst.
      replace w' with (snd (fst y)) by now subst.
      replace s' with (snd y) by now subst.      
      apply HindWf; inv Heqy; auto.
    - intros; apply af_ret; auto.
  Qed.
    
  (*| Instead of a WF relation [Rv] provide a "ranking" function [f] |*)
  Lemma af_iter_state_nat{X I} (s: S) Ri (Rr: rel (X * S) (World F)) (f: I -> World F -> S -> nat) (i: I) w
    (k: I -> ctree E (I + X)):
    (forall (i: I) w s,
        Ri i w s ->
        <( {interp_state h (k i) s}, w |= AF AX done
                    {fun '(x, s') w' =>
                       match x with
                       | inl i' => Ri i' w' s' /\ f i' w' s' < f i w s
                       | inr r' => Rr (r',s') w'
                       end})>) ->
    Ri i w s ->
    <( {interp_state h (Ctree.iter k i) s}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_state with Ri (ltof _ (fun '(i, w, s) => f i w s)); auto.
    apply well_founded_ltof.
  Qed.

  Lemma af_iter_state_nat'{X I} (Rr: rel (X * S) (World F)) (f: I -> S -> nat) (s: S)
    (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w s,
        not_done w ->
        <( {interp_state h (k i) s}, w |= AF AX done
                    {fun '(x, s') w' =>
                       match x with
                       | inl i' => not_done w' /\ f i' s' < f i s
                       | inr r' => Rr (r',s') w'
                       end})>) ->
    not_done w ->
    <( {interp_state h (Ctree.iter k i) s}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_state_nat with (Ri:=fun _ w _ => not_done w) (f:=fun i _ => f i); auto.
  Qed.
End CtlAfState.

(*| Combinators for [interp_state] with [writerE] |*)
Section CtlAfStateList.
  Context {E F A: Type} {HE: Encode E} {HF: Encode F} (h: E ~> stateT (list A) (ctree F)).

  Lemma af_iter_state_list{X I} Ri (Rr: rel (X * list A) (World F)) (l: list A) w (i: I) (k: I -> ctree E (I + X)):
    (forall (i: I) w (l: list A),
        Ri i w l ->
        <( {interp_state h (k i) l}, w |= AF AX done
                 {fun '(x, l') w' =>
                    match x with
                    | inl i' => Ri i' w' l' /\ length l' < length l
                    | inr r' => Rr (r', l') w'
                    end})>) ->
    Ri i w l ->
    <( {interp_state h (Ctree.iter k i) l}, w |= AF done Rr )>.
  Proof.
    intros.
    apply af_iter_state_nat with (Ri:=Ri) (f:=fun _ _ l => length l); auto.
  Qed.

  Lemma af_iter_state_list'{X I} (Rr: rel (X * list A) (World F)) (l: list A) (i: I) w (k: I -> ctree E (I + X)):
    (forall (i: I) w (l: list A),
        not_done w ->
        <( {interp_state h (k i) l}, w |= AF AX done
             {fun '(x, l') w' =>
                match (x: I + X) with
                | inl _ => not_done w' /\ length l' < length l
                | inr r' => Rr (r',l') w'
                end})>) ->
    not_done w ->
    <( {interp_state h (Ctree.iter k i) l}, w |= AF done Rr )>.
  Proof.
    intros.
    eapply af_iter_state_list with (Ri:=fun _ w _ => not_done w); auto.
  Qed.

End CtlAfStateList.  
