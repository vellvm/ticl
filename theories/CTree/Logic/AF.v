From Coq Require Import
  Basics
  Arith.Wf_nat
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

  Lemma au_stuck: forall w φ ψ,
      <( {Ctree.stuck: ctree E X}, w |= φ AU ψ )> <->
        <( {Ctree.stuck: ctree E X}, w |= ψ )>.
  Proof.
    split; intros.
    - remember (Ctree.stuck) as S.
      cinduction H; subst; auto.
      destruct H0, H1; clear H H0.
      now apply can_step_stuck in H1.
    - now next; left.
  Qed.

  Lemma au_ret_r: forall (r: X) w φ ψ,      
      <( {Ret r}, w |= ψ )> ->
      <( {Ret r}, w |= φ AU ψ )>.
  Proof.
    intros * Hr.
    now next; left.
  Qed.
  
  Lemma au_ret_l: forall (r: X) w φ ψ,      
      <( {Ret r}, w |= AX ψ )> ->
      <( {Ret r}, w |= φ )> ->
      <( {Ret r}, w |= φ AU ψ )>.
  Proof.
    intros * Hr Hd.
    next; right; split; auto.
    split.
    - now cdestruct Hr.
    - intros t_ w_ TR_.
      cdestruct Hr.
      destruct (can_step_not_done _ _ Hs).
      + apply ktrans_done in TR_ as (-> & ->).
        next; left. 
        apply Hr; now constructor. 
      + apply ktrans_finish in TR_ as (-> & ->).
        next; left.
        apply Hr; now constructor.
  Qed.

  Lemma not_done_au: forall (t: ctree E X) φ ψ w,
      <( t, w |= ψ AU now φ )> ->
      not_done w.
  Proof.
    intros * Hf.
    cdestruct Hf.
    - now destruct H.
    - destruct H0.
      now apply can_step_not_done with t.
  Qed.

  Lemma au_guard: forall (t: ctree E X) w ψ φ,
      <( {Guard t}, w |= ψ AU φ )> <->
      <( t, w |= ψ AU φ )>.
  Proof.
    intros.
    now rewrite sb_guard.
  Qed.

  Lemma au_br: forall n (k: fin' n -> ctree E X) w ψ φ,
      not_done w ->
      (<( {Br n k}, w |= φ )> \/
         <( {Br n k}, w |= ψ )> /\
           forall (i: fin' n), <( {k i}, w |= ψ AU φ )>) ->
      <( {Br n k}, w |= ψ AU φ )>.     
  Proof.
   intros e k * Hd [Hφ | (Hψ & H)].
   - now next; left. 
   - next; right; split; auto.
     next; split.
     + now apply can_step_br.
     + intros t' w' TR'.
       apply ktrans_br in TR' as (? & -> & -> & ?).
       apply H.
  Qed.

  Lemma au_br_inv: forall n (k: fin' n -> ctree E X) w ψ φ,
      <( {Br n k}, w |= ψ AU φ )> ->
        (<( {Br n k}, w |= φ )> \/
          forall (i: fin' n), <( {k i}, w |= ψ AU φ )>).
  Proof.
    intros.
    next in H; cdestruct H.
    - now left. 
    - cdestruct H.
      right.
      intros i.        
      now apply ax_br in H0 as (? & ?).
  Qed.

  Lemma au_vis_r: forall (e: E) (k: encode e -> ctree E X) w φ ψ,
      not_done w ->
      <( {Vis e k}, w |= φ )> ->
      <( {Vis e k}, w |= ψ AU φ )>.        
  Proof.
    intros e k * Hd H. 
    now next; left.
  Qed.
  
  Lemma au_vis_l: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ ψ,
      not_done w ->
      <( {Vis e k}, w |= ψ )> ->
      (forall (x: encode e), <( {k x}, {Obs e x} |= ψ AU φ )>) ->
      <( {Vis e k}, w |= ψ AU φ )>.        
  Proof.
    intros e k wit * Hd Hψ H. 
    next; right; split; auto.
    next; split.
    + now apply can_step_vis.
    + intros t' w' TR'.
      apply ktrans_vis in TR' as (? & -> & ? & ?).
      now rewrite <- H0.
  Qed.
  
  Lemma au_ret_done: forall (x: X) ψ w R,
      <( {Ret x}, w |= now ψ AU (AX done R) )> <->
      (R x w /\ not_done w).
  Proof.
    split; intros H.
    - remember (Ret x); cdestruct H; subst.
      + apply ax_done in H as (? & ? & ? & ?).
        now apply sbisim_ret_inv in H0 as ->.
      + apply ctl_now in H.
        destruct H0 as ((t' & w' & TR) & ?).
        specialize (H0 _ _ TR).
        pose proof (ktrans_not_done (Ret x) t' w w' TR) as Hinv; inv Hinv.
        * apply ktrans_done in TR as (-> & ?).
          rewrite H1 in H0.
          assert (H0': <( {Ctree.stuck: ctree E X}, {Done x} |= now ψ AU AX done R )>) by
            now rewrite unfold_entailsF.
          apply au_stuck, ax_stuck, ctl_done in H0'.
          ddestruction H0'.
          split; auto with ctl.
        * apply ktrans_finish in TR as (-> & ?).
          rewrite H1 in H0.
          assert (H0': <( {Ctree.stuck: ctree E X}, {Finish e v x} |= now ψ AU AX done R )>) by
            now rewrite unfold_entailsF.
          apply au_stuck, ax_stuck, ctl_done in H0'.
          ddestruction H0'.
          split; auto with ctl.
    - right.
      destruct H.
      apply ax_done.
      split; eauto.
  Qed.

End BasicLemmas.

Section CtlAuBind.
  Context {E: Type} {HE: Encode E}.

  Typeclasses Transparent equ.
  Theorem au_bind_l{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) ψ φ w,
      <( t, w |= base ψ AU now φ )> ->
      <( {x <- t ;; k x}, w |= base ψ AU now φ )>.
  Proof.
    intros * Haf.
    revert X k.
    cinduction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn.
      now apply ctl_now. 
    - (* StepA *)
      destruct H0, H1; clear H1.
      next; right; split; [|split].
      + (* now ψ *)
        apply H.
      + (* can_step *)
        destruct H0 as (t' & w' & TR').
        eapply can_step_bind_l with t' w'; auto.
        eapply not_done_au with (t:=t') (ψ:=<( base ψ )>).
        rewrite unfold_entailsF.        
        now apply H2.
      + (* AX AF *)
        intros t_ w_ TR_.
        apply ktrans_bind_inv in TR_ as
            [(t' & TR' & Hd & ->) |
              (x & w' & TR' & Hr & TRk)].
        * now apply H3.
        * specialize (H2 _ _ TR').
          inv H2; inv Hr;
            rewrite ctl_base in H, H1.
          -- destruct H1; inv H2.
          -- destruct H1; inv H2.
          -- destruct H4; now apply can_step_stuck in H2.
          -- destruct H4; now apply can_step_stuck in H2.
  Qed.

  Typeclasses Transparent sbisim.
  Lemma au_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w ψ φ R,
      <( t, w |= base ψ AU AX done R )> ->
      (forall r w', R r w' -> <( {k r}, w' |= base ψ AU φ )>) ->
      <( {x <- t ;; k x}, w |= base ψ AU φ )>.
  Proof.
    intros.
    cinduction H.
    - apply ax_done in H as (? & ? & ? & HR).
      rewrite H1, bind_ret_l.
      now apply H0.
    - destruct H1, H2; clear H2.
      next; right; split; [|split].
      + apply H.
      + destruct H1 as (t_ & w_ & TR).
        apply can_step_bind_l with t_ w_; auto.
        destruct (H3 _ _ TR).
        * now apply ax_done in H1 as (? & ?).
        * destruct H2.
          now apply can_step_not_done with t0.
      + intros t_ w_ TR.
        apply ktrans_bind_inv in TR as
            [(t' & TR' & Hd & ->) | (x & w' & TR' & Hr & TRk)].
        * now apply H4.
        * specialize (H3 _ _ TR').
          assert(H3': <( {Ctree.stuck: ctree E Y}, w' |= base ψ AU AX done R)>) by
            now rewrite unfold_entailsF.
          apply au_stuck in H3'.
          destruct H3'.
          now apply can_step_stuck in H2.
  Qed.

  Lemma au_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w ψ φ r w',
      <( t, w |= base ψ AU AX done= r w' )> ->
      <( {k r}, w' |= base ψ AU φ )> ->
      <( {x <- t ;; k x}, w |= base ψ AU φ )>.
  Proof.
    intros.
    eapply au_bind_r.
    + apply H.
    + intros.
      now destruct H1 as (-> & ->). 
  Qed.

End CtlAuBind.

Section CtlAuIter.
  Context {E: Type} {HE: Encode E}.

  Lemma au_iter_now{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E (I + X)) (φ: ctlf E (I + X)):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= AF φ \/ 
                    AF AX done
                      {fun (x: I + X) (w': World E) => True})>) ->

    <( {iter k i}, w |= AF φ )>.
                                                
  (* Termination lemma for [iter] *)
  (* [Ri: I -> World E -> Prop] loop invariant (left).
     [Rr: X -> World E -> Prop] loop postcondition (right).
     [Rv: (I * World E) -> (I * World E) -> Prop)] loop variant (left). *)
  Lemma au_iter_done{X I} Ri Rr (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E (I + X)) φ:
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= base φ AU AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                       | inr r' => not_done w' /\ φ w' /\ Rr r' w'
                       end})>) ->
    well_founded Rv ->
    Ri i w ->
    <( {iter k i}, w |= base φ AU done Rr )>.
  Proof.      
    intros H WfR Hi.
    generalize dependent k.
    revert Hi.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    eapply au_bind_r with
      (R:=fun (x : I + X) (w' : World E) =>
            match x with
            | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
            | inr r' => not_done w' /\ φ w' /\ Rr r' w'
            end); auto.
    intros [i' | r] w'.            
    - intros (Hi' & Hv). 
      apply au_guard.
      remember (i', w') as y.
      replace i' with (fst y) by now subst.
      replace w' with (snd y) by now subst.      
      apply HindWf; inv Heqy; auto.
    - intros [Hd (Hφ & HR)]; inv Hd.
      + apply au_ret_l.
        * rewrite ax_done; split; eauto with ctl.
        * apply ctl_base; intuition. 
      + apply au_ret_l.
        * rewrite ax_done; split; eauto with ctl. 
        * apply ctl_base; intuition. 
  Qed.

  (*| Instead of a WF relation [Rv] a "ranking" function [f] |*)
  Lemma au_iter_nat{X I} Ri Rr (f: I -> World E -> nat) (i: I) w (k: I -> ctree E (I + X)) φ:
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= base φ AU AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => Ri i' w' /\ f i' w' < f i w
                       | inr r' => not_done w' /\ φ w' /\ Rr r' w'
                       end})>) ->
    Ri i w ->
    <( {iter k i}, w |= base φ AU done Rr )>.
  Proof.
    intros.
    eapply au_iter with Ri (ltof _ (fun '(i, w) => f i w));
      auto.
    apply well_founded_ltof.
  Qed.

  (* Well-founded induction on length of lists *)
  Lemma au_iter_list{A X I} Ri Rr (f: I -> World E -> list A) (i: I) w (k: I -> ctree E (I + X)) φ:
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= base φ AU AX done
                    {fun (x: I + X) w' =>
                       match x with
                       | inl i' => Ri i' w' /\ length (f i' w') < length (f i w)
                       | inr r' => not_done w' /\ φ w' /\ Rr r' w'
                       end})>) ->
    Ri i w ->
    <( {iter k i}, w |= base φ AU done Rr )>.
  Proof.
    intros.
    eapply au_iter_nat with
      Ri (fun i w => length (f i w)); auto.
  Qed.
End CtlAuIter.

(*| Combinators for [interp_state] |*)
Section CtlAuState.
  Context {E F S: Type} {HE: Encode E} {HF: Encode F}
    (h: E ~> stateT S (ctree F)).

  Theorem au_state_bind_l{X Y}: forall s w (t: ctree E Y) (k: Y -> ctree E X) φ,
      <( {interp_state h t s}, w |= AF now φ )> ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AF now φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    now apply au_bind_l.
  Qed.  

  Theorem au_state_bind_r{X Y}: forall s (t: ctree E Y) (k: Y -> ctree E X) w ψ φ (R: Y -> S -> World F -> Prop),
      <( {interp_state h t s}, w |= base ψ AU AX done {fun '(y, s) => R y s} )> ->
      (forall (y: Y) (s: S) w, R y s w ->
          <( {interp_state h (k y) s}, w |= base ψ AU φ )>) ->
      <( {interp_state h (x <- t ;; k x) s}, w |= base ψ AU φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply au_bind_r with (R:=fun '(y, s) => R y s); auto.
    intros [y s'] w' Hr; auto.
  Qed.

  Theorem au_state_bind_r_eq{X Y}: forall s s' (t: ctree E Y) (k: Y -> ctree E X) w w' ψ φ (r: Y),
      <( {interp_state h t s}, w |= base ψ AU AX done={(r, s')} w' )> ->
      <( {interp_state h (k r) s'}, w' |= base ψ AU φ )> ->
      <( {interp_state h (x <- t ;; k x) s}, w |= base ψ AU φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply au_bind_r_eq with (r, s') w'; auto. 
  Qed.

  Theorem au_state_iter{X I} s Ri (Rr: rel (X * S) (World F)) Rv (i: I) (k: I -> ctree E (I + X)) φ w:
    (forall (i: I) w s,
        Ri i w s ->
        not_done w ->
        <( {interp_state h (k i) s}, w |= base φ AU AX done
          {fun '(x, s') w' => not_done w' /\
             match x with
             | inl i' => Ri i' w' s' /\ Rv (i', w', s') (i, w, s)
             | inr r' => φ w' /\ Rr (r',s') w'
             end})>) ->
    well_founded Rv ->
    Ri i w s ->
    not_done w ->
    <( {interp_state h (Ctree.iter k i) s}, w |= base φ AU done Rr )>.
  Proof.
    intros H WfR Hi Hd.
    generalize dependent k.
    revert Hi.
    remember (i, w, s) as P.
    replace i with (fst (fst P)) by now subst.
    replace w with (snd (fst P)) by now subst.
    replace s with (snd P) by now subst.
    replace w with (snd (fst P)) in Hd by now subst.
    clear HeqP i w s.
    induction P using (well_founded_induction WfR);
      destruct P as ((i, w), s); cbn in *. 
    rename H into HindWf.
    intros.
    rewrite interp_state_unfold_iter.
    eapply au_bind_r with (R:=fun '(r, s0) (w0 : World F) => not_done w0 /\
                      match r with
                      | inl i' => Ri i' w0 s0 /\ Rv (i', w0, s0) (i, w, s)
                      | inr r' => φ w0 /\ Rr (r',s0) w0
                      end); auto.
    intros ([i' | r] & s') w'; cbn.
    - intros (Hd' & Hi' & Hv).
      apply au_guard.
      remember (i', w',s') as y.
      replace i' with (fst (fst y)) by now subst.
      replace w' with (snd (fst y)) by now subst.
      replace s' with (snd y) by now subst.      
      apply HindWf; inv Heqy; auto.
    - intros (Hd' & HR & Hr); inv Hd';
        apply au_ret_l; auto with ctl;
        rewrite ax_done; split; eauto with ctl.          
  Qed.
    
  (*| Instead of a WF relation [Rv] a "ranking" function [f] |*)
  Lemma au_state_iter_nat{X I} (s: S) Ri (Rr: rel (X * S) (World F)) (f: I -> World F -> S -> nat) (i: I) φ w
    (k: I -> ctree E (I + X)):
    (forall (i: I) w s,
        Ri i w s ->
        not_done w ->
        <( {interp_state h (k i) s}, w |= base φ AU AX done
                                       {fun '(x, s') w' =>
                                          not_done w' /\
                                            match x with
                                            | inl i' => Ri i' w' s' /\ f i' w' s' < f i w s
                                            | inr r' => φ w' /\ Rr (r', s') w'
                                            end})>) ->
    Ri i w s ->
    not_done w ->
    <( {interp_state h (Ctree.iter k i) s}, w |= base φ AU done Rr )>.
  Proof.
    intros.
    eapply au_state_iter with Ri (ltof _ (fun '(i, w, s) => f i w s)); auto.
    apply well_founded_ltof.
  Qed.

End CtlAuState.

(*| Combinators for [interp_state] with [writerE] |*)
Section CtlAuStateList.
  Context {E F A: Type} {HE: Encode E} {HF: Encode F} (h: E ~> stateT (list A) (ctree F)).

  Lemma au_state_iter_list{X I} Ri (Rr: rel (X * list A) (World F)) (l: list A) w (i: I) (k: I -> ctree E (I + X)) φ :
    (forall (i: I) w (l: list A),
        Ri i w l ->
        not_done w ->
        <( {interp_state h (k i) l}, w |= base φ AU AX done
                 {fun '(x, l') w' => not_done w' /\
                    match x with
                    | inl i' => Ri i' w' l' /\ length l' < length l
                    | inr r' => φ w' /\ Rr (r', l') w'
                    end})>) ->
    Ri i w l ->
    not_done w ->
    <( {interp_state h (Ctree.iter k i) l}, w |= base φ AU done Rr )>.
  Proof.
    intros.
    apply au_state_iter_nat with (Ri:=Ri) (f:=fun _ _ l => length l);
      auto.
  Qed.
End CtlAuStateList.
