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

  Lemma au_done: forall (t: ctree E X) ψ φ w,
      is_done w ->
      <( t, w |= ψ AU now φ )> ->
      φ w.
  Proof.
    intros * Hret Hcontra.
    inv Hcontra; auto.
    destruct H0 as ((? & ? & ?) & ?).
    exfalso.
    eapply done_not_ktrans with (t:=t); eauto.
  Qed.

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

  Lemma au_ret: forall r w (Rr: rel X (World E)) ψ,      
      Rr r w ->
      not_done w ->
      <( {Ret r}, w |= ψ )> ->
      <( {Ret r}, w |= ψ AU done Rr )>.
  Proof.
    intros * Hr Hd Hw.
    next; right; split; auto.
    split.
    - now apply can_step_ret.
    - intros t_ w_ TR_.
      inv Hd.
      + cbn in TR_. dependent destruction TR_. 
        next; left.
        rewrite ctl_done.
        now constructor.
      + apply ktrans_finish in TR_ as (-> & ->).
        next; left.
        rewrite ctl_done.
        now constructor.       
  Qed.

  Lemma not_done_vis_au: forall (t: ctree E X) φ ψ w,
      <( t, w |= ψ AU vis φ )> ->
      not_done w.
  Proof.
    intros * Hf.
    next in Hf ; destruct Hf.
    - inv H; constructor.
    - destruct H, H0.
      now apply can_step_not_done with t.
  Qed.

  Lemma not_done_pure_au: forall (t: ctree E X) w ψ,
      <( t, w |= ψ AU pure )> ->
      not_done w.
  Proof.
    intros * Hf.
    next in Hf ; destruct Hf.
    - subst; constructor. 
    - destruct H, H0.
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
      <( {Br n k}, w |= now ψ AU now φ )> <->
        (forall (i: fin' n), <( {k i}, w |= now ψ AU now φ )>).
  Proof.
    split; intros.
    - next in H; cdestruct H.
      + next; now left. 
      + cdestruct H.
        now apply ax_br in H0 as (? & ?).
    - next.
      pose proof (H Fin.F1).
      next in H0; cdestruct H0. 
      + now left.
      + cdestruct H0.
        right; split; auto.
        split.
        * apply can_step_br.
          destruct H1.
          now apply can_step_not_done with (k Fin.F1).
        * intros t' w' TR.
          apply ktrans_br in TR as (i & -> & -> & ?); auto.
  Qed.

  Lemma au_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ ψ,
      (φ w \/ (ψ w /\ not_done w /\
                forall (x: encode e), <( {k x}, {Obs e x} |= now ψ AU now φ )>)) ->
      <( {Vis e k}, w |= now ψ AU now φ )>.        
  Proof.
    intros.
    destruct H as [H | [Hd H]].
    - now next; left.
    - next; right; split; auto.
      next; split.
      + now apply can_step_vis.
      + intros t' w' TR'.
        apply ktrans_vis in TR' as (? & -> & ? & ?).
        now rewrite <- H0.
  Qed.

  Lemma au_ret_inv: forall (x: X) ψ w R,
      <( {Ret x}, w |= ψ AU (AX done R) )> ->
      R x w.
  Proof.
    intros.
    next in H; cdestruct H.
    - cdestruct H.
      destruct Hs as (tstuck & w' & TR).
      specialize (H _ _ TR).
      inv TR; rewrite unfold_entailsF in H; now ddestruction H. 
    - cdestruct H.
      cdestruct H0.
      destruct Hs as (tstuck & w' & TR).
      specialize (H0 _ _ TR).
      inv TR; observe_equ H2; rewrite <- Eqt, H4 in H0.
      all: rewrite au_stuck in H0;
        apply ax_stuck in H0;
        rewrite ctl_done in H0;
        now ddestruction H0.
  Qed.

End BasicLemmas.

Section CtlAfBind.
  Context {E: Type} {HE: Encode E}.

  Typeclasses Transparent equ.
  Theorem af_bind_vis{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) φ w,
      <( t, w |= AF vis φ )> ->
      <( {x <- t ;; k x}, w |= AF vis φ )>.
  Proof.
    intros * Haf.
    revert X k.
    induction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn.
      ddestruction H.
      apply ctl_vis; now constructor.
    - (* StepA *)
      destruct H0, H1; clear H H0.      
      next; right; next; split.
      + (* can_step *)
        destruct H1 as (t' & w' & TR').
        eapply can_step_bind_l with t' w'; auto.
        eapply not_done_vis_au with (t:=t') (ψ:=<( ⊤ )>).
        rewrite !unfold_entailsF.        
        now apply H2.
      + (* AX AF *)
        intros t_ w_ TR_.
        apply ktrans_bind_inv in TR_ as
            [(t' & TR' & Hd & ->) |
              (x & w' & TR' & Hr & TRk)].
        * now apply H3.
        * specialize (H2 _ _ TR').
          inv H2.
          ddestruction H.
          -- inv Hr.
          -- destruct H0.
             now apply can_step_stuck in H0.
  Qed.

  Theorem af_bind_pure{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w,
      <( t, w |= AF pure )> ->
      <( {x <- t ;; k x}, w |= AF pure )>.
  Proof.
    intros * Haf.
    revert X k.
    cinduction Haf; intros; subst.
    - (* MatchA *)
      next; left; cbn.
      now apply ctl_pure in H. 
    - (* StepA *)
      destruct H0, H1; clear H H0.      
      next; right; next; split.
      + (* can_step *)
        destruct H1 as (t' & w' & TR').
        eapply can_step_bind_l with t' w'; auto.
        eapply not_done_pure_au with (t:=t') (ψ:=<( ⊤)>).
        rewrite unfold_entailsF.
        now apply H2.
      + (* AX AF *)
        intros t_ w_ TR_.
        apply ktrans_bind_inv in TR_.
        destruct TR_ as [(t' & TR' & Hd & ->) | (x & w' & TR' & Hr & TRk)].
        * now apply H3.
        * specialize (H2 _ _ TR').
          inv H2.
          apply ctl_pure in H; subst.
          -- inv Hr.
          -- destruct H0.
             now apply can_step_stuck in H0.
  Qed.

  Typeclasses Transparent sbisim.
  Lemma au_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w ψ φ R,
      <( t, w |= vis ψ AU AX done R )> ->
      (forall r w', R r w' -> <( {k r}, w' |= vis ψ AU φ )>) ->
      <( {x <- t ;; k x}, w |= vis ψ AU φ )>.
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
          assert(H3': <( {Ctree.stuck: ctree E Y}, w' |= vis ψ AU AX done R)>) by
            now rewrite unfold_entailsF.
          apply au_stuck in H3'.
          destruct H3'.
          now apply can_step_stuck in H2.
  Qed.

  Lemma au_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w ψ φ r w',
      <( t, w |= vis ψ AU AX done= r w' )> ->
      <( {k r}, w' |= vis ψ AU φ )> ->
      <( {x <- t ;; k x}, w |= vis ψ AU φ )>.
  Proof.
    intros.
    eapply au_bind_r.
    + apply H.
    + intros.
      now destruct H1 as (-> & ->). 
  Qed.

  Lemma af_bind_r{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ R,
      <( t, w |= AF AX done R )> ->
      (forall r w', R r w' -> not_done w' -> <( {k r}, w' |= AF φ )>) ->
      <( {x <- t ;; k x}, w |= AF φ )>.
  Proof.
    intros.
    cinduction H.
    - apply ax_done in H as (? & ? & ? & HR).
      rewrite H1, bind_ret_l.
      now apply H0.
    - destruct H1, H2; clear H2.
      next; right; split.
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
          assert(H3': <( {Ctree.stuck: ctree E Y}, w' |= AF AX done R)>) by
            now rewrite unfold_entailsF.
          apply au_stuck in H3'.
          destruct H3'.
          now apply can_step_stuck in H2.
  Qed.          

  Lemma af_bind_r_eq{X Y}: forall (t: ctree E Y) (k: Y -> ctree E X) w φ r w',
      <( t, w |= AF AX done= r w' )> ->
      <( {k r}, w' |= AF φ )> ->
      <( {x <- t ;; k x}, w |= AF φ )>.
  Proof.
    intros.
    eapply af_bind_r.
    + apply H.
    + intros.
      now destruct H1 as (-> & ->). 
  Qed.

End CtlAfBind.

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
      apply au_guard.
      remember (i', w') as y.
      replace i' with (fst y) by now subst.
      replace w' with (snd y) by now subst.      
      apply HindWf; inv Heqy; auto.
    - intros HR Hd; apply au_ret; auto.
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
      apply au_guard.
      remember (i', w',s') as y.
      replace i' with (fst (fst y)) by now subst.
      replace w' with (snd (fst y)) by now subst.
      replace s' with (snd y) by now subst.      
      apply HindWf; inv Heqy; auto.
    - intros; apply au_ret; auto.
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
