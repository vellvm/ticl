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


(*| Combinators for [interp_state] |*)
Section CtlAgState.
  Context {E F S: Type} {HE: Encode E} {HF: Encode F}
    (h: E ~> stateT S (ctree F)).

  Theorem ag_state_bind_l{X Y}: forall s w (t: ctree E Y) (k: Y -> ctree E X) φ,
      <( {interp_state h t s}, w |= AG now φ )> ->
      <( {interp_state h (x <- t ;; k x) s}, w |= AG now φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    now apply ag_bind_l.
  Qed.

  Theorem ag_state_bind_r{X Y}: forall s (t: ctree E Y) (k: Y -> ctree E X) w φ
                                  (R: Y -> S -> World F -> Prop),
      <( {interp_state h t s}, w |= now φ AU (AX done {fun '(x, s) w => R x s w}) )> ->
      (forall (y: Y) (s: S) (w: World F),
          R y s w ->
          <( {interp_state h (k y) s}, w |= AG now φ )>) ->
      <( {interp_state h (x <- t ;; k x) s} , w |= AG now φ )>.
  Proof.
    intros.
    rewrite interp_state_bind.
    apply ag_bind_r with (R:=fun '(x, s) w => R x s w); auto.
    intros [y s'] w' Hr; auto.
  Qed.

  Theorem ag_state_iter{X I}: forall s (k: I -> ctree E (I + X)) w (x: I) φ R,
      R x s ->        (* Iterator invariant: [x] in [R] *)
      φ w ->          (* Worlds invariant: [φ w] *)
      not_done w ->
      (forall (x: I) (s: S) (w: World F),
          R x s ->
          φ w ->
          not_done w ->
          <( {interp_state h (k x) s}, w |= AX (now φ AU AX done
             {fun (lr: (I+X) * S) (w: World F) =>
                exists (i' : I) (s': S), lr = (inl i', s') /\ φ w /\
                                      not_done w /\ R i' s'}))>) ->
      <( {interp_state h (iter k x) s}, w |= AG now φ )>.
  Proof with auto with ctl.
    intros.
    rewrite interp_state_unfold_iter.
    generalize dependent x.
    generalize dependent s.
    generalize dependent w.
    coinduction RR CIH; intros.
    split; [apply ctl_now; now constructor|split].
    - (* can_step *)
      specialize (H2 _ _ _ H H0 H1).
      cdestruct H2.
      destruct Hs as (t' & w' & TR).
      specialize (H2 _ _ TR).
      apply can_step_bind_l with t' w'; auto.
      cdestruct H2.
      + now apply ax_done in H2 as (? & ?).
      + now apply ctl_now in H2 as (? & ?). 
    - intros t' w' TR.
      apply ktrans_bind_inv in TR as
          [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ft_t (ag_bind_now_ag φ
                       (fun (lr: (I+X) * S) (w: World F) =>
                          exists (i': I) (s': S), lr = (inl i', s') /\
                                               φ w /\ not_done w /\ R i' s'))); cbn.
        apply in_bind_ctx1.
        * specialize (H2 _ _ _ H H0 H1) as HAX.
          cdestruct HAX.
          specialize (HAX _ _ TR0).
          apply HAX.
        * intros (lr' & s_) w_ (i & s' & Hinv & Hφ & Hd' & HR'); inv Hinv.
          rewrite sb_guard.
          setoid_rewrite interp_state_unfold_iter.
          apply CIH...
      + (* [k x] returns *)        
        specialize (H2 _ _ _ H H0 H1) as HAX.        
        cdestruct HAX.
        specialize (HAX _ _ TRt0).
        apply au_stuck in HAX.
        cdestruct HAX.
        now apply can_step_stuck in Hs0.
  Qed.        
End CtlAgState.

Section CtlAgW.
  Context {E Σ W: Type} {HE: Encode E} (h:E ~> stateT Σ (ctreeW W)). 

  Theorem ag_iterW{X I}: forall (i: I) (σ: Σ) (w: W) (k: I -> ctree E (I + X)) φ R,
      R i σ ->       (* Iterator & state invariant [R] *)
      φ w ->         (* Goal Invariant [φ] *)
      (forall (i: I) (σ: Σ) (w: W),
          R i σ ->
          φ w ->
          <( {interp_state h (k i) σ}, {Obs (Log w) tt} |=
              AX (visW φ AU AX
                    (finishW {fun (lr: I + X) (σ: Σ) (w: W) =>
                                exists (i: I), lr = inl i /\ R i σ /\ φ w})))>) ->
      <( {interp_state h (iter k i) σ}, {Obs (Log w) tt} |= AG visW φ )>.
  Proof with eauto with ctl.
    setoid_rewrite ctl_vis_now.
    setoid_rewrite ctl_finish_done.
    intros.
    rewrite interp_state_unfold_iter.
    generalize dependent σ.
    generalize dependent i.
    generalize dependent w.    
    coinduction RR CIH; intros.
    split; [apply ctl_now; eauto with ctl |split].
    - (* can_step *)
      specialize (H1 _ _ _ H H0).
      cdestruct H1.
      destruct Hs as (t' & w' & TR).
      specialize (H1 _ _ TR).
      apply can_step_bind_l with t' w'...
      cdestruct H1.
      + apply ax_done in H1 as (? & ?)...
      + apply ctl_now in H1; destruct H1...
    - intros t' w' TR.
      apply ktrans_bind_inv in TR as
          [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ft_t (ag_bind_now_ag
                       (fun w => (exists (e : writerE W) (v : encode e),
                                  w = Obs e v /\
                                    (let 'Log v0 as x := e return (encode x -> Prop) in
                                     fun 'tt => φ v0) v))
                       (fun (x : (I + X) * Σ) (w : World (writerE W)) =>
                        exists (e : writerE W) (v : encode e),
                          w = Obs e v /\
                          (let
                           '(x0, s) := x in
                            fun pat0 : writerE _ =>
                            let
                              'Log w0 as u := pat0 return (encode u -> Prop) in
                            fun 'tt => exists i' : I, x0 = inl i' /\ R i' s /\ φ w0)
                            e v))); cbn.
        apply in_bind_ctx1.
        * specialize (H1 _ _ _ H H0) as HAX.
          cdestruct HAX.
          specialize (HAX _ _ TR0).
          apply HAX.
        * intros (lr' & s_) w_ ([σ'] & [] & ? & ? & i' & ? & ?); subst.
          unfold Classes.iter, MonadIter_ctree.          
          apply (ft_t (mequ_clos_cag (KS:=KripkeSetoidSBisim))); cbn.
          econstructor.
          rewrite sb_guard.
          rewrite interp_state_unfold_iter.
          reflexivity.
          reflexivity.
          apply CIH...
      + (* [k x] returns *)        
        specialize (H1 _ _ _ H H0) as HAX.        
        cdestruct HAX.
        specialize (HAX _ _ TRt0).
        apply au_stuck in HAX.
        cdestruct HAX.
        now apply can_step_stuck in Hs0.
  Qed.        

End CtlAgW.
