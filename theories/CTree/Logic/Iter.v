From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.EG
  CTree.Logic.Bind
  CTree.Logic.Ret
  Logic.Core.

From Stdlib Require Import Arith.Wf_nat.

Generalizable All Variables.

Import CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.

(** * TICL logic iteration lemmas for ctrees and different Ticl operators.*)
(** This section introduces the structural loop lemmas for the iteration of ctrees. 
    Those are the main structural lemmas and the big contribution of this work.
    Examples of the lemmas are: a termination lemma, a loop invariant lemma, a loop invariant lemma with a well-founded relation,
    a loop invariant lemma with a well-founded relation and a post-condition etc.

    The lemmas in this section internalize complex inductive and coinductive proof techniques to simple lemma application.

    Two regimes (see [Bind.v]): the [ret]-premised lemmas require the loop body to
    return a single value at each leaf; the [_done]-suffixed lemmas at the end of the
    file accept a body that returns several values at once through hidden branching
    and state the obligation one step later ([φ AN (φ AU ψ)]).
*)
Section IterLemmas.
  Context {E B: Type -> Type}.

  (** ** Iteration lemmas for the [AN] operator *)
  (** A loop [iter k i] satisfies prefix [φ AN ψ] if [k i] steps to [φ AN ψ] or 
      there is a finite, decreasing chain (well-founded [Rv]) such that eventually [k i]
      will step to [φ AN ψ]. *)
  Lemma anl_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E B (I + X)) (φ ψ: ticll E):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= φ AN ψ )> \/
          <[ {k i}, w |= φ AN done
                      {fun (lr: I + X) (w': World E) => 
                         exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i}]>) ->
    <( {iter k i}, w |= φ AN ψ )>.
  Proof with auto with ticl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (H _ _ Hi).
    - now eapply ticll_bind_l.
    - eapply anl_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ Ri i' w' /\ Rv i' i)... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  (** A loop [iter k i] satisfies suffix [φ AN ψ] if [k i] steps to [φ AN ψ] or
  there is a finite, decreasing chain (well-founded [Rv]) such that eventually [k i]
  will step to [φ AN ψ]. *)
  Lemma anr_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E) (ψ: ticlr E X):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ AN done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => Ri i' w' /\ Rv i' i
                       | inr r => <[ {Ret r: ctree E B X}, w' |= φ AN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AN ψ ]>.
  Proof with auto with ticl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (H _ _ Hi).
    - eapply anr_bind_r with
        (R:=(fun (lr : I + X) (w' : World E) =>
               match lr with
               | inl i' => Ri i' w' /\ Rv i' i
               | inr r => <[ {Ret r: ctree E B X}, w' |= φ AN ψ ]>
               end))...
      intros [i' | r] w'...
      intros (Hi' & Hv). 
      rewrite sb_guard.
      apply HindWf...
  Qed.

  (** ** Iteration lemmas for the [EN] operator *)
  (** A loop [iter k i] satisfies prefix [φ EN ψ] if [k i] steps to [φ EN ψ] or 
      there is a finite, decreasing chain (well-founded [Rv]) such that eventually [k i]
      will step to [φ EN ψ]. *)
  Lemma enl_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E B (I + X)) (φ ψ: ticll E):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <( {k i}, w |= φ EN ψ )> \/
          <[ {k i}, w |= φ EN done {fun (lr: I + X) w' =>
            exists i', lr = inl i' /\ Ri i' w' /\ Rv i' i} ]>) ->
    <( {iter k i}, w |= φ EN ψ )>.
  Proof with auto with ticl.    
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    cbn in *.
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (H _ _ Hi).
    - now eapply ticll_bind_l.
    - eapply enl_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ Ri i' w' /\ Rv i' i)...
      intros [i' | r] w'.
      + intros (j & Hinv & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  (** A loop [iter k i] satisfies suffix [φ EN ψ] if [k i] steps to [φ EN ψ] or
  there is a finite, decreasing chain (well-founded [Rv]) such that eventually [k i]
  will step to [φ EN ψ]. *)
  Lemma enr_iter{X I} Ri (Rv: relation I) (i: I) w (k: I -> ctree E B (I + X))
    (φ: ticll E) (ψ: ticlr E X):
    well_founded Rv ->
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ EN done {fun (lr: I + X) w' =>
                                    match lr with
                                    | inl i' => Ri i' w' /\ Rv i' i
                                    | inr r => <[ {Ret r: ctree E B X}, w' |= φ EN ψ ]>
                                    end}]>) ->
    <[ {iter k i}, w |= φ EN ψ ]>.
  Proof with auto with ticl.
    intros WfR Hi H.
    generalize dependent k.
    generalize dependent w.
    induction i using (well_founded_induction WfR).
    cbn in *.
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.    
    eapply enr_bind_r with
      (R:=(fun (lr : I + X) (w' : World E) =>
             match lr with
             | inl i' => Ri i' w' /\ Rv i' i
             | inr r => <[ {Ret r: ctree E B X}, w' |= φ EN ψ ]>
             end))...
    intros [i' | r] w'...
    intros (Hi' & Hv).
    rewrite sb_guard.
    apply HindWf...
  Qed.  

  (** ** Iteration lemmas for the [AU] operator *)
  (** A loop [iter k i] satisfies prefix [φ AU ψ] if [k i] eventually terminates with post-condition [R],
      and in the next iteration the loop satisfies [φ AU ψ]. Intuitively, this lemma unfolds the loop body once, using
      post-condition [R]. *)
  Lemma aul_iter_next{X I} R (i: I) w (k: I -> ctree E B (I + X)) (φ ψ: ticll E):
    <[ {k i}, w |= φ AU ret {fun lr w => exists i', lr = inl i' /\ R i' w} ]> ->
    (forall i w, R i w -> <( {iter k i}, w |= φ AU ψ )>) ->
    <( {iter k i}, w |= φ AU ψ )>.
  Proof with auto with ticl.
    unfold iter, MonadIter_ctree.
    intros.
    rewrite unfold_iter.
    apply aul_bind_r with (R:=(fun lr w => exists i', lr = inl i' /\ R i' w))...
    intros ? ? (i' & -> & HR).
    rewrite sb_guard...
  Qed.

  (** ** The liveness split lemma. *)
  (** For a loop [iter k i] to satisfy [φ AU ψ], it is sufficient to show that
      [k i] eventually terminates with loop invariant [R], and in every next iteration the loop satisfies some intermediate
      liveness specification [Ri]. Then starting at [Ri], we can show that the loop satisfies [φ AU ψ]. 

      The key idea of this lemma is that every time we split on an intermediate liveness specification [Ri],
      we can also provide two well-founded relations, one until [Ri] and one from [Ri] to [φ AU ψ].
      We can continue splitting liveness proofs, giving smaller well-founded relations in this way. *)
  Lemma aul_iter_split{X I} R Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E B (I + X)) (φ ψ: ticll E):
    well_founded Rv ->
    not_done w ->
    R i w ->
    (forall i w, not_done w -> Ri i w -> <( {iter k i}, w |= φ AU ψ )>) ->    
    (forall (i: I) w,
        not_done w ->
        R i w ->
        <[ {k i}, w |= φ AU ret
                    {fun (lr: I + X) (w': World E) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ Ri i' w'} ]> \/ 
        <[ {k i}, w |= φ AU ret
                    {fun (lr: I + X) (w': World E) =>
                       exists i', lr = inl i'
                             /\ not_done w'
                             /\ R i' w'
                             /\ Rv (i', w') (i, w) }]>) ->
    <( {iter k i}, w |= φ AU ψ )>.
  Proof with auto with ticl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hd HR Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    destruct (H _ _ Hd HR).
    - rewrite unfold_iter.
      eapply aul_bind_r with (R:=fun (lr : I + X) (w' : World E) => exists i' : I, lr = inl i' /\ not_done w' /\ Ri i' w')...
      intros [i' | r] w' (i_ & His & Hd' & HRi); inv His.
      rewrite sb_guard.
      apply Hi...
    - rewrite unfold_iter.
      eapply aul_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ not_done w'/\ R i' w' /\ Rv (i', w') (i, w))... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, w') as y.
        replace j with (fst y) in Hi' |- * by now subst.
        replace w' with (snd y) in Hd', Hi' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.
      
  (** A loop [iter k i] satisfies prefix [φ AU ψ] if [k i] eventually terminates with loop invariant [R],
      and in every next iteration the loop satisfies the invariant and a well-founded relation [Rv] becomes smaller. *)
  Lemma aul_iter{X I} R (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E B (I + X)) (φ ψ: ticll E):
    well_founded Rv ->
    not_done w ->
    R i w ->    
    (forall (i: I) w,
        not_done w ->
        R i w ->
        <( {k i}, w |= φ AU ψ )> \/
          <[ {k i}, w |= φ AU ret
                      {fun (lr: I + X) (w': World E) =>
                         exists i', lr = inl i'
                               /\ not_done w'
                               /\ R i' w'
                               /\ Rv (i', w') (i, w)}]>) ->
    <( {iter k i}, w |= φ AU ψ )>.
  Proof with auto with ticl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hd Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    destruct (H _ _ Hd Hi).
    - rewrite unfold_iter.
      apply ticll_bind_l... 
    - rewrite unfold_iter.
      eapply aul_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ not_done w'/\ R i' w' /\ Rv (i', w') (i, w))... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, w') as y.
        replace j with (fst y) in Hi' |- * by now subst.
        replace w' with (snd y) in Hd', Hi' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  (** Working with well-founded relations can be tricky, so we provide a lemma that allows to use ranking functions instead *)
  Lemma aul_iter_nat{X I} Ri (f: I -> World E -> nat) (i: I) w (k: I -> ctree E B (I + X))
    (φ ψ: ticll E):
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
                               /\ f i'  w' < f i w}]>) ->
    <( {iter k i}, w |= φ AU ψ )>.
  Proof.
    intros.
    eapply aul_iter with Ri
                         (ltof _ (fun '(i, w) => f i w)); auto.
    apply well_founded_ltof.
  Qed.

  (** A loop [iter k i] satisfies suffix [φ AU ψ] if [k i] eventually terminates with post-condition [R],
      and in the next iteration the loop satisfies [φ AU ψ]. Intuitively, this lemma unfolds the loop body once, using
      post-condition [R]. *)
  Lemma aur_iter_next{X I} R (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E) ψ:
    <[ {k i}, w |= φ AU ret {fun lr w => exists i', lr = inl i' /\ R i' w} ]> ->
    (forall i w, R i w -> <[ {iter k i}, w |= φ AU ψ ]>) ->
    <[ {iter k i}, w |= φ AU ψ ]>.
  Proof with auto with ticl.
    unfold iter, MonadIter_ctree.
    intros.
    rewrite unfold_iter.
    apply aur_bind_r with (R:=(fun lr w => exists i', lr = inl i' /\ R i' w))...
    intros ? ? (i' & -> & HR).
    rewrite sb_guard...
  Qed.
  
  (** A loop [iter k i] satisfies suffix [φ AU ψ] if [k i] eventually terminates with loop invariant [Ri],
      and in every next iteration the loop satisfies the invariant and a well-founded relation [Rv] becomes smaller. *)
  Lemma aur_iter{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E) (ψ: ticlr E X):
    well_founded Rv ->    
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ AU ret
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
                       | inr r => <[ {Ret r: ctree E B X}, w' |= φ AN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AU ψ ]>.
  Proof with auto with ticl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    eapply aur_bind_r with
      (R:=(fun (lr : I + X) (w' : World E) =>
             match lr with
             | inl i' => Ri i' w' /\ Rv (i', w') (i, w)
             | inr r => <[ {Ret r: ctree E B X}, w' |= φ AN ψ ]>
             end))...
    intros [i' | r] w'...
    - intros (Hi' & Hv). 
      rewrite sb_guard.
      remember (i', w') as y.
      replace i' with (fst y) in Hi' |- * by now subst.
      replace w' with (snd y) in Hi' |- * by now subst.
      apply HindWf...
    - apply ticlr_an_au. 
  Qed.

  (** Working with well-founded relations can be tricky, so we provide a lemma that allows to use ranking functions
  instead *)
  Lemma aur_iter_nat{X I} Ri (f: I -> World E -> nat) (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E) (ψ: ticlr E X):
    Ri i w ->    
    (forall (i: I) w,
        Ri i w ->
        <[ {k i}, w |= φ AU ret
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => Ri i' w' /\ f i' w' < f i w
                       | inr r => <[ {Ret r: ctree E B X}, w' |= φ AN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AU ψ ]>.
  Proof.
    intros.
    eapply aur_iter with Ri (ltof _ (fun '(i, w) => f i w)); auto.
    apply well_founded_ltof.
  Qed.
  
  (** ** Iteration lemmas for the [EU] operator *)
  (** A loop [iter k i] satisfies prefix [φ EU ψ] if [k i] eventually terminates with loop invariant [Ri],
      and in every next iteration the loop satisfies the invariant and a well-founded relation [Rv] becomes smaller. *)
  Lemma eul_iter{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E B (I + X)) (φ ψ: ticll E):
    well_founded Rv ->
    Ri i w ->
    not_done w ->
    (forall (i: I) w,
        Ri i w ->
        not_done w ->
        <( {k i}, w |= φ EU ψ )> \/
          <[ {k i}, w |= φ EU ret
                      {fun (lr: I + X) (w': World E) =>
                         exists i', lr = inl i' /\ not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)}]>) ->
    <( {iter k i}, w |= φ EU ψ )>.
  Proof with auto with ticl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hi Hd H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    destruct (H _ _ Hi)...
    - now eapply ticll_bind_l.
    - eapply eul_bind_r with
        (R:=fun (lr: I + X) (w': World E) =>
              exists i' : I, lr = inl i' /\ not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w))... 
      intros [i' | r] w'.            
      + intros (j & Hinv & Hd' & Hi' & Hv); inv Hinv.
        rewrite sb_guard.
        remember (j, w') as y.
        replace j with (fst y) in Hi' |- * by now subst.
        replace w' with (snd y) in Hi',Hd' |- * by now subst.
        apply HindWf...
      + intros (j & Hcontra & ?); inv Hcontra.
  Qed.

  (** A loop [iter k i] satisfies suffix [φ EU ψ] if [k i] eventually terminates with loop invariant [Ri],
      and in every next iteration the loop satisfies the invariant and a well-founded relation [Rv] becomes smaller. *)
  Lemma eur_iter{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E) (ψ: ticlr E X):
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
                       | inr r => <[ {Ret r: ctree E B X}, w' |= φ EN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ EU ψ ]>.
  Proof with auto with ticl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hi Hd H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    eapply eur_bind_r with
      (R:=(fun (lr : I + X) (w' : World E) =>
             match lr with
             | inl i' => not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)
             | inr r => <[ {Ret r: ctree E B X}, w' |= φ EN ψ ]>
             end))...
    intros [i' | r] w'...
    intros (Hd' & Hi' & Hv). 
    rewrite sb_guard.
    remember (i', w') as y.
    replace i' with (fst y) in Hi' |- * by now subst.
    replace w' with (snd y) in Hi',Hd' |- * by now subst.
    apply HindWf...
    apply ticlr_en_eu.
  Qed.
  
  (** ** Iteration lemmas for the coinductive [AG] operator *)
  (** The world of [φ EU ret R] is never done (sibling of [aur_ret_not_done]). *)
  Lemma eur_ret_not_done{X}: forall φ R (t: ctree E B X) (w: World E),
      <[ t, w |= φ EU ret R ]> ->
      not_done w.
  Proof.
    intros * H.
    cinduction H.
    - cdestruct Hp; auto.
    - now apply ticll_not_done in Hp.
  Qed.

  (** A loop [iter k i] satisfies [AG φ] if [k i] always terminates with loop invariant [R],
      while the return value of the iteration is always the left-injection [lr = inl i'].
      This lemma internalizes powerful coinductive proof techniques to simple lemma application. *)
  Lemma ag_iter{X I} (R: rel I (World E)) (i: I) w (k: I -> ctree E B (I + X)) φ:
    R i w ->
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |= φ)> /\
          <[ {k i}, w |= AX (φ AU ret
                      {fun (lr: I + X) (w': World E) =>
                         exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
    <( {iter k i}, w |= AG φ )>.
  Proof with auto with ticl.
    intros HR H.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    unfold iter, MonadIter_ctree.
    coinduction RR CIH; intros.
    specialize (H _ _ HR) as (Hφ & H').
    cdestruct H'.
    split2.
    - apply Hφ. 
    - destruct Hs as (k' & wk & TR).
      rewrite unfold_iter.
      apply can_step_bind_l with k' wk...
      specialize (H' _ _ TR).
      now apply aur_ret_not_done in H'.
    - intros t' w' TR.
      rewrite unfold_iter in TR.
      apply ktrans_bind_inv in TR as
          [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ag_bind_chain φ
                 (fun (lr: I+X) (w0: World E) => exists i' : I, lr = inl i' /\ R i' w0)).
        * now apply H'. 
        * intros [l | r] w_ (? & Hinv & HR'); inv Hinv.
          rewrite sb_guard. 
          apply CIH...
      + (* [k x] returns *)        
        specialize (H' _ _ TRt0) as HAN.
        apply aur_stuck in HAN; cdestruct HAN; exfalso; eapply can_step_stuck; eauto.
  Qed.

  (** A loop [iter k i] satisfies [EG φ] if [k i] always terminates with loop invariant [R],
      while the return value of the iteration is always the right-injection [lr = inr r].
      This lemma internalizes powerful coinductive proof techniques to simple lemma application. *)
  Lemma eg_iter{X I} R (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E):
    R i w ->    
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |= φ)> /\
        <[ {k i}, w |= EX (φ EU ret
                    {fun (lr: I + X) (w': World E) =>
                       exists (i': I), lr = inl i' /\ R i' w'}) ]>) ->
    <( {iter k i}, w |= EG φ )>.
  Proof with auto with ticl.
    intros.
    (* coinductive case *)
    generalize dependent i.
    generalize dependent w.
    unfold iter, MonadIter_ctree.
    coinduction RR CIH; intros.
    specialize (H0 _ _ H) as (Hφ & H0').
    cdestruct H0'.
    split.
    - apply Hφ. 
    - exists (lr <- t;; match lr with
                 | inl l => Guard (CTree.iter k l)
                 | inr r => Ret r
                  end), w0; split.
      + rewrite unfold_iter.
        apply ktrans_bind_l...
        now apply eur_ret_not_done in H0'.
      + apply (eg_bind_chain φ
                 (fun (lr: I+X) (w0: World E) => exists i' : I, lr = inl i' /\ R i' w0)).
        * now apply H0'. 
        * intros [l | r] w_ (? & Hinv & HR); inv Hinv.          
          rewrite sb_guard.
          apply CIH...
  Qed.

  (** ** Regime B: iteration through a body with hidden value choice *)
  (** The body may return several indices at once ([brn 2 (fun _ => Ret (inl _))]);
      the termination premise is the world-only [φ AU done R] and the obligation is
      stated one step later ([φ AN (φ AU ψ)]), see [Bind.v]. *)

  (** [φ AN ψ] is a [φ AN (φ AU ψ)] whose successors are all leaves. *)
  Lemma anr_au{X}: forall (t: ctree E B X) w φ ψ,
      <[ t, w |= φ AN ψ ]> ->
      <[ t, w |= φ AN (φ AU ψ) ]>.
  Proof with auto with ticl.
    intros * H.
    cdestruct H; csplit...
    intros t' w' TR; cleft...
  Qed.

  Lemma enr_eu{X}: forall (t: ctree E B X) w φ ψ,
      <[ t, w |= φ EN ψ ]> ->
      <[ t, w |= φ EN (φ EU ψ) ]>.
  Proof with auto with ticl.
    intros * H.
    cdestruct H; csplit...
    exists t0, w0; split...
    cleft...
  Qed.

  Lemma aur_iter_done{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E) (ψ: ticlr E X):
    well_founded Rv ->
    not_done w ->
    Ri i w ->
    (forall (i: I) w,
        not_done w ->
        Ri i w ->
        <[ {k i}, w |= φ AU done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)
                       | inr r => <[ {Ret r: ctree E B X}, w' |= φ AN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AN (φ AU ψ) ]>.
  Proof with auto with ticl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hd Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    eapply aur_bind_r_done with
      (R:=(fun (lr : I + X) (w' : World E) =>
             match lr with
             | inl i' => not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)
             | inr r => <[ {Ret r: ctree E B X}, w' |= φ AN ψ ]>
             end))...
    intros [i' | r] w'...
    - intros (Hd' & Hi' & Hv). 
      rewrite sb_guard.
      remember (i', w') as y.
      replace i' with (fst y) in Hi' |- * by now subst.
      replace w' with (snd y) in Hi', Hd' |- * by now subst.
      apply HindWf...
    - apply anr_au.
  Qed.

  Corollary aur_iter_done_au{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E) (ψ: ticlr E X):
    well_founded Rv ->
    not_done w ->
    Ri i w ->
    (forall (i: I) w,
        not_done w ->
        Ri i w ->
        <[ {k i}, w |= φ AU done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)
                       | inr r => <[ {Ret r: ctree E B X}, w' |= φ AN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ AU ψ ]>.
  Proof.
    intros; cright; eapply aur_iter_done; eauto.
  Qed.

  Lemma eur_iter_done{X I} Ri (Rv: relation (I * World E)) (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E) (ψ: ticlr E X):
    well_founded Rv ->
    not_done w ->
    Ri i w ->
    (forall (i: I) w,
        not_done w ->
        Ri i w ->
        <[ {k i}, w |= φ EU done
                    {fun (lr: I + X) (w': World E) =>
                       match lr with
                       | inl i' => not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)
                       | inr r => <[ {Ret r: ctree E B X}, w' |= φ EN ψ ]>
                       end} ]>) ->
    <[ {iter k i}, w |= φ EN (φ EU ψ) ]>.
  Proof with auto with ticl.
    remember (i, w) as P.
    replace i with (fst P) by now subst.
    replace w with (snd P) by now subst.
    clear HeqP i w.
    intros WfR Hd Hi H.
    generalize dependent k.
    induction P using (well_founded_induction WfR);
      destruct P as (i, w); cbn in *. 
    rename H into HindWf.
    intros.
    unfold iter, MonadIter_ctree.
    rewrite unfold_iter.
    eapply eur_bind_r_done with
      (R:=(fun (lr : I + X) (w' : World E) =>
             match lr with
             | inl i' => not_done w' /\ Ri i' w' /\ Rv (i', w') (i, w)
             | inr r => <[ {Ret r: ctree E B X}, w' |= φ EN ψ ]>
             end))...
    intros [i' | r] w'...
    - intros (Hd' & Hi' & Hv). 
      rewrite sb_guard.
      remember (i', w') as y.
      replace i' with (fst y) in Hi' |- * by now subst.
      replace w' with (snd y) in Hi', Hd' |- * by now subst.
      apply HindWf...
    - apply enr_eu.
  Qed.

  (** [AG] through a body with hidden value choice. The body's first step must be a
      non-returning step ([AX (φ AN …)]): a body [Ret (inl i')] would make [iter] an
      unproductive hidden loop. *)
  Lemma ag_iter_done{X I} (R: rel I (World E)) (i: I) w (k: I -> ctree E B (I + X)) φ:
    R i w ->
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |= φ )> /\
        <[ {k i}, w |= AX (φ AN (φ AU done
                      {fun (lr: I + X) (w': World E) =>
                         exists i', lr = inl i' /\ R i' w'})) ]>) ->
    <( {iter k i}, w |= AG φ )>.
  Proof with auto with ticl.
    intros HR H.
    generalize dependent i.
    generalize dependent w.
    unfold iter, MonadIter_ctree.
    coinduction RR CIH; intros.
    specialize (H _ _ HR) as (Hφ & H').
    cdestruct H'.
    split2.
    - apply Hφ.
    - destruct Hs as (k' & wk & TR).
      rewrite unfold_iter.
      apply can_step_bind_l with k' wk...
      specialize (H' _ _ TR) as HAN.
      cdestruct HAN.
      eapply ticll_not_done; eauto.
    - intros t' w' TR.
      rewrite unfold_iter in TR.
      apply ktrans_bind_inv in TR as
          [(t0' & TR0 & Hd_ & Heq) | (x' & w0 & TRt0 & Hd & TRk)].
      + (* [k x] steps *)
        rewrite Heq; clear Heq t'.
        apply (ag_bind_done_chain φ
                 (fun (lr: I+X) (w0: World E) => exists i' : I, lr = inl i' /\ R i' w0))...
        * cright; now apply H'.
        * intros [l | r] w_ (? & Hinv & HR'); inv Hinv.
          rewrite sb_guard.
          apply CIH...
      + (* [k x] returns immediately: contradicts [AX (φ AN …)] *)
        specialize (H' _ _ TRt0) as HAN.
        now apply anr_stuck in HAN.
  Qed.

  Lemma eg_iter_done{X I} (R: rel I (World E)) (i: I) w (k: I -> ctree E B (I + X)) (φ: ticll E):
    R i w ->
    (forall (i: I) w,
        R i w ->
        <( {iter k i}, w |= φ )> /\
        <[ {k i}, w |= EX (φ EN (φ EU done
                      {fun (lr: I + X) (w': World E) =>
                         exists i', lr = inl i' /\ R i' w'})) ]>) ->
    <( {iter k i}, w |= EG φ )>.
  Proof with auto with ticl.
    intros HR H.
    generalize dependent i.
    generalize dependent w.
    unfold iter, MonadIter_ctree.
    coinduction RR CIH; intros.
    specialize (H _ _ HR) as (Hφ & H').
    cdestruct H'.
    assert (Hd0: not_done w0) by (cdestruct H'; eapply ticll_not_done; eauto).
    split.
    - apply Hφ.
    - exists (lr <- t;; match lr with
                 | inl l => Guard (CTree.iter k l)
                 | inr r => Ret r
                  end), w0; split.
      + rewrite unfold_iter.
        apply ktrans_bind_l...
      + apply (eg_bind_done_chain φ
                 (fun (lr: I+X) (w0: World E) => exists i' : I, lr = inl i' /\ R i' w0))...
        * cright; apply H'.
        * intros [l | r] w_ (? & Hinv & HR'); inv Hinv.
          rewrite sb_guard.
          apply CIH...
  Qed.

End IterLemmas.
