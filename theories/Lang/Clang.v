From Coq Require Import
  Nat
  Strings.String.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList
  Data.String.

From ICTL Require Import
  ICTree.Core
  ICTree.SBisim
  ICTree.Equ
  ICTree.Interp.State
  ICTree.Events.State
  ICTree.Events.Writer.

From ICTL Require Import
  Logic.Ctl
  Logic.Trans
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.EX
  ICTree.Logic.EF
  ICTree.Logic.Bind
  ICTree.Logic.CanStep
  ICTree.Logic.State.

Generalizable All Variables.

Import ICtree ICTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ictree_scope.
Local Open Scope nat_scope.

Generalizable All Variables.

Module Clang.
  Definition Ctx := alist string nat.
  Definition Mem := stateE Ctx.

  Definition assert(k: string)(p: nat -> Prop)(m: Ctx): Prop :=
    match lookup k m with
    | Some v => p v
    | None => False
    end.

  Definition load(k: string)(m: Ctx): nat :=
    match lookup k m with
    | Some v => v
    | None => 0
    end.
    
  Inductive CExp :=
  | CVar (x: string)
  | CConst (z: nat)
  | CAdd (x y: CExp)
  | CSub (x y: CExp).

  Coercion CVar: string >-> CExp.
  Coercion CConst: nat >-> CExp.
  
  Variant CComp :=
    | CEq  (l r: CExp)
    | CLe (l r: CExp)
    | CLt  (l r: CExp).
  
  Inductive CProg :=
  | CAssgn (x: string) (e: CExp)
  | CIf (c: CComp) (t: CProg) (e: CProg)
  | CDoWhile (b: CProg) (c: CComp)
  | CSkip
  | CSeq (l r: CProg).

  Fixpoint cdenote_exp(e: CExp)(ctx: Ctx): nat :=
    match e with
    | CVar v => load v ctx
    | CConst z => z
    | CAdd a b =>
        let x := cdenote_exp a ctx in
        let y := cdenote_exp b ctx in
        (x + y)
    | CSub a b =>
        let x := cdenote_exp a ctx in
        let y := cdenote_exp b ctx in
        (x - y)
    end.

  Definition cdenote_comp(c: CComp)(ctx: Ctx): bool :=
    match c with
    | CEq l r => (cdenote_exp l ctx) =? (cdenote_exp r ctx)
    | CLe l r => (cdenote_exp l ctx) <=? (cdenote_exp r ctx)
    | CLt l r => (cdenote_exp l ctx) <? (cdenote_exp r ctx)
    end.

  Fixpoint cdenote (s: CProg): ictree Mem unit :=
    match s with
    | CAssgn x e =>
        m <- get ;;    
        let v := cdenote_exp e m in
        put (add x v m)
    | CIf c t e =>
        m <- get ;;    
        if cdenote_comp c m then
          cdenote t
        else
          cdenote e
    | CDoWhile b c =>       
        ICtree.iter
          (fun _ =>
             cdenote b ;;
             m <- get ;;
             if cdenote_comp c m then
               continue
             else
               break) tt
    | CSkip => Ret tt        
    | CSeq l r =>
        cdenote l ;;
        cdenote r
    end.

  Definition instr_cprog(p: CProg) (ctx: Ctx) : ictreeW Ctx (unit * Ctx) :=
    instr_stateE (cdenote p) ctx.
  
  Declare Scope clang_scope.
  Local Open Scope clang_scope.
  Local Open Scope string_scope.
  Declare Custom Entry clang.
  
  Notation "[[ e ]]" := e (at level 0, e custom clang at level 95) : clang_scope.
  Notation "( x )" := x (in custom clang, x at level 99) : clang_scope.
  Notation "{ x }" := x (in custom clang at level 0, x constr): clang_scope.
  Notation "x" := x (in custom clang at level 0, x constr at level 0) : clang_scope.

  Notation "a + b" := (CAdd a b)
                        (in custom clang at level 50, left associativity) : clang_scope.

  Notation "a - b" := (CSub a b)
                        (in custom clang at level 50, left associativity) : clang_scope.

  Notation "x := c" := (CAssgn x c)
                         (in custom clang at level 60, right associativity) : clang_scope.

  Notation "a =? b" := (CEq a b)
                         (in custom clang at level 52, left associativity) : clang_scope.
  Notation "a >=? b" := (CLe b a)
                          (in custom clang at level 52, left associativity) : clang_scope.
  Notation "a >? b" := (CLt b a)
                         (in custom clang at level 52, left associativity) : clang_scope.
  Notation "a <=? b" := (CLe a b)
                          (in custom clang at level 52, left associativity) : clang_scope.
  Notation "a <? b" := (CLt a b)
                         (in custom clang at level 52, left associativity) : clang_scope.
  
  
  Notation "'if' c 'then' t 'else' e" :=
    (CIf c t e) (in custom clang at level 63): ictree_scope.

  Notation "'if' c 'then' t 'done'" :=
    (CIf c t CSkip) (in custom clang at level 63): ictree_scope.

  Notation "'do' b 'while' c 'done'" :=
    (CDoWhile b c) (in custom clang at level 63): ictree_scope.

  Notation "'skip'" :=
    (CSkip) (in custom clang at level 63): ictree_scope.

  Notation "t1 ;;; t2" := (CSeq t1 t2) (in custom clang at level 62, right associativity): clang_scope.

  (*| Assertion (base case) |*)
  Lemma vis_c_assert{X}: forall (p: ictreeW Ctx X) c v m φ,
      φ v ->
      <( p, {Obs (Log (add c v m)) tt} |= visW {assert c φ} )>.
  Proof.
    intros.
    apply ctll_vis; constructor.
    unfold assert.
    pose proof (mapsto_lookup c v (add c v m)).
    pose proof (mapsto_add_eq m c v).
    rewrite <- H0 in H1.
    now rewrite H1.
  Qed.

  (*| Assignment: structural temporal lemmas |*)
  Lemma enr_cprog_assgn: forall x a ctx w φ R,
      not_done w ->
      φ w ->
      let ctx' := add x (cdenote_exp a ctx) ctx in
      R (tt, ctx') (Obs (Log ctx') tt) ->
      <[ {instr_cprog [[ x := a]] ctx}, w |= <( now φ )> EN EX done R ]>.
  Proof with eauto with ctl.
    cbn; intros; subst.
    unfold instr_cprog, instr_stateE; cbn.
    eapply enr_state_bind_r_eq.
    - rewrite interp_state_get.
      apply enr_ret.
      + rewrite ctll_now; intuition.
      + intuition.
    - rewrite interp_state_put.
      apply enr_log.
      + apply exr_ret...
      + apply ctll_now; intuition.
  Qed.

  Lemma aur_cprog_assgn: forall x a ctx ctx' w φ ψ,
      ctx' = add x (cdenote_exp a ctx) ctx ->
      <( {instr_cprog [[ x := a ]] ctx}, w |= ψ )> ->
      <[ {Ret (tt, ctx')}, {Obs (Log ctx') tt} |= φ ]> ->
      <[ {instr_cprog [[ x := a ]] ctx}, w |= ψ AU φ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    cbn; intros; subst. 
    unfold get, put, trigger in *.
    rewrite bind_vis in *.
    rewrite interp_state_vis in *; cbn in *.
    rewrite bind_ret_l in *.
    rewrite sb_guard in *.
    rewrite bind_ret_l in *.
    rewrite interp_state_vis in *; cbn in *.
    rewrite bind_bind in *.
    unfold resum_ret, ReSumRet_refl in *.
    cright.
    apply anr_log...
    rewrite bind_ret_l, sb_guard.
    rewrite interp_state_ret. 
    apply aur_ret.
    cleft...
  Qed.
  
  Lemma aul_cprog_assgn: forall x a ctx ctx' w φ ψ,
      ctx' = add x (cdenote_exp a ctx) ctx ->
      <( {instr_cprog [[ x := a ]] ctx}, w |= ψ )> ->
      <( {Ret (tt, ctx')}, {Obs (Log ctx') tt} |= φ )> ->
      <( {instr_cprog [[ x := a ]] ctx}, w |= ψ AU φ )>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    cbn; intros; subst. 
    unfold get, put, trigger in *.
    rewrite bind_vis in *.
    rewrite interp_state_vis in *; cbn in *.
    rewrite bind_ret_l in *.
    rewrite sb_guard in *.
    rewrite bind_ret_l in *.
    rewrite interp_state_vis in *; cbn in *.
    rewrite bind_bind in *.
    unfold resum_ret, ReSumRet_refl in *.
    cright.
    apply anl_log...
    rewrite bind_ret_l, sb_guard.
    rewrite interp_state_ret. 
    apply aul_ret.
    cleft...
  Qed.
      
  (*| Sequence: structural temporal lemmas |*)
  Lemma anr_cprog_seq: forall a b ctx ctx' w w' φ ψ,
      <[ {instr_cprog a ctx}, w |= ψ AN done= {(tt,ctx')} w' ]> ->
      <[ {instr_cprog b ctx'}, w' |= ψ AN φ ]> ->
      <[ {instr_cprog [[ a ;;; b ]] ctx}, w |= ψ AN φ ]>.
  Proof.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply anr_state_bind_r_eq; eauto.
  Qed.
  
  Lemma enr_cprog_seq: forall a b ctx ctx' w w' φ ψ,
      <[ {instr_cprog a ctx}, w |= ψ EN done= {(tt,ctx')} w' ]> ->
      <[ {instr_cprog b ctx'}, w' |= ψ EN φ ]> ->
      <[ {instr_cprog [[ a ;;; b ]] ctx}, w |= ψ EN φ ]>.
  Proof.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply enr_state_bind_r_eq; eauto.
  Qed.
  
  Lemma aur_cprog_seq: forall a b ctx ctx' w w' φ ψ,
      <[ {instr_cprog a ctx}, w |= φ AU AX done= {(tt,ctx')} w' ]> ->
      <[ {instr_cprog b ctx'}, w' |= φ AU ψ ]> ->
      <[ {instr_cprog [[ a ;;; b ]] ctx}, w |= φ AU ψ ]>.
  Proof.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply aur_state_bind_r_eq; eauto.
  Qed.
  
  Lemma aul_cprog_seq: forall a b ctx ctx' w w' φ ψ,
      <[ {instr_cprog a ctx}, w |= φ AU AX done= {(tt,ctx')} w' ]> ->
      <( {instr_cprog b ctx'}, w' |= φ AU ψ )> ->
      <( {instr_cprog [[ a ;;; b ]] ctx}, w |= φ AU ψ )>.
  Proof.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply aul_state_bind_r_eq; eauto.
  Qed.

  Lemma eur_cprog_seq: forall a b ctx ctx' w w' φ ψ,
      <[ {instr_cprog a ctx}, w |= φ EU EX done= {(tt,ctx')} w' ]> ->
      <[ {instr_cprog b ctx'}, w' |= φ EU ψ ]> ->
      <[ {instr_cprog [[ a ;;; b ]] ctx}, w |= φ EU ψ ]>.
  Proof.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply eur_state_bind_r_eq; eauto.
  Qed.
  
  Lemma ag_cprog_seq: forall a b ctx ctx' w w' φ,
      <[ {instr_cprog a ctx}, w |= φ AU AX done= {(tt,ctx')} w' ]> ->
      <( {instr_cprog b ctx'}, w' |= AG φ )> ->
      <( {instr_cprog [[ a ;;; b ]] ctx}, w |= AG φ )>.
  Proof.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply ag_state_bind_r_eq; eauto.
  Qed.

  Lemma eg_cprog_seq: forall a b ctx ctx' w w' φ,
      <[ {instr_cprog a ctx}, w |= φ EU EX done= {(tt,ctx')} w' ]> ->
      <( {instr_cprog b ctx'}, w' |= EG φ )> ->
      <( {instr_cprog [[ a ;;; b ]] ctx}, w |= EG φ )>.
  Proof.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply eg_state_bind_r_eq; eauto.
  Qed.
  
  (*| Conditional: structural temporal lemmas |*)
  Lemma aul_cprog_ite: forall c ctx w φ ψ t f,
      (if cdenote_comp c ctx then
         <( {instr_cprog t ctx}, w |= φ AU ψ )>
       else
         <( {instr_cprog f ctx}, w |= φ AU ψ )>) ->         
      <( {instr_cprog [[ if c then t else f ]] ctx}, w |= φ AU ψ )>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply aul_state_bind_r_eq.
    - unfold get, trigger.
      rewrite interp_state_vis; cbn.
      rewrite bind_ret_l, sb_guard.
      rewrite interp_state_ret.
      cleft.
      eapply axr_ret.
      destruct (cdenote_comp c ctx) eqn:Hc. 
      + now apply ctll_not_done in H.
      + now apply ctll_not_done in H.
      + unfold resum_ret, ReSumRet_refl.
        intuition.
    - destruct (cdenote_comp c ctx) eqn:Hc... 
  Qed.

  Lemma aur_cprog_ite: forall c ctx w φ ψ t f,
      (if cdenote_comp c ctx then
         <[ {instr_cprog t ctx}, w |= φ AU AX ψ ]>
       else
         <[ {instr_cprog f ctx}, w |= φ AU AX ψ ]>) ->   
      <[ {instr_cprog [[ if c then t else f ]] ctx}, w |= φ AU AX ψ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply aur_state_bind_r_eq.
    - unfold get, trigger.
      rewrite interp_state_vis; cbn.
      rewrite bind_ret_l, sb_guard.
      rewrite interp_state_ret.
      cleft.
      eapply axr_ret.
      + destruct (cdenote_comp c ctx) eqn:Hc; 
          now eapply aur_not_done in H.
      + unfold resum_ret, ReSumRet_refl.
        intuition.
    - destruct (cdenote_comp c ctx) eqn:Hc... 
  Qed.

  Lemma eul_cprog_ite: forall c ctx w φ ψ t f,
      (if cdenote_comp c ctx then
         <( {instr_cprog t ctx}, w |= φ EU ψ )>
       else
         <( {instr_cprog f ctx}, w |= φ EU ψ )>) ->   
      <( {instr_cprog [[ if c then t else f ]] ctx}, w |= φ EU ψ )>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply eul_state_bind_r_eq.
    - unfold get, trigger.
      rewrite interp_state_vis; cbn.
      rewrite bind_ret_l, sb_guard.
      rewrite interp_state_ret.
      cleft.
      eapply exr_ret.
      + destruct (cdenote_comp c ctx) eqn:Hc;
          now eapply ctll_not_done in H.
      + intuition.
    - unfold resum_ret, ReSumRet_refl.
      destruct (cdenote_comp c ctx)... 
  Qed.
  
  Lemma eur_cprog_ite: forall c ctx w φ ψ t f,
      (if cdenote_comp c ctx then
         <[ {instr_cprog t ctx}, w |= φ EU EX ψ ]>
       else
         <[ {instr_cprog f ctx}, w |= φ EU EX ψ ]>) ->   
      <[ {instr_cprog [[ if c then t else f ]] ctx}, w |= φ EU EX ψ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply eur_state_bind_r_eq.
    - unfold get, trigger.
      rewrite interp_state_vis; cbn.
      rewrite bind_ret_l, sb_guard.
      rewrite interp_state_ret.
      cleft.
      eapply exr_ret.
      + destruct (cdenote_comp c ctx) eqn:Hc;
          now eapply eur_not_done in H.
      + intuition.
    - unfold resum_ret, ReSumRet_refl.
      destruct (cdenote_comp c ctx)... 
  Qed.
  
  (*| While loops |*)
  Lemma aul_cprog_do_while_true: forall c t w w' φ ψ ctx ctx',
      <[ {instr_cprog t ctx}, w |= φ AU AX done={(tt, ctx')} w' ]> ->
      cdenote_comp c ctx' = true ->
      <( {instr_cprog [[ do t while c done ]] ctx'}, w' |= φ AU ψ )> ->   
      <( {instr_cprog [[ do t while c done ]] ctx}, w |= φ AU ψ )>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE; cbn; intros.
    rewrite unfold_iter.
    eapply aul_state_bind_r_eq.
    - rewrite interp_state_bind.
      eapply aur_bind_r_eq...
      cbn.
      eapply aur_state_bind_r_eq.
      + rewrite interp_state_get.
        cleft...
        apply axr_ret...
        now apply ctll_not_done in H1.
      + destruct (cdenote_comp c ctx'); inv H0.
        rewrite interp_state_ret.
        cleft...
        apply axr_ret...
        now apply ctll_not_done in H1.
    - cbn.
      rewrite unfold_interp_state; cbn.
      rewrite sb_guard...
  Qed.

  Lemma aul_cprog_do_while_false: forall c t w w' φ ψ ctx ctx',
      <[ {instr_cprog t ctx}, w |= φ AU AX done={(tt, ctx')} w' ]> ->
      cdenote_comp c ctx' = false ->
      <( {Ret (tt, ctx')}, w' |= ψ )> ->   
      <( {instr_cprog [[ do t while c done ]] ctx}, w |= φ AU ψ )>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE; cbn; intros.
    rewrite unfold_iter.
    eapply aul_state_bind_r_eq.
    - rewrite interp_state_bind.
      eapply aur_bind_r_eq...
      cbn.
      eapply aur_state_bind_r_eq.
      + rewrite interp_state_get.
        cleft...
        apply axr_ret...
        now apply ctll_not_done in H1.
      + destruct (cdenote_comp c ctx'); inv H0.
        rewrite interp_state_ret.
        cleft...
        apply axr_ret...
        now apply ctll_not_done in H1.
    - cbn.
      rewrite interp_state_ret.
      now cleft.      
  Qed.  

  Lemma aur_cprog_do_while_true: forall c t w w' φ ψ ctx ctx',
      <[ {instr_cprog t ctx}, w |= φ AU AX done={(tt, ctx')} w' ]> ->
      cdenote_comp c ctx' = true ->
      <[ {instr_cprog [[ do t while c done ]] ctx'}, w' |= φ AU AX ψ ]> ->   
      <[ {instr_cprog [[ do t while c done ]] ctx}, w |= φ AU AX ψ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE; cbn; intros.
    rewrite unfold_iter.
    eapply aur_state_bind_r_eq.
    - rewrite interp_state_bind.
      eapply aur_bind_r_eq...
      cbn.
      eapply aur_state_bind_r_eq.
      + rewrite interp_state_get.
        cleft...
        apply axr_ret...
        now apply aur_not_done in H1.
      + destruct (cdenote_comp c ctx'); inv H0.
        rewrite interp_state_ret.
        cleft...
        apply axr_ret...
        now apply aur_not_done in H1.
    - cbn.
      rewrite unfold_interp_state; cbn.
      rewrite sb_guard...
  Qed.

  Lemma aur_cprog_do_while_false: forall c t w w' φ ψ ctx ctx',
      <[ {instr_cprog t ctx}, w |= φ AU AX done={(tt, ctx')} w' ]> ->
      cdenote_comp c ctx' = false ->
      <[ {Ret (tt, ctx')}, w' |= AX ψ ]> ->   
      <[ {instr_cprog [[ do t while c done ]] ctx}, w |= φ AU AX ψ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE; cbn; intros.
    rewrite unfold_iter.
    eapply aur_state_bind_r_eq.
    - rewrite interp_state_bind.
      eapply aur_bind_r_eq...
      cbn.
      eapply aur_state_bind_r_eq.
      + rewrite interp_state_get.
        cleft...
        apply axr_ret...
        cdestruct H1.
        now apply can_step_not_done in Hs.
      + destruct (cdenote_comp c ctx'); inv H0.
        rewrite interp_state_ret.
        cleft...
        apply axr_ret...
        cdestruct H1.
        now apply can_step_not_done in Hs.
    - cbn.
      rewrite interp_state_ret; cbn.
      apply aur_ret.
      now cleft.
  Qed.

  (* Termination *)
  Theorem aur_cprog_do_while_term ctx (t: CProg) Ri f w c φ ψ:    
      not_done w ->
      Ri ctx ->
      (forall ctx w,
          not_done w ->
          Ri ctx ->
          <[ {instr_cprog t ctx}, w |= φ AU AX done {fun '(_, ctx') w' =>
                                                       if cdenote_comp c ctx' then
                                                         not_done w' /\ Ri ctx' /\ f ctx' < f ctx
                                                       else
                                                         <[ {Ret (tt, ctx')}, w' |= φ AN ψ ]>} ]>) -> 
      <[ {instr_cprog [[ do t while c done ]] ctx}, w |= φ AU ψ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE; cbn; intros.
    eapply aur_state_iter_nat with
      (Ri:= fun 'tt ctx' w' => Ri ctx')
      (f:= fun _ ctx _ => f ctx)...             
    - intros [] ctx' w' Hd HR. 
      eapply aur_state_bind_r.
      + apply H1...
      + intros [] ctx_ w_  Hif'.
        eapply aur_state_bind_r_eq.
        * rewrite interp_state_get.
          cleft.
          apply axr_ret...
          destruct (cdenote_comp c ctx_) eqn:Hc.
          -- now destruct Hif'.
          -- cdestruct Hif'.
             now apply can_step_not_done in Hs.
        * destruct (cdenote_comp c ctx_) eqn:Hc;
            rewrite interp_state_ret.
          -- cleft.
             apply axr_ret...
             destruct Hif'...
          -- cleft.
             apply axr_ret...
             cdestruct Hif'.
             now apply can_step_not_done in Hs.
  Qed.

  (* Infinite loops *)
  Lemma ag_cprog_do_while: forall c (t: CProg) R ctx w φ,
      R ctx ->
      not_done w ->
      (forall ctx w,
          R ctx ->
          not_done w ->
          <( {instr_cprog [[do t while c done ]] ctx}, w |= φ )> /\
            <[ {instr_cprog t ctx}, w |= AX (φ AU AX done
                                               {fun '(_, ctx') w' =>
                                                  cdenote_comp c ctx'
                                                  /\ not_done w'
                                                  /\ R ctx' }) ]>) ->
    <( {instr_cprog [[ do t while c done ]] ctx}, w |= AG φ )>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    intros; subst.
    cbn.
    eapply ag_state_iter with (R:=fun 'tt ctx' w' => R ctx')...    
    intros [] ctx' w' Hd HR.
    destruct (H1 _ w' HR Hd); split...
    cdestruct H3.
    rewrite interp_state_bind.
    csplit...
    - destruct Hs as (? & ? & TR').
      eapply can_step_bind_l...
      specialize (H3 _ _ TR').
      cdestruct H3; cdestruct H3; now apply can_step_not_done in Hs.
    - intros t_ w_ TR_...
      apply ktrans_bind_inv in TR_ as [(? & ? & ? & ?) | (? & ? & ? & ?)].
      + rewrite H6.
        apply aur_bind_r with (R:=fun '(_, ctx') (w' : WorldW Ctx) =>
                                    cdenote_comp c ctx' /\ not_done w' /\ R ctx')...
        intros [_ ctx_] w'' (Hcmp_ & Hd'' & ?).
        eapply aur_state_bind_r_eq.
        * rewrite interp_state_get.
          cleft.
          apply axr_ret...
        * destruct (cdenote_comp c ctx_); inv Hcmp_.
          rewrite interp_state_ret.
          cleft.
          apply axr_ret...
      + destruct H5, x.
        specialize (H3 _ _ H4).
        apply aur_stuck in H3.
        now apply anr_stuck in H3.
  Qed.
  
  Lemma eg_cprog_do_while: forall c (t: CProg) R ctx w φ,
      R ctx ->
      not_done w ->
      (forall ctx w,
          R ctx ->
          not_done w ->
          <( {instr_cprog [[do t while c done ]] ctx}, w |= φ )> /\
            <[ {instr_cprog t ctx}, w |= EX (φ EU EX done
                                               {fun '(_, ctx') w' =>
                                                  cdenote_comp c ctx'
                                                  /\ not_done w'
                                                  /\ R ctx' }) ]>) ->
    <( {instr_cprog [[ do t while c done ]] ctx}, w |= EG φ )>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    intros; subst.
    cbn.
    eapply eg_state_iter with (R:=fun 'tt ctx' w' => R ctx')...    
    intros [] ctx' w' Hd HR.
    destruct (H1 _ w' HR Hd); split...
    cdestruct H3.
    rewrite interp_state_bind.
    csplit...
    exists ('(_, s) <- t0 ;; interp_state h_stateW (m <- get;; (if cdenote_comp c m then continue else break)) s), w0.
    split...
    - apply ktrans_bind_l...
      now apply eur_not_done in H3.
    - eapply eur_bind_r...
      intros [_ ctx_] w_ (Hcmp' & Hd' & HR').
      eapply eur_state_bind_r_eq.
      + rewrite interp_state_get.
        cleft.
        apply exr_ret...
      + destruct (cdenote_comp c ctx_); inv Hcmp'.
        rewrite interp_state_ret.
        cleft.
        apply exr_ret...
  Qed.

End Clang.
