From Coq Require Import
  ZArith.ZArith
  ZArith.Zwf
  Strings.String.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList
  Data.String.

From CTree Require Import
  CTree.Core
  CTree.SBisim
  CTree.Equ
  CTree.Interp.State
  CTree.Events.State
  CTree.Events.Writer.

From CTree Require Import
  Logic.Ctl
  Logic.Trans
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.Bind
  CTree.Logic.CanStep
  CTree.Logic.State.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
Local Open Scope Z_scope.

Generalizable All Variables.

Module Clang.
  Definition Ctx := alist string Z.
  Definition Mem := stateE Ctx.

  Definition assert(k: string)(p: Z -> Prop)(m: Ctx): Prop :=
    match lookup k m with
    | Some v => p v
    | None => False
    end.

  Definition load(k: string)(m: Ctx): Z :=
    match lookup k m with
    | Some v => v
    | None => 0%Z
    end.
    
  Inductive CExp :=
  | CVar (x: string)
  | CConst (z: Z)
  | CAdd (x y: CExp)
  | CSub (x y: CExp).

  Coercion CVar: string >-> CExp.
  Coercion CConst: Z >-> CExp.
  
  Variant CComp := CEq | CGte | CGt.
  
  Inductive CProg :=
  | CAssgn (x: string) (e: CExp)
  | CIf (c: CComp) (l r: CExp) (t: CProg) (e: CProg)
  | CWhile (c: CComp) (l r: CExp) (b: CProg)
  | CSkip
  | CSeq (l r: CProg).

  Definition cdenote_comp(c: CComp): Z -> Z -> bool :=
    match c with
    | CGte => fun a b => a >=? b
    | CGt => fun a b => a >? b
    | CEq => fun a b => a =? b
    end.

  Fixpoint cdenote_exp(e: CExp)(ctx: Ctx): Z :=
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

  Fixpoint cdenote (s: CProg ): ctree Mem unit :=
    match s with
    | CAssgn x e =>
        m <- get ;;    
        let v := cdenote_exp e m in
        put (add x v m)
    | CIf c l r t e =>
        m <- get ;;    
        let vl := cdenote_exp l m in
        let vr := cdenote_exp r m in
        if cdenote_comp c vl vr then
          cdenote t
        else
          cdenote e
    | CWhile c l r b =>       
        Ctree.iter
          (fun _ =>
             m <- get ;;    
             let vl := cdenote_exp l m in
             let vr := cdenote_exp r m in
             if cdenote_comp c vl vr then
               cdenote b ;;
               continue
             else
               break) tt
    | CSkip => Ret tt        
    | CSeq l r =>
        cdenote l ;;
        cdenote r
    end.

  Definition instr_cprog(p: CProg) (ctx: Ctx) : ctreeW Ctx (unit * Ctx) :=
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


  Notation "'if' c '=' z 'then' t 'else' e" :=
    (CIf CEq c z t e) (in custom clang at level 63): ctree_scope.

  Notation "'if' c '>=' z 'then' t 'else' e" :=
    (CIf CGte c z t e) (in custom clang at level 63): ctree_scope.

  Notation "'if' c '>' z 'then' t 'else' e" :=
    (CIf CGt c z t e) (in custom clang at level 63): ctree_scope.

  Notation "'if' c '>=' z 'then' t 'done'" :=
    (CIf CGte c z t CSkip) (in custom clang at level 63): ctree_scope.

  Notation "'if' c '>' z 'then' t 'done'" :=
    (CIf CGt c z t CSkip) (in custom clang at level 63): ctree_scope.

  Notation "'if' c '=' z 'then' t 'done'" :=
    (CIf CEq c z t CSkip) (in custom clang at level 63): ctree_scope.

  Notation "'while' c '=' z 'do' b 'done'" :=
    (CWhile CEq c z b) (in custom clang at level 63): ctree_scope.
  
  Notation "'while' c '>' z 'do' b 'done'" :=
    (CWhile CGt c z b) (in custom clang at level 63): ctree_scope.

  Notation "'while' c '>=' z 'do' b 'done'" :=
    (CWhile CGte c z b) (in custom clang at level 63): ctree_scope.

  Notation "'skip'" :=
    (CSkip) (in custom clang at level 63): ctree_scope.

  Notation "t1 ;;; t2" := (CSeq t1 t2) (in custom clang at level 62, right associativity): clang_scope.

  (*| Assertion (base case) |*)
  Lemma vis_c_assert{X}: forall (p: ctreeW Ctx X) c v m φ,
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
      <[ {instr_cprog [[ skip ]] ctx'}, {Obs (Log ctx') tt} |= φ ]> ->
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
    rewrite interp_state_ret in H1 |- *.
    apply aur_ret.
    cleft...
  Qed.
  
  Lemma aul_cprog_assgn: forall x a ctx ctx' w φ ψ,
      ctx' = add x (cdenote_exp a ctx) ctx ->
      <( {instr_cprog [[ x := a ]] ctx}, w |= ψ )> ->
      <( {instr_cprog [[ skip ]] ctx'}, {Obs (Log ctx') tt} |= φ )> ->
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
    rewrite interp_state_ret in H1 |- *.
    apply aul_ret.
    cleft...
  Qed.
  
  Lemma eur_cprog_assgn: forall x a ctx w φ R,
      φ w ->
      not_done w ->
      R (add x (cdenote_exp a ctx) ctx) ->
      <[ {instr_cprog [[ x := a ]] ctx}, w
          |= <( now φ )> EU EX done {fun '(_, ctx') w' =>
                                        R ctx' /\ w' = Obs (Log ctx') tt} ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    cbn; intros; subst.
    eapply eur_state_bind_r_eq...
    - cleft...
      unfold get, put, trigger.
      rewrite interp_state_vis; cbn.
      rewrite bind_ret_l, sb_guard, interp_state_ret.
      eapply enr_done; intuition.
      + csplit...
      + exists (ctx, ctx); intuition.
    - unfold put, trigger.
      rewrite interp_state_vis; cbn.
      rewrite bind_bind.
      eapply eur_log...
      + rewrite bind_ret_l, sb_guard, interp_state_ret.
        cleft.
        eapply enr_done; intuition.
        * csplit...
        * exists (tt, add x (cdenote_exp a ctx) ctx).
          intuition.
  Qed.

  Lemma eur_cprog_assgn_eq: forall x a ctx w φ,
      φ w ->
      not_done w ->
      let ctx' := add x (cdenote_exp a ctx) ctx in
      <[ {instr_cprog [[ x := a ]] ctx}, w
          |= <( now φ )> EU EX done= {(tt, ctx')}
                                        {Obs (Log ctx') tt} ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    cbn; intros; subst.
    eapply eur_state_bind_r_eq...
    - cleft...
      unfold get, put, trigger.
      rewrite interp_state_vis; cbn.
      rewrite bind_ret_l, sb_guard, interp_state_ret.
      eapply enr_done; intuition.
      + csplit...
      + exists (ctx, ctx); intuition.
    - unfold put, trigger.
      rewrite interp_state_vis; cbn.
      rewrite bind_bind.
      eapply eur_log...
      + rewrite bind_ret_l, sb_guard, interp_state_ret.
        cleft.
        eapply enr_done; intuition.
        * csplit...
        * exists (tt, add x (cdenote_exp a ctx) ctx).
          intuition.
  Qed.
    
  (*| Sequence: structural temporal lemmas |*)
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
  Lemma aul_cprog_ite_gte: forall a b ctx w φ ψ t f,
      (if cdenote_exp a ctx >=? cdenote_exp b ctx then        
         <( {instr_cprog t ctx}, w |= φ AU ψ )>
       else
         <( {instr_cprog f ctx}, w |= φ AU ψ )>) ->
      <( {instr_cprog [[ if a >= b then t else f ]] ctx}, w |= φ AU ψ )>.
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
      destruct (cdenote_exp a ctx >=? cdenote_exp b ctx).
      + now apply ctll_not_done in H.
      + now apply ctll_not_done in H.
      + unfold resum_ret, ReSumRet_refl.
        intuition.
    - destruct (cdenote_exp a ctx >=? cdenote_exp b ctx)...
  Qed.

  Lemma aul_cprog_ite_gt: forall a b ctx w φ ψ t f,
      (if cdenote_exp a ctx >? cdenote_exp b ctx then        
         <( {instr_cprog t ctx}, w |= φ AU ψ )>
       else
         <( {instr_cprog f ctx}, w |= φ AU ψ )>) ->
      <( {instr_cprog [[ if a > b then t else f ]] ctx}, w |= φ AU ψ )>.
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
      destruct (cdenote_exp a ctx >? cdenote_exp b ctx).
      + now apply ctll_not_done in H.
      + now apply ctll_not_done in H.
      + unfold resum_ret, ReSumRet_refl.
        intuition.
    - destruct (cdenote_exp a ctx >? cdenote_exp b ctx)...
  Qed.

  Lemma eur_cprog_ite_gte: forall a b ctx w φ t f R,
      (if cdenote_exp a ctx >=? cdenote_exp b ctx then        
         <[ {instr_cprog t ctx}, w |= EX (φ EU EX done R) ]>
       else
         <[ {instr_cprog f ctx}, w |= EX (φ EU EX done R) ]>) ->
      <[ {instr_cprog [[ if a >= b then t else f ]] ctx}, w |= EX (φ EU EX done R) ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply enr_state_bind_r_eq.
    - rewrite interp_state_get.
      apply exr_ret.
      + destruct (cdenote_exp a ctx >=? cdenote_exp b ctx); cdestruct H;
          now apply ktrans_not_done in TR.
      + intuition.
    - destruct (cdenote_exp a ctx >=? cdenote_exp b ctx)...
  Qed.

  Lemma eur_cprog_ite_gt: forall a b ctx w φ ψ t f,
      (if cdenote_exp a ctx >? cdenote_exp b ctx then        
         <[ {instr_cprog t ctx}, w |= φ EU EX ψ ]>
       else
         <[ {instr_cprog f ctx}, w |= φ EU EX ψ ]>) ->
      <[ {instr_cprog [[ if a > b then t else f ]] ctx}, w |= φ EU EX ψ ]>.
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
      + destruct (cdenote_exp a ctx >? cdenote_exp b ctx);
          now eapply eur_not_done in H.
      + intuition.
    - unfold resum_ret, ReSumRet_refl.
      destruct (cdenote_exp a ctx >? cdenote_exp b ctx)...
  Qed.
  
  Lemma eul_cprog_ite_gt: forall a b ctx w φ ψ t f,
      (if cdenote_exp a ctx >? cdenote_exp b ctx then        
         <( {instr_cprog t ctx}, w |= φ EU ψ )>
       else
         <( {instr_cprog f ctx}, w |= φ EU ψ )>) ->
      <( {instr_cprog [[ if a > b then t else f ]] ctx}, w |= φ EU ψ )>.
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
      destruct (cdenote_exp a ctx >? cdenote_exp b ctx).
      + now apply ctll_not_done in H.
      + now apply ctll_not_done in H.
      + unfold resum_ret, ReSumRet_refl.
        intuition.
    - destruct (cdenote_exp a ctx >? cdenote_exp b ctx)...
  Qed.

  (*| While loops |*)
  Lemma afl_cprog_while_unfold: forall a b t w w' φ ctx ctx',
      cdenote_exp a ctx > cdenote_exp b ctx ->
      not_done w' ->
      <[ {instr_cprog t ctx}, w |= AF AX done={(tt, ctx')} w' ]> ->
      <( {instr_cprog [[ while a > b do t done ]] ctx'}, w' |= AF φ )> ->   
      <( {instr_cprog [[ while a > b do t done ]] ctx}, w |= AF φ )>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE; cbn; intros.
    rewrite unfold_iter.
    eapply aul_state_bind_r_eq.
    - rewrite interp_state_bind.
      eapply aur_bind_r_eq.
      + rewrite interp_state_get.
        cleft...
        apply axr_ret.
        * now apply aur_not_done in H1.
        * intuition.
      + cbn.
        apply Z.gtb_gt in H; rewrite H.
        eapply aur_state_bind_r_eq...
        rewrite interp_state_ret.
        cleft.
        eapply axr_ret...
    - cbn.
      rewrite unfold_interp_state; cbn.
      rewrite sb_guard.
      apply H2.
  Qed.

  Lemma aur_cprog_while_unfold: forall a b t w w' φ ψ ctx ctx',
      cdenote_exp a ctx > cdenote_exp b ctx ->
      not_done w' ->
      <[ {instr_cprog t ctx}, w |= ψ AU AX done={(tt, ctx')} w' ]> ->
      <[ {instr_cprog [[ while a > b do t done ]] ctx'}, w' |= ψ AU φ ]> ->   
      <[ {instr_cprog [[ while a > b do t done ]] ctx}, w |= ψ AU φ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE; cbn; intros.
    rewrite unfold_iter.
    eapply aur_state_bind_r_eq.
    - rewrite interp_state_bind.
      eapply aur_bind_r_eq.
      + rewrite interp_state_get.
        cleft...
        apply axr_ret.
        * now apply aur_not_done in H1.
        * intuition.
      + cbn.
        apply Z.gtb_gt in H; rewrite H.
        eapply aur_state_bind_r_eq...
        rewrite interp_state_ret.
        cleft.
        eapply axr_ret...
    - cbn.
      rewrite unfold_interp_state; cbn.
      rewrite sb_guard.
      apply H2.
  Qed.

  (* Termination *)
  Theorem aur_cprog_while ctx (t: CProg) w a b φ ψ:    
    (if cdenote_exp a ctx >? cdenote_exp b ctx then
       not_done w
    else
      <[ {Ret (tt, ctx)}, w |= φ AN ψ ]>)
      ->
    (forall ctx w',
        (if cdenote_exp a ctx >? cdenote_exp b ctx then
          not_done w'
        else
          <[ {Ret (tt, ctx)}, w' |= φ AN ψ ]>)
      ->
        <[ {instr_cprog t ctx}, w' |= φ AU AX done
          {fun '(_, ctx') w' =>
             let va := cdenote_exp a ctx in
             let vb := cdenote_exp b ctx in
             let va' := cdenote_exp a ctx' in
             let vb' := cdenote_exp b ctx' in             
             (Z.abs_nat (va' - vb') < Z.abs_nat (va - vb))%nat
             /\ if va' >? vb' then
                 not_done w'
               else 
                 <[ {Ret (tt, ctx')}, w'|= φ AN ψ ]>
        } ]>) ->
    <[ {instr_cprog [[ while a > b do t done ]] ctx}, w |= φ AU ψ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE; cbn; intros.
    eapply aur_state_iter_nat with
      (Ri:= fun 'tt ctx' w' =>
              if cdenote_exp a ctx' >? cdenote_exp b ctx' then
                not_done w'
              else 
                <[ {Ret (tt, ctx')}, w' |= φ AN ψ ]>
      )
      (f:= fun _ ctx _ =>             
             Z.abs_nat (cdenote_exp a ctx - cdenote_exp b ctx))...
    - destruct (cdenote_exp a ctx >? cdenote_exp b ctx) eqn:Hab.
      + intuition.
      + cdestruct H.
        now apply can_step_not_done in Hs.
    - intros [] ctx' w' Hd Hif. 
      eapply aur_state_bind_r_eq.
      + rewrite interp_state_get.
        cleft.
        apply axr_ret...
      + specialize (H0 ctx' w' Hif).
        destruct (cdenote_exp a ctx' >? cdenote_exp b ctx') eqn:Hab.
        * eapply aur_state_bind_r.
          -- apply H0...
          -- intros [] ctx_ w_  Hif'.
             destruct Hif' as (Hf & Hif').
             rewrite interp_state_ret.
             cleft.
             destruct (cdenote_exp a ctx_ >? cdenote_exp b ctx_) eqn:Heq_;
               apply axr_ret...
             ++ intuition.
                rewrite Heq_...
             ++ cdestruct Hif'.
                now apply can_step_not_done in Hs.
             ++ split2...
                ** cdestruct Hif'.
                   now apply can_step_not_done in Hs.
                ** rewrite Heq_...
        * rewrite interp_state_ret.
          cleft.
          apply axr_ret...
          now cright.
  Qed.
  
  Lemma ag_cprog_while_gt: forall a b (t: CProg) R ctx w' φ,
      R ctx ->
      cdenote_exp a ctx > cdenote_exp b ctx ->
      w' = Obs (Log ctx) tt ->
      (forall ctx,
          R ctx ->
          <( {instr_cprog [[ while a > b do t done ]] ctx}, {Obs (Log ctx) tt} |= φ )> /\
            <[ {instr_cprog t ctx}, {Obs (Log ctx) tt} |= AX (φ AU AX done
             {fun '(_, ctx') w' =>
                cdenote_exp a ctx' > cdenote_exp b ctx'
                /\ w' = Obs (Log ctx') tt
                /\ R ctx' }) ]>) ->
    <( {instr_cprog [[ while a > b do t done ]] ctx}, w' |= AG φ )>.
  Proof with eauto with ctl.
    intros; subst.
    eapply ag_state_iter with (R:=fun 'tt ctx' w' =>
                                    cdenote_exp a ctx' > cdenote_exp b ctx'
                                    /\ w' = Obs (Log ctx') tt
                                    /\ R ctx')...
    intros [] ctx' w' Hd (Hcmp & -> & HR).
    destruct (H2 _ HR); split...
    eapply anr_state_bind_r_eq.
    - rewrite interp_state_get.
      apply axr_ret...
    - cbn.
      apply Z.gtb_gt in Hcmp; rewrite Hcmp.
      rewrite interp_state_bind.      
      cdestruct H3.
      csplit...
      + destruct Hs as (? & ? & TR').
        eapply can_step_bind_l...
        specialize (H3 _ _ TR').
        cdestruct H3; cdestruct H3; now apply can_step_not_done in Hs.
      + intros t' w' TR'...
        apply ktrans_bind_inv in TR' as [(? & ? & ? & ?) | (? & ? & ? & ?)].
        * rewrite H6.
          apply aur_bind_r with (R:=fun '(_, ctx') (w'0 : WorldW Ctx) =>
                       cdenote_exp a ctx' > cdenote_exp b ctx' /\
                         w'0 = Obs (Log ctx') tt /\ R ctx')...
          intros [_ ctx_] w_ (Hcmp_ & -> & ?).
          rewrite interp_state_ret.
          cleft.
          apply axr_ret...
          exists tt; intuition.
        * destruct H5, x; rewrite interp_state_ret in H6.
          specialize (H3 _ _ H4).
          apply aur_stuck in H3.
          now apply anr_stuck in H3.
  Qed.

 Lemma ag_cprog_while_eq: forall a b (t: CProg) R ctx w' φ,
      R ctx ->
      cdenote_exp a ctx = cdenote_exp b ctx ->
      w' = Obs (Log ctx) tt ->
      (forall ctx,
          R ctx ->
          <( {instr_cprog [[ while a = b do t done ]] ctx}, {Obs (Log ctx) tt} |= φ )> /\
            <[ {instr_cprog t ctx}, {Obs (Log ctx) tt} |= AX (φ AU AX done
             {fun '(_, ctx') w' =>
                cdenote_exp a ctx' = cdenote_exp b ctx'
                /\ w' = Obs (Log ctx') tt
                /\ R ctx' }) ]>) ->
    <( {instr_cprog [[ while a = b do t done ]] ctx}, w' |= AG φ )>.
  Proof with eauto with ctl.
    intros; subst.
    eapply ag_state_iter with (R:=fun 'tt ctx' w' =>
                                    cdenote_exp a ctx' = cdenote_exp b ctx'
                                    /\ w' = Obs (Log ctx') tt
                                    /\ R ctx')...
    intros [] ctx' w' Hd (Hcmp & -> & HR).
    destruct (H2 _ HR); split...
    eapply anr_state_bind_r_eq.
    - rewrite interp_state_get.
      apply axr_ret...
    - cbn.
      rewrite Hcmp, Z.eqb_refl.
      rewrite interp_state_bind.      
      cdestruct H3.
      csplit...
      + destruct Hs as (? & ? & TR').
        eapply can_step_bind_l...
        specialize (H3 _ _ TR').
        cdestruct H3; cdestruct H3; now apply can_step_not_done in Hs.
      + intros t' w' TR'...
        apply ktrans_bind_inv in TR' as [(? & ? & ? & ?) | (? & ? & ? & ?)].
        * rewrite H6.
          apply aur_bind_r with (R:=fun '(_, ctx') (w'0 : WorldW Ctx) =>
                       cdenote_exp a ctx' = cdenote_exp b ctx' /\
                         w'0 = Obs (Log ctx') tt /\ R ctx')...
          intros [_ ctx_] w_ (Hcmp_ & -> & ?).
          rewrite interp_state_ret.
          cleft.
          apply axr_ret...
          exists tt; intuition.
        * destruct H5, x; rewrite interp_state_ret in H6.
          specialize (H3 _ _ H4).
          apply aur_stuck in H3.
          now apply anr_stuck in H3.
  Qed.
  
  Lemma eg_cprog_while_gt: forall a b (t: CProg) R ctx w' φ,
      R ctx ->
      cdenote_exp a ctx > cdenote_exp b ctx ->
      w' = Obs (Log ctx) tt ->
      (forall ctx,
          R ctx ->
          <( {instr_cprog [[ while a > b do t done ]] ctx}, {Obs (Log ctx) tt} |= φ )> /\
            <[ {instr_cprog t ctx}, {Obs (Log ctx) tt} |= EX (φ EU EX done
             {fun '(_, ctx') w' =>
                cdenote_exp a ctx' > cdenote_exp b ctx'
                /\ w' = Obs (Log ctx') tt
                /\ R ctx' }) ]>) ->
    <( {instr_cprog [[ while a > b do t done]] ctx}, w' |= EG φ )>.
  Proof with eauto with ctl.
    intros; subst.
    eapply eg_state_iter with (R:=fun 'tt ctx' w' =>
                                    cdenote_exp a ctx' > cdenote_exp b ctx'
                                    /\ w' = Obs (Log ctx') tt
                                    /\ R ctx')...
    intros [] ctx' w' Hd (Hcmp & -> & HR).
    destruct (H2 _ HR); split...
    eapply enr_state_bind_r_eq.
    - rewrite interp_state_get.
      apply exr_ret...
    - cbn.
      apply Z.gtb_gt in Hcmp; rewrite Hcmp.
      rewrite interp_state_bind.
      cdestruct H3.
      csplit...
      exists ('(_, s) <- t0 ;; interp_state h_stateW (continue) s), w.
      split.
      + apply ktrans_bind_l...
        now apply eur_not_done in H3.
      + eapply eur_bind_r...
        intros [_ ctx_] w_ (Hcmp' & -> & HR').
        rewrite interp_state_ret.
        cleft.
        apply exr_ret...
        exists tt; intuition.
  Qed.

  Lemma eg_cprog_while_eq: forall a b (t: CProg) R ctx w' φ,
      R ctx ->
      cdenote_exp a ctx = cdenote_exp b ctx ->
      w' = Obs (Log ctx) tt ->
      (forall ctx,
          R ctx ->
          <( {instr_cprog [[ while a = b do t done ]] ctx}, {Obs (Log ctx) tt} |= φ )> /\
            <[ {instr_cprog t ctx}, {Obs (Log ctx) tt} |= EX (φ EU EX done
             {fun '(_, ctx') w' =>
                cdenote_exp a ctx' = cdenote_exp b ctx'
                /\ w' = Obs (Log ctx') tt
                /\ R ctx' }) ]>) ->
    <( {instr_cprog [[ while a = b do t done ]] ctx}, w' |= EG φ )>.
  Proof with eauto with ctl.
    intros; subst.
    eapply eg_state_iter with (R:=fun 'tt ctx' w' =>
                                    cdenote_exp a ctx' = cdenote_exp b ctx'
                                    /\ w' = Obs (Log ctx') tt
                                    /\ R ctx')...
    intros [] ctx' w' Hd (Hcmp & -> & HR).
    destruct (H2 _ HR); split...
    eapply enr_state_bind_r_eq.
    - rewrite interp_state_get.
      apply exr_ret...
    - cbn.
      rewrite Hcmp; cbn; rewrite Z.eqb_refl.
      rewrite interp_state_bind.
      cdestruct H3.
      csplit...
      exists ('(_, s) <- t0 ;; interp_state h_stateW (continue) s), w.
      split.
      + apply ktrans_bind_l...
        now apply eur_not_done in H3.
      + eapply eur_bind_r...
        intros [_ ctx_] w_ (Hcmp' & -> & HR').
        rewrite interp_state_ret.
        cleft.
        apply exr_ret...
        exists tt; intuition.
  Qed.

End Clang.
