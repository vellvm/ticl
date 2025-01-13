From Coq Require Import
  Nat
  Strings.String.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList
  Data.String.

From TICL Require Import
  ICTree.Core
  ICTree.SBisim
  ICTree.Equ
  ICTree.Interp.State
  ICTree.Events.State
  ICTree.Events.Writer.

From TICL Require Import
  Logic.Core
  Logic.Trans
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.EX
  ICTree.Logic.EF
  ICTree.Logic.Bind
  ICTree.Logic.CanStep
  ICTree.Logic.State.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.
Local Open Scope nat_scope.

Generalizable All Variables.

Module StImp.
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
  | CWhile (c: CComp) (b: CProg) 
  | CSkip
  | CSeq (l r: CProg).

  Fixpoint cdenote_exp(e: CExp): ictree Mem nat :=
    match e with
    | CVar v => m <- get ;; Ret (load v m)
    | CConst z => Ret z
    | CAdd a b =>
        x <- cdenote_exp a ;;
        y <- cdenote_exp b ;;
        Ret (x + y)
    | CSub a b =>
        x <- cdenote_exp a ;;
        y <- cdenote_exp b ;;
        Ret (x - y)
    end.

  Definition cdenote_comp(c: CComp): ictree Mem bool :=
    match c with
    | CEq a b =>
        x <- cdenote_exp a ;;
        y <- cdenote_exp b ;;
        Ret (x =? y)
    | CLe a b =>
        x <- cdenote_exp a ;;
        y <- cdenote_exp b ;;
        Ret (x <=? y)
    | CLt a b =>
        x <- cdenote_exp a ;;
        y <- cdenote_exp b ;;
        Ret (x <? y)
    end.

  Fixpoint cdenote_prog (s: CProg): ictree Mem unit :=
    match s with
    | CAssgn x e =>
        v <- cdenote_exp e;;
        m <- get ;;        
        put (add x v m)
    | CIf c t e =>
        bv <- cdenote_comp c ;;
        if bv then
          cdenote_prog t
        else
          cdenote_prog e
    | CWhile c b =>       
        ICtree.iter
          (fun _ =>
             cv <- cdenote_comp c ;;
             if cv then
               bv <- cdenote_prog b ;;
               continue
             else
               break) tt
    | CSkip => Ret tt        
    | CSeq l r =>
        cdenote_prog l ;;
        cdenote_prog r
    end.

  (* Instrumentation of expressions, comparisons and programs *)
  Definition instr_exp(e: CExp) (ctx: Ctx) : ictreeW Ctx (nat * Ctx) :=
    instr_stateE (cdenote_exp e) ctx.

  Definition instr_comp(c: CComp) (ctx: Ctx) : ictreeW Ctx (bool * Ctx) :=
    instr_stateE (cdenote_comp c) ctx.
    
  Definition instr_prog(p: CProg) (ctx: Ctx) : ictreeW Ctx (unit * Ctx) :=
    instr_stateE (cdenote_prog p) ctx.
  
  Declare Scope stimp_scope.
  Local Open Scope stimp_scope.
  Local Open Scope string_scope.
  Declare Custom Entry stimp.
  
  Notation "[[ e ]]" := e (at level 0, e custom stimp at level 95) : stimp_scope.
  Notation "( x )" := x (in custom stimp, x at level 99) : stimp_scope.
  Notation "{ x }" := x (in custom stimp at level 0, x constr): stimp_scope.
  Notation "x" := x (in custom stimp at level 0, x constr at level 0) : stimp_scope.

  Notation "a + b" := (CAdd a b)
                        (in custom stimp at level 50, left associativity) : stimp_scope.

  Notation "a - b" := (CSub a b)
                        (in custom stimp at level 50, left associativity) : stimp_scope.

  Notation "x := c" := (CAssgn x c)
                         (in custom stimp at level 60, right associativity) : stimp_scope.

  Notation "a =? b" := (CEq a b)
                         (in custom stimp at level 52, left associativity) : stimp_scope.
  Notation "a >=? b" := (CLe b a)
                          (in custom stimp at level 52, left associativity) : stimp_scope.
  Notation "a >? b" := (CLt b a)
                         (in custom stimp at level 52, left associativity) : stimp_scope.
  Notation "a <=? b" := (CLe a b)
                          (in custom stimp at level 52, left associativity) : stimp_scope.
  Notation "a <? b" := (CLt a b)
                         (in custom stimp at level 52, left associativity) : stimp_scope.
  
  
  Notation "'if' c 'then' t 'else' e" :=
    (CIf c t e) (in custom stimp at level 63): ictree_scope.

  Notation "'if' c 'then' t 'done'" :=
    (CIf c t CSkip) (in custom stimp at level 63): ictree_scope.

  Notation "'while' c 'do' b 'done'" :=
    (CWhile c b) (in custom stimp at level 63): ictree_scope.

  Notation "'skip'" :=
    (CSkip) (in custom stimp at level 63): ictree_scope.

  Notation "t1 ;;; t2" := (CSeq t1 t2) (in custom stimp at level 62, right associativity): stimp_scope.
  
  Notation "'var' x '=' c" :=
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log ctx as z := pat return (encode z -> Prop) in
                       fun 'tt => lookup x ctx = Some c)))
      (in custom ticll at level 75): ticl_scope.

  Notation "'var' x '<' c" :=
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log ctx as z := pat return (encode z -> Prop) in
                       fun 'tt => exists v, lookup x ctx = Some v /\ v < c)))
      (in custom ticll at level 75): ticl_scope.

  Notation "'var' x '<=' c" :=
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log ctx as z := pat return (encode z -> Prop) in
                       fun 'tt => exists v, lookup x ctx = Some v /\ v <= c)))
      (in custom ticll at level 75): ticl_scope.

  Notation "'var' x '>' c" :=
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log ctx as z := pat return (encode z -> Prop) in
                       fun 'tt => exists v, lookup x ctx = Some v /\ v > c)))
      (in custom ticll at level 75): ticl_scope.

  Notation "'var' x '>=' c" :=
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log ctx as z := pat return (encode z -> Prop) in
                       fun 'tt => exists v, lookup x ctx = Some v /\ v >= c)))
      (in custom ticll at level 75): ticl_scope.
  
  (*| Equality in context |*)
  Lemma var_eq{X}: forall (p: ictreeW Ctx X) c v m,
      <( p, {Obs (Log (add c v m)) tt} |= var c = v )>.
  Proof.
    intros.
    apply ticll_vis; constructor.
    pose proof (mapsto_lookup c v (add c v m)).
    pose proof (mapsto_add_eq m c v).
    rewrite <- H in H0.
    now rewrite H0.
  Qed.

  Lemma var_neq{X}: forall (p: ictreeW Ctx X) c c' v v' m,
      <( p, {Obs (Log m) tt} |= var c = v )> ->
      c <> c' ->
      <( p, {Obs (Log (add c' v' m)) tt} |= var c = v )>.
  Proof.
    intros.
    apply ticll_vis; constructor.
    rewrite mapsto_lookup.
    apply mapsto_add_neq with (R:=eq); eauto. 
    inv H.
    dependent destruction H1.
    apply mapsto_lookup; auto.
    Unshelve.
    typeclasses eauto.
  Qed.
  
  (*| Assignment: structural temporal lemmas |*)
  Lemma aur_cprog_assgn: forall x a ctx r w R ψ,
      <[ {instr_exp a ctx}, w |= AX done= {(r, ctx)} w ]> ->
      <( {log (add x r ctx)}, w |= ψ )> ->
      R (tt, add x r ctx) (Obs (Log (add x r ctx)) tt) ->
      <[ {instr_prog [[ x := a ]] ctx}, w |= ψ AU AX done R ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_exp.
    intros; cbn.
    eapply aur_state_bind_r_eq.
    - cleft...
    - eapply aur_state_bind_r_eq.
      + eapply aur_get...
        apply ticll_not_done in H0...
      + eapply aur_put...
  Qed.
  
  (*| Sequence: structural temporal lemmas |*)
  Lemma anr_cprog_seq: forall a b ctx ctx' w w' φ ψ,
      <[ {instr_prog a ctx}, w |= ψ AN done= {(tt,ctx')} w' ]> ->
      <[ {instr_prog b ctx'}, w' |= ψ AN φ ]> ->
      <[ {instr_prog [[ a ;;; b ]] ctx}, w |= ψ AN φ ]>.
  Proof.
    unfold instr_prog. 
    intros; cbn.
    eapply anr_state_bind_r_eq; eauto.
  Qed.
  
  Lemma aur_cprog_seq: forall a b ctx ctx' w w' φ ψ,
      <[ {instr_prog a ctx}, w |= φ AU AX done= {(tt,ctx')} w' ]> ->
      <[ {instr_prog b ctx'}, w' |= φ AU ψ ]> ->
      <[ {instr_prog [[ a ;;; b ]] ctx}, w |= φ AU ψ ]>.
  Proof.
    unfold instr_prog.
    intros; cbn.
    eapply aur_state_bind_r_eq; eauto.
  Qed.
  
  Lemma aul_cprog_seq: forall a b ctx ctx' w w' φ ψ,
      <[ {instr_prog a ctx}, w |= φ AU AX done= {(tt,ctx')} w' ]> ->
      <( {instr_prog b ctx'}, w' |= φ AU ψ )> ->
      <( {instr_prog [[ a ;;; b ]] ctx}, w |= φ AU ψ )>.
  Proof.
    unfold instr_prog. 
    intros; cbn.
    eapply aul_state_bind_r_eq; eauto.
  Qed.
  
  Lemma ag_cprog_seq: forall a b ctx ctx' w w' φ,
      <[ {instr_prog a ctx}, w |= φ AU AX done= {(tt,ctx')} w' ]> ->
      <( {instr_prog b ctx'}, w' |= AG φ )> ->
      <( {instr_prog [[ a ;;; b ]] ctx}, w |= AG φ )>.
  Proof.
    unfold instr_prog. 
    intros; cbn.
    eapply ag_state_bind_r_eq; eauto.
  Qed.

  (*| Conditional: structural temporal lemmas |*)
  Lemma aul_cprog_ite: forall c ctx w φ ψ (b: bool) t f,
      <[ {instr_comp c ctx}, w |= AX done= {(b, ctx)} w ]> ->
      (if b then
         <( {instr_prog t ctx}, w |= φ AU ψ )>
       else
         <( {instr_prog f ctx}, w |= φ AU ψ )>) ->
      <( {instr_prog [[ if c then t else f ]] ctx}, w |= φ AU ψ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp. 
    intros; cbn.
    eapply aul_state_bind_r_eq.
    - cleft...
    - destruct b...
  Qed.

  Lemma aur_cprog_ite: forall c ctx w φ ψ (b: bool) t f,
      <[ {instr_comp c ctx}, w |= AX done= {(b, ctx)} w ]> ->
      (if b then
         <[ {instr_prog t ctx}, w |= φ AU ψ ]>
       else
         <[ {instr_prog f ctx}, w |= φ AU ψ ]>) ->
      <[ {instr_prog [[ if c then t else f ]] ctx}, w |= φ AU ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp. 
    intros; cbn.
    eapply aur_state_bind_r_eq.
    - cleft...
    - destruct b...
  Qed.

  (*| While loops |*)
  Lemma aul_cprog_while_true: forall c t w w' φ ψ ctx ctx',
      <[ {instr_comp c ctx}, w |= AX done={(true, ctx)} w ]> ->
      <[ {instr_prog t ctx}, w |= φ AU AX done={(tt, ctx')} w' ]> ->
      <( {instr_prog [[ while c do t done ]] ctx'}, w' |= φ AU ψ )> ->   
      <( {instr_prog [[ while c do t done ]] ctx}, w |= φ AU ψ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; cbn; intros.
    apply aul_state_iter_next_eq with tt w' ctx'...
    - eapply aur_state_bind_r_eq.
      + cleft...
      + cbn; apply ticll_not_done in H1.
        eapply aur_state_bind_r_eq...
        apply aur_state_ret; intuition.
    - apply ticll_not_done in H1...
  Qed.

  Lemma aul_cprog_while_false: forall c t w φ ψ ctx,
      <[ {instr_comp c ctx}, w |= AX done={(false, ctx)} w ]> ->
      <( {Ret (tt, ctx)}, w |= ψ )> ->
      <( {instr_prog [[ while c do t done ]] ctx}, w |= φ AU ψ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; cbn; intros.
    rewrite instr_state_unfold_iter.
    eapply aul_bind_r_eq.
    - eapply aur_state_bind_r_eq.
      + cleft...
      + apply ticll_not_done in H0.
        apply aur_state_ret...
    - cleft...
  Qed.

  Lemma aur_cprog_while_true: forall c t w w' φ ψ ctx ctx',
      <[ {instr_comp c ctx}, w |= AX done={(true, ctx)} w ]> ->
      <[ {instr_prog t ctx}, w |= φ AU AX done={(tt, ctx')} w' ]> ->
      <[ {instr_prog [[ while c do t done ]] ctx'}, w' |= φ AU AX ψ ]> ->   
      <[ {instr_prog [[ while c do t done ]] ctx}, w |= φ AU AX ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; cbn; intros.
    apply aur_state_iter_next_eq with tt w' ctx'...
    - eapply aur_state_bind_r_eq.
      + cleft...
      + cbn. 
        eapply aur_state_bind_r_eq...
        apply aur_state_ret; intuition.
        now apply aur_not_done in H1.
    - now apply aur_not_done in H1. 
  Qed.

  Lemma aur_cprog_while_false: forall c t w φ ψ ctx,
      <[ {instr_comp c ctx}, w |= AX done={(false, ctx)} w ]> ->
      <[ {Ret (tt, ctx)}, w |= AX ψ ]> ->
      <[ {instr_prog [[ while c do t done ]] ctx}, w |= φ AU AX ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; cbn; intros.
    rewrite instr_state_unfold_iter.
    eapply aur_bind_r_eq.
    - eapply aur_state_bind_r_eq.
      + cleft...
      + apply aur_state_ret...
        cdestruct H.
        apply can_step_not_done in Hs...
    - cleft...
  Qed.  
  
  (* Termination *)
  Theorem aur_cprog_while_termination ctx (t: CProg) Ri f w c φ ψ:    
      not_done w ->
      Ri ctx ->
      (forall ctx w (b: bool),
          not_done w ->
          Ri ctx ->
          <[ {instr_comp c ctx}, w |= AX done={(b, ctx)} w ]> /\
          if b then
            <[ {instr_prog t ctx}, w |= φ AU AX done {fun '(_, ctx') w' => not_done w' /\ Ri ctx' /\ f ctx' < f ctx} ]>
          else
            <[ {Ret (tt, ctx)}, w |= φ AN ψ ]>) ->
      <[ {instr_prog [[ while c do t done ]] ctx}, w |= φ AU ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; intros.
    eapply aur_state_iter_nat with
      (Ri:=fun 'tt ctx w => exists (b: bool),
             <[ {instr_stateE (cdenote_comp c) ctx}, w |= AX (done= {(b, ctx)} w) ]> /\
             if b
             then
               <[
                 {instr_stateE (cdenote_prog t) ctx}, {w}
                   |= {φ} AU AX (done {fun '(_, ctx') (w' : WorldW Ctx) => not_done w' /\ Ri ctx' /\ f ctx' < f ctx}) ]>
             else <[ {Ret (tt, ctx)}, {w} |= {φ} AN {ψ} ]>)
      (f:= fun _ ctx _ => f ctx)...
    - intros [] ctx' w' Hd ([] & Hb & HR);
        eapply aur_state_bind_r_eq...
      + cleft...
      + eapply aur_state_bind_r.
        * apply HR.
        * intros; destruct x.
          apply aur_state_ret; intuition.
          exists true...
      + cleft...
      + eapply aur_state_ret...
        Unshelve.
        exact true.
  Qed.

  (* Invariance *)
  Lemma ag_cprog_while: forall c (t: CProg) R ctx w φ,
      R ctx ->
      not_done w ->
      (forall ctx w,
          R ctx ->
          not_done w ->
          <( {instr_prog [[while c do t done ]] ctx}, w |= φ )> /\
          <[ {instr_comp c ctx}, w |= AX done={(true,ctx)} w ]>  /\            
          <[ {instr_prog t ctx}, w |= AX (φ AU AX done {fun '(_, ctx') w' => not_done w' /\ R ctx'}) ]>) ->
    <( {instr_prog [[ while c do t done ]] ctx}, w |= AG φ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp. 
    intros; subst.
    eapply ag_state_iter with (R:=fun 'tt ctx w =>
                                    <( {instr_prog [[while c do t done ]] ctx}, w |= φ )> /\
                                      <[ {instr_comp c ctx}, w |= AX done={(true,ctx)} w ]>  /\            
                                      <[ {instr_prog t ctx}, w |= AX (φ AU AX done {fun '(_, ctx') w' => not_done w' /\ R ctx'}) ]>)...
    - intros [] ctx' w' Hd HR; intuition.
      rewrite interp_state_bind.
      eapply anr_bind_r_eq...
      cbn; rewrite interp_state_bind.
      cdestruct H5.
      csplit...      
      + destruct Hs as (t_ & w_ & TR).
        eapply can_step_bind_l...
        specialize (H5 _ _ TR).
        now apply aur_not_done in H5.
      + intros t_ w_ TR...
        apply ktrans_bind_inv in TR as [(? & TR & Hd_ & ->) | (([] & ctx_) & ? & ? & ? & TR)].
        * specialize (H5 _ _ TR).
          apply aur_bind_r with (R:=fun '(_, ctx') (w' : WorldW Ctx) => not_done w' /\ R ctx')...
          intros [_ ctx_] w'' (Hd'' & HR').
          apply aur_state_ret...
        * specialize (H5 _ _ H3).
          now apply aur_stuck, anr_stuck in H5.
  Qed.
  
End StImp.
