From ExtLib Require
  Structures.Maps.
From ExtLib Require Import Data.String.

From Coq Require Import
  ZArith.ZArith
  Strings.String.

From CTree Require Import
  CTree.Core
  CTree.SBisim
  CTree.Equ
  CTree.Interp.State
  CTree.Events.State
  CTree.Events.Writer.

From CTree Require Import
  Logic.Ctl
  CTree.Logic.AX
  CTree.Logic.Bind
  CTree.Logic.State.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
Local Open Scope Z_scope.

Generalizable All Variables.

Module Clang.
  Module M := Maps.
  Context `{MM: @M.Map string Z Ctx}.
  Definition Mem := stateE Ctx.

  Definition assert(k: string)(p: Z -> Prop)(m: Ctx): Prop :=
    match M.lookup k m with
    | Some v => p v
    | None => False
    end.
  
  Definition load(k: string): ctree Mem Z :=
    m <- get ;;
    match M.lookup k m with
    | Some v => Ret v
    | None => Ret 0%Z
    end.

  Definition store(k: string) (v: Z): ctree Mem unit :=
    m <- get ;;    
    put (M.add k v m).

  (* a := f b *)
  Definition update(a: string) (b: string) (f: Z -> Z): ctree Mem unit :=
    m <- get ;;
    match M.lookup b m with
    | Some v => put (M.add a (f v) m)
    | None => put (M.add a (f 0%Z) m)
    end.

  Inductive CExp :=
  | CVar (x: string)
  | CConst (z: Z)
  | CAdd (x y: CExp)
  | CSub (x y: CExp).

  Coercion CVar: string >-> CExp.
  Coercion CConst: Z >-> CExp.
  
  Variant CComp := CGte | CGt.
  
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
    end.
  
  Fixpoint cdenote_exp(e: CExp): ctree Mem Z :=
    match e with
    | CVar v => load v
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

  Fixpoint cdenote (s: CProg ): ctree Mem unit :=
    match s with
    | CAssgn x e =>
        v <- cdenote_exp e ;;
        store x v
    | CIf c l r t e =>
        vl <- cdenote_exp l ;;
        vr <- cdenote_exp r ;;
        if cdenote_comp c vl vr then
          cdenote t
        else
          cdenote e
    | CWhile c l r b =>       
        Ctree.iter
          (fun _ =>
             vl <- cdenote_exp l ;;
             vr <- cdenote_exp r ;;
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

  Definition instr_cexp(p: CExp) (ctx: Ctx): ctreeW Ctx (Z * Ctx) :=
    instr_stateE (cdenote_exp p) ctx.

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
  
  
  Notation "x ::= y '-' c" := (update x y (fun z => z - c))
                                (in custom clang at level 60, right associativity) : clang_scope.
  
  Notation "'if' c '>=' z 'then' t 'else' e" :=
    (CIf CGte c z t e) (in custom clang at level 63): ctree_scope.

  Notation "'if' c '>' z 'then' t 'else' e" :=
    (CIf CGt c z t e) (in custom clang at level 63): ctree_scope.

  Notation "'if' c '>=' z 'then' t 'done'" :=
    (CIf CGte c z t CSkip) (in custom clang at level 63): ctree_scope.

  Notation "'if' c '>' z 'then' t 'done'" :=
    (CIf CGt c z t CSkip) (in custom clang at level 63): ctree_scope.

  Notation "'while' c '>' z 'do' b" :=
    (CWhile CGt c z b) (in custom clang at level 63): ctree_scope.

  Notation "'while' c '>=' z 'do' b" :=
    (CWhile CGte c z b) (in custom clang at level 63): ctree_scope.

  Notation "'skip'" :=
    (CSkip) (in custom clang at level 63): ctree_scope.

  Notation "t1 ;;; t2" := (CSeq t1 t2) (in custom clang at level 62, right associativity): clang_scope.

  (*| Assignment: structural temporal lemmas |*)
  Lemma axr_cprog_assgn: forall x a za ctx w,
      <[ {instr_cexp a ctx}, w |= AX done={(za, ctx)} w ]> ->
      <[ {instr_cprog [[ x := a ]] ctx}, w |= AX AX done={(tt, M.add x za ctx)} {Obs (Log (M.add x za ctx)) tt} ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply anr_state_bind_r_eq...
    unfold store.
    eapply anr_state_bind_r_eq...
    - unfold get, trigger.
      rewrite interp_state_vis; cbn.
      rewrite bind_ret_l, sb_guard, interp_state_ret.
      apply anr_done; intuition...
    - unfold put, trigger.
      rewrite interp_state_vis; cbn.
      rewrite bind_bind.
      unfold resum_ret, ReSumRet_refl.
      apply axr_log.
      + cdestruct H.
        now apply can_step_not_done in Hs.
      + rewrite bind_ret_l, sb_guard, interp_state_ret.
        apply axr_ret...
  Qed.
        
  (*| Sequence: structural temporal lemmas |*)
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

  Lemma ag_cprog_seq: forall a b ctx ctx' w w' φ,
      <[ {instr_cprog a ctx}, w |= φ AU AX done= {(tt,ctx')} w' ]> ->
      <( {instr_cprog b ctx'}, w' |= AG φ )> ->
      <( {instr_cprog [[ a ;;; b ]] ctx}, w |= AG φ )>.
  Proof.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply ag_state_bind_r_eq; eauto.
  Qed.
  
  (*| Conditional: structural temporal lemmas |*)
  Lemma aul_cprog_ite: forall a b ctx w φ ψ za zb t f,
      <[ {instr_cexp a ctx}, w |= AX done={(za, ctx)} w ]> ->
      <[ {instr_cexp b ctx}, w |= AX done={(zb, ctx)} w ]> ->
      (if za >=? zb then        
         <( {instr_cprog t ctx}, w |= φ AU ψ )>
       else
         <( {instr_cprog f ctx}, w |= φ AU ψ )>) ->
      <( {instr_cprog [[ if a >= b then t else f ]] ctx}, w |= φ AU ψ )>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_cexp, instr_stateE.
    intros; cbn.
    eapply aul_state_bind_r_eq.
    - cleft...
    - eapply aul_state_bind_r_eq.
      + cleft...
      + pose proof (Zge_cases za zb); destruct (za >=? zb)...
  Qed.

  Lemma aur_cprog_ite_gt: forall a b ctx w φ ψ za zb t f,
      <[ {instr_cexp a ctx}, w |= AX done={(za, ctx)} w ]> ->
      <[ {instr_cexp b ctx}, w |= AX done={(zb, ctx)} w ]> ->
      (if za >? zb then        
         <[ {instr_cprog t ctx}, w |= φ AU ψ ]>
       else
         <[ {instr_cprog f ctx}, w |= φ AU ψ ]>) ->
      <[ {instr_cprog [[ if a > b then t else f ]] ctx}, w |= φ AU ψ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_cexp, instr_stateE.
    intros; cbn.
    eapply aur_state_bind_r_eq.
    - cleft...
    - eapply aur_state_bind_r_eq.
      + cleft...
      + pose proof (Zgt_cases za zb); destruct (za >? zb)...
  Qed.

  
  Lemma aur_cprog_ite_gtee: forall a b ctx w φ ψ za zb t f,
      <[ {instr_cexp a ctx}, w |= AX done={(za, ctx)} w ]> ->
      <[ {instr_cexp b ctx}, w |= AX done={(zb, ctx)} w ]> ->
      (if za >=? zb then        
         <[ {instr_cprog t ctx}, w |= φ AU ψ ]>
       else
         <[ {instr_cprog f ctx}, w |= φ AU ψ ]>) ->
      <[ {instr_cprog [[ if a >= b then t else f ]] ctx}, w |= φ AU ψ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_cexp, instr_stateE.
    intros; cbn.
    eapply aur_state_bind_r_eq.
    - cleft...
    - eapply aur_state_bind_r_eq.
      + cleft...
      + pose proof (Zge_cases za zb); destruct (za >=? zb)...
  Qed.

  (*| While loop: structural temporal lemmas |*)
  Lemma instr_cprog_while_unfold: forall a b t ctx,
      instr_cprog [[ while a > b do t ]] ctx ~ instr_cprog [[ if a > b then t ;;; while a > b do t done ]] ctx.
  Proof with eauto.
    intros.
    unfold instr_cprog, instr_stateE; cbn.
    rewrite unfold_iter, bind_bind; do 2 rewrite interp_state_bind.
    __upto_bind_sbisim...
    intros [x ctx'].
    rewrite bind_bind.
    do 2 rewrite interp_state_bind.
    __upto_bind_sbisim...
    intros [y ctx''].
    pose proof (Zgt_cases x y); destruct (x >? y).
    - rewrite bind_bind.
      do 2 rewrite interp_state_bind.
      __upto_bind_sbisim...
      intros [ [] ctx'''].
      setoid_rewrite bind_ret_l.
      rewrite unfold_interp_state; cbn.
      rewrite sb_guard.
      reflexivity.
    - setoid_rewrite bind_ret_l.
      rewrite interp_state_ret.
      reflexivity.
  Qed.
End Clang.
