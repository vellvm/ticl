From ExtLib Require
  Structures.Maps.
From ExtLib Require Import Data.String.

From Coq Require Import
  ZArith.ZArith
  Strings.String.

From CTree Require Import
  CTree.Core
  CTree.Interp.State
  CTree.Events.State
  CTree.Events.Writer.

From CTree Require Import
  Logic.Ctl
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

  Inductive CProg :=
  | CAssgn (x: string) (e: CExp)
  | CIfGte (l r: CExp) (t: CProg) (e: CProg)
  | CWhileGt (l r: CExp) (b: CProg)
  | CSeq (l r: CProg).

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
    | CIfGte l r t e =>
        vl <- cdenote_exp l ;;
        vr <- cdenote_exp r ;;
        if vr <=? vl then
          cdenote t
        else
          cdenote e
    | CWhileGt l r b =>
        vl <- cdenote_exp l ;;
        vr <- cdenote_exp r ;;
        Ctree.iter
          (fun _ =>
             if vr <? vl then
               cdenote b ;;
               continue
             else
               break) tt
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

  Declare Custom Entry clang.
  
  Notation "[[ e ]]" := e (at level 0, e custom clang at level 95) : clang_scope.
  Notation "( x )" := x (in custom clang, x at level 99) : clang_scope.
  Notation "{ x }" := x (in custom clang at level 0, x constr): clang_scope.
  Notation "x" := x (in custom clang at level 0, x constr at level 0) : clang_scope.

  Notation "x := c" := (store x c)
                         (in custom clang at level 60, right associativity) : clang_scope.
  
  Notation "x ::= y '+' c" := (update x y (fun z => z + c))
                                (in custom clang at level 60, right associativity) : clang_scope.
  
  Notation "x ::= y '-' c" := (update x y (fun z => z - c))
                                (in custom clang at level 60, right associativity) : clang_scope.
  
  Notation "'if' c '>=' z 'then' t 'else' e" :=
    (CIfGte c z t e) (in custom clang at level 63): ctree_scope.

  Notation "'while' c '>' z 'do' b 'done'" :=
    (CWhileGt c z b) (in custom clang at level 63): ctree_scope.

  Notation "t1 ;;; t2" := (CSeq t1 t2) (in custom clang at level 62, right associativity): clang_scope.

  Lemma aul_cprog_seq: forall a b ctx ctx' w w' φ ψ,
      <[ {instr_cprog a ctx}, w |= φ AU AX done= {(tt,ctx')} w' ]> ->
      <( {instr_cprog b ctx'}, w' |= φ AU ψ )> ->
      <( {instr_cprog [[ a ;;; b ]] ctx}, w |= φ AU ψ )>.
  Proof.
    unfold instr_cprog, instr_stateE.
    intros; cbn.
    eapply aul_state_bind_r_eq; eauto.
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
  Lemma aur_cprog_ite_left: forall a b ctx w φ ψ za zb t f,
      <[ {instr_cexp a ctx}, w |= AX done={(za, ctx)} w ]> ->
      <[ {instr_cexp b ctx}, w |= AX done={(zb, ctx)} w ]> ->
      za >= zb ->
      <[ {instr_cprog t ctx}, w |= φ AU ψ ]> ->
      <[ {instr_cprog [[ if a >= b then t else f ]] ctx}, w |= φ AU ψ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_cexp, instr_stateE.
    intros; cbn.
    eapply aur_state_bind_r_eq.
    - cleft...
    - eapply aur_state_bind_r_eq.
      + cleft...
      + rewrite Zge_is_le_bool in H1.
        rewrite H1...
  Qed.

  Lemma aur_cprog_ite_right: forall a b ctx w φ ψ za zb t f,
      <[ {instr_cexp a ctx}, w |= AX done={(za, ctx)} w ]> ->
      <[ {instr_cexp b ctx}, w |= AX done={(zb, ctx)} w ]> ->
      za < zb ->
      <[ {instr_cprog f ctx}, w |= φ AU ψ ]> ->
      <[ {instr_cprog [[ if a >= b then t else f ]] ctx}, w |= φ AU ψ ]>.
  Proof with eauto with ctl.
    unfold instr_cprog, instr_cexp, instr_stateE.
    intros; cbn.
    eapply aur_state_bind_r_eq.
    - cleft...
    - eapply aur_state_bind_r_eq.
      + cleft...
      + rewrite <- Z.leb_gt in H1.
        rewrite H1...
  Qed.
End Clang.
