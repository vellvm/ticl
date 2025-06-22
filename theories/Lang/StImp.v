From Stdlib Require Import
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
  ICTree.Events.Writer
  Logic.Trans
  Logic.Core
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.EX
  ICTree.Logic.EF
  ICTree.Logic.Bind
  ICTree.Logic.CanStep
  ICTree.Logic.State
  Lang.Maps.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.
Local Open Scope nat_scope.

Generalizable All Variables.

(** * StImp: A simple imperative language with string-indexed variables *)
(** In this module we define a simple imperative language with string-indexed variables.
    The language is denoted in terms of a set of events [stateE], which include [get] and [put] events.
    The semantics of those events are given in terms of instrumentation handler [h_stateE], which is a state monad
    that also keeps track of the context, which is a map from strings to natural numbers.

    This is a simple deep-embedding of a simple imperative language, which allows us to prove structural versions of
    our sequential and loop lemmas from [State.v], over standard program constructs (assignments, conditionals, sequences, etc.).
*)
Module StImp.
  (** A context is a map from strings to natural numbers *)
  Definition Ctx := alist string nat.
  Definition Mem := stateE Ctx.
  Import Ctx.
  Opaque lookup.
  
  (** * The syntax of StImp programs *)
  (** It includes [CVar], [CConst], [CAdd], [CSub], [CEq], [CLe], [CLt], [CAssgn], [CIf], [CWhile], [CSkip], [CSeq] commands. *)
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

  (** Denotation of expressions to [ictree] *)
  Fixpoint cdenote_exp(e: CExp): ictree Mem nat :=
    match e with
    | CVar v => m <- get ;;
               match lookup v m with
               | Some x => Ret x
               | None => stuck
               end
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

  (** Denotation of boolean comparison expressions to [ictree] *)
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

  (** Denotation of programs to [ictree] *)
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

  (** Instrumentation of expressions, comparisons and programs *)
  Definition instr_exp(e: CExp) (ctx: Ctx) : ictreeW Ctx (nat * Ctx) :=
    instr_stateE (cdenote_exp e) ctx.

  Definition instr_comp(c: CComp) (ctx: Ctx) : ictreeW Ctx (bool * Ctx) :=
    instr_stateE (cdenote_comp c) ctx.
    
  Definition instr_prog(p: CProg) (ctx: Ctx) : ictreeW Ctx (unit * Ctx) :=
    instr_stateE (cdenote_prog p) ctx.
  
  (** * Notations for StImp programs *)
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
                       fun 'tt => assert1 x ctx (fun v => v < c))))
      (in custom ticll at level 75): ticl_scope.

  Notation "'var' x '<=' c" :=
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log ctx as z := pat return (encode z -> Prop) in
                       fun 'tt => assert1 x ctx (fun v => v <= c))))
      (in custom ticll at level 75): ticl_scope.

  Notation "'var' x '>' c" :=
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log ctx as z := pat return (encode z -> Prop) in
                       fun 'tt => assert1 x ctx (fun v => v > c))))
      (in custom ticll at level 75): ticl_scope.

  Notation "'var' x '>=' c" :=
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log ctx as z := pat return (encode z -> Prop) in
                       fun 'tt => assert1 x ctx (fun v => v >= c))))
      (in custom ticll at level 75): ticl_scope.

  (** Utility lemmas *)
  Lemma var_eq{X}: forall (p: ictreeW Ctx X) c v m,
      lookup c m = Some v ->      
      <( p, {Obs (Log m) tt} |= var c = v )>.
  Proof with eauto with ticl.
    intros.
    apply ticll_vis... 
  Qed.

  Lemma var_ge{X}: forall (p: ictreeW Ctx X) c v v' m,
      v' >= v ->
      lookup c m = Some v' ->
      <( p, {Obs (Log m) tt} |= var c >= v )>.
  Proof.
    intros.
    apply ticll_vis...
    constructor.
    exists v'; intuition.
  Qed.

  Lemma var_le{X}: forall (p: ictreeW Ctx X) c v v' m,
      v' <= v ->
      lookup c m = Some v' ->
      <( p, {Obs (Log m) tt} |= var c <= v )>.
  Proof.
    intros.
    apply ticll_vis...
    constructor.
    exists v'; intuition.
  Qed.

  (** Comparing [x] and [c] returns a boolean [b] in one step *)
  Lemma axr_ccomp_lt: forall x (c: string) b ctx w (v: nat),
      lookup c ctx = Some v ->
      b = Nat.ltb x v ->
      not_done w ->
      <[ {instr_comp [[x <? c]] ctx}, {w} |= AX (done= {(b, ctx)} {w}) ]>.
  Proof with eauto with ticl.
    intros.
    Opaque Nat.ltb.
    unfold instr_comp, instr_stateE.    
    eapply anr_state_bind_r_eq...
    - apply axr_state_ret...
    - eapply anr_state_bind_r_eq...
      + eapply anr_state_bind_r_eq...
        * rewrite interp_state_get.
          apply axr_ret...
        * setoid_rewrite H.
          apply axr_state_ret...
      + rewrite H0.
        apply axr_state_ret...
  Qed.
    
  (** Constant expressions are evaluated to the constant in one step *)
  Lemma axr_cexp_const: forall (v v': nat) ctx ctx' w w',
      v = v' ->
      ctx = ctx' ->
      w = w' ->
      not_done w ->
      <[ {instr_exp v ctx}, w |= AX done= {(v', ctx')} w' ]>.
  Proof.
    intros; subst.
    unfold instr_exp, instr_stateE; cbn.
    rewrite interp_state_ret.
    now apply axr_ret.
  Qed.

  (** Adding [v1] to [c] returns [v2] in one step *)
  Lemma axr_cexp_add: forall (c: string) (v0 v1 v2: nat) ctx ctx' w w',
      lookup c ctx = Some v0  ->
      v2 = v0 + v1 ->
      ctx = ctx' ->
      w = w' ->
      not_done w ->
      <[ {instr_exp [[ c + v1 ]] ctx}, w |= AX done= {(v2, ctx')} w' ]>.
  Proof with eauto with ticl.
    intros; subst.
    unfold instr_exp, instr_stateE; cbn.
    rewrite bind_bind.
    eapply anr_state_bind_r_eq.
    - apply axr_get...
    - setoid_rewrite H.
      rewrite ?bind_ret_l.
      apply axr_state_ret...
  Qed.

  (** Subtracting [v1] from [c] returns [v2] in one step *)
  Lemma axr_cexp_sub: forall (c: string) (v0 v1 v2: nat) ctx ctx' w w',
      lookup c ctx = Some v0  ->
      v2 = v0 - v1 ->
      ctx = ctx' ->
      w = w' ->
      not_done w ->
      <[ {instr_exp [[ c - v1 ]] ctx}, w |= AX done= {(v2, ctx')} w' ]>.
  Proof with eauto with ticl.
    intros; subst.
    unfold instr_exp, instr_stateE; cbn.
    rewrite bind_bind.
    eapply anr_state_bind_r_eq.
    - apply axr_get...
    - setoid_rewrite H.
      rewrite ?bind_ret_l.
      apply axr_state_ret...
  Qed.
  
  (** * Assignment: structural temporal lemmas *)
  (** An assignment [x := a] eventually (suffix) [AU] returns, where [r] is the evaluation of [a]. 
      Assignments are instrumented with a [log] event, which records the new context.
  *)
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

  (** An assignment [x := a] eventually (suffix) [AU] returns, where [r] is the evaluation of [a]. 
      Assignments are instrumented with a [log] event, which records the new context.
  *)
  Lemma aul_cprog_assgn: forall x a ctx r w ψ φ,
      <[ {instr_exp a ctx}, w |= AX done= {(r, ctx)} w ]> ->
      <( {log (add x r ctx)}, w |= ψ )> ->
      <( {Ret (tt, add x r ctx)}, {Obs (Log (add x r ctx)) tt} |= φ )> ->
      <( {instr_prog [[ x := a ]] ctx}, w |= ψ AU φ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_exp.
    intros; cbn.
    eapply aul_state_bind_r_eq.
    - cleft...
    - eapply aul_state_bind_r_eq.
      + eapply aur_get...
        apply ticll_not_done in H0...
      + rewrite interp_state_put.
        cright.
        apply anl_log.
        * cleft...
        * apply ticll_bind_l...
  Qed.
  
  (** * Sequence: structural temporal lemmas *)
  (** Sequential composition  [a ;;; b] lemmas *)
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

  (** * Conditional: structural temporal lemmas *)
  (** If-then-else [if c then t else f] lemmas *)
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

  (** * While loops *)
  (** Unroll one iteration of the while loop if [c] evaluates to [true] *)
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

  (** The loop terminates if [c] evaluates to [false] *)
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

  (** Unroll one iteration of the while loop if [c] evaluates to [true], suffix [AU] version *)
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

  (** The loop terminates if [c] evaluates to [false], suffix [AU] version *)
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
  
  (** Termination lemma for a while loop, lifts the [aul_state_iter_nat] lemma from [State.v] 
      to the level of StImp programs. *)
  Theorem aul_cprog_while ctx (t: CProg) Ri f c φ ψ:
    Ri ctx ->
    <[ {instr_comp c ctx}, {Obs (Log ctx) tt} |= AX done={(true, ctx)} {Obs (Log ctx) tt} ]> ->
    (forall ctx,
        Ri ctx ->        
        exists (b: bool), <[ {instr_comp c ctx}, {Obs (Log ctx) tt} |= AX done={(b, ctx)} {Obs (Log ctx) tt} ]> /\
          if b then
            <( {instr_prog t ctx}, {Obs (Log ctx) tt} |= φ AU ψ )> \/ 
              <[ {instr_prog t ctx}, {Obs (Log ctx) tt} |= φ AU AX done {fun '(_, ctx') w' =>
                                            w' = Obs (Log ctx') tt /\ Ri ctx' /\ f ctx' < f ctx} ]>
          else
            <( {Ret (inr unit tt, ctx)}, {Obs (Log ctx) tt} |= ψ )>) ->
      <( {instr_prog [[ while c do t done ]] ctx}, {Obs (Log ctx) tt} |= φ AU ψ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp.
    intros HR Hb H.
    eapply aul_state_iter_nat with
      (Ri:=fun 'tt ctx w =>
             w = Obs (Log ctx) tt /\
             exists (b: bool),
               <[ {instr_stateE (cdenote_comp c) ctx}, w |= AX done={(b, ctx)} w ]> /\
                 if b then
                   <( {instr_stateE (cdenote_prog t) ctx}, w |= φ AU ψ )> \/ 
                     <[ {instr_stateE (cdenote_prog t) ctx}, w |= φ AU AX done {fun '(_, ctx') w' =>
                                                                                  w' = Obs (Log ctx') tt /\ Ri ctx' /\ f ctx' < f ctx} ]>
                 else
                   <( {Ret (inr unit tt, ctx)}, w |= ψ )>)
      (f:= fun _ ctx _ => f ctx)...
    - intros [] ctx' w' _ (-> & b' & Hb' & HR').
      destruct b'.
      + (* true *)
        destruct HR'.
        * left.
          eapply aul_state_bind_r_eq...
          -- cleft...
          -- eapply ticll_state_bind_l...
        * right.
          eapply aur_state_bind_r_eq...
          -- cleft...
          -- eapply aur_state_bind_r with (R:=fun _ ctx'0 w' => w' = Obs (Log ctx'0) tt /\ Ri ctx'0 /\ f ctx'0 < f ctx')...
             intros [] ctx_ w_ (-> & HR_ & Hf).
             apply aur_state_ret...
             exists tt; intuition.
      + (* false *)
        left.
        eapply aul_state_bind_r_eq...
        * cleft...
        * cbn.
          apply aul_state_ret...
  Qed.

  (** Termination lemma for a while loop (suffix version) lifts the [aur_state_iter_nat] lemma from [State.v] 
      to the level of StImp programs. *)
  Theorem aur_cprog_while_termination ctx (t: CProg) Ri f c φ ψ b:    
      Ri ctx ->
      <[ {instr_comp c ctx}, {Obs (Log ctx) tt} |= AX done={(b, ctx)} {Obs (Log ctx) tt} ]> ->
      (forall ctx,
          Ri ctx ->
          exists (b: bool), <[ {instr_comp c ctx}, {Obs (Log ctx) tt} |= AX done={(b, ctx)} {Obs (Log ctx) tt} ]> /\
          if b then
            <[ {instr_prog t ctx}, {Obs (Log ctx) tt} |= φ AU AX done {fun '(_, ctx') w' => w' = Obs (Log ctx') tt /\ Ri ctx' /\ f ctx' < f ctx} ]>
          else
            <[ {Ret (tt, ctx)}, {Obs (Log ctx) tt} |= φ AN ψ ]>) ->
      <[ {instr_prog [[ while c do t done ]] ctx}, {Obs (Log ctx) tt} |= φ AU ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; intros.
    eapply aur_state_iter_nat with
      (Ri:=fun 'tt ctx w =>
             w = Obs (Log ctx) tt /\
             exists b : bool,
               <[ {instr_stateE (cdenote_comp c) ctx}, {Obs (Log ctx) tt} |= AX (done= {(b, ctx)} {Obs (Log ctx) tt}) ]> /\
                 (if b
                  then
                    <[ {instr_stateE (cdenote_prog t) ctx}, {Obs (Log ctx) tt} |= {φ} AU AX (done {fun '(_, ctx') (w' : WorldW Ctx) =>
                                                                       w' = Obs (Log ctx') tt /\ Ri ctx' /\ f ctx' < f ctx}) ]>
                  else <[ {Ret (tt, ctx)}, {Obs (Log ctx) tt} |= {φ} AN {ψ} ]>))
      (f:= fun _ ctx _ => f ctx)...
    - intros [] ctx' w' Hd (-> & b' & Hb' & HR).
      eapply aur_state_bind_r_eq...
      + cleft...
      + destruct b'.
        * (* true *)
          eapply aur_state_bind_r with (R:=fun _ ctx'0 w' => w' = Obs (Log ctx'0) tt /\ Ri ctx'0 /\ f ctx'0 < f ctx')...
          intros [] ctx_ w_ (Hd_ & HR_ & Hf).
          apply aur_state_ret; intuition.
        * (* false *)
          apply aur_state_ret; intuition.
  Qed.

  (** Invariance lemma for an infinite while loop, lifts the [ag_state_iter] lemma from [State.v] 
      to the level of StImp programs. *)
  Lemma ag_cprog_while: forall c (t: CProg) R ctx φ,
      R ctx ->      
      (forall ctx,
          R ctx ->
          <( {instr_prog [[while c do t done ]] ctx}, {Obs (Log ctx) tt} |= φ )> /\
          <[ {instr_comp c ctx}, {Obs (Log ctx) tt} |= AX done={(true,ctx)} {Obs (Log ctx) tt} ]>  /\            
          <[ {instr_prog t ctx}, {Obs (Log ctx) tt} |= AX (φ AU AX done {fun '(_, ctx') w' => w' = Obs (Log ctx') tt /\ R ctx'}) ]>) ->
    <( {instr_prog [[ while c do t done ]] ctx}, {Obs (Log ctx) tt} |= AG φ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp. 
    intros; subst.
    eapply ag_state_iter with (R:=fun 'tt ctx w =>
                                    w = Obs (Log ctx) tt /\
                                    <( {instr_prog [[while c do t done ]] ctx}, w |= φ )> /\
                                      <[ {instr_comp c ctx}, w |= AX done={(true,ctx)} w ]>  /\            
                                      <[ {instr_prog t ctx}, w |= AX (φ AU AX done {fun '(_, ctx') w' =>
                                                                                      w' = Obs (Log ctx') tt /\ R ctx'}) ]>)...
    - intros [] ctx' w' Hd (-> & Ht & Hc & HR); intuition.
      rewrite interp_state_bind.
      eapply anr_bind_r_eq...
      cbn; rewrite interp_state_bind.
      cdestruct HR.
      csplit...      
      + destruct Hs as (t_ & w_ & TR).
        eapply can_step_bind_l...
        specialize (HR _ _ TR).
        now apply aur_not_done in HR.
      + intros t_ w_ TR...
        apply ktrans_bind_inv in TR as [(? & TR & Hd_ & ->) | (([] & ctx_) & ? & ? & ? & TR)].
        * specialize (HR _ _ TR).
          apply aur_bind_r with (R:=fun '(_, ctx') (w' : WorldW Ctx) => w' = Obs (Log ctx') tt /\ R ctx')...
          intros [_ ctx_] w'' (Hd'' & HR').
          apply aur_state_ret...
          exists tt; subst; intuition.
        * specialize (HR _ _ H1).
          now apply aur_stuck, anr_stuck in HR.
  Qed.
  
End StImp.
