(** TICL-facing Yield surface.

    Public tiers exported by this façade:

    - [Lang.Yield.Events], [Lang.Yield.Syntax], and [Lang.Yield.Denote] expose
      raw source-level threads with [Yield], [Fork], and memory effects.
    - [Lang.Yield.Scheduler] exposes the scheduler, and [scheduled_visible]
      exposes scheduled programs with scheduler [Spawn], cooperative [Yield],
      and memory effects visible.
    - [interp_scheduled_erased], [instr_exp_erased], and [instr_stmt_erased]
      expose the state-only TICL view where scheduler/yield observations are
      intentionally erased.
    - [interp_scheduled], [instr_exp], and [instr_stmt] are compatibility
      aliases for the erased tier.

    This file also carries a small regression surface: constructor unfold facts,
    one-step scheduler facts, finite-pool slot regressions, concrete visible
    YYield/YFork examples, and alias facts documenting that the compatibility
    APIs are erased. *)
From Stdlib Require Import
  Fin
  Morphisms
  Nat
  Program.Equality
  Strings.String.

From ExtLib Require Import
  Data.Map.FMapAList
  Data.String
  Structures.Maps.

From TICL Require Export
  Lang.Yield.Events
  Lang.Yield.Syntax
  Lang.Yield.Denote
  Lang.Yield.Vec
  Lang.Yield.Scheduler
  Lang.Yield.Interp.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.Eq.Bind
  ICTree.Events.Writer
  ICTree.Interp.Core
  ICTree.Interp.State
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.Bind
  ICTree.Logic.CanStep
  ICTree.Logic.Iter
  ICTree.Logic.State
  ICTree.SBisim
  Logic.Core.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.

Local Typeclasses Transparent equ.
Lemma interp_equ_hetero
    {E F : Type} `{Encode E} `{Encode F} {X}
    (h : E ~> ictree F) :
  forall (x y : ictree E X),
    x ≅ y -> @equ F _ X X eq (interp h x) (interp h y).
Proof.
  change (forall x y : ictree E X,
             @equ E _ X X eq x y ->
             @equ F _ X X eq (interp h x) (interp h y)).
  __coinduction_equ RR IH; intros * EQ1.
  setoid_rewrite unfold_iter.
  step in EQ1; inv EQ1.
  - setoid_rewrite bind_ret_l; reflexivity.
  - setoid_rewrite bind_bind; setoid_rewrite bind_ret_l.
    upto_bind_equ.
    constructor. intros.
    apply IH. apply H3.
  - setoid_rewrite bind_ret_l.
    constructor.
    apply IH. apply H3.
  - setoid_rewrite bind_bind.
    upto_bind_equ.
    setoid_rewrite bind_ret_l.
    constructor.
    apply IH. apply H3.
Qed.

#[local] Instance interp_equ_hetero_proper
    {E F : Type} `{Encode E} `{Encode F} {X}
    (h : E ~> ictree F) :
  Proper (equ eq ==> equ eq) (@interp E _ _ _ _ _ h X).
Proof.
  intros x y Hxy.
  now apply interp_equ_hetero.
Qed.

Lemma interp_bind_hetero
    {E F : Type} `{Encode E} `{Encode F} {A B}
    (h : E ~> ictree F) (t : ictree E A) (k : A -> ictree E B) :
  interp h (x <- t;; k x) ≅ (x <- interp h t;; interp h (k x)).
Proof.
  revert t.
  __coinduction_equ RR IH; intros.
  rewrite (ictree_eta t).
  rewrite unfold_bind, unfold_interp.
  destruct (observe t) eqn:Hobs; cbn.
  - rewrite unfold_interp.
    cbn.
    rewrite bind_ret_l.
    rewrite unfold_interp.
    reflexivity.
  - rewrite unfold_interp.
    cbn.
    rewrite bind_br.
    setoid_rewrite bind_guard.
    constructor; intro i.
    step; econstructor; intros.
    apply IH.
  - rewrite (@unfold_interp _ _ _ _ _ h (Guard t0)).
    cbn.
    rewrite bind_guard.
    constructor.
    apply IH.
  - rewrite unfold_interp.
    cbn.
    rewrite bind_bind.
    upto_bind_equ.
    rewrite bind_guard.
    constructor.
    apply IH.
Qed.

(** Expression denotation constructor unfold facts. *)
Lemma denote_exp_yvar name :
  denote_exp (YVar name) =
    (ctx <- yget;;
     match lookup name ctx with
     | Some value => yyield;; Ret value
     | None => stuck
     end).
Proof. reflexivity. Qed.

Lemma denote_exp_ylit n : denote_exp (YLit n) = Ret n.
Proof. reflexivity. Qed.

Lemma denote_exp_yplus a b :
  denote_exp (YPlus a b) =
    (x <- denote_exp a;; y <- denote_exp b;; Ret (x + y)%nat).
Proof. reflexivity. Qed.

Lemma denote_exp_yminus a b :
  denote_exp (YMinus a b) =
    (x <- denote_exp a;; y <- denote_exp b;; Ret (x - y)%nat).
Proof. reflexivity. Qed.

Lemma denote_exp_ymult a b :
  denote_exp (YMult a b) =
    (x <- denote_exp a;; y <- denote_exp b;; Ret (x * y)%nat).
Proof. reflexivity. Qed.

(** Flow-sensitive statement denotation constructor unfold facts. *)
Lemma denote_stmt_unfold s :
  denote_stmt s = (_ <- denote_stmt_flow s;; Ret tt).
Proof. reflexivity. Qed.

Lemma denote_stmt_flow_yassign name expr :
  denote_stmt_flow (YAssign name expr) =
    (value <- denote_exp expr;;
     ctx <- yget;;
     yput (add name value ctx);;
     Ret Fallthrough).
Proof. reflexivity. Qed.

Lemma denote_stmt_flow_yseq a b :
  denote_stmt_flow (YSeq a b) =
    (flow <- denote_stmt_flow a;;
     match flow with
     | Fallthrough => denote_stmt_flow b
     | HaltThread => Ret HaltThread
     end).
Proof. reflexivity. Qed.

Lemma denote_stmt_flow_yif test then_branch else_branch :
  denote_stmt_flow (YIf test then_branch else_branch) =
    (condition_value <- denote_exp test;;
     if YieldSyntax.is_true condition_value then
       denote_stmt_flow then_branch
     else
       denote_stmt_flow else_branch).
Proof. reflexivity. Qed.

Lemma denote_stmt_flow_ywhile test body :
  denote_stmt_flow (YWhile test body) =
    ICtree.iter
      (fun _ =>
         condition_value <- denote_exp test;;
         if YieldSyntax.is_true condition_value then
           flow <- denote_stmt_flow body;;
           match flow with
           | Fallthrough => Ret (inl tt)
           | HaltThread => Ret (inr HaltThread)
           end
         else
           Ret (inr Fallthrough)) tt.
Proof. reflexivity. Qed.

Lemma denote_stmt_flow_yfork body :
  denote_stmt_flow (YFork body) =
    (in_child <- yfork;;
     if in_child then
       _ <- denote_stmt_flow body;;
       Ret HaltThread
     else
       Ret Fallthrough).
Proof. reflexivity. Qed.

Lemma denote_stmt_yfork body :
  denote_stmt (YFork body) =
    (_ <- (in_child <- yfork;;
           if in_child then
             _ <- denote_stmt_flow body;;
             Ret HaltThread
           else
             Ret Fallthrough);;
     Ret tt).
Proof. reflexivity. Qed.

Lemma denote_stmt_flow_yskip : denote_stmt_flow YSkip = Ret Fallthrough.
Proof. reflexivity. Qed.

Lemma denote_stmt_flow_yyield :
  denote_stmt_flow YYield = (yyield;; Ret Fallthrough).
Proof. reflexivity. Qed.

(** Erased source-structural facts for the state-only TICL tier. *)
Local Ltac unfold_erased_expression :=
  unfold instr_exp_erased, interp_thread, interp_yield, instr_stateE;
  cbn;
  setoid_rewrite unfold_interp;
  cbn.

Local Ltac unfold_erased_statement :=
  unfold instr_stmt_erased, interp_scheduled_erased, interp_yield,
    interp_spawn, scheduled_visible, instr_stateE;
  cbn;
  setoid_rewrite unfold_interp;
  cbn.

Local Ltac step_erased_state :=
  rewrite interp_state_tau, sb_guard;
  setoid_rewrite unfold_interp;
  cbn.

Local Ltac expose_erased_get_result ctx :=
  rewrite interp_state_tau, sb_guard;
  change (resum_ret (inr (inr StateE.Get)) (resum_ret StateE.Get ctx))
    with ctx;
  setoid_rewrite unfold_interp;
  cbn;
  rewrite interp_state_tau, sb_guard;
  setoid_rewrite unfold_interp;
  cbn.

Local Ltac step_erased_state3 :=
  step_erased_state; step_erased_state; step_erased_state.

(** Flow-preserving erased statement instrumentation for structural facts whose
    contracts must expose [Fallthrough] versus [HaltThread].  The public
    [instr_stmt_erased] remains the scheduled unit-returning view. *)
Definition instr_stmt_flow_erased
    (s : YStmt) (ctx : Ctx) : ictreeW Ctx (YStmtFlow * Ctx) :=
  instr_stateE (interp_thread (denote_stmt_flow s)) ctx.

Lemma axr_yexp_ylit : forall n n' ctx ctx' w w',
    n = n' ->
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (YLit n) ctx},
       w |= AX done= {(n', ctx')} w' ]>.
Proof.
  intros; subst.
  unfold_erased_expression.
  rewrite interp_state_ret.
  now apply axr_ret.
Qed.

Lemma axr_yexp_yvar_some : forall name value ctx ctx' w w',
    lookup name ctx = Some value ->
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (YVar name) ctx},
       w |= AX done= {(value, ctx')} w' ]>.
Proof.
  intros; subst.
  unfold_erased_expression.
  eapply anr_state_bind_r_eq.
  - rewrite interp_state_get.
    now apply axr_ret.
  - cbn.
    rewrite interp_state_tau, sb_guard.
    change (resum_ret (inr (inr StateE.Get)) (resum_ret StateE.Get ctx'))
      with ctx'.
    setoid_rewrite subst_ret_l.
    cbn.
    setoid_rewrite unfold_interp.
    cbn.
    rewrite interp_state_tau, sb_guard.
    setoid_rewrite subst_ret_l.
    cbn.
    setoid_rewrite unfold_interp.
    cbn.
    change (alist_find RelDec_string name ctx') with (lookup name ctx').
    destruct (lookup name ctx') eqn:Hlookup; try congruence.
    inv H.
    cbn.
    rewrite bind_ret_l.
    repeat (rewrite interp_state_tau, sb_guard).
    change (resum_ret (inl Yield) (resum_ret Yield tt)) with tt.
    rewrite subst_ret_l.
    cbn.
    setoid_rewrite unfold_interp.
    cbn.
    rewrite interp_state_tau, sb_guard.
    rewrite subst_ret_l.
    cbn.
    setoid_rewrite unfold_interp.
    cbn.
    rewrite interp_state_ret.
    now apply axr_ret.
Qed.

Lemma axr_yexp_yplus : forall a b x y value ctx ctx' w w',
    <[ {instr_exp_erased a ctx}, w |= AX done= {(x, ctx)} w ]> ->
    <[ {instr_exp_erased b ctx}, w |= AX done= {(y, ctx)} w ]> ->
    value = (x + y)%nat ->
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (YPlus a b) ctx},
       w |= AX done= {(value, ctx')} w' ]>.
Proof.
  intros a b x y value ctx ctx' w w' Ha Hb Hvalue Hctx Hw Hnd.
  subst.
  unfold instr_exp_erased, interp_thread, interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply anr_bind_r_eq.
  - exact Ha.
  - cbn.
    rewrite !interp_bind_hetero.
    rewrite !interp_state_bind.
    eapply anr_bind_r_eq.
    + exact Hb.
    + cbn.
      rewrite !unfold_interp.
      cbn.
      rewrite interp_state_ret.
      apply axr_ret; auto.
Qed.

Lemma axr_yexp_yminus : forall a b x y value ctx ctx' w w',
    <[ {instr_exp_erased a ctx}, w |= AX done= {(x, ctx)} w ]> ->
    <[ {instr_exp_erased b ctx}, w |= AX done= {(y, ctx)} w ]> ->
    value = (x - y)%nat ->
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (YMinus a b) ctx},
       w |= AX done= {(value, ctx')} w' ]>.
Proof.
  intros a b x y value ctx ctx' w w' Ha Hb Hvalue Hctx Hw Hnd.
  subst.
  unfold instr_exp_erased, interp_thread, interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply anr_bind_r_eq.
  - exact Ha.
  - cbn.
    rewrite !interp_bind_hetero.
    rewrite !interp_state_bind.
    eapply anr_bind_r_eq.
    + exact Hb.
    + cbn.
      rewrite !unfold_interp.
      cbn.
      rewrite interp_state_ret.
      apply axr_ret; auto.
Qed.

Lemma axr_yexp_ymult : forall a b x y value ctx ctx' w w',
    <[ {instr_exp_erased a ctx}, w |= AX done= {(x, ctx)} w ]> ->
    <[ {instr_exp_erased b ctx}, w |= AX done= {(y, ctx)} w ]> ->
    value = (x * y)%nat ->
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (YMult a b) ctx},
       w |= AX done= {(value, ctx')} w' ]>.
Proof.
  intros a b x y value ctx ctx' w w' Ha Hb Hvalue Hctx Hw Hnd.
  subst.
  unfold instr_exp_erased, interp_thread, interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply anr_bind_r_eq.
  - exact Ha.
  - cbn.
    rewrite !interp_bind_hetero.
    rewrite !interp_state_bind.
    eapply anr_bind_r_eq.
    + exact Hb.
    + cbn.
      rewrite !unfold_interp.
      cbn.
      rewrite interp_state_ret.
      apply axr_ret; auto.
Qed.

Lemma axr_yexp_yplus_ylit_ylit : forall x y value ctx ctx' w w',
    value = (x + y)%nat ->
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (YPlus (YLit x) (YLit y)) ctx},
       w |= AX done= {(value, ctx')} w' ]>.
Proof.
  intros; subst.
  unfold_erased_expression.
  repeat rewrite subst_ret_l.
  cbn.
  rewrite interp_state_ret.
  now apply axr_ret.
Qed.

Lemma axr_yexp_yminus_ylit_ylit : forall x y value ctx ctx' w w',
    value = (x - y)%nat ->
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (YMinus (YLit x) (YLit y)) ctx},
       w |= AX done= {(value, ctx')} w' ]>.
Proof.
  intros; subst.
  unfold_erased_expression.
  repeat rewrite subst_ret_l.
  cbn.
  rewrite interp_state_ret.
  now apply axr_ret.
Qed.

Lemma axr_yexp_ymult_ylit_ylit : forall x y value ctx ctx' w w',
    value = (x * y)%nat ->
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (YMult (YLit x) (YLit y)) ctx},
       w |= AX done= {(value, ctx')} w' ]>.
Proof.
  intros; subst.
  unfold_erased_expression.
  repeat rewrite subst_ret_l.
  cbn.
  rewrite interp_state_ret.
  now apply axr_ret.
Qed.

Lemma axr_ystmt_yskip_erased : forall ctx ctx' w w',
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_stmt_erased YSkip ctx},
       w |= AX done= {(tt, ctx')} w' ]>.
Proof.
  intros; subst.
  unfold_erased_statement.
  step_erased_state.
  rewrite interp_state_ret.
  now apply axr_ret.
Qed.

Lemma axax_ystmt_yyield_erased : forall ctx ctx' w w',
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_stmt_erased YYield ctx},
       w |= AX AX done= {(tt, ctx')} w' ]>.
Proof.
  intros; subst.
  unfold_erased_statement.
  step_erased_state.
  rewrite bind_ret_l.
  cbn.
  step_erased_state.
  step_erased_state.
  apply anr_state_br; split.
  - csplit; auto.
  - intro i; dependent destruction i.
    + step_erased_state3.
      rewrite interp_state_ret.
      apply axr_ret; auto.
    + inversion i.
Qed.

Lemma aur_ystmt_yyield_erased : forall ctx ctx' w w' ψ,
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_stmt_erased YYield ctx},
       w |= ψ AU AX AX done= {(tt, ctx')} w' ]>.
Proof.
  intros; subst.
  cleft.
  now apply axax_ystmt_yyield_erased.
Qed.

Local Definition yassign_after_value
    (name : var) (value : nat) : ictree YEff YStmtFlow :=
  ctx <- yget;; yput (add name value ctx);; Ret Fallthrough.

Local Lemma aur_yassign_after_value : forall name value ctx w ψ R,
    <( {log (add name value ctx)}, w |= ψ )> ->
    R (Fallthrough, add name value ctx)
      (Obs (Log (add name value ctx)) tt) ->
    <[ {instr_stateE (interp_thread (yassign_after_value name value)) ctx},
       w |= ψ AU AX done R ]>.
Proof.
  intros name value ctx w ψ R Hlog HR.
  pose proof (ticll_not_done unit _ _ _ Hlog) as Hnd.
  unfold yassign_after_value, interp_thread, interp_yield, instr_stateE.
  cbn.
  setoid_rewrite unfold_interp.
  cbn.
  eapply aur_state_bind_r_eq.
  - apply aur_get; auto; split; reflexivity.
  - cbn.
    expose_erased_get_result ctx.
    eapply aur_state_bind_r_eq.
    + apply aur_put; auto; split; reflexivity.
    + cbn.
      step_erased_state.
      step_erased_state.
      rewrite interp_state_ret.
      cleft.
      apply axr_ret; auto.
      constructor.
Qed.

Local Lemma aul_yassign_after_value : forall name value ctx w ψ φ,
    <( {log (add name value ctx)}, w |= ψ )> ->
    <( {Ret (Fallthrough, add name value ctx)},
       {Obs (Log (add name value ctx)) tt} |= φ )> ->
    <( {instr_stateE (interp_thread (yassign_after_value name value)) ctx},
       w |= ψ AU φ )>.
Proof.
  intros name value ctx w ψ φ Hlog Hret.
  pose proof (ticll_not_done unit _ _ _ Hlog) as Hnd.
  unfold yassign_after_value, interp_thread, interp_yield, instr_stateE.
  cbn.
  setoid_rewrite unfold_interp.
  cbn.
  eapply aul_state_bind_r_eq.
  - apply aur_get; auto; split; reflexivity.
  - cbn.
    expose_erased_get_result ctx.
    eapply aul_state_bind_r_eq.
    + apply aur_put; auto; split; reflexivity.
    + cbn.
      step_erased_state.
      step_erased_state.
      rewrite interp_state_ret.
      cleft.
      exact Hret.
Qed.

Lemma aur_ystmt_yassign : forall name expr value ctx w ψ R,
    <[ {instr_exp_erased expr ctx}, w |= AX done= {(value, ctx)} w ]> ->
    <( {log (add name value ctx)}, w |= ψ )> ->
    R (Fallthrough, add name value ctx)
      (Obs (Log (add name value ctx)) tt) ->
    <[ {instr_stmt_flow_erased (YAssign name expr) ctx},
       w |= ψ AU AX done R ]>.
Proof.
  intros name expr value ctx w ψ R Hexp Hlog HR.
  unfold instr_stmt_flow_erased, instr_exp_erased, interp_thread,
    interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply aur_bind_r_eq.
  - cleft.
    exact Hexp.
  - cbn.
    change (interp_state h_stateW
              (interp handle_yield
                 (interp handle_thread
                    (ctx <- yget;; yput (add name value ctx);;
                     Ret Fallthrough))) ctx)
      with (instr_stateE (interp_thread (yassign_after_value name value)) ctx).
    now apply aur_yassign_after_value.
Qed.

Lemma aul_ystmt_yassign : forall name expr value ctx w ψ φ,
    <[ {instr_exp_erased expr ctx}, w |= AX done= {(value, ctx)} w ]> ->
    <( {log (add name value ctx)}, w |= ψ )> ->
    <( {Ret (Fallthrough, add name value ctx)},
       {Obs (Log (add name value ctx)) tt} |= φ )> ->
    <( {instr_stmt_flow_erased (YAssign name expr) ctx}, w |= ψ AU φ )>.
Proof.
  intros name expr value ctx w ψ φ Hexp Hlog Hret.
  unfold instr_stmt_flow_erased, instr_exp_erased, interp_thread,
    interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply aul_bind_r_eq.
  - cleft.
    exact Hexp.
  - cbn.
    change (interp_state h_stateW
              (interp handle_yield
                 (interp handle_thread
                    (ctx <- yget;; yput (add name value ctx);;
                     Ret Fallthrough))) ctx)
      with (instr_stateE (interp_thread (yassign_after_value name value)) ctx).
    now apply aul_yassign_after_value.
Qed.

Lemma anr_ystmt_yseq_fallthrough : forall a b ctx ctx' w w' φ ψ,
    <[ {instr_stmt_flow_erased a ctx},
       w |= φ AN done= {(Fallthrough, ctx')} w' ]> ->
    <[ {instr_stmt_flow_erased b ctx'}, w' |= φ AN ψ ]> ->
    <[ {instr_stmt_flow_erased (YSeq a b) ctx}, w |= φ AN ψ ]>.
Proof.
  intros a b ctx ctx' w w' φ ψ Ha Hb.
  unfold instr_stmt_flow_erased, interp_thread, interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply anr_bind_r_eq; eauto.
Qed.

Lemma aur_ystmt_yseq_fallthrough : forall a b ctx ctx' w w' φ ψ,
    <[ {instr_stmt_flow_erased a ctx},
       w |= φ AU AX done= {(Fallthrough, ctx')} w' ]> ->
    <[ {instr_stmt_flow_erased b ctx'}, w' |= φ AU ψ ]> ->
    <[ {instr_stmt_flow_erased (YSeq a b) ctx}, w |= φ AU ψ ]>.
Proof.
  intros a b ctx ctx' w w' φ ψ Ha Hb.
  unfold instr_stmt_flow_erased, interp_thread, interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply aur_bind_r_eq; eauto.
Qed.

Lemma aul_ystmt_yseq_fallthrough : forall a b ctx ctx' w w' φ ψ,
    <[ {instr_stmt_flow_erased a ctx},
       w |= φ AU AX done= {(Fallthrough, ctx')} w' ]> ->
    <( {instr_stmt_flow_erased b ctx'}, w' |= φ AU ψ )> ->
    <( {instr_stmt_flow_erased (YSeq a b) ctx}, w |= φ AU ψ )>.
Proof.
  intros a b ctx ctx' w w' φ ψ Ha Hb.
  unfold instr_stmt_flow_erased, interp_thread, interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply aul_bind_r_eq; eauto.
Qed.

Lemma yseq_halt_propagates : forall a b ctx ctx' w w' φ,
    <[ {instr_stmt_flow_erased a ctx},
       w |= φ AU AX done= {(HaltThread, ctx')} w' ]> ->
    not_done w' ->
    <[ {instr_stmt_flow_erased (YSeq a b) ctx},
       w |= φ AU AX done= {(HaltThread, ctx')} w' ]>.
Proof.
  intros a b ctx ctx' w w' φ Ha Hnd.
  unfold instr_stmt_flow_erased, interp_thread, interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply aur_bind_r_eq.
  - exact Ha.
  - cbn.
    rewrite !unfold_interp.
    cbn.
    apply aur_state_ret; auto; split; reflexivity.
Qed.

Lemma aul_ystmt_yif : forall test then_branch else_branch condition ctx w φ ψ,
    <[ {instr_exp_erased test ctx}, w |= AX done= {(condition, ctx)} w ]> ->
    (if YieldSyntax.is_true condition then
       <( {instr_stmt_flow_erased then_branch ctx}, w |= φ AU ψ )>
     else
       <( {instr_stmt_flow_erased else_branch ctx}, w |= φ AU ψ )>) ->
    <( {instr_stmt_flow_erased (YIf test then_branch else_branch) ctx},
       w |= φ AU ψ )>.
Proof.
  intros test then_branch else_branch condition ctx w φ ψ Htest Hbranch.
  unfold instr_stmt_flow_erased, instr_exp_erased, interp_thread,
    interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply aul_bind_r_eq.
  - cleft; exact Htest.
  - cbn.
    destruct (YieldSyntax.is_true condition); exact Hbranch.
Qed.

Lemma aur_ystmt_yif : forall test then_branch else_branch condition ctx w φ ψ,
    <[ {instr_exp_erased test ctx}, w |= AX done= {(condition, ctx)} w ]> ->
    (if YieldSyntax.is_true condition then
       <[ {instr_stmt_flow_erased then_branch ctx}, w |= φ AU ψ ]>
     else
       <[ {instr_stmt_flow_erased else_branch ctx}, w |= φ AU ψ ]>) ->
    <[ {instr_stmt_flow_erased (YIf test then_branch else_branch) ctx},
       w |= φ AU ψ ]>.
Proof.
  intros test then_branch else_branch condition ctx w φ ψ Htest Hbranch.
  unfold instr_stmt_flow_erased, instr_exp_erased, interp_thread,
    interp_yield, instr_stateE in *.
  cbn.
  rewrite !interp_bind_hetero.
  rewrite !interp_state_bind.
  eapply aur_bind_r_eq.
  - cleft; exact Htest.
  - cbn.
    destruct (YieldSyntax.is_true condition); exact Hbranch.
Qed.

(** Raw source-flow while unrolling facts.  These expose [YStmtFlow]
    directly, avoiding any claim that the scheduled erased unit layer can
    distinguish loop fallthrough from child-thread halt. *)
Definition ywhile_iteration (test : YExp) (body : YStmt) :
    ictree YEff (unit + YStmtFlow) :=
  condition_value <- denote_exp test;;
  if YieldSyntax.is_true condition_value then
    flow <- denote_stmt_flow body;;
    match flow with
    | Fallthrough => Ret (inl tt)
    | HaltThread => Ret (inr HaltThread)
    end
  else
    Ret (inr Fallthrough).

Lemma aul_ystmt_ywhile_true : forall test body condition w w' φ ψ,
    <[ {denote_exp test}, w |= φ AU AX done= condition w ]> ->
    YieldSyntax.is_true condition = true ->
    <[ {denote_stmt_flow body},
       w |= φ AU AX done= Fallthrough w' ]> ->
    not_done w' ->
    <( {denote_stmt_flow (YWhile test body)}, w' |= φ AU ψ )> ->
    <( {denote_stmt_flow (YWhile test body)}, w |= φ AU ψ )>.
Proof.
  intros test body condition w w' φ ψ Htest Htrue Hbody Hnd Hloop.
  cbn.
  eapply aul_iter_next with (R := fun (_ : unit) w0 => w0 = w').
  - eapply aur_bind_r_eq.
    + exact Htest.
    + rewrite Htrue.
      eapply aur_bind_r_eq.
      * exact Hbody.
      * cbn.
        cleft.
        apply axr_ret; auto.
        exists tt; split; auto.
  - intros [] w0 ->.
    exact Hloop.
Qed.

Lemma aul_ystmt_ywhile_false : forall test body condition w φ ψ,
    <[ {denote_exp test}, w |= φ AU AX done= condition w ]> ->
    YieldSyntax.is_true condition = false ->
    <( {Ret Fallthrough}, w |= ψ )> ->
    <( {denote_stmt_flow (YWhile test body)}, w |= φ AU ψ )>.
Proof.
  intros test body condition w φ ψ Htest Hfalse Hret.
  pose proof Htest as Htest_not_done.
  apply aur_not_done in Htest_not_done.
  cbn.
  rewrite unfold_iter.
  eapply aul_bind_r_eq.
  - eapply aur_bind_r_eq.
    + exact Htest.
    + rewrite Hfalse.
      cbn.
      cleft.
      apply axr_ret.
      * exact Htest_not_done.
      * split; reflexivity.
  - cbn.
    cleft.
    exact Hret.
Qed.

Lemma aul_ystmt_ywhile_halt : forall test body condition w w' φ ψ,
    <[ {denote_exp test}, w |= φ AU AX done= condition w ]> ->
    YieldSyntax.is_true condition = true ->
    <[ {denote_stmt_flow body},
       w |= φ AU AX done= HaltThread w' ]> ->
    not_done w' ->
    <( {Ret HaltThread}, w' |= ψ )> ->
    <( {denote_stmt_flow (YWhile test body)}, w |= φ AU ψ )>.
Proof.
  intros test body condition w w' φ ψ Htest Htrue Hbody Hnd Hret.
  cbn.
  rewrite unfold_iter.
  eapply aul_bind_r_eq.
  - eapply aur_bind_r_eq.
    + exact Htest.
    + rewrite Htrue.
      eapply aur_bind_r_eq.
      * exact Hbody.
      * cbn.
        cleft.
        apply axr_ret; auto.
  - cbn.
    cleft.
    exact Hret.
Qed.

Lemma aur_ystmt_ywhile_true : forall test body condition w w' φ ψ,
    <[ {denote_exp test}, w |= φ AU AX done= condition w ]> ->
    YieldSyntax.is_true condition = true ->
    <[ {denote_stmt_flow body},
       w |= φ AU AX done= Fallthrough w' ]> ->
    not_done w' ->
    <[ {denote_stmt_flow (YWhile test body)}, w' |= φ AU AX ψ ]> ->
    <[ {denote_stmt_flow (YWhile test body)}, w |= φ AU AX ψ ]>.
Proof.
  intros test body condition w w' φ ψ Htest Htrue Hbody Hnd Hloop.
  cbn.
  eapply aur_iter_next with (R := fun (_ : unit) w0 => w0 = w').
  - eapply aur_bind_r_eq.
    + exact Htest.
    + rewrite Htrue.
      eapply aur_bind_r_eq.
      * exact Hbody.
      * cbn.
        cleft.
        apply axr_ret; auto.
        exists tt; split; auto.
  - intros [] w0 ->.
    exact Hloop.
Qed.

Lemma aur_ystmt_ywhile_false : forall test body condition w φ ψ,
    <[ {denote_exp test}, w |= φ AU AX done= condition w ]> ->
    YieldSyntax.is_true condition = false ->
    <[ {Ret Fallthrough}, w |= AX ψ ]> ->
    <[ {denote_stmt_flow (YWhile test body)}, w |= φ AU AX ψ ]>.
Proof.
  intros test body condition w φ ψ Htest Hfalse Hret.
  pose proof Htest as Htest_not_done.
  apply aur_not_done in Htest_not_done.
  cbn.
  rewrite unfold_iter.
  eapply aur_bind_r_eq.
  - eapply aur_bind_r_eq.
    + exact Htest.
    + rewrite Hfalse.
      cbn.
      cleft.
      apply axr_ret.
      * exact Htest_not_done.
      * split; reflexivity.
  - cbn.
    cleft.
    exact Hret.
Qed.

Lemma ag_ystmt_ywhile : forall test body (R : World YEff -> Prop) w φ,
    R w ->
    (forall w,
        R w ->
        <( {denote_stmt_flow (YWhile test body)}, w |= φ )> /\
        <[ {ywhile_iteration test body}, w |= AX (φ AU AX done
             {fun lr w' => exists i' : unit, lr = inl i' /\ R w'}) ]>) ->
    <( {denote_stmt_flow (YWhile test body)}, w |= AG φ )>.
Proof.
  intros test body R w φ HR Hstep.
  cbn.
  change (ICtree.iter (fun _ : unit => ywhile_iteration test body) tt)
    with (denote_stmt_flow (YWhile test body)).
  eapply ag_iter with (R := fun (_ : unit) w => R w); eauto.
  intros [] w0 HR0.
  specialize (Hstep w0 HR0) as [Hφ Hnext].
  split.
  - exact Hφ.
  - cbn.
    exact Hnext.
Qed.

Lemma aur_ystmt_yassign_ylit_erased : forall name n ctx w ψ R,
    <( {log (add name n ctx)}, w |= ψ )> ->
    R (tt, add name n ctx) (Obs (Log (add name n ctx)) tt) ->
    <[ {instr_stmt_erased (YAssign name (YLit n)) ctx},
       w |= ψ AU AX done R ]>.
Proof.
  intros name n ctx w ψ R Hlog HR.
  pose proof (ticll_not_done unit _ _ _ Hlog) as Hnd.
  unfold_erased_statement.
  eapply aur_state_bind_r_eq.
  - apply aur_get; auto; split; reflexivity.
  - cbn.
    expose_erased_get_result ctx.
    eapply aur_state_bind_r_eq.
    + apply aur_put.
      * exact Hlog.
      * split; reflexivity.
    + cbn.
      step_erased_state3.
      apply aur_state_ret; auto with ticl.
Qed.

Lemma aul_ystmt_yassign_ylit_erased : forall name n ctx w ψ φ,
    <( {log (add name n ctx)}, w |= ψ )> ->
    <( {Ret (tt, add name n ctx)},
       {Obs (Log (add name n ctx)) tt} |= φ )> ->
    <( {instr_stmt_erased (YAssign name (YLit n)) ctx}, w |= ψ AU φ )>.
Proof.
  intros name n ctx w ψ φ Hlog Hret.
  pose proof (ticll_not_done unit _ _ _ Hlog) as Hnd.
  unfold_erased_statement.
  eapply aul_state_bind_r_eq.
  - apply aur_get; auto; split; reflexivity.
  - cbn.
    expose_erased_get_result ctx.
    eapply aul_state_bind_r_eq.
    + apply aur_put.
      * exact Hlog.
      * split; reflexivity.
    + cbn.
      step_erased_state3.
      apply aul_state_ret; auto with ticl.
Qed.

(** Scheduler one-step/case regression facts. *)
Section SchedulerFacts.
  Context {E : Type} `{Encode E}.

  Local Ltac solve_focused_schedule H :=
    lazy [schedule observe _observe];
    match type of H with
    | observe (?v ?i) = _ =>
        change (@_observe _ _ unit (v i)) with (observe (v i));
        rewrite H;
        reflexivity
    end.

  Lemma schedule_empty_none (v : pool E 0) :
    observe (schedule 0 v None) = RetF tt.
  Proof. reflexivity. Qed.

  Lemma schedule_no_focus_nonempty n (v : pool E (S n)) :
    observe (schedule (S n) v None) =
      VisF (inl Yield) (fun _ => Br n (fun i => schedule (S n) v (Some i))).
  Proof. reflexivity. Qed.

  Lemma schedule_focused_ret n (v : pool E (S n)) (i : Fin.t (S n)) :
    observe (v i) = RetF tt ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule n (remove_pool v i) None).
  Proof.
    intro Hret.
    solve_focused_schedule Hret.
  Qed.

  Lemma schedule_focused_br n (v : pool E (S n)) (i : Fin.t (S n)) b k :
    observe (v i) = BrF b k ->
    observe (schedule (S n) v (Some i)) =
      BrF b (fun j => schedule (S n) (replace_pool v i (k j)) (Some i)).
  Proof.
    intro Hbr.
    solve_focused_schedule Hbr.
  Qed.

  Lemma schedule_focused_guard n (v : pool E (S n)) (i : Fin.t (S n)) t :
    observe (v i) = GuardF t ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S n) (replace_pool v i t) (Some i)).
  Proof.
    intro Hg.
    solve_focused_schedule Hg.
  Qed.

  Lemma schedule_focused_yield n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inl Yield) k ->
    observe (schedule (S n) v (Some i)) =
      GuardF (schedule (S n) (replace_pool v i (k tt)) None).
  Proof.
    intro Hy.
    solve_focused_schedule Hy.
  Qed.

  Lemma schedule_focused_fork n (v : pool E (S n)) (i : Fin.t (S n)) k :
    observe (v i) = VisF (inr (inl Fork)) k ->
    observe (schedule (S n) v (Some i)) =
      VisF ((inr (inl Spawn)) : yieldE + (spawnE + E))
        (fun _ => schedule (S (S n))
                    (cons_pool (k true) (replace_pool v i (k false)))
                    (Some (Fin.FS i))).
  Proof.
    intro Hf.
    solve_focused_schedule Hf.
  Qed.

  Lemma schedule_focused_user_event n (v : pool E (S n)) (i : Fin.t (S n)) e k :
    observe (v i) = VisF (inr (inr e)) k ->
    observe (schedule (S n) v (Some i)) =
      VisF ((inr (inr e)) : yieldE + (spawnE + E))
        (fun x => schedule (S n) (replace_pool v i (k x)) (Some i)).
  Proof.
    intro Hu.
    solve_focused_schedule Hu.
  Qed.
End SchedulerFacts.

(** Non-degenerate finite-pool scheduler regressions. *)
Section SchedulerPoolRegressions.
  Context {E : Type} `{Encode E}.

  Lemma schedule_yield_two_threads_one_step (next other : thread E) :
    observe
      (schedule 2
         (cons_pool
            (Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next))
            (fun _ : Fin.t 1 => other))
         (Some Fin.F1)) =
      GuardF
        (schedule 2
           (replace_pool
              (cons_pool
                 (Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next))
                 (fun _ : Fin.t 1 => other))
              Fin.F1 next)
           None).
  Proof. reflexivity. Qed.

  Lemma schedule_yield_two_threads_focused_slot (next other : thread E) :
    replace_pool
      (cons_pool
         (Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next))
         (fun _ : Fin.t 1 => other))
      Fin.F1 next Fin.F1 = next.
  Proof. apply replace_pool_hit. Qed.

  Lemma schedule_yield_two_threads_other_slot (next other : thread E) :
    replace_pool
      (cons_pool
         (Vis ((inl Yield) : yieldE + (forkE + E)) (fun _ : unit => next))
         (fun _ : Fin.t 1 => other))
      Fin.F1 next (Fin.FS Fin.F1) = other.
  Proof.
    rewrite replace_pool_miss by discriminate.
    apply cons_pool_tail.
  Qed.

  Lemma schedule_fork_two_threads_one_step
      (child parent other : thread E) :
    observe
      (schedule 2
         (cons_pool
            (Vis ((inr (inl Fork)) : yieldE + (forkE + E))
               (fun in_child : bool => if in_child then child else parent))
            (fun _ : Fin.t 1 => other))
         (Some Fin.F1)) =
      VisF ((inr (inl Spawn)) : yieldE + (spawnE + E))
        (fun _ =>
           schedule 3
             (cons_pool child
                (replace_pool
                   (cons_pool
                      (Vis ((inr (inl Fork)) : yieldE + (forkE + E))
                         (fun in_child : bool => if in_child then child else parent))
                      (fun _ : Fin.t 1 => other))
                   Fin.F1 parent))
             (Some (Fin.FS Fin.F1))).
  Proof. reflexivity. Qed.

  Lemma schedule_fork_two_threads_child_slot
      (child parent other : thread E) :
    cons_pool child
      (replace_pool
         (cons_pool
            (Vis ((inr (inl Fork)) : yieldE + (forkE + E))
               (fun in_child : bool => if in_child then child else parent))
            (fun _ : Fin.t 1 => other))
         Fin.F1 parent)
      Fin.F1 = child.
  Proof. apply cons_pool_head. Qed.

  Lemma schedule_fork_two_threads_parent_slot
      (child parent other : thread E) :
    cons_pool child
      (replace_pool
         (cons_pool
            (Vis ((inr (inl Fork)) : yieldE + (forkE + E))
               (fun in_child : bool => if in_child then child else parent))
            (fun _ : Fin.t 1 => other))
         Fin.F1 parent)
      (Fin.FS Fin.F1) = parent.
  Proof.
    rewrite cons_pool_tail.
    apply replace_pool_hit.
  Qed.

  Lemma schedule_fork_two_threads_other_slot
      (child parent other : thread E) :
    cons_pool child
      (replace_pool
         (cons_pool
            (Vis ((inr (inl Fork)) : yieldE + (forkE + E))
               (fun in_child : bool => if in_child then child else parent))
            (fun _ : Fin.t 1 => other))
         Fin.F1 parent)
      (Fin.FS (Fin.FS Fin.F1)) = other.
  Proof.
    rewrite cons_pool_tail.
    rewrite replace_pool_miss by discriminate.
    apply cons_pool_tail.
  Qed.
End SchedulerPoolRegressions.

(** Concrete scheduler-visible examples. *)
Local Ltac solve_visible_regression :=
  cbn;
  unfold resum, ReSum_refl, resum_ret, ReSumRet_refl;
  reflexivity.

Lemma scheduled_visible_yyield_one_step :
  observe (scheduled_visible YYield) =
    GuardF
      (schedule 1
         (replace_pool
            (fun _ : Fin.t 1 => denote_stmt YYield)
            Fin.F1 (denote_stmt YSkip))
         None).
Proof.
  unfold scheduled_visible.
  apply (@schedule_focused_yield Mem _ 0
           (fun _ : Fin.t 1 => denote_stmt YYield)
           Fin.F1
           (fun _ : unit => denote_stmt YSkip)).
  solve_visible_regression.
Qed.

Definition yfork_body_fork_continuation
    (body : YStmt) (in_child : bool) : thread Mem :=
  ICtree.subst'
    (fun _ : YStmtFlow => Ret tt)
    (observe
       (ICtree.subst'
          (fun branch : bool =>
             if branch then
               denote_stmt_flow body;; Ret HaltThread
             else
               Ret Fallthrough)
          (RetF in_child))).

Lemma scheduled_visible_yfork_body_one_step : forall body,
  observe (scheduled_visible (YFork body)) =
    VisF ((inr (inl Spawn)) : yieldE + (spawnE + Mem))
      (fun _ =>
         schedule 2
           (cons_pool (yfork_body_fork_continuation body true)
              (replace_pool
                 (fun _ : Fin.t 1 => denote_stmt (YFork body))
                 Fin.F1 (yfork_body_fork_continuation body false)))
           (Some (Fin.FS Fin.F1))).
Proof.
  intro body.
  unfold scheduled_visible.
  apply (@schedule_focused_fork Mem _ 0
           (fun _ : Fin.t 1 => denote_stmt (YFork body))
           Fin.F1
           (yfork_body_fork_continuation body)).
  solve_visible_regression.
Qed.

Lemma yfork_child_halts_after_body body :
  yfork_body_fork_continuation body true =
    ICtree.subst' (fun _ : YStmtFlow => Ret tt)
      (observe (denote_stmt_flow body;; Ret HaltThread)).
Proof. reflexivity. Qed.

Lemma yfork_parent_falls_through body :
  observe (yfork_body_fork_continuation body false) = RetF tt.
Proof. solve_visible_regression. Qed.

Definition yseq_yfork_body_rest_fork_continuation
    (body rest : YStmt) (in_child : bool) : thread Mem :=
  ICtree.subst'
    (fun _ : YStmtFlow => Ret tt)
    (observe
       (ICtree.subst'
          (fun flow : YStmtFlow =>
             match flow with
             | Fallthrough => denote_stmt_flow rest
             | HaltThread => Ret HaltThread
             end)
          (observe
             (ICtree.subst'
                (fun branch : bool =>
                   if branch then
                     denote_stmt_flow body;; Ret HaltThread
                   else
                     Ret Fallthrough)
                (RetF in_child))))).

Lemma scheduled_visible_yseq_yfork_body_rest_one_step : forall body rest,
  observe (scheduled_visible (YSeq (YFork body) rest)) =
    VisF ((inr (inl Spawn)) : yieldE + (spawnE + Mem))
      (fun _ =>
         schedule 2
           (cons_pool
              (yseq_yfork_body_rest_fork_continuation body rest true)
              (replace_pool
                 (fun _ : Fin.t 1 =>
                    denote_stmt (YSeq (YFork body) rest))
                 Fin.F1
                 (yseq_yfork_body_rest_fork_continuation body rest false)))
           (Some (Fin.FS Fin.F1))).
Proof.
  intros body rest.
  unfold scheduled_visible.
  apply (@schedule_focused_fork Mem _ 0
           (fun _ : Fin.t 1 => denote_stmt (YSeq (YFork body) rest))
           Fin.F1
           (yseq_yfork_body_rest_fork_continuation body rest)).
  solve_visible_regression.
Qed.

Lemma yseq_yfork_body_rest_parent_runs_rest body rest :
  observe (yseq_yfork_body_rest_fork_continuation body rest false) =
    observe (denote_stmt rest).
Proof. solve_visible_regression. Qed.

Definition yfork_yield_fork_continuation (in_child : bool) : thread Mem :=
  ICtree.subst'
    (fun _ : YStmtFlow => Ret tt)
    (observe
       (ICtree.subst'
          (fun branch : bool =>
             if branch then
               denote_stmt_flow YYield;; Ret HaltThread
             else
               Ret Fallthrough)
          (RetF in_child))).

Lemma scheduled_visible_yfork_yield_one_step :
  observe (scheduled_visible (YFork YYield)) =
    VisF ((inr (inl Spawn)) : yieldE + (spawnE + Mem))
      (fun _ =>
         schedule 2
           (cons_pool (yfork_yield_fork_continuation true)
              (replace_pool
                 (fun _ : Fin.t 1 => denote_stmt (YFork YYield))
                 Fin.F1 (yfork_yield_fork_continuation false)))
           (Some (Fin.FS Fin.F1))).
Proof.
  unfold scheduled_visible.
  apply (@schedule_focused_fork Mem _ 0
           (fun _ : Fin.t 1 => denote_stmt (YFork YYield))
           Fin.F1
           yfork_yield_fork_continuation).
  solve_visible_regression.
Qed.

Definition yseq_yfork_skip_yield_fork_continuation
    (in_child : bool) : thread Mem :=
  ICtree.subst'
    (fun _ : YStmtFlow => Ret tt)
    (observe
       (ICtree.subst'
          (fun flow : YStmtFlow =>
             match flow with
             | Fallthrough => denote_stmt_flow YYield
             | HaltThread => Ret HaltThread
             end)
          (observe
             (ICtree.subst'
                (fun branch : bool =>
                   if branch then
                     denote_stmt_flow YSkip;; Ret HaltThread
                   else
                     Ret Fallthrough)
                (RetF in_child))))).

Lemma yseq_yfork_skip_yield_child_done :
  observe (yseq_yfork_skip_yield_fork_continuation true) = RetF tt.
Proof. solve_visible_regression. Qed.

Lemma yseq_yfork_skip_yield_parent_yields :
  observe (yseq_yfork_skip_yield_fork_continuation false) =
    VisF ((inl Yield) : YEff) (fun _ : unit => denote_stmt YSkip).
Proof. solve_visible_regression. Qed.

Lemma scheduled_visible_yseq_yfork_skip_yield_one_step :
  observe (scheduled_visible (YSeq (YFork YSkip) YYield)) =
    VisF ((inr (inl Spawn)) : yieldE + (spawnE + Mem))
      (fun _ =>
         schedule 2
           (cons_pool (yseq_yfork_skip_yield_fork_continuation true)
              (replace_pool
                 (fun _ : Fin.t 1 =>
                    denote_stmt (YSeq (YFork YSkip) YYield))
                 Fin.F1 (yseq_yfork_skip_yield_fork_continuation false)))
           (Some (Fin.FS Fin.F1))).
Proof.
  unfold scheduled_visible.
  apply (@schedule_focused_fork Mem _ 0
           (fun _ : Fin.t 1 => denote_stmt (YSeq (YFork YSkip) YYield))
           Fin.F1
           yseq_yfork_skip_yield_fork_continuation).
  solve_visible_regression.
Qed.

(** Erasure handlers intentionally hide scheduler/thread observations. *)
Lemma handle_spawn_spawn_erased : handle_spawn (inr (inl Spawn)) = Ret tt.
Proof. reflexivity. Qed.

Lemma handle_yield_yield_erased : handle_yield (inl Yield) = Ret tt.
Proof. reflexivity. Qed.

Lemma interp_scheduled_erased_unfold s :
  interp_scheduled_erased s = interp_yield (interp_spawn (scheduled_visible s)).
Proof. reflexivity. Qed.

(** Compatibility aliases are erased APIs. *)
Lemma scheduled_alias s : scheduled s = scheduled_visible s.
Proof. reflexivity. Qed.

Lemma interp_scheduled_alias_erased s : interp_scheduled s = interp_scheduled_erased s.
Proof. reflexivity. Qed.

Lemma instr_exp_alias_erased e ctx : instr_exp e ctx = instr_exp_erased e ctx.
Proof. reflexivity. Qed.

Lemma instr_stmt_alias_erased s ctx : instr_stmt s ctx = instr_stmt_erased s ctx.
Proof. reflexivity. Qed.
