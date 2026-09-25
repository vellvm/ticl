(** TICL-facing Yield surface.

    Public tiers exported by this façade:

    - [ICTree.Events.Yield], [Lang.Yield.Syntax], and [Lang.Yield.Denote] expose
      raw source-level threads with [Yield], [Fork], and memory effects.
    - [ICTree.Interp.Yield.Mod] exposes the scheduler, and [scheduled_visible]
      exposes scheduled programs with scheduler [Spawn], cooperative [Yield],
      and memory effects visible.
    - [instr_exp_erased], [instr_stmt_flow_erased], and [instr_stmt_erased]
      expose the state-only TICL view where scheduler/yield observations are
      intentionally erased.

    Every temporal lemma below is an instantiation of a raw rule from
    [ICTree.Logic.Yield] at the Yield denotations. *)
From Stdlib Require Import
  Fin
  Morphisms
  Nat
  Program.Equality
  Strings.String
  Vector.

From ExtLib Require Import
  Data.Map.FMapAList
  Data.String
  Structures.Maps.

From TICL Require Export
  ICTree.Logic.Yield
  Lang.Yield.Syntax
  Lang.Yield.Denote
  Lang.Yield.Interp.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.Eq.Bind
  ICTree.Events.Yield
  ICTree.Events.State
  ICTree.Events.Writer
  ICTree.Interp.Core
  ICTree.Interp.State.Mod
  ICTree.Interp.Yield.Mod
  ICTree.Interp.Yield.SBisim
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.Bind
  ICTree.Logic.CanStep
  ICTree.Logic.Iter
  ICTree.Logic.State
  ICTree.SBisim
  Lang.Maps
  Logic.Core
  Utils.Vectors.

Import ICtree ICTreeNotations TiclNotations VectorNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

(** * Source trigger normalizations *)
(** These expose a source trigger followed by a continuation as the single
    [Vis] node the raw rules expect.  They unfold only source denotations and
    triggers; no interpreter is unfolded here. *)

Local Lemma yget_bind {X} (k : Ctx.Ctx -> ictree YEff X) :
  (x <- yget;; k x) ≅ Vis ((inr (inr Get)) : YEff) k.
Proof.
  unfold yget, ytrigger, ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  unfold resum, ReSum_refl, resum_ret, ReSumRet_refl.
  reflexivity.
Qed.

Local Lemma yput_bind {X} (m : Ctx.Ctx) (k : unit -> ictree YEff X) :
  (x <- yput m;; k x) ≅ Vis ((inr (inr (Put m))) : YEff) k.
Proof.
  unfold yput, ytrigger, ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  unfold resum, ReSum_refl, resum_ret, ReSumRet_refl.
  reflexivity.
Qed.

Local Lemma yyield_bind {X} (k : unit -> ictree YEff X) :
  (x <- yyield;; k x) ≅ Vis ((inl Yield) : YEff) k.
Proof.
  unfold yyield, ytrigger, ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  unfold resum, ReSum_refl, resum_ret, ReSumRet_refl.
  reflexivity.
Qed.

(** The assignment tail is exactly the raw state-update node. *)
Local Lemma denote_yassign_tail name value :
  (ctx <- yget;; yput (add name value ctx);; Ret Fallthrough)
    ≅ Vis ((inr (inr Get)) : YEff)
        (fun σ0 : Ctx.Ctx =>
           Vis ((inr (inr (Put (add name value σ0)))) : YEff)
             (fun _ : unit => Ret Fallthrough)).
Proof.
  rewrite yget_bind.
  apply vis_equ_node; intro σ0.
  apply yput_bind.
Qed.

(** Singleton startup denotations, normalized for the raw scheduler rules. *)
Local Lemma denote_stmt_yskip_ret : denote_stmt YSkip ≅ Ret tt.
Proof.
  rewrite denote_stmt_unfold, denote_stmt_flow_yskip.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Local Lemma denote_stmt_yyield_vis :
  denote_stmt YYield ≅ Vis ((inl Yield) : YEff) (fun _ : unit => Ret tt).
Proof.
  rewrite denote_stmt_unfold, denote_stmt_flow_yyield.
  unfold yyield, ytrigger, ICtree.trigger,
    resum, ReSum_refl, resum_ret, ReSumRet_refl.
  rewrite bind_bind, bind_vis.
  apply vis_equ_node; intro x.
  cbv beta.
  repeat (setoid_rewrite bind_ret_l; cbv beta).
  reflexivity.
Qed.

Local Lemma denote_stmt_yassign_ylit_update name n :
  denote_stmt (YAssign name (YLit n))
    ≅ Vis ((inr (inr Get)) : YEff)
        (fun σ0 : Ctx.Ctx =>
           Vis ((inr (inr (Put (add name n σ0)))) : YEff)
             (fun _ : unit => Ret tt)).
Proof.
  rewrite denote_stmt_unfold, denote_stmt_flow_yassign, denote_exp_ylit.
  unfold yget, yput, ytrigger, ICtree.trigger,
    resum, ReSum_refl, resum_ret, ReSumRet_refl.
  rewrite bind_bind, bind_ret_l; cbv beta.
  rewrite bind_bind, bind_vis.
  apply vis_equ_node; intro σ0.
  cbv beta.
  setoid_rewrite bind_ret_l; cbv beta.
  rewrite bind_bind, bind_vis.
  apply vis_equ_node; intro x.
  cbv beta.
  repeat (setoid_rewrite bind_ret_l; cbv beta).
  reflexivity.
Qed.

(** * Expression rules *)

Lemma axr_yexp_ylit : forall n n' ctx ctx' w w',
    n = n' ->
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (YLit n) ctx},
       w |= AX done= {(n', ctx')} w' ]>.
Proof.
  intros; subst.
  unfold instr_exp_erased.
  rewrite denote_exp_ylit.
  apply axr_thread_ret; [ assumption | split; reflexivity ].
Qed.

Lemma axr_yexp_yvar_some : forall name value ctx ctx' w w',
    lookup name ctx = Some value ->
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (YVar name) ctx},
       w |= AX done= {(value, ctx')} w' ]>.
Proof.
  intros name value ctx ctx' w w' Hlookup Hctx Hw Hnd; subst.
  unfold instr_exp_erased.
  rewrite denote_exp_yvar, yget_bind.
  rewrite instr_thread_get; cbv beta.
  rewrite Hlookup.
  rewrite yyield_bind.
  rewrite instr_thread_yield; cbv beta.
  apply axr_thread_ret; [ assumption | split; reflexivity ].
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
  intros a b x y value ctx ctx' w w' Ha Hb Hvalue Hctx Hw Hnd; subst.
  unfold instr_exp_erased in *.
  rewrite denote_exp_yplus.
  eapply anr_thread_bind_r_eq.
  - exact Ha.
  - cbv beta.
    eapply anr_thread_bind_r_eq.
    + exact Hb.
    + cbv beta.
      apply axr_thread_ret; [ assumption | split; reflexivity ].
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
  intros a b x y value ctx ctx' w w' Ha Hb Hvalue Hctx Hw Hnd; subst.
  unfold instr_exp_erased in *.
  rewrite denote_exp_yminus.
  eapply anr_thread_bind_r_eq.
  - exact Ha.
  - cbv beta.
    eapply anr_thread_bind_r_eq.
    + exact Hb.
    + cbv beta.
      apply axr_thread_ret; [ assumption | split; reflexivity ].
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
  intros a b x y value ctx ctx' w w' Ha Hb Hvalue Hctx Hw Hnd; subst.
  unfold instr_exp_erased in *.
  rewrite denote_exp_ymult.
  eapply anr_thread_bind_r_eq.
  - exact Ha.
  - cbv beta.
    eapply anr_thread_bind_r_eq.
    + exact Hb.
    + cbv beta.
      apply axr_thread_ret; [ assumption | split; reflexivity ].
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
  eapply axr_yexp_yplus; eauto; apply axr_yexp_ylit; auto.
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
  eapply axr_yexp_yminus; eauto; apply axr_yexp_ylit; auto.
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
  eapply axr_yexp_ymult; eauto; apply axr_yexp_ylit; auto.
Qed.

(** * Scheduled statement rules *)

Lemma axr_ystmt_yskip_erased : forall ctx ctx' w w',
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_stmt_erased YSkip ctx},
       w |= AX done= {(tt, ctx')} w' ]>.
Proof.
  intros ctx ctx' w w' Hctx Hw Hnd; subst.
  unfold instr_stmt_erased.
  rewrite (instr_schedule_pool_equ 1 _ _ (Some Fin.F1) ctx'
             (cons_pool_equ _ _ _ _ denote_stmt_yskip_ret (pool_equ_refl _))).
  apply axr_schedule_ret; [ assumption | split; reflexivity ].
Qed.

Lemma axax_ystmt_yyield_erased : forall ctx ctx' w w',
    ctx = ctx' ->
    w = w' ->
    not_done w ->
    <[ {instr_stmt_erased YYield ctx},
       w |= AX AX done= {(tt, ctx')} w' ]>.
Proof.
  intros ctx ctx' w w' Hctx Hw Hnd; subst.
  unfold instr_stmt_erased.
  rewrite (instr_schedule_pool_equ 1 _ _ (Some Fin.F1) ctx'
             (cons_pool_equ _ _ _ _ denote_stmt_yyield_vis (pool_equ_refl _))).
  apply axax_schedule_yield; [ assumption | split; reflexivity ].
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

(** * Flow-preserving statement rules *)

Lemma aur_ystmt_yassign : forall name expr value ctx w ψ R,
    <[ {instr_exp_erased expr ctx}, w |= AX done= {(value, ctx)} w ]> ->
    <( {log (add name value ctx)}, w |= ψ )> ->
    R (Fallthrough, add name value ctx)
      (Obs (Log (add name value ctx)) tt) ->
    <[ {instr_stmt_flow_erased (YAssign name expr) ctx},
       w |= ψ AU AX done R ]>.
Proof.
  intros name expr value ctx w ψ R Hexp Hlog HR.
  unfold instr_stmt_flow_erased, instr_exp_erased in *.
  rewrite denote_stmt_flow_yassign.
  eapply aur_thread_bind_r_eq.
  - cleft. exact Hexp.
  - cbv beta.
    rewrite (denote_yassign_tail name value).
    now apply (aur_thread_update (add name value) Fallthrough ctx).
Qed.

Lemma aul_ystmt_yassign : forall name expr value ctx w ψ φ,
    <[ {instr_exp_erased expr ctx}, w |= AX done= {(value, ctx)} w ]> ->
    <( {log (add name value ctx)}, w |= ψ )> ->
    <( {Ret (Fallthrough, add name value ctx)},
       {Obs (Log (add name value ctx)) tt} |= φ )> ->
    <( {instr_stmt_flow_erased (YAssign name expr) ctx}, w |= ψ AU φ )>.
Proof.
  intros name expr value ctx w ψ φ Hexp Hlog Hret.
  unfold instr_stmt_flow_erased, instr_exp_erased in *.
  rewrite denote_stmt_flow_yassign.
  eapply aul_thread_bind_r_eq.
  - cleft. exact Hexp.
  - cbv beta.
    rewrite (denote_yassign_tail name value).
    now apply (aul_thread_update (add name value) Fallthrough ctx).
Qed.

Lemma anr_ystmt_yseq_fallthrough : forall a b ctx ctx' w w' φ ψ,
    <[ {instr_stmt_flow_erased a ctx},
       w |= φ AN done= {(Fallthrough, ctx')} w' ]> ->
    <[ {instr_stmt_flow_erased b ctx'}, w' |= φ AN ψ ]> ->
    <[ {instr_stmt_flow_erased (YSeq a b) ctx}, w |= φ AN ψ ]>.
Proof.
  intros a b ctx ctx' w w' φ ψ Ha Hb.
  unfold instr_stmt_flow_erased in *.
  rewrite denote_stmt_flow_yseq.
  eapply anr_thread_bind_r_eq; eauto.
Qed.

Lemma aur_ystmt_yseq_fallthrough : forall a b ctx ctx' w w' φ ψ,
    <[ {instr_stmt_flow_erased a ctx},
       w |= φ AU AX done= {(Fallthrough, ctx')} w' ]> ->
    <[ {instr_stmt_flow_erased b ctx'}, w' |= φ AU ψ ]> ->
    <[ {instr_stmt_flow_erased (YSeq a b) ctx}, w |= φ AU ψ ]>.
Proof.
  intros a b ctx ctx' w w' φ ψ Ha Hb.
  unfold instr_stmt_flow_erased in *.
  rewrite denote_stmt_flow_yseq.
  eapply aur_thread_bind_r_eq; eauto.
Qed.

Lemma aul_ystmt_yseq_fallthrough : forall a b ctx ctx' w w' φ ψ,
    <[ {instr_stmt_flow_erased a ctx},
       w |= φ AU AX done= {(Fallthrough, ctx')} w' ]> ->
    <( {instr_stmt_flow_erased b ctx'}, w' |= φ AU ψ )> ->
    <( {instr_stmt_flow_erased (YSeq a b) ctx}, w |= φ AU ψ )>.
Proof.
  intros a b ctx ctx' w w' φ ψ Ha Hb.
  unfold instr_stmt_flow_erased in *.
  rewrite denote_stmt_flow_yseq.
  eapply aul_thread_bind_r_eq; eauto.
Qed.

Lemma yseq_halt_propagates : forall a b ctx ctx' w w' φ,
    <[ {instr_stmt_flow_erased a ctx},
       w |= φ AU AX done= {(HaltThread, ctx')} w' ]> ->
    not_done w' ->
    <[ {instr_stmt_flow_erased (YSeq a b) ctx},
       w |= φ AU AX done= {(HaltThread, ctx')} w' ]>.
Proof.
  intros a b ctx ctx' w w' φ Ha Hnd.
  unfold instr_stmt_flow_erased in *.
  rewrite denote_stmt_flow_yseq.
  eapply aur_thread_bind_r_eq.
  - exact Ha.
  - cbv beta.
    cleft.
    apply axr_thread_ret; [ assumption | split; reflexivity ].
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
  unfold instr_stmt_flow_erased, instr_exp_erased in *.
  rewrite denote_stmt_flow_yif.
  eapply aul_thread_bind_r_eq.
  - cleft; exact Htest.
  - cbv beta.
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
  unfold instr_stmt_flow_erased, instr_exp_erased in *.
  rewrite denote_stmt_flow_yif.
  eapply aur_thread_bind_r_eq.
  - cleft; exact Htest.
  - cbv beta.
    destruct (YieldSyntax.is_true condition); exact Hbranch.
Qed.

(** * Raw source-flow while unrolling facts *)
(** These expose [YStmtFlow] directly, avoiding any claim that the scheduled
    erased unit layer can distinguish loop fallthrough from child-thread
    halt. *)
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

(** * Scheduled assignment rules *)

Lemma aur_ystmt_yassign_ylit_erased : forall name n ctx w ψ R,
    <( {log (add name n ctx)}, w |= ψ )> ->
    R (tt, add name n ctx) (Obs (Log (add name n ctx)) tt) ->
    <[ {instr_stmt_erased (YAssign name (YLit n)) ctx},
       w |= ψ AU AX done R ]>.
Proof.
  intros name n ctx w ψ R Hlog HR.
  unfold instr_stmt_erased.
  rewrite (instr_schedule_pool_equ 1 _ _ (Some Fin.F1) ctx
             (cons_pool_equ _ _ _ _ (denote_stmt_yassign_ylit_update name n) (pool_equ_refl _))).
  now apply (aur_schedule_update (add name n) ctx).
Qed.

Lemma aul_ystmt_yassign_ylit_erased : forall name n ctx w ψ φ,
    <( {log (add name n ctx)}, w |= ψ )> ->
    <( {Ret (tt, add name n ctx)},
       {Obs (Log (add name n ctx)) tt} |= φ )> ->
    <( {instr_stmt_erased (YAssign name (YLit n)) ctx}, w |= ψ AU φ )>.
Proof.
  intros name n ctx w ψ φ Hlog Hret.
  unfold instr_stmt_erased.
  rewrite (instr_schedule_pool_equ 1 _ _ (Some Fin.F1) ctx
             (cons_pool_equ _ _ _ _ (denote_stmt_yassign_ylit_update name n) (pool_equ_refl _))).
  now apply (aul_schedule_update (add name n) ctx).
Qed.
