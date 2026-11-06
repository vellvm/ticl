From TICL Require Import CTree.Logic.Yield.
From TICL Require Import CTree.Interp.Yield.Policy.
(** * The canonical CoCSL (cooperative CSL) source language.

    Syntax ([CExp], [CProg]) and denotation share one CSL effect layer.
    Scheduled command/expression modalities preserve actual continuations,
    pool changes, focus, and RR cursors. Indexed until rules use actual-run
    cutpoints; global rules require observable progress before reentry.
    Source-body return is never confused with native whole-pool termination. *)

From TICL Require Export CTree.Interp.CSL.Mod.

(** The generic Yield event, scheduler, bisimulation, observed-scheduler and
    logic layers, re-exported for source-level clients. *)
From TICL Require Export
  CTree.Events.Yield
  Utils.Vectors
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.Observed
  CTree.Interp.Yield.Policy
  CTree.Logic.Yield
  CTree.Logic.SchedulerFairness
  CTree.Interp.Yield.Fair.

From Stdlib Require Import List Arith.PeanoNat Lia Fin Vector Strings.String
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From ExtLib Require Import Data.Monads.StateMonad
  Structures.Maps Data.Map.FMapAList Data.String.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Trace
  CTree.Logic.Trace
  CTree.Events.Writer
  CTree.Events.Yield
  CTree.Events.Heap
  CTree.Interp.State.Mod
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.Nondeterministic
  CTree.Logic.Trans
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.EG
  CTree.Logic.Bind
  CTree.Logic.State
  CTree.Logic.CanStep
  CTree.Logic.Iter
  Logic.World
  Logic.Core
  Logic.Kripke
  Utils.Vectors.

Import CTreeNotations TiclNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** ** Syntax *)

Module CoCSLSyntax.
  (** Natural-number expressions over the shared variable context. *)
  Inductive CExp : Type :=
  | CVar (name : string)
  | CLit (value : nat)
  | CPlus (a b : CExp)
  | CMinus (a b : CExp)
  | CMult (a b : CExp).

  Inductive CProg : Type -> Type :=
  | CRead (a : nat) : CProg nat
  | CWrite (a v : nat) : CProg unit
  | CEmit (tag value : nat) : CProg unit
  | CYield : CProg unit
  | CFork (body : CProg unit) : CProg unit
  | CRet {A : Type} (value : A) : CProg A
  | CBind {A B : Type} (body : CProg A) (next : A -> CProg B) : CProg B
  | CUntilNone {A : Type} (body : CProg (option A)) : CProg unit
  | CAlloc (size : nat) : CProg nat
  | CFree (base : nat) : CProg unit
  | CCAS (a expected desired : CExp) : CProg bool
  | CEval (e : CExp) : CProg nat
  | CAssign (name : string) (e : CExp) : CProg unit
  | CIf {A : Type} (test : CExp) (yes no : CProg A) : CProg A
  | CWhile (test : CExp) (body : CProg unit) : CProg unit.

  (** Any non-zero natural is true. *)
  Definition is_true (v : nat) : bool := negb (Nat.eqb v 0).
End CoCSLSyntax.
Export CoCSLSyntax.

(** ** Denotation *)

(** Expressions evaluate left to right.  A successful variable read yields
    once before returning the value it captured; a missing variable is
    stuck. *)
Fixpoint denote_exp (e : CExp) : ctree CEff Bn nat :=
  match e with
  | CVar name =>
      ctx <- source_get;;
      match lookup name ctx with
      | Some value => source_yield;; Ret value
      | None => Stuck
      end
  | CLit n => Ret n
  | CPlus a b => x <- denote_exp a;; y <- denote_exp b;; Ret (x + y)%nat
  | CMinus a b => x <- denote_exp a;; y <- denote_exp b;; Ret (x - y)%nat
  | CMult a b => x <- denote_exp a;; y <- denote_exp b;; Ret (x * y)%nat
  end.

Fixpoint denote_flow {A : Type} (p : CProg A) : ctree CEff Bn (option A) :=
  match p in CProg A return ctree CEff Bn (option A) with
  | CRead a => x <- heap_read (E:=CEff) a;; Ret (Some x)
  | CWrite a v => heap_write (E:=CEff) a v;; Ret (Some tt)
  | CEmit q v => CTree.trigger (inr1 (inr1 (inr1 (inr1 (Log (q,v))))) : CEff unit);; Ret (Some tt)
  | CYield => source_yield;; Ret (Some tt)
  | CFork body =>
      child <- source_fork;;
      if child then denote_flow body;; Ret None else Ret (Some tt)
  | CRet x => Ret (Some x)
  | CBind body next =>
      flow <- denote_flow body;;
      match flow with None => Ret None | Some x => denote_flow (next x) end
  | CUntilNone body =>
      CTree.iter
        (fun _ : unit =>
          flow <- denote_flow body;;
          match flow with
          | None => Ret (inr None)
          | Some None => Ret (inr (Some tt))
          | Some (Some _) => Ret (inl tt)
          end) tt
  | CAlloc size => a <- heap_alloc (E:=CEff) size;; Ret (Some a)
  | CFree base => heap_free (E:=CEff) base;; Ret (Some tt)
  | CCAS a expected desired =>
      addr <- denote_exp a;;
      old <- denote_exp expected;;
      value <- denote_exp desired;;
      b <- heap_cas (E:=CEff) addr old value;;
      Ret (Some b)
  | CEval e => value <- denote_exp e;; Ret (Some value)
  | CAssign name e =>
      value <- denote_exp e;;
      ctx <- source_get;;
      source_put (add name value ctx);;
      Ret (Some tt)
  | CIf test yes no =>
      value <- denote_exp test;;
      if CoCSLSyntax.is_true value then denote_flow yes else denote_flow no
  | CWhile test body =>
      CTree.iter
        (fun _ : unit =>
          value <- denote_exp test;;
          if CoCSLSyntax.is_true value then
            flow <- denote_flow body;;
            match flow with
            | Some _ => Ret (inl tt)
            | None => Ret (inr None)
            end
          else Ret (inr (Some tt))) tt
  end.

(** One guarded [CWhile] iteration: a false test exits with [Some tt], a
    completed body continues, and a halted body propagates [None]. *)
Definition cwhile_iteration (test : CExp) (body : CProg unit) (_ : unit)
  : ctree CEff Bn (unit + option unit) :=
  value <- denote_exp test;;
  if CoCSLSyntax.is_true value then
    flow <- denote_flow body;;
    match flow with
    | Some _ => Ret (inl tt)
    | None => Ret (inr None)
    end
  else Ret (inr (Some tt)).

Lemma denote_flow_cwhile (test : CExp) (body : CProg unit) :
  denote_flow (CWhile test body) = CTree.iter (cwhile_iteration test body) tt.
Proof. reflexivity. Qed.

Definition denote (p : CProg unit) : thread sE Bn :=
  denote_flow p;; Ret tt.

Lemma denote_exp_branchfree (e : CExp) : BranchFree (denote_exp e).
Proof.
  induction e as [name|n|a IHa b IHb|a IHa b IHb|a IHa b IHb]; cbn [denote_exp].
  - apply branchfree_bind.
    + unfold source_get, CTree.trigger; apply bf_vis; intro x; apply bf_ret.
    + intro ctx; destruct (lookup name ctx).
      * apply branchfree_bind; [unfold source_yield; apply bf_vis; intros []; apply bf_ret|].
        intros []; apply bf_ret.
      * apply bf_stuck.
  - apply bf_ret.
  - apply branchfree_bind; [exact IHa|intro x].
    apply branchfree_bind; [exact IHb|intro y; apply bf_ret].
  - apply branchfree_bind; [exact IHa|intro x].
    apply branchfree_bind; [exact IHb|intro y; apply bf_ret].
  - apply branchfree_bind; [exact IHa|intro x].
    apply branchfree_bind; [exact IHb|intro y; apply bf_ret].
Qed.

Lemma denote_flow_branchfree {A} (p : CProg A) : BranchFree (denote_flow p).
Proof.
  induction p as [a|a v|q v| |body IH|A x|A B body IH next IHnext|A body IH|size|base
    |a expected desired|e|name e|A test yes IHyes no IHno|test body IH];
    cbn [denote_flow].
  - apply branchfree_bind.
    + unfold heap_read, CTree.trigger; apply bf_vis; intro x; apply bf_ret.
    + intro x; apply bf_ret.
  - apply branchfree_bind.
    + unfold heap_write, CTree.trigger; apply bf_vis; intros []; apply bf_ret.
    + intros []; apply bf_ret.
  - apply branchfree_bind.
    + unfold CTree.trigger; apply bf_vis; intros []; apply bf_ret.
    + intros []; apply bf_ret.
  - apply branchfree_bind.
    + unfold source_yield; apply bf_vis; intros []; apply bf_ret.
    + intros []; apply bf_ret.
  - apply branchfree_bind.
    + unfold source_fork; apply bf_vis; intro b; apply bf_ret.
    + intros []; cbn.
      * apply branchfree_bind; [exact IH|intro flow; apply bf_ret].
      * apply bf_ret.
  - apply bf_ret.
  - apply branchfree_bind; [exact IH|].
    intros [x|]; [apply IHnext|apply bf_ret].
  - apply branchfree_iter; intros [].
    apply branchfree_bind; [exact IH|].
    intros [[x|]|]; apply bf_ret.
  - apply branchfree_bind.
    + unfold heap_alloc, CTree.trigger; apply bf_vis; intro a; apply bf_ret.
    + intro a; apply bf_ret.
  - apply branchfree_bind.
    + unfold heap_free, CTree.trigger; apply bf_vis; intros []; apply bf_ret.
    + intros []; apply bf_ret.
  - apply branchfree_bind; [apply denote_exp_branchfree|intro addr].
    apply branchfree_bind; [apply denote_exp_branchfree|intro old].
    apply branchfree_bind; [apply denote_exp_branchfree|intro value].
    apply branchfree_bind.
    + unfold heap_cas, CTree.trigger; apply bf_vis; intro b; apply bf_ret.
    + intro b; apply bf_ret.
  - apply branchfree_bind; [apply denote_exp_branchfree|intro v; apply bf_ret].
  - apply branchfree_bind; [apply denote_exp_branchfree|intro v].
    apply branchfree_bind.
    + unfold source_get, CTree.trigger; apply bf_vis; intro x; apply bf_ret.
    + intro ctx; apply branchfree_bind.
      * unfold source_put, CTree.trigger; apply bf_vis; intros []; apply bf_ret.
      * intros []; apply bf_ret.
  - apply branchfree_bind; [apply denote_exp_branchfree|intro v].
    destruct (CoCSLSyntax.is_true v); assumption.
  - apply branchfree_iter; intros [].
    apply branchfree_bind; [apply denote_exp_branchfree|intro v].
    destruct (CoCSLSyntax.is_true v); [|apply bf_ret].
    apply branchfree_bind; [exact IH|].
    intros [[]|]; apply bf_ret.
Qed.

Lemma denote_branchfree (p : CProg unit) : BranchFree (denote p).
Proof.
  unfold denote; apply branchfree_bind;
    [apply denote_flow_branchfree|intro flow; apply bf_ret].
Qed.

Lemma denote_fork_bind (p : CProg unit) (next : unit -> CProg unit) :
  denote (CBind (CFork p) next) ≅
  Vis (inr1 (inl1 Fork))
    (fun child : bool => if child then denote p else denote (next tt)).
Proof.
  unfold denote; cbn [denote_flow]; unfold source_fork.
  rewrite !bind_bind, bind_vis.
  step; constructor; intro child.
  rewrite bind_ret_l; destruct child; cbn.
  - rewrite !bind_bind.
    apply equ_clo_bind_eq; intro flow.
    rewrite !bind_ret_l; reflexivity.
  - rewrite !bind_ret_l; reflexivity.
Qed.

(** ** Head normalisation of [denote_flow].

    What a single source instruction looks like at the head of a thread,
    before any scheduling is applied.  The [interp_*] families below are
    built on top of these raw equations. *)

Lemma source_raw_read_head a (K : option nat -> thread sE Bn) :
  (denote_flow (CRead a) >>= K) ≅ Vis (inr1 (inr1 (inl1 (HRead a)))) (fun v => K (Some v)).
Proof.
  cbn [denote_flow]; unfold heap_read, CTree.trigger; rewrite !bind_bind, bind_vis.
  step; constructor; intro x; rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_write_head a v (K : option unit -> thread sE Bn) :
  (denote_flow (CWrite a v) >>= K) ≅ Vis (inr1 (inr1 (inl1 (HWrite a v)))) (fun _ => K (Some tt)).
Proof.
  cbn [denote_flow]; unfold heap_write, CTree.trigger; rewrite !bind_bind, bind_vis.
  step; constructor; intros [].
  change (((Ret tt : thread sE Bn) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
    K (Some tt)).
  rewrite !bind_ret_l; reflexivity.
Qed.

(** Immediate CAS rules (raw head, scheduler, state, segment, and AN/AU/AG)
    apply to literal operands.  General operands first evaluate with
    [source_raw_cas]. *)
Lemma source_raw_cas_head a old desired (K : option bool -> thread sE Bn) :
  (denote_flow (CCAS (CLit a) (CLit old) (CLit desired)) >>= K) ≅
    Vis (inr1 (inr1 (inl1 (HCAS a old desired)))) (fun b => K (Some b)).
Proof.
  cbn [denote_flow denote_exp]; rewrite !bind_ret_l.
  unfold heap_cas, CTree.trigger; rewrite !bind_bind, bind_vis.
  step; constructor; intro x; rewrite !bind_ret_l; reflexivity.
Qed.

(** Evaluate operands once, in address/expected/desired order, before the
    atomic heap operation.  Expression yields remain inside the thread. *)
Lemma source_raw_cas (a expected desired : CExp)
    (K : option bool -> thread sE Bn) :
  (denote_flow (CCAS a expected desired) >>= K) ≅
  (addr <- denote_exp a;;
   old <- denote_exp expected;;
   value <- denote_exp desired;;
   denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K).
Proof.
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro addr; rewrite bind_bind.
  apply equ_clo_bind_eq; intro old; rewrite bind_bind.
  apply equ_clo_bind_eq; intro value.
  cbn [denote_exp]; rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_emit_head tag value (K : option unit -> thread sE Bn) :
  (denote_flow (CEmit tag value) >>= K) ≅
    Vis (inr1 (inr1 (inr1 (inr1 (Log (tag,value)))))) (fun _ => K (Some tt)).
Proof.
  cbn [denote_flow]; unfold CTree.trigger.
  rewrite bind_bind, bind_vis; step; constructor; intros [].
  rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_yield_head (K : option unit -> thread sE Bn) :
  (denote_flow CYield >>= K) ≅ Vis (inl1 Yield) (fun _ => K (Some tt)).
Proof.
  cbn [denote_flow]; unfold source_yield.
  rewrite bind_bind, bind_vis; step; constructor; intros [].
  change (((Ret tt : thread sE Bn) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
    K (Some tt)).
  rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_alloc_head size (K : option nat -> thread sE Bn) :
  (denote_flow (CAlloc size) >>= K) ≅
    Vis (inr1 (inr1 (inl1 (HAlloc size)))) (fun base => K (Some base)).
Proof.
  cbn [denote_flow]; unfold heap_alloc, CTree.trigger.
  rewrite bind_bind, bind_vis; step; constructor; intro base.
  rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_free_head base (K : option unit -> thread sE Bn) :
  (denote_flow (CFree base) >>= K) ≅
    Vis (inr1 (inr1 (inl1 (HFree base)))) (fun _ => K (Some tt)).
Proof.
  cbn [denote_flow]; unfold heap_free, CTree.trigger; rewrite !bind_bind, bind_vis.
  step; constructor; intros [].
  change (((Ret tt : thread sE Bn) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
    K (Some tt)).
  rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_fork_head (child : CProg unit) (K : option unit -> thread sE Bn) :
  (denote_flow (CFork child) >>= K) ≅
    Vis (inr1 (inl1 Fork))
      (fun spawned : bool => if spawned
        then denote_flow child >>= fun _ => K None else K (Some tt)).
Proof.
  cbn [denote_flow]; unfold source_fork.
  rewrite bind_bind, bind_vis; step; constructor; intro spawned.
  rewrite bind_ret_l; destruct spawned; cbn.
  - rewrite bind_bind; apply equ_clo_bind_eq; intro flow.
    rewrite bind_ret_l; reflexivity.
  - apply bind_ret_l.
Qed.

(** These are the actual [CUntilNone] continuations, including halt flow. *)
Definition until_tail {A} (body : CProg (option A))
  (K : option unit -> thread sE Bn) (flow : option (option A)) : thread sE Bn :=
  match flow with
  | None => K None
  | Some None => K (Some tt)
  | Some (Some _) => Guard (denote_flow (CUntilNone body) >>= K)
  end.

(** Raw source equations retain the outer option halt flow: [None] skips
    [next] and reaches the continuation unchanged, and [Some x] runs [next x]
    before the continuation, so a completed callee returns through its caller
    before any following instruction (such as a yield). *)
Lemma source_raw_bind {A B} (p : CProg A) (next : A -> CProg B)
  (K : option B -> thread sE Bn) :
  (denote_flow (CBind p next) >>= K) ≅
  (denote_flow p >>= fun flow =>
    match flow with None => K None | Some x => denote_flow (next x) >>= K end).
Proof.
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intros [x|]; [reflexivity|apply bind_ret_l].
Qed.

Lemma source_raw_ret {A} (x : A) (K : option A -> thread sE Bn) :
  (denote_flow (CRet x) >>= K) ≅ K (Some x).
Proof. cbn [denote_flow]; apply bind_ret_l. Qed.

Lemma source_raw_until {A} (body : CProg (option A))
  (K : option unit -> thread sE Bn) :
  (denote_flow (CUntilNone body) >>= K) ≅
  (denote_flow body >>= until_tail body K).
Proof.
  set (loop_body := fun _ : unit =>
    flow <- denote_flow body;;
    match flow with
    | None => Ret (inr (None : option unit))
    | Some None => Ret (inr (Some tt))
    | Some (Some _) => Ret (inl tt)
    end).
  change ((CTree.iter loop_body tt >>= K) ≅
    (denote_flow body >>= fun flow =>
      match flow with
      | None => K None
      | Some None => K (Some tt)
      | Some (Some _) => Guard (CTree.iter loop_body tt >>= K)
      end)).
  transitivity ((loop_body tt >>= fun lr =>
    match lr with
    | inl j => Guard (CTree.iter loop_body j)
    | inr result => Ret result
    end) >>= K).
  - apply equ_clo_bind with (S := eq).
    + apply unfold_iter.
    + intros r r' <-; reflexivity.
  - etransitivity; [apply bind_bind|].
    unfold loop_body at 1.
    etransitivity; [apply bind_bind|].
    apply equ_clo_bind_eq; intros [[x|]|]; cbn.
    + etransitivity; [apply bind_ret_l|]. apply bind_guard.
    + etransitivity; [apply bind_ret_l|]. apply bind_ret_l.
    + etransitivity; [apply bind_ret_l|]. apply bind_ret_l.
Qed.

(** Yield-style expression and control statements, as raw CPS equations. *)
Lemma source_raw_eval (e : CExp) (K : option nat -> thread sE Bn) :
  (denote_flow (CEval e) >>= K) ≅
  (denote_exp e >>= fun value => K (Some value)).
Proof.
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro value; apply bind_ret_l.
Qed.

Lemma source_raw_assign (name : string) (e : CExp)
    (K : option unit -> thread sE Bn) :
  (denote_flow (CAssign name e) >>= K) ≅
  (value <- denote_exp e;; ctx <- source_get;;
   source_put (add name value ctx);; K (Some tt)).
Proof.
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro value; rewrite bind_bind.
  apply equ_clo_bind_eq; intro ctx; rewrite bind_bind.
  apply equ_clo_bind_eq; intros []; apply bind_ret_l.
Qed.

Lemma source_raw_if {A} (test : CExp) (yes no : CProg A)
    (K : option A -> thread sE Bn) :
  (denote_flow (CIf test yes no) >>= K) ≅
  (value <- denote_exp test;;
   if CoCSLSyntax.is_true value then denote_flow yes >>= K
   else denote_flow no >>= K).
Proof.
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro value; destruct (CoCSLSyntax.is_true value); reflexivity.
Qed.

Lemma source_raw_while (test : CExp) (body : CProg unit)
    (K : option unit -> thread sE Bn) :
  (denote_flow (CWhile test body) >>= K) ≅
  (CTree.iter (cwhile_iteration test body) tt >>= K).
Proof. rewrite denote_flow_cwhile; reflexivity. Qed.

(** ** Runners

    A pool of source programs runs under either scheduler from an explicit
    full state [((h,allocs),(ctx,c))]; the singleton runners start focused,
    and round robin starts at cursor [0]. Round-robin program observations
    are logged under [inl], and scheduling picks under [inr]; nondeterministic
    runs keep the program-only observation alphabet. *)
Definition csl_pool {n} (ps : Vector.t (CProg unit) n) : pool sE Bn n :=
  Vector.map denote ps.

Definition run_nd_pool {n} (ps : Vector.t (CProg unit) n)
    (focus : option (Fin.t n)) (s : SSig)
  : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) :=
  interp_schedule_nd sh n (csl_pool ps) focus s.

Definition run_rr_pool {n} (ps : Vector.t (CProg unit) n)
    (focus : option (Fin.t n)) (cursor : nat) (s : SSig)
  : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) :=
  interp_schedule_rr sh n (csl_pool ps) focus cursor s.

Definition run_nd (p : CProg unit) (s : SSig)
  : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) :=
  run_nd_pool [p]%vector (Some Fin.F1) s.

Definition run_rr (p : CProg unit) (s : SSig)
  : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) :=
  run_rr_pool [p]%vector (Some Fin.F1) 0 s.

(** Derived recurrence of payload-emission edges for every initial counter. *)
Definition run_rr_recurrently_emits
    (p : CProg unit) (memory : ManagedHeap) (ctx : Ctx.Ctx)
    (P : nat * nat -> Prop) : Prop :=
  forall c,
    recurrent_label (csl_label_emitsW P) (run_rr p (memory,(ctx,c))).

Lemma run_nd_unfold (p : CProg unit) (s : SSig) :
  run_nd p s = interp_schedule_nd sh 1 [denote p]%vector (Some Fin.F1) s.
Proof. reflexivity. Qed.

Lemma run_rr_unfold (p : CProg unit) (s : SSig) :
  run_rr p s = interp_schedule_rr sh 1 [denote p]%vector (Some Fin.F1) 0 s.
Proof. reflexivity. Qed.

(** ** Expression execution

    A literal is pure.  A variable reads the shared context, and on success
    yields once before returning the captured value; a missing variable is
    stuck, faulting the whole run. *)

Lemma source_raw_lit {X} n (K : nat -> ctree CEff Bn X) :
  (denote_exp (CLit n) >>= K) ≅ K n.
Proof. cbn [denote_exp]; rewrite bind_ret_l; reflexivity. Qed.

Lemma source_raw_var {X} name (K : nat -> ctree CEff Bn X) :
  (denote_exp (CVar name) >>= K) ≅
  (source_get >>= fun ctx =>
     match lookup name ctx with
     | Some value => Vis (inl1 Yield : CEff unit) (fun _ => K value)
     | None => Stuck
     end).
Proof.
  cbn [denote_exp]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro ctx.
  destruct (lookup name ctx) as [value|].
  - unfold source_yield; rewrite bind_bind, bind_vis.
    apply vis_equ_node; intros []; cbv beta.
    etransitivity; [apply bind_ret_l|]; cbv beta.
    apply bind_ret_l.
  - apply bind_stuck.
Qed.

Lemma interp_rr_lit n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  v (K : nat -> thread sE Bn) m (s : SSig) :
  interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit v) >>= K)) (Some i) m s ≅
  interp_schedule_rr sh (S n) (ts @ i := K v) (Some i) m s.
Proof.
  apply interp_schedule_fair_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_lit.
Qed.

Lemma interp_nd_lit n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  v (K : nat -> thread sE Bn) (s : SSig) :
  interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit v) >>= K)) (Some i) s ≅
  interp_schedule_nd sh (S n) (ts @ i := K v) (Some i) s.
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_lit.
Qed.

(** Assignment evaluates its expression, then performs a late
    read-modify-write of the shared context. *)
Lemma interp_rr_assign n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name e (K : option unit -> thread sE Bn) m (s : SSig) :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) m s ≅
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_exp e >>= fun value =>
      source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt)))
    (Some i) m s.
Proof.
  apply interp_schedule_fair_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_assign.
Qed.

Lemma interp_nd_assign n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name e (K : option unit -> thread sE Bn) (s : SSig) :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) s ≅
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_exp e >>= fun value =>
      source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt)))
    (Some i) s.
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_assign.
Qed.

(** Expand expression CAS inside the focused thread, retaining every yield
    and the scheduler's interleavings before the literal heap operation. *)
Lemma interp_rr_cas_exp n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
    (a expected desired : CExp) (K : option bool -> thread sE Bn)
    m (s : SSig) :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m s ≅
  interp_schedule_rr sh (S n)
    (ts @ i :=
      (addr <- denote_exp a;; old <- denote_exp expected;; value <- denote_exp desired;;
       denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) m s.
Proof.
  apply interp_schedule_fair_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_cas.
Qed.

Lemma interp_nd_cas_exp n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
    (a expected desired : CExp) (K : option bool -> thread sE Bn) (s : SSig) :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) s ≅
  interp_schedule_nd sh (S n)
    (ts @ i :=
      (addr <- denote_exp a;; old <- denote_exp expected;; value <- denote_exp desired;;
       denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) s.
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_cas.
Qed.

Lemma interp_rr_var n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) m (s : SSig) :
  lookup name (csl_context s) = Some value ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) m s ~
  interp_schedule_rr sh (S n) (ts @ i := K value) None m s.
Proof.
  intro Hlookup.
  rewrite (interp_schedule_fair_equ rr_scheduler sh (S n) _ _ (Some i) m s
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_var name K))).
  rewrite interp_rr_get_ctx; cbv beta; rewrite Hlookup.
  erewrite interp_schedule_fair_yield by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_var n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) (s : SSig) :
  lookup name (csl_context s) = Some value ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) s ~
  interp_schedule_nd sh (S n) (ts @ i := K value) None s.
Proof.
  intro Hlookup.
  rewrite (interp_schedule_nd_equ sh (S n) _ _ (Some i) s
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_var name K))).
  rewrite interp_nd_get_ctx; cbv beta; rewrite Hlookup.
  erewrite (interp_schedule_nd_yield sh)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_var_missing n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) m (s : SSig) :
  lookup name (csl_context s) = None ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) m s ~
  (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intro Hlookup.
  rewrite (interp_schedule_fair_equ rr_scheduler sh (S n) _ _ (Some i) m s
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_var name K))).
  rewrite interp_rr_get_ctx; cbv beta; rewrite Hlookup.
  rewrite (interp_schedule_fair_stuck rr_scheduler sh n _ i m s)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  reflexivity.
Qed.

Lemma interp_nd_var_missing n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) (s : SSig) :
  lookup name (csl_context s) = None ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) s ~
  (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  intro Hlookup.
  rewrite (interp_schedule_nd_equ sh (S n) _ _ (Some i) s
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_var name K))).
  rewrite interp_nd_get_ctx; cbv beta; rewrite Hlookup.
  rewrite (interp_schedule_nd_stuck sh n _ i s)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  reflexivity.
Qed.

Lemma interp_rr_ret {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m σ ≅
  interp_schedule_rr sh (S n) (ts @ i := K (Some x)) (Some i) m σ.
Proof.
  apply interp_schedule_fair_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_ret.
Qed.

Lemma interp_rr_read n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m σ ~
  (translate relabel_log (interp_state sh (heap_read (E:=sE) (B:=Bn) a) σ) >>= fun '(σ',x) =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some x)) (Some i) m σ').
Proof.
  rewrite (interp_schedule_fair_user_bind rr_scheduler sh n ts i _ (inl1 (HRead a))
    (fun x => K (Some x)) m σ (source_raw_read_head a K)).
  unfold heap_read; rewrite translate_interp_state_trigger_bind; reflexivity.
Qed.

Lemma interp_rr_alloc n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) m sigma :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m sigma ~
  (translate relabel_log (interp_state sh (heap_alloc (E:=sE) (B:=Bn) size) sigma) >>= fun '(sigma',base) =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some base)) (Some i) m sigma').
Proof.
  rewrite (interp_schedule_fair_user_bind rr_scheduler sh n ts i _ (inl1 (HAlloc size))
    (fun base => K (Some base)) m sigma (source_raw_alloc_head size K)).
  unfold heap_alloc; rewrite translate_interp_state_trigger_bind; reflexivity.
Qed.

Lemma interp_rr_cas n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) m sigma :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K))
    (Some i) m sigma ~
  (translate relabel_log (interp_state sh (heap_cas (E:=sE) (B:=Bn) a expected desired) sigma) >>= fun '(sigma',b) =>
   interp_schedule_rr sh (S n) (ts @ i := K (Some b)) (Some i) m sigma').
Proof.
  rewrite (interp_schedule_fair_user_bind rr_scheduler sh n ts i _ (inl1 (HCAS a expected desired))
    (fun b => K (Some b)) m sigma (source_raw_cas_head a expected desired K)).
  unfold heap_cas; rewrite translate_interp_state_trigger_bind; reflexivity.
Qed.

Lemma interp_rr_write n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE Bn) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m σ ~
  (translate relabel_log (interp_state sh (heap_write (E:=sE) (B:=Bn) a v) σ) >>= fun '(σ',_) =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m σ').
Proof.
  rewrite (interp_schedule_fair_user_bind rr_scheduler sh n ts i _ (inl1 (HWrite a v))
    (fun _ => K (Some tt)) m σ (source_raw_write_head a v K)).
  unfold heap_write; rewrite translate_interp_state_trigger_bind; reflexivity.
Qed.

Lemma interp_rr_emit n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  q v (K : option unit -> thread sE Bn) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit q v) >>= K)) (Some i) m σ ~
  (translate relabel_log (interp_state sh (semit q v) σ) >>= fun '(σ',_) =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m σ').
Proof.
  rewrite (interp_schedule_fair_user_bind rr_scheduler sh n ts i _ (inr1 (inr1 (Log (q,v))))
    (fun _ => K (Some tt)) m σ (source_raw_emit_head q v K)).
  unfold semit; rewrite translate_interp_state_trigger_bind; reflexivity.
Qed.

Lemma interp_rr_bind {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) m σ :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m σ ≅
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun r =>
      match r with None => K None | Some x => denote_flow (next x) >>= K end))
    (Some i) m σ.
Proof.
  apply interp_schedule_fair_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_bind.
Qed.

Lemma interp_rr_yield n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) m σ ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) None m σ.
Proof.
  pose proof (interp_schedule_fair_equ rr_scheduler sh (S n)
    (ts @ i := (denote_flow CYield >>= K))
    (ts @ i := Vis (inl1 Yield) (fun _ => K (Some tt)))
    (Some i) m σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_yield_head K))) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_fair_yield by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_fork n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg unit) (K : option unit -> thread sE Bn) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork p) >>= K)) (Some i) m σ ~
  interp_schedule_rr sh (S (S n))
    ((denote_flow p >>= fun _ => K None) :: (ts @ i := K (Some tt)))
    (Some (Fin.FS i)) m σ.
Proof.
  pose proof (interp_schedule_fair_equ rr_scheduler sh (S n)
    (ts @ i := (denote_flow (CFork p) >>= K))
    (ts @ i := Vis (inr1 (inl1 Fork))
      (fun child : bool => if child
        then denote_flow p >>= fun _ => K None else K (Some tt)))
    (Some i) m σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_fork_head p K))) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_fair_fork by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_until_none {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) m σ :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m σ ≅
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= fun r =>
      match r with
      | None => K None
      | Some None => K (Some tt)
      | Some (Some _) => Guard (denote_flow (CUntilNone body) >>= K)
      end)) (Some i) m σ.
Proof.
  apply interp_schedule_fair_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_until.
Qed.

Lemma run_rr_fork_bind (p : CProg unit) (next : unit -> CProg unit) (s : SSig) :
  run_rr (CBind (CFork p) next) s ~
  interp_schedule_rr sh 2 [denote p; denote (next tt)]%vector
    (Some (Fin.FS Fin.F1)) 0 s.
Proof.
  rewrite run_rr_unfold.
  assert (Hpool : pool_equ [denote (CBind (CFork p) next)]%vector
    [Vis (inr1 (inl1 Fork))
      (fun child : bool => if child then denote p else denote (next tt))]%vector).
  { apply cons_pool_equ; [apply denote_fork_bind|apply pool_equ_refl]. }
  rewrite (interp_schedule_fair_equ rr_scheduler sh 1 _ _ (Some Fin.F1) 0 s Hpool).
  erewrite interp_schedule_fair_fork by reflexivity.
  reflexivity.
Qed.

(** ** The scheduler-generic instrumented runner.

    Scheduling picks are logged as [inr slot]; program observations are
    relabelled [inl].  Only the equations the startup chains of the examples
    need are ported from the round-robin set. *)
Definition run_fair_pool (sch : Scheduler) {n} (ps : Vector.t (CProg unit) n)
    (focus : option (Fin.t n)) (st : sched_state sch) (s : SSig)
  : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) :=
  interp_schedule_fair sch sh n (csl_pool ps) focus st s.

Definition run_fair (sch : Scheduler) (p : CProg unit) (st : sched_state sch) (s : SSig)
  : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) :=
  run_fair_pool sch [p]%vector (Some Fin.F1) st s.

Lemma run_fair_unfold sch (p : CProg unit) st (s : SSig) :
  run_fair sch p st s = interp_schedule_fair sch sh 1 [denote p]%vector (Some Fin.F1) st s.
Proof. reflexivity. Qed.

Lemma interp_fair_bind sch {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) st σ :
  interp_schedule_fair sch sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) st σ ≅
  interp_schedule_fair sch sh (S n)
    (ts @ i := (denote_flow p >>= fun r =>
      match r with None => K None | Some x => denote_flow (next x) >>= K end))
    (Some i) st σ.
Proof.
  apply interp_schedule_fair_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_bind.
Qed.

Lemma interp_fair_ret sch {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) st σ :
  interp_schedule_fair sch sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) st σ ≅
  interp_schedule_fair sch sh (S n) (ts @ i := K (Some x)) (Some i) st σ.
Proof.
  apply interp_schedule_fair_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_ret.
Qed.

Lemma interp_fair_yield sch n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) st σ :
  interp_schedule_fair sch sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) st σ ~
  interp_schedule_fair sch sh (S n) (ts @ i := K (Some tt)) None st σ.
Proof.
  rewrite (interp_schedule_fair_equ sch sh (S n)
    (ts @ i := (denote_flow CYield >>= K))
    (ts @ i := Vis (inl1 Yield) (fun _ => K (Some tt)))
    (Some i) st σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_yield_head K))).
  erewrite interp_schedule_fair_yield by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_fair_fork sch n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg unit) (K : option unit -> thread sE Bn) st σ :
  interp_schedule_fair sch sh (S n) (ts @ i := (denote_flow (CFork p) >>= K)) (Some i) st σ ~
  interp_schedule_fair sch sh (S (S n))
    ((denote_flow p >>= fun _ => K None) :: (ts @ i := K (Some tt)))
    (Some (Fin.FS i)) st σ.
Proof.
  rewrite (interp_schedule_fair_equ sch sh (S n)
    (ts @ i := (denote_flow (CFork p) >>= K))
    (ts @ i := Vis (inr1 (inl1 Fork))
      (fun child : bool => if child
        then denote_flow p >>= fun _ => K None else K (Some tt)))
    (Some i) st σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_fork_head p K))).
  erewrite interp_schedule_fair_fork by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma run_fair_fork_bind sch (p : CProg unit) (next : unit -> CProg unit) st (s : SSig) :
  run_fair sch (CBind (CFork p) next) st s ~
  interp_schedule_fair sch sh 2 [denote p; denote (next tt)]%vector
    (Some (Fin.FS Fin.F1)) st s.
Proof.
  rewrite run_fair_unfold.
  assert (Hpool : pool_equ [denote (CBind (CFork p) next)]%vector
    [Vis (inr1 (inl1 Fork))
      (fun child : bool => if child then denote p else denote (next tt))]%vector).
  { apply cons_pool_equ; [apply denote_fork_bind|apply pool_equ_refl]. }
  rewrite (interp_schedule_fair_equ sch sh 1 _ _ (Some Fin.F1) st s Hpool).
  erewrite interp_schedule_fair_fork by reflexivity.
  reflexivity.
Qed.

Lemma interp_nd_source_ret {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) σ ≅
  interp_schedule_nd sh (S n) (ts @ i := K (Some x)) (Some i) σ.
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_ret.
Qed.

Lemma interp_nd_source_read n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) σ ~
  (interp_state sh (heap_read (E:=sE) (B:=Bn) a) σ >>= fun '(σ',x) =>
    interp_schedule_nd sh (S n) (ts @ i := K (Some x)) (Some i) σ').
Proof.
  apply (interp_schedule_nd_user_bind sh n ts i _ (inl1 (HRead a))
    (fun x => K (Some x)) σ).
  apply source_raw_read_head.
Qed.

Lemma interp_nd_source_alloc n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) sigma :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) sigma ~
  (interp_state sh (heap_alloc (E:=sE) (B:=Bn) size) sigma >>= fun '(sigma',base) =>
    interp_schedule_nd sh (S n) (ts @ i := K (Some base)) (Some i) sigma').
Proof.
  apply (interp_schedule_nd_user_bind sh n ts i _ (inl1 (HAlloc size))
    (fun base => K (Some base)) sigma).
  apply source_raw_alloc_head.
Qed.

Lemma interp_nd_source_cas n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) sigma :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K))
    (Some i) sigma ~
  (interp_state sh (heap_cas (E:=sE) (B:=Bn) a expected desired) sigma >>= fun '(sigma',b) =>
   interp_schedule_nd sh (S n) (ts @ i := K (Some b)) (Some i) sigma').
Proof.
  apply (interp_schedule_nd_user_bind sh n ts i _ (inl1 (HCAS a expected desired))
    (fun b => K (Some b)) sigma).
  apply source_raw_cas_head.
Qed.

Lemma interp_nd_source_write n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE Bn) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) σ ~
  (interp_state sh (heap_write (E:=sE) (B:=Bn) a v) σ >>= fun '(σ',_) =>
    interp_schedule_nd sh (S n) (ts @ i := K (Some tt)) (Some i) σ').
Proof.
  apply (interp_schedule_nd_user_bind sh n ts i _ (inl1 (HWrite a v))
    (fun _ => K (Some tt)) σ).
  apply source_raw_write_head.
Qed.

Lemma interp_nd_source_emit n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  q v (K : option unit -> thread sE Bn) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit q v) >>= K)) (Some i) σ ~
  (interp_state sh (semit q v) σ >>= fun '(σ',_) =>
    interp_schedule_nd sh (S n) (ts @ i := K (Some tt)) (Some i) σ').
Proof.
  apply (interp_schedule_nd_user_bind sh n ts i _ (inr1 (inr1 (Log (q,v))))
    (fun _ => K (Some tt)) σ).
  apply source_raw_emit_head.
Qed.

Lemma interp_nd_source_bind {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) σ :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) σ ≅
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun r =>
      match r with None => K None | Some x => denote_flow (next x) >>= K end))
    (Some i) σ.
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_bind.
Qed.

Lemma interp_nd_source_yield n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) σ ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some tt)) None σ.
Proof.
  pose proof (interp_schedule_nd_equ sh (S n)
    (ts @ i := (denote_flow CYield >>= K))
    (ts @ i := Vis (inl1 Yield) (fun _ => K (Some tt)))
    (Some i) σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_yield_head K))) as Hpool.
  rewrite Hpool.
  erewrite (interp_schedule_nd_yield sh) by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_fork n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg unit) (K : option unit -> thread sE Bn) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork p) >>= K)) (Some i) σ ~
  interp_schedule_nd sh (S (S n))
    ((denote_flow p >>= fun _ => K None) :: (ts @ i := K (Some tt)))
    (Some (Fin.FS i)) σ.
Proof.
  pose proof (interp_schedule_nd_equ sh (S n)
    (ts @ i := (denote_flow (CFork p) >>= K))
    (ts @ i := Vis (inr1 (inl1 Fork))
      (fun child : bool => if child
        then denote_flow p >>= fun _ => K None else K (Some tt)))
    (Some i) σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_fork_head p K))) as Hpool.
  rewrite Hpool.
  erewrite (interp_schedule_nd_fork sh) by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_until_none {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) σ :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) σ ≅
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= fun r =>
      match r with
      | None => K None
      | Some None => K (Some tt)
      | Some (Some _) => Guard (denote_flow (CUntilNone body) >>= K)
      end)) (Some i) σ.
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_until.
Qed.

(** [interp_state_trigger] exposes the handler call under the generic
    [Monad.bind]; fold it back to [CTree.bind] so the [sbisim] congruences
    for [bind] apply. *)
Ltac csl_monad_bind :=
  repeat match goal with
  | |- context [ @Monad.bind ?M ?I ?X ?Y ?a ?k ] =>
      change (@Monad.bind M I X Y a k) with (CTree.bind a k)
  end.



(** The first-fit witness of a finite heap, independent of any handler. *)
Lemma first_fit_exists h size :
  heap_finite h -> Nat.lt 0 size ->
  exists base,
    Nat.lt 0 base /\ block_free h base size /\
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size).
Proof.
  intros Finite Pos.
  destruct (heap_handler_alloc_finite (F:=void1) (B:=B2) (Sigma:=unit) h (fun _ => None) size tt Finite Pos)
    as (base & Base & Free & First & _).
  exists base; auto.
Qed.

(** Successful checked writes expose their post-operation memory before
    continuing at the same focus and cursor. *)
Lemma interp_rr_write_present n
  (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE Bn) m h allocs ctx c :
  h a <> None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  (log (inl (CSLHeap (upd h a v,allocs)));;
   interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
     (Some i) m ((upd h a v,allocs),(ctx,c))).
Proof.
  intro Present.
  pose proof (interp_heapW_wr_present CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))) a h allocs (ctx,c) v
    (fun x : unit => (Ret x : ctree sE Bn unit)) Present) as Hstate.
  rewrite bind_ret_r in Hstate; setoid_rewrite interp_state_ret in Hstate.
  rewrite interp_rr_write; csl_lift_handler_result Hstate.
  rewrite translate_log_bind, bind_bind;
  setoid_rewrite translate_ret; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_source_write_present n
  (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE Bn) h allocs ctx c :
  h a <> None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  (log (CSLHeap (upd h a v,allocs));;
   interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
     (Some i) ((upd h a v,allocs),(ctx,c))).
Proof.
  intro Present.
  pose proof (interp_heapW_wr_present CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))) a h allocs (ctx,c) v
    (fun x : unit => (Ret x : ctree sE Bn unit)) Present) as Hstate.
  rewrite bind_ret_r in Hstate; setoid_rewrite interp_state_ret in Hstate.
  rewrite interp_nd_source_write; csl_lift_handler_result Hstate.
  rewrite bind_bind; setoid_rewrite bind_ret_l; reflexivity.
Qed.
Lemma interp_rr_read_value n
  (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) m h allocs ctx c :
  h a = Some value ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some value)) (Some i) m ((h,allocs),(ctx,c)).
Proof.
  intro Lookup.
  pose proof (interp_heapW_rd CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))) a h allocs (ctx,c) value
    (fun x : nat => (Ret x : ctree sE Bn nat)) Lookup) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_rr_read.
  csl_lift_handler_result Hstate.
  rewrite translate_ret, bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_source_read_value n
  (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c :
  h a = Some value ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some value)) (Some i) ((h,allocs),(ctx,c)).
Proof.
  intro Lookup.
  pose proof (interp_heapW_rd CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))) a h allocs (ctx,c) value
    (fun x : nat => (Ret x : ctree sE Bn nat)) Lookup) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_nd_source_read.
  csl_lift_handler_result Hstate.
  rewrite bind_ret_l; reflexivity.
Qed.

(** Checked operations with their scheduler continuation held fixed. *)

Lemma interp_rr_emit_log n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) m memory ctx c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,(ctx,c)) ~
  (log (inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat);;
   interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))).
Proof.
  pose proof (interp_csl_emit (tag,value) memory ctx c
    (fun x : unit => (Ret x : ctree sE Bn unit))) as Hemit.
  rewrite bind_ret_r in Hemit.
  setoid_rewrite interp_state_ret in Hemit.
  rewrite interp_rr_emit; unfold semit.
  rewrite Hemit, translate_log_bind, bind_bind.
  setoid_rewrite translate_ret; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_cas_value n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) m h allocs ctx c :
  h a = Some current ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  (if Nat.eqb current expected then
    log (inl (CSLHeap (upd h a desired,allocs)));;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),(ctx,c))).
Proof.
  intro Lookup; rewrite interp_rr_cas.
  destruct (Nat.eqb current expected) eqn:Cmp.
  - apply Nat.eqb_eq in Cmp; subst current.
    pose proof (interp_heapW_cas_success CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))) a expected desired h allocs (ctx,c)
      (fun x : bool => (Ret x : ctree sE Bn bool)) Lookup) as Hstate.
    rewrite bind_ret_r in Hstate; setoid_rewrite interp_state_ret in Hstate.
    csl_lift_handler_result Hstate.
    rewrite translate_log_bind, bind_bind;
    setoid_rewrite translate_ret; setoid_rewrite bind_ret_l; reflexivity.
  - apply Nat.eqb_neq in Cmp.
    pose proof (interp_heapW_cas_failure CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))) a expected desired current h allocs (ctx,c)
      (fun x : bool => (Ret x : ctree sE Bn bool)) Lookup Cmp) as Hstate.
    rewrite bind_ret_r, interp_state_ret in Hstate.
    csl_lift_handler_result Hstate.
    rewrite translate_ret, bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_alloc_first n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) m h allocs ctx c :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));;
   interp_schedule_rr sh (S n)
     (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))).
Proof.
  intros Pos Base Free First.
  pose proof (interp_heapW_alloc_first CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))) h allocs size base (ctx,c)
    (fun x : nat => (Ret x : ctree sE Bn nat)) Pos Base Free First) as Hstate.
  rewrite bind_ret_r in Hstate; setoid_rewrite interp_state_ret in Hstate.
  rewrite interp_rr_alloc; csl_lift_handler_result Hstate.
  rewrite translate_log_bind, bind_bind;
  setoid_rewrite translate_ret; setoid_rewrite bind_ret_l; reflexivity.
Qed.

(** Focused heap primitives on the fair runner, directly from the handler
    equations (all [≅], so they pass under the relabelling [translate]). *)
Lemma interp_fair_write_present sch n
  (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE Bn) st h allocs ctx c :
  h a <> None ->
  interp_schedule_fair sch sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) st ((h,allocs),(ctx,c)) ~
  (log (inl (CSLHeap (upd h a v,allocs)));;
   interp_schedule_fair sch sh (S n) (ts @ i := K (Some tt))
     (Some i) st ((upd h a v,allocs),(ctx,c))).
Proof.
  intro Present.
  destruct (h a) as [w|] eqn:Ha; [|contradiction].
  rewrite (interp_schedule_fair_user_bind sch sh n ts i _ (inl1 (HWrite a v))
    (fun _ => K (Some tt)) st _ (source_raw_write_head a v K)).
  cbn [sh h_sum].
  rewrite (heap_handlerW_wr_some CSLHeap a h allocs (ctx,c) v w Ha).
  unfold log; rewrite !bind_vis, translate_vis; cbn [relabel_log].
  setoid_rewrite bind_ret_l; setoid_rewrite translate_ret;
    rewrite bind_vis; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_fair_alloc_first sch n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) st h allocs ctx c :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  interp_schedule_fair sch sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) st ((h,allocs),(ctx,c)) ~
  (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));;
   interp_schedule_fair sch sh (S n)
     (ts @ i := K (Some base)) (Some i) st (managed_alloc (h,allocs) base size,(ctx,c))).
Proof.
  intros Pos Base Free First.
  rewrite (interp_schedule_fair_user_bind sch sh n ts i _ (inl1 (HAlloc size))
    (fun base => K (Some base)) st _ (source_raw_alloc_head size K)).
  cbn [sh h_sum].
  rewrite (heap_handlerW_alloc_first_guards CSLHeap h allocs size base (ctx,c) Pos Base Free First).
  rewrite translate_guards, bind_guards, guards_sbisim.
  unfold log; rewrite !bind_vis, translate_vis; cbn [relabel_log].
  setoid_rewrite bind_ret_l; setoid_rewrite translate_ret;
    rewrite bind_vis; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_read_missing n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) m h allocs ctx c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intro Missing.
  pose proof (interp_heapW_rd_missing CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))
    a h allocs (ctx,c) (fun x : nat => (Ret x : ctree sE Bn nat)) Missing) as Hstate.
  rewrite bind_ret_r in Hstate.
  rewrite interp_rr_read; csl_lift_handler_result Hstate.
  rewrite translate_stuck_node, bind_stuck; reflexivity.
Qed.

Lemma interp_rr_write_missing n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE Bn) m h allocs ctx c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intro Missing.
  pose proof (interp_heapW_wr_missing CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))
    a v h allocs (ctx,c) (fun x : unit => (Ret x : ctree sE Bn unit)) Missing) as Hstate.
  rewrite bind_ret_r in Hstate.
  rewrite interp_rr_write; csl_lift_handler_result Hstate.
  rewrite translate_stuck_node, bind_stuck; reflexivity.
Qed.

Lemma interp_rr_cas_missing n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) m h allocs ctx c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intro Missing.
  pose proof (interp_heapW_cas_missing CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))
    a expected desired h allocs (ctx,c) (fun x : bool => (Ret x : ctree sE Bn bool)) Missing) as Hstate.
  rewrite bind_ret_r in Hstate.
  rewrite interp_rr_cas; csl_lift_handler_result Hstate.
  rewrite translate_stuck_node, bind_stuck; reflexivity.
Qed.


Lemma interp_nd_source_emit_log n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c)) ~
  (log (CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat));;
   interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))).
Proof.
  pose proof (interp_csl_emit (tag,value) memory ctx c
    (fun x : unit => (Ret x : ctree sE Bn unit))) as Hemit.
  rewrite bind_ret_r in Hemit.
  setoid_rewrite interp_state_ret in Hemit.
  rewrite interp_nd_source_emit; unfold semit.
  rewrite Hemit, bind_bind.
  setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_source_cas_value n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c :
  h a = Some current ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  (if Nat.eqb current expected then
    log (CSLHeap (upd h a desired,allocs));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),(ctx,c))).
Proof.
  intro Lookup; rewrite interp_nd_source_cas.
  destruct (Nat.eqb current expected) eqn:Cmp.
  - apply Nat.eqb_eq in Cmp; subst current.
    pose proof (interp_heapW_cas_success CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))) a expected desired h allocs (ctx,c)
      (fun x : bool => (Ret x : ctree sE Bn bool)) Lookup) as Hstate.
    rewrite bind_ret_r in Hstate; setoid_rewrite interp_state_ret in Hstate.
    csl_lift_handler_result Hstate.
    rewrite bind_bind; setoid_rewrite bind_ret_l; reflexivity.
  - apply Nat.eqb_neq in Cmp.
    pose proof (interp_heapW_cas_failure CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))) a expected desired current h allocs (ctx,c)
      (fun x : bool => (Ret x : ctree sE Bn bool)) Lookup Cmp) as Hstate.
    rewrite bind_ret_r, interp_state_ret in Hstate.
    csl_lift_handler_result Hstate.
    rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_source_alloc_first n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  (log (CSLHeap (managed_alloc (h,allocs) base size));;
   interp_schedule_nd sh (S n)
     (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))).
Proof.
  intros Pos Base Free First.
  pose proof (interp_heapW_alloc_first CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))) h allocs size base (ctx,c)
    (fun x : nat => (Ret x : ctree sE Bn nat)) Pos Base Free First) as Hstate.
  rewrite bind_ret_r in Hstate; setoid_rewrite interp_state_ret in Hstate.
  rewrite interp_nd_source_alloc; csl_lift_handler_result Hstate.
  rewrite bind_bind; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_source_read_missing n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c :
  h a = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  intro Missing.
  pose proof (interp_heapW_rd_missing CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))
    a h allocs (ctx,c) (fun x : nat => (Ret x : ctree sE Bn nat)) Missing) as Hstate.
  rewrite bind_ret_r in Hstate.
  rewrite interp_nd_source_read; csl_lift_handler_result Hstate.
  rewrite bind_stuck; reflexivity.
Qed.

Lemma interp_nd_source_write_missing n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE Bn) h allocs ctx c :
  h a = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  intro Missing.
  pose proof (interp_heapW_wr_missing CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))
    a v h allocs (ctx,c) (fun x : unit => (Ret x : ctree sE Bn unit)) Missing) as Hstate.
  rewrite bind_ret_r in Hstate.
  rewrite interp_nd_source_write; csl_lift_handler_result Hstate.
  rewrite bind_stuck; reflexivity.
Qed.

Lemma interp_nd_source_cas_missing n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c :
  h a = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  intro Missing.
  pose proof (interp_heapW_cas_missing CSLHeap (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))
    a expected desired h allocs (ctx,c) (fun x : bool => (Ret x : ctree sE Bn bool)) Missing) as Hstate.
  rewrite bind_ret_r in Hstate.
  rewrite interp_nd_source_cas; csl_lift_handler_result Hstate.
  rewrite bind_stuck; reflexivity.
Qed.


(** Whole-block free preserves focus and cursor. Nonzero success logs the
    released memory; free zero is silent, and invalid free is a fault. *)

Lemma source_free_raw_heap_free base (K : option unit -> thread sE Bn) :
  (denote_flow (CFree base) >>= K) ≅
    (heap_free (E:=CEff) base >>= fun _ => K (Some tt)).
Proof.
  etransitivity; [apply source_raw_free_head|].
  symmetry; apply raw_heap_free_head.
Qed.

Lemma interp_rr_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c :
  managed_free memory base = Some memory' ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) cursor (memory,(ctx,c)) ~
  match base with
  | 0 => interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
      (Some i) cursor (memory',(ctx,c))
  | S _ => log (inl (CSLHeap memory'));;
      interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
        (Some i) cursor (memory',(ctx,c))
  end.
Proof.
  intro Free.
  rewrite (interp_schedule_fair_equ rr_scheduler sh (S n) _ _ (Some i) cursor (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_rr_heap_free n ts i base (fun _ => K (Some tt)) cursor memory memory' ctx c Free).
Qed.

Lemma interp_rr_free_invalid n (ts : pool sE Bn (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c :
  managed_free memory base = None ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) cursor (memory,(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intro Invalid.
  rewrite (interp_schedule_fair_equ rr_scheduler sh (S n) _ _ (Some i) cursor (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_rr_heap_free_invalid n ts i base (fun _ => K (Some tt)) cursor memory ctx c Invalid).
Qed.

Lemma interp_nd_source_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c :
  managed_free memory base = Some memory' ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) (memory,(ctx,c)) ~
  match base with
  | 0 => interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
      (Some i) (memory',(ctx,c))
  | S _ => log (CSLHeap memory');;
      interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
        (Some i) (memory',(ctx,c))
  end.
Proof.
  intro Free.
  rewrite (interp_schedule_nd_equ sh (S n) _ _ (Some i) (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_nd_heap_free n ts i base (fun _ => K (Some tt)) memory memory' ctx c Free).
Qed.

Lemma interp_nd_source_free_invalid n (ts : pool sE Bn (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c :
  managed_free memory base = None ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) (memory,(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  intro Invalid.
  rewrite (interp_schedule_nd_equ sh (S n) _ _ (Some i) (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_nd_heap_free_invalid n ts i base (fun _ => K (Some tt)) memory ctx c Invalid).
Qed.



(** ** Source-instruction first-yield rules, in exact mode. *)

Local Open Scope list_scope.

Lemma exact_source_bind {A B} (p : CProg A) (next : A -> CProg B)
  (K : option B -> thread sE Bn) sigma logs target sigma' :
  segment_to sh csl_equ (denote_flow p >>= fun flow =>
    match flow with None => K None | Some x => denote_flow (next x) >>= K end)
    sigma logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CBind p next) >>= K) sigma logs target sigma'.
Proof.
  intro H; eapply segment_to_equ; [apply source_raw_bind|exact H].
Qed.

Lemma exact_source_ret {A} (x : A) (K : option A -> thread sE Bn)
  sigma logs target sigma' :
  segment_to sh csl_equ (K (Some x)) sigma logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CRet x) >>= K) sigma logs target sigma'.
Proof.
  intro H; eapply segment_to_equ; [apply source_raw_ret|exact H].
Qed.

Lemma exact_source_until {A} (body : CProg (option A))
  (K : option unit -> thread sE Bn) sigma logs target sigma' :
  segment_to sh csl_equ (denote_flow body >>= until_tail body K)
    sigma logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CUntilNone body) >>= K)
    sigma logs target sigma'.
Proof.
  intro H; eapply segment_to_equ; [apply source_raw_until|exact H].
Qed.

Lemma exact_source_read a v (K : option nat -> thread sE Bn)
  h allocs ctx c logs target sigma' :
  h a = Some v ->
  segment_to sh csl_equ (K (Some v)) ((h,allocs),(ctx,c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CRead a) >>= K) ((h,allocs),(ctx,c)) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr1 (inr1 (inl1 (HRead a)))) (fun v => K (Some v))).
  - apply source_raw_read_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr1 (inr1 (inl1 (HRead a)))) (fun v => K (Some v)))
      ((h,allocs),(ctx,c)) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list sh h_sum]; rewrite (heap_handlerW_rd_some CSLHeap a h allocs (ctx,c) v Hr); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_write a v (K : option unit -> thread sE Bn)
  h allocs ctx c logs target sigma' :
  h a <> None ->
  segment_to sh csl_equ (K (Some tt)) ((upd h a v,allocs),(ctx,c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CWrite a v) >>= K) ((h,allocs),(ctx,c))
    (CSLHeap (upd h a v,allocs) :: logs) target sigma'.
Proof.
  intros Hp (residual & Hseg & Htail).
  destruct (h a) as [w|] eqn:Hw; [|contradiction].
  exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr1 (inr1 (inl1 (HWrite a v)))) (fun _ => K (Some tt))).
  - apply source_raw_write_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr1 (inr1 (inl1 (HWrite a v)))) (fun _ => K (Some tt)))
      ((h,allocs),(ctx,c)) ([CSLHeap (upd h a v,allocs)] ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list sh h_sum]; rewrite (heap_handlerW_wr_some CSLHeap a h allocs (ctx,c) v w Hw); reflexivity.
  - reflexivity.
Qed.

(** The raw handler equation [csl_emit_handler_log] is the response
    certificate here; [interp_csl_emit] is an interpretation equation and
    cannot discharge this premise. *)
Lemma exact_source_emit tag block (K : option unit -> thread sE Bn)
  (memory : ManagedHeap) ctx c logs target sigma' :
  segment_to sh csl_equ (K (Some tt)) (memory,(ctx,S c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CEmit tag block) >>= K) (memory,(ctx,c))
    (CSLEmit (stamp (tag,block) c) :: logs) target sigma'.
Proof.
  intros (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr1 (inr1 (inr1 (inr1 (Log (tag,block)))))) (fun _ => K (Some tt))).
  - apply source_raw_emit_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr1 (inr1 (inr1 (inr1 (Log (tag,block)))))) (fun _ => K (Some tt)))
      (memory,(ctx,c)) ([CSLEmit (stamp (tag,block) c)] ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list sh h_sum]; rewrite (csl_emit_handler_log (tag,block) memory ctx c);
      reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_cas_success a expected desired
  (K : option bool -> thread sE Bn) h allocs ctx c logs target sigma' :
  h a = Some expected ->
  segment_to sh csl_equ (K (Some true)) ((upd h a desired,allocs),(ctx,c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)
    ((h,allocs),(ctx,c)) (CSLHeap (upd h a desired,allocs) :: logs) target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr1 (inr1 (inl1 (HCAS a expected desired)))) (fun b => K (Some b))).
  - apply source_raw_cas_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr1 (inr1 (inl1 (HCAS a expected desired)))) (fun b => K (Some b)))
      ((h,allocs),(ctx,c)) ([CSLHeap (upd h a desired,allocs)] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list sh h_sum];
      rewrite (heap_handlerW_cas_success CSLHeap a expected desired h allocs (ctx,c) Hr); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_cas_failure a expected desired current
  (K : option bool -> thread sE Bn) h allocs ctx c logs target sigma' :
  h a = Some current -> current <> expected ->
  segment_to sh csl_equ (K (Some false)) ((h,allocs),(ctx,c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)
    ((h,allocs),(ctx,c)) logs target sigma'.
Proof.
  intros Hr Hne (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr1 (inr1 (inl1 (HCAS a expected desired)))) (fun b => K (Some b))).
  - apply source_raw_cas_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr1 (inr1 (inl1 (HCAS a expected desired)))) (fun b => K (Some b)))
      ((h,allocs),(ctx,c)) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list sh h_sum];
      rewrite (heap_handlerW_cas_failure CSLHeap a expected desired current h allocs (ctx,c) Hr Hne);
      reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_free base (K : option unit -> thread sE Bn)
  (memory memory' : ManagedHeap) ctx c logs target sigma' :
  managed_free memory base = Some memory' ->
  segment_to sh csl_equ (K (Some tt)) (memory',(ctx,c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CFree base) >>= K) (memory,(ctx,c))
    ((match base with 0 => [] | S _ => [CSLHeap memory'] end) ++ logs) target sigma'.
Proof.
  intros Free (residual & Hseg & Htail).
  exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr1 (inr1 (inl1 (HFree base)))) (fun _ => K (Some tt))).
  - apply source_raw_free_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr1 (inr1 (inl1 (HFree base)))) (fun _ => K (Some tt)))
      (memory,(ctx,c)) ((match base with 0 => [] | S _ => [CSLHeap memory'] end) ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [sh h_sum]; rewrite (heap_handlerW_free CSLHeap base memory memory' (ctx,c) Free).
    destruct base; reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_yield (K : option unit -> thread sE Bn) sigma target :
  guard_equ (K (Some tt)) target ->
  segment_to sh csl_equ (denote_flow CYield >>= K) sigma [] target sigma.
Proof.
  intro Htail; exists (K (Some tt)); split; [|exact Htail].
  eapply segment_equ with (u := Vis (inl1 Yield) (fun _ => K (Some tt))).
  - apply source_raw_yield_head.
  - apply segment_yield.
  - reflexivity.
Qed.

(** Finite syntax normalization is used only for raw equ and leading guards.
    It never changes a scheduler focus or invokes pool sbisim congruence. *)
Ltac csl_raw_equ :=
  cbn beta iota zeta;
  first [reflexivity |
    lazymatch goal with
    | |- (denote_flow (CBind _ _) >>= _) ≅ _ =>
        etransitivity; [apply source_raw_bind|]; csl_raw_equ
    | |- (denote_flow (CRet _) >>= _) ≅ _ =>
        etransitivity; [apply source_raw_ret|]; csl_raw_equ
    | |- ((?t >>= ?k) >>= ?j) ≅ _ =>
        etransitivity; [apply bind_bind|]; csl_raw_equ
    | |- (Ret _ >>= _) ≅ _ =>
        etransitivity; [apply bind_ret_l|]; csl_raw_equ
    | |- _ ≅ (denote_flow (CBind _ _) >>= _) => symmetry; csl_raw_equ
    | |- _ ≅ (denote_flow (CRet _) >>= _) => symmetry; csl_raw_equ
    | |- _ ≅ ((_ >>= _) >>= _) => symmetry; csl_raw_equ
    | |- _ ≅ (Ret _ >>= _) => symmetry; csl_raw_equ
    | |- Guard _ ≅ Guard _ => apply guard_equ_node; csl_raw_equ
    end].

Local Close Scope list_scope.

(** ** Structural Ticl rules over source programs *)

Local Open Scope ticl_scope.
Local Typeclasses Transparent equ sbisim.


(** ** Observable emission and cooperative selection *)

Lemma an_csl_nd_emit {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat))) None) (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  (entails (SSig * unit) b <( φ AN ψ )> (interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
   (<( {log (CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {w} |=L φ )> /\
    entails (SSig * unit) b ψ (interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))) (Obs (Log (CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat))) tt))).
Proof.
  ticl_normalize.
  rewrite interp_nd_source_emit_log.
  apply (an_log_iff (b:=b)).
Qed.

Lemma au_csl_nd_emit {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat))) None) (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  (entails (SSig * unit) b <( φ AU ψ )> (interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
   (entails (SSig * unit) b ψ (log (CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))) (w) \/
   (<( {log (CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {w} |=L φ )> /\
    entails (SSig * unit) b <( φ AU ψ )> (interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))) (Obs (Log (CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat))) tt)))).
Proof.
  ticl_normalize.
  rewrite interp_nd_source_emit_log.
  apply (au_log_iff (b:=b)).
Qed.

Lemma ag_csl_nd_emit n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat))) None) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))}, {w} |=L AG φ )> <->
   (<( {log (CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {w} |=L φ )> /\
    <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {Obs (Log (CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |=L AG φ )>)).
Proof.
  ticl_normalize.
  rewrite interp_nd_source_emit_log.
  apply ag_log_iff.
Qed.

Lemma an_csl_rr_emit {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) m memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat) + nat)) None) (ψ : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  (entails (SSig * unit) b <( φ AN ψ )> (interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,(ctx,c))) (w) <->
   (<( {log (inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {w} |=L φ )> /\
    entails (SSig * unit) b ψ (interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))) (Obs (Log (inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat)) tt))).
Proof.
  ticl_normalize.
  rewrite interp_rr_emit_log.
  apply (an_log_iff (b:=b)).
Qed.

Lemma au_csl_rr_emit {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) m memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat) + nat)) None) (ψ : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  (entails (SSig * unit) b <( φ AU ψ )> (interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,(ctx,c))) (w) <->
   (entails (SSig * unit) b ψ (log (inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))) (w) \/
   (<( {log (inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {w} |=L φ )> /\
    entails (SSig * unit) b <( φ AU ψ )> (interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))) (Obs (Log (inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat)) tt)))).
Proof.
  ticl_normalize.
  rewrite interp_rr_emit_log.
  apply (au_log_iff (b:=b)).
Qed.

Lemma ag_csl_rr_emit n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) m memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat) + nat)) None) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |=L AG φ )> <->
   (<( {log (inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {w} |=L φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {Obs (Log (inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat)) tt} |=L AG φ )>)).
Proof.
  ticl_normalize.
  rewrite interp_rr_emit_log.
  apply ag_log_iff.
Qed.

Lemma an_csl_nd_yield {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE Bn) memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat))) None) (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  (entails (SSig * unit) b <( φ AN ψ )> (interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))}, {w} |=L φ )> /\
    forall j : Fin.t (S n),
      entails (SSig * unit) b ψ (interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c))) (w))).
Proof.
  ticl_normalize.
  rewrite interp_nd_source_yield.
  apply (an_csl_nd_select n (ts @ i := K (Some tt)) memory ctx c w (b:=b)).
Qed.

Lemma au_csl_nd_yield {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE Bn) memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat))) None) (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  (entails (SSig * unit) b <( φ AU ψ )> (interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
   (entails (SSig * unit) b ψ (brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))) (w) \/
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))}, {w} |=L φ )> /\
    forall j : Fin.t (S n),
      entails (SSig * unit) b <( φ AU ψ )> (interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c))) (w)))).
Proof.
  ticl_normalize.
  rewrite interp_nd_source_yield.
  apply (au_csl_nd_select n (ts @ i := K (Some tt)) memory ctx c w (b:=b)).
Qed.

Lemma ag_csl_nd_yield n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE Bn) memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat))) None) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,(ctx,c))}, {w} |=L AG φ )> <->
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))}, {w} |=L φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c))}, {w} |=L AG φ )>)).
Proof.
  ticl_normalize.
  rewrite interp_nd_source_yield.
  apply ag_csl_nd_select.
Qed.

(** A round-robin yield logs the scheduler's selected slot before the
    picked slot runs: the shapes mirror [an_csl_rr_select], [au_csl_rr_select], and [ag_csl_rr_select]. *)

Lemma an_csl_rr_yield {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE Bn) m memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat) + nat)) None) (ψ : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  (entails (SSig * unit) b <( φ AN ψ )> (interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,(ctx,c))) (w) <->
   (<( {Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ => interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, {w} |=L φ )> /\
    entails (SSig * unit) b ψ (interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n m)))) tt))).
Proof.
  ticl_normalize.
  rewrite interp_rr_yield.
  apply (an_csl_rr_select n (ts @ i := K (Some tt)) m memory ctx c w (b:=b)).
Qed.

Lemma au_csl_rr_yield {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE Bn) m memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat) + nat)) None) (ψ : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  (entails (SSig * unit) b <( φ AU ψ )> (interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,(ctx,c))) (w) <->
   (entails (SSig * unit) b ψ (Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ => interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c)))) (w) \/
   (<( {Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ => interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, {w} |=L φ )> /\
    entails (SSig * unit) b <( φ AU ψ )> (interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n m)))) tt)))).
Proof.
  ticl_normalize.
  rewrite interp_rr_yield.
  apply (au_csl_rr_select n (ts @ i := K (Some tt)) m memory ctx c w (b:=b)).
Qed.

Lemma ag_csl_rr_yield n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE Bn) m memory ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat) + nat)) None) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |=L AG φ )> <->
   (<( {Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ => interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, {w} |=L φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {Obs (Log (inr (slot_index (rr_pick n m)))) tt} |=L AG φ )>)).
Proof.
  ticl_normalize.
  rewrite interp_rr_yield.
  apply ag_csl_rr_select.
Qed.

(** ** Finite heaps supply their constructive first-fit witness *)

Lemma ticl_csl_nd_alloc_finite {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  heap_finite h -> Nat.lt 0 size -> not_done w ->
  (entails (SSig * unit) b p (interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     entails (SSig * unit) b p (log (CSLHeap (managed_alloc (h,allocs) base size));;
       interp_schedule_nd sh (S n)
         (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) w).
Proof.
  intros Finite Pos ND; split.
  - intros Hsource base Base Free First.
    ticl_normalize in Hsource; ticl_normalize.
    rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c Pos Base Free First) in Hsource.
    exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size Finite Pos) as (base & Base & Free & First).
    ticl_normalize.
    rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c Pos Base Free First).
    apply Hall; assumption.
Qed.

Lemma ticl_csl_rr_alloc_finite {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) m h allocs ctx c w
  (p : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  heap_finite h -> Nat.lt 0 size -> not_done w ->
  (entails (SSig * unit) b p (interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))) (w) <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     entails (SSig * unit) b p (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));;
       interp_schedule_rr sh (S n)
         (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))) w).
Proof.
  intros Finite Pos ND; split.
  - intros Hsource base Base Free First.
    ticl_normalize in Hsource; ticl_normalize.
    rewrite (interp_rr_alloc_first n ts i size base K m h allocs ctx c Pos Base Free First) in Hsource.
    exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size Finite Pos) as (base & Base & Free & First).
    ticl_normalize.
    rewrite (interp_rr_alloc_first n ts i size base K m h allocs ctx c Pos Base Free First).
    apply Hall; assumption.
Qed.


Lemma source_raw_exp_plus {X} (ea eb : CExp) (K : nat -> ctree CEff Bn X) :
  (denote_exp (CPlus ea eb) >>= K) ≅
  (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat).
Proof.
  cbn [denote_exp]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro x; rewrite bind_bind.
  apply equ_clo_bind_eq; intro y; apply bind_ret_l.
Qed.

Lemma source_raw_exp_minus {X} (ea eb : CExp) (K : nat -> ctree CEff Bn X) :
  (denote_exp (CMinus ea eb) >>= K) ≅
  (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat).
Proof.
  cbn [denote_exp]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro x; rewrite bind_bind.
  apply equ_clo_bind_eq; intro y; apply bind_ret_l.
Qed.

Lemma source_raw_exp_mult {X} (ea eb : CExp) (K : nat -> ctree CEff Bn X) :
  (denote_exp (CMult ea eb) >>= K) ≅
  (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat).
Proof.
  cbn [denote_exp]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro x; rewrite bind_bind.
  apply equ_clo_bind_eq; intro y; apply bind_ret_l.
Qed.


Lemma interp_nd_source_eval n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) (sigma : SSig) :
  (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) sigma) ≅ (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) sigma).
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_eval].
Qed.

Lemma interp_nd_source_if {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) (sigma : SSig) :
  (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) sigma) ≅ (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) sigma).
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_if].
Qed.

Lemma interp_nd_source_exp_plus n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) (sigma : SSig) :
  (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) sigma) ≅ (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) sigma).
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_exp_plus].
Qed.

Lemma interp_nd_source_exp_minus n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) (sigma : SSig) :
  (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) sigma) ≅ (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) sigma).
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_exp_minus].
Qed.

Lemma interp_nd_source_exp_mult n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) (sigma : SSig) :
  (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) sigma) ≅ (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) sigma).
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_exp_mult].
Qed.

Lemma interp_nd_source_alloc_zero n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c :
  (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) ~
  (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  rewrite interp_nd_source_alloc.
  unfold heap_alloc.
  rewrite interp_state_trigger_bind, subevent_left; cbn [sh h_sum].
  rewrite (heap_handlerW_alloc_zero CSLHeap h allocs (ctx,c)), bind_stuck; reflexivity.
Qed.

Lemma interp_nd_source_alloc_no_space n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c :
  Nat.lt 0 size -> (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) ~
  (CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  intros Pos Full.
  rewrite interp_nd_source_alloc.
  unfold heap_alloc.
  rewrite interp_state_trigger_bind, subevent_left; cbn [sh h_sum].
  rewrite (heap_handlerW_alloc_no_space CSLHeap h allocs size (ctx,c) Pos Full), bind_spin; reflexivity.
Qed.

Lemma interp_nd_source_guard n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (t : thread sE Bn) (sigma : SSig) :
  (interp_schedule_nd sh (S n) (ts @ i := (Guard t)) (Some i) sigma) ~ (interp_schedule_nd sh (S n) (ts @ i := (t)) (Some i) sigma).
Proof.
  erewrite (interp_schedule_nd_guard sh)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_source_eval n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor (sigma : SSig) :
  (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor sigma) ≅ (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor sigma).
Proof.
  apply (interp_schedule_fair_equ rr_scheduler sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_eval].
Qed.

Lemma interp_rr_source_if {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor (sigma : SSig) :
  (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor sigma) ≅ (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor sigma).
Proof.
  apply (interp_schedule_fair_equ rr_scheduler sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_if].
Qed.

Lemma interp_rr_source_exp_plus n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor (sigma : SSig) :
  (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor sigma) ≅ (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor sigma).
Proof.
  apply (interp_schedule_fair_equ rr_scheduler sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_exp_plus].
Qed.

Lemma interp_rr_source_exp_minus n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor (sigma : SSig) :
  (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor sigma) ≅ (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor sigma).
Proof.
  apply (interp_schedule_fair_equ rr_scheduler sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_exp_minus].
Qed.

Lemma interp_rr_source_exp_mult n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor (sigma : SSig) :
  (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor sigma) ≅ (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor sigma).
Proof.
  apply (interp_schedule_fair_equ rr_scheduler sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_exp_mult].
Qed.

Lemma interp_rr_alloc_zero n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c :
  (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) ~
  (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  rewrite interp_rr_alloc.
  unfold heap_alloc.
  rewrite translate_interp_state_trigger_bind, subevent_left; cbn [sh h_sum].
  rewrite (heap_handlerW_alloc_zero CSLHeap h allocs (ctx,c)), translate_stuck_node, bind_stuck; reflexivity.
Qed.

Lemma interp_rr_alloc_no_space n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c :
  Nat.lt 0 size -> (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) ~
  (CTree.spin : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intros Pos Full.
  rewrite interp_rr_alloc.
  unfold heap_alloc.
  rewrite translate_interp_state_trigger_bind, subevent_left; cbn [sh h_sum].
  rewrite (heap_handlerW_alloc_no_space CSLHeap h allocs size (ctx,c) Pos Full), translate_spin, bind_spin; reflexivity.
Qed.

Lemma interp_rr_source_guard n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (t : thread sE Bn) cursor (sigma : SSig) :
  (interp_schedule_rr sh (S n) (ts @ i := (Guard t)) (Some i) cursor sigma) ~ (interp_schedule_rr sh (S n) (ts @ i := (t)) (Some i) cursor sigma).
Proof.
  erewrite (interp_schedule_fair_guard rr_scheduler sh)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

(** The one-unroll equations preserve expression evaluation and the actual
    source continuation, including halt and guarded loop re-entry. *)
Lemma source_raw_while_unfold (test : CExp) (body : CProg unit)
    (K : option unit -> thread sE Bn) :
  (denote_flow (CWhile test body) >>= K) ≅
  (denote_exp test >>= fun value =>
    if CoCSLSyntax.is_true value then
      denote_flow body >>= fun flow =>
        match flow with
        | None => K None
        | Some _ => Guard (denote_flow (CWhile test body) >>= K)
        end
    else K (Some tt)).
Proof.
  rewrite source_raw_while.
  transitivity ((cwhile_iteration test body tt >>= fun lr =>
    match lr with
    | inl j => Guard (CTree.iter (cwhile_iteration test body) j)
    | inr result => Ret result
    end) >>= K).
  - apply equ_clo_bind with (S := eq).
    + apply unfold_iter.
    + intros r r' <-; reflexivity.
  - etransitivity; [apply bind_bind|].
    unfold cwhile_iteration at 1.
    etransitivity; [apply bind_bind|].
    apply equ_clo_bind_eq; intro value.
    destruct (CoCSLSyntax.is_true value).
    + etransitivity; [apply bind_bind|].
      apply equ_clo_bind_eq; intros [result|]; cbn.
      * etransitivity; [apply bind_ret_l|].
        apply bind_guard.
      * etransitivity; [apply bind_ret_l|]. apply bind_ret_l.
    + etransitivity; [apply bind_ret_l|]. apply bind_ret_l.
Qed.

Lemma interp_nd_source_while_unfold n
    (ts : pool sE Bn (S n)) (i : Fin.t (S n))
    (test : CExp) (body : CProg unit)
    (K : option unit -> thread sE Bn) sigma :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) sigma ≅
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_exp test >>= fun value =>
      if CoCSLSyntax.is_true value then
        denote_flow body >>= fun flow =>
          match flow with
          | None => K None
          | Some _ => Guard (denote_flow (CWhile test body) >>= K)
          end
      else K (Some tt))) (Some i) sigma.
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_while_unfold].
Qed.

Lemma interp_rr_while_unfold n
    (ts : pool sE Bn (S n)) (i : Fin.t (S n))
    (test : CExp) (body : CProg unit)
    (K : option unit -> thread sE Bn) cursor sigma :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWhile test body) >>= K))
    (Some i) cursor sigma ≅
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_exp test >>= fun value =>
      if CoCSLSyntax.is_true value then
        denote_flow body >>= fun flow =>
          match flow with
          | None => K None
          | Some _ => Guard (denote_flow (CWhile test body) >>= K)
          end
      else K (Some tt))) (Some i) cursor sigma.
Proof.
  apply interp_schedule_fair_equ, replace_pool_equ;
    [apply pool_equ_refl|apply source_raw_while_unfold].
Qed.

(** Complete source-loop rules cut the actual scheduled execution. The
    proof-local dependent contexts admit changed pools, focus and RR cursors.
    Global rules require a productive next segment before any cutpoint. *)

Lemma au_csl_nd_until_none_wf {A G : Type} {b : bool}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (ltG : relation G) (phi : ticllW (CSLObs (nat * nat)))
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    quntil Q_A (entails (SSig * unit) false phi)
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') sigma')
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) b (Cu Q_A phi psi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) sigma) w.
Proof.
  intros Wf Hbody g n ts i sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * SSig))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
            (ts @ i := (denote_flow body >>= until_tail body K))
            (Some i) sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, sigma))) => Inv g n ts i sigma w0 end).
  set (Rv := fun (a b : (G * C) * WorldW (CSLObs (nat * nat))) =>
    ltG (fst (fst a)) (fst (fst b))).
  assert (WfR : well_founded Rv).
  { intros [[g0 context] w0].
    revert context w0.
    induction g0 as [g0 IH] using (well_founded_induction Wf).
    intros context w0; constructor.
    intros [[g' context'] w'] Hlt.
    exact (IH g' Hlt context' w'). }
  change (entails (SSig * unit) b (Cu Q_A phi psi)
    (T (g, existT _ n (ts, (i, sigma)))) w).
  eapply (au_family_wf T U J Rv phi psi).
  - intros [g0 [n0 [ts0 [i0 sigma0]]]]; cbn [T U].
    rewrite interp_nd_source_until_none; reflexivity.
  - exact WfR.
  - intros [g0 [n0 [ts0 [i0 sigma0]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply auc_mono_r; [|exact Hsegment].
    intros t z [Hpsi | (g' & n' & ts' & i' & sigma' & Hinv' & Hlt & Htree)].
    + left; exact Hpsi.
    + right; exists (g', existT _ n' (ts', (i', sigma'))).
      split; [exact Hinv'|].
      split; [exact Hlt|exact Htree].
  - exact Hinv.
Qed.

Lemma eu_csl_nd_until_none_wf {A G : Type} {b : bool}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (ltG : relation G) (phi : ticllW (CSLObs (nat * nat)))
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    quntil Q_E (entails (SSig * unit) false phi)
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') sigma')
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) b (Cu Q_E phi psi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) sigma) w.
Proof.
  intros Wf Hbody g n ts i sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * SSig))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
            (ts @ i := (denote_flow body >>= until_tail body K))
            (Some i) sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, sigma))) => Inv g n ts i sigma w0 end).
  set (Rv := fun (a b : (G * C) * WorldW (CSLObs (nat * nat))) =>
    ltG (fst (fst a)) (fst (fst b))).
  assert (WfR : well_founded Rv).
  { intros [[g0 context] w0].
    revert context w0.
    induction g0 as [g0 IH] using (well_founded_induction Wf).
    intros context w0; constructor.
    intros [[g' context'] w'] Hlt.
    exact (IH g' Hlt context' w'). }
  change (entails (SSig * unit) b (Cu Q_E phi psi)
    (T (g, existT _ n (ts, (i, sigma)))) w).
  eapply (eu_family_wf T U J Rv phi psi).
  - intros [g0 [n0 [ts0 [i0 sigma0]]]]; cbn [T U].
    rewrite interp_nd_source_until_none; reflexivity.
  - exact WfR.
  - intros [g0 [n0 [ts0 [i0 sigma0]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply euc_mono_r; [|exact Hsegment].
    intros t z [Hpsi | (g' & n' & ts' & i' & sigma' & Hinv' & Hlt & Htree)].
    + left; exact Hpsi.
    + right; exists (g', existT _ n' (ts', (i', sigma'))).
      split; [exact Hinv'|].
      split; [exact Hlt|exact Htree].
  - exact Hinv.
Qed.

Lemma af_csl_nd_until_none_wf {A G : Type} {b : bool}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (ltG : relation G)
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    quntil Q_A (entails (SSig * unit) false (CNow (fun _ => True)))
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') sigma')
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) sigma) w.
Proof.
  exact (au_csl_nd_until_none_wf
    body K Inv ltG (CNow (fun _ => True)) psi).
Qed.

Lemma ef_csl_nd_until_none_wf {A G : Type} {b : bool}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (ltG : relation G)
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    quntil Q_E (entails (SSig * unit) false (CNow (fun _ => True)))
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') sigma')
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) sigma) w.
Proof.
  exact (eu_csl_nd_until_none_wf
    body K Inv ltG (CNow (fun _ => True)) psi).
Qed.

Lemma ag_csl_nd_until_none {A G : Type}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (phi : ticllW (CSLObs (nat * nat))) :
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    qnext Q_A (entails (SSig * unit) false phi)
      (quntil Q_A (entails (SSig * unit) false phi)
      (fun t z => (exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') sigma') \/
        entails (SSig * unit) false (Cg Q_A phi) t z))
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) false (Cg Q_A phi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) sigma) w.
Proof.
  intros Hbody g n ts i sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * SSig))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
            (ts @ i := (denote_flow body >>= until_tail body K))
            (Some i) sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, sigma))) => Inv g n ts i sigma w0 end).
  change (entails (SSig * unit) false (Cg Q_A phi)
    (T (g, existT _ n (ts, (i, sigma)))) w).
  eapply (ag_family T U J phi).
  - intros [g0 [n0 [ts0 [i0 sigma0]]]]; cbn [T U].
    rewrite interp_nd_source_until_none; reflexivity.
  - intros [g0 [n0 [ts0 [i0 sigma0]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply anc_mono_r; [|exact Hsegment].
    intros t z Hfinite.
    eapply auc_mono_r; [|exact Hfinite].
    intros t' z' [(g' & n' & ts' & i' & sigma' & Hinv' & Htree) | Htail].
    + left; exists (g', existT _ n' (ts', (i', sigma')));
        split; [exact Hinv'|exact Htree].
    + right; exact Htail.
  - exact Hinv.
Qed.

Lemma eg_csl_nd_until_none {A G : Type}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (phi : ticllW (CSLObs (nat * nat))) :
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    qnext Q_E (entails (SSig * unit) false phi)
      (quntil Q_E (entails (SSig * unit) false phi)
      (fun t z => (exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') sigma') \/
        entails (SSig * unit) false (Cg Q_E phi) t z))
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) false (Cg Q_E phi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) sigma) w.
Proof.
  intros Hbody g n ts i sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * SSig))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
            (ts @ i := (denote_flow body >>= until_tail body K))
            (Some i) sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, sigma))) => Inv g n ts i sigma w0 end).
  change (entails (SSig * unit) false (Cg Q_E phi)
    (T (g, existT _ n (ts, (i, sigma)))) w).
  eapply (eg_family T U J phi).
  - intros [g0 [n0 [ts0 [i0 sigma0]]]]; cbn [T U].
    rewrite interp_nd_source_until_none; reflexivity.
  - intros [g0 [n0 [ts0 [i0 sigma0]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply enc_mono_r; [|exact Hsegment].
    intros t z Hfinite.
    eapply euc_mono_r; [|exact Hfinite].
    intros t' z' [(g' & n' & ts' & i' & sigma' & Hinv' & Htree) | Htail].
    + left; exists (g', existT _ n' (ts', (i', sigma')));
        split; [exact Hinv'|exact Htree].
    + right; exact Htail.
  - exact Hinv.
Qed.

Lemma au_csl_nd_while_wf {G : Type} {b : bool}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (ltG : relation G) (phi : ticllW (CSLObs (nat * nat)))
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    quntil Q_A (entails (SSig * unit) false phi)
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') sigma')
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) b (Cu Q_A phi psi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) sigma) w.
Proof.
  intros Wf Hbody g n ts i sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * SSig))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
            (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
            (Some i) sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, sigma))) => Inv g n ts i sigma w0 end).
  set (Rv := fun (a b : (G * C) * WorldW (CSLObs (nat * nat))) =>
    ltG (fst (fst a)) (fst (fst b))).
  assert (WfR : well_founded Rv).
  { intros [[g0 context] w0].
    revert context w0.
    induction g0 as [g0 IH] using (well_founded_induction Wf).
    intros context w0; constructor.
    intros [[g' context'] w'] Hlt.
    exact (IH g' Hlt context' w'). }
  change (entails (SSig * unit) b (Cu Q_A phi psi)
    (T (g, existT _ n (ts, (i, sigma)))) w).
  eapply (au_family_wf T U J Rv phi psi).
  - intros [g0 [n0 [ts0 [i0 sigma0]]]]; cbn [T U].
    rewrite interp_nd_source_while_unfold; reflexivity.
  - exact WfR.
  - intros [g0 [n0 [ts0 [i0 sigma0]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply auc_mono_r; [|exact Hsegment].
    intros t z [Hpsi | (g' & n' & ts' & i' & sigma' & Hinv' & Hlt & Htree)].
    + left; exact Hpsi.
    + right; exists (g', existT _ n' (ts', (i', sigma'))).
      split; [exact Hinv'|].
      split; [exact Hlt|exact Htree].
  - exact Hinv.
Qed.

Lemma eu_csl_nd_while_wf {G : Type} {b : bool}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (ltG : relation G) (phi : ticllW (CSLObs (nat * nat)))
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    quntil Q_E (entails (SSig * unit) false phi)
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') sigma')
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) b (Cu Q_E phi psi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) sigma) w.
Proof.
  intros Wf Hbody g n ts i sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * SSig))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
            (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
            (Some i) sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, sigma))) => Inv g n ts i sigma w0 end).
  set (Rv := fun (a b : (G * C) * WorldW (CSLObs (nat * nat))) =>
    ltG (fst (fst a)) (fst (fst b))).
  assert (WfR : well_founded Rv).
  { intros [[g0 context] w0].
    revert context w0.
    induction g0 as [g0 IH] using (well_founded_induction Wf).
    intros context w0; constructor.
    intros [[g' context'] w'] Hlt.
    exact (IH g' Hlt context' w'). }
  change (entails (SSig * unit) b (Cu Q_E phi psi)
    (T (g, existT _ n (ts, (i, sigma)))) w).
  eapply (eu_family_wf T U J Rv phi psi).
  - intros [g0 [n0 [ts0 [i0 sigma0]]]]; cbn [T U].
    rewrite interp_nd_source_while_unfold; reflexivity.
  - exact WfR.
  - intros [g0 [n0 [ts0 [i0 sigma0]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply euc_mono_r; [|exact Hsegment].
    intros t z [Hpsi | (g' & n' & ts' & i' & sigma' & Hinv' & Hlt & Htree)].
    + left; exact Hpsi.
    + right; exists (g', existT _ n' (ts', (i', sigma'))).
      split; [exact Hinv'|].
      split; [exact Hlt|exact Htree].
  - exact Hinv.
Qed.

Lemma af_csl_nd_while_wf {G : Type} {b : bool}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (ltG : relation G)
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    quntil Q_A (entails (SSig * unit) false (CNow (fun _ => True)))
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') sigma')
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) sigma) w.
Proof.
  exact (au_csl_nd_while_wf
    test body K Inv ltG (CNow (fun _ => True)) psi).
Qed.

Lemma ef_csl_nd_while_wf {G : Type} {b : bool}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (ltG : relation G)
    (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    quntil Q_E (entails (SSig * unit) false (CNow (fun _ => True)))
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') sigma')
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) sigma) w.
Proof.
  exact (eu_csl_nd_while_wf
    test body K Inv ltG (CNow (fun _ => True)) psi).
Qed.

Lemma ag_csl_nd_while {G : Type}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (phi : ticllW (CSLObs (nat * nat))) :
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    qnext Q_A (entails (SSig * unit) false phi)
      (quntil Q_A (entails (SSig * unit) false phi)
      (fun t z => (exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') sigma') \/
        entails (SSig * unit) false (Cg Q_A phi) t z))
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) false (Cg Q_A phi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) sigma) w.
Proof.
  intros Hbody g n ts i sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * SSig))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
            (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
            (Some i) sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, sigma))) => Inv g n ts i sigma w0 end).
  change (entails (SSig * unit) false (Cg Q_A phi)
    (T (g, existT _ n (ts, (i, sigma)))) w).
  eapply (ag_family T U J phi).
  - intros [g0 [n0 [ts0 [i0 sigma0]]]]; cbn [T U].
    rewrite interp_nd_source_while_unfold; reflexivity.
  - intros [g0 [n0 [ts0 [i0 sigma0]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply anc_mono_r; [|exact Hsegment].
    intros t z Hfinite.
    eapply auc_mono_r; [|exact Hfinite].
    intros t' z' [(g' & n' & ts' & i' & sigma' & Hinv' & Htree) | Htail].
    + left; exists (g', existT _ n' (ts', (i', sigma')));
        split; [exact Hinv'|exact Htree].
    + right; exact Htail.
  - exact Hinv.
Qed.

Lemma eg_csl_nd_while {G : Type}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      SSig -> WorldW (CSLObs (nat * nat)) -> Prop)
    (phi : ticllW (CSLObs (nat * nat))) :
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    qnext Q_E (entails (SSig * unit) false phi)
      (quntil Q_E (entails (SSig * unit) false phi)
      (fun t z => (exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (sigma' : SSig),
          Inv g' n' ts' i' sigma' z /\ t ~ interp_schedule_nd sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') sigma') \/
        entails (SSig * unit) false (Cg Q_E phi) t z))
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      sigma w, Inv g n ts i sigma w ->
    entails (SSig * unit) false (Cg Q_E phi)
      (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) sigma) w.
Proof.
  intros Hbody g n ts i sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * SSig))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, sigma))) =>
      interp_schedule_nd sh (S n)
            (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
            (Some i) sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, sigma))) => Inv g n ts i sigma w0 end).
  change (entails (SSig * unit) false (Cg Q_E phi)
    (T (g, existT _ n (ts, (i, sigma)))) w).
  eapply (eg_family T U J phi).
  - intros [g0 [n0 [ts0 [i0 sigma0]]]]; cbn [T U].
    rewrite interp_nd_source_while_unfold; reflexivity.
  - intros [g0 [n0 [ts0 [i0 sigma0]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply enc_mono_r; [|exact Hsegment].
    intros t z Hfinite.
    eapply euc_mono_r; [|exact Hfinite].
    intros t' z' [(g' & n' & ts' & i' & sigma' & Hinv' & Htree) | Htail].
    + left; exists (g', existT _ n' (ts', (i', sigma')));
        split; [exact Hinv'|exact Htree].
    + right; exact Htail.
  - exact Hinv.
Qed.

Lemma au_csl_rr_until_none_wf {A G : Type} {b : bool}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (ltG : relation G) (phi : ticllW (CSLObs (nat * nat) + nat))
    (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    quntil Q_A (entails (SSig * unit) false phi)
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') cursor' sigma')
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) b (Cu Q_A phi psi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  intros Wf Hbody g n ts i cursor sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * (nat * SSig)))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) cursor sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
            (ts @ i := (denote_flow body >>= until_tail body K))
            (Some i) cursor sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) => Inv g n ts i cursor sigma w0 end).
  set (Rv := fun (a b : (G * C) * WorldW (CSLObs (nat * nat) + nat)) =>
    ltG (fst (fst a)) (fst (fst b))).
  assert (WfR : well_founded Rv).
  { intros [[g0 context] w0].
    revert context w0.
    induction g0 as [g0 IH] using (well_founded_induction Wf).
    intros context w0; constructor.
    intros [[g' context'] w'] Hlt.
    exact (IH g' Hlt context' w'). }
  change (entails (SSig * unit) b (Cu Q_A phi psi)
    (T (g, existT _ n (ts, (i, (cursor, sigma))))) w).
  eapply (au_family_wf T U J Rv phi psi).
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]]; cbn [T U].
    rewrite interp_rr_until_none; reflexivity.
  - exact WfR.
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 cursor0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply auc_mono_r; [|exact Hsegment].
    intros t z [Hpsi | (g' & n' & ts' & i' & cursor' & sigma' & Hinv' & Hlt & Htree)].
    + left; exact Hpsi.
    + right; exists (g', existT _ n' (ts', (i', (cursor', sigma')))).
      split; [exact Hinv'|].
      split; [exact Hlt|exact Htree].
  - exact Hinv.
Qed.

Lemma eu_csl_rr_until_none_wf {A G : Type} {b : bool}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (ltG : relation G) (phi : ticllW (CSLObs (nat * nat) + nat))
    (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    quntil Q_E (entails (SSig * unit) false phi)
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') cursor' sigma')
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) b (Cu Q_E phi psi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  intros Wf Hbody g n ts i cursor sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * (nat * SSig)))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) cursor sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
            (ts @ i := (denote_flow body >>= until_tail body K))
            (Some i) cursor sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) => Inv g n ts i cursor sigma w0 end).
  set (Rv := fun (a b : (G * C) * WorldW (CSLObs (nat * nat) + nat)) =>
    ltG (fst (fst a)) (fst (fst b))).
  assert (WfR : well_founded Rv).
  { intros [[g0 context] w0].
    revert context w0.
    induction g0 as [g0 IH] using (well_founded_induction Wf).
    intros context w0; constructor.
    intros [[g' context'] w'] Hlt.
    exact (IH g' Hlt context' w'). }
  change (entails (SSig * unit) b (Cu Q_E phi psi)
    (T (g, existT _ n (ts, (i, (cursor, sigma))))) w).
  eapply (eu_family_wf T U J Rv phi psi).
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]]; cbn [T U].
    rewrite interp_rr_until_none; reflexivity.
  - exact WfR.
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 cursor0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply euc_mono_r; [|exact Hsegment].
    intros t z [Hpsi | (g' & n' & ts' & i' & cursor' & sigma' & Hinv' & Hlt & Htree)].
    + left; exact Hpsi.
    + right; exists (g', existT _ n' (ts', (i', (cursor', sigma')))).
      split; [exact Hinv'|].
      split; [exact Hlt|exact Htree].
  - exact Hinv.
Qed.

Lemma af_csl_rr_until_none_wf {A G : Type} {b : bool}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (ltG : relation G)
    (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    quntil Q_A (entails (SSig * unit) false (CNow (fun _ => True)))
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') cursor' sigma')
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  exact (au_csl_rr_until_none_wf
    body K Inv ltG (CNow (fun _ => True)) psi).
Qed.

Lemma ef_csl_rr_until_none_wf {A G : Type} {b : bool}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (ltG : relation G)
    (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    quntil Q_E (entails (SSig * unit) false (CNow (fun _ => True)))
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') cursor' sigma')
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  exact (eu_csl_rr_until_none_wf
    body K Inv ltG (CNow (fun _ => True)) psi).
Qed.

Lemma ag_csl_rr_until_none {A G : Type}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (phi : ticllW (CSLObs (nat * nat) + nat)) :
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    qnext Q_A (entails (SSig * unit) false phi)
      (quntil Q_A (entails (SSig * unit) false phi)
      (fun t z => (exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') cursor' sigma') \/
        entails (SSig * unit) false (Cg Q_A phi) t z))
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) false (Cg Q_A phi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  intros Hbody g n ts i cursor sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * (nat * SSig)))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) cursor sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
            (ts @ i := (denote_flow body >>= until_tail body K))
            (Some i) cursor sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) => Inv g n ts i cursor sigma w0 end).
  change (entails (SSig * unit) false (Cg Q_A phi)
    (T (g, existT _ n (ts, (i, (cursor, sigma))))) w).
  eapply (ag_family T U J phi).
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]]; cbn [T U].
    rewrite interp_rr_until_none; reflexivity.
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 cursor0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply anc_mono_r; [|exact Hsegment].
    intros t z Hfinite.
    eapply auc_mono_r; [|exact Hfinite].
    intros t' z' [(g' & n' & ts' & i' & cursor' & sigma' & Hinv' & Htree) | Htail].
    + left; exists (g', existT _ n' (ts', (i', (cursor', sigma'))));
        split; [exact Hinv'|exact Htree].
    + right; exact Htail.
  - exact Hinv.
Qed.

Lemma eg_csl_rr_until_none {A G : Type}
    (body : CProg (option A)) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (phi : ticllW (CSLObs (nat * nat) + nat)) :
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    qnext Q_E (entails (SSig * unit) false phi)
      (quntil Q_E (entails (SSig * unit) false phi)
      (fun t z => (exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CUntilNone body) >>= K))
              (Some i') cursor' sigma') \/
        entails (SSig * unit) false (Cg Q_E phi) t z))
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow body >>= until_tail body K))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) false (Cg Q_E phi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  intros Hbody g n ts i cursor sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * (nat * SSig)))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CUntilNone body) >>= K))
          (Some i) cursor sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
            (ts @ i := (denote_flow body >>= until_tail body K))
            (Some i) cursor sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) => Inv g n ts i cursor sigma w0 end).
  change (entails (SSig * unit) false (Cg Q_E phi)
    (T (g, existT _ n (ts, (i, (cursor, sigma))))) w).
  eapply (eg_family T U J phi).
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]]; cbn [T U].
    rewrite interp_rr_until_none; reflexivity.
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 cursor0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply enc_mono_r; [|exact Hsegment].
    intros t z Hfinite.
    eapply euc_mono_r; [|exact Hfinite].
    intros t' z' [(g' & n' & ts' & i' & cursor' & sigma' & Hinv' & Htree) | Htail].
    + left; exists (g', existT _ n' (ts', (i', (cursor', sigma'))));
        split; [exact Hinv'|exact Htree].
    + right; exact Htail.
  - exact Hinv.
Qed.

Lemma au_csl_rr_while_wf {G : Type} {b : bool}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (ltG : relation G) (phi : ticllW (CSLObs (nat * nat) + nat))
    (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    quntil Q_A (entails (SSig * unit) false phi)
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') cursor' sigma')
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) b (Cu Q_A phi psi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  intros Wf Hbody g n ts i cursor sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * (nat * SSig)))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) cursor sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
            (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
            (Some i) cursor sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) => Inv g n ts i cursor sigma w0 end).
  set (Rv := fun (a b : (G * C) * WorldW (CSLObs (nat * nat) + nat)) =>
    ltG (fst (fst a)) (fst (fst b))).
  assert (WfR : well_founded Rv).
  { intros [[g0 context] w0].
    revert context w0.
    induction g0 as [g0 IH] using (well_founded_induction Wf).
    intros context w0; constructor.
    intros [[g' context'] w'] Hlt.
    exact (IH g' Hlt context' w'). }
  change (entails (SSig * unit) b (Cu Q_A phi psi)
    (T (g, existT _ n (ts, (i, (cursor, sigma))))) w).
  eapply (au_family_wf T U J Rv phi psi).
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]]; cbn [T U].
    rewrite interp_rr_while_unfold; reflexivity.
  - exact WfR.
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 cursor0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply auc_mono_r; [|exact Hsegment].
    intros t z [Hpsi | (g' & n' & ts' & i' & cursor' & sigma' & Hinv' & Hlt & Htree)].
    + left; exact Hpsi.
    + right; exists (g', existT _ n' (ts', (i', (cursor', sigma')))).
      split; [exact Hinv'|].
      split; [exact Hlt|exact Htree].
  - exact Hinv.
Qed.

Lemma eu_csl_rr_while_wf {G : Type} {b : bool}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (ltG : relation G) (phi : ticllW (CSLObs (nat * nat) + nat))
    (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    quntil Q_E (entails (SSig * unit) false phi)
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') cursor' sigma')
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) b (Cu Q_E phi psi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  intros Wf Hbody g n ts i cursor sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * (nat * SSig)))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) cursor sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
            (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
            (Some i) cursor sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) => Inv g n ts i cursor sigma w0 end).
  set (Rv := fun (a b : (G * C) * WorldW (CSLObs (nat * nat) + nat)) =>
    ltG (fst (fst a)) (fst (fst b))).
  assert (WfR : well_founded Rv).
  { intros [[g0 context] w0].
    revert context w0.
    induction g0 as [g0 IH] using (well_founded_induction Wf).
    intros context w0; constructor.
    intros [[g' context'] w'] Hlt.
    exact (IH g' Hlt context' w'). }
  change (entails (SSig * unit) b (Cu Q_E phi psi)
    (T (g, existT _ n (ts, (i, (cursor, sigma))))) w).
  eapply (eu_family_wf T U J Rv phi psi).
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]]; cbn [T U].
    rewrite interp_rr_while_unfold; reflexivity.
  - exact WfR.
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 cursor0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply euc_mono_r; [|exact Hsegment].
    intros t z [Hpsi | (g' & n' & ts' & i' & cursor' & sigma' & Hinv' & Hlt & Htree)].
    + left; exact Hpsi.
    + right; exists (g', existT _ n' (ts', (i', (cursor', sigma')))).
      split; [exact Hinv'|].
      split; [exact Hlt|exact Htree].
  - exact Hinv.
Qed.

Lemma af_csl_rr_while_wf {G : Type} {b : bool}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (ltG : relation G)
    (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    quntil Q_A (entails (SSig * unit) false (CNow (fun _ => True)))
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') cursor' sigma')
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  exact (au_csl_rr_while_wf
    test body K Inv ltG (CNow (fun _ => True)) psi).
Qed.

Lemma ef_csl_rr_while_wf {G : Type} {b : bool}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (ltG : relation G)
    (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  well_founded ltG ->
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    quntil Q_E (entails (SSig * unit) false (CNow (fun _ => True)))
      (fun t z => entails (SSig * unit) b psi t z \/
        exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ ltG g' g /\
          t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') cursor' sigma')
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  exact (eu_csl_rr_while_wf
    test body K Inv ltG (CNow (fun _ => True)) psi).
Qed.

Lemma ag_csl_rr_while {G : Type}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (phi : ticllW (CSLObs (nat * nat) + nat)) :
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    qnext Q_A (entails (SSig * unit) false phi)
      (quntil Q_A (entails (SSig * unit) false phi)
      (fun t z => (exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') cursor' sigma') \/
        entails (SSig * unit) false (Cg Q_A phi) t z))
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) false (Cg Q_A phi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  intros Hbody g n ts i cursor sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * (nat * SSig)))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) cursor sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
            (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
            (Some i) cursor sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) => Inv g n ts i cursor sigma w0 end).
  change (entails (SSig * unit) false (Cg Q_A phi)
    (T (g, existT _ n (ts, (i, (cursor, sigma))))) w).
  eapply (ag_family T U J phi).
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]]; cbn [T U].
    rewrite interp_rr_while_unfold; reflexivity.
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 cursor0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply anc_mono_r; [|exact Hsegment].
    intros t z Hfinite.
    eapply auc_mono_r; [|exact Hfinite].
    intros t' z' [(g' & n' & ts' & i' & cursor' & sigma' & Hinv' & Htree) | Htail].
    + left; exists (g', existT _ n' (ts', (i', (cursor', sigma'))));
        split; [exact Hinv'|exact Htree].
    + right; exact Htail.
  - exact Hinv.
Qed.

Lemma eg_csl_rr_while {G : Type}
    (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn)
    (Inv : G -> forall n, pool sE Bn (S n) -> Fin.t (S n) ->
      nat -> SSig -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
    (phi : ticllW (CSLObs (nat * nat) + nat)) :
  (forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    qnext Q_E (entails (SSig * unit) false phi)
      (quntil Q_E (entails (SSig * unit) false phi)
      (fun t z => (exists (g' : G) (n' : nat) (ts' : pool sE Bn (S n'))
          (i' : Fin.t (S n')) (cursor' : nat) (sigma' : SSig),
          Inv g' n' ts' i' cursor' sigma' z /\ t ~ interp_schedule_rr sh (S n')
              (ts' @ i' := (denote_flow (CWhile test body) >>= K))
              (Some i') cursor' sigma') \/
        entails (SSig * unit) false (Cg Q_E phi) t z))
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
          (Some i) cursor sigma) w) ->
  forall g n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      cursor sigma w, Inv g n ts i cursor sigma w ->
    entails (SSig * unit) false (Cg Q_E phi)
      (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) cursor sigma) w.
Proof.
  intros Hbody g n ts i cursor sigma w Hinv.
  set (C := { n : nat & (pool sE Bn (S n) * (Fin.t (S n) * (nat * SSig)))%type }).
  set (T := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow (CWhile test body) >>= K))
          (Some i) cursor sigma
    end).
  set (U := fun c : (G * C)%type =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) =>
      interp_schedule_rr sh (S n)
            (ts @ i := (denote_exp test >>= fun value =>
        if CoCSLSyntax.is_true value then
          denote_flow body >>= fun flow =>
            match flow with
            | None => K None
            | Some _ => Guard (denote_flow (CWhile test body) >>= K)
            end
        else K (Some tt)))
            (Some i) cursor sigma
    end).
  set (J := fun (c : (G * C)%type) w0 =>
    match c with (g, existT _ n (ts, (i, (cursor, sigma)))) => Inv g n ts i cursor sigma w0 end).
  change (entails (SSig * unit) false (Cg Q_E phi)
    (T (g, existT _ n (ts, (i, (cursor, sigma))))) w).
  eapply (eg_family T U J phi).
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]]; cbn [T U].
    rewrite interp_rr_while_unfold; reflexivity.
  - intros [g0 [n0 [ts0 [i0 [cursor0 sigma0]]]]] w0 Hinv0.
    pose proof (Hbody g0 n0 ts0 i0 cursor0 sigma0 w0 Hinv0)
      as Hsegment.
    eapply enc_mono_r; [|exact Hsegment].
    intros t z Hfinite.
    eapply euc_mono_r; [|exact Hfinite].
    intros t' z' [(g' & n' & ts' & i' & cursor' & sigma' & Hinv' & Htree) | Htail].
    + left; exists (g', existT _ n' (ts', (i', (cursor', sigma'))));
        split; [exact Hinv'|exact Htree].
    + right; exact Htail.
  - exact Hinv.
Qed.

(** ** Complete scheduled command and expression modalities *)

Lemma x_csl_nd_read  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = Some value ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c H0).
  reflexivity.
Qed.

Lemma u_csl_nd_read  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = Some value ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c H0).
  reflexivity.
Qed.

Lemma an_csl_nd_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c H0).
  reflexivity.
Qed.

Lemma en_csl_nd_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c H0).
  reflexivity.
Qed.

Lemma au_csl_nd_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c H0).
  reflexivity.
Qed.

Lemma eu_csl_nd_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c H0).
  reflexivity.
Qed.

Lemma ag_csl_nd_read  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a = Some value ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c H0).
  reflexivity.
Qed.

Lemma eg_csl_nd_read  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a = Some value ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c H0).
  reflexivity.
Qed.

Lemma ax_csl_nd_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  apply an_csl_nd_read; assumption.
Qed.

Lemma ex_csl_nd_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  apply en_csl_nd_read; assumption.
Qed.

Lemma af_csl_nd_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  apply au_csl_nd_read; assumption.
Qed.

Lemma ef_csl_nd_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some value))) (Some i) ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  apply eu_csl_nd_read; assumption.
Qed.

Lemma x_csl_nd_read_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_read_missing by assumption.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_nd_read_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_read_missing by assumption.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_nd_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_read_missing by assumption.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_nd_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_read_missing by assumption.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_nd_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_read_missing by assumption.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_nd_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_read_missing by assumption.
  apply eu_stuck.
Qed.

Lemma ag_csl_nd_read_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_read_missing by assumption.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_nd_read_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_read_missing by assumption.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_nd_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply an_csl_nd_read_missing; assumption.
Qed.

Lemma ex_csl_nd_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply en_csl_nd_read_missing; assumption.
Qed.

Lemma af_csl_nd_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply au_csl_nd_read_missing; assumption.
Qed.

Lemma ef_csl_nd_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply eu_csl_nd_read_missing; assumption.
Qed.

Lemma x_csl_nd_write  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a <> None ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  (P (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt)).
Proof.
  intros H0.
  rewrite interp_nd_source_write_present by assumption.
  apply qnext_log_iff; assumption.
Qed.

Lemma u_csl_nd_write  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a <> None ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  (Q (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) (w) \/ (P (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt))).
Proof.
  intros H0.
  rewrite interp_nd_source_write_present by assumption.
  rewrite quntil_unfold at 1.
  rewrite qnext_log_iff by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
Qed.

Lemma an_csl_nd_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt)).
Proof.
  intros H0.
  rewrite interp_nd_source_write_present by assumption.
  apply an_log_iff.
Qed.

Lemma en_csl_nd_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt)).
Proof.
  intros H0.
  rewrite interp_nd_source_write_present by assumption.
  apply en_log_iff.
Qed.

Lemma au_csl_nd_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt))).
Proof.
  intros H0.
  rewrite interp_nd_source_write_present by assumption.
  apply au_log_iff.
Qed.

Lemma eu_csl_nd_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt))).
Proof.
  intros H0.
  rewrite interp_nd_source_write_present by assumption.
  apply eu_log_iff.
Qed.

Lemma ag_csl_nd_write  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a <> None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt)).
Proof.
  intros H0.
  rewrite interp_nd_source_write_present by assumption.
  apply ag_log_iff.
Qed.

Lemma eg_csl_nd_write  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a <> None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt)).
Proof.
  intros H0.
  rewrite interp_nd_source_write_present by assumption.
  apply eg_log_iff.
Qed.

Lemma ax_csl_nd_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt)).
Proof.
  intros H0.
  apply an_csl_nd_write; assumption.
Qed.

Lemma ex_csl_nd_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt)).
Proof.
  intros H0.
  apply en_csl_nd_write; assumption.
Qed.

Lemma af_csl_nd_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt))).
Proof.
  intros H0.
  apply au_csl_nd_write; assumption.
Qed.

Lemma ef_csl_nd_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (upd h a value,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) ((upd h a value,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a value,allocs))) tt))).
Proof.
  intros H0.
  apply eu_csl_nd_write; assumption.
Qed.

Lemma x_csl_nd_write_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_write_missing by assumption.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_nd_write_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_write_missing by assumption.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_nd_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_write_missing by assumption.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_nd_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_write_missing by assumption.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_nd_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_write_missing by assumption.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_nd_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_write_missing by assumption.
  apply eu_stuck.
Qed.

Lemma ag_csl_nd_write_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_write_missing by assumption.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_nd_write_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_write_missing by assumption.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_nd_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply an_csl_nd_write_missing; assumption.
Qed.

Lemma ex_csl_nd_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply en_csl_nd_write_missing; assumption.
Qed.

Lemma af_csl_nd_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply au_csl_nd_write_missing; assumption.
Qed.

Lemma ef_csl_nd_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply eu_csl_nd_write_missing; assumption.
Qed.

Lemma x_csl_nd_emit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) w <->
  (P (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) w /\ Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c))) (Obs (Log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)))) tt)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply qnext_log_iff; assumption.
Qed.

Lemma u_csl_nd_emit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) w <->
  (Q (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) (w) \/ (P (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) w /\ quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c))) (Obs (Log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)))) tt))).
Proof.
  rewrite interp_nd_source_emit_log.
  rewrite quntil_unfold at 1.
  rewrite qnext_log_iff by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
Qed.

Lemma en_csl_nd_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c))) (Obs (Log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)))) tt)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply en_log_iff.
Qed.

Lemma eu_csl_nd_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) (w) \/ (entails (SSig * unit) false phi (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c))) (Obs (Log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)))) tt))).
Proof.
  rewrite interp_nd_source_emit_log.
  apply eu_log_iff.
Qed.

Lemma eg_csl_nd_emit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c))) (Obs (Log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)))) tt)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply eg_log_iff.
Qed.

Lemma ax_csl_nd_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c))) (Obs (Log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)))) tt)).
Proof.
  apply an_csl_nd_emit; assumption.
Qed.

Lemma ex_csl_nd_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c))) (Obs (Log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)))) tt)).
Proof.
  apply en_csl_nd_emit; assumption.
Qed.

Lemma af_csl_nd_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c))) (Obs (Log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)))) tt))).
Proof.
  apply au_csl_nd_emit; assumption.
Qed.

Lemma ef_csl_nd_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory,(ctx,S c))) (Obs (Log ((CSLEmit (stamp (tag,value) c) : CSLObs (nat * nat)))) tt))).
Proof.
  apply eu_csl_nd_emit; assumption.
Qed.

Lemma x_csl_nd_yield  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) (memory,(ctx,c))) w <->
  (P (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) w /\ (match q with Q_A => forall j : Fin.t (S n), Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w) | Q_E => exists j : Fin.t (S n), Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w) end)).
Proof.
  rewrite interp_nd_source_yield.
  rewrite (interp_schedule_nd_select sh).
  apply (qnext_brS_iff q _ _ Fin.F1); assumption.
Qed.

Lemma u_csl_nd_yield  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) (memory,(ctx,c))) w <->
  (Q (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) (w) \/ (P (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) w /\ (match q with Q_A => forall j : Fin.t (S n), quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w) | Q_E => exists j : Fin.t (S n), quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w) end))).
Proof.
  rewrite interp_nd_source_yield.
  rewrite (interp_schedule_nd_select sh).
  rewrite quntil_unfold at 1.
  rewrite (qnext_brS_iff q _ _ Fin.F1) by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
Qed.

Lemma en_csl_nd_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) w /\ (exists j : Fin.t (S n), entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w))).
Proof.
  rewrite interp_nd_source_yield.
  rewrite (interp_schedule_nd_select sh).
  apply en_brS.
Qed.

Lemma eu_csl_nd_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) w /\ (exists j : Fin.t (S n), entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w)))).
Proof.
  rewrite interp_nd_source_yield.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply eu_brS.
Qed.

Lemma eg_csl_nd_yield  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) w /\ (exists j : Fin.t (S n), entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w))).
Proof.
  rewrite interp_nd_source_yield.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply eg_brS.
Qed.

Lemma ax_csl_nd_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) w /\ (forall j : Fin.t (S n), entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w))).
Proof.
  apply an_csl_nd_yield; assumption.
Qed.

Lemma ex_csl_nd_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) w /\ (exists j : Fin.t (S n), entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w))).
Proof.
  apply en_csl_nd_yield; assumption.
Qed.

Lemma af_csl_nd_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) w /\ (forall j : Fin.t (S n), entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w)))).
Proof.
  apply au_csl_nd_yield; assumption.
Qed.

Lemma ef_csl_nd_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c)))) w /\ (exists j : Fin.t (S n), entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some j) (memory,(ctx,c))) (w)))).
Proof.
  apply eu_csl_nd_yield; assumption.
Qed.

Lemma x_csl_nd_fork  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_fork.
  reflexivity.
Qed.

Lemma u_csl_nd_fork  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_fork.
  reflexivity.
Qed.

Lemma an_csl_nd_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_fork.
  reflexivity.
Qed.

Lemma en_csl_nd_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_fork.
  reflexivity.
Qed.

Lemma au_csl_nd_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_fork.
  reflexivity.
Qed.

Lemma eu_csl_nd_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_fork.
  reflexivity.
Qed.

Lemma ag_csl_nd_fork  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_fork.
  reflexivity.
Qed.

Lemma eg_csl_nd_fork  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_fork.
  reflexivity.
Qed.

Lemma ax_csl_nd_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_fork; assumption.
Qed.

Lemma ex_csl_nd_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_fork; assumption.
Qed.

Lemma af_csl_nd_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_fork; assumption.
Qed.

Lemma ef_csl_nd_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_fork; assumption.
Qed.

Lemma x_csl_nd_ret {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_ret.
  reflexivity.
Qed.

Lemma u_csl_nd_ret {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_ret.
  reflexivity.
Qed.

Lemma an_csl_nd_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_ret.
  reflexivity.
Qed.

Lemma en_csl_nd_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_ret.
  reflexivity.
Qed.

Lemma au_csl_nd_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_ret.
  reflexivity.
Qed.

Lemma eu_csl_nd_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_ret.
  reflexivity.
Qed.

Lemma ag_csl_nd_ret {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_ret.
  reflexivity.
Qed.

Lemma eg_csl_nd_ret {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_ret.
  reflexivity.
Qed.

Lemma ax_csl_nd_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_ret; assumption.
Qed.

Lemma ex_csl_nd_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_ret; assumption.
Qed.

Lemma af_csl_nd_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_ret; assumption.
Qed.

Lemma ef_csl_nd_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some x))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_ret; assumption.
Qed.

Lemma x_csl_nd_bind {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_bind.
  reflexivity.
Qed.

Lemma u_csl_nd_bind {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_bind.
  reflexivity.
Qed.

Lemma an_csl_nd_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_bind.
  reflexivity.
Qed.

Lemma en_csl_nd_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_bind.
  reflexivity.
Qed.

Lemma au_csl_nd_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_bind.
  reflexivity.
Qed.

Lemma eu_csl_nd_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_bind.
  reflexivity.
Qed.

Lemma ag_csl_nd_bind {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_bind.
  reflexivity.
Qed.

Lemma eg_csl_nd_bind {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_bind.
  reflexivity.
Qed.

Lemma ax_csl_nd_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_bind; assumption.
Qed.

Lemma ex_csl_nd_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_bind; assumption.
Qed.

Lemma af_csl_nd_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_bind; assumption.
Qed.

Lemma ef_csl_nd_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_bind; assumption.
Qed.

Lemma x_csl_nd_alloc_first  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  (P (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c H0 H1 H2 H3).
  apply qnext_log_iff; assumption.
Qed.

Lemma u_csl_nd_alloc_first  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  (Q (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (P (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c H0 H1 H2 H3).
  rewrite quntil_unfold at 1.
  rewrite qnext_log_iff by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
Qed.

Lemma an_csl_nd_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c H0 H1 H2 H3).
  apply an_log_iff.
Qed.

Lemma en_csl_nd_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c H0 H1 H2 H3).
  apply en_log_iff.
Qed.

Lemma au_csl_nd_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c H0 H1 H2 H3).
  apply au_log_iff.
Qed.

Lemma eu_csl_nd_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c H0 H1 H2 H3).
  apply eu_log_iff.
Qed.

Lemma ag_csl_nd_alloc_first  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c H0 H1 H2 H3).
  apply ag_log_iff.
Qed.

Lemma eg_csl_nd_alloc_first  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c H0 H1 H2 H3).
  apply eg_log_iff.
Qed.

Lemma ax_csl_nd_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)).
Proof.
  intros H0 H1 H2 H3.
  apply an_csl_nd_alloc_first; assumption.
Qed.

Lemma ex_csl_nd_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)).
Proof.
  intros H0 H1 H2 H3.
  apply en_csl_nd_alloc_first; assumption.
Qed.

Lemma af_csl_nd_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1 H2 H3.
  apply au_csl_nd_alloc_first; assumption.
Qed.

Lemma ef_csl_nd_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1 H2 H3.
  apply eu_csl_nd_alloc_first; assumption.
Qed.

Lemma x_csl_nd_alloc  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  heap_finite h ->
  Nat.lt 0 size ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (P (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (x_csl_nd_alloc_first n ts i size base K h allocs ctx c w q P Q HP HP_live HQ H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (x_csl_nd_alloc_first n ts i size base K h allocs ctx c w q P Q HP HP_live HQ H1 Base Free First); apply Hall; assumption.
Qed.

Lemma u_csl_nd_alloc  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  heap_finite h ->
  Nat.lt 0 size ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (Q (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (P (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (u_csl_nd_alloc_first n ts i size base K h allocs ctx c w q P Q HP HP_live HQ H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (u_csl_nd_alloc_first n ts i size base K h allocs ctx c w q P Q HP HP_live HQ H1 Base Free First); apply Hall; assumption.
Qed.

Lemma an_csl_nd_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (an_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi psi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (an_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi psi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma en_csl_nd_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (en_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi psi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (en_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi psi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma au_csl_nd_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) b psi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (au_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi psi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (au_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi psi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma eu_csl_nd_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) b psi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (eu_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi psi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (eu_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi psi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma ag_csl_nd_alloc  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (ag_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (ag_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma eg_csl_nd_alloc  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false phi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (eg_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (eg_csl_nd_alloc_first n ts i size base K h allocs ctx c w phi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma ax_csl_nd_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1.
  apply an_csl_nd_alloc; assumption.
Qed.

Lemma ex_csl_nd_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt))).
Proof.
  intros H0 H1.
  apply en_csl_nd_alloc; assumption.
Qed.

Lemma af_csl_nd_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) b psi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)))).
Proof.
  intros H0 H1.
  apply au_csl_nd_alloc; assumption.
Qed.

Lemma ef_csl_nd_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) b psi (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (managed_alloc (h,allocs) base size));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some base))) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (CSLHeap (managed_alloc (h,allocs) base size))) tt)))).
Proof.
  intros H0 H1.
  apply eu_csl_nd_alloc; assumption.
Qed.

Lemma x_csl_nd_alloc_zero  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  False.
Proof.
  rewrite interp_nd_source_alloc_zero.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_nd_alloc_zero  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  rewrite interp_nd_source_alloc_zero.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_nd_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  rewrite interp_nd_source_alloc_zero.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_nd_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  rewrite interp_nd_source_alloc_zero.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_nd_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  rewrite interp_nd_source_alloc_zero.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_nd_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  rewrite interp_nd_source_alloc_zero.
  apply eu_stuck.
Qed.

Lemma ag_csl_nd_alloc_zero  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  rewrite interp_nd_source_alloc_zero.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_nd_alloc_zero  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  rewrite interp_nd_source_alloc_zero.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_nd_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  apply an_csl_nd_alloc_zero; assumption.
Qed.

Lemma ex_csl_nd_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  apply en_csl_nd_alloc_zero; assumption.
Qed.

Lemma af_csl_nd_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  apply au_csl_nd_alloc_zero; assumption.
Qed.

Lemma ef_csl_nd_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  apply eu_csl_nd_alloc_zero; assumption.
Qed.

Lemma x_csl_nd_alloc_no_space  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  False.
Proof.
  intros H0 H1.
  rewrite interp_nd_source_alloc_no_space by assumption.
  apply qnext_dead_iff; apply spin_no_ktrans.
Qed.

Lemma u_csl_nd_alloc_no_space  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  Q ((CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0 H1.
  rewrite interp_nd_source_alloc_no_space by assumption.
  apply quntil_dead_iff; apply spin_no_ktrans.
Qed.

Lemma an_csl_nd_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  rewrite interp_nd_source_alloc_no_space by assumption.
  rewrite ticl_an; exact (qnext_dead_iff Q_A (CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)) (entails _ false phi) (entails _ b psi) w (spin_no_ktrans w)).
Qed.

Lemma en_csl_nd_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  rewrite interp_nd_source_alloc_no_space by assumption.
  rewrite ticl_en; exact (qnext_dead_iff Q_E (CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)) (entails _ false phi) (entails _ b psi) w (spin_no_ktrans w)).
Qed.

Lemma au_csl_nd_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0 H1.
  rewrite interp_nd_source_alloc_no_space by assumption.
  rewrite ticl_au; exact (quntil_dead_iff Q_A (CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)) (entails _ false phi) (entails _ b psi) w (spin_no_ktrans w)).
Qed.

Lemma eu_csl_nd_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0 H1.
  rewrite interp_nd_source_alloc_no_space by assumption.
  rewrite ticl_eu; exact (quntil_dead_iff Q_E (CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)) (entails _ false phi) (entails _ b psi) w (spin_no_ktrans w)).
Qed.

Lemma ag_csl_nd_alloc_no_space  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  rewrite interp_nd_source_alloc_no_space by assumption.
  split; [intro H; cdestruct H|contradiction].
  destruct Hs as (u & z & TR); exact (spin_no_ktrans w u z TR).
Qed.

Lemma eg_csl_nd_alloc_no_space  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  rewrite interp_nd_source_alloc_no_space by assumption.
  split; [intro H; cdestruct H|contradiction].
  exact (spin_no_ktrans w _ _ TR).
Qed.

Lemma ax_csl_nd_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  apply an_csl_nd_alloc_no_space; assumption.
Qed.

Lemma ex_csl_nd_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  apply en_csl_nd_alloc_no_space; assumption.
Qed.

Lemma af_csl_nd_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0 H1.
  apply au_csl_nd_alloc_no_space; assumption.
Qed.

Lemma ef_csl_nd_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0 H1.
  apply eu_csl_nd_alloc_no_space; assumption.
Qed.

Lemma x_csl_nd_free  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  managed_free memory base = Some memory' ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) w <->
  (match base with 0 => qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (P (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt)) end).
Proof.
  intros H0.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply qnext_log_iff; assumption.
Qed.

Lemma u_csl_nd_free  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  managed_free memory base = Some memory' ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) w <->
  (match base with 0 => quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (Q (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) (w) \/ (P (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt))) end).
Proof.
  intros H0.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - rewrite quntil_unfold at 1.
  rewrite qnext_log_iff by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
Qed.

Lemma an_csl_nd_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false phi (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt)) end).
Proof.
  intros H0.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply an_log_iff.
Qed.

Lemma en_csl_nd_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false phi (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt)) end).
Proof.
  intros H0.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply en_log_iff.
Qed.

Lemma au_csl_nd_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) b psi (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt))) end).
Proof.
  intros H0.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply au_log_iff.
Qed.

Lemma eu_csl_nd_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) b psi (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt))) end).
Proof.
  intros H0.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply eu_log_iff.
Qed.

Lemma ag_csl_nd_free  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false phi (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt)) end).
Proof.
  intros H0.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply ag_log_iff.
Qed.

Lemma eg_csl_nd_free  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false phi (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt)) end).
Proof.
  intros H0.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply eg_log_iff.
Qed.

Lemma ax_csl_nd_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt)) end).
Proof.
  intros H0.
  apply an_csl_nd_free; assumption.
Qed.

Lemma ex_csl_nd_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt)) end).
Proof.
  intros H0.
  apply en_csl_nd_free; assumption.
Qed.

Lemma af_csl_nd_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) b psi (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt))) end).
Proof.
  intros H0.
  apply au_csl_nd_free; assumption.
Qed.

Lemma ef_csl_nd_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) b psi (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap memory');; (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some tt))) (Some i) (memory',(ctx,c))) (Obs (Log (CSLHeap memory')) tt))) end).
Proof.
  intros H0.
  apply eu_csl_nd_free; assumption.
Qed.

Lemma x_csl_nd_free_invalid  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  managed_free memory base = None ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) w <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_free_invalid by assumption.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_nd_free_invalid  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  managed_free memory base = None ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_free_invalid by assumption.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_nd_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_free_invalid by assumption.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_nd_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_free_invalid by assumption.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_nd_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_free_invalid by assumption.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_nd_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_free_invalid by assumption.
  apply eu_stuck.
Qed.

Lemma ag_csl_nd_free_invalid  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  managed_free memory base = None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_free_invalid by assumption.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_nd_free_invalid  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  managed_free memory base = None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_free_invalid by assumption.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_nd_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply an_csl_nd_free_invalid; assumption.
Qed.

Lemma ex_csl_nd_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply en_csl_nd_free_invalid; assumption.
Qed.

Lemma af_csl_nd_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply au_csl_nd_free_invalid; assumption.
Qed.

Lemma ef_csl_nd_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) (memory : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply eu_csl_nd_free_invalid; assumption.
Qed.

Lemma x_csl_nd_cas  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_cas_exp.
  reflexivity.
Qed.

Lemma u_csl_nd_cas  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_cas_exp.
  reflexivity.
Qed.

Lemma an_csl_nd_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_cas_exp.
  reflexivity.
Qed.

Lemma en_csl_nd_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_cas_exp.
  reflexivity.
Qed.

Lemma au_csl_nd_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_cas_exp.
  reflexivity.
Qed.

Lemma eu_csl_nd_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_cas_exp.
  reflexivity.
Qed.

Lemma ag_csl_nd_cas  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_cas_exp.
  reflexivity.
Qed.

Lemma eg_csl_nd_cas  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_cas_exp.
  reflexivity.
Qed.

Lemma ax_csl_nd_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_cas; assumption.
Qed.

Lemma ex_csl_nd_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_cas; assumption.
Qed.

Lemma af_csl_nd_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_cas; assumption.
Qed.

Lemma ef_csl_nd_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_cas; assumption.
Qed.

Lemma x_csl_nd_cas_value  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = Some current ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  (if Nat.eqb current expected then (P (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt)) else qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply qnext_log_iff; assumption.
  - reflexivity.
Qed.

Lemma u_csl_nd_cas_value  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = Some current ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  (if Nat.eqb current expected then (Q (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) (w) \/ (P (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt))) else quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - rewrite quntil_unfold at 1.
  rewrite qnext_log_iff by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
  - reflexivity.
Qed.

Lemma an_csl_nd_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false phi (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt)) else entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply an_log_iff.
  - reflexivity.
Qed.

Lemma en_csl_nd_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false phi (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt)) else entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply en_log_iff.
  - reflexivity.
Qed.

Lemma au_csl_nd_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) b psi (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt))) else entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply au_log_iff.
  - reflexivity.
Qed.

Lemma eu_csl_nd_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) b psi (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt))) else entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply eu_log_iff.
  - reflexivity.
Qed.

Lemma ag_csl_nd_cas_value  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a = Some current ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false phi (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt)) else entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply ag_log_iff.
  - reflexivity.
Qed.

Lemma eg_csl_nd_cas_value  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a = Some current ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false phi (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt)) else entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply eg_log_iff.
  - reflexivity.
Qed.

Lemma ax_csl_nd_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt)) else entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  apply an_csl_nd_cas_value; assumption.
Qed.

Lemma ex_csl_nd_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt)) else entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  apply en_csl_nd_cas_value; assumption.
Qed.

Lemma af_csl_nd_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) b psi (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt))) else entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  apply au_csl_nd_cas_value; assumption.
Qed.

Lemma ef_csl_nd_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) b psi (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (CSLHeap (upd h a desired,allocs));; (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some true))) (Some i) ((upd h a desired,allocs),(ctx,c))) (Obs (Log (CSLHeap (upd h a desired,allocs))) tt))) else entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K (Some false))) (Some i) ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  apply eu_csl_nd_cas_value; assumption.
Qed.

Lemma x_csl_nd_cas_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_cas_missing by assumption.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_nd_cas_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_cas_missing by assumption.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_nd_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_cas_missing by assumption.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_nd_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_cas_missing by assumption.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_nd_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_cas_missing by assumption.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_nd_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_source_cas_missing by assumption.
  apply eu_stuck.
Qed.

Lemma ag_csl_nd_cas_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_cas_missing by assumption.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_nd_cas_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_source_cas_missing by assumption.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_nd_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply an_csl_nd_cas_missing; assumption.
Qed.

Lemma ex_csl_nd_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply en_csl_nd_cas_missing; assumption.
Qed.

Lemma af_csl_nd_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply au_csl_nd_cas_missing; assumption.
Qed.

Lemma ef_csl_nd_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply eu_csl_nd_cas_missing; assumption.
Qed.

Lemma x_csl_nd_eval  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_eval.
  reflexivity.
Qed.

Lemma u_csl_nd_eval  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_eval.
  reflexivity.
Qed.

Lemma an_csl_nd_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_eval.
  reflexivity.
Qed.

Lemma en_csl_nd_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_eval.
  reflexivity.
Qed.

Lemma au_csl_nd_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_eval.
  reflexivity.
Qed.

Lemma eu_csl_nd_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_eval.
  reflexivity.
Qed.

Lemma ag_csl_nd_eval  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_eval.
  reflexivity.
Qed.

Lemma eg_csl_nd_eval  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_eval.
  reflexivity.
Qed.

Lemma ax_csl_nd_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_eval; assumption.
Qed.

Lemma ex_csl_nd_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_eval; assumption.
Qed.

Lemma af_csl_nd_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_eval; assumption.
Qed.

Lemma ef_csl_nd_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_eval; assumption.
Qed.

Lemma x_csl_nd_assign  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_assign.
  reflexivity.
Qed.

Lemma u_csl_nd_assign  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_assign.
  reflexivity.
Qed.

Lemma an_csl_nd_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_assign.
  reflexivity.
Qed.

Lemma en_csl_nd_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_assign.
  reflexivity.
Qed.

Lemma au_csl_nd_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_assign.
  reflexivity.
Qed.

Lemma eu_csl_nd_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_assign.
  reflexivity.
Qed.

Lemma ag_csl_nd_assign  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_assign.
  reflexivity.
Qed.

Lemma eg_csl_nd_assign  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_assign.
  reflexivity.
Qed.

Lemma ax_csl_nd_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_assign; assumption.
Qed.

Lemma ex_csl_nd_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_assign; assumption.
Qed.

Lemma af_csl_nd_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_assign; assumption.
Qed.

Lemma ef_csl_nd_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_assign; assumption.
Qed.

Lemma x_csl_nd_if {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_if.
  reflexivity.
Qed.

Lemma u_csl_nd_if {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_if.
  reflexivity.
Qed.

Lemma an_csl_nd_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_if.
  reflexivity.
Qed.

Lemma en_csl_nd_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_if.
  reflexivity.
Qed.

Lemma au_csl_nd_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_if.
  reflexivity.
Qed.

Lemma eu_csl_nd_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_if.
  reflexivity.
Qed.

Lemma ag_csl_nd_if {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_if.
  reflexivity.
Qed.

Lemma eg_csl_nd_if {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_if.
  reflexivity.
Qed.

Lemma ax_csl_nd_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_if; assumption.
Qed.

Lemma ex_csl_nd_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_if; assumption.
Qed.

Lemma af_csl_nd_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_if; assumption.
Qed.

Lemma ef_csl_nd_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_if; assumption.
Qed.

Lemma x_csl_nd_until_none_unfold {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_until_none.
  reflexivity.
Qed.

Lemma u_csl_nd_until_none_unfold {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_until_none.
  reflexivity.
Qed.

Lemma an_csl_nd_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_until_none.
  reflexivity.
Qed.

Lemma en_csl_nd_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_until_none.
  reflexivity.
Qed.

Lemma au_csl_nd_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_until_none.
  reflexivity.
Qed.

Lemma eu_csl_nd_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_until_none.
  reflexivity.
Qed.

Lemma ag_csl_nd_until_none_unfold {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_until_none.
  reflexivity.
Qed.

Lemma eg_csl_nd_until_none_unfold {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_until_none.
  reflexivity.
Qed.

Lemma ax_csl_nd_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_until_none_unfold; assumption.
Qed.

Lemma ex_csl_nd_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_until_none_unfold; assumption.
Qed.

Lemma af_csl_nd_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_until_none_unfold; assumption.
Qed.

Lemma ef_csl_nd_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_until_none_unfold; assumption.
Qed.

Lemma x_csl_nd_while_unfold  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_while_unfold.
  reflexivity.
Qed.

Lemma u_csl_nd_while_unfold  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_while_unfold.
  reflexivity.
Qed.

Lemma an_csl_nd_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_while_unfold.
  reflexivity.
Qed.

Lemma en_csl_nd_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_while_unfold.
  reflexivity.
Qed.

Lemma au_csl_nd_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_while_unfold.
  reflexivity.
Qed.

Lemma eu_csl_nd_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_while_unfold.
  reflexivity.
Qed.

Lemma ag_csl_nd_while_unfold  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_while_unfold.
  reflexivity.
Qed.

Lemma eg_csl_nd_while_unfold  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_while_unfold.
  reflexivity.
Qed.

Lemma ax_csl_nd_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_while_unfold; assumption.
Qed.

Lemma ex_csl_nd_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_while_unfold; assumption.
Qed.

Lemma af_csl_nd_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_while_unfold; assumption.
Qed.

Lemma ef_csl_nd_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_while_unfold; assumption.
Qed.

Lemma x_csl_nd_exp_lit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_lit.
  reflexivity.
Qed.

Lemma u_csl_nd_exp_lit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_lit.
  reflexivity.
Qed.

Lemma an_csl_nd_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_lit.
  reflexivity.
Qed.

Lemma en_csl_nd_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_lit.
  reflexivity.
Qed.

Lemma au_csl_nd_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_lit.
  reflexivity.
Qed.

Lemma eu_csl_nd_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_lit.
  reflexivity.
Qed.

Lemma ag_csl_nd_exp_lit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_lit.
  reflexivity.
Qed.

Lemma eg_csl_nd_exp_lit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_lit.
  reflexivity.
Qed.

Lemma ax_csl_nd_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_exp_lit; assumption.
Qed.

Lemma ex_csl_nd_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_exp_lit; assumption.
Qed.

Lemma af_csl_nd_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_exp_lit; assumption.
Qed.

Lemma ef_csl_nd_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_exp_lit; assumption.
Qed.

Lemma x_csl_nd_exp_var  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  lookup name ctx = Some value ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) w <->
  (P (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (match q with Q_A => forall j : Fin.t (S n), Q (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w) | Q_E => exists j : Fin.t (S n), Q (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w) end)).
Proof.
  intros H0.
  rewrite (interp_nd_var n ts i name value K (memory,(ctx,c)) H0).
  rewrite (interp_schedule_nd_select sh).
  apply (qnext_brS_iff q _ _ Fin.F1); assumption.
Qed.

Lemma u_csl_nd_exp_var  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  lookup name ctx = Some value ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) w <->
  (Q (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) (w) \/ (P (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (match q with Q_A => forall j : Fin.t (S n), quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w) | Q_E => exists j : Fin.t (S n), quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w) end))).
Proof.
  intros H0.
  rewrite (interp_nd_var n ts i name value K (memory,(ctx,c)) H0).
  rewrite (interp_schedule_nd_select sh).
  rewrite quntil_unfold at 1.
  rewrite (qnext_brS_iff q _ _ Fin.F1) by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
Qed.

Lemma an_csl_nd_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (forall j : Fin.t (S n), entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w))).
Proof.
  intros H0.
  rewrite (interp_nd_var n ts i name value K (memory,(ctx,c)) H0).
  rewrite (interp_schedule_nd_select sh).
  apply (an_brS _ _ Fin.F1).
Qed.

Lemma en_csl_nd_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (exists j : Fin.t (S n), entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w))).
Proof.
  intros H0.
  rewrite (interp_nd_var n ts i name value K (memory,(ctx,c)) H0).
  rewrite (interp_schedule_nd_select sh).
  apply en_brS.
Qed.

Lemma au_csl_nd_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (forall j : Fin.t (S n), entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w)))).
Proof.
  intros H0.
  rewrite (interp_nd_var n ts i name value K (memory,(ctx,c)) H0).
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply (au_brS _ _ Fin.F1).
Qed.

Lemma eu_csl_nd_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (exists j : Fin.t (S n), entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w)))).
Proof.
  intros H0.
  rewrite (interp_nd_var n ts i name value K (memory,(ctx,c)) H0).
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply eu_brS.
Qed.

Lemma ag_csl_nd_exp_var  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  lookup name ctx = Some value ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (forall j : Fin.t (S n), entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w))).
Proof.
  intros H0.
  rewrite (interp_nd_var n ts i name value K (memory,(ctx,c)) H0).
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply (ag_brS _ _ Fin.F1).
Qed.

Lemma eg_csl_nd_exp_var  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  lookup name ctx = Some value ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (exists j : Fin.t (S n), entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w))).
Proof.
  intros H0.
  rewrite (interp_nd_var n ts i name value K (memory,(ctx,c)) H0).
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply eg_brS.
Qed.

Lemma ax_csl_nd_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (forall j : Fin.t (S n), entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w))).
Proof.
  intros H0.
  apply an_csl_nd_exp_var; assumption.
Qed.

Lemma ex_csl_nd_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (exists j : Fin.t (S n), entails (SSig * unit) b psi (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w))).
Proof.
  intros H0.
  apply en_csl_nd_exp_var; assumption.
Qed.

Lemma af_csl_nd_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (forall j : Fin.t (S n), entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w)))).
Proof.
  intros H0.
  apply au_csl_nd_exp_var; assumption.
Qed.

Lemma ef_csl_nd_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (brS (branchn (S n)) (fun j : Fin.t (S n) => interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c)))) w /\ (exists j : Fin.t (S n), entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (K value)) (Some j) (memory,(ctx,c))) (w)))).
Proof.
  intros H0.
  apply eu_csl_nd_exp_var; assumption.
Qed.

Lemma x_csl_nd_exp_var_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  lookup name ctx = None ->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) w <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_var_missing by assumption.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_nd_exp_var_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  lookup name ctx = None ->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_var_missing by assumption.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_nd_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_var_missing by assumption.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_nd_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_var_missing by assumption.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_nd_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_var_missing by assumption.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_nd_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_nd_var_missing by assumption.
  apply eu_stuck.
Qed.

Lemma ag_csl_nd_exp_var_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  lookup name ctx = None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_var_missing by assumption.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_nd_exp_var_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  lookup name ctx = None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_nd_var_missing by assumption.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_nd_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply an_csl_nd_exp_var_missing; assumption.
Qed.

Lemma ex_csl_nd_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply en_csl_nd_exp_var_missing; assumption.
Qed.

Lemma af_csl_nd_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply au_csl_nd_exp_var_missing; assumption.
Qed.

Lemma ef_csl_nd_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply eu_csl_nd_exp_var_missing; assumption.
Qed.

Lemma x_csl_nd_exp_plus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_plus.
  reflexivity.
Qed.

Lemma u_csl_nd_exp_plus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_plus.
  reflexivity.
Qed.

Lemma an_csl_nd_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_plus.
  reflexivity.
Qed.

Lemma en_csl_nd_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_plus.
  reflexivity.
Qed.

Lemma au_csl_nd_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_plus.
  reflexivity.
Qed.

Lemma eu_csl_nd_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_plus.
  reflexivity.
Qed.

Lemma ag_csl_nd_exp_plus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_plus.
  reflexivity.
Qed.

Lemma eg_csl_nd_exp_plus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_plus.
  reflexivity.
Qed.

Lemma ax_csl_nd_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_exp_plus; assumption.
Qed.

Lemma ex_csl_nd_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_exp_plus; assumption.
Qed.

Lemma af_csl_nd_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_exp_plus; assumption.
Qed.

Lemma ef_csl_nd_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_exp_plus; assumption.
Qed.

Lemma x_csl_nd_exp_minus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_minus.
  reflexivity.
Qed.

Lemma u_csl_nd_exp_minus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_minus.
  reflexivity.
Qed.

Lemma an_csl_nd_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_minus.
  reflexivity.
Qed.

Lemma en_csl_nd_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_minus.
  reflexivity.
Qed.

Lemma au_csl_nd_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_minus.
  reflexivity.
Qed.

Lemma eu_csl_nd_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_minus.
  reflexivity.
Qed.

Lemma ag_csl_nd_exp_minus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_minus.
  reflexivity.
Qed.

Lemma eg_csl_nd_exp_minus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_minus.
  reflexivity.
Qed.

Lemma ax_csl_nd_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_exp_minus; assumption.
Qed.

Lemma ex_csl_nd_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_exp_minus; assumption.
Qed.

Lemma af_csl_nd_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_exp_minus; assumption.
Qed.

Lemma ef_csl_nd_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_exp_minus; assumption.
Qed.

Lemma x_csl_nd_exp_mult  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_mult.
  reflexivity.
Qed.

Lemma u_csl_nd_exp_mult  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_mult.
  reflexivity.
Qed.

Lemma an_csl_nd_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_mult.
  reflexivity.
Qed.

Lemma en_csl_nd_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_mult.
  reflexivity.
Qed.

Lemma au_csl_nd_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_mult.
  reflexivity.
Qed.

Lemma eu_csl_nd_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_mult.
  reflexivity.
Qed.

Lemma ag_csl_nd_exp_mult  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_mult.
  reflexivity.
Qed.

Lemma eg_csl_nd_exp_mult  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat)))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_exp_mult.
  reflexivity.
Qed.

Lemma ax_csl_nd_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply an_csl_nd_exp_mult; assumption.
Qed.

Lemma ex_csl_nd_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply en_csl_nd_exp_mult; assumption.
Qed.

Lemma af_csl_nd_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply au_csl_nd_exp_mult; assumption.
Qed.

Lemma ef_csl_nd_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_nd sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_nd_exp_mult; assumption.
Qed.

Lemma x_csl_nd_guard  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (t : thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (Guard t)) (Some i) (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_nd sh (S n) (ts @ i := (t)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_guard.
  reflexivity.
Qed.

Lemma u_csl_nd_guard  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (t : thread sE Bn) memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat)) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (Guard t)) (Some i) (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_nd sh (S n) (ts @ i := (t)) (Some i) (memory,(ctx,c))) (w).
Proof.
  rewrite interp_nd_source_guard.
  reflexivity.
Qed.

Lemma x_csl_rr_read  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = Some value ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_rr_read_value n ts i a value K cursor h allocs ctx c H0).
  reflexivity.
Qed.

Lemma u_csl_rr_read  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = Some value ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_rr_read_value n ts i a value K cursor h allocs ctx c H0).
  reflexivity.
Qed.

Lemma an_csl_rr_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_rr_read_value n ts i a value K cursor h allocs ctx c H0).
  reflexivity.
Qed.

Lemma en_csl_rr_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_rr_read_value n ts i a value K cursor h allocs ctx c H0).
  reflexivity.
Qed.

Lemma au_csl_rr_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_rr_read_value n ts i a value K cursor h allocs ctx c H0).
  reflexivity.
Qed.

Lemma eu_csl_rr_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_rr_read_value n ts i a value K cursor h allocs ctx c H0).
  reflexivity.
Qed.

Lemma ag_csl_rr_read  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a = Some value ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_rr_read_value n ts i a value K cursor h allocs ctx c H0).
  reflexivity.
Qed.

Lemma eg_csl_rr_read  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a = Some value ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  rewrite (interp_rr_read_value n ts i a value K cursor h allocs ctx c H0).
  reflexivity.
Qed.

Lemma ax_csl_rr_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  apply an_csl_rr_read; assumption.
Qed.

Lemma ex_csl_rr_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  apply en_csl_rr_read; assumption.
Qed.

Lemma af_csl_rr_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  apply au_csl_rr_read; assumption.
Qed.

Lemma ef_csl_rr_read  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some value ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some value))) (Some i) cursor ((h,allocs),(ctx,c))) (w).
Proof.
  intros H0.
  apply eu_csl_rr_read; assumption.
Qed.

Lemma x_csl_rr_read_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_read_missing by assumption.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_rr_read_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_read_missing by assumption.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_rr_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_read_missing by assumption.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_rr_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_read_missing by assumption.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_rr_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_read_missing by assumption.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_rr_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_read_missing by assumption.
  apply eu_stuck.
Qed.

Lemma ag_csl_rr_read_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_read_missing by assumption.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_rr_read_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_read_missing by assumption.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_rr_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply an_csl_rr_read_missing; assumption.
Qed.

Lemma ex_csl_rr_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply en_csl_rr_read_missing; assumption.
Qed.

Lemma af_csl_rr_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply au_csl_rr_read_missing; assumption.
Qed.

Lemma ef_csl_rr_read_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply eu_csl_rr_read_missing; assumption.
Qed.

Lemma x_csl_rr_write  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a <> None ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  (P (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt)).
Proof.
  intros H0.
  rewrite interp_rr_write_present by assumption.
  apply qnext_log_iff; assumption.
Qed.

Lemma u_csl_rr_write  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a <> None ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  (Q (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) (w) \/ (P (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt))).
Proof.
  intros H0.
  rewrite interp_rr_write_present by assumption.
  rewrite quntil_unfold at 1.
  rewrite qnext_log_iff by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
Qed.

Lemma an_csl_rr_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt)).
Proof.
  intros H0.
  rewrite interp_rr_write_present by assumption.
  apply an_log_iff.
Qed.

Lemma en_csl_rr_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt)).
Proof.
  intros H0.
  rewrite interp_rr_write_present by assumption.
  apply en_log_iff.
Qed.

Lemma au_csl_rr_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt))).
Proof.
  intros H0.
  rewrite interp_rr_write_present by assumption.
  apply au_log_iff.
Qed.

Lemma eu_csl_rr_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt))).
Proof.
  intros H0.
  rewrite interp_rr_write_present by assumption.
  apply eu_log_iff.
Qed.

Lemma ag_csl_rr_write  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a <> None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt)).
Proof.
  intros H0.
  rewrite interp_rr_write_present by assumption.
  apply ag_log_iff.
Qed.

Lemma eg_csl_rr_write  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a <> None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt)).
Proof.
  intros H0.
  rewrite interp_rr_write_present by assumption.
  apply eg_log_iff.
Qed.

Lemma ax_csl_rr_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt)).
Proof.
  intros H0.
  apply an_csl_rr_write; assumption.
Qed.

Lemma ex_csl_rr_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt)).
Proof.
  intros H0.
  apply en_csl_rr_write; assumption.
Qed.

Lemma af_csl_rr_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt))).
Proof.
  intros H0.
  apply au_csl_rr_write; assumption.
Qed.

Lemma ef_csl_rr_write  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a <> None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (upd h a value,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor ((upd h a value,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a value,allocs)))) tt))).
Proof.
  intros H0.
  apply eu_csl_rr_write; assumption.
Qed.

Lemma x_csl_rr_write_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_write_missing by assumption.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_rr_write_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_write_missing by assumption.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_rr_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_write_missing by assumption.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_rr_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_write_missing by assumption.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_rr_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_write_missing by assumption.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_rr_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_write_missing by assumption.
  apply eu_stuck.
Qed.

Lemma ag_csl_rr_write_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_write_missing by assumption.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_rr_write_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_write_missing by assumption.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_rr_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply an_csl_rr_write_missing; assumption.
Qed.

Lemma ex_csl_rr_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply en_csl_rr_write_missing; assumption.
Qed.

Lemma af_csl_rr_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply au_csl_rr_write_missing; assumption.
Qed.

Lemma ef_csl_rr_write_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a value (K : option unit -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a value) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply eu_csl_rr_write_missing; assumption.
Qed.

Lemma x_csl_rr_emit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  (P (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) w /\ Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c))) (Obs (Log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat))) tt)).
Proof.
  rewrite interp_rr_emit_log.
  apply qnext_log_iff; assumption.
Qed.

Lemma u_csl_rr_emit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  (Q (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) (w) \/ (P (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) w /\ quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c))) (Obs (Log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat))) tt))).
Proof.
  rewrite interp_rr_emit_log.
  rewrite quntil_unfold at 1.
  rewrite qnext_log_iff by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
Qed.

Lemma en_csl_rr_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c))) (Obs (Log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat))) tt)).
Proof.
  rewrite interp_rr_emit_log.
  apply en_log_iff.
Qed.

Lemma eu_csl_rr_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) (w) \/ (entails (SSig * unit) false phi (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c))) (Obs (Log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat))) tt))).
Proof.
  rewrite interp_rr_emit_log.
  apply eu_log_iff.
Qed.

Lemma eg_csl_rr_emit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c))) (Obs (Log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat))) tt)).
Proof.
  rewrite interp_rr_emit_log.
  apply eg_log_iff.
Qed.

Lemma ax_csl_rr_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c))) (Obs (Log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat))) tt)).
Proof.
  apply an_csl_rr_emit; assumption.
Qed.

Lemma ex_csl_rr_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c))) (Obs (Log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat))) tt)).
Proof.
  apply en_csl_rr_emit; assumption.
Qed.

Lemma af_csl_rr_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c))) (Obs (Log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat))) tt))).
Proof.
  apply au_csl_rr_emit; assumption.
Qed.

Lemma ef_csl_rr_emit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory,(ctx,S c))) (Obs (Log ((inl (CSLEmit (stamp (tag,value) c)) : CSLObs (nat * nat) + nat))) tt))).
Proof.
  apply eu_csl_rr_emit; assumption.
Qed.

Lemma x_csl_rr_yield  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  (P (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  rewrite interp_rr_yield.
  rewrite (interp_schedule_rr_select sh).
  rewrite (qnext_vis_iff q _ _ tt P Q HP HP_live HQ).
  destruct q; cbn.
  - split.
    + intros [Hp Hnext]; split; [exact Hp | exact (Hnext tt)].
    + intros [Hp Hnext]; split; [exact Hp | intros []; exact Hnext].
  - split.
    + intros [Hp [[] Hnext]]; split; assumption.
    + intros [Hp Hnext]; split; [exact Hp | exists tt; exact Hnext].
Qed.

Lemma u_csl_rr_yield  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  (Q (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) (w) \/ (P (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt))).
Proof.
  rewrite interp_rr_yield.
  rewrite (interp_schedule_rr_select sh).
  etransitivity; [apply quntil_unfold|].
  rewrite (qnext_vis_iff q _ _ tt P (quntil q P Q) HP HP_live ltac:(typeclasses eauto)).
  destruct q; cbn.
  - split.
    + intros [Hnow | [Hp Hnext]]; [now left | right; split; [exact Hp | exact (Hnext tt)]].
    + intros [Hnow | [Hp Hnext]]; [now left | right; split; [exact Hp | intros []; exact Hnext]].
  - split.
    + intros [Hnow | [Hp [[] Hnext]]]; [now left | right; split; assumption].
    + intros [Hnow | [Hp Hnext]]; [now left | right; split; [exact Hp | exists tt; exact Hnext]].
Qed.

Lemma en_csl_rr_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  rewrite interp_rr_yield.
  apply en_csl_rr_select.
Qed.

Lemma eu_csl_rr_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt))).
Proof.
  rewrite interp_rr_yield.
  apply eu_csl_rr_select.
Qed.

Lemma eg_csl_rr_yield  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  rewrite interp_rr_yield.
  apply eg_csl_rr_select.
Qed.

Lemma ax_csl_rr_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  apply an_csl_rr_yield; assumption.
Qed.

Lemma ex_csl_rr_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  apply en_csl_rr_yield; assumption.
Qed.

Lemma af_csl_rr_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt))).
Proof.
  apply au_csl_rr_yield; assumption.
Qed.

Lemma ef_csl_rr_yield  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt))).
Proof.
  apply eu_csl_rr_yield; assumption.
Qed.

Lemma x_csl_rr_fork  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_fork.
  reflexivity.
Qed.

Lemma u_csl_rr_fork  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_fork.
  reflexivity.
Qed.

Lemma an_csl_rr_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_fork.
  reflexivity.
Qed.

Lemma en_csl_rr_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_fork.
  reflexivity.
Qed.

Lemma au_csl_rr_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_fork.
  reflexivity.
Qed.

Lemma eu_csl_rr_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_fork.
  reflexivity.
Qed.

Lemma ag_csl_rr_fork  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_fork.
  reflexivity.
Qed.

Lemma eg_csl_rr_fork  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_fork.
  reflexivity.
Qed.

Lemma ax_csl_rr_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_fork; assumption.
Qed.

Lemma ex_csl_rr_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_fork; assumption.
Qed.

Lemma af_csl_rr_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_fork; assumption.
Qed.

Lemma ef_csl_rr_fork  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S (S n)) ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt))) (Some (Fin.FS i)) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_fork; assumption.
Qed.

Lemma x_csl_rr_ret {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_ret.
  reflexivity.
Qed.

Lemma u_csl_rr_ret {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_ret.
  reflexivity.
Qed.

Lemma an_csl_rr_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_ret.
  reflexivity.
Qed.

Lemma en_csl_rr_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_ret.
  reflexivity.
Qed.

Lemma au_csl_rr_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_ret.
  reflexivity.
Qed.

Lemma eu_csl_rr_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_ret.
  reflexivity.
Qed.

Lemma ag_csl_rr_ret {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_ret.
  reflexivity.
Qed.

Lemma eg_csl_rr_ret {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_ret.
  reflexivity.
Qed.

Lemma ax_csl_rr_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_ret; assumption.
Qed.

Lemma ex_csl_rr_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_ret; assumption.
Qed.

Lemma af_csl_rr_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_ret; assumption.
Qed.

Lemma ef_csl_rr_ret {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some x))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_ret; assumption.
Qed.

Lemma x_csl_rr_bind {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_bind.
  reflexivity.
Qed.

Lemma u_csl_rr_bind {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_bind.
  reflexivity.
Qed.

Lemma an_csl_rr_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_bind.
  reflexivity.
Qed.

Lemma en_csl_rr_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_bind.
  reflexivity.
Qed.

Lemma au_csl_rr_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_bind.
  reflexivity.
Qed.

Lemma eu_csl_rr_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_bind.
  reflexivity.
Qed.

Lemma ag_csl_rr_bind {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_bind.
  reflexivity.
Qed.

Lemma eg_csl_rr_bind {A B} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_bind.
  reflexivity.
Qed.

Lemma ax_csl_rr_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_bind; assumption.
Qed.

Lemma ex_csl_rr_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_bind; assumption.
Qed.

Lemma af_csl_rr_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_bind; assumption.
Qed.

Lemma ef_csl_rr_bind {A B} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= fun flow => match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_bind; assumption.
Qed.

Lemma x_csl_rr_alloc_first  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  (P (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_rr_alloc_first n ts i size base K cursor h allocs ctx c H0 H1 H2 H3).
  apply qnext_log_iff; assumption.
Qed.

Lemma u_csl_rr_alloc_first  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  (Q (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (P (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_rr_alloc_first n ts i size base K cursor h allocs ctx c H0 H1 H2 H3).
  rewrite quntil_unfold at 1.
  rewrite qnext_log_iff by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
Qed.

Lemma an_csl_rr_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_rr_alloc_first n ts i size base K cursor h allocs ctx c H0 H1 H2 H3).
  apply an_log_iff.
Qed.

Lemma en_csl_rr_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_rr_alloc_first n ts i size base K cursor h allocs ctx c H0 H1 H2 H3).
  apply en_log_iff.
Qed.

Lemma au_csl_rr_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_rr_alloc_first n ts i size base K cursor h allocs ctx c H0 H1 H2 H3).
  apply au_log_iff.
Qed.

Lemma eu_csl_rr_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_rr_alloc_first n ts i size base K cursor h allocs ctx c H0 H1 H2 H3).
  apply eu_log_iff.
Qed.

Lemma ag_csl_rr_alloc_first  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_rr_alloc_first n ts i size base K cursor h allocs ctx c H0 H1 H2 H3).
  apply ag_log_iff.
Qed.

Lemma eg_csl_rr_alloc_first  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)).
Proof.
  intros H0 H1 H2 H3.
  rewrite (interp_rr_alloc_first n ts i size base K cursor h allocs ctx c H0 H1 H2 H3).
  apply eg_log_iff.
Qed.

Lemma ax_csl_rr_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)).
Proof.
  intros H0 H1 H2 H3.
  apply an_csl_rr_alloc_first; assumption.
Qed.

Lemma ex_csl_rr_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)).
Proof.
  intros H0 H1 H2 H3.
  apply en_csl_rr_alloc_first; assumption.
Qed.

Lemma af_csl_rr_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1 H2 H3.
  apply au_csl_rr_alloc_first; assumption.
Qed.

Lemma ef_csl_rr_alloc_first  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  Nat.lt 0 base ->
  block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1 H2 H3.
  apply eu_csl_rr_alloc_first; assumption.
Qed.

Lemma x_csl_rr_alloc  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  heap_finite h ->
  Nat.lt 0 size ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (P (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (x_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w q P Q HP HP_live HQ H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (x_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w q P Q HP HP_live HQ H1 Base Free First); apply Hall; assumption.
Qed.

Lemma u_csl_rr_alloc  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  heap_finite h ->
  Nat.lt 0 size ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (Q (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (P (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (u_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w q P Q HP HP_live HQ H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (u_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w q P Q HP HP_live HQ H1 Base Free First); apply Hall; assumption.
Qed.

Lemma an_csl_rr_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (an_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi psi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (an_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi psi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma en_csl_rr_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (en_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi psi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (en_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi psi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma au_csl_rr_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) b psi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (au_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi psi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (au_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi psi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma eu_csl_rr_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) b psi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (eu_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi psi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (eu_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi psi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma ag_csl_rr_alloc  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (ag_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (ag_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma eg_csl_rr_alloc  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false phi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1.
  split.
  - intros Hsource base Base Free First.
    rewrite <- (eg_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi H1 Base Free First); exact Hsource.
  - intro Hall.
    destruct (first_fit_exists h size H0 H1) as (base & Base & Free & First).
    rewrite (eg_csl_rr_alloc_first n ts i size base K cursor h allocs ctx c w phi H1 Base Free First); apply Hall; assumption.
Qed.

Lemma ax_csl_rr_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1.
  apply an_csl_rr_alloc; assumption.
Qed.

Lemma ex_csl_rr_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt))).
Proof.
  intros H0 H1.
  apply en_csl_rr_alloc; assumption.
Qed.

Lemma af_csl_rr_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) b psi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)))).
Proof.
  intros H0 H1.
  apply au_csl_rr_alloc; assumption.
Qed.

Lemma ef_csl_rr_alloc  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  heap_finite h ->
  Nat.lt 0 size ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (forall base, Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    (entails (SSig * unit) b psi (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (managed_alloc (h,allocs) base size)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some base))) (Some i) cursor (managed_alloc (h,allocs) base size,(ctx,c))) (Obs (Log (inl (CSLHeap (managed_alloc (h,allocs) base size)))) tt)))).
Proof.
  intros H0 H1.
  apply eu_csl_rr_alloc; assumption.
Qed.

Lemma x_csl_rr_alloc_zero  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  False.
Proof.
  rewrite interp_rr_alloc_zero.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_rr_alloc_zero  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  rewrite interp_rr_alloc_zero.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_rr_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  rewrite interp_rr_alloc_zero.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_rr_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  rewrite interp_rr_alloc_zero.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_rr_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  rewrite interp_rr_alloc_zero.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_rr_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  rewrite interp_rr_alloc_zero.
  apply eu_stuck.
Qed.

Lemma ag_csl_rr_alloc_zero  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  rewrite interp_rr_alloc_zero.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_rr_alloc_zero  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  rewrite interp_rr_alloc_zero.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_rr_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  apply an_csl_rr_alloc_zero; assumption.
Qed.

Lemma ex_csl_rr_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  apply en_csl_rr_alloc_zero; assumption.
Qed.

Lemma af_csl_rr_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  apply au_csl_rr_alloc_zero; assumption.
Qed.

Lemma ef_csl_rr_alloc_zero  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  apply eu_csl_rr_alloc_zero; assumption.
Qed.

Lemma x_csl_rr_alloc_no_space  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  False.
Proof.
  intros H0 H1.
  rewrite interp_rr_alloc_no_space by assumption.
  apply qnext_dead_iff; apply spin_no_ktrans.
Qed.

Lemma u_csl_rr_alloc_no_space  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  Q ((CTree.spin : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0 H1.
  rewrite interp_rr_alloc_no_space by assumption.
  apply quntil_dead_iff; apply spin_no_ktrans.
Qed.

Lemma an_csl_rr_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  rewrite interp_rr_alloc_no_space by assumption.
  rewrite ticl_an; exact (qnext_dead_iff Q_A (CTree.spin : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)) (entails _ false phi) (entails _ b psi) w (spin_no_ktrans w)).
Qed.

Lemma en_csl_rr_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  rewrite interp_rr_alloc_no_space by assumption.
  rewrite ticl_en; exact (qnext_dead_iff Q_E (CTree.spin : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)) (entails _ false phi) (entails _ b psi) w (spin_no_ktrans w)).
Qed.

Lemma au_csl_rr_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((CTree.spin : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0 H1.
  rewrite interp_rr_alloc_no_space by assumption.
  rewrite ticl_au; exact (quntil_dead_iff Q_A (CTree.spin : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)) (entails _ false phi) (entails _ b psi) w (spin_no_ktrans w)).
Qed.

Lemma eu_csl_rr_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((CTree.spin : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0 H1.
  rewrite interp_rr_alloc_no_space by assumption.
  rewrite ticl_eu; exact (quntil_dead_iff Q_E (CTree.spin : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)) (entails _ false phi) (entails _ b psi) w (spin_no_ktrans w)).
Qed.

Lemma ag_csl_rr_alloc_no_space  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  rewrite interp_rr_alloc_no_space by assumption.
  split; [intro H; cdestruct H|contradiction].
  destruct Hs as (u & z & TR); exact (spin_no_ktrans w u z TR).
Qed.

Lemma eg_csl_rr_alloc_no_space  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  rewrite interp_rr_alloc_no_space by assumption.
  split; [intro H; cdestruct H|contradiction].
  exact (spin_no_ktrans w _ _ TR).
Qed.

Lemma ax_csl_rr_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  apply an_csl_rr_alloc_no_space; assumption.
Qed.

Lemma ex_csl_rr_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0 H1.
  apply en_csl_rr_alloc_no_space; assumption.
Qed.

Lemma af_csl_rr_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((CTree.spin : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0 H1.
  apply au_csl_rr_alloc_no_space; assumption.
Qed.

Lemma ef_csl_rr_alloc_no_space  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((CTree.spin : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0 H1.
  apply eu_csl_rr_alloc_no_space; assumption.
Qed.

Lemma x_csl_rr_free  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  managed_free memory base = Some memory' ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  (match base with 0 => qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (P (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt)) end).
Proof.
  intros H0.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply qnext_log_iff; assumption.
Qed.

Lemma u_csl_rr_free  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  managed_free memory base = Some memory' ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  (match base with 0 => quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (Q (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) (w) \/ (P (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt))) end).
Proof.
  intros H0.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - rewrite quntil_unfold at 1.
  rewrite qnext_log_iff by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
Qed.

Lemma an_csl_rr_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false phi (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt)) end).
Proof.
  intros H0.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply an_log_iff.
Qed.

Lemma en_csl_rr_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false phi (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt)) end).
Proof.
  intros H0.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply en_log_iff.
Qed.

Lemma au_csl_rr_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) b psi (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt))) end).
Proof.
  intros H0.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply au_log_iff.
Qed.

Lemma eu_csl_rr_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) b psi (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt))) end).
Proof.
  intros H0.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply eu_log_iff.
Qed.

Lemma ag_csl_rr_free  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false phi (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt)) end).
Proof.
  intros H0.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply ag_log_iff.
Qed.

Lemma eg_csl_rr_free  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false phi (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt)) end).
Proof.
  intros H0.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c H0).
  destruct base.
  - reflexivity.
  - apply eg_log_iff.
Qed.

Lemma ax_csl_rr_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt)) end).
Proof.
  intros H0.
  apply an_csl_rr_free; assumption.
Qed.

Lemma ex_csl_rr_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt)) end).
Proof.
  intros H0.
  apply en_csl_rr_free; assumption.
Qed.

Lemma af_csl_rr_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) b psi (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt))) end).
Proof.
  intros H0.
  apply au_csl_rr_free; assumption.
Qed.

Lemma ef_csl_rr_free  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory memory' : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = Some memory' ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (match base with 0 => entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (w) | S _ => (entails (SSig * unit) b psi (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap memory'));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some tt))) (Some i) cursor (memory',(ctx,c))) (Obs (Log (inl (CSLHeap memory'))) tt))) end).
Proof.
  intros H0.
  apply eu_csl_rr_free; assumption.
Qed.

Lemma x_csl_rr_free_invalid  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  managed_free memory base = None ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_free_invalid by assumption.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_rr_free_invalid  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  managed_free memory base = None ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_free_invalid by assumption.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_rr_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_free_invalid by assumption.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_rr_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_free_invalid by assumption.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_rr_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_free_invalid by assumption.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_rr_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_free_invalid by assumption.
  apply eu_stuck.
Qed.

Lemma ag_csl_rr_free_invalid  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  managed_free memory base = None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_free_invalid by assumption.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_rr_free_invalid  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  managed_free memory base = None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_free_invalid by assumption.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_rr_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply an_csl_rr_free_invalid; assumption.
Qed.

Lemma ex_csl_rr_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply en_csl_rr_free_invalid; assumption.
Qed.

Lemma af_csl_rr_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply au_csl_rr_free_invalid; assumption.
Qed.

Lemma ef_csl_rr_free_invalid  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE Bn) cursor (memory : ManagedHeap) ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  managed_free memory base = None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply eu_csl_rr_free_invalid; assumption.
Qed.

Lemma x_csl_rr_cas  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_cas_exp.
  reflexivity.
Qed.

Lemma u_csl_rr_cas  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_cas_exp.
  reflexivity.
Qed.

Lemma an_csl_rr_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_cas_exp.
  reflexivity.
Qed.

Lemma en_csl_rr_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_cas_exp.
  reflexivity.
Qed.

Lemma au_csl_rr_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_cas_exp.
  reflexivity.
Qed.

Lemma eu_csl_rr_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_cas_exp.
  reflexivity.
Qed.

Lemma ag_csl_rr_cas  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_cas_exp.
  reflexivity.
Qed.

Lemma eg_csl_rr_cas  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_cas_exp.
  reflexivity.
Qed.

Lemma ax_csl_rr_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_cas; assumption.
Qed.

Lemma ex_csl_rr_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_cas; assumption.
Qed.

Lemma af_csl_rr_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_cas; assumption.
Qed.

Lemma ef_csl_rr_cas  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (a expected desired : CExp) (K : option bool -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp a >>= fun addr => denote_exp expected >>= fun old => denote_exp desired >>= fun value => denote_flow (CCAS (CLit addr) (CLit old) (CLit value)) >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_cas; assumption.
Qed.

Lemma x_csl_rr_cas_value  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = Some current ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  (if Nat.eqb current expected then (P (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt)) else qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_rr_cas_value n ts i a expected desired current K cursor h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply qnext_log_iff; assumption.
  - reflexivity.
Qed.

Lemma u_csl_rr_cas_value  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = Some current ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  (if Nat.eqb current expected then (Q (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) (w) \/ (P (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt))) else quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_rr_cas_value n ts i a expected desired current K cursor h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - rewrite quntil_unfold at 1.
  rewrite qnext_log_iff by (first [exact HP | exact HP_live | typeclasses eauto]); reflexivity.
  - reflexivity.
Qed.

Lemma an_csl_rr_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt)) else entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_rr_cas_value n ts i a expected desired current K cursor h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply an_log_iff.
  - reflexivity.
Qed.

Lemma en_csl_rr_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt)) else entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_rr_cas_value n ts i a expected desired current K cursor h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply en_log_iff.
  - reflexivity.
Qed.

Lemma au_csl_rr_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) b psi (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt))) else entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_rr_cas_value n ts i a expected desired current K cursor h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply au_log_iff.
  - reflexivity.
Qed.

Lemma eu_csl_rr_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) b psi (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt))) else entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_rr_cas_value n ts i a expected desired current K cursor h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply eu_log_iff.
  - reflexivity.
Qed.

Lemma ag_csl_rr_cas_value  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a = Some current ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt)) else entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_rr_cas_value n ts i a expected desired current K cursor h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply ag_log_iff.
  - reflexivity.
Qed.

Lemma eg_csl_rr_cas_value  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a = Some current ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false phi (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt)) else entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  rewrite (interp_rr_cas_value n ts i a expected desired current K cursor h allocs ctx c H0).
  destruct (Nat.eqb current expected).
  - apply eg_log_iff.
  - reflexivity.
Qed.

Lemma ax_csl_rr_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt)) else entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  apply an_csl_rr_cas_value; assumption.
Qed.

Lemma ex_csl_rr_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt)) else entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  apply en_csl_rr_cas_value; assumption.
Qed.

Lemma af_csl_rr_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) b psi (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt))) else entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  apply au_csl_rr_cas_value; assumption.
Qed.

Lemma ef_csl_rr_cas_value  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = Some current ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  (if Nat.eqb current expected then (entails (SSig * unit) b psi (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (log (inl (CSLHeap (upd h a desired,allocs)));; (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some true))) (Some i) cursor ((upd h a desired,allocs),(ctx,c))) (Obs (Log (inl (CSLHeap (upd h a desired,allocs)))) tt))) else entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K (Some false))) (Some i) cursor ((h,allocs),(ctx,c))) (w)).
Proof.
  intros H0.
  apply eu_csl_rr_cas_value; assumption.
Qed.

Lemma x_csl_rr_cas_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_cas_missing by assumption.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_rr_cas_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  h a = None ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_cas_missing by assumption.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_rr_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_cas_missing by assumption.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_rr_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_cas_missing by assumption.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_rr_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_cas_missing by assumption.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_rr_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_cas_missing by assumption.
  apply eu_stuck.
Qed.

Lemma ag_csl_rr_cas_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_cas_missing by assumption.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_rr_cas_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  h a = None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_cas_missing by assumption.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_rr_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply an_csl_rr_cas_missing; assumption.
Qed.

Lemma ex_csl_rr_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply en_csl_rr_cas_missing; assumption.
Qed.

Lemma af_csl_rr_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply au_csl_rr_cas_missing; assumption.
Qed.

Lemma ef_csl_rr_cas_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE Bn) cursor h allocs ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  h a = None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CCAS (CLit a) (CLit expected) (CLit desired)) >>= K)) (Some i) cursor ((h,allocs),(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply eu_csl_rr_cas_missing; assumption.
Qed.

Lemma x_csl_rr_eval  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_eval.
  reflexivity.
Qed.

Lemma u_csl_rr_eval  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_eval.
  reflexivity.
Qed.

Lemma an_csl_rr_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_eval.
  reflexivity.
Qed.

Lemma en_csl_rr_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_eval.
  reflexivity.
Qed.

Lemma au_csl_rr_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_eval.
  reflexivity.
Qed.

Lemma eu_csl_rr_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_eval.
  reflexivity.
Qed.

Lemma ag_csl_rr_eval  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_eval.
  reflexivity.
Qed.

Lemma eg_csl_rr_eval  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_eval.
  reflexivity.
Qed.

Lemma ax_csl_rr_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_eval; assumption.
Qed.

Lemma ex_csl_rr_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_eval; assumption.
Qed.

Lemma af_csl_rr_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_eval; assumption.
Qed.

Lemma ef_csl_rr_eval  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (e : CExp) (K : option nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEval e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => K (Some value))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_eval; assumption.
Qed.

Lemma x_csl_rr_assign  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_assign.
  reflexivity.
Qed.

Lemma u_csl_rr_assign  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_assign.
  reflexivity.
Qed.

Lemma an_csl_rr_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_assign.
  reflexivity.
Qed.

Lemma en_csl_rr_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_assign.
  reflexivity.
Qed.

Lemma au_csl_rr_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_assign.
  reflexivity.
Qed.

Lemma eu_csl_rr_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_assign.
  reflexivity.
Qed.

Lemma ag_csl_rr_assign  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_assign.
  reflexivity.
Qed.

Lemma eg_csl_rr_assign  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_assign.
  reflexivity.
Qed.

Lemma ax_csl_rr_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_assign; assumption.
Qed.

Lemma ex_csl_rr_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_assign; assumption.
Qed.

Lemma af_csl_rr_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_assign; assumption.
Qed.

Lemma ef_csl_rr_assign  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (e : CExp) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp e >>= fun value => source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_assign; assumption.
Qed.

Lemma x_csl_rr_if {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_if.
  reflexivity.
Qed.

Lemma u_csl_rr_if {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_if.
  reflexivity.
Qed.

Lemma an_csl_rr_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_if.
  reflexivity.
Qed.

Lemma en_csl_rr_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_if.
  reflexivity.
Qed.

Lemma au_csl_rr_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_if.
  reflexivity.
Qed.

Lemma eu_csl_rr_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_if.
  reflexivity.
Qed.

Lemma ag_csl_rr_if {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_if.
  reflexivity.
Qed.

Lemma eg_csl_rr_if {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_if.
  reflexivity.
Qed.

Lemma ax_csl_rr_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_if; assumption.
Qed.

Lemma ex_csl_rr_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_if; assumption.
Qed.

Lemma af_csl_rr_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_if; assumption.
Qed.

Lemma ef_csl_rr_if {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (yes no : CProg A) (K : option A -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CIf test yes no) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow yes >>= K else denote_flow no >>= K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_if; assumption.
Qed.

Lemma x_csl_rr_until_none_unfold {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_until_none.
  reflexivity.
Qed.

Lemma u_csl_rr_until_none_unfold {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_until_none.
  reflexivity.
Qed.

Lemma an_csl_rr_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_until_none.
  reflexivity.
Qed.

Lemma en_csl_rr_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_until_none.
  reflexivity.
Qed.

Lemma au_csl_rr_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_until_none.
  reflexivity.
Qed.

Lemma eu_csl_rr_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_until_none.
  reflexivity.
Qed.

Lemma ag_csl_rr_until_none_unfold {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_until_none.
  reflexivity.
Qed.

Lemma eg_csl_rr_until_none_unfold {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_until_none.
  reflexivity.
Qed.

Lemma ax_csl_rr_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_until_none_unfold; assumption.
Qed.

Lemma ex_csl_rr_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_until_none_unfold; assumption.
Qed.

Lemma af_csl_rr_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_until_none_unfold; assumption.
Qed.

Lemma ef_csl_rr_until_none_unfold {A} {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_until_none_unfold; assumption.
Qed.

Lemma x_csl_rr_while_unfold  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_while_unfold.
  reflexivity.
Qed.

Lemma u_csl_rr_while_unfold  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_while_unfold.
  reflexivity.
Qed.

Lemma an_csl_rr_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_while_unfold.
  reflexivity.
Qed.

Lemma en_csl_rr_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_while_unfold.
  reflexivity.
Qed.

Lemma au_csl_rr_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_while_unfold.
  reflexivity.
Qed.

Lemma eu_csl_rr_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_while_unfold.
  reflexivity.
Qed.

Lemma ag_csl_rr_while_unfold  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_while_unfold.
  reflexivity.
Qed.

Lemma eg_csl_rr_while_unfold  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_while_unfold.
  reflexivity.
Qed.

Lemma ax_csl_rr_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_while_unfold; assumption.
Qed.

Lemma ex_csl_rr_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_while_unfold; assumption.
Qed.

Lemma af_csl_rr_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_while_unfold; assumption.
Qed.

Lemma ef_csl_rr_while_unfold  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (test : CExp) (body : CProg unit) (K : option unit -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWhile test body) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp test >>= fun value => if CoCSLSyntax.is_true value then denote_flow body >>= fun flow => match flow with None => K None | Some _ => Guard (denote_flow (CWhile test body) >>= K) end else K (Some tt))) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_while_unfold; assumption.
Qed.

Lemma x_csl_rr_exp_lit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_lit.
  reflexivity.
Qed.

Lemma u_csl_rr_exp_lit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_lit.
  reflexivity.
Qed.

Lemma an_csl_rr_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_lit.
  reflexivity.
Qed.

Lemma en_csl_rr_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_lit.
  reflexivity.
Qed.

Lemma au_csl_rr_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_lit.
  reflexivity.
Qed.

Lemma eu_csl_rr_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_lit.
  reflexivity.
Qed.

Lemma ag_csl_rr_exp_lit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_lit.
  reflexivity.
Qed.

Lemma eg_csl_rr_exp_lit  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_lit.
  reflexivity.
Qed.

Lemma ax_csl_rr_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_exp_lit; assumption.
Qed.

Lemma ex_csl_rr_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_exp_lit; assumption.
Qed.

Lemma af_csl_rr_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_exp_lit; assumption.
Qed.

Lemma ef_csl_rr_exp_lit  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  value (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit value) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_exp_lit; assumption.
Qed.

Lemma x_csl_rr_exp_var  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  lookup name ctx = Some value ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  (P (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ Q (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  intros H0.
  rewrite (interp_rr_var n ts i name value K cursor (memory,(ctx,c)) H0).
  rewrite (interp_schedule_rr_select sh).
  rewrite (qnext_vis_iff q _ _ tt P Q HP HP_live HQ).
  destruct q; cbn.
  - split.
    + intros [Hp Hnext]; split; [exact Hp | exact (Hnext tt)].
    + intros [Hp Hnext]; split; [exact Hp | intros []; exact Hnext].
  - split.
    + intros [Hp [[] Hnext]]; split; assumption.
    + intros [Hp Hnext]; split; [exact Hp | exists tt; exact Hnext].
Qed.

Lemma u_csl_rr_exp_var  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  lookup name ctx = Some value ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  (Q (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) (w) \/ (P (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt))).
Proof.
  intros H0.
  rewrite (interp_rr_var n ts i name value K cursor (memory,(ctx,c)) H0).
  rewrite (interp_schedule_rr_select sh).
  etransitivity; [apply quntil_unfold|].
  rewrite (qnext_vis_iff q _ _ tt P (quntil q P Q) HP HP_live ltac:(typeclasses eauto)).
  destruct q; cbn.
  - split.
    + intros [Hnow | [Hp Hnext]]; [now left | right; split; [exact Hp | exact (Hnext tt)]].
    + intros [Hnow | [Hp Hnext]]; [now left | right; split; [exact Hp | intros []; exact Hnext]].
  - split.
    + intros [Hnow | [Hp [[] Hnext]]]; [now left | right; split; assumption].
    + intros [Hnow | [Hp Hnext]]; [now left | right; split; [exact Hp | exists tt; exact Hnext]].
Qed.

Lemma an_csl_rr_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  intros H0.
  rewrite (interp_rr_var n ts i name value K cursor (memory,(ctx,c)) H0).
  apply an_csl_rr_select.
Qed.

Lemma en_csl_rr_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  intros H0.
  rewrite (interp_rr_var n ts i name value K cursor (memory,(ctx,c)) H0).
  apply en_csl_rr_select.
Qed.

Lemma au_csl_rr_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt))).
Proof.
  intros H0.
  rewrite (interp_rr_var n ts i name value K cursor (memory,(ctx,c)) H0).
  apply au_csl_rr_select.
Qed.

Lemma eu_csl_rr_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false phi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt))).
Proof.
  intros H0.
  rewrite (interp_rr_var n ts i name value K cursor (memory,(ctx,c)) H0).
  apply eu_csl_rr_select.
Qed.

Lemma ag_csl_rr_exp_var  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  lookup name ctx = Some value ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  intros H0.
  rewrite (interp_rr_var n ts i name value K cursor (memory,(ctx,c)) H0).
  apply ag_csl_rr_select.
Qed.

Lemma eg_csl_rr_exp_var  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  lookup name ctx = Some value ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false phi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  intros H0.
  rewrite (interp_rr_var n ts i name value K cursor (memory,(ctx,c)) H0).
  apply eg_csl_rr_select.
Qed.

Lemma ax_csl_rr_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  intros H0.
  apply an_csl_rr_exp_var; assumption.
Qed.

Lemma ex_csl_rr_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) false (CNow (fun _ => True)) (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b psi (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt)).
Proof.
  intros H0.
  apply en_csl_rr_exp_var; assumption.
Qed.

Lemma af_csl_rr_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt))).
Proof.
  intros H0.
  apply au_csl_rr_exp_var; assumption.
Qed.

Lemma ef_csl_rr_exp_var  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = Some value ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  (entails (SSig * unit) b psi (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) (w) \/ (entails (SSig * unit) false (CNow (fun _ => True)) (Vis (Log (inr (slot_index (rr_pick n cursor)))) (fun _ => interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c)))) w /\ entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (K value)) (Some (rr_pick n cursor)) (S cursor) (memory,(ctx,c))) (Obs (Log (inr (slot_index (rr_pick n cursor)))) tt))).
Proof.
  intros H0.
  apply eu_csl_rr_exp_var; assumption.
Qed.

Lemma x_csl_rr_exp_var_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  lookup name ctx = None ->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_var_missing by assumption.
  apply qnext_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma u_csl_rr_exp_var_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  lookup name ctx = None ->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  Q ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_var_missing by assumption.
  apply quntil_dead_iff; intros u z; apply ktrans_stuck.
Qed.

Lemma an_csl_rr_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_var_missing by assumption.
  split; [apply an_stuck|contradiction].
Qed.

Lemma en_csl_rr_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_var_missing by assumption.
  split; [apply en_stuck|contradiction].
Qed.

Lemma au_csl_rr_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_var_missing by assumption.
  symmetry; apply au_stuck.
Qed.

Lemma eu_csl_rr_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  rewrite interp_rr_var_missing by assumption.
  apply eu_stuck.
Qed.

Lemma ag_csl_rr_exp_var_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  lookup name ctx = None ->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_var_missing by assumption.
  split; [apply ag_stuck|contradiction].
Qed.

Lemma eg_csl_rr_exp_var_missing  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  lookup name ctx = None ->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  rewrite interp_rr_var_missing by assumption.
  split; [apply eg_stuck|contradiction].
Qed.

Lemma ax_csl_rr_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply an_csl_rr_exp_var_missing; assumption.
Qed.

Lemma ex_csl_rr_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  False.
Proof.
  intros H0.
  apply en_csl_rr_exp_var_missing; assumption.
Qed.

Lemma af_csl_rr_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply au_csl_rr_exp_var_missing; assumption.
Qed.

Lemma ef_csl_rr_exp_var_missing  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  lookup name ctx = None ->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b psi ((Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit))) (w).
Proof.
  intros H0.
  apply eu_csl_rr_exp_var_missing; assumption.
Qed.

Lemma x_csl_rr_exp_plus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_plus.
  reflexivity.
Qed.

Lemma u_csl_rr_exp_plus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_plus.
  reflexivity.
Qed.

Lemma an_csl_rr_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_plus.
  reflexivity.
Qed.

Lemma en_csl_rr_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_plus.
  reflexivity.
Qed.

Lemma au_csl_rr_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_plus.
  reflexivity.
Qed.

Lemma eu_csl_rr_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_plus.
  reflexivity.
Qed.

Lemma ag_csl_rr_exp_plus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_plus.
  reflexivity.
Qed.

Lemma eg_csl_rr_exp_plus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_plus.
  reflexivity.
Qed.

Lemma ax_csl_rr_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_exp_plus; assumption.
Qed.

Lemma ex_csl_rr_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_exp_plus; assumption.
Qed.

Lemma af_csl_rr_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_exp_plus; assumption.
Qed.

Lemma ef_csl_rr_exp_plus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CPlus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x + y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_exp_plus; assumption.
Qed.

Lemma x_csl_rr_exp_minus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_minus.
  reflexivity.
Qed.

Lemma u_csl_rr_exp_minus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_minus.
  reflexivity.
Qed.

Lemma an_csl_rr_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_minus.
  reflexivity.
Qed.

Lemma en_csl_rr_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_minus.
  reflexivity.
Qed.

Lemma au_csl_rr_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_minus.
  reflexivity.
Qed.

Lemma eu_csl_rr_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_minus.
  reflexivity.
Qed.

Lemma ag_csl_rr_exp_minus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_minus.
  reflexivity.
Qed.

Lemma eg_csl_rr_exp_minus  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_minus.
  reflexivity.
Qed.

Lemma ax_csl_rr_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_exp_minus; assumption.
Qed.

Lemma ex_csl_rr_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_exp_minus; assumption.
Qed.

Lemma af_csl_rr_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_exp_minus; assumption.
Qed.

Lemma ef_csl_rr_exp_minus  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMinus ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x - y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_exp_minus; assumption.
Qed.

Lemma x_csl_rr_exp_mult  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_mult.
  reflexivity.
Qed.

Lemma u_csl_rr_exp_mult  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_mult.
  reflexivity.
Qed.

Lemma an_csl_rr_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_mult.
  reflexivity.
Qed.

Lemma en_csl_rr_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_mult.
  reflexivity.
Qed.

Lemma au_csl_rr_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_mult.
  reflexivity.
Qed.

Lemma eu_csl_rr_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E phi psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_mult.
  reflexivity.
Qed.

Lemma ag_csl_rr_exp_mult  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_A phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_mult.
  reflexivity.
Qed.

Lemma eg_csl_rr_exp_mult  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (phi : ticll (writerE (CSLObs (nat * nat) + nat))) :
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) false (Cg Q_E phi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_exp_mult.
  reflexivity.
Qed.

Lemma ax_csl_rr_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply an_csl_rr_exp_mult; assumption.
Qed.

Lemma ex_csl_rr_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cx Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply en_csl_rr_exp_mult; assumption.
Qed.

Lemma af_csl_rr_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_A (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply au_csl_rr_exp_mult; assumption.
Qed.

Lemma ef_csl_rr_exp_mult  {b : bool} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ea eb : CExp) (K : nat -> thread sE Bn) cursor memory ctx c w
  (psi : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CMult ea eb) >>= K)) (Some i) cursor (memory,(ctx,c))) (w) <->
  entails (SSig * unit) b (Cu Q_E (CNow (fun _ => True)) psi) (interp_schedule_rr sh (S n) (ts @ i := (denote_exp ea >>= fun x => denote_exp eb >>= fun y => K (x * y)%nat)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  apply eu_csl_rr_exp_mult; assumption.
Qed.

Lemma x_csl_rr_guard  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (t : thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (Guard t)) (Some i) cursor (memory,(ctx,c))) w <->
  qnext q P Q (interp_schedule_rr sh (S n) (ts @ i := (t)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_guard.
  reflexivity.
Qed.

Lemma u_csl_rr_guard  n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (t : thread sE Bn) cursor memory ctx c w
  (q : ticlq)
  (P Q : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit) -> WorldW (CSLObs (nat * nat) + nat) -> Prop)
  (HP : Proper (sbisim eq ==> eq ==> iff) P)
  (HP_live : forall t w, P t w -> not_done w)
  (HQ : Proper (sbisim eq ==> eq ==> iff) Q) :
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (Guard t)) (Some i) cursor (memory,(ctx,c))) w <->
  quntil q P Q (interp_schedule_rr sh (S n) (ts @ i := (t)) (Some i) cursor (memory,(ctx,c))) (w).
Proof.
  rewrite interp_rr_source_guard.
  reflexivity.
Qed.


(** ** Source loops: actual observations sustain AG; guard-only divergence does not *)

Lemma run_nd_emit_loop_ag tag value memory ctx c w :
  not_done w ->
  <( {run_nd (CUntilNone (CBind (CEmit tag value)
    (fun _ => CRet (Some tt : option unit)))) (memory,(ctx,c))}, {w} |=L AG ⊤ )>.
Proof.
  revert c w; coinduction R CIH; intros c w Hw.
  unfold run_nd, run_nd_pool, csl_pool, denote.
  change (anc (entails (SSig * unit) false <( ⊤ )>) (elem R)
    (interp_schedule_nd sh 1
      (([Ret tt] : pool sE Bn 1) @ Fin.F1 :=
        (denote_flow
          (CUntilNone
            (CBind (CEmit tag value) (fun _ => CRet (Some tt : option unit))))
          >>= fun _ => Ret tt))
      (Some Fin.F1) (memory,(ctx,c))) w).
  rewrite interp_nd_source_until_none, interp_nd_source_bind,
    interp_nd_source_emit_log.
  unfold log, CTree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  split; [apply ticl_now; split; [exact I | exact Hw] |].
  split.
  - apply can_step_vis; [exact tt | exact Hw].
  - intros t' w' Htr.
    apply ktrans_vis in Htr as ([] & -> & Heq & Hnd).
    rewrite <- Heq.
    rewrite interp_nd_source_ret.
    erewrite (interp_schedule_nd_guard sh) by reflexivity.
    cbn [Vector.replace].
    apply CIH.
    constructor.
Qed.

Lemma run_rr_emit_loop_ag tag value memory ctx c w :
  not_done w ->
  <( {run_rr (CUntilNone (CBind (CEmit tag value)
    (fun _ => CRet (Some tt : option unit)))) (memory,(ctx,c))}, {w} |=L AG ⊤ )>.
Proof.
  revert c w; coinduction R CIH; intros c w Hw.
  unfold run_rr, run_rr_pool, csl_pool, denote.
  change (anc (entails (SSig * unit) false <( ⊤ )>) (elem R)
    (interp_schedule_rr sh 1
      (([Ret tt] : pool sE Bn 1) @ Fin.F1 :=
        (denote_flow
          (CUntilNone
            (CBind (CEmit tag value) (fun _ => CRet (Some tt : option unit))))
          >>= fun _ => Ret tt))
      (Some Fin.F1) 0 (memory,(ctx,c))) w).
  rewrite interp_rr_until_none, interp_rr_bind, interp_rr_emit_log.
  unfold log, CTree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  split; [apply ticl_now; split; [exact I | exact Hw] |].
  split.
  - apply can_step_vis; [exact tt | exact Hw].
  - intros t' w' Htr.
    apply ktrans_vis in Htr as ([] & -> & Heq & Hnd).
    rewrite <- Heq.
    rewrite interp_rr_ret.
    erewrite interp_schedule_fair_guard by reflexivity.
    cbn [Vector.replace].
    apply CIH.
    constructor.
Qed.


(** The silent loop starts focused, so the whole run is raw-equivalent to its
    own guard and hence to [spin]; no scheduler tau is erased. *)
Lemma run_nd_silent_loop_no_ag (s : SSig) w :
  ~ <( {run_nd (CUntilNone (CRet (Some tt : option unit))) s}, {w} |=L AG ⊤ )>.
Proof.
  set (p := CUntilNone (CRet (Some tt : option unit))).
  assert (Hraw : denote p ≅ Guard (denote p)).
  { unfold p, denote.
    etransitivity; [apply source_raw_until |].
    etransitivity; [apply source_raw_ret |].
    reflexivity. }
  assert (Hguard : run_nd p s ≅ Guard (run_nd p s)).
  { rewrite run_nd_unfold.
    etransitivity.
    - apply (interp_schedule_nd_equ sh 1 _ [Guard (denote p)]).
      apply cons_pool_equ; [exact Hraw | apply pool_equ_refl].
    - unfold interp_schedule_nd.
      rewrite (ctree_eta (schedule 1 _ (Some Fin.F1))).
      rewrite (schedule_focused_guard 0 [Guard (denote p)] Fin.F1 (denote p) eq_refl).
      rewrite project_scheduled_guard, interp_state_guard.
      reflexivity. }
  exact (guard_fixed_no_ag _ _ _ Hguard).
Qed.

Lemma run_rr_silent_loop_no_ag (s : SSig) w :
  ~ <( {run_rr (CUntilNone (CRet (Some tt : option unit))) s}, {w} |=L AG ⊤ )>.
Proof.
  set (p := CUntilNone (CRet (Some tt : option unit))).
  assert (Hraw : denote p ≅ Guard (denote p)).
  { unfold p, denote.
    etransitivity; [apply source_raw_until |].
    etransitivity; [apply source_raw_ret |].
    reflexivity. }
  assert (Hguard : run_rr p s ≅ Guard (run_rr p s)).
  { rewrite run_rr_unfold.
    etransitivity.
    - apply (interp_schedule_fair_equ rr_scheduler sh 1 _ [Guard (denote p)]).
      apply cons_pool_equ; [exact Hraw | apply pool_equ_refl].
    - rewrite (interp_schedule_fair_guard_exact rr_scheduler sh 0 [Guard (denote p)] Fin.F1 (denote p) 0 s eq_refl).
      reflexivity. }
  exact (guard_fixed_no_ag _ _ _ Hguard).
Qed.

(** ** Yield-language structural surface

    The Yield-style expression and control fragment of [CProg] is reasoned
    about through three views, all built from the generic eraser and state
    interpreter:

    - [scheduled_visible]: the scheduled program with scheduler [Scheduled]
      observations and user effects visible;
    - [instr_exp_erased]/[instr_flow_erased]: a standalone erased thread run
      through [sh], exposing the outer option flow;
    - [run_nd]: the erased nondeterministic singleton schedule. *)

Definition scheduled_visible (p : CProg unit) : completed sE Bn :=
  schedule 1 [denote p]%vector (Some Fin.F1).

Definition instr_exp_erased (e : CExp) (s : SSig)
  : ctreeW (CSLObs (nat * nat)) Bn (SSig * nat) :=
  interp_state sh (interp_thread (denote_exp e)) s.

Definition instr_flow_erased {A} (p : CProg A) (s : SSig)
  : ctreeW (CSLObs (nat * nat)) Bn (SSig * option A) :=
  interp_state sh (interp_thread (denote_flow p)) s.

(** *** Constructor unfold equations *)

Lemma denote_exp_cvar name :
  denote_exp (CVar name) =
    (ctx <- source_get;;
     match lookup name ctx with
     | Some value => source_yield;; Ret value
     | None => Stuck
     end).
Proof. reflexivity. Qed.

Lemma denote_exp_clit n : denote_exp (CLit n) = Ret n.
Proof. reflexivity. Qed.

Lemma denote_exp_cplus a b :
  denote_exp (CPlus a b) =
    (x <- denote_exp a;; y <- denote_exp b;; Ret (x + y)%nat).
Proof. reflexivity. Qed.

Lemma denote_exp_cminus a b :
  denote_exp (CMinus a b) =
    (x <- denote_exp a;; y <- denote_exp b;; Ret (x - y)%nat).
Proof. reflexivity. Qed.

Lemma denote_exp_cmult a b :
  denote_exp (CMult a b) =
    (x <- denote_exp a;; y <- denote_exp b;; Ret (x * y)%nat).
Proof. reflexivity. Qed.

Lemma denote_unfold (p : CProg unit) :
  denote p = (_ <- denote_flow p;; Ret tt).
Proof. reflexivity. Qed.

Lemma denote_flow_cassign name e :
  denote_flow (CAssign name e) =
    (value <- denote_exp e;;
     ctx <- source_get;;
     source_put (add name value ctx);;
     Ret (Some tt)).
Proof. reflexivity. Qed.

Lemma denote_flow_cbind_unit (a b : CProg unit) :
  denote_flow (CBind a (fun _ => b)) =
    (flow <- denote_flow a;;
     match flow with
     | None => Ret None
     | Some _ => denote_flow b
     end).
Proof. reflexivity. Qed.

Lemma denote_flow_cif {A} test (yes no : CProg A) :
  denote_flow (CIf test yes no) =
    (value <- denote_exp test;;
     if CoCSLSyntax.is_true value then denote_flow yes else denote_flow no).
Proof. reflexivity. Qed.

Lemma denote_flow_cret_unit : denote_flow (CRet tt) = Ret (Some tt).
Proof. reflexivity. Qed.

Lemma denote_flow_cyield : denote_flow CYield = (source_yield;; Ret (Some tt)).
Proof. reflexivity. Qed.

Lemma denote_flow_bind_equ {A B} (p q : CProg A)
  (next next' : A -> CProg B) :
  denote_flow p ≅ denote_flow q ->
  (forall a, denote_flow (next a) ≅ denote_flow (next' a)) ->
  denote_flow (CBind p next) ≅ denote_flow (CBind q next').
Proof.
  intros Hp Hnext.
  cbn [denote_flow].
  apply equ_clo_bind with (S:=eq); [exact Hp|].
  intros [a|] y <-; [apply Hnext|reflexivity].
Qed.

Lemma denote_flow_fork_equ (p q : CProg unit) :
  denote_flow p ≅ denote_flow q ->
  denote_flow (CFork p) ≅ denote_flow (CFork q).
Proof.
  intro H; cbn [denote_flow].
  apply equ_clo_bind_eq; intros []; [|reflexivity].
  apply equ_clo_bind with (S:=eq); [exact H|intros x y <-; reflexivity].
Qed.

Lemma denote_equ (p q : CProg unit) :
  denote_flow p ≅ denote_flow q -> denote p ≅ denote q.
Proof.
  intro H; unfold denote; apply equ_clo_bind with (S:=eq);
    [exact H|intros x y <-; reflexivity].
Qed.

(** *** Startup normalizations used by the singleton rules *)

Local Lemma source_yield_bind {X} (k : unit -> ctree CEff Bn X) :
  (source_yield >>= k) ≅ Vis (inl1 Yield) k.
Proof.
  unfold source_yield; rewrite bind_vis.
  apply vis_equ_node; intros []; apply bind_ret_l.
Qed.

Local Lemma denote_ret_unit : denote (CRet tt) ≅ Ret tt.
Proof. unfold denote; cbn [denote_flow]; rewrite !bind_ret_l; reflexivity. Qed.

Local Lemma denote_yield_vis :
  denote CYield ≅ Vis (inl1 Yield : CEff unit) (fun _ : unit => Ret tt).
Proof.
  unfold denote; cbn [denote_flow]; unfold source_yield.
  rewrite bind_bind, bind_vis.
  apply vis_equ_node; intros []; rewrite !bind_ret_l; reflexivity.
Qed.

Lemma denote_assign_lit name n :
  denote (CAssign name (CLit n)) ≅
  (source_get >>= fun ctx => source_put (add name n ctx) >>= fun _ => Ret tt).
Proof.
  unfold denote; cbn [denote_flow denote_exp].
  rewrite bind_bind, bind_ret_l, bind_bind.
  apply equ_clo_bind_eq; intro ctx.
  rewrite bind_bind.
  apply equ_clo_bind_eq; intros [].
  rewrite bind_ret_l; reflexivity.
Qed.

(** *** Expression rules *)

Lemma axr_csl_exp_lit : forall n n' s s' w w',
    n = n' ->
    s = s' ->
    w = w' ->
    not_done w ->
    <( {instr_exp_erased (CLit n) s}, w |=R ret= {(s', n')} w' )>.
Proof.
  intros; subst.
  unfold instr_exp_erased; cbn [denote_exp].
  rewrite interp_state_thread_ret; apply ret_ret; [assumption | split; reflexivity].
Qed.

Lemma axr_csl_exp_var_some : forall name value s s' w w',
    lookup name (csl_context s) = Some value ->
    s = s' ->
    w = w' ->
    not_done w ->
    <( {instr_exp_erased (CVar name) s}, w |=R ret= {(s', value)} w' )>.
Proof.
  intros name value s s' w w' Hlookup Hs Hw Hnd; subst.
  unfold instr_exp_erased; cbn [denote_exp].
  rewrite interp_thread_get_ctx, Hlookup, source_yield_bind.
  rewrite interp_state_thread_yield.
  rewrite interp_state_thread_ret; apply ret_ret; [assumption | split; reflexivity].
Qed.

Lemma axr_csl_exp_plus : forall a b x y value s s' w w',
    <( {instr_exp_erased a s}, w |=R ret= {(s, x)} w )> ->
    <( {instr_exp_erased b s}, w |=R ret= {(s, y)} w )> ->
    value = (x + y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <( {instr_exp_erased (CPlus a b) s}, w |=R ret= {(s', value)} w' )>.
Proof.
  intros a b x y value s s' w w' Ha Hb Hvalue Hs Hw Hnd; subst.
  unfold instr_exp_erased in *; cbn [denote_exp].
  apply ret_sbisim in Ha as (ra & [Hra _] & Ha); subst ra.
  apply ret_sbisim in Hb as (rb & [Hrb _] & Hb); subst rb.
  rewrite interp_state_thread_bind, Ha, bind_ret_l; cbn [fst snd].
  rewrite interp_state_thread_bind, Hb, bind_ret_l; cbn [fst snd].
  rewrite interp_state_thread_ret; apply ret_ret; [assumption | split; reflexivity].
Qed.

Lemma axr_csl_exp_minus : forall a b x y value s s' w w',
    <( {instr_exp_erased a s}, w |=R ret= {(s, x)} w )> ->
    <( {instr_exp_erased b s}, w |=R ret= {(s, y)} w )> ->
    value = (x - y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <( {instr_exp_erased (CMinus a b) s}, w |=R ret= {(s', value)} w' )>.
Proof.
  intros a b x y value s s' w w' Ha Hb Hvalue Hs Hw Hnd; subst.
  unfold instr_exp_erased in *; cbn [denote_exp].
  apply ret_sbisim in Ha as (ra & [Hra _] & Ha); subst ra.
  apply ret_sbisim in Hb as (rb & [Hrb _] & Hb); subst rb.
  rewrite interp_state_thread_bind, Ha, bind_ret_l; cbn [fst snd].
  rewrite interp_state_thread_bind, Hb, bind_ret_l; cbn [fst snd].
  rewrite interp_state_thread_ret; apply ret_ret; [assumption | split; reflexivity].
Qed.

Lemma axr_csl_exp_mult : forall a b x y value s s' w w',
    <( {instr_exp_erased a s}, w |=R ret= {(s, x)} w )> ->
    <( {instr_exp_erased b s}, w |=R ret= {(s, y)} w )> ->
    value = (x * y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <( {instr_exp_erased (CMult a b) s}, w |=R ret= {(s', value)} w' )>.
Proof.
  intros a b x y value s s' w w' Ha Hb Hvalue Hs Hw Hnd; subst.
  unfold instr_exp_erased in *; cbn [denote_exp].
  apply ret_sbisim in Ha as (ra & [Hra _] & Ha); subst ra.
  apply ret_sbisim in Hb as (rb & [Hrb _] & Hb); subst rb.
  rewrite interp_state_thread_bind, Ha, bind_ret_l; cbn [fst snd].
  rewrite interp_state_thread_bind, Hb, bind_ret_l; cbn [fst snd].
  rewrite interp_state_thread_ret; apply ret_ret; [assumption | split; reflexivity].
Qed.

Lemma axr_csl_exp_plus_lit_lit : forall x y value s s' w w',
    value = (x + y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <( {instr_exp_erased (CPlus (CLit x) (CLit y)) s},
       w |=R ret= {(s', value)} w' )>.
Proof.
  intros; subst.
  eapply axr_csl_exp_plus; eauto; apply axr_csl_exp_lit; auto.
Qed.

Lemma axr_csl_exp_minus_lit_lit : forall x y value s s' w w',
    value = (x - y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <( {instr_exp_erased (CMinus (CLit x) (CLit y)) s},
       w |=R ret= {(s', value)} w' )>.
Proof.
  intros; subst.
  eapply axr_csl_exp_minus; eauto; apply axr_csl_exp_lit; auto.
Qed.

Lemma axr_csl_exp_mult_lit_lit : forall x y value s s' w w',
    value = (x * y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <( {instr_exp_erased (CMult (CLit x) (CLit y)) s},
       w |=R ret= {(s', value)} w' )>.
Proof.
  intros; subst.
  eapply axr_csl_exp_mult; eauto; apply axr_csl_exp_lit; auto.
Qed.

(** *** Scheduled singleton rules (nondeterministic scheduler) *)

Lemma axr_csl_nd_skip : forall s s' w w',
    s = s' ->
    w = w' ->
    not_done w ->
    <( {run_nd (CRet tt) s}, w |=R ret= {(s', tt)} w' )>.
Proof.
  intros s s' w w' Hs Hw Hnd; subst.
  ticl_normalize.
  rewrite run_nd_unfold.
  rewrite (interp_schedule_nd_equ sh 1 _ _ (Some Fin.F1) s'
             (cons_pool_equ _ _ _ _ denote_ret_unit (pool_equ_refl _))).
  rewrite (interp_schedule_nd_ret sh 0 [(Ret tt : thread sE Bn)]%vector Fin.F1 s' eq_refl).
  rewrite interp_schedule_nd_empty.
  apply ret_ret; [assumption | split; reflexivity].
Qed.

(** The [AX ret] count is specific to the nondeterministic scheduler: its
    scheduling point is a real branch, whereas round robin selects
    deterministically. *)
Lemma axr_csl_nd_yield : forall s s' w w',
    s = s' ->
    w = w' ->
    not_done w ->
    <( {run_nd CYield s}, w |=R AX ret= {(s', tt)} w' )>.
Proof.
  intros s s' w w' Hs Hw Hnd; subst.
  ticl_normalize.
  rewrite run_nd_unfold.
  rewrite (interp_schedule_nd_equ sh 1 _ _ (Some Fin.F1) s'
             (cons_pool_equ _ _ _ _ denote_yield_vis (pool_equ_refl _))).
  rewrite (interp_schedule_nd_yield sh 0
             [Vis (inl1 Yield : CEff unit) (fun _ : unit => Ret tt)]%vector
             Fin.F1 (fun _ : unit => (Ret tt : thread sE Bn)) s' eq_refl).
  rewrite interp_schedule_nd_select.
  apply (an_brS (b:=true) _ _ Fin.F1); split.
  - csplit; auto.
  - intro i; dependent destruction i.
    + rewrite (interp_schedule_nd_ret sh 0 _ Fin.F1 s')
        by (now rewrite Vector.nth_replace_eq).
      rewrite interp_schedule_nd_empty.
      apply ret_ret; [assumption | split; reflexivity].
    + inversion i.
Qed.

Lemma aur_csl_nd_yield_ret : forall s s' w w' ψ,
    s = s' ->
    w = w' ->
    not_done w ->
    <( {run_nd CYield s}, w |=R ψ AU AX ret= {(s', tt)} w' )>.
Proof.
  intros; subst.
  cleft.
  now apply axr_csl_nd_yield.
Qed.

(** *** Flow-preserving statement rules *)

(** The context-update observation is stated on the exact successor tree
    (one [Log] whose continuation is the finished program): the library
    [log] term carries rigid universes that do not unify with the goals.
    The endpoint formula is indexed at the instrumented state/flow result;
    native-return clients supply [CRet] and prove the final [Ret] premise. *)

Lemma au_csl_flow_assign {b : bool} : forall name expr (value : nat) s
    (w : WorldW (CSLObs (nat * nat))) (φ : ticl (writerE (CSLObs (nat * nat))) None)
    (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * option unit) b),
    <( {instr_exp_erased expr s}, w |=R ret= {(s, value)} w )> ->
    <( {Vis (Log (CSLCtx (add name value (csl_context s)) : CSLObs (nat * nat)))
          (fun _ : unit => Ret (csl_set_context s (add name value (csl_context s)), Some tt))
        : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)}, w |=L φ )> ->
    entails (SSig * option unit) b ψ
      (Ret (csl_set_context s (add name value (csl_context s)), Some tt)
        : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))
      (Obs (Log (CSLCtx (add name value (csl_context s)) : CSLObs (nat * nat))) tt) ->
    entails (SSig * option unit) b (Cu Q_A φ ψ)
      (instr_flow_erased (CAssign name expr) s) w.
Proof.
  intros name expr value s w φ ψ Hexp Hlog Hret.
  unfold instr_flow_erased, instr_exp_erased in *.
  rewrite denote_flow_cassign.
  eapply (au_ithread_bind_r_eq sh (b:=b)); [cleft; exact Hexp | cbv beta].
  rewrite (interp_thread_ctx_update (add name value)).
  unfold log, CTree.trigger; rewrite bind_vis; setoid_rewrite bind_ret_l.
  cright; apply (an_vis (b:=b) _ _ tt); split; [exact Hlog |].
  intros []; cleft; exact Hret.
Qed.

Lemma anr_csl_flow_bind_fallthrough : forall (a b : CProg unit) s s' w w'
    (φ : ticl (writerE (CSLObs (nat * nat))) None) (ψ : ticl (writerE (CSLObs (nat * nat))) (Some ((SSig * option unit) : Type))),
    <( {instr_flow_erased a s}, w |=R ret= {(s', Some tt)} w' )> ->
    <( {instr_flow_erased b s'}, w' |=R φ AN ψ )> ->
    <( {instr_flow_erased (CBind a (fun _ => b)) s}, w |=R φ AN ψ )>.
Proof.
  intros a b s s' w w' φ ψ Ha Hb.
  unfold instr_flow_erased in *.
  rewrite denote_flow_cbind_unit.
  rewrite interp_state_thread_bind.
  eapply ticl_bind_ret_eq; eauto.
Qed.

Lemma au_csl_flow_bind {suffix : bool} : forall (a b : CProg unit) s s' w w'
    (φ : ticl (writerE (CSLObs (nat * nat))) None)
    (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * option unit) suffix),
    <( {instr_flow_erased a s}, w |=R φ AU ret= {(s', Some tt)} w' )> ->
    entails (SSig * option unit) suffix (Cu Q_A φ ψ) (instr_flow_erased b s') w' ->
    entails (SSig * option unit) suffix (Cu Q_A φ ψ)
      (instr_flow_erased (CBind a (fun _ => b)) s) w.
Proof.
  intros a b s s' w w' φ ψ Ha Hb.
  unfold instr_flow_erased in *.
  rewrite denote_flow_cbind_unit.
  eapply (au_ithread_bind_r_eq sh (b:=suffix)); eauto.
Qed.


(** A halted first statement skips the second: the halt flow propagates. *)
Lemma aur_csl_flow_bind_halt : forall (a b : CProg unit) s s' w w' φ,
    <( {instr_flow_erased a s}, w |=R φ AU ret= {(s', None)} w' )> ->
    not_done w' ->
    <( {instr_flow_erased (CBind a (fun _ => b)) s},
       w |=R φ AU ret= {(s', None)} w' )>.
Proof.
  intros a b s s' w w' φ Ha Hnd.
  unfold instr_flow_erased in *.
  rewrite denote_flow_cbind_unit.
  ticl_normalize.
  eapply (au_ithread_bind_r_eq sh (b:=true)); [exact Ha | cbv beta].
  cleft.
  rewrite interp_state_thread_ret; apply ret_ret; [assumption | split; reflexivity].
Qed.

Lemma au_csl_flow_if {A suffix} : forall test (yes no : CProg A) condition s w
    (φ : ticl (writerE (CSLObs (nat * nat))) None)
    (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * option A) suffix),
    <( {instr_exp_erased test s}, w |=R ret= {(s, condition)} w )> ->
    (if CoCSLSyntax.is_true condition then
       entails (SSig * option A) suffix (Cu Q_A φ ψ) (instr_flow_erased yes s) w
     else
       entails (SSig * option A) suffix (Cu Q_A φ ψ) (instr_flow_erased no s) w) ->
    entails (SSig * option A) suffix (Cu Q_A φ ψ)
      (instr_flow_erased (CIf test yes no) s) w.
Proof.
  intros test yes no condition s w φ ψ Htest Hbranch.
  unfold instr_flow_erased, instr_exp_erased in *.
  rewrite denote_flow_cif.
  eapply (au_ithread_bind_r_eq sh (b:=suffix)); [cleft; exact Htest | cbv beta].
  destruct (CoCSLSyntax.is_true condition); exact Hbranch.
Qed.


(** *** Raw source-flow while rules

    These are stated over raw [World CEff] events and expose the option
    flow directly; they make no claim about scheduled liveness.  The shared
    step rules accept an indexed endpoint; clients requiring a next step
    pass their entire [AX] formula as that endpoint. *)

Lemma au_csl_raw_while {b : bool} : forall test body condition w w'
    (φ : ticl CEff None) (ψ : ticl_at CEff (option unit) b),
    <( {denote_exp test}, w |=R φ AU ret= condition w )> ->
    CoCSLSyntax.is_true condition = true ->
    <( {denote_flow body}, w |=R φ AU ret= {Some tt} w' )> ->
    not_done w' ->
    entails (option unit) b (Cu Q_A φ ψ) (denote_flow (CWhile test body)) w' ->
    entails (option unit) b (Cu Q_A φ ψ) (denote_flow (CWhile test body)) w.
Proof.
  intros test body condition w w' φ ψ Htest Htrue Hbody Hnd Hloop.
  rewrite denote_flow_cwhile in *.
  eapply (u_iter_next (b:=b) Q_A) with (R := fun (_ : unit) w0 => w0 = w').
  - unfold cwhile_iteration.
    eapply (u_bind_r_eq (b:=true) Q_A); [exact Htest |].
    rewrite Htrue.
    eapply (u_bind_r_eq (b:=true) Q_A); [exact Hbody |].
    cleft; apply ret_ret; auto.
    exists tt; split; auto.
  - intros [] w0 ->; exact Hloop.
Qed.

Lemma au_csl_raw_while_false {b : bool} : forall test body condition w
    (φ : ticl CEff None) (ψ : ticl_at CEff (option unit) b),
    <( {denote_exp test}, w |=R φ AU ret= condition w )> ->
    CoCSLSyntax.is_true condition = false ->
    entails (option unit) b ψ (Ret (Some tt) : ctree CEff Bn (option unit)) w ->
    entails (option unit) b (Cu Q_A φ ψ) (denote_flow (CWhile test body)) w.
Proof.
  intros test body condition w φ ψ Htest Hfalse Hret.
  pose proof Htest as Htest_not_done.
  apply ticl_not_done in Htest_not_done.
  rewrite denote_flow_cwhile, unfold_iter.
  eapply (u_bind_r_eq (b:=b) Q_A).
  - unfold cwhile_iteration.
    eapply (u_bind_r_eq (b:=true) Q_A); [exact Htest |].
    rewrite Hfalse.
    cleft; apply ret_ret; [exact Htest_not_done | split; reflexivity].
  - cbn; cleft; exact Hret.
Qed.

Lemma aul_csl_raw_while_halt : forall test body condition w w' (φ ψ : ticl CEff None),
    <( {denote_exp test}, w |=R φ AU ret= condition w )> ->
    CoCSLSyntax.is_true condition = true ->
    <( {denote_flow body}, w |=R φ AU ret= {None} w' )> ->
    not_done w' ->
    <( {Ret None : ctree CEff Bn (option unit)}, w' |=L ψ )> ->
    <( {denote_flow (CWhile test body)}, w |=L φ AU ψ )>.
Proof.
  intros test body condition w w' φ ψ Htest Htrue Hbody Hnd Hret.
  ticl_normalize.
  rewrite denote_flow_cwhile, unfold_iter.
  eapply (u_bind_r_eq (b:=false) Q_A).
  - unfold cwhile_iteration.
    eapply (u_bind_r_eq (b:=true) Q_A); [exact Htest |].
    rewrite Htrue.
    eapply (u_bind_r_eq (b:=true) Q_A); [exact Hbody |].
    cleft; apply ret_ret; auto.
  - cbn; cleft; exact Hret.
Qed.


Lemma ag_csl_raw_while : forall test body (R : World CEff -> Prop) w (φ : ticl CEff None),
    R w ->
    (forall w,
        R w ->
        <( {denote_flow (CWhile test body)}, w |=L φ )> /\
        <( {cwhile_iteration test body tt}, w |=R AX (φ AU ret
             {fun lr w' => exists i' : unit, lr = inl i' /\ R w'}) )>) ->
    <( {denote_flow (CWhile test body)}, w |=L AG φ )>.
Proof.
  intros test body R w φ HR Hstep.
  ticl_normalize.
  rewrite denote_flow_cwhile.
  eapply ag_iter with (R := fun (_ : unit) w => R w); eauto.
  intros [] w0 HR0.
  specialize (Hstep w0 HR0) as [Hφ Hnext].
  rewrite denote_flow_cwhile in Hφ.
  split; [exact Hφ | exact Hnext].
Qed.

(** A ranked raw while rule: every iteration either establishes the goal or
    returns to the loop head at a smaller natural rank. *)
Lemma aul_csl_raw_while_nat : forall test body (Ri : World CEff -> Prop)
    (f : World CEff -> nat) w (φ ψ : ticl CEff None),
    not_done w ->
    Ri w ->
    (forall w,
        not_done w ->
        Ri w ->
        <( {cwhile_iteration test body tt}, w |=L φ AU ψ )> \/
        <( {cwhile_iteration test body tt}, w |=R φ AU ret
             {fun lr w' => exists i' : unit,
                lr = inl i' /\ not_done w' /\ Ri w' /\ f w' < f w} )>) ->
    <( {denote_flow (CWhile test body)}, w |=L φ AU ψ )>.
Proof.
  intros test body Ri f w φ ψ Hnd HRi Hstep.
  ticl_normalize.
  rewrite denote_flow_cwhile.
  apply (u_iter_prefix_nat Q_A (fun (_ : unit) w => Ri w) (fun _ w => f w) tt w
           (cwhile_iteration test body)); auto.
Qed.

(** *** Scheduled assignment rules *)


Lemma au_csl_nd_assign_lit {b : bool} : forall name (n : nat) s
    (w : WorldW (CSLObs (nat * nat))) (φ : ticl (writerE (CSLObs (nat * nat))) None)
    (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b),
    <( {Vis (Log (CSLCtx (add name n (csl_context s)) : CSLObs (nat * nat)))
          (fun _ : unit => interp_schedule_nd sh 1 [(Ret tt : thread sE Bn)]%vector (Some Fin.F1)
                             (csl_set_context s (add name n (csl_context s))))}, w |=L φ )> ->
    entails (SSig * unit) b ψ
      (Ret (csl_set_context s (add name n (csl_context s)), tt)
        : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))
      (Obs (Log (CSLCtx (add name n (csl_context s)) : CSLObs (nat * nat))) tt) ->
    entails (SSig * unit) b (Cu Q_A φ ψ) (run_nd (CAssign name (CLit n)) s) w.
Proof.
  intros name n s w φ ψ Hlog Hret.
  rewrite run_nd_unfold.
  rewrite (interp_schedule_nd_equ sh 1 _
    ([Ret tt]%vector @ Fin.F1 :=
      (source_get >>= fun ctx => source_put (add name n ctx) >>= fun _ => Ret tt))
    (Some Fin.F1) s
    (cons_pool_equ _ _ _ _ (denote_assign_lit name n) (pool_equ_refl _))).
  rewrite interp_nd_get_ctx; cbv beta.
  rewrite interp_nd_put_ctx.
  unfold log, CTree.trigger; rewrite bind_vis; setoid_rewrite bind_ret_l.
  cright; apply (an_vis (b:=b) _ _ tt); split; [exact Hlog |].
  intros [].
  rewrite (interp_schedule_nd_ret sh 0 _ Fin.F1 _) by reflexivity.
  rewrite interp_schedule_nd_empty.
  cleft; exact Hret.
Qed.

(** *** Scheduler-visible and observed-scheduler bridges *)

Corollary sbisim_scheduled_visible (p q : CProg unit) :
  denote p ~ denote q ->
  scheduled_visible p ~ scheduled_visible q.
Proof.
  intro Hpq.
  unfold scheduled_visible.
  apply sbisim_schedule.
  - intro i; dependent destruction i; [apply denote_branchfree | inversion i].
  - intro i; dependent destruction i; [apply denote_branchfree | inversion i].
  - intro i; dependent destruction i; [exact Hpq | inversion i].
Qed.

Definition scheduled_observed (p : CProg unit) : observed_completed sE Bn :=
  schedule_with_offers 1 [denote p]%vector (Some Fin.F1).

Theorem forget_scheduled_observed_is_scheduled_visible (p : CProg unit) :
  forget_scheduler_offers (scheduled_observed p) ~ scheduled_visible p.
Proof.
  unfold scheduled_observed, scheduled_visible.
  apply forget_scheduler_offers_preserves_schedule.
Qed.

(** Conditional on scheduler progress; this is about scheduling-point offers,
    not fair thread selection. *)
Theorem scheduled_observed_every_live_slot_eventually_offered (p : CProg unit) :
  SchedulerProgress (scheduled_observed p) Pure ->
  agc scheduling_point_offer_obligation (scheduled_observed p) Pure.
Proof.
  unfold scheduled_observed.
  apply every_live_slot_is_eventually_offered_at_scheduling_points.
Qed.


(** ** Source pools: closed turns, selection, and structural rules

    The generic pool rules of [CTree.Logic.Yield] specialized to source
    pools [csl_pool ps].  A turn certificate is an exact first-yield segment
    of the slot's own denotation that returns to that same denotation. *)

Lemma run_nd_pool_turn {n} (ps : Vector.t (CProg unit) (S n)) (i : Fin.t (S n))
  (s s' : SSig) logs :
  segment_to sh csl_equ (csl_pool ps $ i) s logs (csl_pool ps $ i) s' ->
  run_nd_pool ps (Some i) s ~ emit_list logs (run_nd_pool ps None s').
Proof. exact (segment_pool_nd_loop sh n (csl_pool ps) i s logs s'). Qed.

Lemma run_rr_pool_turn {n} (ps : Vector.t (CProg unit) (S n)) (i : Fin.t (S n))
  cursor (s s' : SSig) logs :
  segment_to sh csl_equ (csl_pool ps $ i) s logs (csl_pool ps $ i) s' ->
  run_rr_pool ps (Some i) cursor s ~
  emit_list (List.map inl logs) (run_rr_pool ps None cursor s').
Proof. exact (segment_pool_fair_loop rr_scheduler sh n (csl_pool ps) i cursor s logs s'). Qed.

Lemma run_nd_pool_select {n} (ps : Vector.t (CProg unit) (S n)) (s : SSig) :
  run_nd_pool ps None s ~ brS (branchn (S n)) (fun i => run_nd_pool ps (Some i) s).
Proof. exact (interp_schedule_nd_select sh n (csl_pool ps) s). Qed.

Lemma run_rr_pool_select {n} (ps : Vector.t (CProg unit) (S n)) cursor (s : SSig) :
  run_rr_pool ps None cursor s ~
  Vis (Log (inr (slot_index (rr_pick n cursor))))
    (fun _ => run_rr_pool ps (Some (rr_pick n cursor)) (S cursor) s).
Proof. exact (interp_schedule_rr_select sh n (csl_pool ps) cursor s). Qed.

Lemma ag_csl_nd_invariance {G n} (ps : Vector.t (CProg unit) (S n))
    (Inv : G -> SSig -> Prop) (φ : ticl (writerE (CSLObs (nat * nat))) None) :
  ClosedTurns sh (csl_pool ps) Inv ->
  (forall (o : CSLObs (nat * nat)) (t : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)) w,
    not_done w -> entails (SSig * unit) false φ t (Obs (Log o) tt) ->
    entails (SSig * unit) false φ (Vis (Log o) (fun _ => t)) w) ->
  (forall g s focus w, Inv g s -> not_done w ->
     <( {run_nd_pool ps focus s}, {w} |=L φ )>) ->
  forall g s focus w, Inv g s -> not_done w ->
    <( {run_nd_pool ps focus s}, {w} |=L AG φ )>.
Proof. exact (ag_pool_nd_invariance sh (csl_pool ps) Inv φ). Qed.

Lemma ag_csl_rr_invariance {G n} (ps : Vector.t (CProg unit) (S n))
    (Inv : G -> SSig -> Prop) (φ : ticl (writerE (CSLObs (nat * nat) + nat)) None) :
  ClosedTurns sh (csl_pool ps) Inv ->
  (forall (o : CSLObs (nat * nat)) (t : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)) w,
    not_done w -> entails (SSig * unit) false φ t (Obs (Log (inl o)) tt) ->
    entails (SSig * unit) false φ (Vis (Log (inl o)) (fun _ => t)) w) ->
  (forall g s focus cursor w, Inv g s -> not_done w ->
     <( {run_rr_pool ps focus cursor s}, {w} |=L φ )>) ->
  forall g s focus cursor w, Inv g s -> not_done w ->
    <( {run_rr_pool ps focus cursor s}, {w} |=L AG φ )>.
Proof. exact (ag_pool_rr_invariance sh (csl_pool ps) Inv φ). Qed.

Lemma aul_csl_nd_eventually {G V n} (ps : Vector.t (CProg unit) (S n))
    (Inv : G -> SSig -> Prop) (rank : G -> V) (ltV : V -> V -> Prop)
    (P : CSLObs (nat * nat) -> Prop) :
  well_founded ltV -> RankedTurns sh (csl_pool ps) Inv rank ltV P ->
  forall g s focus w, Inv g s -> not_done w ->
    <( {run_nd_pool ps focus s}, {w} |=L AF visW {P} )>.
Proof. exact (aul_pool_nd_eventually sh (csl_pool ps) Inv rank ltV P). Qed.

Lemma aul_csl_rr_eventually {G V n} (ps : Vector.t (CProg unit) (S n))
    (Inv : G -> SSig -> Prop) (rank : G -> V) (ltV : V -> V -> Prop)
    (P : CSLObs (nat * nat) -> Prop) :
  well_founded ltV -> RankedTurns sh (csl_pool ps) Inv rank ltV P ->
  forall g s focus cursor w, Inv g s -> not_done w ->
    <( {run_rr_pool ps focus cursor s}, {w} |=L AF visW {fair_obs P} )>.
Proof. exact (aul_pool_rr_eventually sh (csl_pool ps) Inv rank ltV P). Qed.

(** *** Two-child startup

    [fork p; fork q; skip]: each fork prepends its child and keeps the
    parent focused, and the parent then terminates.  What remains is the
    unfocused pool [q; p] at the unchanged state and cursor. *)

Local Lemma replace_cons {A n} (c : A) (ts : Vector.t A n) (i : Fin.t n) x :
  (c :: (ts @ i := x))%vector = ((c :: ts)%vector @ Fin.FS i := x).
Proof. reflexivity. Qed.

Lemma run_nd_two_forks (p q : CProg unit) (s : SSig) :
  run_nd (CBind (CFork p) (fun _ => CBind (CFork q) (fun _ => CRet tt))) s ~
  run_nd_pool [q; p]%vector None s.
Proof.
  rewrite run_nd_unfold.
  change (interp_schedule_nd sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CFork p) (fun _ => CBind (CFork q) (fun _ => CRet tt)))
         >>= fun _ => Ret tt)) (Some Fin.F1) s ~ run_nd_pool [q; p]%vector None s).
  rewrite interp_nd_source_bind, interp_nd_source_fork; cbv beta iota.
  rewrite replace_cons, interp_nd_source_bind, interp_nd_source_fork; cbv beta iota.
  rewrite replace_cons, interp_nd_source_ret; cbv beta iota.
  rewrite (interp_schedule_nd_ret sh 2 _ (Fin.FS (Fin.FS Fin.F1)) s) by reflexivity.
  cbn [Vector.replace Vector.caseS'].
  rewrite !vector_remove_tail, vector_remove_head.
  reflexivity.
Qed.

Lemma run_rr_two_forks (p q : CProg unit) (s : SSig) :
  run_rr (CBind (CFork p) (fun _ => CBind (CFork q) (fun _ => CRet tt))) s ~
  run_rr_pool [q; p]%vector None 0 s.
Proof.
  rewrite run_rr_unfold.
  change (interp_schedule_rr sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CFork p) (fun _ => CBind (CFork q) (fun _ => CRet tt)))
         >>= fun _ => Ret tt)) (Some Fin.F1) 0 s ~ run_rr_pool [q; p]%vector None 0 s).
  rewrite interp_rr_bind, interp_rr_fork; cbv beta iota.
  rewrite replace_cons, interp_rr_bind, interp_rr_fork; cbv beta iota.
  rewrite replace_cons, interp_rr_ret; cbv beta iota.
  rewrite (interp_schedule_fair_ret rr_scheduler sh 2 _ (Fin.FS (Fin.FS Fin.F1)) 0 s) by reflexivity.
  cbn [Vector.replace Vector.caseS'].
  rewrite !vector_remove_tail, vector_remove_head.
  reflexivity.
Qed.

Lemma run_fair_two_forks sch (p q : CProg unit) st (s : SSig) :
  run_fair sch (CBind (CFork p) (fun _ => CBind (CFork q) (fun _ => CRet tt))) st s ~
  run_fair_pool sch [q; p]%vector None st s.
Proof.
  rewrite run_fair_unfold.
  change (interp_schedule_fair sch sh 1
    ([Ret tt]%vector @ Fin.F1 :=
      (denote_flow (CBind (CFork p) (fun _ => CBind (CFork q) (fun _ => CRet tt)))
         >>= fun _ => Ret tt)) (Some Fin.F1) st s ~ run_fair_pool sch [q; p]%vector None st s).
  rewrite interp_fair_bind, interp_fair_fork; cbv beta iota.
  rewrite replace_cons, interp_fair_bind, interp_fair_fork; cbv beta iota.
  rewrite replace_cons, interp_fair_ret; cbv beta iota.
  rewrite (interp_schedule_fair_ret sch sh 2 _ (Fin.FS (Fin.FS Fin.F1)) st s) by reflexivity.
  cbn [Vector.replace Vector.caseS'].
  rewrite !vector_remove_tail, vector_remove_head.
  reflexivity.
Qed.

(** Both forks retain parent focus, so no selection precedes the
    unfocused two-worker pool. *)
Lemma scheduled_visible_two_forks (p q : CProg unit) :
  scheduled_visible (CBind (CFork p) (fun _ => CBind (CFork q) (fun _ => CRet tt))) ~
  schedule 2 [denote q; denote p]%vector None.
Proof.
  unfold scheduled_visible.
  rewrite (schedule_pool_proper 1 _ _ (Some Fin.F1)
    (cons_pool_equ _ _ _ _ (denote_fork_bind p (fun _ => CBind (CFork q) (fun _ => CRet tt)))
      (pool_equ_refl _))).
  rewrite (ctree_eta (schedule 1 _ (Some Fin.F1))).
  erewrite schedule_focused_fork by reflexivity.
  rewrite sb_guard.
  cbn [Vector.replace Vector.caseS'].
  rewrite (schedule_pool_proper 2 _
    [denote p; Vis (inr1 (inl1 Fork))
      (fun child : bool => if child then denote q else denote (CRet tt))]%vector
    (Some (Fin.FS Fin.F1))
    (cons_pool_equ _ _ _ _ (reflexivity _)
      (cons_pool_equ _ _ _ _ (denote_fork_bind q (fun _ => CRet tt)) (pool_equ_refl _)))).
  rewrite (ctree_eta (schedule 2 _ (Some (Fin.FS Fin.F1)))).
  erewrite schedule_focused_fork by reflexivity.
  rewrite sb_guard.
  cbn [Vector.replace Vector.caseS'].
  rewrite (schedule_pool_proper 3 _ [denote q; denote p; Ret tt]%vector
    (Some (Fin.FS (Fin.FS Fin.F1)))
    (cons_pool_equ _ _ _ _ (reflexivity _)
      (cons_pool_equ _ _ _ _ (reflexivity _)
        (cons_pool_equ _ _ _ _ denote_ret_unit (pool_equ_refl _))))).
  rewrite (ctree_eta (schedule 3 _ (Some (Fin.FS (Fin.FS Fin.F1))))).
  erewrite schedule_focused_ret by reflexivity.
  rewrite sb_guard, !vector_remove_tail, vector_remove_head.
  reflexivity.
Qed.

(** Native whole-pool return, with exactly one scheduler step per newly
    selected source slot.  An already focused slot does not need selection. *)
Lemma run_nd_pool_returns n (focus : option (Fin.t n)) (s : SSig) :
  run_nd_pool (Vector.const (CoCSLSyntax.CRet tt) n) focus s ~
  Nat.iter (match focus with None => n | Some _ => Nat.pred n end)
    (fun t => Step t) (Ret (s,tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  unfold run_nd_pool; apply (interp_schedule_nd_returns sh).
  intro i; exists 0; unfold csl_pool.
  rewrite (Vector.nth_map denote (Vector.const (CoCSLSyntax.CRet tt) n)
    i i eq_refl), Vector.const_nth.
  cbn [Nat.iter]; unfold denote; rewrite source_raw_ret; reflexivity.
Qed.

(** Native whole-pool return logs each selected slot at its actual shrinking
    pool size, starting from the initial RR cursor. *)
Lemma run_rr_pool_returns n (focus : option (Fin.t n)) cursor (s : SSig) :
  run_rr_pool (Vector.const (CoCSLSyntax.CRet tt) n) focus cursor s ~
  emit_list (List.map (@inr (CSLObs (nat * nat)) nat)
    (rr_return_picks (match focus with None => n | Some _ => Nat.pred n end) cursor)) (Ret (s,tt) : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  unfold run_rr_pool; apply (interp_schedule_rr_returns sh).
  intro i; exists 0; unfold csl_pool.
  rewrite (Vector.nth_map denote (Vector.const (CoCSLSyntax.CRet tt) n)
    i i eq_refl), Vector.const_nth.
  cbn [Nat.iter]; unfold denote; rewrite source_raw_ret; reflexivity.
Qed.
