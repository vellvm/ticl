(** * The canonical CSL source language.

    Syntax ([CExp], [CProg]), its denotation into threads over the CSL
    effects, the source-instruction execution equations under both
    schedulers, the exact first-yield segment rules, and the structural Ticl
    rules stated over source programs.  Every law here specializes an
    effect-level law of [ICTree.Interp.CSL.Mod]. *)

From TICL Require Export ICTree.Interp.CSL.Mod.

(** The generic Yield event, scheduler, bisimulation, observed-scheduler and
    logic layers, re-exported for source-level clients. *)
From TICL Require Export
  ICTree.Events.Yield
  Utils.Vectors
  ICTree.Interp.Yield.Mod
  ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.Observed
  ICTree.Logic.Yield
  ICTree.Logic.SchedulerFairness.

From Stdlib Require Import List Arith.PeanoNat Lia Fin Vector Strings.String
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From ExtLib Require Import Data.Monads.StateMonad
  Structures.Maps Data.Map.FMapAList Data.String.
From Coinduction Require Import coinduction lattice tactics.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Trans ICTree.Trace
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Events.Heap
  ICTree.Interp.State.Mod ICTree.Interp.Refine
  ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin ICTree.Interp.Yield.Nondeterministic
  ICTree.Logic.Trans ICTree.Logic.AX ICTree.Logic.AF ICTree.Logic.AG
  ICTree.Logic.Bind ICTree.Logic.State ICTree.Logic.CanStep ICTree.Logic.Iter
  ICTree.Interp.Core Logic.World Logic.Core Logic.Kripke Utils.Vectors.

Import ICtree ICTreeNotations TiclNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

(** ** Syntax *)

Module CSLSyntax.
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
  | CCAS (a expected desired : nat) : CProg bool
  | CEval (e : CExp) : CProg nat
  | CAssign (name : string) (e : CExp) : CProg unit
  | CIf {A : Type} (test : CExp) (yes no : CProg A) : CProg A
  | CWhile (test : CExp) (body : CProg unit) : CProg unit.

  (** Any non-zero natural is true. *)
  Definition is_true (v : nat) : bool := negb (Nat.eqb v 0).
End CSLSyntax.
Export CSLSyntax.

(** ** Denotation *)

(** Expressions evaluate left to right.  A successful variable read yields
    once before returning the value it captured; a missing variable is
    stuck. *)
Fixpoint denote_exp (e : CExp) : ictree CEff nat :=
  match e with
  | CVar name =>
      ctx <- source_get;;
      match lookup name ctx with
      | Some value => source_yield;; Ret value
      | None => stuck
      end
  | CLit n => Ret n
  | CPlus a b => x <- denote_exp a;; y <- denote_exp b;; Ret (x + y)%nat
  | CMinus a b => x <- denote_exp a;; y <- denote_exp b;; Ret (x - y)%nat
  | CMult a b => x <- denote_exp a;; y <- denote_exp b;; Ret (x * y)%nat
  end.

Fixpoint denote_flow {A : Type} (p : CProg A) : ictree CEff (option A) :=
  match p in CProg A return ictree CEff (option A) with
  | CRead a => x <- heap_read (E:=CEff) a;; Ret (Some x)
  | CWrite a v => heap_write (E:=CEff) a v;; Ret (Some tt)
  | CEmit q v => ICtree.trigger (E2:=CEff) (Log (q,v));; Ret (Some tt)
  | CYield => source_yield;; Ret (Some tt)
  | CFork body =>
      child <- source_fork;;
      if child then denote_flow body;; Ret None else Ret (Some tt)
  | CRet x => Ret (Some x)
  | CBind body next =>
      flow <- denote_flow body;;
      match flow with None => Ret None | Some x => denote_flow (next x) end
  | CUntilNone body =>
      ICtree.iter
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
      b <- heap_cas (E:=CEff) a expected desired;; Ret (Some b)
  | CEval e => value <- denote_exp e;; Ret (Some value)
  | CAssign name e =>
      value <- denote_exp e;;
      ctx <- source_get;;
      source_put (add name value ctx);;
      Ret (Some tt)
  | CIf test yes no =>
      value <- denote_exp test;;
      if CSLSyntax.is_true value then denote_flow yes else denote_flow no
  | CWhile test body =>
      ICtree.iter
        (fun _ : unit =>
          value <- denote_exp test;;
          if CSLSyntax.is_true value then
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
  : ictree CEff (unit + option unit) :=
  value <- denote_exp test;;
  if CSLSyntax.is_true value then
    flow <- denote_flow body;;
    match flow with
    | Some _ => Ret (inl tt)
    | None => Ret (inr None)
    end
  else Ret (inr (Some tt)).

Lemma denote_flow_cwhile (test : CExp) (body : CProg unit) :
  denote_flow (CWhile test body) = ICtree.iter (cwhile_iteration test body) tt.
Proof. reflexivity. Qed.

Definition denote (p : CProg unit) : thread sE :=
  denote_flow p;; Ret tt.

Lemma denote_exp_branchfree (e : CExp) : BranchFree (denote_exp e).
Proof.
  induction e as [name|n|a IHa b IHb|a IHa b IHb|a IHa b IHb]; cbn [denote_exp].
  - apply branchfree_bind.
    + unfold source_get, ICtree.trigger; apply bf_vis; intro x; apply bf_ret.
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
    + unfold heap_read, ICtree.trigger; apply bf_vis; intro x; apply bf_ret.
    + intro x; apply bf_ret.
  - apply branchfree_bind.
    + unfold heap_write, ICtree.trigger; apply bf_vis; intros []; apply bf_ret.
    + intros []; apply bf_ret.
  - apply branchfree_bind.
    + unfold ICtree.trigger; apply bf_vis; intros []; apply bf_ret.
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
    + unfold heap_alloc, ICtree.trigger; apply bf_vis; intro a; apply bf_ret.
    + intro a; apply bf_ret.
  - apply branchfree_bind.
    + unfold heap_free, ICtree.trigger; apply bf_vis; intros []; apply bf_ret.
    + intros []; apply bf_ret.
  - apply branchfree_bind.
    + unfold heap_cas, ICtree.trigger; apply bf_vis; intro b; apply bf_ret.
    + intro b; apply bf_ret.
  - apply branchfree_bind; [apply denote_exp_branchfree|intro v; apply bf_ret].
  - apply branchfree_bind; [apply denote_exp_branchfree|intro v].
    apply branchfree_bind.
    + unfold source_get, ICtree.trigger; apply bf_vis; intro x; apply bf_ret.
    + intro ctx; apply branchfree_bind.
      * unfold source_put, ICtree.trigger; apply bf_vis; intros []; apply bf_ret.
      * intros []; apply bf_ret.
  - apply branchfree_bind; [apply denote_exp_branchfree|intro v].
    destruct (CSLSyntax.is_true v); assumption.
  - apply branchfree_iter; intros [].
    apply branchfree_bind; [apply denote_exp_branchfree|intro v].
    destruct (CSLSyntax.is_true v); [|apply bf_ret].
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
  Vis (inr (inl Fork))
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

Lemma source_raw_read_head a (K : option nat -> thread sE) :
  (denote_flow (CRead a) >>= K) ≅ Vis (inr (inr (inl (HRead a)))) (fun v => K (Some v)).
Proof.
  cbn [denote_flow]; unfold heap_read, ICtree.trigger; rewrite !bind_bind, bind_vis.
  step; constructor; intro x; rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_write_head a v (K : option unit -> thread sE) :
  (denote_flow (CWrite a v) >>= K) ≅ Vis (inr (inr (inl (HWrite a v)))) (fun _ => K (Some tt)).
Proof.
  cbn [denote_flow]; unfold heap_write, ICtree.trigger; rewrite !bind_bind, bind_vis.
  step; constructor; intros [].
  change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
    K (Some tt)).
  rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_cas_head a old desired (K : option bool -> thread sE) :
  (denote_flow (CCAS a old desired) >>= K) ≅
    Vis (inr (inr (inl (HCAS a old desired)))) (fun b => K (Some b)).
Proof.
  cbn [denote_flow]; unfold heap_cas, ICtree.trigger; rewrite !bind_bind, bind_vis.
  step; constructor; intro x; rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_emit_head tag value (K : option unit -> thread sE) :
  (denote_flow (CEmit tag value) >>= K) ≅
    Vis (inr (inr (inr (inr (Log (tag,value)))))) (fun _ => K (Some tt)).
Proof.
  cbn [denote_flow]; unfold ICtree.trigger, resum, resum_ret,
    ReSum_tagged_CEff, ReSumRet_tagged_CEff.
  rewrite bind_bind, bind_vis; step; constructor; intros [].
  rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_yield_head (K : option unit -> thread sE) :
  (denote_flow CYield >>= K) ≅ Vis (inl Yield) (fun _ => K (Some tt)).
Proof.
  cbn [denote_flow]; unfold source_yield.
  rewrite bind_bind, bind_vis; step; constructor; intros [].
  change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
    K (Some tt)).
  rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_alloc_head size (K : option nat -> thread sE) :
  (denote_flow (CAlloc size) >>= K) ≅
    Vis (inr (inr (inl (HAlloc size)))) (fun base => K (Some base)).
Proof.
  cbn [denote_flow]; unfold heap_alloc, ICtree.trigger, resum, resum_ret,
    ReSum_heap_CEff, ReSumRet_heap_CEff.
  rewrite bind_bind, bind_vis; step; constructor; intro base.
  rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_free_head base (K : option unit -> thread sE) :
  (denote_flow (CFree base) >>= K) ≅
    Vis (inr (inr (inl (HFree base)))) (fun _ => K (Some tt)).
Proof.
  cbn [denote_flow]; unfold heap_free, ICtree.trigger; rewrite !bind_bind, bind_vis.
  step; constructor; intros [].
  change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
    K (Some tt)).
  rewrite !bind_ret_l; reflexivity.
Qed.

Lemma source_raw_fork_head (child : CProg unit) (K : option unit -> thread sE) :
  (denote_flow (CFork child) >>= K) ≅
    Vis (inr (inl Fork))
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
  (K : option unit -> thread sE) (flow : option (option A)) : thread sE :=
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
  (K : option B -> thread sE) :
  (denote_flow (CBind p next) >>= K) ≅
  (denote_flow p >>= fun flow =>
    match flow with None => K None | Some x => denote_flow (next x) >>= K end).
Proof.
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intros [x|]; [reflexivity|apply bind_ret_l].
Qed.

Lemma source_raw_ret {A} (x : A) (K : option A -> thread sE) :
  (denote_flow (CRet x) >>= K) ≅ K (Some x).
Proof. cbn [denote_flow]; apply bind_ret_l. Qed.

Lemma source_raw_until {A} (body : CProg (option A))
  (K : option unit -> thread sE) :
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
  change ((ICtree.iter loop_body tt >>= K) ≅
    (denote_flow body >>= fun flow =>
      match flow with
      | None => K None
      | Some None => K (Some tt)
      | Some (Some _) => Guard (ICtree.iter loop_body tt >>= K)
      end)).
  transitivity ((loop_body tt >>= fun lr =>
    match lr with
    | inl j => Guard (ICtree.iter loop_body j)
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
Lemma source_raw_eval (e : CExp) (K : option nat -> thread sE) :
  (denote_flow (CEval e) >>= K) ≅
  (denote_exp e >>= fun value => K (Some value)).
Proof.
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro value; apply bind_ret_l.
Qed.

Lemma source_raw_assign (name : string) (e : CExp)
    (K : option unit -> thread sE) :
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
    (K : option A -> thread sE) :
  (denote_flow (CIf test yes no) >>= K) ≅
  (value <- denote_exp test;;
   if CSLSyntax.is_true value then denote_flow yes >>= K
   else denote_flow no >>= K).
Proof.
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro value; destruct (CSLSyntax.is_true value); reflexivity.
Qed.

Lemma source_raw_while (test : CExp) (body : CProg unit)
    (K : option unit -> thread sE) :
  (denote_flow (CWhile test body) >>= K) ≅
  (ICtree.iter (cwhile_iteration test body) tt >>= K).
Proof. rewrite denote_flow_cwhile; reflexivity. Qed.

(** ** Runners

    A pool of source programs runs under either scheduler from an explicit
    full state [((h,allocs),(ctx,c))]; the singleton runners start focused,
    and round robin starts at cursor [0]. *)
Definition csl_pool {n} (ps : Vector.t (CProg unit) n) : pool sE n :=
  Vector.map denote ps.

Definition run_nd_pool {n} (ps : Vector.t (CProg unit) n)
    (focus : option (Fin.t n)) (s : SSig)
  : ictreeW (CSLObs (nat * nat)) (unit * SSig) :=
  interp_schedule_nd sh n (csl_pool ps) focus s.

Definition run_rr_pool {n} (ps : Vector.t (CProg unit) n)
    (focus : option (Fin.t n)) (cursor : nat) (s : SSig)
  : ictreeW (CSLObs (nat * nat)) (unit * SSig) :=
  interp_schedule_rr sh n (csl_pool ps) focus cursor s.

Definition run_nd (p : CProg unit) (s : SSig)
  : ictreeW (CSLObs (nat * nat)) (unit * SSig) :=
  run_nd_pool [p]%vector (Some Fin.F1) s.

Definition run_rr (p : CProg unit) (s : SSig)
  : ictreeW (CSLObs (nat * nat)) (unit * SSig) :=
  run_rr_pool [p]%vector (Some Fin.F1) 0 s.

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

Lemma source_raw_lit {X} n (K : nat -> ictree CEff X) :
  (denote_exp (CLit n) >>= K) ≅ K n.
Proof. cbn [denote_exp]; rewrite bind_ret_l; reflexivity. Qed.

Lemma source_raw_var {X} name (K : nat -> ictree CEff X) :
  (denote_exp (CVar name) >>= K) ≅
  (source_get >>= fun ctx =>
     match lookup name ctx with
     | Some value => Vis (inl Yield : CEff) (fun _ => K value)
     | None => stuck
     end).
Proof.
  cbn [denote_exp]; rewrite bind_bind.
  apply equ_clo_bind_eq; intro ctx.
  destruct (lookup name ctx) as [value|].
  - unfold source_yield; rewrite bind_bind, bind_vis.
    apply vis_equ_node; intros []; cbv beta.
    etransitivity; [apply bind_ret_l|]; cbv beta.
    apply bind_ret_l.
  - apply bind_stuck_equ.
Qed.

Lemma interp_rr_lit n (ts : pool sE (S n)) (i : Fin.t (S n))
  v (K : nat -> thread sE) m (s : SSig) :
  interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CLit v) >>= K)) (Some i) m s ≅
  interp_schedule_rr sh (S n) (ts @ i := K v) (Some i) m s.
Proof.
  apply interp_schedule_rr_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_lit.
Qed.

Lemma interp_nd_lit n (ts : pool sE (S n)) (i : Fin.t (S n))
  v (K : nat -> thread sE) (s : SSig) :
  interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CLit v) >>= K)) (Some i) s ≅
  interp_schedule_nd sh (S n) (ts @ i := K v) (Some i) s.
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_lit.
Qed.

(** Assignment evaluates its expression, then performs a late
    read-modify-write of the shared context. *)
Lemma interp_rr_assign n (ts : pool sE (S n)) (i : Fin.t (S n))
  name e (K : option unit -> thread sE) m (s : SSig) :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) m s ≅
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_exp e >>= fun value =>
      source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt)))
    (Some i) m s.
Proof.
  apply interp_schedule_rr_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_assign.
Qed.

Lemma interp_nd_assign n (ts : pool sE (S n)) (i : Fin.t (S n))
  name e (K : option unit -> thread sE) (s : SSig) :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CAssign name e) >>= K)) (Some i) s ≅
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_exp e >>= fun value =>
      source_get >>= fun ctx => source_put (add name value ctx) >>= fun _ => K (Some tt)))
    (Some i) s.
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_assign.
Qed.

Lemma interp_rr_var n (ts : pool sE (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE) m (s : SSig) :
  lookup name (csl_context s) = Some value ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) m s ~
  interp_schedule_rr sh (S n) (ts @ i := K value) None m s.
Proof.
  intro Hlookup.
  rewrite (interp_schedule_rr_equ sh (S n) _ _ (Some i) m s
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_var name K))).
  rewrite interp_rr_get_ctx; cbv beta; rewrite Hlookup.
  erewrite interp_schedule_rr_yield by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_var n (ts : pool sE (S n)) (i : Fin.t (S n))
  name value (K : nat -> thread sE) (s : SSig) :
  lookup name (csl_context s) = Some value ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) s ~
  interp_schedule_nd sh (S n) (ts @ i := K value) None s.
Proof.
  intro Hlookup.
  rewrite ((interp_schedule_nd_equ sh) (S n) _ _ (Some i) s
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_var name K))).
  rewrite interp_nd_get_ctx; cbv beta; rewrite Hlookup.
  erewrite (interp_schedule_nd_yield sh)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_var_missing n (ts : pool sE (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE) m (s : SSig) :
  lookup name (csl_context s) = None ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) m s ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Hlookup.
  rewrite (interp_schedule_rr_equ sh (S n) _ _ (Some i) m s
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_var name K))).
  rewrite interp_rr_get_ctx; cbv beta; rewrite Hlookup.
  rewrite (interp_schedule_rr_stuck sh n _ i m s)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  reflexivity.
Qed.

Lemma interp_nd_var_missing n (ts : pool sE (S n)) (i : Fin.t (S n))
  name (K : nat -> thread sE) (s : SSig) :
  lookup name (csl_context s) = None ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_exp (CVar name) >>= K)) (Some i) s ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Hlookup.
  rewrite ((interp_schedule_nd_equ sh) (S n) _ _ (Some i) s
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_var name K))).
  rewrite interp_nd_get_ctx; cbv beta; rewrite Hlookup.
  rewrite (interp_schedule_nd_stuck sh n _ i s)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  reflexivity.
Qed.

Lemma interp_rr_ret {A} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m σ ≅
  interp_schedule_rr sh (S n) (ts @ i := K (Some x)) (Some i) m σ.
Proof.
  apply interp_schedule_rr_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_ret.
Qed.

Lemma interp_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m σ ~
  (interp_state sh (heap_read (E:=sE) a) σ >>= fun '(x,σ') =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some x)) (Some i) m σ').
Proof.
  apply ((interp_schedule_rr_user_bind sh) n ts i _ (inl (HRead a))
    (fun x => K (Some x)) m σ).
  apply source_raw_read_head.
Qed.

Lemma interp_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m sigma :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m sigma ~
  (interp_state sh (heap_alloc (E:=sE) size) sigma >>= fun '(base,sigma') =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some base)) (Some i) m sigma').
Proof.
  apply ((interp_schedule_rr_user_bind sh) n ts i _ (inl (HAlloc size))
    (fun base => K (Some base)) m sigma).
  apply source_raw_alloc_head.
Qed.

Lemma interp_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE) m sigma :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K))
    (Some i) m sigma ~
  (interp_state sh (heap_cas (E:=sE) a expected desired) sigma >>= fun '(b,sigma') =>
   interp_schedule_rr sh (S n) (ts @ i := K (Some b)) (Some i) m sigma').
Proof.
  apply ((interp_schedule_rr_user_bind sh) n ts i _ (inl (HCAS a expected desired))
    (fun b => K (Some b)) m sigma).
  apply source_raw_cas_head.
Qed.

Lemma interp_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m σ ~
  (interp_state sh (heap_write (E:=sE) a v) σ >>= fun '(_,σ') =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m σ').
Proof.
  apply ((interp_schedule_rr_user_bind sh) n ts i _ (inl (HWrite a v))
    (fun _ => K (Some tt)) m σ).
  apply source_raw_write_head.
Qed.

Lemma interp_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  q v (K : option unit -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit q v) >>= K)) (Some i) m σ ~
  (interp_state sh (semit q v) σ >>= fun '(_,σ') =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m σ').
Proof.
  apply ((interp_schedule_rr_user_bind sh) n ts i _ (inr (inr (Log (q,v))))
    (fun _ => K (Some tt)) m σ).
  apply source_raw_emit_head.
Qed.

Lemma interp_rr_bind {A B} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m σ :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m σ ≅
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun r =>
      match r with None => K None | Some x => denote_flow (next x) >>= K end))
    (Some i) m σ.
Proof.
  apply interp_schedule_rr_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_bind.
Qed.

Lemma interp_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) m σ ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) None m σ.
Proof.
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (denote_flow CYield >>= K))
    (ts @ i := Vis (inl Yield) (fun _ => K (Some tt)))
    (Some i) m σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_yield_head K))) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_yield by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg unit) (K : option unit -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFork p) >>= K)) (Some i) m σ ~
  interp_schedule_rr sh (S (S n))
    ((denote_flow p >>= fun _ => K None) :: (ts @ i := K (Some tt)))
    (Some (Fin.FS i)) m σ.
Proof.
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (denote_flow (CFork p) >>= K))
    (ts @ i := Vis (inr (inl Fork))
      (fun child : bool => if child
        then denote_flow p >>= fun _ => K None else K (Some tt)))
    (Some i) m σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_fork_head p K))) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_fork by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_until_none {A} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m σ :
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
  apply interp_schedule_rr_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_until.
Qed.

Lemma run_rr_fork_bind (p : CProg unit) (next : unit -> CProg unit) (s : SSig) :
  run_rr (CBind (CFork p) next) s ~
  interp_schedule_rr sh 2 [denote p; denote (next tt)]%vector
    (Some (Fin.FS Fin.F1)) 0 s.
Proof.
  rewrite run_rr_unfold.
  assert (Hpool : pool_equ [denote (CBind (CFork p) next)]%vector
    [Vis (inr (inl Fork))
      (fun child : bool => if child then denote p else denote (next tt))]%vector).
  { apply cons_pool_equ; [apply denote_fork_bind|apply pool_equ_refl]. }
  rewrite (interp_schedule_rr_equ sh 1 _ _ (Some Fin.F1) 0 s Hpool).
  erewrite interp_schedule_rr_fork by reflexivity.
  reflexivity.
Qed.

Lemma interp_nd_source_ret {A} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) σ ≅
  interp_schedule_nd sh (S n) (ts @ i := K (Some x)) (Some i) σ.
Proof.
  apply (interp_schedule_nd_equ sh), replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_ret.
Qed.

Lemma interp_nd_source_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) σ ~
  (interp_state sh (heap_read (E:=sE) a) σ >>= fun '(x,σ') =>
    interp_schedule_nd sh (S n) (ts @ i := K (Some x)) (Some i) σ').
Proof.
  apply ((interp_schedule_nd_user_bind sh) n ts i _ (inl (HRead a))
    (fun x => K (Some x)) σ).
  apply source_raw_read_head.
Qed.

Lemma interp_nd_source_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) sigma :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) sigma ~
  (interp_state sh (heap_alloc (E:=sE) size) sigma >>= fun '(base,sigma') =>
    interp_schedule_nd sh (S n) (ts @ i := K (Some base)) (Some i) sigma').
Proof.
  apply ((interp_schedule_nd_user_bind sh) n ts i _ (inl (HAlloc size))
    (fun base => K (Some base)) sigma).
  apply source_raw_alloc_head.
Qed.

Lemma interp_nd_source_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE) sigma :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K))
    (Some i) sigma ~
  (interp_state sh (heap_cas (E:=sE) a expected desired) sigma >>= fun '(b,sigma') =>
   interp_schedule_nd sh (S n) (ts @ i := K (Some b)) (Some i) sigma').
Proof.
  apply ((interp_schedule_nd_user_bind sh) n ts i _ (inl (HCAS a expected desired))
    (fun b => K (Some b)) sigma).
  apply source_raw_cas_head.
Qed.

Lemma interp_nd_source_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) σ ~
  (interp_state sh (heap_write (E:=sE) a v) σ >>= fun '(_,σ') =>
    interp_schedule_nd sh (S n) (ts @ i := K (Some tt)) (Some i) σ').
Proof.
  apply ((interp_schedule_nd_user_bind sh) n ts i _ (inl (HWrite a v))
    (fun _ => K (Some tt)) σ).
  apply source_raw_write_head.
Qed.

Lemma interp_nd_source_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  q v (K : option unit -> thread sE) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CEmit q v) >>= K)) (Some i) σ ~
  (interp_state sh (semit q v) σ >>= fun '(_,σ') =>
    interp_schedule_nd sh (S n) (ts @ i := K (Some tt)) (Some i) σ').
Proof.
  apply ((interp_schedule_nd_user_bind sh) n ts i _ (inr (inr (Log (q,v))))
    (fun _ => K (Some tt)) σ).
  apply source_raw_emit_head.
Qed.

Lemma interp_nd_source_bind {A B} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) σ :
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

Lemma interp_nd_source_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) σ ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some tt)) None σ.
Proof.
  pose proof ((interp_schedule_nd_equ sh) (S n)
    (ts @ i := (denote_flow CYield >>= K))
    (ts @ i := Vis (inl Yield) (fun _ => K (Some tt)))
    (Some i) σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_yield_head K))) as Hpool.
  rewrite Hpool.
  erewrite (interp_schedule_nd_yield sh) by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg unit) (K : option unit -> thread sE) σ :
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFork p) >>= K)) (Some i) σ ~
  interp_schedule_nd sh (S (S n))
    ((denote_flow p >>= fun _ => K None) :: (ts @ i := K (Some tt)))
    (Some (Fin.FS i)) σ.
Proof.
  pose proof ((interp_schedule_nd_equ sh) (S n)
    (ts @ i := (denote_flow (CFork p) >>= K))
    (ts @ i := Vis (inr (inl Fork))
      (fun child : bool => if child
        then denote_flow p >>= fun _ => K None else K (Some tt)))
    (Some i) σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_fork_head p K))) as Hpool.
  rewrite Hpool.
  erewrite (interp_schedule_nd_fork sh) by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_until_none {A} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) σ :
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

(** Silent checked writes, with the continuation held fixed while the state
    handler is simplified.  No congruence on a pool of bisimilar threads is
    used here. *)
Lemma interp_rr_write_present n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs ctx c :
  h a <> None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
    (Some i) m ((upd h a v,allocs),(ctx,c)).
Proof.
  intro Present.
  pose proof ((interp_heap_wr_present (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) a h allocs (ctx,c) v
    (fun x : unit => (Ret x : ictree sE unit)) Present) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_rr_write.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_source_write_present n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs ctx c :
  h a <> None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
    (Some i) ((upd h a v,allocs),(ctx,c)).
Proof.
  intro Present.
  pose proof ((interp_heap_wr_present (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) a h allocs (ctx,c) v
    (fun x : unit => (Ret x : ictree sE unit)) Present) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_nd_source_write.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.
Lemma interp_rr_read_value n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs ctx c :
  h a = Some value ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some value)) (Some i) m ((h,allocs),(ctx,c)).
Proof.
  intro Lookup.
  pose proof ((interp_heap_rd (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) a h allocs (ctx,c) value
    (fun x : nat => (Ret x : ictree sE nat)) Lookup) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_rr_read.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_source_read_value n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h allocs ctx c :
  h a = Some value ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some value)) (Some i) ((h,allocs),(ctx,c)).
Proof.
  intro Lookup.
  pose proof ((interp_heap_rd (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) a h allocs (ctx,c) value
    (fun x : nat => (Ret x : ictree sE nat)) Lookup) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_nd_source_read.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.

(** Checked operations with their scheduler continuation held fixed. *)

Lemma interp_rr_emit_log n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory ctx c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,(ctx,c)) ~
  (log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
   interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))).
Proof.
  pose proof (interp_csl_emit (tag,value) memory ctx c
    (fun x : unit => (Ret x : ictree sE unit))) as Hemit.
  rewrite bind_ret_r in Hemit.
  assert (Hstate : interp_state sh (semit tag value) (memory,(ctx,c)) ~
    (log (inr (stamp (tag,value) c) : CSLObs (nat * nat));; Ret (tt,(memory,(ctx,S c))))).
  { etransitivity; [exact Hemit |].
    apply sbisim_clo_bind_eq; [reflexivity | intros []].
    eapply equ_clos_sbisim_goal;
      [apply interp_state_ret | reflexivity | reflexivity]. }
  rewrite interp_rr_emit.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_cas_value n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs ctx c :
  h a = Some current ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  (if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),(ctx,c))).
Proof.
  intro Lookup; rewrite interp_rr_cas.
  destruct (Nat.eqb current expected) eqn:Cmp.
  - apply Nat.eqb_eq in Cmp; subst current.
    pose proof ((interp_heap_cas_success (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) a expected desired h allocs (ctx,c)
      (fun x : bool => (Ret x : ictree sE bool)) Lookup) as Hstate.
    rewrite bind_ret_r, interp_state_ret in Hstate.
    lazymatch goal with
    | |- (interp_state sh _ _ >>= ?next) ~ _ =>
      etransitivity;
      [apply sbisim_clo_bind_eq with (k2 := next);
        [exact Hstate | intro result; reflexivity] |]
    end.
    rewrite bind_ret_l; reflexivity.
  - apply Nat.eqb_neq in Cmp.
    pose proof ((interp_heap_cas_failure (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) a expected desired current h allocs (ctx,c)
      (fun x : bool => (Ret x : ictree sE bool)) Lookup Cmp) as Hstate.
    rewrite bind_ret_r, interp_state_ret in Hstate.
    lazymatch goal with
    | |- (interp_state sh _ _ >>= ?next) ~ _ =>
      etransitivity;
      [apply sbisim_clo_bind_eq with (k2 := next);
        [exact Hstate | intro result; reflexivity] |]
    end.
    rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_alloc_first n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs ctx c :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c)).
Proof.
  intros Pos Base Free First.
  pose proof ((interp_heap_alloc_first (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) h allocs size base (ctx,c)
    (fun x : nat => (Ret x : ictree sE nat)) Pos Base Free First) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_rr_alloc.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_read_missing n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE) m h allocs ctx c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_rd_stuck (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))))
    a h allocs (ctx,c) Missing) as Hstate.
  rewrite interp_rr_read.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [eapply equ_clos_sbisim_goal; [exact Hstate | reflexivity | reflexivity] | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_rr_write_missing n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs ctx c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_wr_stuck (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))))
    a v h allocs (ctx,c) Missing) as Hstate.
  rewrite interp_rr_write.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [eapply equ_clos_sbisim_goal; [exact Hstate | reflexivity | reflexivity] | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_rr_cas_missing n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE) m h allocs ctx c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),(ctx,c)) ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_cas_missing (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))))
    a expected desired h allocs (ctx,c) (fun b : bool => (Ret b : ictree sE bool)) Missing) as Hstate.
  rewrite bind_ret_r in Hstate.
  rewrite interp_rr_cas.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next); [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.


Lemma interp_nd_source_emit_log n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory ctx c :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c)) ~
  (log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
   interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))).
Proof.
  pose proof (interp_csl_emit (tag,value) memory ctx c
    (fun x : unit => (Ret x : ictree sE unit))) as Hemit.
  rewrite bind_ret_r in Hemit.
  assert (Hstate : interp_state sh (semit tag value) (memory,(ctx,c)) ~
    (log (inr (stamp (tag,value) c) : CSLObs (nat * nat));; Ret (tt,(memory,(ctx,S c))))).
  { etransitivity; [exact Hemit |].
    apply sbisim_clo_bind_eq; [reflexivity | intros []].
    eapply equ_clos_sbisim_goal;
      [apply interp_state_ret | reflexivity | reflexivity]. }
  rewrite interp_nd_source_emit.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_source_cas_value n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs ctx c :
  h a = Some current ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  (if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),(ctx,c))).
Proof.
  intro Lookup; rewrite interp_nd_source_cas.
  destruct (Nat.eqb current expected) eqn:Cmp.
  - apply Nat.eqb_eq in Cmp; subst current.
    pose proof ((interp_heap_cas_success (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) a expected desired h allocs (ctx,c)
      (fun x : bool => (Ret x : ictree sE bool)) Lookup) as Hstate.
    rewrite bind_ret_r, interp_state_ret in Hstate.
    lazymatch goal with
    | |- (interp_state sh _ _ >>= ?next) ~ _ =>
      etransitivity;
      [apply sbisim_clo_bind_eq with (k2 := next);
        [exact Hstate | intro result; reflexivity] |]
    end.
    rewrite bind_ret_l; reflexivity.
  - apply Nat.eqb_neq in Cmp.
    pose proof ((interp_heap_cas_failure (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) a expected desired current h allocs (ctx,c)
      (fun x : bool => (Ret x : ictree sE bool)) Lookup Cmp) as Hstate.
    rewrite bind_ret_r, interp_state_ret in Hstate.
    lazymatch goal with
    | |- (interp_state sh _ _ >>= ?next) ~ _ =>
      etransitivity;
      [apply sbisim_clo_bind_eq with (k2 := next);
        [exact Hstate | intro result; reflexivity] |]
    end.
    rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_source_alloc_first n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs ctx c :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c)).
Proof.
  intros Pos Base Free First.
  pose proof ((interp_heap_alloc_first (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) h allocs size base (ctx,c)
    (fun x : nat => (Ret x : ictree sE nat)) Pos Base Free First) as Hstate.
  rewrite bind_ret_r, interp_state_ret in Hstate.
  rewrite interp_nd_source_alloc.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_source_read_missing n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE) h allocs ctx c :
  h a = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_rd_stuck (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat)))) a h allocs (ctx,c) Missing) as Hstate.
  rewrite interp_nd_source_read.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [eapply equ_clos_sbisim_goal; [exact Hstate | reflexivity | reflexivity] | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_nd_source_write_missing n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs ctx c :
  h a = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_wr_stuck (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))))
    a v h allocs (ctx,c) Missing) as Hstate.
  rewrite interp_nd_source_write.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [eapply equ_clos_sbisim_goal; [exact Hstate | reflexivity | reflexivity] | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_nd_source_cas_missing n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE) h allocs ctx c :
  h a = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),(ctx,c)) ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_cas_missing (h_sum csl_context_handler (csl_emit_handler (A:=nat * nat))))
    a expected desired h allocs (ctx,c) (fun b : bool => (Ret b : ictree sE bool)) Missing) as Hstate.
  rewrite bind_ret_r in Hstate.
  rewrite interp_nd_source_cas.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next); [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.


(** Whole-block free: a valid free replaces the focused instruction by its
    continuation at the released memory, preserving focus (and the RR
    cursor); an invalid free is a fault for every continuation. *)

Lemma source_free_raw_heap_free base (K : option unit -> thread sE) :
  (denote_flow (CFree base) >>= K) ≅
    (heap_free (E:=CEff) base >>= fun _ => K (Some tt)).
Proof.
  etransitivity; [apply source_raw_free_head|].
  symmetry; apply raw_heap_free_head.
Qed.

Lemma interp_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) ctx c :
  managed_free memory base = Some memory' ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) cursor (memory,(ctx,c)) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
    (Some i) cursor (memory',(ctx,c)).
Proof.
  intro Free.
  rewrite (interp_schedule_rr_equ sh (S n) _ _ (Some i) cursor (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_rr_heap_free n ts i base (fun _ => K (Some tt)) cursor memory memory' ctx c Free).
Qed.

Lemma interp_rr_free_invalid n (ts : pool sE (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE) cursor (memory : ManagedHeap) ctx c :
  managed_free memory base = None ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) cursor (memory,(ctx,c)) ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Invalid.
  rewrite (interp_schedule_rr_equ sh (S n) _ _ (Some i) cursor (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_rr_heap_free_invalid n ts i base (fun _ => K (Some tt)) cursor memory ctx c Invalid).
Qed.

Lemma interp_nd_source_free n (ts : pool sE (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE) (memory memory' : ManagedHeap) ctx c :
  managed_free memory base = Some memory' ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) (memory,(ctx,c)) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
    (Some i) (memory',(ctx,c)).
Proof.
  intro Free.
  rewrite ((interp_schedule_nd_equ sh) (S n) _ _ (Some i) (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_nd_heap_free n ts i base (fun _ => K (Some tt)) memory memory' ctx c Free).
Qed.

Lemma interp_nd_source_free_invalid n (ts : pool sE (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE) (memory : ManagedHeap) ctx c :
  managed_free memory base = None ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) (memory,(ctx,c)) ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Invalid.
  rewrite ((interp_schedule_nd_equ sh) (S n) _ _ (Some i) (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_nd_heap_free_invalid n ts i base (fun _ => K (Some tt)) memory ctx c Invalid).
Qed.



(** ** Source-instruction first-yield rules, in exact mode. *)

Local Open Scope list_scope.

Lemma exact_source_bind {A B} (p : CProg A) (next : A -> CProg B)
  (K : option B -> thread sE) sigma logs target sigma' :
  segment_to sh csl_equ (denote_flow p >>= fun flow =>
    match flow with None => K None | Some x => denote_flow (next x) >>= K end)
    sigma logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CBind p next) >>= K) sigma logs target sigma'.
Proof.
  intro H; eapply segment_to_equ; [apply source_raw_bind|exact H].
Qed.

Lemma exact_source_ret {A} (x : A) (K : option A -> thread sE)
  sigma logs target sigma' :
  segment_to sh csl_equ (K (Some x)) sigma logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CRet x) >>= K) sigma logs target sigma'.
Proof.
  intro H; eapply segment_to_equ; [apply source_raw_ret|exact H].
Qed.

Lemma exact_source_until {A} (body : CProg (option A))
  (K : option unit -> thread sE) sigma logs target sigma' :
  segment_to sh csl_equ (denote_flow body >>= until_tail body K)
    sigma logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CUntilNone body) >>= K)
    sigma logs target sigma'.
Proof.
  intro H; eapply segment_to_equ; [apply source_raw_until|exact H].
Qed.

Lemma exact_source_read a v (K : option nat -> thread sE)
  h allocs ctx c logs target sigma' :
  h a = Some v ->
  segment_to sh csl_equ (K (Some v)) ((h,allocs),(ctx,c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CRead a) >>= K) ((h,allocs),(ctx,c)) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HRead a)))) (fun v => K (Some v))).
  - apply source_raw_read_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HRead a)))) (fun v => K (Some v)))
      ((h,allocs),(ctx,c)) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list]; rewrite (heap_handler_rd_some a h allocs (ctx,c) v Hr); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_write a v (K : option unit -> thread sE)
  h allocs ctx c logs target sigma' :
  h a <> None ->
  segment_to sh csl_equ (K (Some tt)) ((upd h a v,allocs),(ctx,c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CWrite a v) >>= K) ((h,allocs),(ctx,c)) logs target sigma'.
Proof.
  intros Hp (residual & Hseg & Htail).
  destruct (h a) as [w|] eqn:Hw; [|contradiction].
  exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HWrite a v)))) (fun _ => K (Some tt))).
  - apply source_raw_write_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HWrite a v)))) (fun _ => K (Some tt)))
      ((h,allocs),(ctx,c)) ([] ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite (heap_handler_wr_some a h allocs (ctx,c) v w Hw); reflexivity.
  - reflexivity.
Qed.

(** The raw handler equation [csl_emit_handler_log] is the response
    certificate here; [interp_csl_emit] is an interpretation equation and
    cannot discharge this premise. *)
Lemma exact_source_emit tag block (K : option unit -> thread sE)
  (memory : ManagedHeap) ctx c logs target sigma' :
  segment_to sh csl_equ (K (Some tt)) (memory,(ctx,S c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CEmit tag block) >>= K) (memory,(ctx,c))
    (inr (stamp (tag,block) c) :: logs) target sigma'.
Proof.
  intros (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inr (inr (Log (tag,block)))))) (fun _ => K (Some tt))).
  - apply source_raw_emit_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inr (inr (Log (tag,block)))))) (fun _ => K (Some tt)))
      (memory,(ctx,c)) ([inr (stamp (tag,block) c)] ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite (csl_emit_handler_log (tag,block) memory ctx c);
      reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_cas_success a expected desired
  (K : option bool -> thread sE) h allocs ctx c logs target sigma' :
  h a = Some expected ->
  segment_to sh csl_equ (K (Some true)) ((upd h a desired,allocs),(ctx,c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CCAS a expected desired) >>= K)
    ((h,allocs),(ctx,c)) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b))).
  - apply source_raw_cas_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b)))
      ((h,allocs),(ctx,c)) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list];
      rewrite (heap_handler_cas_success a expected desired h allocs (ctx,c) Hr); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_cas_failure a expected desired current
  (K : option bool -> thread sE) h allocs ctx c logs target sigma' :
  h a = Some current -> current <> expected ->
  segment_to sh csl_equ (K (Some false)) ((h,allocs),(ctx,c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CCAS a expected desired) >>= K)
    ((h,allocs),(ctx,c)) logs target sigma'.
Proof.
  intros Hr Hne (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b))).
  - apply source_raw_cas_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b)))
      ((h,allocs),(ctx,c)) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list];
      rewrite (heap_handler_cas_failure a expected desired current h allocs (ctx,c) Hr Hne);
      reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_free base (K : option unit -> thread sE)
  (memory memory' : ManagedHeap) ctx c logs target sigma' :
  managed_free memory base = Some memory' ->
  segment_to sh csl_equ (K (Some tt)) (memory',(ctx,c)) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CFree base) >>= K) (memory,(ctx,c)) logs target sigma'.
Proof.
  intros Free (residual & Hseg & Htail).
  exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HFree base)))) (fun _ => K (Some tt))).
  - apply source_raw_free_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HFree base)))) (fun _ => K (Some tt)))
      (memory,(ctx,c)) ([] ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite (heap_handler_free base memory memory' (ctx,c) Free); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_yield (K : option unit -> thread sE) sigma target :
  guard_equ (K (Some tt)) target ->
  segment_to sh csl_equ (denote_flow CYield >>= K) sigma [] target sigma.
Proof.
  intro Htail; exists (K (Some tt)); split; [|exact Htail].
  eapply segment_equ with (u := Vis (inl Yield) (fun _ => K (Some tt))).
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

(** ** Checked silent effects *)

Lemma anl_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c Lookup); reflexivity.
Qed.

Lemma anr_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c Lookup); reflexivity.
Qed.

Lemma aul_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c Lookup); reflexivity.
Qed.

Lemma aur_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c Lookup); reflexivity.
Qed.

Lemma ag_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) ((h,allocs),(ctx,c))}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs ctx c Lookup); reflexivity.
Qed.

Lemma anl_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h allocs ctx c Lookup); reflexivity.
Qed.

Lemma anr_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h allocs ctx c Lookup); reflexivity.
Qed.

Lemma aul_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h allocs ctx c Lookup); reflexivity.
Qed.

Lemma aur_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h allocs ctx c Lookup); reflexivity.
Qed.

Lemma ag_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h allocs ctx c Lookup); reflexivity.
Qed.

Lemma anl_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) ((upd h a v,allocs),(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h allocs ctx c Present); reflexivity.
Qed.

Lemma anr_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) ((upd h a v,allocs),(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h allocs ctx c Present); reflexivity.
Qed.

Lemma aul_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) ((upd h a v,allocs),(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h allocs ctx c Present); reflexivity.
Qed.

Lemma aur_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) ((upd h a v,allocs),(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h allocs ctx c Present); reflexivity.
Qed.

Lemma ag_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) ((upd h a v,allocs),(ctx,c))}, {w} |= AG φ )>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h allocs ctx c Present); reflexivity.
Qed.

Lemma anl_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m ((upd h a v,allocs),(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h allocs ctx c Present); reflexivity.
Qed.

Lemma anr_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m ((upd h a v,allocs),(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h allocs ctx c Present); reflexivity.
Qed.

Lemma aul_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m ((upd h a v,allocs),(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h allocs ctx c Present); reflexivity.
Qed.

Lemma aur_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m ((upd h a v,allocs),(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h allocs ctx c Present); reflexivity.
Qed.

Lemma ag_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m ((upd h a v,allocs),(ctx,c))}, {w} |= AG φ )>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h allocs ctx c Present); reflexivity.
Qed.

(** ** Valid whole-block free; [managed_free] covers the null no-op. *)

Lemma anl_csl_nd_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory',(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  intros Free.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma anr_csl_nd_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory',(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  intros Free.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma aul_csl_nd_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory',(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  intros Free.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma aur_csl_nd_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory',(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  intros Free.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma ag_csl_nd_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory',(ctx,c))}, {w} |= AG φ )>)).
Proof.
  intros Free.
  rewrite (interp_nd_source_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma anl_csl_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) cursor (memory',(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  intros Free.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c Free); reflexivity.
Qed.

Lemma anr_csl_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) cursor (memory',(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  intros Free.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c Free); reflexivity.
Qed.

Lemma aul_csl_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) cursor (memory',(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  intros Free.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c Free); reflexivity.
Qed.

Lemma aur_csl_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) cursor (memory',(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  intros Free.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c Free); reflexivity.
Qed.

Lemma ag_csl_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) cursor (memory',(ctx,c))}, {w} |= AG φ )>)).
Proof.
  intros Free.
  rewrite (interp_rr_free n ts i base K cursor memory memory' ctx c Free); reflexivity.
Qed.

Lemma anl_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c Pos Base Free First); reflexivity.
Qed.

Lemma anr_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c Pos Base Free First); reflexivity.
Qed.

Lemma aul_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c Pos Base Free First); reflexivity.
Qed.

Lemma aur_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c Pos Base Free First); reflexivity.
Qed.

Lemma ag_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs ctx c Pos Base Free First); reflexivity.
Qed.

Lemma anl_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h allocs ctx c Pos Base Free First); reflexivity.
Qed.

Lemma anr_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h allocs ctx c Pos Base Free First); reflexivity.
Qed.

Lemma aul_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h allocs ctx c Pos Base Free First); reflexivity.
Qed.

Lemma aur_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h allocs ctx c Pos Base Free First); reflexivity.
Qed.

Lemma ag_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h allocs ctx c Pos Base Free First); reflexivity.
Qed.

Lemma anl_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c Lookup); reflexivity.
Qed.

Lemma anr_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c Lookup); reflexivity.
Qed.

Lemma aul_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c Lookup); reflexivity.
Qed.

Lemma aur_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c Lookup); reflexivity.
Qed.

Lemma ag_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= AG φ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),(ctx,c))}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs ctx c Lookup); reflexivity.
Qed.

Lemma anl_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h allocs ctx c Lookup); reflexivity.
Qed.

Lemma anr_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h allocs ctx c Lookup); reflexivity.
Qed.

Lemma aul_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h allocs ctx c Lookup); reflexivity.
Qed.

Lemma aur_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h allocs ctx c Lookup); reflexivity.
Qed.

Lemma ag_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= AG φ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),(ctx,c))
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h allocs ctx c Lookup); reflexivity.
Qed.

(** ** Source flow and pool structure *)

Lemma anl_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (memory,(ctx,c))); reflexivity.
Qed.

Lemma anr_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (memory,(ctx,c))); reflexivity.
Qed.

Lemma aul_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (memory,(ctx,c))); reflexivity.
Qed.

Lemma aur_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (memory,(ctx,c))); reflexivity.
Qed.

Lemma ag_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (memory,(ctx,c))); reflexivity.
Qed.

Lemma anl_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma anr_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma aul_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma aur_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma ag_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma anl_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (memory,(ctx,c))); reflexivity.
Qed.

Lemma anr_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (memory,(ctx,c))); reflexivity.
Qed.

Lemma aul_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (memory,(ctx,c))); reflexivity.
Qed.

Lemma aur_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (memory,(ctx,c))); reflexivity.
Qed.

Lemma ag_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (memory,(ctx,c))); reflexivity.
Qed.

Lemma anl_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma anr_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma aul_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma aur_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma ag_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma anl_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (memory,(ctx,c))); reflexivity.
Qed.

Lemma anr_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (memory,(ctx,c))); reflexivity.
Qed.

Lemma aul_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (memory,(ctx,c))); reflexivity.
Qed.

Lemma aur_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (memory,(ctx,c))); reflexivity.
Qed.

Lemma ag_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (memory,(ctx,c))); reflexivity.
Qed.

Lemma anl_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma anr_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma aul_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma aur_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma ag_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma anl_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (memory,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (memory,(ctx,c))); reflexivity.
Qed.

Lemma anr_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (memory,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (memory,(ctx,c))); reflexivity.
Qed.

Lemma aul_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (memory,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (memory,(ctx,c))); reflexivity.
Qed.

Lemma aur_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (memory,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (memory,(ctx,c))); reflexivity.
Qed.

Lemma ag_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (memory,(ctx,c))); reflexivity.
Qed.

Lemma anl_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (memory,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma anr_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (memory,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma aul_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (memory,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma aur_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (memory,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (memory,(ctx,c))); reflexivity.
Qed.

Lemma ag_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (memory,(ctx,c))); reflexivity.
Qed.

(** ** Observable emission and cooperative selection *)

Lemma anl_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {w} |= φ )> /\
    <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {Obs (Log (inr (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |= ψ )>)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply anl_log_iff.
Qed.

Lemma anr_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {w} |= φ )> /\
    <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {Obs (Log (inr (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |= ψ ]>)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply anr_log_iff.
Qed.

Lemma aul_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {w} |= ψ )> \/
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {w} |= φ )> /\
    <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {Obs (Log (inr (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |= φ AU ψ )>))).
Proof.
  rewrite interp_nd_source_emit_log.
  apply aul_log_iff.
Qed.

Lemma aur_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {w} |= ψ ]> \/
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {w} |= φ )> /\
    <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {Obs (Log (inr (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |= φ AU ψ ]>))).
Proof.
  rewrite interp_nd_source_emit_log.
  apply aur_log_iff.
Qed.

Lemma ag_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {w} |= φ )> /\
    <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,(ctx,S c))}, {Obs (Log (inr (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |= AG φ )>)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply ag_log_iff.
Qed.

Lemma anl_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {Obs (Log (inr (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |= ψ )>)).
Proof.
  rewrite interp_rr_emit_log.
  apply anl_log_iff.
Qed.

Lemma anr_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {w} |= φ )> /\
    <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {Obs (Log (inr (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |= ψ ]>)).
Proof.
  rewrite interp_rr_emit_log.
  apply anr_log_iff.
Qed.

Lemma aul_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {w} |= ψ )> \/
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {Obs (Log (inr (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |= φ AU ψ )>))).
Proof.
  rewrite interp_rr_emit_log.
  apply aul_log_iff.
Qed.

Lemma aur_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {w} |= ψ ]> \/
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {w} |= φ )> /\
    <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {Obs (Log (inr (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |= φ AU ψ ]>))).
Proof.
  rewrite interp_rr_emit_log.
  apply aur_log_iff.
Qed.

Lemma ag_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {log (inr (stamp (tag,value) c) : CSLObs (nat * nat));;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,(ctx,S c))}, {Obs (Log (inr (stamp (tag,value) c) : CSLObs (nat * nat))) tt} |= AG φ )>)).
Proof.
  rewrite interp_rr_emit_log.
  apply ag_log_iff.
Qed.

Lemma anl_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c))}, {w} |= ψ )>)).
Proof.
  rewrite interp_nd_source_yield.
  apply anl_csl_nd_select.
Qed.

Lemma anr_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c))}, {w} |= ψ ]>)).
Proof.
  rewrite interp_nd_source_yield.
  apply anr_csl_nd_select.
Qed.

Lemma aul_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))}, {w} |= ψ )> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c))}, {w} |= φ AU ψ )>))).
Proof.
  rewrite interp_nd_source_yield.
  apply aul_csl_nd_select.
Qed.

Lemma aur_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))}, {w} |= ψ ]> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c))}, {w} |= φ AU ψ ]>))).
Proof.
  rewrite interp_nd_source_yield.
  apply aur_csl_nd_select.
Qed.

Lemma ag_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite interp_nd_source_yield.
  apply ag_csl_nd_select.
Qed.

Lemma anl_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  rewrite interp_rr_yield.
  apply anl_csl_rr_select.
Qed.

Lemma anr_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite interp_rr_yield.
  apply anr_csl_rr_select.
Qed.

Lemma aul_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m memory ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  rewrite interp_rr_yield.
  apply aul_csl_rr_select.
Qed.

Lemma aur_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite interp_rr_yield.
  apply aur_csl_rr_select.
Qed.

Lemma ag_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m memory ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite interp_rr_yield.
  apply ag_csl_rr_select.
Qed.

(** ** Finite heaps supply their constructive first-fit witness *)

Lemma anl_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AN ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anl_csl_nd_alloc n ts i size base K h allocs ctx c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size (ctx,c) Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anl_csl_nd_alloc n ts i size base K h allocs ctx c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma anr_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AN ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anr_csl_nd_alloc n ts i size base K h allocs ctx c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size (ctx,c) Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anr_csl_nd_alloc n ts i size base K h allocs ctx c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aul_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AU ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aul_csl_nd_alloc n ts i size base K h allocs ctx c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size (ctx,c) Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aul_csl_nd_alloc n ts i size base K h allocs ctx c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aur_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AU ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aur_csl_nd_alloc n ts i size base K h allocs ctx c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size (ctx,c) Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aur_csl_nd_alloc n ts i size base K h allocs ctx c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma ag_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),(ctx,c))}, {w} |= AG φ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= AG φ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (ag_csl_nd_alloc n ts i size base K h allocs ctx c w φ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size (ctx,c) Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (ag_csl_nd_alloc n ts i size base K h allocs ctx c w φ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma anl_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AN ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anl_csl_rr_alloc n ts i size base K m h allocs ctx c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size (ctx,c) Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anl_csl_rr_alloc n ts i size base K m h allocs ctx c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma anr_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AN ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AN ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anr_csl_rr_alloc n ts i size base K m h allocs ctx c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size (ctx,c) Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anr_csl_rr_alloc n ts i size base K m h allocs ctx c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aul_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h allocs ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AU ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aul_csl_rr_alloc n ts i size base K m h allocs ctx c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size (ctx,c) Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aul_csl_rr_alloc n ts i size base K m h allocs ctx c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aur_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= φ AU ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= φ AU ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aur_csl_rr_alloc n ts i size base K m h allocs ctx c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size (ctx,c) Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aur_csl_rr_alloc n ts i size base K m h allocs ctx c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma ag_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h allocs ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),(ctx,c))}, {w} |= AG φ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,(ctx,c))}, {w} |= AG φ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (ag_csl_rr_alloc n ts i size base K m h allocs ctx c w φ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size (ctx,c) Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (ag_csl_rr_alloc n ts i size base K m h allocs ctx c w φ Pos Base Free First)).
    apply Hall; assumption.
Qed.

(** ** Source loops: actual observations sustain AG; guard-only divergence does not *)

Lemma run_nd_emit_loop_ag tag value memory ctx c w :
  not_done w ->
  <( {run_nd (CUntilNone (CBind (CEmit tag value)
    (fun _ => CRet (Some tt : option unit)))) (memory,(ctx,c))}, {w} |= AG ⊤ )>.
Proof.
  revert c w; coinduction R CIH; intros c w Hw.
  unfold run_nd, run_nd_pool, csl_pool, denote.
  change (agcbt (entailsL (unit * SSig) <[ ⊤ ]>) R
    (interp_schedule_nd sh 1
      (([Ret tt] : pool sE 1) @ Fin.F1 :=
        (denote_flow
          (CUntilNone
            (CBind (CEmit tag value) (fun _ => CRet (Some tt : option unit))))
          >>= fun _ => Ret tt))
      (Some Fin.F1) (memory,(ctx,c))) w).
  rewrite interp_nd_source_until_none, interp_nd_source_bind,
    interp_nd_source_emit_log.
  unfold log, ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  split; [split; [exact I | exact Hw] |].
  split.
  - apply can_step_vis; [exact tt | exact Hw].
  - intros t' w' Htr.
    apply ktrans_vis in Htr as ([] & -> & <- & Hnd).
    rewrite interp_nd_source_ret.
    erewrite (interp_schedule_nd_guard sh) by reflexivity.
    cbn [Vector.replace].
    apply CIH.
    constructor.
Qed.

Lemma run_rr_emit_loop_ag tag value memory ctx c w :
  not_done w ->
  <( {run_rr (CUntilNone (CBind (CEmit tag value)
    (fun _ => CRet (Some tt : option unit)))) (memory,(ctx,c))}, {w} |= AG ⊤ )>.
Proof.
  revert c w; coinduction R CIH; intros c w Hw.
  unfold run_rr, run_rr_pool, csl_pool, denote.
  change (agcbt (entailsL (unit * SSig) <[ ⊤ ]>) R
    (interp_schedule_rr sh 1
      (([Ret tt] : pool sE 1) @ Fin.F1 :=
        (denote_flow
          (CUntilNone
            (CBind (CEmit tag value) (fun _ => CRet (Some tt : option unit))))
          >>= fun _ => Ret tt))
      (Some Fin.F1) 0 (memory,(ctx,c))) w).
  rewrite interp_rr_until_none, interp_rr_bind, interp_rr_emit_log.
  unfold log, ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  split; [split; [exact I | exact Hw] |].
  split.
  - apply can_step_vis; [exact tt | exact Hw].
  - intros t' w' Htr.
    apply ktrans_vis in Htr as ([] & -> & <- & Hnd).
    rewrite interp_rr_ret.
    erewrite interp_schedule_rr_guard by reflexivity.
    cbn [Vector.replace].
    apply CIH.
    constructor.
Qed.

(** The silent loop starts focused, so the whole run is raw-equivalent to its
    own guard and hence to [stuck]; no scheduler tau is erased. *)
Lemma run_nd_silent_loop_no_ag (s : SSig) w :
  ~ <( {run_nd (CUntilNone (CRet (Some tt : option unit))) s}, {w} |= AG ⊤ )>.
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
    - apply ((interp_schedule_nd_equ sh) 1 _ [Guard (denote p)]).
      apply SBisim.cons_pool_equ; [exact Hraw | apply SBisim.pool_equ_refl].
    - unfold interp_schedule_nd.
      rewrite (SBisim.trans_schedule_focused_guard
        0 [Guard (denote p)] Fin.F1 (denote p) eq_refl).
      rewrite interp_erase_guard, ICTree.Interp.State.Mod.interp_state_tau.
      reflexivity. }
  rewrite (equ_guard_stuck _ Hguard).
  apply ag_stuck.
Qed.

Lemma run_rr_silent_loop_no_ag (s : SSig) w :
  ~ <( {run_rr (CUntilNone (CRet (Some tt : option unit))) s}, {w} |= AG ⊤ )>.
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
    - apply (interp_schedule_rr_equ sh 1 _ [Guard (denote p)]).
      apply SBisim.cons_pool_equ; [exact Hraw | apply SBisim.pool_equ_refl].
    - unfold interp_schedule_rr.
      rewrite unfold_run_round_robin,
        (schedule_focused_guard 0 [Guard (denote p)] Fin.F1 (denote p) eq_refl).
      rewrite interp_erase_guard, ICTree.Interp.State.Mod.interp_state_tau.
      reflexivity. }
  rewrite (equ_guard_stuck _ Hguard).
  apply ag_stuck.
Qed.

(** ** Yield-language structural surface

    The Yield-style expression and control fragment of [CProg] is reasoned
    about through three views, all built from the generic eraser and state
    interpreter:

    - [scheduled_visible]: the scheduled program with scheduler [Spawn],
      cooperative [Yield] and user effects visible;
    - [instr_exp_erased]/[instr_flow_erased]: a standalone erased thread run
      through [sh], exposing the outer option flow;
    - [run_nd]: the erased nondeterministic singleton schedule. *)

Definition scheduled_visible (p : CProg unit) : completed sE :=
  schedule 1 [denote p]%vector (Some Fin.F1).

Definition instr_exp_erased (e : CExp) (s : SSig)
  : ictreeW (CSLObs (nat * nat)) (nat * SSig) :=
  interp_state sh (interp_thread (denote_exp e)) s.

Definition instr_flow_erased {A} (p : CProg A) (s : SSig)
  : ictreeW (CSLObs (nat * nat)) (option A * SSig) :=
  interp_state sh (interp_thread (denote_flow p)) s.

(** *** Constructor unfold equations *)

Lemma denote_exp_cvar name :
  denote_exp (CVar name) =
    (ctx <- source_get;;
     match lookup name ctx with
     | Some value => source_yield;; Ret value
     | None => stuck
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
     if CSLSyntax.is_true value then denote_flow yes else denote_flow no).
Proof. reflexivity. Qed.

Lemma denote_flow_cret_unit : denote_flow (CRet tt) = Ret (Some tt).
Proof. reflexivity. Qed.

Lemma denote_flow_cyield : denote_flow CYield = (source_yield;; Ret (Some tt)).
Proof. reflexivity. Qed.

(** *** Startup normalizations used by the singleton rules *)

Local Lemma source_yield_bind {X} (k : unit -> ictree CEff X) :
  (source_yield >>= k) ≅ Vis (inl Yield) k.
Proof.
  unfold source_yield; rewrite bind_vis.
  apply vis_equ_node; intros []; apply bind_ret_l.
Qed.

Local Lemma denote_ret_unit : denote (CRet tt) ≅ Ret tt.
Proof. unfold denote; cbn [denote_flow]; step; cbn; constructor; reflexivity. Qed.

Local Lemma denote_yield_vis :
  denote CYield ≅ Vis (inl Yield : CEff) (fun _ : unit => Ret tt).
Proof.
  unfold denote; cbn [denote_flow]; unfold source_yield.
  step; cbn; constructor; intros [].
  step; cbn; constructor; reflexivity.
Qed.

Local Lemma denote_assign_lit name n :
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
    <[ {instr_exp_erased (CLit n) s}, w |= AX done= {(n', s')} w' ]>.
Proof.
  intros; subst.
  unfold instr_exp_erased; cbn [denote_exp].
  apply axr_ithread_ret; [assumption | split; reflexivity].
Qed.

Lemma axr_csl_exp_var_some : forall name value s s' w w',
    lookup name (csl_context s) = Some value ->
    s = s' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (CVar name) s}, w |= AX done= {(value, s')} w' ]>.
Proof.
  intros name value s s' w w' Hlookup Hs Hw Hnd; subst.
  unfold instr_exp_erased; cbn [denote_exp].
  rewrite interp_thread_get_ctx, Hlookup, source_yield_bind.
  rewrite interp_state_thread_yield.
  apply axr_ithread_ret; [assumption | split; reflexivity].
Qed.

Lemma axr_csl_exp_plus : forall a b x y value s s' w w',
    <[ {instr_exp_erased a s}, w |= AX done= {(x, s)} w ]> ->
    <[ {instr_exp_erased b s}, w |= AX done= {(y, s)} w ]> ->
    value = (x + y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (CPlus a b) s}, w |= AX done= {(value, s')} w' ]>.
Proof.
  intros a b x y value s s' w w' Ha Hb Hvalue Hs Hw Hnd; subst.
  unfold instr_exp_erased in *; cbn [denote_exp].
  eapply anr_ithread_bind_r_eq; [exact Ha | cbv beta].
  eapply anr_ithread_bind_r_eq; [exact Hb | cbv beta].
  apply axr_ithread_ret; [assumption | split; reflexivity].
Qed.

Lemma axr_csl_exp_minus : forall a b x y value s s' w w',
    <[ {instr_exp_erased a s}, w |= AX done= {(x, s)} w ]> ->
    <[ {instr_exp_erased b s}, w |= AX done= {(y, s)} w ]> ->
    value = (x - y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (CMinus a b) s}, w |= AX done= {(value, s')} w' ]>.
Proof.
  intros a b x y value s s' w w' Ha Hb Hvalue Hs Hw Hnd; subst.
  unfold instr_exp_erased in *; cbn [denote_exp].
  eapply anr_ithread_bind_r_eq; [exact Ha | cbv beta].
  eapply anr_ithread_bind_r_eq; [exact Hb | cbv beta].
  apply axr_ithread_ret; [assumption | split; reflexivity].
Qed.

Lemma axr_csl_exp_mult : forall a b x y value s s' w w',
    <[ {instr_exp_erased a s}, w |= AX done= {(x, s)} w ]> ->
    <[ {instr_exp_erased b s}, w |= AX done= {(y, s)} w ]> ->
    value = (x * y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (CMult a b) s}, w |= AX done= {(value, s')} w' ]>.
Proof.
  intros a b x y value s s' w w' Ha Hb Hvalue Hs Hw Hnd; subst.
  unfold instr_exp_erased in *; cbn [denote_exp].
  eapply anr_ithread_bind_r_eq; [exact Ha | cbv beta].
  eapply anr_ithread_bind_r_eq; [exact Hb | cbv beta].
  apply axr_ithread_ret; [assumption | split; reflexivity].
Qed.

Lemma axr_csl_exp_plus_lit_lit : forall x y value s s' w w',
    value = (x + y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (CPlus (CLit x) (CLit y)) s},
       w |= AX done= {(value, s')} w' ]>.
Proof.
  intros; subst.
  eapply axr_csl_exp_plus; eauto; apply axr_csl_exp_lit; auto.
Qed.

Lemma axr_csl_exp_minus_lit_lit : forall x y value s s' w w',
    value = (x - y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (CMinus (CLit x) (CLit y)) s},
       w |= AX done= {(value, s')} w' ]>.
Proof.
  intros; subst.
  eapply axr_csl_exp_minus; eauto; apply axr_csl_exp_lit; auto.
Qed.

Lemma axr_csl_exp_mult_lit_lit : forall x y value s s' w w',
    value = (x * y)%nat ->
    s = s' ->
    w = w' ->
    not_done w ->
    <[ {instr_exp_erased (CMult (CLit x) (CLit y)) s},
       w |= AX done= {(value, s')} w' ]>.
Proof.
  intros; subst.
  eapply axr_csl_exp_mult; eauto; apply axr_csl_exp_lit; auto.
Qed.

(** *** Scheduled singleton rules (nondeterministic scheduler) *)

Lemma axr_csl_nd_skip : forall s s' w w',
    s = s' ->
    w = w' ->
    not_done w ->
    <[ {run_nd (CRet tt) s}, w |= AX done= {(tt, s')} w' ]>.
Proof.
  intros s s' w w' Hs Hw Hnd; subst.
  rewrite run_nd_unfold.
  rewrite ((interp_schedule_nd_equ sh) 1 _ _ (Some Fin.F1) s'
             (cons_pool_equ _ _ _ _ denote_ret_unit (pool_equ_refl _))).
  apply axr_schedule_nd_ret; [assumption | split; reflexivity].
Qed.

(** The [AX AX] count is specific to the nondeterministic scheduler: its
    scheduling point is a real branch, whereas round robin selects
    deterministically. *)
Lemma axax_csl_nd_yield : forall s s' w w',
    s = s' ->
    w = w' ->
    not_done w ->
    <[ {run_nd CYield s}, w |= AX AX done= {(tt, s')} w' ]>.
Proof.
  intros s s' w w' Hs Hw Hnd; subst.
  rewrite run_nd_unfold.
  rewrite ((interp_schedule_nd_equ sh) 1 _ _ (Some Fin.F1) s'
             (cons_pool_equ _ _ _ _ denote_yield_vis (pool_equ_refl _))).
  apply axax_schedule_nd_yield; [assumption | split; reflexivity].
Qed.

Lemma aur_csl_nd_yield_done : forall s s' w w' ψ,
    s = s' ->
    w = w' ->
    not_done w ->
    <[ {run_nd CYield s}, w |= ψ AU AX AX done= {(tt, s')} w' ]>.
Proof.
  intros; subst.
  cleft.
  now apply axax_csl_nd_yield.
Qed.

(** *** Flow-preserving statement rules *)

Lemma aur_csl_flow_assign : forall name expr value s w ψ R,
    <[ {instr_exp_erased expr s}, w |= AX done= {(value, s)} w ]> ->
    <( {log (inl (add name value (csl_context s)) : CSLObs (nat * nat))}, w |= ψ )> ->
    R (Some tt, csl_set_context s (add name value (csl_context s)))
      (Obs (Log (inl (add name value (csl_context s)) : CSLObs (nat * nat))) tt) ->
    <[ {instr_flow_erased (CAssign name expr) s}, w |= ψ AU AX done R ]>.
Proof.
  intros name expr value s w ψ R Hexp Hlog HR.
  pose proof (ticll_not_done unit _ _ _ Hlog) as Hnd.
  unfold instr_flow_erased, instr_exp_erased in *.
  rewrite denote_flow_cassign.
  eapply aur_ithread_bind_r_eq; [cleft; exact Hexp | cbv beta].
  rewrite (interp_thread_ctx_update (add name value)).
  eapply aur_log.
  - cleft; apply axr_ret; [constructor | exact HR].
  - now apply ticll_bind_l.
Qed.

Lemma aul_csl_flow_assign : forall name expr value s w ψ φ,
    <[ {instr_exp_erased expr s}, w |= AX done= {(value, s)} w ]> ->
    <( {log (inl (add name value (csl_context s)) : CSLObs (nat * nat))}, w |= ψ )> ->
    <( {Ret (Some tt, csl_set_context s (add name value (csl_context s)))},
       {Obs (Log (inl (add name value (csl_context s)) : CSLObs (nat * nat))) tt}
       |= φ )> ->
    <( {instr_flow_erased (CAssign name expr) s}, w |= ψ AU φ )>.
Proof.
  intros name expr value s w ψ φ Hexp Hlog Hret.
  unfold instr_flow_erased, instr_exp_erased in *.
  rewrite denote_flow_cassign.
  eapply aul_ithread_bind_r_eq; [cleft; exact Hexp | cbv beta].
  rewrite (interp_thread_ctx_update (add name value)).
  cright.
  apply anl_log.
  - cleft; exact Hret.
  - now apply ticll_bind_l.
Qed.

Lemma anr_csl_flow_bind_fallthrough : forall (a b : CProg unit) s s' w w' φ ψ,
    <[ {instr_flow_erased a s}, w |= φ AN done= {(Some tt, s')} w' ]> ->
    <[ {instr_flow_erased b s'}, w' |= φ AN ψ ]> ->
    <[ {instr_flow_erased (CBind a (fun _ => b)) s}, w |= φ AN ψ ]>.
Proof.
  intros a b s s' w w' φ ψ Ha Hb.
  unfold instr_flow_erased in *.
  rewrite denote_flow_cbind_unit.
  eapply anr_ithread_bind_r_eq; eauto.
Qed.

Lemma aur_csl_flow_bind : forall (a b : CProg unit) s s' w w' φ ψ,
    <[ {instr_flow_erased a s}, w |= φ AU AX done= {(Some tt, s')} w' ]> ->
    <[ {instr_flow_erased b s'}, w' |= φ AU ψ ]> ->
    <[ {instr_flow_erased (CBind a (fun _ => b)) s}, w |= φ AU ψ ]>.
Proof.
  intros a b s s' w w' φ ψ Ha Hb.
  unfold instr_flow_erased in *.
  rewrite denote_flow_cbind_unit.
  eapply aur_ithread_bind_r_eq; eauto.
Qed.

Lemma aul_csl_flow_bind : forall (a b : CProg unit) s s' w w' φ ψ,
    <[ {instr_flow_erased a s}, w |= φ AU AX done= {(Some tt, s')} w' ]> ->
    <( {instr_flow_erased b s'}, w' |= φ AU ψ )> ->
    <( {instr_flow_erased (CBind a (fun _ => b)) s}, w |= φ AU ψ )>.
Proof.
  intros a b s s' w w' φ ψ Ha Hb.
  unfold instr_flow_erased in *.
  rewrite denote_flow_cbind_unit.
  eapply aul_ithread_bind_r_eq; eauto.
Qed.

(** A halted first statement skips the second: the halt flow propagates. *)
Lemma aur_csl_flow_bind_halt : forall (a b : CProg unit) s s' w w' φ,
    <[ {instr_flow_erased a s}, w |= φ AU AX done= {(None, s')} w' ]> ->
    not_done w' ->
    <[ {instr_flow_erased (CBind a (fun _ => b)) s},
       w |= φ AU AX done= {(None, s')} w' ]>.
Proof.
  intros a b s s' w w' φ Ha Hnd.
  unfold instr_flow_erased in *.
  rewrite denote_flow_cbind_unit.
  eapply aur_ithread_bind_r_eq; [exact Ha | cbv beta].
  cleft.
  apply axr_ithread_ret; [assumption | split; reflexivity].
Qed.

Lemma aul_csl_flow_if {A} : forall test (yes no : CProg A) condition s w φ ψ,
    <[ {instr_exp_erased test s}, w |= AX done= {(condition, s)} w ]> ->
    (if CSLSyntax.is_true condition then
       <( {instr_flow_erased yes s}, w |= φ AU ψ )>
     else
       <( {instr_flow_erased no s}, w |= φ AU ψ )>) ->
    <( {instr_flow_erased (CIf test yes no) s}, w |= φ AU ψ )>.
Proof.
  intros test yes no condition s w φ ψ Htest Hbranch.
  unfold instr_flow_erased, instr_exp_erased in *.
  rewrite denote_flow_cif.
  eapply aul_ithread_bind_r_eq; [cleft; exact Htest | cbv beta].
  destruct (CSLSyntax.is_true condition); exact Hbranch.
Qed.

Lemma aur_csl_flow_if {A} : forall test (yes no : CProg A) condition s w φ ψ,
    <[ {instr_exp_erased test s}, w |= AX done= {(condition, s)} w ]> ->
    (if CSLSyntax.is_true condition then
       <[ {instr_flow_erased yes s}, w |= φ AU ψ ]>
     else
       <[ {instr_flow_erased no s}, w |= φ AU ψ ]>) ->
    <[ {instr_flow_erased (CIf test yes no) s}, w |= φ AU ψ ]>.
Proof.
  intros test yes no condition s w φ ψ Htest Hbranch.
  unfold instr_flow_erased, instr_exp_erased in *.
  rewrite denote_flow_cif.
  eapply aur_ithread_bind_r_eq; [cleft; exact Htest | cbv beta].
  destruct (CSLSyntax.is_true condition); exact Hbranch.
Qed.

(** *** Raw source-flow while rules

    These are stated over raw [World CEff] events and expose the option
    flow directly; they make no claim about scheduled liveness. *)

Lemma aul_csl_raw_while : forall test body condition w w' φ ψ,
    <[ {denote_exp test}, w |= φ AU AX done= condition w ]> ->
    CSLSyntax.is_true condition = true ->
    <[ {denote_flow body}, w |= φ AU AX done= {Some tt} w' ]> ->
    not_done w' ->
    <( {denote_flow (CWhile test body)}, w' |= φ AU ψ )> ->
    <( {denote_flow (CWhile test body)}, w |= φ AU ψ )>.
Proof.
  intros test body condition w w' φ ψ Htest Htrue Hbody Hnd Hloop.
  rewrite denote_flow_cwhile in *.
  eapply aul_iter_next with (R := fun (_ : unit) w0 => w0 = w').
  - unfold cwhile_iteration.
    eapply aur_bind_r_eq; [exact Htest |].
    rewrite Htrue.
    eapply aur_bind_r_eq; [exact Hbody |].
    cleft; apply axr_ret; auto.
    exists tt; split; auto.
  - intros [] w0 ->; exact Hloop.
Qed.

Lemma aul_csl_raw_while_false : forall test body condition w φ ψ,
    <[ {denote_exp test}, w |= φ AU AX done= condition w ]> ->
    CSLSyntax.is_true condition = false ->
    <( {Ret (Some tt) : ictree CEff (option unit)}, w |= ψ )> ->
    <( {denote_flow (CWhile test body)}, w |= φ AU ψ )>.
Proof.
  intros test body condition w φ ψ Htest Hfalse Hret.
  pose proof Htest as Htest_not_done.
  apply aur_not_done in Htest_not_done.
  rewrite denote_flow_cwhile, unfold_iter.
  eapply aul_bind_r_eq.
  - unfold cwhile_iteration.
    eapply aur_bind_r_eq; [exact Htest |].
    rewrite Hfalse.
    cleft; apply axr_ret; [exact Htest_not_done | split; reflexivity].
  - cbn; cleft; exact Hret.
Qed.

Lemma aul_csl_raw_while_halt : forall test body condition w w' φ ψ,
    <[ {denote_exp test}, w |= φ AU AX done= condition w ]> ->
    CSLSyntax.is_true condition = true ->
    <[ {denote_flow body}, w |= φ AU AX done= {None} w' ]> ->
    not_done w' ->
    <( {Ret None : ictree CEff (option unit)}, w' |= ψ )> ->
    <( {denote_flow (CWhile test body)}, w |= φ AU ψ )>.
Proof.
  intros test body condition w w' φ ψ Htest Htrue Hbody Hnd Hret.
  rewrite denote_flow_cwhile, unfold_iter.
  eapply aul_bind_r_eq.
  - unfold cwhile_iteration.
    eapply aur_bind_r_eq; [exact Htest |].
    rewrite Htrue.
    eapply aur_bind_r_eq; [exact Hbody |].
    cleft; apply axr_ret; auto.
  - cbn; cleft; exact Hret.
Qed.

Lemma aur_csl_raw_while : forall test body condition w w' φ ψ,
    <[ {denote_exp test}, w |= φ AU AX done= condition w ]> ->
    CSLSyntax.is_true condition = true ->
    <[ {denote_flow body}, w |= φ AU AX done= {Some tt} w' ]> ->
    not_done w' ->
    <[ {denote_flow (CWhile test body)}, w' |= φ AU AX ψ ]> ->
    <[ {denote_flow (CWhile test body)}, w |= φ AU AX ψ ]>.
Proof.
  intros test body condition w w' φ ψ Htest Htrue Hbody Hnd Hloop.
  rewrite denote_flow_cwhile in *.
  eapply aur_iter_next with (R := fun (_ : unit) w0 => w0 = w').
  - unfold cwhile_iteration.
    eapply aur_bind_r_eq; [exact Htest |].
    rewrite Htrue.
    eapply aur_bind_r_eq; [exact Hbody |].
    cleft; apply axr_ret; auto.
    exists tt; split; auto.
  - intros [] w0 ->; exact Hloop.
Qed.

Lemma aur_csl_raw_while_false : forall test body condition w φ ψ,
    <[ {denote_exp test}, w |= φ AU AX done= condition w ]> ->
    CSLSyntax.is_true condition = false ->
    <[ {Ret (Some tt) : ictree CEff (option unit)}, w |= AX ψ ]> ->
    <[ {denote_flow (CWhile test body)}, w |= φ AU AX ψ ]>.
Proof.
  intros test body condition w φ ψ Htest Hfalse Hret.
  pose proof Htest as Htest_not_done.
  apply aur_not_done in Htest_not_done.
  rewrite denote_flow_cwhile, unfold_iter.
  eapply aur_bind_r_eq.
  - unfold cwhile_iteration.
    eapply aur_bind_r_eq; [exact Htest |].
    rewrite Hfalse.
    cleft; apply axr_ret; [exact Htest_not_done | split; reflexivity].
  - cbn; cleft; exact Hret.
Qed.

Lemma ag_csl_raw_while : forall test body (R : World CEff -> Prop) w φ,
    R w ->
    (forall w,
        R w ->
        <( {denote_flow (CWhile test body)}, w |= φ )> /\
        <[ {cwhile_iteration test body tt}, w |= AX (φ AU AX done
             {fun lr w' => exists i' : unit, lr = inl i' /\ R w'}) ]>) ->
    <( {denote_flow (CWhile test body)}, w |= AG φ )>.
Proof.
  intros test body R w φ HR Hstep.
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
    (f : World CEff -> nat) w φ ψ,
    not_done w ->
    Ri w ->
    (forall w,
        not_done w ->
        Ri w ->
        <( {cwhile_iteration test body tt}, w |= φ AU ψ )> \/
        <[ {cwhile_iteration test body tt}, w |= φ AU AX done
             {fun lr w' => exists i' : unit,
                lr = inl i' /\ not_done w' /\ Ri w' /\ f w' < f w} ]>) ->
    <( {denote_flow (CWhile test body)}, w |= φ AU ψ )>.
Proof.
  intros test body Ri f w φ ψ Hnd HRi Hstep.
  rewrite denote_flow_cwhile.
  apply (aul_iter_nat (fun (_ : unit) w => Ri w) (fun _ w => f w) tt w
           (cwhile_iteration test body)); auto.
Qed.

(** *** Scheduled assignment rules *)

Lemma aur_csl_nd_assign_lit : forall name n s w ψ R,
    <( {log (inl (add name n (csl_context s)) : CSLObs (nat * nat))}, w |= ψ )> ->
    R (tt, csl_set_context s (add name n (csl_context s)))
      (Obs (Log (inl (add name n (csl_context s)) : CSLObs (nat * nat))) tt) ->
    <[ {run_nd (CAssign name (CLit n)) s}, w |= ψ AU AX done R ]>.
Proof.
  intros name n s w ψ R Hlog HR.
  pose proof (ticll_not_done unit _ _ _ Hlog) as Hnd.
  rewrite run_nd_unfold.
  rewrite ((interp_schedule_nd_equ sh) 1 _
    ([Ret tt]%vector @ Fin.F1 :=
      (source_get >>= fun ctx => source_put (add name n ctx) >>= fun _ => Ret tt))
    (Some Fin.F1) s
    (cons_pool_equ _ _ _ _ (denote_assign_lit name n) (pool_equ_refl _))).
  rewrite interp_nd_get_ctx; cbv beta.
  rewrite interp_nd_put_ctx.
  eapply aur_log.
  - rewrite (interp_schedule_nd_ret sh 0 _ Fin.F1 _) by reflexivity.
    rewrite interp_schedule_nd_empty.
    cleft; apply axr_ret; [constructor | exact HR].
  - now apply ticll_bind_l.
Qed.

Lemma aul_csl_nd_assign_lit : forall name n s w ψ φ,
    <( {log (inl (add name n (csl_context s)) : CSLObs (nat * nat))}, w |= ψ )> ->
    <( {Ret (tt, csl_set_context s (add name n (csl_context s)))},
       {Obs (Log (inl (add name n (csl_context s)) : CSLObs (nat * nat))) tt} |= φ )> ->
    <( {run_nd (CAssign name (CLit n)) s}, w |= ψ AU φ )>.
Proof.
  intros name n s w ψ φ Hlog Hret.
  rewrite run_nd_unfold.
  rewrite ((interp_schedule_nd_equ sh) 1 _
    ([Ret tt]%vector @ Fin.F1 :=
      (source_get >>= fun ctx => source_put (add name n ctx) >>= fun _ => Ret tt))
    (Some Fin.F1) s
    (cons_pool_equ _ _ _ _ (denote_assign_lit name n) (pool_equ_refl _))).
  rewrite interp_nd_get_ctx; cbv beta.
  rewrite interp_nd_put_ctx.
  cright.
  apply anl_log.
  - rewrite (interp_schedule_nd_ret sh 0 _ Fin.F1 _) by reflexivity.
    rewrite interp_schedule_nd_empty.
    cleft; exact Hret.
  - now apply ticll_bind_l.
Qed.

(** *** Scheduler-visible and observed-scheduler bridges *)

Corollary sbisim_scheduled_visible (p q : CProg unit) :
  denote p ~ denote q ->
  scheduled_visible p ~ scheduled_visible q.
Proof.
  intro Hpq.
  unfold scheduled_visible.
  apply sbisim_schedule.
  intro i.
  dependent destruction i.
  - exact Hpq.
  - inversion i.
Qed.

Definition scheduled_observed (p : CProg unit) : observed_completed sE :=
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

    The generic pool rules of [ICTree.Logic.Yield] specialized to source
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
  run_rr_pool ps (Some i) cursor s ~ emit_list logs (run_rr_pool ps None cursor s').
Proof. exact (segment_pool_rr_loop sh n (csl_pool ps) i cursor s logs s'). Qed.

Lemma run_nd_pool_select {n} (ps : Vector.t (CProg unit) (S n)) (s : SSig) :
  run_nd_pool ps None s ~ Br n (fun i => run_nd_pool ps (Some i) s).
Proof. exact (interp_schedule_nd_select sh n (csl_pool ps) s). Qed.

Lemma run_rr_pool_select {n} (ps : Vector.t (CProg unit) (S n)) cursor (s : SSig) :
  run_rr_pool ps None cursor s ~ run_rr_pool ps (Some (rr_pick n cursor)) (S cursor) s.
Proof. exact (interp_schedule_rr_select sh n (csl_pool ps) cursor s). Qed.

Lemma ag_csl_nd_invariance {G n} (ps : Vector.t (CProg unit) (S n))
    (Inv : G -> SSig -> Prop) (φ : ticllW (CSLObs (nat * nat))) :
  ClosedTurns sh (csl_pool ps) Inv ->
  (forall g s focus w, Inv g s -> not_done w ->
     <( {run_nd_pool ps focus s}, {w} |= φ )>) ->
  forall g s focus w, Inv g s -> not_done w ->
    <( {run_nd_pool ps focus s}, {w} |= AG φ )>.
Proof. exact (ag_pool_nd_invariance sh (csl_pool ps) Inv φ). Qed.

Lemma ag_csl_rr_invariance {G n} (ps : Vector.t (CProg unit) (S n))
    (Inv : G -> SSig -> Prop) (φ : ticllW (CSLObs (nat * nat))) :
  ClosedTurns sh (csl_pool ps) Inv ->
  (forall g s focus cursor w, Inv g s -> not_done w ->
     <( {run_rr_pool ps focus cursor s}, {w} |= φ )>) ->
  forall g s focus cursor w, Inv g s -> not_done w ->
    <( {run_rr_pool ps focus cursor s}, {w} |= AG φ )>.
Proof. exact (ag_pool_rr_invariance sh (csl_pool ps) Inv φ). Qed.

Lemma aul_csl_nd_eventually {G V n} (ps : Vector.t (CProg unit) (S n))
    (Inv : G -> SSig -> Prop) (rank : G -> V) (ltV : V -> V -> Prop)
    (P : CSLObs (nat * nat) -> Prop) :
  well_founded ltV -> RankedTurns sh (csl_pool ps) Inv rank ltV P ->
  forall g s focus w, Inv g s -> not_done w ->
    <( {run_nd_pool ps focus s}, {w} |= AF visW {P} )>.
Proof. exact (aul_pool_nd_eventually sh (csl_pool ps) Inv rank ltV P). Qed.

Lemma aul_csl_rr_eventually {G V n} (ps : Vector.t (CProg unit) (S n))
    (Inv : G -> SSig -> Prop) (rank : G -> V) (ltV : V -> V -> Prop)
    (P : CSLObs (nat * nat) -> Prop) :
  well_founded ltV -> RankedTurns sh (csl_pool ps) Inv rank ltV P ->
  forall g s focus cursor w, Inv g s -> not_done w ->
    <( {run_rr_pool ps focus cursor s}, {w} |= AF visW {P} )>.
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
  rewrite (interp_schedule_rr_ret sh 2 _ (Fin.FS (Fin.FS Fin.F1)) 0 s) by reflexivity.
  cbn [Vector.replace Vector.caseS'].
  rewrite !vector_remove_tail, vector_remove_head.
  reflexivity.
Qed.

(** The scheduler-visible view exhibits both [Spawn] events before the
    unfocused two-worker pool. *)
Lemma scheduled_visible_two_forks (p q : CProg unit) :
  scheduled_visible (CBind (CFork p) (fun _ => CBind (CFork q) (fun _ => CRet tt))) ~
  Vis (inr (inl Spawn) : yieldE + (spawnE + sE)) (fun _ =>
  Vis (inr (inl Spawn) : yieldE + (spawnE + sE)) (fun _ =>
    schedule 2 [denote q; denote p]%vector None)).
Proof.
  unfold scheduled_visible.
  rewrite (schedule_pool_proper 1 _ _ (Some Fin.F1)
    (cons_pool_equ _ _ _ _ (denote_fork_bind p (fun _ => CBind (CFork q) (fun _ => CRet tt)))
      (pool_equ_refl _))).
  rewrite (ictree_eta (schedule 1 _ (Some Fin.F1))).
  erewrite schedule_focused_fork by reflexivity.
  apply sb_vis; intros [].
  cbn [Vector.replace Vector.caseS'].
  rewrite (schedule_pool_proper 2 _
    [denote p; Vis (inr (inl Fork))
      (fun child : bool => if child then denote q else denote (CRet tt))]%vector
    (Some (Fin.FS Fin.F1))
    (cons_pool_equ _ _ _ _ (reflexivity _)
      (cons_pool_equ _ _ _ _ (denote_fork_bind q (fun _ => CRet tt)) (pool_equ_refl _)))).
  rewrite (ictree_eta (schedule 2 _ (Some (Fin.FS Fin.F1)))).
  erewrite schedule_focused_fork by reflexivity.
  apply sb_vis; intros [].
  cbn [Vector.replace Vector.caseS'].
  rewrite (schedule_pool_proper 3 _ [denote q; denote p; Ret tt]%vector
    (Some (Fin.FS (Fin.FS Fin.F1)))
    (cons_pool_equ _ _ _ _ (reflexivity _)
      (cons_pool_equ _ _ _ _ (reflexivity _)
        (cons_pool_equ _ _ _ _ denote_ret_unit (pool_equ_refl _))))).
  rewrite (ictree_eta (schedule 3 _ (Some (Fin.FS (Fin.FS Fin.F1))))).
  erewrite schedule_focused_ret by reflexivity.
  rewrite sb_guard, !vector_remove_tail, vector_remove_head.
  reflexivity.
Qed.
