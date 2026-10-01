(** * The canonical CSL source language.

    Syntax ([CProg]), its denotation into threads over the CSL effects, the
    source-instruction execution equations under both schedulers, the
    exact first-yield segment rules, and the structural Ticl rules stated over
    source programs.  Every law here specializes an effect-level law of
    [ICTree.Interp.CSL.Mod]. *)

From TICL Require Export ICTree.Interp.CSL.Mod.

From Stdlib Require Import List Arith.PeanoNat Lia Fin Vector
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From ExtLib Require Import Data.Monads.StateMonad.
From Coinduction Require Import coinduction lattice tactics.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Trans ICTree.Trace
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Events.Heap
  ICTree.Interp.State.Mod ICTree.Interp.Refine
  ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin ICTree.Interp.Yield.Nondeterministic
  ICTree.Logic.Trans ICTree.Logic.AX ICTree.Logic.AF ICTree.Logic.AG
  ICTree.Logic.Bind ICTree.Logic.State ICTree.Logic.CanStep
  Logic.World Logic.Core Utils.Vectors.

Import ICtree ICTreeNotations TiclNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

(** ** Syntax *)

Module CSLSyntax.
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
  | CCAS (a expected desired : nat) : CProg bool.
End CSLSyntax.
Export CSLSyntax.

(** ** Denotation *)

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
  end.

Definition denote (p : CProg unit) : thread sE :=
  denote_flow p;; Ret tt.

Lemma denote_flow_branchfree {A} (p : CProg A) : BranchFree (denote_flow p).
Proof.
  induction p as [a|a v|q v| |body IH|A x|A B body IH next IHnext|A body IH|size|base
    |a expected desired];
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
    Vis (inr (inr (inr (Log (tag,value))))) (fun _ => K (Some tt)).
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

(** Runners start from explicit managed memory: [managed_empty] for a fresh
    program, or an explicit [(h,allocs)] for preallocated data. *)
Definition run_rr (p : CProg unit) (memory : ManagedHeap) (c : nat)
  : ictreeW (indexed (nat * nat)) (unit * SSig) :=
  interp_schedule_rr sh 1 [denote p]%vector (Some Fin.F1) 0 (memory,c).

Definition run_nd (p : CProg unit) (memory : ManagedHeap) (c : nat)
  : ictreeW (indexed (nat * nat)) (unit * SSig) :=
  interp_schedule_nd sh 1 [denote p]%vector (Some Fin.F1) (memory,c).

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
  apply ((interp_schedule_rr_user_bind sh) n ts i _ (inr (Log (q,v)))
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

Lemma run_rr_fork_bind (p : CProg unit) (next : unit -> CProg unit) memory c :
  run_rr (CBind (CFork p) next) memory c ~
  interp_schedule_rr sh 2 [denote p; denote (next tt)]%vector
    (Some (Fin.FS Fin.F1)) 0 (memory,c).
Proof.
  unfold run_rr.
  assert (Hpool : pool_equ [denote (CBind (CFork p) next)]%vector
    [Vis (inr (inl Fork))
      (fun child : bool => if child then denote p else denote (next tt))]%vector).
  { apply cons_pool_equ; [apply denote_fork_bind|apply pool_equ_refl]. }
  rewrite (interp_schedule_rr_equ sh 1 _ _ (Some Fin.F1) 0 (memory,c) Hpool).
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
  apply ((interp_schedule_nd_user_bind sh) n ts i _ (inr (Log (q,v)))
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
  a v (K : option unit -> thread sE) m h allocs c :
  h a <> None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
    (Some i) m ((upd h a v,allocs),c).
Proof.
  intro Present.
  pose proof ((interp_heap_wr_present (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) a h allocs c v
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
  a v (K : option unit -> thread sE) h allocs c :
  h a <> None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),c) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
    (Some i) ((upd h a v,allocs),c).
Proof.
  intro Present.
  pose proof ((interp_heap_wr_present (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) a h allocs c v
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
  a value (K : option nat -> thread sE) m h allocs c :
  h a = Some value ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some value)) (Some i) m ((h,allocs),c).
Proof.
  intro Lookup.
  pose proof ((interp_heap_rd (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) a h allocs c value
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
  a value (K : option nat -> thread sE) h allocs c :
  h a = Some value ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),c) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some value)) (Some i) ((h,allocs),c).
Proof.
  intro Lookup.
  pose proof ((interp_heap_rd (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) a h allocs c value
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
  tag value (K : option unit -> thread sE) m memory c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,c) ~
  (log (stamp (tag,value) c);;
   interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)).
Proof.
  pose proof (interp_indexed_emit heap_handler (tag,value) memory c
    (fun x : unit => (Ret x : ictree sE unit))) as Hemit.
  rewrite bind_ret_r in Hemit.
  assert (Hstate : interp_state sh (semit tag value) (memory,c) ~
    (log (stamp (tag,value) c);; Ret (tt,(memory,S c)))).
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
  a expected desired current (K : option bool -> thread sE) m h allocs c :
  h a = Some current ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),c) ~
  (if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),c)).
Proof.
  intro Lookup; rewrite interp_rr_cas.
  destruct (Nat.eqb current expected) eqn:Cmp.
  - apply Nat.eqb_eq in Cmp; subst current.
    pose proof ((interp_heap_cas_success (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) a expected desired h allocs c
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
    pose proof ((interp_heap_cas_failure (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) a expected desired current h allocs c
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
  size base (K : option nat -> thread sE) m h allocs c :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c) ~
  interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c).
Proof.
  intros Pos Base Free First.
  pose proof ((interp_heap_alloc_first (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) h allocs size base c
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
  a (K : option nat -> thread sE) m h allocs c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),c) ~
  (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_rd_stuck (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap)))
    a h allocs c Missing) as Hstate.
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
  a v (K : option unit -> thread sE) m h allocs c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),c) ~
  (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_wr_stuck (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap)))
    a v h allocs c Missing) as Hstate.
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
  a expected desired (K : option bool -> thread sE) m h allocs c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),c) ~
  (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_cas_missing (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap)))
    a expected desired h allocs c (fun b : bool => (Ret b : ictree sE bool)) Missing) as Hstate.
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
  tag value (K : option unit -> thread sE) memory c :
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,c) ~
  (log (stamp (tag,value) c);;
   interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)).
Proof.
  pose proof (interp_indexed_emit heap_handler (tag,value) memory c
    (fun x : unit => (Ret x : ictree sE unit))) as Hemit.
  rewrite bind_ret_r in Hemit.
  assert (Hstate : interp_state sh (semit tag value) (memory,c) ~
    (log (stamp (tag,value) c);; Ret (tt,(memory,S c)))).
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
  a expected desired current (K : option bool -> thread sE) h allocs c :
  h a = Some current ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),c) ~
  (if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),c)).
Proof.
  intro Lookup; rewrite interp_nd_source_cas.
  destruct (Nat.eqb current expected) eqn:Cmp.
  - apply Nat.eqb_eq in Cmp; subst current.
    pose proof ((interp_heap_cas_success (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) a expected desired h allocs c
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
    pose proof ((interp_heap_cas_failure (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) a expected desired current h allocs c
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
  size base (K : option nat -> thread sE) h allocs c :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c) ~
  interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c).
Proof.
  intros Pos Base Free First.
  pose proof ((interp_heap_alloc_first (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) h allocs size base c
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
  a (K : option nat -> thread sE) h allocs c :
  h a = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),c) ~
  (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_rd_stuck (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap))) a h allocs c Missing) as Hstate.
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
  a v (K : option unit -> thread sE) h allocs c :
  h a = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),c) ~
  (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_wr_stuck (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap)))
    a v h allocs c Missing) as Hstate.
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
  a expected desired (K : option bool -> thread sE) h allocs c :
  h a = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),c) ~
  (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Missing.
  pose proof ((interp_heap_cas_missing (h_indexed (A:=(nat * nat)) (Sigma:=ManagedHeap)))
    a expected desired h allocs c (fun b : bool => (Ret b : ictree sE bool)) Missing) as Hstate.
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
  (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) c :
  managed_free memory base = Some memory' ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) cursor (memory,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
    (Some i) cursor (memory',c).
Proof.
  intro Free.
  rewrite (interp_schedule_rr_equ sh (S n) _ _ (Some i) cursor (memory,c)
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_rr_heap_free n ts i base (fun _ => K (Some tt)) cursor memory memory' c Free).
Qed.

Lemma interp_rr_free_invalid n (ts : pool sE (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE) cursor (memory : ManagedHeap) c :
  managed_free memory base = None ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) cursor (memory,c) ~
  (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Invalid.
  rewrite (interp_schedule_rr_equ sh (S n) _ _ (Some i) cursor (memory,c)
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_rr_heap_free_invalid n ts i base (fun _ => K (Some tt)) cursor memory c Invalid).
Qed.

Lemma interp_nd_source_free n (ts : pool sE (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE) (memory memory' : ManagedHeap) c :
  managed_free memory base = Some memory' ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) (memory,c) ~
  interp_schedule_nd sh (S n) (ts @ i := K (Some tt))
    (Some i) (memory',c).
Proof.
  intro Free.
  rewrite ((interp_schedule_nd_equ sh) (S n) _ _ (Some i) (memory,c)
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_nd_heap_free n ts i base (fun _ => K (Some tt)) memory memory' c Free).
Qed.

Lemma interp_nd_source_free_invalid n (ts : pool sE (S n)) (i : Fin.t (S n)) base
  (K : option unit -> thread sE) (memory : ManagedHeap) c :
  managed_free memory base = None ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (CFree base) >>= K))
    (Some i) (memory,c) ~
  (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Invalid.
  rewrite ((interp_schedule_nd_equ sh) (S n) _ _ (Some i) (memory,c)
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_free_raw_heap_free base K))).
  exact (interp_nd_heap_free_invalid n ts i base (fun _ => K (Some tt)) memory c Invalid).
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
  h allocs c logs target sigma' :
  h a = Some v ->
  segment_to sh csl_equ (K (Some v)) ((h,allocs),c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CRead a) >>= K) ((h,allocs),c) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HRead a)))) (fun v => K (Some v))).
  - apply source_raw_read_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HRead a)))) (fun v => K (Some v)))
      ((h,allocs),c) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list]; rewrite (heap_handler_rd_some a h allocs c v Hr); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_write a v (K : option unit -> thread sE)
  h allocs c logs target sigma' :
  h a <> None ->
  segment_to sh csl_equ (K (Some tt)) ((upd h a v,allocs),c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CWrite a v) >>= K) ((h,allocs),c) logs target sigma'.
Proof.
  intros Hp (residual & Hseg & Htail).
  destruct (h a) as [w|] eqn:Hw; [|contradiction].
  exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HWrite a v)))) (fun _ => K (Some tt))).
  - apply source_raw_write_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HWrite a v)))) (fun _ => K (Some tt)))
      ((h,allocs),c) ([] ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite (heap_handler_wr_some a h allocs c v w Hw); reflexivity.
  - reflexivity.
Qed.

(** The raw handler equation [h_indexed_log] is the response certificate here;
    [interp_indexed_emit] is an interpretation equation and cannot discharge
    this premise. *)
Lemma exact_source_emit tag block (K : option unit -> thread sE)
  (memory : ManagedHeap) c logs target sigma' :
  segment_to sh csl_equ (K (Some tt)) (memory,S c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CEmit tag block) >>= K) (memory,c)
    (stamp (tag,block) c :: logs) target sigma'.
Proof.
  intros (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inr (Log (tag,block))))) (fun _ => K (Some tt))).
  - apply source_raw_emit_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inr (Log (tag,block))))) (fun _ => K (Some tt)))
      (memory,c) ([stamp (tag,block) c] ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite (h_indexed_log (Sigma:=ManagedHeap) (tag,block) memory c);
      reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_cas_success a expected desired
  (K : option bool -> thread sE) h allocs c logs target sigma' :
  h a = Some expected ->
  segment_to sh csl_equ (K (Some true)) ((upd h a desired,allocs),c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CCAS a expected desired) >>= K)
    ((h,allocs),c) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b))).
  - apply source_raw_cas_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b)))
      ((h,allocs),c) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list];
      rewrite (heap_handler_cas_success a expected desired h allocs c Hr); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_cas_failure a expected desired current
  (K : option bool -> thread sE) h allocs c logs target sigma' :
  h a = Some current -> current <> expected ->
  segment_to sh csl_equ (K (Some false)) ((h,allocs),c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CCAS a expected desired) >>= K)
    ((h,allocs),c) logs target sigma'.
Proof.
  intros Hr Hne (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b))).
  - apply source_raw_cas_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b)))
      ((h,allocs),c) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list];
      rewrite (heap_handler_cas_failure a expected desired current h allocs c Hr Hne);
      reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_free base (K : option unit -> thread sE)
  (memory memory' : ManagedHeap) c logs target sigma' :
  managed_free memory base = Some memory' ->
  segment_to sh csl_equ (K (Some tt)) (memory',c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CFree base) >>= K) (memory,c) logs target sigma'.
Proof.
  intros Free (residual & Hseg & Htail).
  exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HFree base)))) (fun _ => K (Some tt))).
  - apply source_raw_free_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HFree base)))) (fun _ => K (Some tt)))
      (memory,c) ([] ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite (heap_handler_free base memory memory' c Free); reflexivity.
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
  a value (K : option nat -> thread sE) h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs c Lookup); reflexivity.
Qed.

Lemma anr_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs c Lookup); reflexivity.
Qed.

Lemma aul_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs c Lookup); reflexivity.
Qed.

Lemma aur_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs c Lookup); reflexivity.
Qed.

Lemma ag_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) ((h,allocs),c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) ((h,allocs),c)}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h allocs c Lookup); reflexivity.
Qed.

Lemma anl_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h allocs c Lookup); reflexivity.
Qed.

Lemma anr_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h allocs c Lookup); reflexivity.
Qed.

Lemma aul_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h allocs c Lookup); reflexivity.
Qed.

Lemma aur_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h allocs c Lookup); reflexivity.
Qed.

Lemma ag_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m ((h,allocs),c)}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h allocs c Lookup); reflexivity.
Qed.

Lemma anl_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) ((upd h a v,allocs),c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h allocs c Present); reflexivity.
Qed.

Lemma anr_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) ((upd h a v,allocs),c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h allocs c Present); reflexivity.
Qed.

Lemma aul_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) ((upd h a v,allocs),c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h allocs c Present); reflexivity.
Qed.

Lemma aur_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) ((upd h a v,allocs),c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h allocs c Present); reflexivity.
Qed.

Lemma ag_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) ((h,allocs),c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) ((upd h a v,allocs),c)}, {w} |= AG φ )>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h allocs c Present); reflexivity.
Qed.

Lemma anl_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m ((upd h a v,allocs),c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h allocs c Present); reflexivity.
Qed.

Lemma anr_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m ((upd h a v,allocs),c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h allocs c Present); reflexivity.
Qed.

Lemma aul_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m ((upd h a v,allocs),c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h allocs c Present); reflexivity.
Qed.

Lemma aur_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m ((upd h a v,allocs),c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h allocs c Present); reflexivity.
Qed.

Lemma ag_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m ((upd h a v,allocs),c)}, {w} |= AG φ )>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h allocs c Present); reflexivity.
Qed.

(** ** Valid whole-block free; [managed_free] covers the null no-op. *)

Lemma anl_csl_nd_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) (memory memory' : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory',c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Free.
  rewrite (interp_nd_source_free n ts i base K memory memory' c Free); reflexivity.
Qed.

Lemma anr_csl_nd_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory',c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Free.
  rewrite (interp_nd_source_free n ts i base K memory memory' c Free); reflexivity.
Qed.

Lemma aul_csl_nd_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) (memory memory' : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory',c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Free.
  rewrite (interp_nd_source_free n ts i base K memory memory' c Free); reflexivity.
Qed.

Lemma aur_csl_nd_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory',c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Free.
  rewrite (interp_nd_source_free n ts i base K memory memory' c Free); reflexivity.
Qed.

Lemma ag_csl_nd_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory',c)}, {w} |= AG φ )>)).
Proof.
  intros Free.
  rewrite (interp_nd_source_free n ts i base K memory memory' c Free); reflexivity.
Qed.

Lemma anl_csl_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) cursor (memory',c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Free.
  rewrite (interp_rr_free n ts i base K cursor memory memory' c Free); reflexivity.
Qed.

Lemma anr_csl_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) cursor (memory',c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Free.
  rewrite (interp_rr_free n ts i base K cursor memory memory' c Free); reflexivity.
Qed.

Lemma aul_csl_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) cursor (memory',c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Free.
  rewrite (interp_rr_free n ts i base K cursor memory memory' c Free); reflexivity.
Qed.

Lemma aur_csl_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) cursor (memory',c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Free.
  rewrite (interp_rr_free n ts i base K cursor memory memory' c Free); reflexivity.
Qed.

Lemma ag_csl_rr_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : option unit -> thread sE) cursor (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFree base) >>= K)) (Some i) cursor (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) cursor (memory',c)}, {w} |= AG φ )>)).
Proof.
  intros Free.
  rewrite (interp_rr_free n ts i base K cursor memory memory' c Free); reflexivity.
Qed.

Lemma anl_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs c Pos Base Free First); reflexivity.
Qed.

Lemma anr_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs c Pos Base Free First); reflexivity.
Qed.

Lemma aul_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs c Pos Base Free First); reflexivity.
Qed.

Lemma aur_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs c Pos Base Free First); reflexivity.
Qed.

Lemma ag_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c)}, {w} |= AG φ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h allocs c Pos Base Free First); reflexivity.
Qed.

Lemma anl_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h allocs c Pos Base Free First); reflexivity.
Qed.

Lemma anr_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h allocs c Pos Base Free First); reflexivity.
Qed.

Lemma aul_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h allocs c Pos Base Free First); reflexivity.
Qed.

Lemma aur_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h allocs c Pos Base Free First); reflexivity.
Qed.

Lemma ag_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c)}, {w} |= AG φ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h allocs c Pos Base Free First); reflexivity.
Qed.

Lemma anl_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs c Lookup); reflexivity.
Qed.

Lemma anr_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs c Lookup); reflexivity.
Qed.

Lemma aul_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs c Lookup); reflexivity.
Qed.

Lemma aur_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs c Lookup); reflexivity.
Qed.

Lemma ag_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) ((h,allocs),c)}, {w} |= AG φ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) ((upd h a desired,allocs),c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) ((h,allocs),c)}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h allocs c Lookup); reflexivity.
Qed.

Lemma anl_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h allocs c Lookup); reflexivity.
Qed.

Lemma anr_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h allocs c Lookup); reflexivity.
Qed.

Lemma aul_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h allocs c Lookup); reflexivity.
Qed.

Lemma aur_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h allocs c Lookup); reflexivity.
Qed.

Lemma ag_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= AG φ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m ((upd h a desired,allocs),c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m ((h,allocs),c)}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h allocs c Lookup); reflexivity.
Qed.

(** ** Source flow and pool structure *)

Lemma anl_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (memory,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (memory,c)); reflexivity.
Qed.

Lemma anr_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (memory,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (memory,c)); reflexivity.
Qed.

Lemma aul_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (memory,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (memory,c)); reflexivity.
Qed.

Lemma aur_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (memory,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (memory,c)); reflexivity.
Qed.

Lemma ag_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (memory,c)); reflexivity.
Qed.

Lemma anl_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (memory,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (memory,c)); reflexivity.
Qed.

Lemma anr_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (memory,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (memory,c)); reflexivity.
Qed.

Lemma aul_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (memory,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (memory,c)); reflexivity.
Qed.

Lemma aur_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (memory,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (memory,c)); reflexivity.
Qed.

Lemma ag_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (memory,c)); reflexivity.
Qed.

Lemma anl_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (memory,c)); reflexivity.
Qed.

Lemma anr_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (memory,c)); reflexivity.
Qed.

Lemma aul_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (memory,c)); reflexivity.
Qed.

Lemma aur_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (memory,c)); reflexivity.
Qed.

Lemma ag_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (memory,c)); reflexivity.
Qed.

Lemma anl_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (memory,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (memory,c)); reflexivity.
Qed.

Lemma anr_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (memory,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (memory,c)); reflexivity.
Qed.

Lemma aul_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (memory,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (memory,c)); reflexivity.
Qed.

Lemma aur_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (memory,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (memory,c)); reflexivity.
Qed.

Lemma ag_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (memory,c)); reflexivity.
Qed.

Lemma anl_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (memory,c)); reflexivity.
Qed.

Lemma anr_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (memory,c)); reflexivity.
Qed.

Lemma aul_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (memory,c)); reflexivity.
Qed.

Lemma aur_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (memory,c)); reflexivity.
Qed.

Lemma ag_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (memory,c)); reflexivity.
Qed.

Lemma anl_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (memory,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (memory,c)); reflexivity.
Qed.

Lemma anr_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (memory,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (memory,c)); reflexivity.
Qed.

Lemma aul_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (memory,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (memory,c)); reflexivity.
Qed.

Lemma aur_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (memory,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (memory,c)); reflexivity.
Qed.

Lemma ag_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (memory,c)); reflexivity.
Qed.

Lemma anl_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (memory,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (memory,c)); reflexivity.
Qed.

Lemma anr_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (memory,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (memory,c)); reflexivity.
Qed.

Lemma aul_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (memory,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (memory,c)); reflexivity.
Qed.

Lemma aur_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (memory,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (memory,c)); reflexivity.
Qed.

Lemma ag_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (memory,c)); reflexivity.
Qed.

Lemma anl_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (memory,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (memory,c)); reflexivity.
Qed.

Lemma anr_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (memory,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (memory,c)); reflexivity.
Qed.

Lemma aul_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (memory,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (memory,c)); reflexivity.
Qed.

Lemma aur_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (memory,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (memory,c)); reflexivity.
Qed.

Lemma ag_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (memory,c)); reflexivity.
Qed.

(** ** Observable emission and cooperative selection *)

Lemma anl_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {w} |= φ )> /\
    <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= ψ )>)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply anl_log_iff.
Qed.

Lemma anr_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ ]> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {w} |= φ )> /\
    <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= ψ ]>)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply anr_log_iff.
Qed.

Lemma aul_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {w} |= ψ )> \/
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {w} |= φ )> /\
    <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= φ AU ψ )>))).
Proof.
  rewrite interp_nd_source_emit_log.
  apply aul_log_iff.
Qed.

Lemma aur_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {w} |= ψ ]> \/
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {w} |= φ )> /\
    <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= φ AU ψ ]>))).
Proof.
  rewrite interp_nd_source_emit_log.
  apply aur_log_iff.
Qed.

Lemma ag_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (memory,c)}, {w} |= AG φ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {w} |= φ )> /\
    <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (memory,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= AG φ )>)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply ag_log_iff.
Qed.

Lemma anl_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= ψ )>)).
Proof.
  rewrite interp_rr_emit_log.
  apply anl_log_iff.
Qed.

Lemma anr_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ ]> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {w} |= φ )> /\
    <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= ψ ]>)).
Proof.
  rewrite interp_rr_emit_log.
  apply anr_log_iff.
Qed.

Lemma aul_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {w} |= ψ )> \/
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= φ AU ψ )>))).
Proof.
  rewrite interp_rr_emit_log.
  apply aul_log_iff.
Qed.

Lemma aur_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {w} |= ψ ]> \/
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {w} |= φ )> /\
    <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= φ AU ψ ]>))).
Proof.
  rewrite interp_rr_emit_log.
  apply aur_log_iff.
Qed.

Lemma ag_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (memory,c)}, {w} |= AG φ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (memory,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= AG φ )>)).
Proof.
  rewrite interp_rr_emit_log.
  apply ag_log_iff.
Qed.

Lemma anl_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c)}, {w} |= ψ )>)).
Proof.
  rewrite interp_nd_source_yield.
  apply anl_csl_nd_select.
Qed.

Lemma anr_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ ]> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c)}, {w} |= ψ ]>)).
Proof.
  rewrite interp_nd_source_yield.
  apply anr_csl_nd_select.
Qed.

Lemma aul_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c))}, {w} |= ψ )> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c)}, {w} |= φ AU ψ )>))).
Proof.
  rewrite interp_nd_source_yield.
  apply aul_csl_nd_select.
Qed.

Lemma aur_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c))}, {w} |= ψ ]> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c)}, {w} |= φ AU ψ ]>))).
Proof.
  rewrite interp_nd_source_yield.
  apply aur_csl_nd_select.
Qed.

Lemma ag_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (memory,c)}, {w} |= AG φ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite interp_nd_source_yield.
  apply ag_csl_nd_select.
Qed.

Lemma anl_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite interp_rr_yield.
  apply anl_csl_rr_select.
Qed.

Lemma anr_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite interp_rr_yield.
  apply anr_csl_rr_select.
Qed.

Lemma aul_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m memory c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite interp_rr_yield.
  apply aul_csl_rr_select.
Qed.

Lemma aur_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite interp_rr_yield.
  apply aur_csl_rr_select.
Qed.

Lemma ag_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m memory c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite interp_rr_yield.
  apply ag_csl_rr_select.
Qed.

(** ** Finite heaps supply their constructive first-fit witness *)

Lemma anl_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c)}, {w} |= φ AN ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anl_csl_nd_alloc n ts i size base K h allocs c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anl_csl_nd_alloc n ts i size base K h allocs c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma anr_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AN ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c)}, {w} |= φ AN ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anr_csl_nd_alloc n ts i size base K h allocs c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anr_csl_nd_alloc n ts i size base K h allocs c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aul_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c)}, {w} |= φ AU ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aul_csl_nd_alloc n ts i size base K h allocs c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aul_csl_nd_alloc n ts i size base K h allocs c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aur_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c)}, {w} |= φ AU ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c)}, {w} |= φ AU ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aur_csl_nd_alloc n ts i size base K h allocs c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aur_csl_nd_alloc n ts i size base K h allocs c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma ag_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h allocs c w
  (φ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) ((h,allocs),c)}, {w} |= AG φ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (managed_alloc (h,allocs) base size,c)}, {w} |= AG φ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (ag_csl_nd_alloc n ts i size base K h allocs c w φ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (ag_csl_nd_alloc n ts i size base K h allocs c w φ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma anl_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c)}, {w} |= φ AN ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anl_csl_rr_alloc n ts i size base K m h allocs c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anl_csl_rr_alloc n ts i size base K m h allocs c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma anr_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AN ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c)}, {w} |= φ AN ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anr_csl_rr_alloc n ts i size base K m h allocs c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anr_csl_rr_alloc n ts i size base K m h allocs c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aul_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h allocs c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c)}, {w} |= φ AU ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aul_csl_rr_alloc n ts i size base K m h allocs c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aul_csl_rr_alloc n ts i size base K m h allocs c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aur_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= φ AU ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c)}, {w} |= φ AU ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aur_csl_rr_alloc n ts i size base K m h allocs c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aur_csl_rr_alloc n ts i size base K m h allocs c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma ag_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h allocs c w
  (φ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m ((h,allocs),c)}, {w} |= AG φ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (managed_alloc (h,allocs) base size,c)}, {w} |= AG φ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (ag_csl_rr_alloc n ts i size base K m h allocs c w φ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h allocs size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (ag_csl_rr_alloc n ts i size base K m h allocs c w φ Pos Base Free First)).
    apply Hall; assumption.
Qed.

(** ** Source loops: actual observations sustain AG; guard-only divergence does not *)

Lemma run_nd_emit_loop_ag tag value memory c w :
  not_done w ->
  <( {run_nd (CUntilNone (CBind (CEmit tag value)
    (fun _ => CRet (Some tt : option unit)))) memory c}, {w} |= AG ⊤ )>.
Proof.
  revert c w; coinduction R CIH; intros c w Hw.
  unfold run_nd, denote.
  change (agcbt (entailsL (unit * SSig) <[ ⊤ ]>) R
    (interp_schedule_nd sh 1
      (([Ret tt] : pool sE 1) @ Fin.F1 :=
        (denote_flow
          (CUntilNone
            (CBind (CEmit tag value) (fun _ => CRet (Some tt : option unit))))
          >>= fun _ => Ret tt))
      (Some Fin.F1) (memory,c)) w).
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

Lemma run_rr_emit_loop_ag tag value memory c w :
  not_done w ->
  <( {run_rr (CUntilNone (CBind (CEmit tag value)
    (fun _ => CRet (Some tt : option unit)))) memory c}, {w} |= AG ⊤ )>.
Proof.
  revert c w; coinduction R CIH; intros c w Hw.
  unfold run_rr, denote.
  change (agcbt (entailsL (unit * SSig) <[ ⊤ ]>) R
    (interp_schedule_rr sh 1
      (([Ret tt] : pool sE 1) @ Fin.F1 :=
        (denote_flow
          (CUntilNone
            (CBind (CEmit tag value) (fun _ => CRet (Some tt : option unit))))
          >>= fun _ => Ret tt))
      (Some Fin.F1) 0 (memory,c)) w).
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
Lemma run_nd_silent_loop_no_ag memory c w :
  ~ <( {run_nd (CUntilNone (CRet (Some tt : option unit))) memory c}, {w} |= AG ⊤ )>.
Proof.
  set (p := CUntilNone (CRet (Some tt : option unit))).
  assert (Hraw : denote p ≅ Guard (denote p)).
  { unfold p, denote.
    etransitivity; [apply source_raw_until |].
    etransitivity; [apply source_raw_ret |].
    reflexivity. }
  assert (Hguard : run_nd p memory c ≅ Guard (run_nd p memory c)).
  { unfold run_nd.
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

Lemma run_rr_silent_loop_no_ag memory c w :
  ~ <( {run_rr (CUntilNone (CRet (Some tt : option unit))) memory c}, {w} |= AG ⊤ )>.
Proof.
  set (p := CUntilNone (CRet (Some tt : option unit))).
  assert (Hraw : denote p ≅ Guard (denote p)).
  { unfold p, denote.
    etransitivity; [apply source_raw_until |].
    etransitivity; [apply source_raw_ret |].
    reflexivity. }
  assert (Hguard : run_rr p memory c ≅ Guard (run_rr p memory c)).
  { unfold run_rr.
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
