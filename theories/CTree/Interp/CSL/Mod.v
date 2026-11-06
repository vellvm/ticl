From TICL Require Import CTree.Interp.Yield.Policy.
(** * The canonical CSL effect interpreter.

    This module owns the CSL effect sum, its interpretation state and the one
    payload-polymorphic handler [sh] that combines the shared checked heap,
    the shared variable context (with context-update observations) and the
    shared indexing writer.  Everything here is stated over effects and
    trees: it does not mention CSL syntax.  The source language
    ([Lang.CoCSL.Mod]) specializes these laws to its denotation.

    Generic checked heap access, allocation search, indexed observation and
    the scheduler/segment machinery live one layer further down and are
    re-exported from here.

    The whole CSL stack is fixed at the finite branch signature [Bn]: the
    policy runner ([CTree.Interp.Yield.Policy]) only exists at [Bn], and the
    non-deterministic scheduler is instantiated at the same signature so one
    denotation serves both schedulers.  Under round robin the observations
    are [CSLObs (nat * nat) + nat]: program observations under [inl], logged
    scheduling decisions under [inr]. *)

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector.

From Coinduction Require Import all.

From TICL Require Export
  Events.HeapModel
  CTree.Events.Heap
  CTree.Events.Writer
  CTree.Events.State
  CTree.Interp.Heap
  CTree.Logic.Heap
  CTree.Trace
  CTree.Interp.Yield.Nondeterministic
  CTree.Interp.Yield.Segments
  Utils.Maps.

From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Interp.State.Mod
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.Policy
  CTree.Interp.Yield.RoundRobin
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.Trace
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.EG
  CTree.Logic.Bind
  CTree.Logic.Iter
  CTree.Logic.State
  Logic.World
  Logic.Core
  Utils.Vectors.

Import CTreeNotations TiclNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

(** ** Effects and interpretation state *)

(** [sE] is a notation, not a definition: the payload-polymorphic handler
    [sh] below is typed over [heapE +' (stateE Ctx.Ctx +' writerE A)], so
    instantiating it at the tagged payload yields this sum syntactically, and
    rewrites stated over [sE] keep matching terms elaborated through [sh]. *)
Abbreviation sE := (heapE +' (stateE Ctx.Ctx +' writerE (nat * nat))).

(** Interpretation state: the SHARED managed memory (data heap and live
    allocation extents), the SHARED variable context, and one GLOBAL
    occurrence counter for indexed emissions.  A state is
    [((h,allocs),(ctx,c))].  The context is not part of heap ownership. *)
Definition SSig : Type := (ManagedHeap * (Ctx.Ctx * nat))%type.

(** Mutation snapshots, context updates and indexed user emissions are
    distinct alternatives. Only user emissions carry occurrence indices. *)
Inductive CSLObs (A : Type) : Type :=
| CSLHeap (memory : ManagedHeap)
| CSLCtx (context : Ctx.Ctx)
| CSLEmit (emission : indexed A).
Arguments CSLHeap {A} memory.
Arguments CSLCtx {A} context.
Arguments CSLEmit {A} emission.

Definition csl_heap {A} (P : ManagedHeap -> Prop) (o : CSLObs A) : Prop :=
  match o with CSLHeap memory => P memory | _ => False end.

(** Thread effects: yield, fork, and the interpreted sum.  A notation, so
    that [thread sE Bn] and [ctree CEff Bn unit] coincide syntactically and
    the ITree [-<] instances for the components resolve without unfolding. *)
Abbreviation CEff := (yieldE +' (forkE +' sE)).

Definition csl_memory (s : SSig) : ManagedHeap := fst s.
Definition csl_context (s : SSig) : Ctx.Ctx := fst (snd s).
Definition csl_counter (s : SSig) : nat := snd (snd s).
Definition csl_set_context (s : SSig) (ctx : Ctx.Ctx) : SSig :=
  (csl_memory s, (ctx, csl_counter s)).
Definition csl_indexed {A} (P : indexed A -> Prop) (o : CSLObs A) : Prop :=
  match o with CSLEmit x => P x | _ => False end.
(** Heap and context observations carry no occurrence index and project to [0]. *)
Definition csl_index {A} (o : CSLObs A) : nat :=
  match o with CSLEmit x => indexed_index x | _ => 0 end.

(** Payload-only matching on actual labels; stamps remain internal data. *)
Definition csl_label_emits {A : Type} (P : A -> Prop)
    : @label (writerE (CSLObs A)) -> Prop :=
  log_label (csl_indexed (fun emission => P (indexed_value emission))).

Lemma csl_label_emits_emit {A : Type} (P : A -> Prop) a j :
  csl_label_emits P (obs (Log (CSLEmit (stamp a j))) tt) <-> P a.
Proof. reflexivity. Qed.

Theorem csl_fresh_implies_recurrent_emission
    {A X : Type} {B : Type -> Type}
    (P : A -> Prop)
    (P_dec : forall a, {P a} + {~ P a})
    (t : ctreeW (CSLObs A) B X)
    (w : World (writerE (CSLObs A))) :
  (forall k,
    <( t, w |=L AG
      (AF visW {csl_indexed (indexed_after P k)}) )>) ->
  recurrent_label (csl_label_emits P) t.
Proof.
  intro H; unfold csl_label_emits.
  eapply agaf_family_recurrent_label with
    (Q:=fun k => csl_indexed (indexed_after P k)) (w:=w).
  - intros [memory|ctx|emission]; cbn [csl_indexed].
    + right; tauto.
    + right; tauto.
    + apply P_dec.
  - intros k [memory|ctx|emission]; unfold csl_indexed, indexed_after; cbn; tauto.
  - intros [memory|ctx|emission].
    + exists 0; cbn [csl_indexed]; tauto.
    + exists 0; cbn [csl_indexed]; tauto.
    + exists (S (indexed_index emission)); unfold csl_indexed, indexed_after; cbn.
      intros [_ Hle]; exact (Nat.nle_succ_diag_l _ Hle).
  - exact H.
Qed.

(** Payload matching on instrumented runs ignores scheduling labels. *)
Definition csl_label_emitsW {A : Type} (P : A -> Prop)
    : @label (writerE (CSLObs A + nat)) -> Prop :=
  log_label (fair_obs (csl_indexed (fun emission => P (indexed_value emission)))).

Lemma csl_label_emitsW_emit {A : Type} (P : A -> Prop) a j :
  csl_label_emitsW P (obs (Log (inl (CSLEmit (stamp a j)))) tt) <-> P a.
Proof. reflexivity. Qed.

Theorem csl_fresh_implies_recurrent_emissionW
    {A X : Type} {B : Type -> Type}
    (P : A -> Prop) (P_dec : forall a, {P a} + {~ P a})
    (t : ctreeW (CSLObs A + nat) B X)
    (w : World (writerE (CSLObs A + nat))) :
  (forall k, <( t, w |=L AG
    (AF visW {fair_obs (csl_indexed (indexed_after P k))}) )>) ->
  recurrent_label (csl_label_emitsW P) t.
Proof.
  intro H; unfold csl_label_emitsW.
  eapply agaf_family_recurrent_label with
    (Q := fun k => fair_obs (csl_indexed (indexed_after P k))) (w := w).
  - intros [[memory|ctx|emission]|pick]; cbn [fair_obs csl_indexed].
    + right; tauto.
    + right; tauto.
    + apply P_dec.
    + right; tauto.
  - intros k [[memory|ctx|emission]|pick];
      unfold fair_obs, csl_indexed, indexed_after; cbn; tauto.
  - intros [[memory|ctx|emission]|pick].
    + exists 0; cbn [fair_obs csl_indexed]; tauto.
    + exists 0; cbn [fair_obs csl_indexed]; tauto.
    + exists (S (indexed_index emission)); unfold fair_obs, csl_indexed, indexed_after; cbn.
      intros [_ Hle]; exact (Nat.nle_succ_diag_l _ Hle).
    + exists 0; cbn [fair_obs csl_indexed]; tauto.
  - exact H.
Qed.

(** Preserve only user emissions, in order; mutation/context logs do not
    participate in occurrence-counter contracts. *)
Fixpoint csl_emissions {A} (logs : list (CSLObs A)) : list (indexed A) :=
  match logs with
  | List.nil => List.nil
  | List.cons (CSLEmit emission) rest => List.cons emission (csl_emissions rest)
  | List.cons _ rest => csl_emissions rest
  end.
Lemma csl_emissions_in {A} (emission : indexed A) logs :
  List.In emission (csl_emissions logs) <-> List.In (CSLEmit emission) logs.
Proof.
  induction logs as [|[memory|ctx|head] rest IH]; cbn [csl_emissions List.In];
    intuition congruence.
Qed.

Lemma csl_emissions_heap_prefix {A} (heaps : list ManagedHeap) (logs : list (CSLObs A)) :
  csl_emissions (List.app (List.map CSLHeap heaps) logs) = csl_emissions logs.
Proof.
  induction heaps as [|memory heaps IH]; cbn [List.map List.app csl_emissions];
    [reflexivity|exact IH].
Qed.

Lemma csl_emissions_heaps {A} (heaps : list ManagedHeap) :
  @csl_emissions A (List.map CSLHeap heaps) = List.nil.
Proof.
  induction heaps as [|memory heaps IH]; cbn [List.map csl_emissions];
    [reflexivity|exact IH].
Qed.

Definition semit (q v : nat) : ctree sE Bn unit :=
  CTree.trigger (inr1 (inr1 (Log (q,v))) : sE unit).

(** The context handler acts on the shared context exactly as [h_stateW]
    does ([Get] is silent, [Put] logs [CSLCtx] with the new context)
    and leaves memory and the indexed counter untouched. *)
Definition csl_context_handler {A : Type} :
  stateE Ctx.Ctx ~> stateT SSig (ctreeW (CSLObs A) Bn) :=
  fun _ e s =>
    match e in stateE _ X return ctreeW (CSLObs A) Bn (SSig * X) with
    | Get => Ret (s, csl_context s)
    | Put ctx' => log (CSLCtx ctx' : CSLObs A);; Ret (csl_set_context s ctx', tt)
    end.

(** The emission handler acts as [h_indexed] on the global counter: every
    [Log a] emits exactly one [CSLEmit] stamp and advances only the
    counter. *)
Definition csl_emit_handler {A : Type} :
  writerE A ~> stateT SSig (ctreeW (CSLObs A) Bn) :=
  fun _ '(Log a) s =>
    log (CSLEmit (stamp a (csl_counter s)) : CSLObs A);;
    Ret ((csl_memory s, (csl_context s, S (csl_counter s))), tt).

(** The one CSL handler: the shared checked-heap handler summed with the
    context and indexing handlers.  It is polymorphic in the observation
    payload; the tagged source language uses [nat * nat], a unary reference
    model uses [nat]. *)
Definition sh {A : Type} :
  (heapE +' (stateE Ctx.Ctx +' writerE A)) ~> stateT SSig (ctreeW (CSLObs A) Bn) :=
  h_sum (heap_handlerW CSLHeap) (h_sum csl_context_handler csl_emit_handler).

(** Raw handler equations: [Get] is silent, [Put] logs exactly the new
    context, [Log] logs exactly one stamp and advances only the counter. *)
Lemma csl_context_handler_get {A} memory ctx c :
  csl_context_handler (A:=A) _ Get (memory,(ctx,c)) ≅
    Ret ((memory,(ctx,c)),ctx).
Proof. reflexivity. Qed.

Lemma csl_context_handler_put {A} ctx' memory ctx c :
  csl_context_handler (A:=A) _ (Put ctx') (memory,(ctx,c)) ≅
    (log (CSLCtx ctx' : CSLObs A);; Ret ((memory,(ctx',c)),tt)).
Proof. reflexivity. Qed.

Lemma csl_emit_handler_log {A} (a : A) memory ctx c :
  csl_emit_handler _ (Log a) (memory,(ctx,c)) ≅
    (log (CSLEmit (stamp a c) : CSLObs A);; Ret ((memory,(ctx,S c)),tt)).
Proof. reflexivity. Qed.

(** Rewrite a handler result under a fixed bind continuation; [H] may be
    either [equ] or [sbisim] evidence ([bind_sbisim_cong]/[equ_bind]). *)
Ltac csl_lift_handler_result H := rewrite H.

(** Interpretation-level emission: exactly one [CSLEmit] stamp. *)
Lemma interp_csl_emit {A X} (a : A) memory ctx c
  (k : unit -> ctree (heapE +' (stateE Ctx.Ctx +' writerE A)) Bn X) :
  interp_state sh
    (CTree.trigger (inr1 (inr1 (Log a)) : (heapE +' (stateE Ctx.Ctx +' writerE A)) unit) >>= k)
    (memory,(ctx,c)) ~
  (log (CSLEmit (stamp a c) : CSLObs A);;
   interp_state sh (k tt) (memory,(ctx,S c))).
Proof.
  rewrite interp_state_bind, interp_state_trigger_bind; cbn [sh h_sum].
  rewrite csl_emit_handler_log, bind_bind.
  setoid_rewrite bind_ret_l; reflexivity.
Qed.

(** ** Thread effects *)

Definition source_yield : ctree CEff Bn unit :=
  Vis (inl1 Yield) (fun _ => Ret tt).
Definition source_fork : ctree CEff Bn bool :=
  Vis (inr1 (inl1 Fork)) (fun b => Ret b).
Definition source_get : ctree CEff Bn Ctx.Ctx :=
  CTree.trigger (inr1 (inr1 (inr1 (inl1 Get))) : CEff Ctx.Ctx).
Definition source_put (ctx : Ctx.Ctx) : ctree CEff Bn unit :=
  CTree.trigger (inr1 (inr1 (inr1 (inl1 (Put ctx)))) : CEff unit).

(** ** The two response-relation instances of the generic segment theory. *)
Abbreviation csl_sb :=
  (fun X (t u : ctreeW (CSLObs (nat * nat)) Bn X) => t ~ u).
Abbreviation csl_equ :=
  (fun X (t u : ctreeW (CSLObs (nat * nat)) Bn X) => t ≅ u).

(** ** Raw physical free through the shared heap event *)

Lemma raw_heap_free_head a (K : unit -> thread sE Bn) :
  (heap_free (E:=CEff) a >>= K) ≅
    Vis (inr1 (inr1 (inl1 (HFree a)))) K.
Proof.
  unfold heap_free; rewrite bind_trigger; reflexivity.
Qed.

Lemma interp_rr_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) m (memory memory' : ManagedHeap) ctx c :
  managed_free memory base = Some memory' ->
  interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c)) ~
  match base with
  | 0 => interp_schedule_rr sh (S n) (ts @ i := K tt) (Some i) m (memory',(ctx,c))
  | S _ => log (inl (CSLHeap memory'));;
      interp_schedule_rr sh (S n) (ts @ i := K tt) (Some i) m (memory',(ctx,c))
  end.
Proof.
  intro Free.
  rewrite (interp_schedule_fair_user_bind rr_scheduler sh n ts i _
    (inl1 (HFree base)) K m (memory,(ctx,c)) (raw_heap_free_head base K)).
  cbn [sh h_sum].
  rewrite (heap_handlerW_free CSLHeap base memory memory' (ctx,c) Free).
  destruct base; [rewrite translate_ret, bind_ret_l; reflexivity|].
  rewrite translate_log_bind, bind_bind.
  setoid_rewrite translate_ret; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_heap_free_invalid n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) m (memory : ManagedHeap) ctx c :
  managed_free memory base = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * unit)).
Proof.
  intro Invalid.
  rewrite (interp_schedule_fair_user_bind rr_scheduler sh n ts i _
    (inl1 (HFree base)) K m (memory,(ctx,c)) (raw_heap_free_head base K)).
  cbn [sh h_sum].
  rewrite (heap_handlerW_free_invalid CSLHeap base memory (ctx,c) Invalid),
    translate_stuck_node, bind_stuck; reflexivity.
Qed.

Lemma interp_nd_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c :
  managed_free memory base = Some memory' ->
  interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c)) ~
  match base with
  | 0 => interp_schedule_nd sh (S n) (ts @ i := K tt) (Some i) (memory',(ctx,c))
  | S _ => log (CSLHeap memory');;
      interp_schedule_nd sh (S n) (ts @ i := K tt) (Some i) (memory',(ctx,c))
  end.
Proof.
  intro Free.
  rewrite (interp_schedule_nd_user_bind sh n ts i _
    (inl1 (HFree base)) K (memory,(ctx,c)) (raw_heap_free_head base K)).
  rewrite interp_state_trigger_bind; cbn [sh h_sum].
  rewrite (heap_handlerW_free CSLHeap base memory memory' (ctx,c) Free).
  destruct base; [rewrite bind_ret_l; reflexivity|].
  rewrite bind_bind; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_heap_free_invalid n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) (memory : ManagedHeap) ctx c :
  managed_free memory base = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  intro Invalid.
  rewrite (interp_schedule_nd_user_bind sh n ts i _
    (inl1 (HFree base)) K (memory,(ctx,c)) (raw_heap_free_head base K)).
  rewrite interp_state_trigger_bind; cbn [sh h_sum].
  rewrite (heap_handlerW_free_invalid CSLHeap base memory (ctx,c) Invalid), bind_stuck; reflexivity.
Qed.

(** ** Shared-context access through the scheduler

    [Get] substitutes the current context and is silent; [Put] emits exactly
    the left-injected new context.  Neither changes focus or the RR cursor,
    and neither touches memory or the indexed counter. *)

Lemma raw_source_get_head {X} (K : Ctx.Ctx -> ctree CEff Bn X) :
  (source_get >>= K) ≅ Vis (inr1 (inr1 (inr1 (inl1 Get))) : CEff Ctx.Ctx) K.
Proof.
  unfold source_get; rewrite bind_trigger; reflexivity.
Qed.

Lemma raw_source_put_head {X} ctx' (K : unit -> ctree CEff Bn X) :
  (source_put ctx' >>= K) ≅ Vis (inr1 (inr1 (inr1 (inl1 (Put ctx')))) : CEff unit) K.
Proof.
  unfold source_put; rewrite bind_trigger; reflexivity.
Qed.

Lemma interp_nd_get_ctx n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : Ctx.Ctx -> thread sE Bn) (s : SSig) :
  interp_schedule_nd sh (S n) (ts @ i := (source_get >>= K)) (Some i) s ~
  interp_schedule_nd sh (S n) (ts @ i := K (csl_context s)) (Some i) s.
Proof.
  destruct s as [memory [ctx c]].
  rewrite (interp_schedule_nd_user_bind sh n ts i _
    (inr1 (inl1 Get)) K (memory,(ctx,c)) (raw_source_get_head K)).
  rewrite interp_state_trigger_bind; cbn [sh h_sum].
  rewrite csl_context_handler_get, bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_get_ctx n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (K : Ctx.Ctx -> thread sE Bn) (cursor : nat) (s : SSig) :
  interp_schedule_rr sh (S n) (ts @ i := (source_get >>= K)) (Some i) cursor s ~
  interp_schedule_rr sh (S n) (ts @ i := K (csl_context s)) (Some i) cursor s.
Proof.
  destruct s as [memory [ctx c]].
  rewrite (interp_schedule_fair_user_bind rr_scheduler sh n ts i _
    (inr1 (inl1 Get)) K cursor (memory,(ctx,c)) (raw_source_get_head K)).
  cbn [sh h_sum].
  rewrite csl_context_handler_get, translate_ret, bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_put_ctx n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ctx' : Ctx.Ctx) (K : unit -> thread sE Bn) (s : SSig) :
  interp_schedule_nd sh (S n) (ts @ i := (source_put ctx' >>= K)) (Some i) s ~
  (log (CSLCtx ctx' : CSLObs (nat * nat));;
   interp_schedule_nd sh (S n) (ts @ i := K tt) (Some i)
     (csl_set_context s ctx')).
Proof.
  destruct s as [memory [ctx c]].
  rewrite (interp_schedule_nd_user_bind sh n ts i _
    (inr1 (inl1 (Put ctx'))) K (memory,(ctx,c)) (raw_source_put_head ctx' K)).
  rewrite interp_state_trigger_bind; cbn [sh h_sum].
  rewrite csl_context_handler_put, bind_bind.
  setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_put_ctx n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ctx' : Ctx.Ctx) (K : unit -> thread sE Bn) (cursor : nat) (s : SSig) :
  interp_schedule_rr sh (S n) (ts @ i := (source_put ctx' >>= K)) (Some i) cursor s ~
  (log (inl (CSLCtx ctx') : CSLObs (nat * nat) + nat);;
   interp_schedule_rr sh (S n) (ts @ i := K tt) (Some i) cursor
     (csl_set_context s ctx')).
Proof.
  destruct s as [memory [ctx c]].
  rewrite (interp_schedule_fair_user_bind rr_scheduler sh n ts i _
    (inr1 (inl1 (Put ctx'))) K cursor (memory,(ctx,c)) (raw_source_put_head ctx' K)).
  cbn [sh h_sum].
  rewrite csl_context_handler_put, translate_log_bind, bind_bind.
  setoid_rewrite translate_ret; setoid_rewrite bind_ret_l; reflexivity.
Qed.

(** ** Standalone erased threads over the CSL handler

    The erased standalone view resolves [Fork] to the parent branch, erases
    [Yield], and interprets the residual effects with [sh].  Context access
    behaves exactly as under the schedulers. *)

Lemma interp_thread_get_ctx {X} (K : Ctx.Ctx -> ctree CEff Bn X) (s : SSig) :
  interp_state sh (interp_thread (source_get >>= K)) s ~
  interp_state sh (interp_thread (K (csl_context s))) s.
Proof.
  destruct s as [memory [ctx c]].
  rewrite (raw_source_get_head K).
  rewrite (interp_state_thread_user sh (inr1 (inl1 Get))); cbn [sh h_sum].
  rewrite csl_context_handler_get, bind_ret_l; reflexivity.
Qed.

Lemma interp_thread_put_ctx {X} ctx' (K : unit -> ctree CEff Bn X) (s : SSig) :
  interp_state sh (interp_thread (source_put ctx' >>= K)) s ~
  (log (CSLCtx ctx' : CSLObs (nat * nat));;
   interp_state sh (interp_thread (K tt)) (csl_set_context s ctx')).
Proof.
  destruct s as [memory [ctx c]].
  rewrite (raw_source_put_head ctx' K).
  rewrite (interp_state_thread_user sh (inr1 (inl1 (Put ctx')))); cbn [sh h_sum].
  rewrite csl_context_handler_put, bind_bind.
  setoid_rewrite bind_ret_l; reflexivity.
Qed.

(** A read-modify-write of the shared context leaves exactly one context
    observation. *)
Lemma interp_thread_ctx_update {X} (f : Ctx.Ctx -> Ctx.Ctx) (r : X) (s : SSig) :
  interp_state sh (interp_thread
    (ctx <- source_get;; source_put (f ctx);; Ret r)) s ~
  ((log (CSLCtx (f (csl_context s)) : CSLObs (nat * nat));;
    Ret (csl_set_context s (f (csl_context s)), r))
   : ctreeW (CSLObs (nat * nat)) Bn (SSig * X)).
Proof.
  rewrite interp_thread_get_ctx; cbv beta.
  rewrite interp_thread_put_ctx.
  setoid_rewrite interp_state_thread_ret; reflexivity.
Qed.

(** ** Selection from an unfocused nonempty pool

    The non-deterministic scheduler picks with one visible branch; the
    round-robin scheduler picks with one logged [Scheduled] slot.  Both are
    exposed through the [_brS]/[_vis] lemma families. *)

Lemma an_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  {b : bool} (φ : ticl (writerE (CSLObs (nat * nat))) None)
  (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  (entails (SSig * unit) b (Cx Q_A φ ψ)
    (interp_schedule_nd sh (S n) ts None (memory,(ctx,c))) w <->
   (entails (SSig * unit) false φ
    (brS (branchn (S n)) (fun j : Fin.t (S n) =>
      interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c)))) w /\
    forall j : Fin.t (S n),
      entails (SSig * unit) b ψ
        (interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c))) w)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  apply (an_brS _ _ Fin.F1).
Qed.

Lemma au_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  {b : bool} (φ : ticl (writerE (CSLObs (nat * nat))) None)
  (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  (entails (SSig * unit) b (Cu Q_A φ ψ)
    (interp_schedule_nd sh (S n) ts None (memory,(ctx,c))) w <->
   (entails (SSig * unit) b ψ
    (brS (branchn (S n)) (fun j : Fin.t (S n) =>
      interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c)))) w \/
   (entails (SSig * unit) false φ
    (brS (branchn (S n)) (fun j : Fin.t (S n) =>
      interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c)))) w /\
    forall j : Fin.t (S n),
      entails (SSig * unit) b (Cu Q_A φ ψ)
        (interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c))) w))).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply (au_brS _ _ Fin.F1).
Qed.

Lemma ag_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat))) None) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |=L AG φ )> <->
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |=L φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |=L AG φ )>)).
Proof.
  ticl_normalize.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply (ag_brS _ _ Fin.F1).
Qed.

Lemma an_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  {b : bool} (φ : ticll (writerE (CSLObs (nat * nat) + nat)))
  (ψ : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_A φ ψ)
    (interp_schedule_rr sh (S n) ts None m (memory,(ctx,c))) w <->
  entails (SSig * unit) false φ
    (Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ =>
      interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))) w /\
  entails (SSig * unit) b ψ
    (interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))
    (Obs (Log (inr (slot_index (rr_pick n m)))) tt).
Proof.
  rewrite (interp_schedule_rr_select sh), (an_vis _ _ tt).
  split; intros [H1 H2]; (split; [exact H1|]); [exact (H2 tt)|intros []; exact H2].
Qed.

Lemma au_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  {b : bool} (φ : ticll (writerE (CSLObs (nat * nat) + nat)))
  (ψ : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_A φ ψ)
    (interp_schedule_rr sh (S n) ts None m (memory,(ctx,c))) w <->
  entails (SSig * unit) b ψ
    (Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ =>
      interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))) w \/
  (entails (SSig * unit) false φ
    (Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ =>
      interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))) w /\
   entails (SSig * unit) b (Cu Q_A φ ψ)
    (interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))
    (Obs (Log (inr (slot_index (rr_pick n m)))) tt)).
Proof.
  rewrite (interp_schedule_rr_select sh), <- (au_vis _ _ tt).
  split; (intros [H|[H1 H2]]; [left; exact H|right; split; [exact H1|]]);
    [exact (H2 tt)|intros []; exact H2].
Qed.

Lemma ag_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  (φ : ticll (writerE (CSLObs (nat * nat) + nat))) :
  <( {interp_schedule_rr sh (S n) ts None m (memory,(ctx,c))}, w |=L AG φ )> <->
  (<( {Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ =>
    interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, w |=L φ )> /\
   <( {interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))},
     {Obs (Log (inr (slot_index (rr_pick n m)))) tt} |=L AG φ )>).
Proof.
  rewrite (interp_schedule_rr_select sh), <- (ag_vis _ _ tt).
  split; intros [H1 H2]; (split; [exact H1|]); [exact (H2 tt)|intros []; exact H2].
Qed.

Lemma en_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  {b : bool} (φ : ticl (writerE (CSLObs (nat * nat))) None)
  (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E φ ψ)
    (interp_schedule_nd sh (S n) ts None (memory,(ctx,c))) w <->
  entails (SSig * unit) false φ
    (brS (branchn (S n)) (fun j : Fin.t (S n) =>
      interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c)))) w /\
  exists j : Fin.t (S n), entails (SSig * unit) b ψ
    (interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c))) w.
Proof.
  rewrite (interp_schedule_nd_select sh).
  apply en_brS.
Qed.

Lemma eu_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  {b : bool} (φ : ticl (writerE (CSLObs (nat * nat))) None)
  (ψ : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E φ ψ)
    (interp_schedule_nd sh (S n) ts None (memory,(ctx,c))) w <->
  entails (SSig * unit) b ψ
    (brS (branchn (S n)) (fun j : Fin.t (S n) =>
      interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c)))) w \/
  (entails (SSig * unit) false φ
    (brS (branchn (S n)) (fun j : Fin.t (S n) =>
      interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c)))) w /\
   exists j : Fin.t (S n), entails (SSig * unit) b (Cu Q_E φ ψ)
    (interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c))) w).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply eu_brS.
Qed.

Lemma eg_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  (φ : ticl (writerE (CSLObs (nat * nat))) None) :
  (<( {interp_schedule_nd sh (S n) ts None (memory,(ctx,c))}, {w} |=L EG φ )> <->
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
     interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c)))}, {w} |=L φ )> /\
    exists j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n) ts (Some j) (memory,(ctx,c))}, {w} |=L EG φ )>)).
Proof.
  ticl_normalize.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply eg_brS.
Qed.

Lemma en_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  {b : bool} (φ : ticll (writerE (CSLObs (nat * nat) + nat)))
  (ψ : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cx Q_E φ ψ)
    (interp_schedule_rr sh (S n) ts None m (memory,(ctx,c))) w <->
  entails (SSig * unit) false φ
    (Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ =>
      interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))) w /\
  entails (SSig * unit) b ψ
    (interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))
    (Obs (Log (inr (slot_index (rr_pick n m)))) tt).
Proof.
  rewrite (interp_schedule_rr_select sh), en_vis.
  split; intros [H1 H2]; split; [exact H1|destruct H2 as [[] H2]; exact H2|exact H1|].
  exists tt; exact H2.
Qed.

Lemma eu_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  {b : bool} (φ : ticll (writerE (CSLObs (nat * nat) + nat)))
  (ψ : ticl_at (writerE (CSLObs (nat * nat) + nat)) (SSig * unit) b) :
  entails (SSig * unit) b (Cu Q_E φ ψ)
    (interp_schedule_rr sh (S n) ts None m (memory,(ctx,c))) w <->
  entails (SSig * unit) b ψ
    (Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ =>
      interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))) w \/
  (entails (SSig * unit) false φ
    (Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ =>
      interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))) w /\
   entails (SSig * unit) b (Cu Q_E φ ψ)
    (interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))
    (Obs (Log (inr (slot_index (rr_pick n m)))) tt)).
Proof.
  rewrite (interp_schedule_rr_select sh), <- eu_vis.
  split; intros [H|[H1 H2]]; [left; exact H|right|left; exact H|right];
    split; [exact H1|destruct H2 as [[] H2]; exact H2|exact H1|exists tt; exact H2].
Qed.

Lemma eg_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  (φ : ticll (writerE (CSLObs (nat * nat) + nat))) :
  <( {interp_schedule_rr sh (S n) ts None m (memory,(ctx,c))}, w |=L EG φ )> <->
  (<( {Vis (Log (inr (slot_index (rr_pick n m)))) (fun _ =>
    interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, w |=L φ )> /\
   <( {interp_schedule_rr sh (S n) ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))},
     {Obs (Log (inr (slot_index (rr_pick n m)))) tt} |=L EG φ )>).
Proof.
  rewrite (interp_schedule_rr_select sh), <- eg_vis.
  split; intros [H1 H2]; split; [exact H1|destruct H2 as [[] H2]; exact H2|exact H1|].
  exists tt; exact H2.
Qed.
