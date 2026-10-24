(** * The canonical CSL effect interpreter.

    This module owns the CSL effect sum, its interpretation state and the one
    payload-polymorphic handler [sh] that combines the shared checked heap,
    the shared variable context (with context-update observations) and the
    shared indexing writer.  Everything here is stated over effects and
    trees: it does not mention CSL syntax.  The source language
    ([Lang.CSL.Mod]) specializes these laws to its denotation.

    Generic checked heap access, allocation search, indexed observation and
    the scheduler/segment machinery live one layer further down and are
    re-exported from here.

    The whole CSL stack is fixed at the finite branch signature [Bn]: the
    round-robin refinement ([CTree.Interp.Refine]) only exists at [Bn], and
    the non-deterministic scheduler is instantiated at the same signature so
    one denotation serves both schedulers. *)

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
  CTree.Interp.Refine
  CTree.Interp.Yield.Nondeterministic
  CTree.Interp.Yield.Segments
  Utils.Maps.

From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Interp.State.Mod
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.RoundRobin
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
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
Notation sE := (heapE +' (stateE Ctx.Ctx +' writerE (nat * nat))).

(** Interpretation state: the SHARED managed memory (data heap and live
    allocation extents), the SHARED variable context, and one GLOBAL
    occurrence counter for indexed emissions.  A state is
    [((h,allocs),(ctx,c))].  The context is not part of heap ownership. *)
Definition SSig : Type := (ManagedHeap * (Ctx.Ctx * nat))%type.

(** Observations: a context update logs the new context ([inl]); an indexed
    emission logs its stamped payload ([inr]). *)
Definition CSLObs (A : Type) : Type := (Ctx.Ctx + indexed A)%type.

(** Thread effects: yield, fork, and the interpreted sum.  A notation, so
    that [thread sE Bn] and [ctree CEff Bn unit] coincide syntactically and
    the ITree [-<] instances for the components resolve without unfolding. *)
Notation CEff := (yieldE +' (forkE +' sE)).

Definition csl_memory (s : SSig) : ManagedHeap := fst s.
Definition csl_context (s : SSig) : Ctx.Ctx := fst (snd s).
Definition csl_counter (s : SSig) : nat := snd (snd s).
Definition csl_set_context (s : SSig) (ctx : Ctx.Ctx) : SSig :=
  (csl_memory s, (ctx, csl_counter s)).
Definition csl_indexed {A} (P : indexed A -> Prop) (o : CSLObs A) : Prop :=
  match o with inl _ => False | inr x => P x end.
(** The occurrence index of an indexed emission; context updates carry no
    occurrence index and project to [0]. *)
Definition csl_index {A} (o : CSLObs A) : nat :=
  match o with inl _ => 0 | inr x => indexed_index x end.

Definition semit (q v : nat) : ctree sE Bn unit :=
  CTree.trigger (inr1 (inr1 (Log (q,v))) : sE unit).

(** The context handler acts on the shared context exactly as [h_stateW]
    does ([Get] is silent, [Put] logs the new context, injected on the left)
    and leaves memory and the indexed counter untouched. *)
Definition csl_context_handler {A : Type} :
  stateE Ctx.Ctx ~> stateT SSig (ctreeW (CSLObs A) Bn) :=
  fun _ e s =>
    match e in stateE _ X return ctreeW (CSLObs A) Bn (SSig * X) with
    | Get => Ret (s, csl_context s)
    | Put ctx' => log (inl ctx' : CSLObs A);; Ret (csl_set_context s ctx', tt)
    end.

(** The emission handler acts as [h_indexed] on the global counter: every
    [Log a] emits exactly one right-injected stamp and advances only the
    counter. *)
Definition csl_emit_handler {A : Type} :
  writerE A ~> stateT SSig (ctreeW (CSLObs A) Bn) :=
  fun _ '(Log a) s =>
    log (inr (stamp a (csl_counter s)) : CSLObs A);;
    Ret ((csl_memory s, (csl_context s, S (csl_counter s))), tt).

(** The one CSL handler: the shared checked-heap handler summed with the
    context and indexing handlers.  It is polymorphic in the observation
    payload; the tagged source language uses [nat * nat], a unary reference
    model uses [nat]. *)
Definition sh {A : Type} :
  (heapE +' (stateE Ctx.Ctx +' writerE A)) ~> stateT SSig (ctreeW (CSLObs A) Bn) :=
  h_sum heap_handler (h_sum csl_context_handler csl_emit_handler).

(** Raw handler equations: [Get] is silent, [Put] logs exactly the new
    context, [Log] logs exactly one stamp and advances only the counter. *)
Lemma csl_context_handler_get {A} memory ctx c :
  csl_context_handler (A:=A) _ Get (memory,(ctx,c)) ≅
    Ret ((memory,(ctx,c)),ctx).
Proof. reflexivity. Qed.

Lemma csl_context_handler_put {A} ctx' memory ctx c :
  csl_context_handler (A:=A) _ (Put ctx') (memory,(ctx,c)) ≅
    (log (inl ctx' : CSLObs A);; Ret ((memory,(ctx',c)),tt)).
Proof. reflexivity. Qed.

Lemma csl_emit_handler_log {A} (a : A) memory ctx c :
  csl_emit_handler _ (Log a) (memory,(ctx,c)) ≅
    (log (inr (stamp a c) : CSLObs A);; Ret ((memory,(ctx,S c)),tt)).
Proof. reflexivity. Qed.

(** Rewrite a handler result under a fixed bind continuation; [H] may be
    either [equ] or [sbisim] evidence ([bind_sbisim_cong]/[equ_bind]). *)
Ltac csl_lift_handler_result H := rewrite H.

(** Interpretation-level emission: exactly one right-injected stamp. *)
Lemma interp_csl_emit {A X} (a : A) memory ctx c
  (k : unit -> ctree (heapE +' (stateE Ctx.Ctx +' writerE A)) Bn X) :
  interp_state sh
    (CTree.trigger (inr1 (inr1 (Log a)) : (heapE +' (stateE Ctx.Ctx +' writerE A)) unit) >>= k)
    (memory,(ctx,c)) ~
  (log (inr (stamp a c) : CSLObs A);;
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
Notation csl_sb :=
  (fun X (t u : ctreeW (CSLObs (nat * nat)) Bn X) => t ~ u).
Notation csl_equ :=
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
  interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c)).
Proof.
  intro Free.
  rewrite (interp_schedule_rr_user_bind sh n ts i _
    (inl1 (HFree base)) K m (memory,(ctx,c)) (raw_heap_free_head base K)).
  rewrite interp_state_trigger_bind; cbn [sh h_sum].
  rewrite (heap_handler_free base memory memory' (ctx,c) Free), bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_heap_free_invalid n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) m (memory : ManagedHeap) ctx c :
  managed_free memory base = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c)) ~
  (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  intro Invalid.
  rewrite (interp_schedule_rr_user_bind sh n ts i _
    (inl1 (HFree base)) K m (memory,(ctx,c)) (raw_heap_free_head base K)).
  rewrite interp_state_trigger_bind; cbn [sh h_sum].
  rewrite (heap_handler_free_invalid base memory (ctx,c) Invalid), bind_stuck; reflexivity.
Qed.

Lemma interp_nd_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c :
  managed_free memory base = Some memory' ->
  interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c)) ~
  interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c)).
Proof.
  intro Free.
  rewrite (interp_schedule_nd_user_bind sh n ts i _
    (inl1 (HFree base)) K (memory,(ctx,c)) (raw_heap_free_head base K)).
  rewrite interp_state_trigger_bind; cbn [sh h_sum].
  rewrite (heap_handler_free base memory memory' (ctx,c) Free), bind_ret_l; reflexivity.
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
  rewrite (heap_handler_free_invalid base memory (ctx,c) Invalid), bind_stuck; reflexivity.
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
  rewrite (interp_schedule_rr_user_bind sh n ts i _
    (inr1 (inl1 Get)) K cursor (memory,(ctx,c)) (raw_source_get_head K)).
  rewrite interp_state_trigger_bind; cbn [sh h_sum].
  rewrite csl_context_handler_get, bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_put_ctx n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (ctx' : Ctx.Ctx) (K : unit -> thread sE Bn) (s : SSig) :
  interp_schedule_nd sh (S n) (ts @ i := (source_put ctx' >>= K)) (Some i) s ~
  (log (inl ctx' : CSLObs (nat * nat));;
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
  (log (inl ctx' : CSLObs (nat * nat));;
   interp_schedule_rr sh (S n) (ts @ i := K tt) (Some i) cursor
     (csl_set_context s ctx')).
Proof.
  destruct s as [memory [ctx c]].
  rewrite (interp_schedule_rr_user_bind sh n ts i _
    (inr1 (inl1 (Put ctx'))) K cursor (memory,(ctx,c)) (raw_source_put_head ctx' K)).
  rewrite interp_state_trigger_bind; cbn [sh h_sum].
  rewrite csl_context_handler_put, bind_bind.
  setoid_rewrite bind_ret_l; reflexivity.
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
  (log (inl ctx' : CSLObs (nat * nat));;
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
  ((log (inl (f (csl_context s)) : CSLObs (nat * nat));;
    Ret (csl_set_context s (f (csl_context s)), r))
   : ctreeW (CSLObs (nat * nat)) Bn (SSig * X)).
Proof.
  rewrite interp_thread_get_ctx; cbv beta.
  rewrite interp_thread_put_ctx.
  setoid_rewrite interp_state_thread_ret; reflexivity.
Qed.

(** ** Selection from an unfocused nonempty pool

    The non-deterministic scheduler picks with one visible branch; the
    round-robin scheduler picks with one visible step.  Both are exposed
    through the [_brS]/[_step] lemma families. *)

Lemma anl_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |= ψ )>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  apply (anl_brS _ _ Fin.F1).
Qed.

Lemma anr_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (SSig * unit)) :
  (<[ {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |= ψ ]>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  apply (anr_brS _ _ Fin.F1).
Qed.

Lemma aul_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= ψ )> \/
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |= φ AU ψ )>))).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply (aul_brS _ _ Fin.F1).
Qed.

Lemma aur_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (SSig * unit)) :
  (<[ {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= ψ ]> \/
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |= φ AU ψ ]>))).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply (aur_brS _ _ Fin.F1).
Qed.

Lemma ag_csl_nd_select n (ts : pool sE Bn (S n)) (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {brS (branchn (S n)) (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply (ag_brS _ _ Fin.F1).
Qed.

Lemma anl_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {Step (interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= ψ )>)).
Proof.
  rewrite interp_schedule_rr_select.
  apply anl_step.
Qed.

Lemma anr_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (SSig * unit)) :
  (<[ {interp_schedule_rr sh (S n)
    ts (None) m (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<( {Step (interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, {w} |= φ )> /\
    <[ {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= ψ ]>)).
Proof.
  rewrite interp_schedule_rr_select.
  apply anr_step.
Qed.

Lemma aul_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {Step (interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, {w} |= ψ )> \/
   (<( {Step (interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= φ AU ψ )>))).
Proof.
  rewrite interp_schedule_rr_select.
  symmetry; apply aul_step.
Qed.

Lemma aur_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (SSig * unit)) :
  (<[ {interp_schedule_rr sh (S n)
    ts (None) m (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {Step (interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, {w} |= ψ ]> \/
   (<( {Step (interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, {w} |= φ )> /\
    <[ {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= φ AU ψ ]>))).
Proof.
  rewrite interp_schedule_rr_select.
  symmetry; apply aur_step.
Qed.

Lemma ag_csl_rr_select n (ts : pool sE Bn (S n)) m (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {Step (interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c)))}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite interp_schedule_rr_select.
  symmetry; apply ag_step.
Qed.

(** ** Valid whole-block free through the shared raw heap event *)

Lemma anl_csl_nd_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c))}, {w} |= φ AN ψ )>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma anr_csl_nd_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (SSig * unit)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   <[ {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c))}, {w} |= φ AN ψ ]>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma aul_csl_nd_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c))}, {w} |= φ AU ψ )>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma aur_csl_nd_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (SSig * unit)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   <[ {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c))}, {w} |= φ AU ψ ]>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma ag_csl_nd_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c))}, {w} |= AG φ )>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma anl_csl_rr_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) m (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c))}, {w} |= φ AN ψ )>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' ctx c Free); reflexivity.
Qed.

Lemma anr_csl_rr_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) m (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (SSig * unit)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   <[ {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c))}, {w} |= φ AN ψ ]>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' ctx c Free); reflexivity.
Qed.

Lemma aul_csl_rr_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) m (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c))}, {w} |= φ AU ψ )>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' ctx c Free); reflexivity.
Qed.

Lemma aur_csl_rr_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) m (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (SSig * unit)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   <[ {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c))}, {w} |= φ AU ψ ]>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' ctx c Free); reflexivity.
Qed.

Lemma ag_csl_rr_heap_free n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE Bn) m (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c))}, {w} |= AG φ )>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' ctx c Free); reflexivity.
Qed.
