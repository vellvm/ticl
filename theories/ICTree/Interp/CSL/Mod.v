(** * The canonical CSL effect interpreter.

    This module owns the CSL effect sum, its interpretation state and the one
    payload-polymorphic handler [sh] that combines the shared checked heap,
    the shared variable context (with context-update observations) and the
    shared indexing writer.  Everything here is stated over effects and
    trees: it does not mention CSL syntax.  The source language
    ([Lang.CSL.Mod]) specializes these laws to its denotation.

    Generic checked heap access, allocation search, indexed observation and
    the scheduler/segment machinery live one layer further down and are
    re-exported from here. *)

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad.

From Coinduction Require Import coinduction lattice tactics.

From TICL Require Export
  Events.HeapModel
  ICTree.Events.Heap
  ICTree.Events.Writer
  ICTree.Events.State
  ICTree.Interp.Heap
  ICTree.Logic.Heap
  ICTree.Trace
  ICTree.Interp.Refine
  ICTree.Interp.Yield.Nondeterministic
  ICTree.Interp.Yield.Segments
  Utils.Maps.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Trans
  ICTree.Events.Yield
  ICTree.Interp.State.Mod
  ICTree.Interp.Yield.Mod
  ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.State
  Logic.World
  Logic.Core
  Utils.Vectors.

Import ICtree ICTreeNotations TiclNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

(** ** Effects and interpretation state *)

(** [sE] is a notation, not a definition: the payload-polymorphic handler
    [sh] below is typed over [heapE + (stateE Ctx.Ctx + writerE A)], so
    instantiating it at the tagged payload yields this sum syntactically, and
    rewrites stated over [sE] keep matching terms elaborated through [sh]. *)
Notation sE := (heapE + (stateE Ctx.Ctx + writerE (nat * nat)))%type.

(** Interpretation state: the SHARED managed memory (data heap and live
    allocation extents), the SHARED variable context, and one GLOBAL
    occurrence counter for indexed emissions.  A state is
    [((h,allocs),(ctx,c))].  The context is not part of heap ownership. *)
Definition SSig : Type := (ManagedHeap * (Ctx.Ctx * nat))%type.

(** Observations: a context update logs the new context ([inl]); an indexed
    emission logs its stamped payload ([inr]). *)
Definition CSLObs (A : Type) : Type := (Ctx.Ctx + indexed A)%type.

Definition CEff : Type := (yieldE + (forkE + sE))%type.

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

Definition semit (q v : nat) : ictree sE unit :=
  @ICtree.trigger sE sE _ _ ReSum_refl ReSumRet_refl (inr (inr (Log (q,v)))).

(** The context handler projects the shared context, runs the existing
    [h_stateW], injects its context logs on the left, and rebuilds the state.
    Memory and the indexed counter are untouched. *)
Definition csl_context_handler {A : Type} :
  stateE Ctx.Ctx ~> stateT SSig (ictreeW (CSLObs A)) :=
  fun e => mkStateT (fun s =>
    '(x, ctx') <- @resumICtree (writerE Ctx.Ctx) (writerE (CSLObs A)) _ _ _ _ _
        (runStateT (h_stateW e) (csl_context s));;
    Ret (x, csl_set_context s ctx')).

(** The emission handler reassociates [(memory,(ctx,c))] to
    [((memory,ctx),c)], runs the existing [h_indexed], injects its stamped
    logs on the right, and reassociates back. *)
Definition csl_emit_handler {A : Type} :
  writerE A ~> stateT SSig (ictreeW (CSLObs A)) :=
  fun e => mkStateT (fun s =>
    '(x, ((memory, ctx), c)) <-
      @resumICtree (writerE (indexed A)) (writerE (CSLObs A)) _ _ _ _ _
        (runStateT (h_indexed (Sigma:=ManagedHeap * Ctx.Ctx) e)
          ((csl_memory s, csl_context s), csl_counter s));;
    Ret (x, (memory, (ctx, c)))).

(** The one CSL handler: the shared checked-heap handler summed with the
    context and indexing handlers.  It is polymorphic in the observation
    payload; the tagged source language uses [nat * nat], a unary reference
    model uses [nat]. *)
Definition sh {A : Type} :
  (heapE + (stateE Ctx.Ctx + writerE A)) ~> stateT SSig (ictreeW (CSLObs A)) :=
  h_sum heap_handler (h_sum csl_context_handler csl_emit_handler).

Local Typeclasses Transparent equ.

(** Raw handler equations: [Get] is silent, [Put] logs exactly the new
    context, [Log] logs exactly one stamp and advances only the counter. *)
Lemma csl_context_handler_get {A} memory ctx c :
  runStateT (csl_context_handler (A:=A) Get) (memory,(ctx,c)) ≅
    Ret (ctx,(memory,(ctx,c))).
Proof.
  unfold csl_context_handler; cbn [runStateT h_stateW].
  step; cbn; constructor; reflexivity.
Qed.

Lemma csl_context_handler_put {A} ctx' memory ctx c :
  runStateT (csl_context_handler (A:=A) (Put ctx')) (memory,(ctx,c)) ≅
    (log (inl ctx' : CSLObs A);; Ret (tt,(memory,(ctx',c)))).
Proof.
  unfold csl_context_handler; cbn [runStateT h_stateW].
  step; cbn; constructor; intros [].
  step; cbn; constructor; reflexivity.
Qed.

Lemma csl_emit_handler_log {A} (a : A) memory ctx c :
  runStateT (csl_emit_handler (Log a)) (memory,(ctx,c)) ≅
    (log (inr (stamp a c) : CSLObs A);; Ret (tt,(memory,(ctx,S c)))).
Proof.
  unfold csl_emit_handler; cbn [runStateT h_indexed].
  step; cbn; constructor; intros [].
  step; cbn; constructor; reflexivity.
Qed.

(** Interpretation-level emission: exactly one right-injected stamp. *)
Lemma interp_csl_emit {A X} (a : A) memory ctx c
  (k : unit -> ictree (heapE + (stateE Ctx.Ctx + writerE A)) X) :
  interp_state sh
    ((@ICtree.trigger _ _ _ _ ReSum_refl ReSumRet_refl
       (inr (inr (Log a)) : heapE + (stateE Ctx.Ctx + writerE A))) >>= k)
    (memory,(ctx,c)) ~
  (log (inr (stamp a c) : CSLObs A);;
   interp_state sh (k tt) (memory,(ctx,S c))).
Proof.
  unfold ICtree.trigger, resum, resum_ret, ReSum_refl, ReSumRet_refl;
    rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis; cbn [sh h_sum].
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (csl_emit_handler_log a memory ctx c) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l; apply sb_guard.
Qed.
Local Typeclasses Opaque equ.

(** ** Thread effects *)

#[global] Instance ReSum_heap_CEff : ReSum heapE CEff :=
  fun e => inr (inr (inl e)).
#[global] Instance ReSumRet_heap_CEff : ReSumRet heapE CEff :=
  fun e response => response.
#[global] Instance ReSum_ctx_CEff : ReSum (stateE Ctx.Ctx) CEff :=
  fun e => inr (inr (inr (inl e))).
#[global] Instance ReSumRet_ctx_CEff : ReSumRet (stateE Ctx.Ctx) CEff :=
  fun e response => response.
#[global] Instance ReSum_tagged_CEff : ReSum (writerE (nat * nat)) CEff :=
  fun e => inr (inr (inr (inr e))).
#[global] Instance ReSumRet_tagged_CEff : ReSumRet (writerE (nat * nat)) CEff :=
  fun e response => response.
Definition source_yield : ictree CEff unit :=
  Vis (inl Yield) (fun _ => Ret tt).
Definition source_fork : ictree CEff bool :=
  Vis (inr (inl Fork)) (fun b => Ret b).
Definition source_get : ictree CEff Ctx.Ctx :=
  ICtree.trigger (E1:=stateE Ctx.Ctx) (E2:=CEff) Get.
Definition source_put (ctx : Ctx.Ctx) : ictree CEff unit :=
  ICtree.trigger (E1:=stateE Ctx.Ctx) (E2:=CEff) (Put ctx).

(** ** The two response-relation instances of the generic segment theory. *)
Notation csl_sb :=
  (fun X (t u : ictreeW (CSLObs (nat * nat)) X) => t ~ u).
Notation csl_equ :=
  (fun X (t u : ictreeW (CSLObs (nat * nat)) X) => t ≅ u).

(** ** Raw physical free through the shared heap event *)

Lemma raw_heap_free_head a (K : unit -> thread sE) :
  (heap_free (E:=CEff) a >>= K) ≅
    Vis (inr (inr (inl (HFree a)))) K.
Proof.
  unfold heap_free, ICtree.trigger, resum, resum_ret,
    ReSum_heap_CEff, ReSumRet_heap_CEff.
  rewrite bind_vis; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) ctx c :
  managed_free memory base = Some memory' ->
  interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c)) ~
  interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c)).
Proof.
  intro Free.
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K))
    (ts @ i := Vis (inr (inr (inl (HFree base)))) K)
    (Some i) m (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_heap_free_head base K))) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user with (e:=inl (HFree base)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (heap_handler_free base memory memory' (ctx,c) Free) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l, Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_heap_free_invalid n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory : ManagedHeap) ctx c :
  managed_free memory base = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c)) ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Invalid.
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K))
    (ts @ i := Vis (inr (inr (inl (HFree base)))) K)
    (Some i) m (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_heap_free_head base K))) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user with (e:=inl (HFree base)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (heap_handler_free_invalid base memory (ctx,c) Invalid) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) ctx c :
  managed_free memory base = Some memory' ->
  interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c)) ~
  interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c)).
Proof.
  intro Free.
  pose proof ((interp_schedule_nd_equ sh) (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K))
    (ts @ i := Vis (inr (inr (inl (HFree base)))) K)
    (Some i) (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_heap_free_head base K))) as Hpool.
  rewrite Hpool.
  erewrite (interp_schedule_nd_user sh) with (e:=inl (HFree base)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (heap_handler_free base memory memory' (ctx,c) Free) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l, Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_heap_free_invalid n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory : ManagedHeap) ctx c :
  managed_free memory base = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c)) ~
  (stuck : ictreeW (CSLObs (nat * nat)) (unit * SSig)).
Proof.
  intro Invalid.
  pose proof ((interp_schedule_nd_equ sh) (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K))
    (ts @ i := Vis (inr (inr (inl (HFree base)))) K)
    (Some i) (memory,(ctx,c))
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_heap_free_head base K))) as Hpool.
  rewrite Hpool.
  erewrite (interp_schedule_nd_user sh) with (e:=inl (HFree base)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (heap_handler_free_invalid base memory (ctx,c) Invalid) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

(** ** Shared-context access through the scheduler

    [Get] substitutes the current context and is silent; [Put] emits exactly
    the left-injected new context.  Neither changes focus or the RR cursor,
    and neither touches memory or the indexed counter. *)

Lemma raw_source_get_head {X} (K : Ctx.Ctx -> ictree CEff X) :
  (source_get >>= K) ≅ Vis (inr (inr (inr (inl Get))) : CEff) K.
Proof.
  unfold source_get, ICtree.trigger, resum, resum_ret,
    ReSum_ctx_CEff, ReSumRet_ctx_CEff.
  rewrite bind_vis; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma raw_source_put_head {X} ctx' (K : unit -> ictree CEff X) :
  (source_put ctx' >>= K) ≅ Vis (inr (inr (inr (inl (Put ctx')))) : CEff) K.
Proof.
  unfold source_put, ICtree.trigger, resum, resum_ret,
    ReSum_ctx_CEff, ReSumRet_ctx_CEff.
  rewrite bind_vis; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_nd_get_ctx n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : Ctx.Ctx -> thread sE) (s : SSig) :
  interp_schedule_nd sh (S n) (ts @ i := (source_get >>= K)) (Some i) s ~
  interp_schedule_nd sh (S n) (ts @ i := K (csl_context s)) (Some i) s.
Proof.
  destruct s as [memory [ctx c]].
  rewrite ((interp_schedule_nd_equ sh) (S n) _
    (ts @ i := Vis (inr (inr (inr (inl Get))) : CEff) K) (Some i) _
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_source_get_head K))).
  erewrite (interp_schedule_nd_user sh) with (e:=inr (inl Get)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (csl_context_handler_get (A:=nat * nat) memory ctx c)
        | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l, Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_get_ctx n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : Ctx.Ctx -> thread sE) (cursor : nat) (s : SSig) :
  interp_schedule_rr sh (S n) (ts @ i := (source_get >>= K)) (Some i) cursor s ~
  interp_schedule_rr sh (S n) (ts @ i := K (csl_context s)) (Some i) cursor s.
Proof.
  destruct s as [memory [ctx c]].
  rewrite (interp_schedule_rr_equ sh (S n) _
    (ts @ i := Vis (inr (inr (inr (inl Get))) : CEff) K) (Some i) cursor _
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_source_get_head K))).
  erewrite interp_schedule_rr_user with (e:=inr (inl Get)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (csl_context_handler_get (A:=nat * nat) memory ctx c)
        | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l, Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_put_ctx n (ts : pool sE (S n)) (i : Fin.t (S n))
  (ctx' : Ctx.Ctx) (K : unit -> thread sE) (s : SSig) :
  interp_schedule_nd sh (S n) (ts @ i := (source_put ctx' >>= K)) (Some i) s ~
  (log (inl ctx' : CSLObs (nat * nat));;
   interp_schedule_nd sh (S n) (ts @ i := K tt) (Some i)
     (csl_set_context s ctx')).
Proof.
  destruct s as [memory [ctx c]].
  rewrite ((interp_schedule_nd_equ sh) (S n) _
    (ts @ i := Vis (inr (inr (inr (inl (Put ctx')))) : CEff) K) (Some i) _
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_source_put_head ctx' K))).
  erewrite (interp_schedule_nd_user sh) with (e:=inr (inl (Put ctx'))) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (csl_context_handler_put (A:=nat * nat) ctx' memory ctx c)
        | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l, Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_put_ctx n (ts : pool sE (S n)) (i : Fin.t (S n))
  (ctx' : Ctx.Ctx) (K : unit -> thread sE) (cursor : nat) (s : SSig) :
  interp_schedule_rr sh (S n) (ts @ i := (source_put ctx' >>= K)) (Some i) cursor s ~
  (log (inl ctx' : CSLObs (nat * nat));;
   interp_schedule_rr sh (S n) (ts @ i := K tt) (Some i) cursor
     (csl_set_context s ctx')).
Proof.
  destruct s as [memory [ctx c]].
  rewrite (interp_schedule_rr_equ sh (S n) _
    (ts @ i := Vis (inr (inr (inr (inl (Put ctx')))) : CEff) K) (Some i) cursor _
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_source_put_head ctx' K))).
  erewrite interp_schedule_rr_user with (e:=inr (inl (Put ctx'))) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (csl_context_handler_put (A:=nat * nat) ctx' memory ctx c)
        | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l, Vector.replace_replace_eq; reflexivity.
Qed.

Local Typeclasses Transparent equ sbisim.

(** ** Standalone erased threads over the CSL handler

    The erased standalone view resolves [Fork] to the parent branch, erases
    [Yield], and interprets the residual effects with [sh].  Context access
    behaves exactly as under the schedulers. *)

Lemma interp_thread_get_ctx {X} (K : Ctx.Ctx -> ictree CEff X) (s : SSig) :
  interp_state sh (interp_thread (source_get >>= K)) s ~
  interp_state sh (interp_thread (K (csl_context s))) s.
Proof.
  destruct s as [memory [ctx c]].
  rewrite (raw_source_get_head K).
  rewrite (interp_state_thread_user sh (inr (inl Get))).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (csl_context_handler_get (A:=nat * nat) memory ctx c)
        | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_thread_put_ctx {X} ctx' (K : unit -> ictree CEff X) (s : SSig) :
  interp_state sh (interp_thread (source_put ctx' >>= K)) s ~
  (log (inl ctx' : CSLObs (nat * nat));;
   interp_state sh (interp_thread (K tt)) (csl_set_context s ctx')).
Proof.
  destruct s as [memory [ctx c]].
  rewrite (raw_source_put_head ctx' K).
  rewrite (interp_state_thread_user sh (inr (inl (Put ctx')))).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (csl_context_handler_put (A:=nat * nat) ctx' memory ctx c)
        | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l; reflexivity.
Qed.

(** A read-modify-write of the shared context leaves exactly one context
    observation. *)
Lemma interp_thread_ctx_update {X} (f : Ctx.Ctx -> Ctx.Ctx) (r : X) (s : SSig) :
  interp_state sh (interp_thread
    (ctx <- source_get;; source_put (f ctx);; Ret r)) s ~
  (log (inl (f (csl_context s)) : CSLObs (nat * nat));;
   Ret (r, csl_set_context s (f (csl_context s)))).
Proof.
  rewrite interp_thread_get_ctx; cbv beta.
  rewrite interp_thread_put_ctx.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite interp_state_thread_ret; reflexivity.
Qed.

(** ** Selection from an unfocused nonempty pool *)

Lemma anl_csl_nd_select n (ts : pool sE (S n)) (memory : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |= ψ )>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  apply anl_br.
Qed.

Lemma anr_csl_nd_select n (ts : pool sE (S n)) (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |= ψ ]>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  apply anr_br.
Qed.

Lemma aul_csl_nd_select n (ts : pool sE (S n)) (memory : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= ψ )> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |= φ AU ψ )>))).

Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply aul_br.
Qed.

Lemma aur_csl_nd_select n (ts : pool sE (S n)) (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= ψ ]> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |= φ AU ψ ]>))).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply aur_br.
Qed.

Lemma ag_csl_nd_select n (ts : pool sE (S n)) (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c)))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply ag_br.
Qed.

Lemma anl_csl_rr_select n (ts : pool sE (S n)) m (memory : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= φ AN ψ )>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma anr_csl_rr_select n (ts : pool sE (S n)) m (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    ts (None) m (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma aul_csl_rr_select n (ts : pool sE (S n)) m (memory : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= φ AU ψ )>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma aur_csl_rr_select n (ts : pool sE (S n)) m (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    ts (None) m (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma ag_csl_rr_select n (ts : pool sE (S n)) m (memory : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (memory,(ctx,c))}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,(ctx,c))}, {w} |= AG φ )>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

(** ** Valid whole-block free through the shared raw heap event *)

Lemma anl_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c))}, {w} |= φ AN ψ )>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma anr_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   <[ {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c))}, {w} |= φ AN ψ ]>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma aul_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c))}, {w} |= φ AU ψ )>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma aur_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   <[ {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c))}, {w} |= φ AU ψ ]>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma ag_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,(ctx,c))}, {w} |= AG φ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',(ctx,c))}, {w} |= AG φ )>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' ctx c Free); reflexivity.
Qed.

Lemma anl_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c))}, {w} |= φ AN ψ )>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' ctx c Free); reflexivity.
Qed.

Lemma anr_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AN ψ ]> <->
   <[ {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c))}, {w} |= φ AN ψ ]>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' ctx c Free); reflexivity.
Qed.

Lemma aul_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) ctx c w
  (φ ψ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c))}, {w} |= φ AU ψ )>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' ctx c Free); reflexivity.
Qed.

Lemma aur_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) (ψ : ticlrW (CSLObs (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= φ AU ψ ]> <->
   <[ {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c))}, {w} |= φ AU ψ ]>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' ctx c Free); reflexivity.
Qed.

Lemma ag_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) ctx c w
  (φ : ticllW (CSLObs (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,(ctx,c))}, {w} |= AG φ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',(ctx,c))}, {w} |= AG φ )>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' ctx c Free); reflexivity.
Qed.
