(** * Cooperative prefixes of CoCSL source programs.

    A yield/fork-free program runs in a pool exactly as its standalone erased
    run [instr_flow_erased], then rejoins the pool with the resulting state.
    This is the join principle that lets per-process facts, framed by the
    other process's region, compose into pool-level facts. *)

From TICL Require Export Lang.CoCSL.Mod CTree.Interp.Yield.Sequential.
From Stdlib Require Import Fin Vector.
From ExtLib Require Import Structures.Maps Data.Map.FMapAList.
From Coinduction Require Import all.
From TICL Require Import
  Lang.CoCSL.Frame
  CTree.Core
  CTree.Events.Heap
  CTree.Events.Writer
  CTree.Interp.State.Mod
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.Nondeterministic
  CTree.Interp.Heap
  Utils.Vectors.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** No yield, fork, or variable read ([CVar] itself yields). *)
Definition yield_fork_free {A} (p : CProg A) : Prop := prog_ok user_only p.

(** A yield/fork-free program denotes a sequential raw thread. *)
Lemma denote_flow_sequential {A} (p : CProg A) : yield_fork_free p -> Sequential (denote_flow p).
Proof.
  intro H; split; [apply denote_flow_branchfree|exact (denote_flow_framable user_only p H)].
Qed.

(** ** One-step equations of the standalone erased run. *)


(** A user-event head runs its handler, then the standalone erased continuation. *)
Lemma instr_flow_head {A} (p : CProg A) {Y} (e : sE Y) (k : Y -> ctree CEff Bn (option A)) (s : SSig) :
  denote_flow p ≅ Vis (inr1 (inr1 e)) k ->
  instr_flow_erased p s ~ (sh _ e s >>= fun '(s', x) => interp_state sh (interp_thread (k x)) s').
Proof.
  intro Hp; unfold instr_flow_erased; rewrite Hp; apply interp_state_thread_user.
Qed.

(** Expose the user event at the head of a bound source program. *)
Local Ltac flow_head :=
  cbn [denote_flow]; unfold heap_read, heap_write, heap_free, heap_cas, source_get, source_put, CTree.trigger;
  rewrite bind_bind, bind_vis; step; constructor; intro; rewrite !bind_ret_l; reflexivity.

(** Read an owned cell and continue with its value in the standalone erased run. *)
Lemma instr_flow_read a v (k : nat -> CProg unit) (s : SSig) :
  fst (csl_memory s) a = Some v ->
  instr_flow_erased (CBind (CRead a) k) s ~ instr_flow_erased (k v) s.
Proof.
  intro Hv.
  rewrite instr_flow_head with (e := inl1 (HRead a)) (k := fun v => denote_flow (k v)); [|flow_head].
  cbn [sh h_sum heap_handler].
  destruct s as [[h al] aux]; cbn in Hv |- *; rewrite Hv, bind_ret_l; reflexivity.
Qed.

(** Write an owned cell and continue in the updated standalone state. *)
Lemma instr_flow_write a v (k : unit -> CProg unit) (s : SSig) :
  fst (csl_memory s) a <> None ->
  instr_flow_erased (CBind (CWrite a v) k) s ~
  instr_flow_erased (k tt) ((upd (fst (csl_memory s)) a v, snd (csl_memory s)), snd s).
Proof.
  intro Hv.
  rewrite instr_flow_head with (e := inl1 (HWrite a v)) (k := fun _ => denote_flow (k tt)); [|flow_head].
  cbn [sh h_sum heap_handler].
  destruct s as [[h al] aux]; cbn in Hv |- *.
  destruct (h a) as [w|] eqn:Hh; [|contradiction].
  rewrite bind_ret_l; reflexivity.
Qed.

(** A standalone write returns the updated state and [Some tt]. *)
Lemma instr_flow_write_single a v (s : SSig) :
  fst (csl_memory s) a <> None ->
  instr_flow_erased (CWrite a v) s ~
  (Ret (((upd (fst (csl_memory s)) a v, snd (csl_memory s)), snd s), Some tt)
    : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)).
Proof.
  intro Hv.
  rewrite instr_flow_head with (e := inl1 (HWrite a v)) (k := fun _ => Ret (Some tt)).
  2:{ cbn [denote_flow]; unfold heap_write, CTree.trigger; rewrite bind_vis; step; constructor; intro; rewrite bind_ret_l; reflexivity. }
  cbn [sh h_sum heap_handler].
  destruct s as [[h al] aux]; cbn in Hv |- *.
  destruct (h a) as [w|] eqn:Hh; [|contradiction].
  rewrite bind_ret_l, interp_state_thread_ret; reflexivity.
Qed.


(** ** Pool-level prefix equations. *)

(** Join principle: a focused yield/fork-free segment runs standalone, then its round-robin pool continues. *)
Lemma run_rr_prefix {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (K : option A -> thread sE Bn) m σ :
  yield_fork_free p ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= K)) (Some i) m σ ~
  (instr_flow_erased p σ >>= fun '(σ', r) =>
    interp_schedule_rr sh (S n) (ts @ i := K r) (Some i) m σ').
Proof.
  intro Hp; unfold instr_flow_erased.
  apply interp_schedule_rr_prefix_bind, denote_flow_sequential, Hp.
Qed.

(** Join principle: a focused yield/fork-free segment runs standalone, then its nondeterministic pool continues. *)
Lemma run_nd_prefix {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (K : option A -> thread sE Bn) σ :
  yield_fork_free p ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow p >>= K)) (Some i) σ ~
  (instr_flow_erased p σ >>= fun '(σ', r) =>
    interp_schedule_nd sh (S n) (ts @ i := K r) (Some i) σ').
Proof.
  intro Hp; unfold instr_flow_erased.
  apply interp_schedule_nd_prefix_bind, denote_flow_sequential, Hp.
Qed.

(** A nondeterministic fork starts the child and continues with the parent focused. *)
Lemma run_nd_fork_bind (p : CProg unit) (next : unit -> CProg unit) (s : SSig) :
  run_nd (CBind (CFork p) next) s ~
  interp_schedule_nd sh 2 [denote p; denote (next tt)]%vector (Some (Fin.FS Fin.F1)) s.
Proof.
  rewrite run_nd_unfold.
  assert (Hpool : pool_equ [denote (CBind (CFork p) next)]%vector
    [Vis (inr1 (inl1 Fork))
      (fun child : bool => if child then denote p else denote (next tt))]%vector).
  { apply cons_pool_equ; [apply denote_fork_bind|apply pool_equ_refl]. }
  rewrite (interp_schedule_nd_equ sh 1 _ _ (Some Fin.F1) s Hpool).
  erewrite (interp_schedule_nd_fork sh) by reflexivity.
  reflexivity.
Qed.
