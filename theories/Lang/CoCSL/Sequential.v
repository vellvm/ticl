(** * Cooperative prefixes of CoCSL source programs.

    Yield/fork-free code executes its standalone checked prefix and rejoins
    the actual pool with the resulting state. Round-robin and fair prefixes
    preserve scheduler state and relabel program observations under [inl].
    Chronological write plans retain repeated snapshots and stop at the first
    missing address. *)

From TICL Require Export Lang.CoCSL.Mod CTree.Interp.Yield.Sequential.
From Stdlib Require Import Fin Vector Arith.PeanoNat List.
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
  CTree.Interp.Yield.Policy
  CTree.Interp.Yield.RoundRobin
  CTree.Interp.Yield.Nondeterministic
  CTree.Interp.Yield.Fair
  CTree.Trace
  Logic.World
  Events.HeapModel
  CTree.Interp.Heap
  Utils.Vectors.

Import CTreeNotations ListNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.

(** No yield, fork, or variable read ([CVar] itself yields). *)
Definition yield_fork_free {A} (p : CProg A) : Prop := prog_ok user_only p.

(** A yield/fork-free program denotes a sequential raw thread. *)
Lemma denote_flow_sequential {A} (p : CProg A) : yield_fork_free p -> Sequential (denote_flow p).
Proof.
  intro H; split; [apply denote_flow_branchfree|exact (denote_flow_framable user_only p H)].
Qed.

(** Chronological checked writes. Every occurrence performs a write, including
    repeated keys; a missing cell stops the source program at that occurrence. *)
Fixpoint write_list (ws : list (nat * nat)) : CProg unit :=
  match ws with
  | List.nil => CRet tt
  | List.cons (a,v) rest => CBind (CWrite a v) (fun _ => write_list rest)
  end.

(** Heap observations retain the allocation table and do not stamp an event or
    advance the source counter. The list includes every intermediate memory. *)
Fixpoint write_snapshots {A} (ws : list (nat * nat))
    (memory : ManagedHeap) : list (CSLObs A) :=
  match ws with
  | List.nil => List.nil
  | List.cons (a,v) rest =>
      let next := (upd (fst memory) a v,snd memory) in
      List.cons (CSLHeap next) (write_snapshots rest next)
  end.

Lemma write_list_yield_fork_free ws : yield_fork_free (write_list ws).
Proof.
  induction ws as [|[a v] rest IH]; cbn [write_list yield_fork_free prog_ok user_only].
  - exact I.
  - split; [exact I|intro; exact IH].
Qed.

Lemma write_list_alloc_free ws : alloc_free (write_list ws).
Proof.
  induction ws as [|[a v] rest IH]; cbn [write_list alloc_free prog_ok okE_thread no_alloc_sE].
  - exact I.
  - split; [exact I|intro; exact IH].
Qed.

Lemma write_snapshots_length {A} ws memory :
  List.length (write_snapshots (A:=A) ws memory) = List.length ws.
Proof.
  revert memory; induction ws as [|[a v] rest IH]; intro memory;
    cbn [write_snapshots List.length]; [reflexivity|now rewrite IH].
Qed.

Lemma write_snapshots_app {A} xs ys memory :
  write_snapshots (A:=A) (List.app xs ys) memory =
  List.app (write_snapshots xs memory)
    (write_snapshots ys (apply_writes xs (fst memory),snd memory)).
Proof.
  revert memory; induction xs as [|[a v] rest IH]; intros [h allocs].
  - reflexivity.
  - cbn [write_snapshots List.app]; rewrite apply_writes_cons, IH; reflexivity.
Qed.

Lemma write_snapshots_last_heap {A} ws memory :
  List.last (write_snapshots (A:=A) ws memory) (CSLHeap memory) =
  CSLHeap (apply_writes ws (fst memory),snd memory).
Proof.
  induction ws as [|[a v] ws IH] using List.rev_ind; [destruct memory; reflexivity|].
  rewrite write_snapshots_app; cbn [write_snapshots]; rewrite List.last_last.
  rewrite apply_writes_app; destruct memory; reflexivity.
Qed.

Lemma write_snapshots_after {A} ws memory :
  after_logs (write_snapshots (A:=A) ws memory)
    (Obs (Log (CSLHeap memory)) tt) =
  Obs (Log (CSLHeap (apply_writes ws (fst memory),snd memory))) tt.
Proof.
  revert memory; induction ws as [|[a v] rest IH]; intros [h allocs]; [reflexivity|].
  cbn [write_snapshots after_logs fst snd]; rewrite apply_writes_cons; exact (IH (upd h a v,allocs)).
Qed.

(** Native source return has no observation or state effect. *)
Lemma instr_flow_ret {A} (value : A) (s : SSig) :
  instr_flow_erased (CRet value) s ≅
    (Ret (s, Some value) : ctreeW (CSLObs (nat * nat)) Bn (SSig * option A)).
Proof.
  unfold instr_flow_erased; cbn [denote_flow]; rewrite interp_state_thread_ret; reflexivity.
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
  cbn [denote_flow denote_exp];
  unfold heap_read, heap_write, heap_alloc, heap_free, heap_cas, source_get, source_put, CTree.trigger;
  repeat first [rewrite bind_ret_l | rewrite bind_bind | rewrite bind_vis];
  step; constructor; intro; try rewrite !bind_ret_l; reflexivity.

(** Read an owned cell and continue with its value in the standalone erased run. *)
Lemma instr_flow_read {A} a v (k : nat -> CProg A) (s : SSig) :
  fst (csl_memory s) a = Some v ->
  instr_flow_erased (CBind (CRead a) k) s ~ instr_flow_erased (k v) s.
Proof.
  intro Hv.
  rewrite instr_flow_head with (e := inl1 (HRead a)) (k := fun v => denote_flow (k v)); [|flow_head].
  cbn [sh h_sum]; destruct s as [[h al] aux]; cbn [csl_memory fst snd] in Hv |- *.
  rewrite (heap_handlerW_rd_some CSLHeap a h al aux v Hv), bind_ret_l; reflexivity.
Qed.

(** Write an owned cell and continue in the updated standalone state. *)
Lemma instr_flow_write {A} a v (k : unit -> CProg A) (s : SSig) :
  fst (csl_memory s) a <> None ->
  instr_flow_erased (CBind (CWrite a v) k) s ~
  (log (CSLHeap (upd (fst (csl_memory s)) a v, snd (csl_memory s)));;
   instr_flow_erased (k tt) ((upd (fst (csl_memory s)) a v, snd (csl_memory s)), snd s)).
Proof.
  intro Hv.
  rewrite instr_flow_head with (e := inl1 (HWrite a v)) (k := fun _ => denote_flow (k tt)); [|flow_head].
  cbn [sh h_sum]; destruct s as [[h al] aux]; cbn [csl_memory fst snd] in Hv |- *.
  destruct (h a) as [old|] eqn:Hh; [|contradiction].
  rewrite (heap_handlerW_wr_some CSLHeap a h al aux v old Hh), bind_bind.
  setoid_rewrite bind_ret_l; reflexivity.
Qed.

(** A standalone write logs its post-memory, then returns [Some tt]. *)
Lemma instr_flow_write_single a v (s : SSig) :
  fst (csl_memory s) a <> None ->
  instr_flow_erased (CWrite a v) s ~
  (log (CSLHeap (upd (fst (csl_memory s)) a v, snd (csl_memory s)));;
   Ret (((upd (fst (csl_memory s)) a v, snd (csl_memory s)), snd s), Some tt)
    : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)).
Proof.
  intro Hv.
  rewrite instr_flow_head with (e := inl1 (HWrite a v)) (k := fun _ => Ret (Some tt)).
  2:{ cbn [denote_flow]; unfold heap_write, CTree.trigger; rewrite bind_vis; step; constructor; intro; rewrite bind_ret_l; reflexivity. }
  cbn [sh h_sum]; destruct s as [[h al] aux]; cbn [csl_memory fst snd] in Hv |- *.
  destruct (h a) as [old|] eqn:Hh; [|contradiction].
  rewrite (heap_handlerW_wr_some CSLHeap a h al aux v old Hh), bind_bind.
  setoid_rewrite bind_ret_l; setoid_rewrite interp_state_thread_ret; reflexivity.
Qed.

(** Each primitive exposes its checked outcome before the source continuation. *)
Lemma instr_flow_read_missing {A} a (k : nat -> CProg A) (s : SSig) :
  fst (csl_memory s) a = None ->
  instr_flow_erased (CBind (CRead a) k) s ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option A)).
Proof.
  intro Hv; rewrite instr_flow_head with (e := inl1 (HRead a))
    (k := fun value => denote_flow (k value)); [|flow_head].
  cbn [sh h_sum]; destruct s as [[h al] aux]; cbn [csl_memory fst snd] in Hv |- *.
  rewrite (heap_handlerW_rd_none CSLHeap a h al aux Hv), bind_stuck; reflexivity.
Qed.

Lemma instr_flow_write_missing {A} a v (k : unit -> CProg A) (s : SSig) :
  fst (csl_memory s) a = None ->
  instr_flow_erased (CBind (CWrite a v) k) s ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option A)).
Proof.
  intro Hv; rewrite instr_flow_head with (e := inl1 (HWrite a v))
    (k := fun _ => denote_flow (k tt)); [|flow_head].
  cbn [sh h_sum]; destruct s as [[h al] aux]; cbn [csl_memory fst snd] in Hv |- *.
  rewrite (heap_handlerW_wr_none CSLHeap a h al aux v Hv), bind_stuck; reflexivity.
Qed.

(** A checked finite prefix keeps the allocation table, context and event
    counter unchanged. Allocated keys may repeat and may include address zero. *)
Lemma instr_flow_write_list ws h allocs aux :
  (forall a v, List.In (a,v) ws -> h a <> None) ->
  instr_flow_erased (write_list ws) ((h,allocs),aux) ~
  emit_list (write_snapshots ws (h,allocs))
    (Ret (((apply_writes ws h,allocs),aux),Some tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)).
Proof.
  revert h; induction ws as [|[a v] rest IH]; intros h Hall.
  - cbn [write_list write_snapshots emit_list apply_writes];
      apply equ_sbisim, instr_flow_ret.
  - cbn [write_list write_snapshots]; rewrite apply_writes_cons.
    rewrite instr_flow_write by (apply (Hall a v); left; reflexivity).
    change ((log (CSLHeap (upd h a v,allocs));;
      instr_flow_erased (write_list rest) ((upd h a v,allocs),aux)) ~
      (log (CSLHeap (upd h a v,allocs));;
       emit_list (write_snapshots rest (upd h a v,allocs))
         (Ret (((apply_writes rest (upd h a v),allocs),aux),Some tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)))).
    __upto_bind_sbisim_eq; intros []; apply IH.
    intros x value Hin; apply upd_mono; apply (Hall x value); right; exact Hin.
Qed.

(** Stop at the first missing address, retaining exactly the preceding
    snapshots and never evaluating the remaining writes. *)
Lemma instr_flow_write_list_fault ws pre a v post h allocs aux :
  ws = List.app pre (List.cons (a,v) post) ->
  (forall x value, List.In (x,value) pre -> h x <> None) ->
  apply_writes pre h a = None ->
  instr_flow_erased (write_list ws) ((h,allocs),aux) ~
  emit_list (write_snapshots pre (h,allocs))
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)).
Proof.
  intro Ews; subst ws; revert h.
  induction pre as [|[x value] pre IH]; intros h Hall Hmissing.
  - cbn [write_list write_snapshots emit_list apply_writes] in *.
    apply instr_flow_write_missing, Hmissing.
  - cbn [List.app write_list write_snapshots].
    rewrite apply_writes_cons in Hmissing.
    rewrite instr_flow_write by (apply (Hall x value); left; reflexivity).
    change ((log (CSLHeap (upd h x value,allocs));;
      instr_flow_erased (write_list (List.app pre (List.cons (a,v) post)))
        ((upd h x value,allocs),aux)) ~
      (log (CSLHeap (upd h x value,allocs));;
       emit_list (write_snapshots pre (upd h x value,allocs)) (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)))).
    __upto_bind_sbisim_eq; intros []; apply IH; [|exact Hmissing].
    intros y val Hin; apply upd_mono; apply (Hall y val); right; exact Hin.
Qed.

Lemma instr_flow_cas_value {A} a expected desired current (k : bool -> CProg A) (s : SSig) :
  fst (csl_memory s) a = Some current ->
  instr_flow_erased (CBind (CCAS (CLit a) (CLit expected) (CLit desired)) k) s ~
    if Nat.eqb current expected then
      log (CSLHeap (upd (fst (csl_memory s)) a desired, snd (csl_memory s)));;
      instr_flow_erased (k true) ((upd (fst (csl_memory s)) a desired, snd (csl_memory s)), snd s)
    else instr_flow_erased (k false) s.
Proof.
  intro Hv; rewrite instr_flow_head with (e := inl1 (HCAS a expected desired))
    (k := fun success => denote_flow (k success)); [|flow_head].
  cbn [sh h_sum]; destruct s as [[h al] aux]; cbn [csl_memory fst snd] in Hv |- *.
  destruct (Nat.eqb current expected) eqn:HC.
  - apply Nat.eqb_eq in HC; subst current.
    rewrite (heap_handlerW_cas_success CSLHeap a expected desired h al aux Hv), bind_bind.
    setoid_rewrite bind_ret_l; reflexivity.
  - apply Nat.eqb_neq in HC.
    rewrite (heap_handlerW_cas_failure CSLHeap a expected desired current h al aux Hv HC), bind_ret_l;
      reflexivity.
Qed.

Lemma instr_flow_cas_missing {A} a expected desired (k : bool -> CProg A) (s : SSig) :
  fst (csl_memory s) a = None ->
  instr_flow_erased (CBind (CCAS (CLit a) (CLit expected) (CLit desired)) k) s ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option A)).
Proof.
  intro Hv; rewrite instr_flow_head with (e := inl1 (HCAS a expected desired))
    (k := fun success => denote_flow (k success)); [|flow_head].
  cbn [sh h_sum]; destruct s as [[h al] aux]; cbn [csl_memory fst snd] in Hv |- *.
  rewrite (heap_handlerW_cas_missing CSLHeap a expected desired h al aux Hv), bind_stuck;
    reflexivity.
Qed.

Lemma instr_flow_free {A} base (k : unit -> CProg A) (s : SSig) memory' :
  managed_free (csl_memory s) base = Some memory' ->
  instr_flow_erased (CBind (CFree base) k) s ~
    match base with
    | 0 => instr_flow_erased (k tt) (memory',snd s)
    | S _ => log (CSLHeap memory');; instr_flow_erased (k tt) (memory',snd s)
    end.
Proof.
  intro HF; rewrite instr_flow_head with (e := inl1 (HFree base))
    (k := fun _ => denote_flow (k tt)); [|flow_head].
  cbn [sh h_sum]; destruct s as [memory aux]; cbn [csl_memory fst snd] in HF |- *.
  rewrite (heap_handlerW_free CSLHeap base memory memory' aux HF).
  destruct base; [rewrite bind_ret_l; reflexivity|].
  rewrite bind_bind; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma instr_flow_free_invalid {A} base (k : unit -> CProg A) (s : SSig) :
  managed_free (csl_memory s) base = None ->
  instr_flow_erased (CBind (CFree base) k) s ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option A)).
Proof.
  intro HF; rewrite instr_flow_head with (e := inl1 (HFree base))
    (k := fun _ => denote_flow (k tt)); [|flow_head].
  cbn [sh h_sum]; destruct s as [memory aux]; cbn [csl_memory fst snd] in HF |- *.
  rewrite (heap_handlerW_free_invalid CSLHeap base memory aux HF), bind_stuck; reflexivity.
Qed.

Lemma instr_flow_alloc_first {A} size base (k : nat -> CProg A) (s : SSig) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free (fst (csl_memory s)) base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free (fst (csl_memory s)) j size) ->
  instr_flow_erased (CBind (CAlloc size) k) s ~
    (log (CSLHeap (managed_alloc (csl_memory s) base size));;
     instr_flow_erased (k base) (managed_alloc (csl_memory s) base size,snd s)).
Proof.
  intros Pos Base Free First.
  rewrite instr_flow_head with (e := inl1 (HAlloc size))
    (k := fun address => denote_flow (k address)); [|flow_head].
  cbn [sh h_sum]; destruct s as [[h al] aux]; cbn [csl_memory fst snd] in Free, First |- *.
  rewrite (heap_handlerW_alloc_first_guards CSLHeap h al size base aux Pos Base Free First),
    bind_guards, guards_sbisim, bind_bind.
  setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma instr_flow_alloc_zero {A} (k : nat -> CProg A) (s : SSig) :
  instr_flow_erased (CBind (CAlloc 0) k) s ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option A)).
Proof.
  rewrite instr_flow_head with (e := inl1 (HAlloc 0))
    (k := fun address => denote_flow (k address)); [|flow_head].
  cbn [sh h_sum]; destruct s as [[h al] aux].
  rewrite (heap_handlerW_alloc_zero CSLHeap h al aux), bind_stuck; reflexivity.
Qed.

Lemma instr_flow_alloc_no_space {A} size (k : nat -> CProg A) (s : SSig) :
  Nat.lt 0 size ->
  (forall j, Nat.lt 0 j -> ~ block_free (fst (csl_memory s)) j size) ->
  instr_flow_erased (CBind (CAlloc size) k) s ~
    (CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * option A)).
Proof.
  intros Pos Full.
  rewrite instr_flow_head with (e := inl1 (HAlloc size))
    (k := fun address => denote_flow (k address)); [|flow_head].
  cbn [sh h_sum]; destruct s as [[h al] aux]; cbn [csl_memory fst snd] in Full.
  rewrite (heap_handlerW_alloc_no_space CSLHeap h al size aux Pos Full), bind_spin; reflexivity.
Qed.

Lemma instr_flow_emit {A} tag value (k : unit -> CProg A) (s : SSig) :
  instr_flow_erased (CBind (CEmit tag value) k) s ~
    (log (CSLEmit (stamp (tag,value) (csl_counter s)));;
     instr_flow_erased (k tt) (csl_memory s,(csl_context s,S (csl_counter s)))).
Proof.
  rewrite instr_flow_head with (e := inr1 (inr1 (Log (tag,value))))
    (k := fun _ => denote_flow (k tt)); [|flow_head].
  cbn [sh h_sum]; destruct s as [memory [ctx c]].
  rewrite (csl_emit_handler_log (tag,value) memory ctx c), bind_bind.
  setoid_rewrite bind_ret_l; reflexivity.
Qed.


(** ** Pool-level prefix equations. *)

(** Join principle: a focused yield/fork-free segment runs standalone, then its round-robin pool continues. *)
Lemma run_rr_prefix {A} n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
  (p : CProg A) (K : option A -> thread sE Bn) m σ :
  yield_fork_free p ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow p >>= K)) (Some i) m σ ~
  (translate relabel_log (instr_flow_erased p σ) >>= fun '(σ', r) =>
    interp_schedule_rr sh (S n) (ts @ i := K r) (Some i) m σ').
Proof.
  intro Hp; unfold instr_flow_erased.
  apply interp_schedule_fair_prefix_bind, denote_flow_sequential, Hp.
Qed.

(** The relabelled standalone run is the standalone run under the policy
    handler, with its events embedded on the left. *)
Lemma instr_flow_sched_interp {A} (p : CProg A) σ :
  translate relabel_log (instr_flow_erased p σ) ≅
  interp_state (policy_handler sh) (translate inl1 (interp_thread (denote_flow p))) σ.
Proof. symmetry; apply interp_state_policy_translate. Qed.

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

(** The fair policy is untouched until the focused source prefix completes. *)
Lemma run_fair_prefix {A} (sch : Scheduler) n (ts : pool sE Bn (S n))
    (i : Fin.t (S n)) (p : CProg A) (K : option A -> thread sE Bn) st sigma :
  yield_fork_free p ->
  interp_schedule_fair sch sh (S n) (ts @ i := (denote_flow p >>= K)) (Some i) st sigma ~
  (translate relabel_log (instr_flow_erased p sigma) >>= fun '(sigma',r) =>
    interp_schedule_fair sch sh (S n) (ts @ i := K r) (Some i) st sigma').
Proof.
  intro Hp; unfold instr_flow_erased.
  apply interp_schedule_fair_prefix_bind, denote_flow_sequential, Hp.
Qed.

(** Any standalone finite sequential return prefix lifts to the instrumented
    scheduler, retaining its precise state and source return value. *)
Lemma interp_fair_sequential {A} (sch : Scheduler) n (ts : pool sE Bn (S n))
    (i : Fin.t (S n)) (p : CProg A) (K : option A -> thread sE Bn)
    st sigma logs sigma' result :
  yield_fork_free p ->
  instr_flow_erased p sigma ~ emit_list logs (Ret (sigma',result) : ctreeW (CSLObs (nat * nat)) Bn (SSig * option A)) ->
  interp_schedule_fair sch sh (S n) (ts @ i := (denote_flow p >>= K)) (Some i) st sigma ~
  emit_list (List.map inl logs)
    (interp_schedule_fair sch sh (S n) (ts @ i := K result) (Some i) st sigma').
Proof.
  intros Hp Hprefix; rewrite run_fair_prefix by exact Hp.
  assert (Hlabels :
    translate relabel_log (instr_flow_erased p sigma) ~
    (emit_list (List.map inl logs) (Ret (sigma',result)) :
      ctreeW (CSLObs (nat * nat) + nat) Bn (SSig * option A))).
  {
    etransitivity; [apply translate_sbisim; exact Hprefix|].
    etransitivity; [apply equ_sbisim, translate_emit_list|].
    apply emit_list_sbisim, equ_sbisim, translate_ret.
  }
  rewrite Hlabels.
  apply equ_sbisim; exact (emit_list_ret_bind (List.map (@inl (CSLObs (nat * nat)) nat) logs)
    (sigma',result) (fun '(s,r) => interp_schedule_fair sch sh (S n)
      (ts @ i := K r) (Some i) st s)).
Qed.

Lemma interp_nd_write_list n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
    ws (K : option unit -> thread sE Bn) h allocs aux :
  (forall a v, List.In (a,v) ws -> h a <> None) ->
  interp_schedule_nd sh (S n) (ts @ i := (denote_flow (write_list ws) >>= K))
    (Some i) ((h,allocs),aux) ~
  emit_list (write_snapshots ws (h,allocs))
    (interp_schedule_nd sh (S n) (ts @ i := K (Some tt)) (Some i)
      ((apply_writes ws h,allocs),aux)).
Proof.
  intro Hall; rewrite run_nd_prefix by apply write_list_yield_fork_free.
  rewrite instr_flow_write_list by exact Hall.
  rewrite emit_list_ret_bind; reflexivity.
Qed.

Lemma interp_rr_write_list n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
    ws (K : option unit -> thread sE Bn) cursor h allocs aux :
  (forall a v, List.In (a,v) ws -> h a <> None) ->
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (write_list ws) >>= K))
    (Some i) cursor ((h,allocs),aux) ~
  emit_list (List.map inl (write_snapshots ws (h,allocs)))
    (interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) cursor
      ((apply_writes ws h,allocs),aux)).
Proof.
  intro Hall; apply (interp_fair_sequential rr_scheduler);
    [apply write_list_yield_fork_free|apply instr_flow_write_list, Hall].
Qed.

Lemma interp_fair_write_list (sch : Scheduler) n (ts : pool sE Bn (S n))
    (i : Fin.t (S n)) ws (K : option unit -> thread sE Bn) st h allocs aux :
  (forall a v, List.In (a,v) ws -> h a <> None) ->
  interp_schedule_fair sch sh (S n) (ts @ i := (denote_flow (write_list ws) >>= K))
    (Some i) st ((h,allocs),aux) ~
  emit_list (List.map inl (write_snapshots ws (h,allocs)))
    (interp_schedule_fair sch sh (S n) (ts @ i := K (Some tt)) (Some i) st
      ((apply_writes ws h,allocs),aux)).
Proof.
  intro Hall; apply interp_fair_sequential;
    [apply write_list_yield_fork_free|apply instr_flow_write_list, Hall].
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
