From TICL Require Export ICTree.Trace.
From Stdlib Require Import Fin Vector List Arith.PeanoNat Lia.
From TICL Require Import
  Lang.CSL.Syntax Lang.CSL.Heap Lang.CSL.Denote
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Trans ICTree.Logic.State Logic.World
  ICTree.Events.Writer ICTree.Events.Yield
  ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin ICTree.Interp.Refine
  ICTree.Interp.State.Mod Utils.Vectors.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

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

(** Raw source equations retain the outer option; in particular a successful
    remote publication must return through its caller before reaching Yield. *)
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

Definition scheduled (p : CProg unit) : completed sE :=
  schedule 1 [denote p]%vector (Some Fin.F1).
Definition scheduled_rr (p : CProg unit) : completed sE :=
  run_round_robin (scheduled p) 0.
Definition run_rr (p : CProg unit) (h : Heap) (c : nat)
  : ictreeW SObs (unit * SSig) :=
  interp_schedule_rr sh 1 [denote p]%vector (Some Fin.F1) 0 (h,c).

Definition interp_nd (n : nat) (ts : pool sE n)
  (focus : option (Fin.t n)) (sigma : SSig)
  : ictreeW SObs (unit * SSig) :=
  interp_state sh (interp_yield (interp_spawn (schedule n ts focus))) sigma.

Definition run_nd (p : CProg unit) (h : Heap) (c : nat)
  : ictreeW SObs (unit * SSig) :=
  interp_nd 1 [denote p]%vector (Some Fin.F1) (h,c).

Lemma run_rr_unfold p h c :
  run_rr p h c ≅
  interp_state sh (interp_yield (interp_spawn (scheduled_rr p))) (h,c).
Proof. reflexivity. Qed.

(** Keep one scheduler continuation fixed while interpreting a raw user event. *)
Lemma interp_rr_user_bind n (ts : pool sE (S n)) (i : Fin.t (S n))
  (t : thread sE) (e : sE) (k : encode e -> thread sE) m sigma :
  t ≅ Vis (inr (inr e)) k ->
  interp_schedule_rr sh (S n) (ts @ i := t) (Some i) m sigma ~
  (interp_state sh (@ICtree.trigger sE sE _ _ ReSum_refl ReSumRet_refl e) sigma >>=
    fun '(x,sigma') =>
      interp_schedule_rr sh (S n) (ts @ i := k x) (Some i) m sigma').
Proof.
  intro Hnode.
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := t) (ts @ i := Vis (inr (inr e)) k) (Some i) m sigma
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user with (e:=e) (k:=k)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite interp_state_trigger_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros [x sigma']].
  rewrite Vector.replace_replace_eq; reflexivity.
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
  apply (interp_rr_user_bind n ts i _ (inl (HRead a))
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
  apply (interp_rr_user_bind n ts i _ (inl (HAlloc size))
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
  apply (interp_rr_user_bind n ts i _ (inl (HCAS a expected desired))
    (fun b => K (Some b)) m sigma).
  apply source_raw_cas_head.
Qed.

Lemma interp_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m σ ~
  (interp_state sh (heap_write (E:=sE) a v) σ >>= fun '(_,σ') =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m σ').
Proof.
  apply (interp_rr_user_bind n ts i _ (inl (HWrite a v))
    (fun _ => K (Some tt)) m σ).
  apply source_raw_write_head.
Qed.

Lemma interp_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  q v (K : option unit -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit q v) >>= K)) (Some i) m σ ~
  (interp_state sh (semit q v) σ >>= fun '(_,σ') =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m σ').
Proof.
  apply (interp_rr_user_bind n ts i _ (inr (Log (q,v)))
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

Lemma run_rr_fork_bind (p : CProg unit) (next : unit -> CProg unit) h c :
  run_rr (CBind (CFork p) next) h c ~
  interp_schedule_rr sh 2 [denote p; denote (next tt)]%vector
    (Some (Fin.FS Fin.F1)) 0 (h,c).
Proof.
  unfold run_rr.
  assert (Hpool : pool_equ [denote (CBind (CFork p) next)]%vector
    [Vis (inr (inl Fork))
      (fun child : bool => if child then denote p else denote (next tt))]%vector).
  { apply cons_pool_equ; [apply denote_fork_bind|apply pool_equ_refl]. }
  rewrite (interp_schedule_rr_equ sh 1 _ _ (Some Fin.F1) 0 (h,c) Hpool).
  erewrite interp_schedule_rr_fork by reflexivity.
  reflexivity.
Qed.

Lemma interp_nd_equ n (ts ts' : pool sE n) focus sigma :
  pool_equ ts ts' ->
  interp_nd n ts focus sigma ≅ interp_nd n ts' focus sigma.
Proof.
  intro Hts; unfold interp_nd.
  apply equ_interp_state; [|reflexivity].
  apply interp_yield_equ, interp_spawn_equ.
  now apply schedule_pool_proper.
Qed.

Lemma interp_nd_empty sigma :
  interp_nd 0 ([] : pool sE 0) None sigma ~ Ret (tt,sigma).
Proof.
  unfold interp_nd.
  assert (Hempty : schedule 0 ([] : pool sE 0) None ≅ Ret tt).
  { rewrite (ictree_eta (schedule 0 ([] : pool sE 0) None)), schedule_empty_none.
    reflexivity. }
  rewrite Hempty, interp_erase_ret, interp_state_ret; reflexivity.
Qed.

Lemma interp_nd_ret n (ts : pool sE (S n)) (i : Fin.t (S n)) sigma :
  observe (ts $ i) = RetF tt ->
  interp_nd (S n) ts (Some i) sigma ~ interp_nd n (ts -- i) None sigma.
Proof.
  intro Hobs; unfold interp_nd at 1.
  assert (Hnode : schedule (S n) ts (Some i) ≅ Guard (schedule n (ts -- i) None)).
  { rewrite (ictree_eta (schedule (S n) ts (Some i))),
      (schedule_focused_ret n ts i Hobs); reflexivity. }
  rewrite Hnode, interp_erase_guard, interp_state_tau, sb_guard; reflexivity.
Qed.

Lemma interp_nd_guard n (ts : pool sE (S n)) (i : Fin.t (S n)) t sigma :
  observe (ts $ i) = GuardF t ->
  interp_nd (S n) ts (Some i) sigma ~
    interp_nd (S n) (ts @ i := t) (Some i) sigma.
Proof.
  intro Hobs; unfold interp_nd at 1.
  assert (Hnode : schedule (S n) ts (Some i) ≅
    Guard (schedule (S n) (ts @ i := t) (Some i))).
  { rewrite (ictree_eta (schedule (S n) ts (Some i))),
      (schedule_focused_guard n ts i t Hobs); reflexivity. }
  rewrite Hnode, interp_erase_guard, interp_state_tau, sb_guard; reflexivity.
Qed.

Lemma interp_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n)) k sigma :
  observe (ts $ i) = VisF (inl Yield) k ->
  interp_nd (S n) ts (Some i) sigma ~
    interp_nd (S n) (ts @ i := k tt) None sigma.
Proof.
  intro Hobs; unfold interp_nd at 1.
  assert (Hnode : schedule (S n) ts (Some i) ≅
    Guard (schedule (S n) (ts @ i := k tt) None)).
  { rewrite (ictree_eta (schedule (S n) ts (Some i))),
      (schedule_focused_yield n ts i k Hobs); reflexivity. }
  rewrite Hnode, interp_erase_guard, interp_state_tau, sb_guard; reflexivity.
Qed.

Lemma interp_nd_select n (ts : pool sE (S n)) sigma :
  interp_nd (S n) ts None sigma ~
    Br n (fun i => interp_nd (S n) ts (Some i) sigma).
Proof.
  unfold interp_nd at 1.
  assert (Hnode : schedule (S n) ts None ≅
    Vis (inl Yield) (fun _ => Br n (fun i => schedule (S n) ts (Some i)))).
  { rewrite (ictree_eta (schedule (S n) ts None)), schedule_no_focus_nonempty.
    reflexivity. }
  rewrite Hnode, interp_erase_yield, interp_state_tau, sb_guard,
    interp_state_tau, sb_guard.
  rewrite interp_erase_br, interp_state_br.
  apply sb_br_id; intro i.
  rewrite sb_guard, interp_state_tau, sb_guard, interp_state_tau, sb_guard;
    reflexivity.
Qed.

Lemma interp_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n)) k sigma :
  observe (ts $ i) = VisF (inr (inl Fork)) k ->
  interp_nd (S n) ts (Some i) sigma ~
    interp_nd (S (S n)) (k true :: (ts @ i := k false))
      (Some (Fin.FS i)) sigma.
Proof.
  intro Hobs; unfold interp_nd at 1.
  assert (Hnode : schedule (S n) ts (Some i) ≅
    Vis (inr (inl Spawn)) (fun _ =>
      schedule (S (S n)) (k true :: (ts @ i := k false)) (Some (Fin.FS i)))).
  { rewrite (ictree_eta (schedule (S n) ts (Some i))),
      (schedule_focused_fork n ts i k Hobs); reflexivity. }
  rewrite Hnode, interp_erase_spawn, interp_state_tau, sb_guard; reflexivity.
Qed.

Lemma interp_nd_user n (ts : pool sE (S n)) (i : Fin.t (S n)) e k sigma :
  observe (ts $ i) = VisF (inr (inr e)) k ->
  interp_nd (S n) ts (Some i) sigma ~
    (runStateT (sh e) sigma >>= fun '(x,sigma') =>
     interp_nd (S n) (ts @ i := k x) (Some i) sigma').
Proof.
  intro Hobs; unfold interp_nd at 1.
  assert (Hnode : schedule (S n) ts (Some i) ≅
    Vis (inr (inr e) : yieldE + (spawnE + sE))
      (fun x => schedule (S n) (ts @ i := k x) (Some i))).
  { rewrite (ictree_eta (schedule (S n) ts (Some i))),
      (schedule_focused_user_event n ts i e k Hobs); reflexivity. }
  rewrite Hnode, interp_erase_user, interp_state_vis.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [x sigma']; rewrite sb_guard, interp_state_tau, sb_guard,
    interp_state_tau, sb_guard; reflexivity.
Qed.

Lemma interp_nd_user_bind n (ts : pool sE (S n)) (i : Fin.t (S n))
  (t : thread sE) (e : sE) (k : encode e -> thread sE) sigma :
  t ≅ Vis (inr (inr e)) k ->
  interp_nd (S n) (ts @ i := t) (Some i) sigma ~
  (interp_state sh (@ICtree.trigger sE sE _ _ ReSum_refl ReSumRet_refl e) sigma >>=
    fun '(x,sigma') => interp_nd (S n) (ts @ i := k x) (Some i) sigma').
Proof.
  intro Hnode.
  pose proof (interp_nd_equ (S n)
    (ts @ i := t) (ts @ i := Vis (inr (inr e)) k) (Some i) sigma
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_nd_user with (e:=e) (k:=k)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite interp_state_trigger_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros [x sigma']].
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_ret {A} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) σ ≅
  interp_nd (S n) (ts @ i := K (Some x)) (Some i) σ.
Proof.
  apply interp_nd_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_ret.
Qed.

Lemma interp_nd_source_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) σ ~
  (interp_state sh (heap_read (E:=sE) a) σ >>= fun '(x,σ') =>
    interp_nd (S n) (ts @ i := K (Some x)) (Some i) σ').
Proof.
  apply (interp_nd_user_bind n ts i _ (inl (HRead a))
    (fun x => K (Some x)) σ).
  apply source_raw_read_head.
Qed.

Lemma interp_nd_source_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) sigma :
  interp_nd (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) sigma ~
  (interp_state sh (heap_alloc (E:=sE) size) sigma >>= fun '(base,sigma') =>
    interp_nd (S n) (ts @ i := K (Some base)) (Some i) sigma').
Proof.
  apply (interp_nd_user_bind n ts i _ (inl (HAlloc size))
    (fun base => K (Some base)) sigma).
  apply source_raw_alloc_head.
Qed.

Lemma interp_nd_source_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE) sigma :
  interp_nd (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K))
    (Some i) sigma ~
  (interp_state sh (heap_cas (E:=sE) a expected desired) sigma >>= fun '(b,sigma') =>
   interp_nd (S n) (ts @ i := K (Some b)) (Some i) sigma').
Proof.
  apply (interp_nd_user_bind n ts i _ (inl (HCAS a expected desired))
    (fun b => K (Some b)) sigma).
  apply source_raw_cas_head.
Qed.

Lemma interp_nd_source_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) σ ~
  (interp_state sh (heap_write (E:=sE) a v) σ >>= fun '(_,σ') =>
    interp_nd (S n) (ts @ i := K (Some tt)) (Some i) σ').
Proof.
  apply (interp_nd_user_bind n ts i _ (inl (HWrite a v))
    (fun _ => K (Some tt)) σ).
  apply source_raw_write_head.
Qed.

Lemma interp_nd_source_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  q v (K : option unit -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow (CEmit q v) >>= K)) (Some i) σ ~
  (interp_state sh (semit q v) σ >>= fun '(_,σ') =>
    interp_nd (S n) (ts @ i := K (Some tt)) (Some i) σ').
Proof.
  apply (interp_nd_user_bind n ts i _ (inr (Log (q,v)))
    (fun _ => K (Some tt)) σ).
  apply source_raw_emit_head.
Qed.

Lemma interp_nd_source_bind {A B} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) σ :
  interp_nd (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) σ ≅
  interp_nd (S n)
    (ts @ i := (denote_flow p >>= fun r =>
      match r with None => K None | Some x => denote_flow (next x) >>= K end))
    (Some i) σ.
Proof.
  apply interp_nd_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_bind.
Qed.

Lemma interp_nd_source_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) σ ~
  interp_nd (S n) (ts @ i := K (Some tt)) None σ.
Proof.
  pose proof (interp_nd_equ (S n)
    (ts @ i := (denote_flow CYield >>= K))
    (ts @ i := Vis (inl Yield) (fun _ => K (Some tt)))
    (Some i) σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_yield_head K))) as Hpool.
  rewrite Hpool.
  erewrite interp_nd_yield by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg unit) (K : option unit -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow (CFork p) >>= K)) (Some i) σ ~
  interp_nd (S (S n))
    ((denote_flow p >>= fun _ => K None) :: (ts @ i := K (Some tt)))
    (Some (Fin.FS i)) σ.
Proof.
  pose proof (interp_nd_equ (S n)
    (ts @ i := (denote_flow (CFork p) >>= K))
    (ts @ i := Vis (inr (inl Fork))
      (fun child : bool => if child
        then denote_flow p >>= fun _ => K None else K (Some tt)))
    (Some i) σ
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (source_raw_fork_head p K))) as Hpool.
  rewrite Hpool.
  erewrite interp_nd_fork by (rewrite Vector.nth_replace_eq; reflexivity).
  rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_until_none {A} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) σ :
  interp_nd (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) σ ≅
  interp_nd (S n)
    (ts @ i := (denote_flow body >>= fun r =>
      match r with
      | None => K None
      | Some None => K (Some tt)
      | Some (Some _) => Guard (denote_flow (CUntilNone body) >>= K)
      end)) (Some i) σ.
Proof.
  apply interp_nd_equ, replace_pool_equ; [apply pool_equ_refl|].
  apply source_raw_until.
Qed.

(** Silent checked writes, with the continuation held fixed while the state
    handler is simplified.  No congruence on a pool of bisimilar threads is
    used here. *)
Lemma interp_rr_write_present n
  (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h c :
  h a <> None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt))
    (Some i) m (upd h a v,c).
Proof.
  intro Present.
  pose proof (sinterp_wr' a h c v
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
  a v (K : option unit -> thread sE) h c :
  h a <> None ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) (h,c) ~
  interp_nd (S n) (ts @ i := K (Some tt))
    (Some i) (upd h a v,c).
Proof.
  intro Present.
  pose proof (sinterp_wr' a h c v
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
  a value (K : option nat -> thread sE) m h c :
  h a = Some value ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some value)) (Some i) m (h,c).
Proof.
  intro Lookup.
  pose proof (sinterp_rd a h c value
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
  a value (K : option nat -> thread sE) h c :
  h a = Some value ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) (h,c) ~
  interp_nd (S n) (ts @ i := K (Some value)) (Some i) (h,c).
Proof.
  intro Lookup.
  pose proof (sinterp_rd a h c value
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
  tag value (K : option unit -> thread sE) m h c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (h,c) ~
  (log (SPop tag value c);;
   interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)).
Proof.
  pose proof (sinterp_emit tag value h c
    (fun x : unit => (Ret x : ictree sE unit))) as Hemit.
  rewrite bind_ret_r in Hemit.
  assert (Hstate : interp_state sh (semit tag value) (h,c) ~
    (log (SPop tag value c);; Ret (tt,(h,S c)))).
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
  a expected desired current (K : option bool -> thread sE) m h c :
  h a = Some current ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m (h,c) ~
  (if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m (upd h a desired,c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m (h,c)).
Proof.
  intro Lookup; rewrite interp_rr_cas.
  destruct (Nat.eqb current expected) eqn:Cmp.
  - apply Nat.eqb_eq in Cmp; subst current.
    pose proof (sinterp_cas_success a expected desired h c
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
    pose proof (sinterp_cas_failure a expected desired current h c
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
  size base (K : option nat -> thread sE) m h c :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c).
Proof.
  intros Pos Base Free First.
  pose proof (sinterp_alloc_first h size base c
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
  a (K : option nat -> thread sE) m h c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m (h,c) ~
  (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intro Missing.
  pose proof (sinterp_srd_stuck a h c Missing) as Hstate.
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
  a v (K : option unit -> thread sE) m h c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m (h,c) ~
  (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intro Missing.
  pose proof (sinterp_swr_stuck a v h c Missing) as Hstate.
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
  a expected desired (K : option bool -> thread sE) m h c :
  h a = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m (h,c) ~
  (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intro Missing.
  pose proof (sinterp_cas_missing a expected desired h c
    (fun x : bool => (Ret x : ictree sE bool)) Missing) as Hstate.
  rewrite bind_ret_r in Hstate.
  rewrite interp_rr_cas.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_rr_alloc_zero n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option nat -> thread sE) m h c :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) m (h,c) ~
  (stuck : ictreeW SObs (unit * SSig)).
Proof.
  pose proof (sinterp_salloc_zero h c) as Hstate.
  rewrite interp_rr_alloc.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [eapply equ_clos_sbisim_goal; [exact Hstate | reflexivity | reflexivity] | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_rr_alloc_no_space n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h c :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c) ~
  (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intros Pos Full.
  assert (Hstate : interp_state sh (heap_alloc (E:=sE) size) (h,c) ≅
    (stuck : ictreeW SObs (nat * SSig))).
  { unfold heap_alloc, ICtree.trigger, resum, resum_ret, ReSum_inl, ReSumRet_inl.
    rewrite interp_state_vis.
    change ((alloc_search (W:=SObs) h size 1 c >>=
      fun '(base,sigma') => Guard (interp_state sh (Ret base) sigma')) ≅ stuck).
    etransitivity.
    - apply equ_clo_bind with (S:=eq)
        (k2:=fun '(base,sigma') => Guard (interp_state sh (Ret base) sigma')).
      + apply (alloc_search_no_space (W:=SObs) h size 1 c Pos).
        intros base Positive; apply Full; lia.
      + intros result result' <-; reflexivity.
    -
    apply bind_stuck_equ. }
  rewrite interp_rr_alloc.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [eapply equ_clos_sbisim_goal; [exact Hstate | reflexivity | reflexivity] | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_nd_source_emit_log n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) h c :
  interp_nd (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (h,c) ~
  (log (SPop tag value c);;
   interp_nd (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)).
Proof.
  pose proof (sinterp_emit tag value h c
    (fun x : unit => (Ret x : ictree sE unit))) as Hemit.
  rewrite bind_ret_r in Hemit.
  assert (Hstate : interp_state sh (semit tag value) (h,c) ~
    (log (SPop tag value c);; Ret (tt,(h,S c)))).
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
  a expected desired current (K : option bool -> thread sE) h c :
  h a = Some current ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (h,c) ~
  (if Nat.eqb current expected then
    interp_nd (S n)
    (ts @ i := K (Some true)) (Some i) (upd h a desired,c)
  else
    interp_nd (S n)
    (ts @ i := K (Some false)) (Some i) (h,c)).
Proof.
  intro Lookup; rewrite interp_nd_source_cas.
  destruct (Nat.eqb current expected) eqn:Cmp.
  - apply Nat.eqb_eq in Cmp; subst current.
    pose proof (sinterp_cas_success a expected desired h c
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
    pose proof (sinterp_cas_failure a expected desired current h c
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
  size base (K : option nat -> thread sE) h c :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c) ~
  interp_nd (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c).
Proof.
  intros Pos Base Free First.
  pose proof (sinterp_alloc_first h size base c
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
  a (K : option nat -> thread sE) h c :
  h a = None ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) (h,c) ~
  (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intro Missing.
  pose proof (sinterp_srd_stuck a h c Missing) as Hstate.
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
  a v (K : option unit -> thread sE) h c :
  h a = None ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) (h,c) ~
  (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intro Missing.
  pose proof (sinterp_swr_stuck a v h c Missing) as Hstate.
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
  a expected desired (K : option bool -> thread sE) h c :
  h a = None ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (h,c) ~
  (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intro Missing.
  pose proof (sinterp_cas_missing a expected desired h c
    (fun x : bool => (Ret x : ictree sE bool)) Missing) as Hstate.
  rewrite bind_ret_r in Hstate.
  rewrite interp_nd_source_cas.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [exact Hstate | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_nd_source_alloc_zero n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option nat -> thread sE) h c :
  interp_nd (S n)
    (ts @ i := (denote_flow (CAlloc 0) >>= K)) (Some i) (h,c) ~
  (stuck : ictreeW SObs (unit * SSig)).
Proof.
  pose proof (sinterp_salloc_zero h c) as Hstate.
  rewrite interp_nd_source_alloc.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [eapply equ_clos_sbisim_goal; [exact Hstate | reflexivity | reflexivity] | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_nd_source_alloc_no_space n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h c :
  Nat.lt 0 size ->
  (forall base, Nat.lt 0 base -> ~ block_free h base size) ->
  interp_nd (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c) ~
  (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intros Pos Full.
  assert (Hstate : interp_state sh (heap_alloc (E:=sE) size) (h,c) ≅
    (stuck : ictreeW SObs (nat * SSig))).
  { unfold heap_alloc, ICtree.trigger, resum, resum_ret, ReSum_inl, ReSumRet_inl.
    rewrite interp_state_vis.
    change ((alloc_search (W:=SObs) h size 1 c >>=
      fun '(base,sigma') => Guard (interp_state sh (Ret base) sigma')) ≅ stuck).
    etransitivity.
    - apply equ_clo_bind with (S:=eq)
        (k2:=fun '(base,sigma') => Guard (interp_state sh (Ret base) sigma')).
      + apply (alloc_search_no_space (W:=SObs) h size 1 c Pos).
        intros base Positive; apply Full; lia.
      + intros result result' <-; reflexivity.
    -
    apply bind_stuck_equ. }
  rewrite interp_nd_source_alloc.
  lazymatch goal with
  | |- (interp_state sh _ _ >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2 := next);
      [eapply equ_clos_sbisim_goal; [exact Hstate | reflexivity | reflexivity] | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

(** Physical free is a raw shared command, not a source constructor. *)

Lemma raw_heap_free_head a (K : unit -> thread sE) :
  (heap_free (E:=CEff) a >>= K) ≅
    Vis (inr (inr (inl (HFree a)))) K.
Proof.
  unfold heap_free, ICtree.trigger, resum, resum_ret,
    ReSum_heap_CEff, ReSumRet_heap_CEff.
  rewrite bind_vis; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) m h c :
  interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) m (h,c) ~
  interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (Pcm.hfree a h,c).
Proof.
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K))
    (ts @ i := Vis (inr (inr (inl (HFree a)))) K)
    (Some i) m (h,c)
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_heap_free_head a K))) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user with (e:=inl (HFree a)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (sh_free a h c) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l, Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) h c :
  interp_nd (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) (h,c) ~
  interp_nd (S n)
    (ts @ i := K tt) (Some i) (Pcm.hfree a h,c).
Proof.
  pose proof (interp_nd_equ (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K))
    (ts @ i := Vis (inr (inr (inl (HFree a)))) K)
    (Some i) (h,c)
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_heap_free_head a K))) as Hpool.
  rewrite Hpool.
  erewrite interp_nd_user with (e:=inl (HFree a)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (sh_free a h c) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l, Vector.replace_replace_eq; reflexivity.
Qed.


(** Only finite leading guards and raw tree equivalence are forgotten.
    A real [Br] node is never included in this closure. *)
Inductive guard_equ : thread sE -> thread sE -> Prop :=
| guard_equ_equ t u : t ≅ u -> guard_equ t u
| guard_equ_left t u : guard_equ t u -> guard_equ (Guard t) u
| guard_equ_right t u : guard_equ t u -> guard_equ t (Guard u)
| guard_equ_sym t u : guard_equ t u -> guard_equ u t
| guard_equ_trans t u v : guard_equ t u -> guard_equ u v -> guard_equ t v.

(** ** Pool-shape tactics for concrete round-robin computations. *)

Ltac source_observe :=
  lazy [observe _observe Vector.nth Vector.replace Vector.caseS'
    denote denote_flow ICtree.bind ICtree.subst' rr_pick
    heap_read heap_write heap_alloc heap_cas ICtree.trigger
    resum resum_ret ReSum_heap_CEff ReSumRet_heap_CEff
    ReSum_tagged_CEff ReSumRet_tagged_CEff
    Nat.modulo Nat.divmod Fin.of_nat_lt]; reflexivity.

Ltac pool_simpl :=
  cbv [Vector.replace Vector.caseS' rr_pick Nat.modulo Nat.divmod Fin.of_nat_lt].

Ltac finish_pool :=
  repeat first
    [ progress pool_simpl
    | rewrite vector_remove_head
    | rewrite vector_remove_tail
    | erewrite interp_schedule_rr_ret by source_observe
    | rewrite interp_schedule_rr_select
    | rewrite interp_schedule_rr_empty ];
  reflexivity.
