From Stdlib Require Import Fin Vector.
From TICL Require Import
  Lang.CSL.Syntax Lang.CSL.Heap Lang.CSL.Denote
  ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Events.Yield
  ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin ICTree.Interp.Refine
  ICTree.Interp.State.Mod Utils.Vectors.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

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

Lemma interp_rr_ret {A} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m σ ≅
  interp_schedule_rr sh (S n) (ts @ i := K (Some x)) (Some i) m σ.
Proof.
  apply interp_schedule_rr_equ, replace_pool_equ; [apply pool_equ_refl|].
  cbn [denote_flow]; apply bind_ret_l.
Qed.

Lemma interp_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m σ ~
  (interp_state sh (srd a) σ >>= fun '(x,σ') =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some x)) (Some i) m σ').
Proof.
  assert (Hnode : (denote_flow (CRead a) >>= K) ≅
    Vis (inr (inr (SRd a))) (fun x => K (Some x))).
  {
    cbn [denote_flow]; unfold heap_event.
    rewrite bind_bind, bind_vis; step; constructor; intro x.
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K))
    (ts @ i := Vis (inr (inr (SRd a))) (fun x => K (Some x)))
    (Some i) m σ (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user by (rewrite Vector.nth_replace_eq; reflexivity).
  set (resume := fun result : (nat * SSig)%type =>
    let '(x,σ') := result in
    interp_schedule_rr sh (S n) (ts @ i := K (Some x)) (Some i) m σ').
  assert (Hrhs : (interp_state sh (srd a) σ >>= resume) ≅
    ((runStateT (sh (SRd a)) σ >>= fun '(x,σ') =>
      Guard (interp_state sh (Ret x) σ')) >>= resume)).
  {
    apply equ_clo_bind with (S := eq).
    - unfold srd; apply interp_state_vis.
    - intros r r' <-; reflexivity.
  }
  rewrite Hrhs, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [x σ']; rewrite bind_guard, sb_guard.
  assert (Hret : (interp_state sh (Ret x) σ' >>= resume) ≅ resume (x,σ')).
  {
    transitivity (Ret (x,σ') >>= resume).
    - apply equ_clo_bind with (S := eq); [apply interp_state_ret|].
      intros r r' <-; reflexivity.
    - apply bind_ret_l.
  }
  rewrite Hret; unfold resume; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m sigma :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m sigma ~
  (interp_state sh (salloc size) sigma >>= fun '(base,sigma') =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some base)) (Some i) m sigma').
Proof.
  assert (Hnode : (denote_flow (CAlloc size) >>= K) ≅
    Vis (inr (inr (SAlloc size))) (fun base => K (Some base))).
  {
    cbn [denote_flow]; unfold heap_event.
    rewrite bind_bind, bind_vis; step; constructor; intro base.
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K))
    (ts @ i := Vis (inr (inr (SAlloc size))) (fun base => K (Some base)))
    (Some i) m sigma (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user by (rewrite Vector.nth_replace_eq; reflexivity).
  set (resume := fun result : (nat * SSig)%type =>
    let '(base,sigma') := result in
    interp_schedule_rr sh (S n) (ts @ i := K (Some base)) (Some i) m sigma').
  assert (Hrhs : (interp_state sh (salloc size) sigma >>= resume) ≅
    ((runStateT (sh (SAlloc size)) sigma >>= fun '(base,sigma') =>
      Guard (interp_state sh (Ret base) sigma')) >>= resume)).
  {
    apply equ_clo_bind with (S := eq).
    - unfold salloc; apply interp_state_vis.
    - intros r r' <-; reflexivity.
  }
  rewrite Hrhs, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [base sigma']; rewrite bind_guard, sb_guard.
  assert (Hret : (interp_state sh (Ret base) sigma' >>= resume) ≅ resume (base,sigma')).
  {
    transitivity (Ret (base,sigma') >>= resume).
    - apply equ_clo_bind with (S := eq); [apply interp_state_ret|].
      intros r r' <-; reflexivity.
    - apply bind_ret_l.
  }
  rewrite Hret; unfold resume; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE) m sigma :
  interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K))
    (Some i) m sigma ~
  (interp_state sh (scas a expected desired) sigma >>= fun '(b,sigma') =>
   interp_schedule_rr sh (S n) (ts @ i := K (Some b)) (Some i) m sigma').
Proof.
  assert (Hnode : (denote_flow (CCAS a expected desired) >>= K) ≅
    Vis (inr (inr (SCAS a expected desired))) (fun b => K (Some b))).
  {
    cbn [denote_flow]; unfold heap_event.
    rewrite bind_bind, bind_vis; step; constructor; intro b.
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K))
    (ts @ i := Vis (inr (inr (SCAS a expected desired))) (fun b => K (Some b)))
    (Some i) m sigma (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user by (rewrite Vector.nth_replace_eq; reflexivity).
  set (resume := fun result : (bool * SSig)%type =>
    let '(b,sigma') := result in
    interp_schedule_rr sh (S n) (ts @ i := K (Some b)) (Some i) m sigma').
  assert (Hrhs : (interp_state sh (scas a expected desired) sigma >>= resume) ≅
    ((runStateT (sh (SCAS a expected desired)) sigma >>= fun '(b,sigma') =>
      Guard (interp_state sh (Ret b) sigma')) >>= resume)).
  {
    apply equ_clo_bind with (S := eq).
    - unfold scas; apply interp_state_vis.
    - intros r r' <-; reflexivity.
  }
  rewrite Hrhs, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [b sigma']; rewrite bind_guard, sb_guard.
  assert (Hret : (interp_state sh (Ret b) sigma' >>= resume) ≅ resume (b,sigma')).
  {
    transitivity (Ret (b,sigma') >>= resume).
    - apply equ_clo_bind with (S := eq); [apply interp_state_ret|].
      intros r r' <-; reflexivity.
    - apply bind_ret_l.
  }
  rewrite Hret; unfold resume; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m σ ~
  (interp_state sh (swr a v) σ >>= fun '(_,σ') =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m σ').
Proof.
  assert (Hnode : (denote_flow (CWrite a v) >>= K) ≅
    Vis (inr (inr (SWr a v))) (fun _ => K (Some tt))).
  {
    cbn [denote_flow]; unfold heap_event.
    rewrite bind_bind, bind_vis; step; constructor; intros [].
    change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
      K (Some tt)).
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K))
    (ts @ i := Vis (inr (inr (SWr a v))) (fun _ => K (Some tt)))
    (Some i) m σ (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user by (rewrite Vector.nth_replace_eq; reflexivity).
  set (resume := fun result : (unit * SSig)%type =>
    let '(_,σ') := result in
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m σ').
  assert (Hrhs : (interp_state sh (swr a v) σ >>= resume) ≅
    ((runStateT (sh (SWr a v)) σ >>= fun '(_,σ') =>
      Guard (interp_state sh (Ret tt) σ')) >>= resume)).
  {
    apply equ_clo_bind with (S := eq).
    - unfold swr; apply interp_state_vis.
    - intros r r' <-; reflexivity.
  }
  rewrite Hrhs, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [[] σ']; rewrite bind_guard, sb_guard.
  assert (Hret : (interp_state sh (Ret tt) σ' >>= resume) ≅ resume (tt,σ')).
  {
    transitivity (Ret (tt,σ') >>= resume).
    - apply equ_clo_bind with (S := eq); [apply interp_state_ret|].
      intros r r' <-; reflexivity.
    - apply bind_ret_l.
  }
  rewrite Hret; unfold resume; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  q v (K : option unit -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow (CEmit q v) >>= K)) (Some i) m σ ~
  (interp_state sh (semit q v) σ >>= fun '(_,σ') =>
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m σ').
Proof.
  assert (Hnode : (denote_flow (CEmit q v) >>= K) ≅
    Vis (inr (inr (SEmit q v))) (fun _ => K (Some tt))).
  {
    cbn [denote_flow]; unfold heap_event.
    rewrite bind_bind, bind_vis; step; constructor; intros [].
    change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
      K (Some tt)).
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (denote_flow (CEmit q v) >>= K))
    (ts @ i := Vis (inr (inr (SEmit q v))) (fun _ => K (Some tt)))
    (Some i) m σ (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user by (rewrite Vector.nth_replace_eq; reflexivity).
  set (resume := fun result : (unit * SSig)%type =>
    let '(_,σ') := result in
    interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) (Some i) m σ').
  assert (Hrhs : (interp_state sh (semit q v) σ >>= resume) ≅
    ((runStateT (sh (SEmit q v)) σ >>= fun '(_,σ') =>
      Guard (interp_state sh (Ret tt) σ')) >>= resume)).
  {
    apply equ_clo_bind with (S := eq).
    - unfold semit; apply interp_state_vis.
    - intros r r' <-; reflexivity.
  }
  rewrite Hrhs, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [[] σ']; rewrite bind_guard, sb_guard.
  assert (Hret : (interp_state sh (Ret tt) σ' >>= resume) ≅ resume (tt,σ')).
  {
    transitivity (Ret (tt,σ') >>= resume).
    - apply equ_clo_bind with (S := eq); [apply interp_state_ret|].
      intros r r' <-; reflexivity.
    - apply bind_ret_l.
  }
  rewrite Hret; unfold resume; rewrite Vector.replace_replace_eq; reflexivity.
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
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intros [x|]; [reflexivity|apply bind_ret_l].
Qed.

Lemma interp_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE) m σ :
  interp_schedule_rr sh (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) m σ ~
  interp_schedule_rr sh (S n) (ts @ i := K (Some tt)) None m σ.
Proof.
  assert (Hnode : (denote_flow CYield >>= K) ≅
    Vis (inl Yield) (fun _ => K (Some tt))).
  {
    cbn [denote_flow]; unfold source_yield.
    rewrite bind_bind, bind_vis; step; constructor; intros [].
    change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
      K (Some tt)).
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (denote_flow CYield >>= K))
    (ts @ i := Vis (inl Yield) (fun _ => K (Some tt)))
    (Some i) m σ (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
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
  assert (Hnode : (denote_flow (CFork p) >>= K) ≅
    Vis (inr (inl Fork))
      (fun child : bool => if child
        then denote_flow p >>= fun _ => K None else K (Some tt))).
  {
    cbn [denote_flow]; unfold source_fork.
    rewrite bind_bind, bind_vis; step; constructor; intro child.
    rewrite bind_ret_l; destruct child; cbn.
    - rewrite bind_bind; apply equ_clo_bind_eq; intro flow.
      rewrite bind_ret_l; reflexivity.
    - apply bind_ret_l.
  }
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (denote_flow (CFork p) >>= K))
    (ts @ i := Vis (inr (inl Fork))
      (fun child : bool => if child
        then denote_flow p >>= fun _ => K None else K (Some tt)))
    (Some i) m σ (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
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
  set (loop_body := fun _ : unit =>
    flow <- denote_flow body;;
    match flow with
    | None => Ret (inr (None : option unit))
    | Some None => Ret (inr (Some tt))
    | Some (Some _) => Ret (inl tt)
    end).
  change ((ICtree.iter loop_body tt >>= K) ≅
    (denote_flow body >>= fun r =>
      match r with
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

Lemma interp_nd_source_ret {A} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) σ ≅
  interp_nd (S n) (ts @ i := K (Some x)) (Some i) σ.
Proof.
  apply interp_nd_equ, replace_pool_equ; [apply pool_equ_refl|].
  cbn [denote_flow]; apply bind_ret_l.
Qed.

Lemma interp_nd_source_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : option nat -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) σ ~
  (interp_state sh (srd a) σ >>= fun '(x,σ') =>
    interp_nd (S n) (ts @ i := K (Some x)) (Some i) σ').
Proof.
  assert (Hnode : (denote_flow (CRead a) >>= K) ≅
    Vis (inr (inr (SRd a))) (fun x => K (Some x))).
  {
    cbn [denote_flow]; unfold heap_event.
    rewrite bind_bind, bind_vis; step; constructor; intro x.
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_nd_equ (S n)
    (ts @ i := (denote_flow (CRead a) >>= K))
    (ts @ i := Vis (inr (inr (SRd a))) (fun x => K (Some x)))
    (Some i) σ (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_nd_user by (rewrite Vector.nth_replace_eq; reflexivity).
  set (resume := fun result : (nat * SSig)%type =>
    let '(x,σ') := result in
    interp_nd (S n) (ts @ i := K (Some x)) (Some i) σ').
  assert (Hrhs : (interp_state sh (srd a) σ >>= resume) ≅
    ((runStateT (sh (SRd a)) σ >>= fun '(x,σ') =>
      Guard (interp_state sh (Ret x) σ')) >>= resume)).
  {
    apply equ_clo_bind with (S := eq).
    - unfold srd; apply interp_state_vis.
    - intros r r' <-; reflexivity.
  }
  rewrite Hrhs, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [x σ']; rewrite bind_guard, sb_guard.
  assert (Hret : (interp_state sh (Ret x) σ' >>= resume) ≅ resume (x,σ')).
  {
    transitivity (Ret (x,σ') >>= resume).
    - apply equ_clo_bind with (S := eq); [apply interp_state_ret|].
      intros r r' <-; reflexivity.
    - apply bind_ret_l.
  }
  rewrite Hret; unfold resume; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) sigma :
  interp_nd (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) sigma ~
  (interp_state sh (salloc size) sigma >>= fun '(base,sigma') =>
    interp_nd (S n) (ts @ i := K (Some base)) (Some i) sigma').
Proof.
  assert (Hnode : (denote_flow (CAlloc size) >>= K) ≅
    Vis (inr (inr (SAlloc size))) (fun base => K (Some base))).
  {
    cbn [denote_flow]; unfold heap_event.
    rewrite bind_bind, bind_vis; step; constructor; intro base.
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_nd_equ (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K))
    (ts @ i := Vis (inr (inr (SAlloc size))) (fun base => K (Some base)))
    (Some i) sigma (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_nd_user by (rewrite Vector.nth_replace_eq; reflexivity).
  set (resume := fun result : (nat * SSig)%type =>
    let '(base,sigma') := result in
    interp_nd (S n) (ts @ i := K (Some base)) (Some i) sigma').
  assert (Hrhs : (interp_state sh (salloc size) sigma >>= resume) ≅
    ((runStateT (sh (SAlloc size)) sigma >>= fun '(base,sigma') =>
      Guard (interp_state sh (Ret base) sigma')) >>= resume)).
  {
    apply equ_clo_bind with (S := eq).
    - unfold salloc; apply interp_state_vis.
    - intros r r' <-; reflexivity.
  }
  rewrite Hrhs, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [base sigma']; rewrite bind_guard, sb_guard.
  assert (Hret : (interp_state sh (Ret base) sigma' >>= resume) ≅ resume (base,sigma')).
  {
    transitivity (Ret (base,sigma') >>= resume).
    - apply equ_clo_bind with (S := eq); [apply interp_state_ret|].
      intros r r' <-; reflexivity.
    - apply bind_ret_l.
  }
  rewrite Hret; unfold resume; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired (K : option bool -> thread sE) sigma :
  interp_nd (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K))
    (Some i) sigma ~
  (interp_state sh (scas a expected desired) sigma >>= fun '(b,sigma') =>
   interp_nd (S n) (ts @ i := K (Some b)) (Some i) sigma').
Proof.
  assert (Hnode : (denote_flow (CCAS a expected desired) >>= K) ≅
    Vis (inr (inr (SCAS a expected desired))) (fun b => K (Some b))).
  {
    cbn [denote_flow]; unfold heap_event.
    rewrite bind_bind, bind_vis; step; constructor; intro b.
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_nd_equ (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K))
    (ts @ i := Vis (inr (inr (SCAS a expected desired))) (fun b => K (Some b)))
    (Some i) sigma (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_nd_user by (rewrite Vector.nth_replace_eq; reflexivity).
  set (resume := fun result : (bool * SSig)%type =>
    let '(b,sigma') := result in
    interp_nd (S n) (ts @ i := K (Some b)) (Some i) sigma').
  assert (Hrhs : (interp_state sh (scas a expected desired) sigma >>= resume) ≅
    ((runStateT (sh (SCAS a expected desired)) sigma >>= fun '(b,sigma') =>
      Guard (interp_state sh (Ret b) sigma')) >>= resume)).
  {
    apply equ_clo_bind with (S := eq).
    - unfold scas; apply interp_state_vis.
    - intros r r' <-; reflexivity.
  }
  rewrite Hrhs, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [b sigma']; rewrite bind_guard, sb_guard.
  assert (Hret : (interp_state sh (Ret b) sigma' >>= resume) ≅ resume (b,sigma')).
  {
    transitivity (Ret (b,sigma') >>= resume).
    - apply equ_clo_bind with (S := eq); [apply interp_state_ret|].
      intros r r' <-; reflexivity.
    - apply bind_ret_l.
  }
  rewrite Hret; unfold resume; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) σ ~
  (interp_state sh (swr a v) σ >>= fun '(_,σ') =>
    interp_nd (S n) (ts @ i := K (Some tt)) (Some i) σ').
Proof.
  assert (Hnode : (denote_flow (CWrite a v) >>= K) ≅
    Vis (inr (inr (SWr a v))) (fun _ => K (Some tt))).
  {
    cbn [denote_flow]; unfold heap_event.
    rewrite bind_bind, bind_vis; step; constructor; intros [].
    change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
      K (Some tt)).
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_nd_equ (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K))
    (ts @ i := Vis (inr (inr (SWr a v))) (fun _ => K (Some tt)))
    (Some i) σ (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_nd_user by (rewrite Vector.nth_replace_eq; reflexivity).
  set (resume := fun result : (unit * SSig)%type =>
    let '(_,σ') := result in
    interp_nd (S n) (ts @ i := K (Some tt)) (Some i) σ').
  assert (Hrhs : (interp_state sh (swr a v) σ >>= resume) ≅
    ((runStateT (sh (SWr a v)) σ >>= fun '(_,σ') =>
      Guard (interp_state sh (Ret tt) σ')) >>= resume)).
  {
    apply equ_clo_bind with (S := eq).
    - unfold swr; apply interp_state_vis.
    - intros r r' <-; reflexivity.
  }
  rewrite Hrhs, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [[] σ']; rewrite bind_guard, sb_guard.
  assert (Hret : (interp_state sh (Ret tt) σ' >>= resume) ≅ resume (tt,σ')).
  {
    transitivity (Ret (tt,σ') >>= resume).
    - apply equ_clo_bind with (S := eq); [apply interp_state_ret|].
      intros r r' <-; reflexivity.
    - apply bind_ret_l.
  }
  rewrite Hret; unfold resume; rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_source_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  q v (K : option unit -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow (CEmit q v) >>= K)) (Some i) σ ~
  (interp_state sh (semit q v) σ >>= fun '(_,σ') =>
    interp_nd (S n) (ts @ i := K (Some tt)) (Some i) σ').
Proof.
  assert (Hnode : (denote_flow (CEmit q v) >>= K) ≅
    Vis (inr (inr (SEmit q v))) (fun _ => K (Some tt))).
  {
    cbn [denote_flow]; unfold heap_event.
    rewrite bind_bind, bind_vis; step; constructor; intros [].
    change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
      K (Some tt)).
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_nd_equ (S n)
    (ts @ i := (denote_flow (CEmit q v) >>= K))
    (ts @ i := Vis (inr (inr (SEmit q v))) (fun _ => K (Some tt)))
    (Some i) σ (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
  rewrite Hpool.
  erewrite interp_nd_user by (rewrite Vector.nth_replace_eq; reflexivity).
  set (resume := fun result : (unit * SSig)%type =>
    let '(_,σ') := result in
    interp_nd (S n) (ts @ i := K (Some tt)) (Some i) σ').
  assert (Hrhs : (interp_state sh (semit q v) σ >>= resume) ≅
    ((runStateT (sh (SEmit q v)) σ >>= fun '(_,σ') =>
      Guard (interp_state sh (Ret tt) σ')) >>= resume)).
  {
    apply equ_clo_bind with (S := eq).
    - unfold semit; apply interp_state_vis.
    - intros r r' <-; reflexivity.
  }
  rewrite Hrhs, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity|].
  intros [[] σ']; rewrite bind_guard, sb_guard.
  assert (Hret : (interp_state sh (Ret tt) σ' >>= resume) ≅ resume (tt,σ')).
  {
    transitivity (Ret (tt,σ') >>= resume).
    - apply equ_clo_bind with (S := eq); [apply interp_state_ret|].
      intros r r' <-; reflexivity.
    - apply bind_ret_l.
  }
  rewrite Hret; unfold resume; rewrite Vector.replace_replace_eq; reflexivity.
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
  cbn [denote_flow]; rewrite bind_bind.
  apply equ_clo_bind_eq; intros [x|]; [reflexivity|apply bind_ret_l].
Qed.

Lemma interp_nd_source_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
  (K : option unit -> thread sE) σ :
  interp_nd (S n) (ts @ i := (denote_flow CYield >>= K)) (Some i) σ ~
  interp_nd (S n) (ts @ i := K (Some tt)) None σ.
Proof.
  assert (Hnode : (denote_flow CYield >>= K) ≅
    Vis (inl Yield) (fun _ => K (Some tt))).
  {
    cbn [denote_flow]; unfold source_yield.
    rewrite bind_bind, bind_vis; step; constructor; intros [].
    change (((Ret tt : thread sE) >>= fun _ : unit => Ret (Some tt) >>= K) ≅
      K (Some tt)).
    rewrite !bind_ret_l; reflexivity.
  }
  pose proof (interp_nd_equ (S n)
    (ts @ i := (denote_flow CYield >>= K))
    (ts @ i := Vis (inl Yield) (fun _ => K (Some tt)))
    (Some i) σ (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
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
  assert (Hnode : (denote_flow (CFork p) >>= K) ≅
    Vis (inr (inl Fork))
      (fun child : bool => if child
        then denote_flow p >>= fun _ => K None else K (Some tt))).
  {
    cbn [denote_flow]; unfold source_fork.
    rewrite bind_bind, bind_vis; step; constructor; intro child.
    rewrite bind_ret_l; destruct child; cbn.
    - rewrite bind_bind; apply equ_clo_bind_eq; intro flow.
      rewrite bind_ret_l; reflexivity.
    - apply bind_ret_l.
  }
  pose proof (interp_nd_equ (S n)
    (ts @ i := (denote_flow (CFork p) >>= K))
    (ts @ i := Vis (inr (inl Fork))
      (fun child : bool => if child
        then denote_flow p >>= fun _ => K None else K (Some tt)))
    (Some i) σ (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)) as Hpool.
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
  set (loop_body := fun _ : unit =>
    flow <- denote_flow body;;
    match flow with
    | None => Ret (inr (None : option unit))
    | Some None => Ret (inr (Some tt))
    | Some (Some _) => Ret (inl tt)
    end).
  change ((ICtree.iter loop_body tt >>= K) ≅
    (denote_flow body >>= fun r =>
      match r with
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
