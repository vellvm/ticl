(** * Scheduler-generic fairness for yielding pools.

    [interp_schedule_rr] and [interp_schedule_nd] erase every scheduling
    decision.  Here a [Scheduler] policy record drives the same [schedule]
    pool semantics through [run_sched], which logs a [Scheduled i] event at
    every pick while yields and spawns are erased as before.  Fairness is a
    property of the policy's own pick stream ([FairScheduler]); the pool rules
    at the end conclude [AG (AF _)] on the instrumented runner for any fair
    policy from an invariant, a well-founded rank and a helpful slot. *)

From Stdlib Require Import List Arith.PeanoNat Lia Fin Vector Morphisms
  Program.Equality Wellfounded.Inverse_Image.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Events.Writer
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.Segments
  CTree.Interp.Yield.Sequential
  CTree.Interp.Yield.Execution
  CTree.Interp.State.Mod
  CTree.Trace
  CTree.Logic.Trans
  CTree.Logic.AG
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.Bind
  CTree.Logic.Trace
  CTree.Logic.CanStep
  CTree.Logic.State
  Logic.Core
  Utils.Vectors.

Import CTreeNotations TiclNotations CoindNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

Generalizable All Variables.

(** * Scheduling policies *)

(** The slot index [proj1_sig (Fin.to_nat j)] picked at a scheduling point. *)
Variant schedE : Type -> Type :=
| Scheduled : nat -> schedE unit.

(** A policy carries its own state; at a scheduling point of a pool of size
    [S n] it offers [S (sched_arity n st)] alternatives, each resolving to a
    slot and a successor state.  Plain record: the policy is always passed
    explicitly, nothing drives inference. *)
Record Scheduler : Type := {
  sched_state : Type;
  sched_arity : nat -> sched_state -> nat;
  sched_pick  : forall n (st : sched_state),
                Fin.t (S (sched_arity n st)) -> Fin.t (S n) * sched_state;
}.

Definition rr_scheduler : Scheduler :=
  {| sched_state := nat; sched_arity := fun _ _ => 0;
     sched_pick := fun n m _ => (rr_pick n m, S m) |}.

(** Not fair: a branch may avoid any slot forever; no [FairScheduler]. *)
Definition nd_scheduler : Scheduler :=
  {| sched_state := unit; sched_arity := fun n _ => n;
     sched_pick := fun n _ c => (c, tt) |}.

Definition widen {E} : (yieldE +' (spawnE +' E)) ~> (yieldE +' (spawnE +' (schedE +' E))) :=
  fun _ e => match e with
             | inl1 y => inl1 y
             | inr1 (inl1 s) => inr1 (inl1 s)
             | inr1 (inr1 e) => inr1 (inr1 (inr1 e))
             end.

Definition sched_event {E} (k : nat) : (yieldE +' (spawnE +' (schedE +' E))) unit :=
  inr1 (inr1 (inl1 (Scheduled k))).

Definition slot_index {n} (j : Fin.t n) : nat := proj1_sig (Fin.to_nat j).

(** Resolve every [Bn] branch of a scheduled pool through the policy and log
    the pick.  The pick is a delayed [Br] followed by the [Scheduled] event, so
    one pick is one visible [ktrans] step.  Like [refine_rr], this also
    resolves thread-internal [Bn] branches; CSL threads are branch-free. *)
CoFixpoint run_sched {E : Type -> Type} (sch : Scheduler)
  (t : completed E Bn) (st : sched_state sch) : completed (schedE +' E) Bn :=
  match observe t with
  | RetF x => Ret x
  | StuckF => Stuck
  | StepF t' => Step (run_sched sch t' st)
  | GuardF t' => Guard (run_sched sch t' st)
  | VisF e k => Vis (widen _ e) (fun x => run_sched sch (k x) st)
  | BrF c k =>
      match c in Bn Y return (Y -> completed E Bn) -> completed (schedE +' E) Bn with
      | branchn 0 => fun _ => Stuck
      | branchn (S m) => fun k =>
          Br (branchn (S (sched_arity sch m st))) (fun a =>
            Vis (sched_event (slot_index (fst (sched_pick sch m st a))))
              (fun _ => run_sched sch (k (fst (sched_pick sch m st a))) (snd (sched_pick sch m st a))))
      end k
  end.

Lemma unfold_run_sched {E : Type -> Type} (sch : Scheduler)
  (t : completed E Bn) (st : sched_state sch) :
  run_sched sch t st ≅
  match observe t with
  | RetF x => Ret x
  | StuckF => Stuck
  | StepF t' => Step (run_sched sch t' st)
  | GuardF t' => Guard (run_sched sch t' st)
  | VisF e k => Vis (widen _ e) (fun x => run_sched sch (k x) st)
  | BrF c k =>
      match c in Bn Y return (Y -> completed E Bn) -> completed (schedE +' E) Bn with
      | branchn 0 => fun _ => Stuck
      | branchn (S m) => fun k =>
          Br (branchn (S (sched_arity sch m st))) (fun a =>
            Vis (sched_event (slot_index (fst (sched_pick sch m st a))))
              (fun _ => run_sched sch (k (fst (sched_pick sch m st a))) (snd (sched_pick sch m st a))))
      end k
  end.
Proof. step; now cbn. Qed.

#[global] Instance run_sched_equ {E : Type -> Type} (sch : Scheduler) :
  Proper (equ eq ==> eq ==> equ eq) (@run_sched E sch).
Proof.
  unfold Proper, respectful.
  __coinduction_equ R IH; intros t u Htu st st' <-.
  rewrite !unfold_run_sched.
  step in Htu.
  destruct Htu as [x y Hxy| |t1 t2 Ht|t1 t2 Ht|Y e k1 k2 Hk|Y c k1 k2 Hk]; cbn.
  - subst; reflexivity.
  - constructor.
  - constructor; apply IH; [exact Ht|reflexivity].
  - constructor; apply IH; [exact Ht|reflexivity].
  - constructor; intro x; apply IH; [exact (Hk x)|reflexivity].
  - destruct c as [[|m]]; constructor; intro a.
    step; constructor; intros _; apply IH; [exact (Hk _)|reflexivity].
Qed.

(** * Handlers and the instrumented runner *)

Definition relabel_log {W} : writerE W ~> writerE (W + nat) :=
  fun _ e => match e in writerE _ X return writerE (W + nat) X with
             | Log w => Log (inl w) end.

Definition sched_handler {W Σ} : schedE ~> stateT Σ (ctreeW (W + nat) Bn) :=
  fun _ e σ => match e in schedE X return ctreeW (W + nat) Bn (Σ * X) with
               | Scheduled i => Vis (Log (inr i)) (fun _ => Ret (σ, tt)) end.

Definition interp_schedule_fair {E W Σ} (sch : Scheduler) (h : E ~> stateT Σ (ctreeW W Bn))
    (n : nat) (ts : pool E Bn n) (focus : option (Fin.t n)) (st : sched_state sch) (σ : Σ)
    : ctreeW (W + nat) Bn (Σ * unit) :=
  interp_state (h_sum sched_handler (fun _ e σ => translate relabel_log (h _ e σ)))
    (interp_yield (interp_spawn (run_sched sch (schedule n ts focus) st))) σ.

(** Program observations only: scheduling logs never satisfy [fair_obs P]. *)
Definition fair_obs {W} (P : W -> Prop) (o : W + nat) : Prop :=
  match o with inl w => P w | inr _ => False end.

(** * Relabelling helpers *)

Lemma translate_emit_list {W : Type} {X : Type} (os : list W) (t : ctreeW W Bn X) :
  translate relabel_log (emit_list os t) ≅ emit_list (List.map inl os) (translate relabel_log t).
Proof.
  induction os as [|o os IH]; [reflexivity|].
  cbn [List.map]; rewrite !emit_list_cons, translate_vis; cbn [relabel_log].
  apply vis_equ_node; intros _; exact IH.
Qed.

Lemma translate_guards {E F B : Type -> Type} {X : Type} (f : E ~> F) k (t : ctree E B X) :
  translate f (guards k t) ≅ guards k (translate f t).
Proof.
  induction k as [|k IH]; cbn [guards]; [reflexivity|].
  rewrite translate_guard; apply guard_equ_node; exact IH.
Qed.

(** * Guard alignment through [run_sched] *)
Section RunSchedAlign.
  Context {E : Type -> Type} (sch : Scheduler).
  Local Typeclasses Transparent equ.

  Lemma run_sched_guards n (t : completed E Bn) st :
    run_sched sch (guards n t) st ≅ guards n (run_sched sch t st).
  Proof.
    induction n; cbn [guards]; [reflexivity|].
    rewrite unfold_run_sched; cbn [observe _observe].
    apply guard_equ_node; exact IHn.
  Qed.

  Inductive sched_rel : completed (schedE +' E) Bn -> completed (schedE +' E) Bn -> Prop :=
  | sched_rel_at n m (t u : completed E Bn) st T U :
      galigned t u -> T ≅ guards n (run_sched sch t st) ->
      U ≅ guards m (run_sched sch u st) -> sched_rel T U
  | sched_rel_pick (t u : completed E Bn) st k T U :
      galigned t u ->
      T ≅ Vis (sched_event k) (fun _ => run_sched sch t st) ->
      U ≅ Vis (sched_event k) (fun _ => run_sched sch u st) -> sched_rel T U.

  Lemma sched_rel_step T U : sched_rel T U -> galignF sched_rel T U.
  Proof.
    intros [n m t u st T' U' A HT HU|t u st k T' U' A HT HU].
    2: { apply (galignF_vis _ T' U' 0 0 (sched_event k)
           (fun _ => run_sched sch t st) (fun _ => run_sched sch u st)); [exact HT|exact HU|].
         intros _; apply (sched_rel_at 0 0 t u st); [exact A|reflexivity|reflexivity]. }
    destruct A as [t u a b t' u' Et Eu A|t u a b r Et Eu|t u a b Y d kk kk' Et Eu Hk
      |t u a b Y e kk kk' Et Eu Hk|t u a b Et Eu|t u a b t' u' Et Eu A].
    - apply (galignF_guard _ T' U' (n + a) (m + b)
        (run_sched sch t' st) (run_sched sch u' st)).
      + rewrite HT, Et, run_sched_guards, guards_shift; reflexivity.
      + rewrite HU, Eu, run_sched_guards, guards_shift; reflexivity.
      + apply (sched_rel_at 0 0 t' u' st); [exact A|reflexivity|reflexivity].
    - apply (galignF_ret _ T' U' (n + a) (m + b) r).
      + rewrite HT, Et, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
      + rewrite HU, Eu, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
    - destruct d as [[|p]].
      + apply (galignF_stuck _ T' U' (n + a) (m + b)).
        * rewrite HT, Et, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
        * rewrite HU, Eu, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
      + apply (galignF_br _ T' U' (n + a) (m + b) (branchn (S (sched_arity sch p st)))
          (fun c => Vis (sched_event (slot_index (fst (sched_pick sch p st c))))
             (fun _ => run_sched sch (kk (fst (sched_pick sch p st c))) (snd (sched_pick sch p st c))))
          (fun c => Vis (sched_event (slot_index (fst (sched_pick sch p st c))))
             (fun _ => run_sched sch (kk' (fst (sched_pick sch p st c))) (snd (sched_pick sch p st c))))).
        * rewrite HT, Et, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
        * rewrite HU, Eu, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
        * intro c; apply (sched_rel_pick (kk (fst (sched_pick sch p st c))) (kk' (fst (sched_pick sch p st c)))
            (snd (sched_pick sch p st c)) (slot_index (fst (sched_pick sch p st c))));
            [apply Hk|reflexivity|reflexivity].
    - apply (galignF_vis _ T' U' (n + a) (m + b) (widen _ e)
        (fun x => run_sched sch (kk x) st) (fun x => run_sched sch (kk' x) st)).
      + rewrite HT, Et, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
      + rewrite HU, Eu, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
      + intro x; apply (sched_rel_at 0 0 (kk x) (kk' x) st); [apply Hk|reflexivity|reflexivity].
    - apply (galignF_stuck _ T' U' (n + a) (m + b)).
      + rewrite HT, Et, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
      + rewrite HU, Eu, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
    - apply (galignF_step _ T' U' (n + a) (m + b) (run_sched sch t' st) (run_sched sch u' st)).
      + rewrite HT, Et, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
      + rewrite HU, Eu, run_sched_guards, <- guards_add, unfold_run_sched; reflexivity.
      + apply (sched_rel_at 0 0 t' u' st); [exact A|reflexivity|reflexivity].
  Qed.

  Lemma run_sched_galigned (t u : completed E Bn) st :
    galigned t u -> galigned (run_sched sch t st) (run_sched sch u st).
  Proof.
    intro H; apply (galigned_coind sched_rel sched_rel_step).
    apply (sched_rel_at 0 0 t u st); [exact H|reflexivity|reflexivity].
  Qed.
End RunSchedAlign.

(** * Node equations of [run_sched] *)
Section RunSchedNodes.
  Context {E : Type -> Type} (sch : Scheduler).

  Lemma run_sched_ret (x : unit) st :
    run_sched sch (Ret x : completed E Bn) st ≅ Ret x.
  Proof. rewrite unfold_run_sched; reflexivity. Qed.

  Lemma run_sched_stuck st :
    run_sched sch (Stuck : completed E Bn) st ≅ Stuck.
  Proof. rewrite unfold_run_sched; reflexivity. Qed.

  Lemma run_sched_guard (t : completed E Bn) st :
    run_sched sch (Guard t) st ≅ Guard (run_sched sch t st).
  Proof. rewrite unfold_run_sched; reflexivity. Qed.

  Lemma run_sched_step (t : completed E Bn) st :
    run_sched sch (Step t) st ≅ Step (run_sched sch t st).
  Proof. rewrite unfold_run_sched; reflexivity. Qed.

  Lemma run_sched_vis {Y} (e : (yieldE +' (spawnE +' E)) Y) (k : Y -> completed E Bn) st :
    run_sched sch (Vis e k) st ≅ Vis (widen _ e) (fun x => run_sched sch (k x) st).
  Proof. rewrite unfold_run_sched; reflexivity. Qed.

  (** One scheduling point: a delayed pick, its log, then [schedule]'s own
      visible step. *)
  Lemma run_sched_brS m (k : Fin.t (S m) -> completed E Bn) st :
    run_sched sch (brS (branchn (S m)) k) st ≅
    Br (branchn (S (sched_arity sch m st))) (fun a =>
      Vis (sched_event (slot_index (fst (sched_pick sch m st a))))
        (fun _ => Step (run_sched sch (k (fst (sched_pick sch m st a)))
                                      (snd (sched_pick sch m st a))))).
  Proof.
    rewrite unfold_run_sched; cbn.
    step; constructor; intro a.
    apply vis_equ_node; intros _; apply run_sched_step.
  Qed.
End RunSchedNodes.

(** * Structural equations of the instrumented runner *)
Section FairInterpretation.
  Context {E : Type -> Type} {W Σ : Type} (sch : Scheduler)
    (h : E ~> stateT Σ (ctreeW W Bn)).

  Lemma interp_schedule_fair_equ n (ts ts' : pool E Bn n) focus st σ :
    pool_equ ts ts' ->
    interp_schedule_fair sch h n ts focus st σ ≅
    interp_schedule_fair sch h n ts' focus st σ.
  Proof.
    intro Hts; unfold interp_schedule_fair.
    now rewrite (schedule_pool_proper n ts ts' focus Hts).
  Qed.

  Lemma interp_schedule_fair_empty (ts : pool E Bn 0) st σ :
    interp_schedule_fair sch h 0 ts None st σ ~ (Ret (σ,tt) : ctreeW (W + nat) Bn (Σ * unit)).
  Proof.
    unfold interp_schedule_fair.
    assert (Hempty : schedule 0 ts None ≅ Ret tt).
    { rewrite (ctree_eta (schedule 0 ts None)), schedule_empty_none; reflexivity. }
    rewrite Hempty, run_sched_ret, interp_erase_ret, interp_state_ret; reflexivity.
  Qed.

  Lemma interp_schedule_fair_ret n (ts : pool E Bn (S n)) (i : Fin.t (S n)) st σ :
    observe (ts $ i) = RetF tt ->
    interp_schedule_fair sch h (S n) ts (Some i) st σ ~
    interp_schedule_fair sch h n (ts -- i) None st σ.
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅ Guard (schedule n (ts -- i) None)).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_ret n ts i Hobs); reflexivity. }
    rewrite Hnode, run_sched_guard, interp_erase_guard, interp_state_guard, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_fair_guard n (ts : pool E Bn (S n)) (i : Fin.t (S n)) t st σ :
    observe (ts $ i) = GuardF t ->
    interp_schedule_fair sch h (S n) ts (Some i) st σ ~
    interp_schedule_fair sch h (S n) (ts @ i := t) (Some i) st σ.
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Guard (schedule (S n) (ts @ i := t) (Some i))).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_guard n ts i t Hobs); reflexivity. }
    rewrite Hnode, run_sched_guard, interp_erase_guard, interp_state_guard, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_fair_step n (ts : pool E Bn (S n)) (i : Fin.t (S n)) t st σ :
    observe (ts $ i) = StepF t ->
    interp_schedule_fair sch h (S n) ts (Some i) st σ ~
    Step (interp_schedule_fair sch h (S n) (ts @ i := t) (Some i) st σ).
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Step (schedule (S n) (ts @ i := t) (Some i))).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_step n ts i t Hobs); reflexivity. }
    rewrite Hnode, run_sched_step, interp_erase_step, interp_state_step.
    apply sb_step.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.

  Lemma interp_schedule_fair_yield n (ts : pool E Bn (S n)) (i : Fin.t (S n)) k st σ :
    observe (ts $ i) = VisF (inl1 Yield) k ->
    interp_schedule_fair sch h (S n) ts (Some i) st σ ~
    interp_schedule_fair sch h (S n) (ts @ i := k tt) None st σ.
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Guard (schedule (S n) (ts @ i := k tt) None)).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_yield n ts i k Hobs); reflexivity. }
    rewrite Hnode, run_sched_guard, interp_erase_guard, interp_state_guard, sb_guard; reflexivity.
  Qed.

  (** The scheduling point: the policy's alternatives, the logged slot, then
      [schedule]'s visible step into the focused pool. *)
  Lemma interp_schedule_fair_select n (ts : pool E Bn (S n)) st σ :
    interp_schedule_fair sch h (S n) ts None st σ ~
    Br (branchn (S (sched_arity sch n st))) (fun a =>
      Vis (Log (inr (slot_index (fst (sched_pick sch n st a)))))
        (fun _ => Step (interp_schedule_fair sch h (S n) ts
                         (Some (fst (sched_pick sch n st a))) (snd (sched_pick sch n st a)) σ))).
  Proof.
    unfold interp_schedule_fair at 1.
    assert (Hnode : run_sched sch (schedule (S n) ts None) st ≅
      Vis (inl1 Yield) (fun _ =>
        Br (branchn (S (sched_arity sch n st))) (fun a =>
          Vis (sched_event (slot_index (fst (sched_pick sch n st a))))
            (fun _ => Step (run_sched sch (schedule (S n) ts (Some (fst (sched_pick sch n st a))))
                                          (snd (sched_pick sch n st a))))))).
    { rewrite (ctree_eta (schedule (S n) ts None)), schedule_no_focus_nonempty, run_sched_vis.
      cbn [widen]; apply vis_equ_node; intros _; apply run_sched_brS. }
    rewrite Hnode, interp_erase_yield, interp_state_guard, sb_guard,
      interp_state_guard, sb_guard.
    rewrite interp_erase_br, interp_state_br.
    change (Monad.bind (mbr ?c) ?f)
      with (CTree.bind (branch c : ctree (writerE (W + nat)) Bn _) f).
    rewrite bind_branch.
    apply sb_br_id; intro a.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    unfold sched_event; rewrite interp_erase_user, interp_state_vis; cbn [h_sum sched_handler].
    change (Monad.bind ?a ?b) with (CTree.bind a b); rewrite bind_vis.
    apply sb_vis; intros _.
    rewrite bind_ret_l; cbn [fst snd].
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    rewrite interp_erase_step, interp_state_step.
    apply sb_step.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.

  Lemma interp_schedule_fair_fork n (ts : pool E Bn (S n)) (i : Fin.t (S n)) k st σ :
    observe (ts $ i) = VisF (inr1 (inl1 Fork)) k ->
    interp_schedule_fair sch h (S n) ts (Some i) st σ ~
    interp_schedule_fair sch h (S (S n)) (k true :: (ts @ i := k false)) (Some (Fin.FS i)) st σ.
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Vis (inr1 (inl1 Spawn)) (fun _ =>
        schedule (S (S n)) (k true :: (ts @ i := k false)) (Some (Fin.FS i)))).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_fork n ts i k Hobs); reflexivity. }
    rewrite Hnode, run_sched_vis; cbn [widen].
    rewrite interp_erase_spawn, interp_state_guard, sb_guard; reflexivity.
  Qed.

  Lemma interp_schedule_fair_user n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    {Y} (e : E Y) k st σ :
    observe (ts $ i) = VisF (inr1 (inr1 e)) k ->
    interp_schedule_fair sch h (S n) ts (Some i) st σ ~
    (translate relabel_log (h _ e σ) >>= fun '(σ',x) =>
       interp_schedule_fair sch h (S n) (ts @ i := k x) (Some i) st σ').
  Proof.
    intro Hobs; unfold interp_schedule_fair at 1.
    assert (Hnode : schedule (S n) ts (Some i) ≅
      Vis (inr1 (inr1 e) : (yieldE +' (spawnE +' E)) Y)
        (fun x => schedule (S n) (ts @ i := k x) (Some i))).
    { rewrite (ctree_eta (schedule (S n) ts (Some i))),
        (schedule_focused_user_event n ts i e k Hobs); reflexivity. }
    rewrite Hnode, run_sched_vis; cbn [widen].
    rewrite interp_erase_user, interp_state_vis; cbn [h_sum].
    __upto_bind_sbisim_eq; intros [σ' x]; cbn.
    rewrite sb_guard, interp_state_guard, sb_guard, interp_state_guard, sb_guard.
    reflexivity.
  Qed.

  Lemma interp_schedule_fair_stuck n (ts : pool E Bn (S n)) (i : Fin.t (S n)) st σ :
    (ts $ i) ≅ Stuck ->
    interp_schedule_fair sch h (S n) ts (Some i) st σ ≅ Stuck.
  Proof.
    intro Hstuck.
    rewrite (interp_schedule_fair_equ (S n) ts (ts @ i := Stuck) (Some i) st σ)
      by (intro j; destruct (Fin.eq_dec j i) as [->|Hne];
          [rewrite Vector.nth_replace_eq; exact Hstuck
          |rewrite Vector.nth_replace_neq by congruence; reflexivity]).
    unfold interp_schedule_fair.
    assert (Hnode : schedule (S n) (ts @ i := Stuck) (Some i) ≅ Stuck).
    { rewrite (ctree_eta (schedule (S n) (ts @ i := Stuck) (Some i))),
        (schedule_focused_stuck n (ts @ i := Stuck) i)
        by (rewrite Vector.nth_replace_eq; reflexivity); reflexivity. }
    rewrite Hnode, run_sched_stuck, interp_erase_stuck, interp_state_stuck; reflexivity.
  Qed.

  (** Keep one scheduler continuation fixed while interpreting a raw user
      event; stated on the handler itself so client handler equations
      ([≅]) apply under [translate] directly. *)
  Lemma interp_schedule_fair_user_bind n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    (t : thread E Bn) {Y} (e : E Y) (k : Y -> thread E Bn) st σ :
    t ≅ Vis (inr1 (inr1 e)) k ->
    interp_schedule_fair sch h (S n) (ts @ i := t) (Some i) st σ ~
    (translate relabel_log (h _ e σ) >>=
      fun '(σ',x) => interp_schedule_fair sch h (S n) (ts @ i := k x) (Some i) st σ').
  Proof.
    intro Hnode.
    rewrite (interp_schedule_fair_equ (S n)
      (ts @ i := t) (ts @ i := Vis (inr1 (inr1 e)) k) (Some i) st σ
      (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) Hnode)).
    erewrite interp_schedule_fair_user with (e:=e) (k:=k)
      by (rewrite Vector.nth_replace_eq; reflexivity).
    __upto_bind_sbisim_eq; intros [σ' x].
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  Lemma interp_schedule_fair_guard_equ n (ts us : pool E Bn n) focus st σ :
    pool_guard_equ ts us ->
    interp_schedule_fair sch h n ts focus st σ ~
    interp_schedule_fair sch h n us focus st σ.
  Proof.
    intro H'; unfold interp_schedule_fair, interp_yield, interp_spawn.
    apply galigned_sbisim, interp_state_galigned, interp_galigned, interp_galigned,
      run_sched_galigned, schedule_galigned, H'.
  Qed.

  (** ** Focused-slot congruence *)

  Lemma segment_fair_replace_equ n (ts : pool E Bn (S n)) (i : Fin.t (S n))
    t u focus st σ :
    t ≅ u ->
    interp_schedule_fair sch h (S n) (ts @ i := t) focus st σ ~
    interp_schedule_fair sch h (S n) (ts @ i := u) focus st σ.
  Proof.
    intro Eq.
    rewrite (interp_schedule_fair_equ (S n) (ts @ i := t) (ts @ i := u)
      focus st σ (replace_pool_equ ts ts i t u (pool_equ_refl ts) Eq)); reflexivity.
  Qed.

  Lemma segment_fair_focused_guard n (ts : pool E Bn (S n)) (i : Fin.t (S n)) t st σ :
    interp_schedule_fair sch h (S n) (ts @ i := Guard t) (Some i) st σ ~
    interp_schedule_fair sch h (S n) (ts @ i := t) (Some i) st σ.
  Proof.
    erewrite interp_schedule_fair_guard by (rewrite Vector.nth_replace_eq; reflexivity).
    rewrite Vector.replace_replace_eq; reflexivity.
  Qed.

  (** ** Segment-driven scheduling.

      The response relation must be bisimulation evidence after relabelling;
      every client uses raw [≅] ([relabel_equ_sb]), so no [translate]/[~]
      congruence is needed. *)
  Lemma relabel_equ_sb {X} (t u : ctreeW W Bn X) :
    t ≅ u -> translate relabel_log t ~ translate relabel_log u.
  Proof. intro Eq; rewrite Eq; reflexivity. Qed.

  Section SegmentInterpretationFair.
    Context (R : forall X : Type, ctreeW W Bn X -> ctreeW W Bn X -> Prop)
      (HR : forall X (t u : ctreeW W Bn X), R X t u ->
        translate relabel_log t ~ translate relabel_log u).

    Lemma segment_interp_fair n (ts : pool E Bn (S n)) (i : Fin.t (S n))
      st σ xs residual σ' :
      ThreadSegment h R (ts $ i) σ xs residual σ' ->
      interp_schedule_fair sch h (S n) ts (Some i) st σ ~
      emit_list (List.map inl xs)
        (interp_schedule_fair sch h (S n) (ts @ i := residual) None st σ').
    Proof.
      intro Hseg.
      assert (Hgen : forall t s0 ys r0 s1,
        ThreadSegment h R t s0 ys r0 s1 ->
        forall p (us : pool E Bn (S p)) (j : Fin.t (S p)),
          interp_schedule_fair sch h (S p) (us @ j := t) (Some j) st s0 ~
          emit_list (List.map inl ys)
            (interp_schedule_fair sch h (S p) (us @ j := r0) None st s1)).
      {
        intros t s0 ys r0 s1 H'; induction H' as
          [k σ0
          |t0 σ0 xs0 residual0 σ0' H' IH
          |Y e k σ0 result σ1 before after residual0 σ0' Eh H' IH
          |t0 u σ0 xs0 u' residual0 σ0' Etu H' IH Eout]; intros p us j.
        - cbn [List.map emit_list List.fold_right].
          erewrite interp_schedule_fair_yield
            by (rewrite Vector.nth_replace_eq; reflexivity).
          rewrite Vector.replace_replace_eq; reflexivity.
        - etransitivity; [apply segment_fair_focused_guard|apply IH].
        - etransitivity; [apply interp_schedule_fair_user_bind; reflexivity|].
          transitivity (emit_list (List.map inl before) (Ret (σ1,result)) >>=
            fun '(σ2,x) =>
              interp_schedule_fair sch h (S p) (us @ j := k x) (Some j) st σ2).
          + apply HR in Eh; rewrite Eh, translate_emit_list,
              (emit_list_equ _ _ _ (translate_ret (σ1,result) relabel_log)); reflexivity.
          + rewrite emit_list_ret_bind, List.map_app, emit_list_app.
            apply emit_list_sbisim; apply IH.
        - etransitivity; [apply segment_fair_replace_equ; exact Etu|].
          etransitivity; [apply IH|].
          apply emit_list_sbisim, segment_fair_replace_equ; exact Eout.
      }
      transitivity
        (interp_schedule_fair sch h (S n) (ts @ i := (ts $ i)) (Some i) st σ).
      - symmetry; apply equ_sbisim;
          exact (interp_schedule_fair_equ (S n) (ts @ i := (ts $ i)) ts
            (Some i) st σ (pool_replace_current ts i)).
      - apply Hgen; exact Hseg.
    Qed.
  End SegmentInterpretationFair.
End FairInterpretation.

(** * Policy traces and fairness *)

(** The policy's own pick stream for a live pool of size [S n]. *)
CoFixpoint sched_trace (sch : Scheduler) (n : nat) (st : sched_state sch) : ctreeW nat Bn unit :=
  Br (branchn (S (sched_arity sch n st))) (fun a =>
    Vis (Log (slot_index (fst (sched_pick sch n st a))))
      (fun _ => sched_trace sch n (snd (sched_pick sch n st a)))).

Lemma unfold_sched_trace sch n st :
  sched_trace sch n st ≅
  Br (branchn (S (sched_arity sch n st))) (fun a =>
    Vis (Log (slot_index (fst (sched_pick sch n st a))))
      (fun _ => sched_trace sch n (snd (sched_pick sch n st a)))).
Proof. step; now cbn. Qed.

(** Fairness: from every policy state, every slot of a fixed-size pool is
    picked again and again. *)
Class FairScheduler (sch : Scheduler) : Prop :=
  fair_scheduled : forall n (i : Fin.t (S n)) (st : sched_state sch) (w : World (writerE nat)),
    not_done w ->
    <( {sched_trace sch n st}, w |= AG (AF visW {eq (slot_index i)}) )>.

(** Induction-friendly witness: along every alternative that avoids slot
    [i], slot [i] is still picked after finitely many scheduling points. *)
Inductive EventuallyPicks (sch : Scheduler) (n : nat) (i : Fin.t (S n)) : sched_state sch -> Prop :=
| ep_intro st :
    (forall a, fst (sched_pick sch n st a) <> i ->
               EventuallyPicks sch n i (snd (sched_pick sch n st a))) ->
    EventuallyPicks sch n i st.

Section FairBridge.
  Context (sch : Scheduler) (n : nat) (i : Fin.t (S n)).

  Lemma eventually_picks_af st w :
    EventuallyPicks sch n i st -> not_done w ->
    <( {sched_trace sch n st}, w |= AF visW {eq (slot_index i)} )>.
  Proof.
    intro Hep; revert w; induction Hep as [st Hst IH]; intros w Hw.
    rewrite unfold_sched_trace.
    apply aul_br; [apply ticll_top; exact Hw|exists Fin.F1; apply can_step_vis; [exact tt|exact Hw]|].
    intros a t' w' TR.
    apply ktrans_vis in TR as ([] & -> & Heq & _); rewrite <- Heq.
    destruct (Fin.eq_dec (fst (sched_pick sch n st a)) i) as [Hpick|Hne].
    - cleft; apply ticll_vis; constructor; rewrite Hpick; reflexivity.
    - apply IH; [exact Hne|constructor].
  Qed.

  Lemma af_trace_eventually_picks :
    forall (t : ctreeW nat Bn unit) w,
      <( t, w |= AF visW {eq (slot_index i)} )> ->
      forall st, t ≅ sched_trace sch n st ->
      w <> Obs (Log (slot_index i)) tt ->
      EventuallyPicks sch n i st.
  Proof.
    intros t w H.
    cinduction H; intros st Et Hw.
    - exfalso; apply Hw.
      apply ticll_vis in Hp; inversion Hp as [Y e v Hv Ew]; clear Hp.
      destruct e as [k]; destruct v; cbn in Hv; subst; reflexivity.
    - constructor; intros a Hne.
      apply ticll_not_done in Hp.
      apply (HInd (sched_trace sch n (snd (sched_pick sch n st a)))
        (Obs (Log (slot_index (fst (sched_pick sch n st a)))) tt)).
      + rewrite Et, unfold_sched_trace; apply ktrans_br; exists a.
        apply ktrans_vis; exists tt; split; [reflexivity|split; [reflexivity|exact Hp]].
      + reflexivity.
      + intro Ew; apply Hne, Fin.to_nat_inj.
        injection Ew as Ek; exact Ek.
  Qed.

  Lemma fair_eventually_picks `{FairScheduler sch} st : EventuallyPicks sch n i st.
  Proof.
    pose proof (fair_scheduled n i st Pure ltac:(constructor)) as Hag.
    cdestruct Hag.
    apply (af_trace_eventually_picks _ Pure Hp st); [reflexivity|discriminate].
  Qed.
End FairBridge.

(** Any policy whose picks are inductively fair is a [FairScheduler]. *)
Lemma eventually_picks_fair (sch : Scheduler) :
  (forall n (i : Fin.t (S n)) st, EventuallyPicks sch n i st) -> FairScheduler sch.
Proof.
  intros Hep n i.
  coinduction R CIH; intros st w Hw.
  split; [apply eventually_picks_af; [apply Hep|exact Hw]|].
  split.
  - rewrite unfold_sched_trace; apply can_step_br; exists Fin.F1.
    apply can_step_vis; [exact tt|exact Hw].
  - intros t' w' TR.
    rewrite unfold_sched_trace in TR.
    apply ktrans_br in TR as (a & TR).
    apply ktrans_vis in TR as ([] & -> & Heq & _); rewrite <- Heq.
    apply CIH; constructor.
Qed.

Lemma rr_eventually_picks n (i : Fin.t (S n)) : forall m, EventuallyPicks rr_scheduler n i m.
Proof.
  assert (Hk : forall k m, (m + k) mod S n = slot_index i -> EventuallyPicks rr_scheduler n i m).
  { induction k as [|k IH]; intros m Hm; constructor; intros a Hne;
      cbn [sched_pick rr_scheduler fst snd] in *.
    - exfalso; apply Hne, Fin.to_nat_inj; unfold rr_pick; rewrite Fin.to_nat_of_nat; cbn [proj1_sig].
      rewrite Nat.add_0_r in Hm; exact Hm.
    - apply IH; rewrite <- Hm; f_equal; lia. }
  intro m; apply (Hk (S n - m mod S n + slot_index i)).
  pose proof (Nat.div_mod m (S n) (Nat.neq_succ_0 n)) as Hdm.
  pose proof (Nat.mod_upper_bound m (S n) (Nat.neq_succ_0 n)) as Hub.
  pose proof (proj2_sig (Fin.to_nat i)) as Hi; unfold slot_index in *.
  replace (m + (S n - m mod S n + proj1_sig (Fin.to_nat i)))
    with (proj1_sig (Fin.to_nat i) + (m / S n + 1) * S n) by lia.
  rewrite Nat.Div0.mod_add, Nat.mod_small; [reflexivity|exact Hi].
Qed.

#[global] Instance rr_fair : FairScheduler rr_scheduler :=
  eventually_picks_fair rr_scheduler (fun n i => rr_eventually_picks n i).

(** * Inversion rules: invariant, well-founded rank, helpful slot.

    The certificate is the Manna–Pnueli response rule under justice: a turn
    either reaches the goal, or strictly decreases the rank, or is taken by a
    non-helpful slot and changes neither rank nor helpful slot.  Fairness of
    the policy guarantees that the helpful slot is eventually picked.  The
    pool text is part of the invariant: threads may change code at turn
    boundaries (program-counter residuals as in allocator pools). *)
Section PoolRulesFair.
  Context {E : Type -> Type} {W Sigma : Type}
    (handler : E ~> stateT Sigma (ctreeW W Bn)) (sch : Scheduler) {n : nat}.

  Abbreviation exactW := (fun X (t u : ctreeW W Bn X) => t ≅ u).
  #[local] Abbreviation fair := (interp_schedule_fair sch handler (S n)).

  Record FairCertificate {G V : Type}
      (Inv : G -> pool E Bn (S n) -> Sigma -> Prop)
      (rank : G -> V) (ltV : V -> V -> Prop)
      (target : G -> Fin.t (S n)) (P : W -> Prop) : Prop := {
    fair_wf : well_founded ltV;
    fair_turn : forall g ts sigma (j : Fin.t (S n)), Inv g ts sigma ->
      exists g' logs residual sigma',
        ThreadSegment handler exactW (ts $ j) sigma logs residual sigma' /\
        Inv g' (ts @ j := residual) sigma' /\
        (List.Exists P logs \/
         ltV (rank g') (rank g) \/
         (j <> target g /\ rank g' = rank g /\ target g' = target g))
  }.
  Arguments fair_wf {G V Inv rank ltV target P} _.
  Arguments fair_turn {G V Inv rank ltV target P} _ g ts sigma j _.

  (** Closed turns alone, for the [AG] half. *)
  Definition ClosedPool {G} (Inv : G -> pool E Bn (S n) -> Sigma -> Prop) : Prop :=
    forall g ts sigma (j : Fin.t (S n)), Inv g ts sigma ->
      exists g' logs residual sigma',
        ThreadSegment handler exactW (ts $ j) sigma logs residual sigma' /\
        Inv g' (ts @ j := residual) sigma'.

  Lemma fair_certificate_closed {G V} Inv rank ltV target P :
    @FairCertificate G V Inv rank ltV target P -> ClosedPool Inv.
  Proof.
    intros Hc g ts sigma j Hinv.
    destruct (fair_turn Hc g ts sigma j Hinv) as (g' & logs & residual & sigma' & Hseg & Hinv' & _).
    exists g', logs, residual, sigma'; split; assumption.
  Qed.

  (** ** The [AG] half: closed turns keep [φ] invariant on the fair runner. *)
  Lemma ag_pool_fair_invariance {G} (Inv : G -> pool E Bn (S n) -> Sigma -> Prop)
      (φ : ticllW (W + nat)) :
    ClosedPool Inv ->
    (forall (t : ctreeW (W + nat) Bn (Sigma * unit)) w, not_done w ->
       <( t, w |= φ )> -> <( {Step t}, w |= φ )>) ->
    (forall (o : W) (t : ctreeW (W + nat) Bn (Sigma * unit)) w, not_done w ->
       <( t, {Obs (Log (inl o)) tt} |= φ )> -> <( {Vis (Log (inl o)) (fun _ => t)}, w |= φ )>) ->
    (forall g ts sigma st w, Inv g ts sigma -> not_done w ->
       <( {fair ts None st sigma}, w |= φ )>) ->
    forall g ts sigma focus st w, Inv g ts sigma -> not_done w ->
      <( {fair ts focus st sigma}, w |= AG φ )>.
  Proof.
    intros Hclosed Hstep Hlog Hφ.
    assert (Hpref : forall xs (t : ctreeW (W + nat) Bn (Sigma * unit)),
      (forall w, not_done w -> <( t, w |= φ )>) ->
      forall w, not_done w -> <( {emit_list (List.map inl xs) t}, w |= φ )>).
    { induction xs as [|o xs IH]; intros t Ht w Hw; [apply Ht, Hw|].
      cbn [List.map]; rewrite emit_list_cons.
      apply Hlog; [exact Hw|]; apply IH; [exact Ht|constructor]. }
    coinduction R CIH; intros g ts sigma focus st w Hinv Hw.
    assert (Hnone : forall g ts sigma st w, Inv g ts sigma -> not_done w ->
      agcF (entailsL (Sigma * unit) φ) (elem R) (fair ts None st sigma) w).
    { clear g ts sigma focus st w Hinv Hw; intros g ts sigma st w Hinv Hw.
      pose proof (Hφ g ts sigma st w Hinv Hw) as Hnow.
      rewrite interp_schedule_fair_select in Hnow |- *.
      split; [exact Hnow|]; split.
      - apply can_step_br; exists Fin.F1; apply can_step_vis; [exact tt|exact Hw].
      - intros t' w' Htr.
        apply ktrans_br in Htr as (a & Htr).
        apply ktrans_vis in Htr as ([] & -> & Heq & _); rewrite <- Heq.
        apply (b_chain R); split; [|split].
        + apply Hstep; [constructor|].
          destruct (Hclosed g ts sigma (fst (sched_pick sch n st a)) Hinv)
            as (g' & logs & residual & sigma' & Hseg & Hinv').
          rewrite (segment_interp_fair sch handler exactW (fun X t u => relabel_equ_sb t u)
            n ts _ _ sigma logs residual sigma' Hseg).
          apply Hpref; [|constructor].
          intros w'' Hw''; apply (Hφ g'); [exact Hinv'|exact Hw''].
        + apply can_step_step; constructor.
        + intros t'' w'' Htr.
          apply ktrans_step in Htr as (Heq' & <- & _); rewrite Heq'.
          apply (CIH g ts sigma (Some _)); [exact Hinv|constructor]. }
    destruct focus as [i|]; [|apply (Hnone g ts sigma st w Hinv Hw)].
    destruct (Hclosed g ts sigma i Hinv) as (g' & logs & residual & sigma' & Hseg & Hinv').
    rewrite (segment_interp_fair sch handler exactW (fun X t u => relabel_equ_sb t u)
      n ts i st sigma logs residual sigma' Hseg).
    clear Hseg; revert w Hw.
    induction logs as [|o logs IH]; intros w Hw.
    { cbn [List.map emit_list List.fold_right]; apply (Hnone g' _ sigma' st w Hinv' Hw). }
    cbn [List.map]; rewrite emit_list_cons.
    split; [|split].
    - apply Hlog; [exact Hw|].
      apply Hpref; [|constructor].
      intros w'' Hw''; apply (Hφ g'); [exact Hinv'|exact Hw''].
    - apply can_step_vis; [exact tt|exact Hw].
    - intros t' w' Htr.
      apply ktrans_vis in Htr as ([] & -> & Heq & _); rewrite <- Heq.
      apply (b_chain R), IH; constructor.
  Qed.

  (** ** The [AF] half: the helpful slot is eventually picked, and every turn
      makes progress toward the goal or leaves the rank alone. *)
  Lemma aul_pool_fair_eventually `{FairScheduler sch} {G V} Inv rank ltV target P :
    @FairCertificate G V Inv rank ltV target P ->
    forall g ts sigma focus st w, Inv g ts sigma -> not_done w ->
      <( {fair ts focus st sigma}, w |= AF visW {fair_obs P} )>.
  Proof.
    intros Hcert g.
    induction g as [g IHrank] using
      (well_founded_induction (wf_inverse_image G V ltV rank (fair_wf Hcert))).
    intros ts sigma focus st w Hinv Hw.
    (* A turn of the helpful slot: a hit or a strict rank drop. *)
    assert (Htarget : forall g0 ts sigma st w,
      Inv g0 ts sigma -> rank g0 = rank g -> target g0 = target g -> not_done w ->
      <( {fair ts (Some (target g)) st sigma}, w |= AF visW {fair_obs P} )>).
    { intros g0 ts0 sigma0 st0 w0 Hinv0 Hrank Htgt Hw0.
      destruct (fair_turn Hcert g0 ts0 sigma0 (target g) Hinv0)
        as (g' & logs & residual & sigma' & Hseg & Hinv' & [HP|[Hlt|(Hne & _)]]);
        [| |exfalso; apply Hne; symmetry; exact Htgt];
        rewrite (segment_interp_fair sch handler exactW (fun X t u => relabel_equ_sb t u)
          n ts0 _ st0 sigma0 logs residual sigma' Hseg).
      - apply List.Exists_exists in HP as (o & Hin & HP).
        eapply af_emit_list_member with (o := inl o);
          [exact Hw0|apply List.in_map; exact Hin|exact HP].
      - apply af_emit_list with (xs := List.map inl logs); [exact Hw0|].
        apply (IHrank g'); [rewrite <- Hrank; exact Hlt|exact Hinv'|].
        apply after_logs_not_done; exact Hw0. }
    (* Until the helpful slot is picked, the rank is preserved. *)
    assert (Hinner : forall st, EventuallyPicks sch n (target g) st ->
      forall g0 ts sigma focus w,
        Inv g0 ts sigma -> rank g0 = rank g -> target g0 = target g -> not_done w ->
        <( {fair ts focus st sigma}, w |= AF visW {fair_obs P} )>).
    { intros st0 Hep; induction Hep as [st0 Hst0 IH].
      assert (Hnone : forall g0 ts sigma w,
        Inv g0 ts sigma -> rank g0 = rank g -> target g0 = target g -> not_done w ->
        <( {fair ts None st0 sigma}, w |= AF visW {fair_obs P} )>).
      { intros g0 ts0 sigma0 w0 Hinv0 Hrank Htgt Hw0.
        rewrite interp_schedule_fair_select.
        apply aul_br; [apply ticll_top; exact Hw0|exists Fin.F1; apply can_step_vis; [exact tt|exact Hw0]|].
        intros a t' w' TR.
        apply ktrans_vis in TR as ([] & -> & Heq & _); rewrite <- Heq.
        apply aul_step; right; split; [apply ticll_top; constructor|].
        destruct (Fin.eq_dec (fst (sched_pick sch n st0 a)) (target g)) as [Hj|Hj].
        - rewrite Hj; apply (Htarget g0); [exact Hinv0|exact Hrank|exact Htgt|constructor].
        - apply (IH a Hj g0); [exact Hinv0|exact Hrank|exact Htgt|constructor]. }
      intros g0 ts0 sigma0 [j|] w0 Hinv0 Hrank Htgt Hw0; [|apply (Hnone g0); assumption].
      destruct (fair_turn Hcert g0 ts0 sigma0 j Hinv0)
        as (g' & logs & residual & sigma' & Hseg & Hinv' & [HP|[Hlt|(Hne & Hrank' & Htgt')]]);
        rewrite (segment_interp_fair sch handler exactW (fun X t u => relabel_equ_sb t u)
          n ts0 j st0 sigma0 logs residual sigma' Hseg).
      - apply List.Exists_exists in HP as (o & Hin & HP).
        eapply af_emit_list_member with (o := inl o);
          [exact Hw0|apply List.in_map; exact Hin|exact HP].
      - apply af_emit_list with (xs := List.map inl logs); [exact Hw0|].
        apply (IHrank g'); [rewrite <- Hrank; exact Hlt|exact Hinv'|].
        apply after_logs_not_done; exact Hw0.
      - apply af_emit_list with (xs := List.map inl logs); [exact Hw0|].
        apply (Hnone g'); [exact Hinv'|congruence|congruence|].
        apply after_logs_not_done; exact Hw0. }
    apply (Hinner st (fair_eventually_picks sch n (target g) st) g);
      [exact Hinv|reflexivity|reflexivity|exact Hw].
  Qed.

  (** The fairness inversion rule: witnesses are an invariant, a well-founded
      rank and a helpful slot. *)
  Theorem agaf_pool_fair `{FairScheduler sch} {G V} Inv rank ltV target P :
    @FairCertificate G V Inv rank ltV target P ->
    forall g ts sigma focus st w, Inv g ts sigma -> not_done w ->
      <( {fair ts focus st sigma}, w |= AG (AF visW {fair_obs P}) )>.
  Proof.
    intro Hcert.
    apply ag_pool_fair_invariance.
    - exact (fair_certificate_closed _ _ _ _ _ Hcert).
    - intros t w Hw Ht; apply aul_step; right; split; [apply ticll_top; exact Hw|exact Ht].
    - intros o t w Hw Ht; apply (aul_vis _ _ tt); right; split;
        [apply ticll_top; exact Hw|intros []; exact Ht].
    - intros g ts sigma st w Hinv Hw.
      apply (aul_pool_fair_eventually _ _ _ _ _ Hcert g ts sigma None st w Hinv Hw).
  Qed.

  (** ** Fixed pool text, one log per turn, constant helpful slot. *)
  Definition FairTurns {G V} (ts : pool E Bn (S n)) (i : Fin.t (S n))
      (Inv : G -> Sigma -> Prop) (rank : G -> V) (ltV : V -> V -> Prop) (P : W -> Prop) : Prop :=
    forall g sigma (j : Fin.t (S n)), Inv g sigma ->
    exists g' sigma' o,
      segment_to handler exactW (ts $ j) sigma (List.cons o List.nil) (ts $ j) sigma' /\
      Inv g' sigma' /\
      (P o \/ ltV (rank g') (rank g) \/ (j <> i /\ rank g' = rank g)).

  Theorem agaf_fair_turns `{FairScheduler sch} {G V} ts i Inv rank ltV P :
    well_founded ltV -> @FairTurns G V ts i Inv rank ltV P ->
    forall g sigma focus st w, Inv g sigma -> not_done w ->
      <( {fair ts focus st sigma}, w |= AG (AF visW {fair_obs P}) )>.
  Proof.
    intros Hwf Hturns g sigma focus st w Hinv Hw.
    refine (agaf_pool_fair (fun g ts' σ => Inv g σ /\ pool_guard_equ ts' ts) rank ltV (fun _ => i) P
      _ g ts sigma focus st w (conj Hinv (fun j => guard_equ_equ _ _ (reflexivity _))) Hw).
    constructor; [exact Hwf|].
    intros g0 ts' σ j (Hinv0 & Hpool).
    destruct (Hturns g0 σ j Hinv0) as (g' & σ' & o & (residual & Hseg & Htail) & Hinv' & Hcase).
    apply (proj2 (guard_equ_segment_iff handler exactW (ts' $ j) (ts $ j) (Hpool j)
      σ (List.cons o List.nil) residual σ')) in Hseg.
    exists g', (List.cons o List.nil), residual, σ'; split; [exact Hseg|]; split.
    - split; [exact Hinv'|].
      intro k; destruct (Fin.eq_dec k j) as [->|Hne].
      + rewrite Vector.nth_replace_eq; exact Htail.
      + rewrite Vector.nth_replace_neq by congruence; apply Hpool.
    - destruct Hcase as [HP|[Hlt|(Hne & Hrank)]];
        [left; constructor; exact HP|right; left; exact Hlt|right; right; auto].
  Qed.

  (** ** Abstract-model clients: ghost data projects to model states. *)
  Theorem agaf_pool_simulation_fair `{FairScheduler sch} {St Act G V}
      (actor : Fin.t (S n) -> Act) (slot : Act -> Fin.t (S n))
      (slot_actor : forall i, slot (actor i) = i)
      (step : Act -> St -> option (St * option W)) (pool_of : St -> pool E Bn (S n))
      (agree : Sigma -> St -> Prop) (Inv : St -> Prop)
      (Hsim : PoolSimulation n handler slot step pool_of agree Inv)
      (st_of : G -> St) (InvG : G -> Prop) (rank : G -> V) (ltV : V -> V -> Prop)
      (target : G -> Fin.t (S n)) (P : W -> Prop) :
    well_founded ltV ->
    (forall g, InvG g -> Inv (st_of g)) ->
    (forall g who s' event, InvG g -> step who (st_of g) = Some (s', event) ->
       exists g', st_of g' = s' /\ InvG g' /\
         ((exists o, event = Some o /\ P o) \/ ltV (rank g') (rank g) \/
          (slot who <> target g /\ rank g' = rank g /\ target g' = target g))) ->
    forall g ts sigma focus st w,
      InvG g -> agree sigma (st_of g) -> pool_guard_equ ts (pool_of (st_of g)) -> not_done w ->
      <( {fair ts focus st sigma}, w |= AG (AF visW {fair_obs P}) )>.
  Proof.
    intros Hwf HInv Hturn g ts sigma focus st w Hg Hagree Hpool Hw.
    refine (agaf_pool_fair
      (fun g ts σ => InvG g /\ agree σ (st_of g) /\ pool_guard_equ ts (pool_of (st_of g)))
      rank ltV target P _ g ts sigma focus st w (conj Hg (conj Hagree Hpool)) Hw).
    constructor; [exact Hwf|].
    intros g0 ts0 σ j (Hg0 & Hagree0 & Hpool0).
    destruct (simulation_total Hsim (actor j) (st_of g0) (HInv g0 Hg0)) as (s' & event & Hstep & _).
    destruct (Hturn g0 (actor j) s' event Hg0 Hstep) as (g' & Es' & Hg' & Hcase).
    destruct (selected_turn_segment Hsim ts0 (st_of g0) (actor j) s' event σ
      (HInv g0 Hg0) Hagree0 Hpool0 Hstep) as (residual & σ' & Hseg & Hagree' & Hpool').
    rewrite slot_actor in Hseg, Hpool', Hcase.
    exists g', (event_obs event), residual, σ'; split; [exact Hseg|]; split.
    - split; [exact Hg'|rewrite Es'; split; assumption].
    - destruct Hcase as [(o & -> & HP)|Hcase]; [left; constructor; exact HP|right; exact Hcase].
  Qed.
End PoolRulesFair.
