(** * The owned action machine of CoCSL.

    A forked CoCSL program after its outer fork is a pool whose slots are
    tagged with the lineage ([Child] or [Parent]) that owns them.  Each
    lineage owns a disjoint [ManagedHeap] reserved at the fork (its immutable
    [oc_anchor]) and its current heap, emission count, and last local
    observation.  The variable context is shared and read-only here.

    [owned_step] is the scheduler of [CTree.Interp.Yield.Mod] made
    state-visible: selection, source steps, yields, forks, returns, and every
    successful primitive is one labelled action of its owner.  This clock is
    finer than raw interpreted TICL; [owned_erasure] relates it to [run_nd].
    [project] keeps exactly one lineage, in its original order. *)

From TICL Require Export Lang.CoCSL.Frame.
From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector Relations
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Yield
  CTree.Events.Writer
  CTree.Interp.State.Mod
  CTree.Interp.Refine
  CTree.Interp.Yield.Mod
  CTree.Interp.Yield.SBisim
  CTree.Interp.Yield.Nondeterministic
  CTree.Interp.Yield.Frame
  CTree.Logic.Sim
  Utils.Vectors
  Utils.Pcm.

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

(** ** Lineages *)

Inductive side := Child | Parent.

Definition side_eq_dec (a b : side) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition side_eqb (a b : side) : bool :=
  match a, b with Child, Child | Parent, Parent => true | _, _ => false end.

Lemma side_eqb_spec a b : side_eqb a b = true <-> a = b.
Proof. destruct a, b; cbn; intuition congruence. Qed.

Definition other (i : side) : side := match i with Child => Parent | Parent => Child end.

(** Overwrite one lineage's field. *)
Definition side_upd {A} (f : side -> A) (i : side) (x : A) : side -> A :=
  fun j => if side_eqb j i then x else f j.

(** Keep one lineage's field and reset the other to [d]. *)
Definition side_only {A} (f : side -> A) (i : side) (d : A) : side -> A :=
  fun j => if side_eqb j i then f j else d.

(** ** Pools and configurations *)

Record TaggedPool := {
  tp_size : nat;
  tp_threads : pool sE Bn tp_size;
  tp_tags : Vector.t side tp_size;
  tp_focus : option (Fin.t tp_size)
}.

Record OwnedCfg := {
  oc_pool : TaggedPool;
  oc_anchor : side -> ManagedHeap;
  oc_heap : side -> ManagedHeap;
  oc_ctx : Ctx.Ctx;
  oc_base : nat;
  oc_count : side -> nat;
  oc_last : side -> option (indexed (nat * nat))
}.

Definition mk_pool n (v : pool sE Bn n) (g : Vector.t side n) (f : option (Fin.t n)) : TaggedPool :=
  {| tp_size := n; tp_threads := v; tp_tags := g; tp_focus := f |}.

Definition set_pool (c : OwnedCfg) (p : TaggedPool) : OwnedCfg :=
  {| oc_pool := p; oc_anchor := oc_anchor c; oc_heap := oc_heap c; oc_ctx := oc_ctx c;
     oc_base := oc_base c; oc_count := oc_count c; oc_last := oc_last c |}.

Definition set_heap (c : OwnedCfg) (i : side) (m : ManagedHeap) : OwnedCfg :=
  {| oc_pool := oc_pool c; oc_anchor := oc_anchor c; oc_heap := side_upd (oc_heap c) i m;
     oc_ctx := oc_ctx c; oc_base := oc_base c; oc_count := oc_count c; oc_last := oc_last c |}.

(** Emission advances only the owner's count; the remembered stamp is local. *)
Definition emit_cfg (c : OwnedCfg) (i : side) (payload : nat * nat) : OwnedCfg :=
  {| oc_pool := oc_pool c; oc_anchor := oc_anchor c; oc_heap := oc_heap c;
     oc_ctx := oc_ctx c; oc_base := oc_base c;
     oc_count := side_upd (oc_count c) i (S (oc_count c i));
     oc_last := side_upd (oc_last c) i (Some (stamp payload (oc_base c + oc_count c i))) |}.

Definition global_count (c : OwnedCfg) : nat :=
  oc_base c + oc_count c Child + oc_count c Parent.

(** The state one lineage sees, and the state the original runner sees. *)
Definition local_state (i : side) (c : OwnedCfg) : SSig :=
  (oc_heap c i, (oc_ctx c, oc_base c + oc_count c i)).

Definition joined_heap (c : OwnedCfg) : ManagedHeap := oc_heap c Child ⊎ oc_heap c Parent.

Definition joined_state (c : OwnedCfg) : SSig :=
  (joined_heap c, (oc_ctx c, global_count c)).

(** ** Actions *)

Inductive OwnedKind :=
| OASelect | OAStep | OAYield | OAFork | OAReturn
| OARead | OAWrite | OAFree | OACAS | OAGet
| OAEmit (payload : nat * nat) (global_index : nat).

Record OwnedAction := { owner : side; action_kind : OwnedKind }.

Definition act (i : side) (k : OwnedKind) : OwnedAction := {| owner := i; action_kind := k |}.

(** A thread reaches the non-guard head [u] after finitely many guards. *)
Definition headed (t u : thread sE Bn) : Prop := exists n, t ≅ guards n u.

(** One primitive on the owner's local heap.  Allocation and context writes
    have no rule; failed primitives have no result. *)
Definition heap_prim (i : side) (c : OwnedCfg) {Y} (e : heapE Y) : option (OwnedKind * Y * OwnedCfg) :=
  let m := oc_heap c i in
  match e in heapE Y return option (OwnedKind * Y * OwnedCfg) with
  | HRead a => match fst m a with Some v => Some (OARead, v, c) | None => None end
  | HWrite a v =>
      match fst m a with
      | Some _ => Some (OAWrite, tt, set_heap c i (upd (fst m) a v, snd m))
      | None => None
      end
  | HAlloc _ => None
  | HFree b =>
      match managed_free m b with
      | Some m' => Some (OAFree, tt, set_heap c i m')
      | None => None
      end
  | HCAS a expected desired =>
      match fst m a with
      | None => None
      | Some current =>
          if Nat.eqb current expected
          then Some (OACAS, true, set_heap c i (upd (fst m) a desired, snd m))
          else Some (OACAS, false, c)
      end
  end.

Definition ctx_prim (c : OwnedCfg) {Y} (e : stateE Ctx.Ctx Y) : option (OwnedKind * Y * OwnedCfg) :=
  match e in stateE _ Y return option (OwnedKind * Y * OwnedCfg) with
  | Get => Some (OAGet, oc_ctx c, c)
  | Put _ => None
  end.

Definition emit_prim (i : side) (c : OwnedCfg) {Y} (e : writerE (nat * nat) Y)
  : option (OwnedKind * Y * OwnedCfg) :=
  match e in writerE _ Y return option (OwnedKind * Y * OwnedCfg) with
  | Log p => Some (OAEmit p (global_count c), tt, emit_cfg c i p)
  end.

Definition prim_step (i : side) (c : OwnedCfg) {Y} (e : sE Y) : option (OwnedKind * Y * OwnedCfg) :=
  match e with
  | inl1 he => heap_prim i c he
  | inr1 (inl1 se) => ctx_prim c se
  | inr1 (inr1 we) => emit_prim i c we
  end.

(** Selection from an unfocused nonempty pool. *)
Definition sel_step (c : OwnedCfg) n (v : pool sE Bn (S n)) (g : Vector.t side (S n))
  (a : OwnedAction) (c' : OwnedCfg) : Prop :=
  exists j, a = act (g $ j) OASelect /\ c' = set_pool c (mk_pool (S n) v g (Some j)).

(** One action of the focused slot [j], after its finite guard prefix. *)
Definition focus_step (c : OwnedCfg) n (v : pool sE Bn (S n)) (g : Vector.t side (S n))
  (j : Fin.t (S n)) (a : OwnedAction) (c' : OwnedCfg) : Prop :=
  (exists t, headed (v $ j) (Step t) /\ a = act (g $ j) OAStep /\
     c' = set_pool c (mk_pool (S n) (v @ j := t) g (Some j))) \/
  (exists k, headed (v $ j) (Vis (inl1 Yield : CEff unit) k) /\ a = act (g $ j) OAYield /\
     c' = set_pool c (mk_pool (S n) (v @ j := k tt) g None)) \/
  (exists k, headed (v $ j) (Vis (inr1 (inl1 Fork) : CEff bool) k) /\ a = act (g $ j) OAFork /\
     c' = set_pool c (mk_pool (S (S n)) (k true :: (v @ j := k false)) ((g $ j) :: g) (Some (Fin.FS j)))) \/
  (headed (v $ j) (Ret tt) /\ a = act (g $ j) OAReturn /\
     c' = set_pool c (mk_pool n (v -- j) (g -- j) None)) \/
  (exists Y (e : sE Y) (k : Y -> thread sE Bn) kind y c1,
     headed (v $ j) (Vis (inr1 (inr1 e) : CEff Y) k) /\
     prim_step (g $ j) c e = Some (kind, y, c1) /\ a = act (g $ j) kind /\
     c' = set_pool c1 (mk_pool (S n) (v @ j := k y) g (Some j))).

Definition owned_step (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) : Prop :=
  match oc_pool c with
  | Build_TaggedPool n v g f =>
      match n return pool sE Bn n -> Vector.t side n -> option (Fin.t n) -> Prop with
      | 0 => fun _ _ _ => False
      | S n' => fun v g f =>
          match f with
          | None => sel_step c n' v g a c'
          | Some j => focus_step c n' v g j a c'
          end
      end v g f
  end.

Definition owned_next (c c' : OwnedCfg) : Prop := exists a, owned_step c a c'.

(** Progress for an arbitrary transition relation (not the world-indexed
    Kripke [can_step]). *)
Definition hcan_step (R : relation OwnedCfg) (c : OwnedCfg) : Prop := exists c', R c c'.

(** ** Initial configurations *)

(** The state after the outer fork: child slot first, parent focused. *)
Definition init_owned (child parent : CProg unit) (h h' : ManagedHeap) (ctx : Ctx.Ctx) (base : nat)
  : OwnedCfg :=
  let hs := fun i => match i with Child => h | Parent => h' end in
  {| oc_pool := mk_pool 2 [denote child; denote parent] [Child; Parent] (Some (Fin.FS Fin.F1));
     oc_anchor := hs; oc_heap := hs; oc_ctx := ctx; oc_base := base;
     oc_count := fun _ => 0; oc_last := fun _ => None |}.

(** A standalone singleton lineage, focused or awaiting selection. *)
Definition init_local (i : side) (p : CProg unit) (h : ManagedHeap) (ctx : Ctx.Ctx) (base : nat)
  (focused : bool) : OwnedCfg :=
  let hs := side_only (fun _ => h) i managed_empty in
  {| oc_pool := mk_pool 1 [denote p] [i] (if focused then Some Fin.F1 else None);
     oc_anchor := hs; oc_heap := hs; oc_ctx := ctx; oc_base := base;
     oc_count := fun _ => 0; oc_last := fun _ => None |}.

(** ** Projection onto one lineage *)

Definition fin_nat {n} (j : Fin.t n) : nat := proj1_sig (Fin.to_nat j).

Definition tp_slots (p : TaggedPool) : list (thread sE Bn * side) :=
  List.combine (Vector.to_list (tp_threads p)) (Vector.to_list (tp_tags p)).

Definition owned_by (i : side) (s : thread sE Bn * side) : bool := side_eqb (snd s) i.

Definition proj_indices (i : side) (p : TaggedPool) : list (Fin.t (tp_size p)) :=
  List.filter (fun j => side_eqb (tp_tags p $ j) i) (fin_all (tp_size p)).

Definition proj_slots (i : side) (p : TaggedPool) : list (thread sE Bn * side) :=
  List.map (fun j => (tp_threads p $ j, tp_tags p $ j)) (proj_indices i p).

Lemma tp_slots_indices p :
  List.map (fun j => (tp_threads p $ j, tp_tags p $ j)) (fin_all (tp_size p)) = tp_slots p.
Proof.
  destruct p as [n v g f]; unfold tp_slots; cbn [tp_threads tp_tags tp_size]; clear f.
  revert g; induction v as [|x n v IH]; intros g; dependent destruction g; [reflexivity|].
  rewrite !Vector.to_list_cons; cbn [fin_all List.map List.combine].
  rewrite List.map_map; f_equal; apply IH.
Qed.

Lemma proj_slots_filter i p : proj_slots i p = List.filter (owned_by i) (tp_slots p).
Proof.
  rewrite <- tp_slots_indices; unfold proj_slots, proj_indices.
  rewrite List.filter_map_swap; reflexivity.
Qed.

Lemma vector_to_list_length {A n} (v : Vector.t A n) : List.length (Vector.to_list v) = n.
Proof.
  induction v as [|x n v IH]; [reflexivity|].
  rewrite Vector.to_list_cons; cbn; now rewrite IH.
Qed.

Lemma vector_to_list_nth_error {A n} (v : Vector.t A n) (j : Fin.t n) :
  List.nth_error (Vector.to_list v) (fin_nat j) = Some (v $ j).
Proof.
  induction v as [|x n v IH]; [inversion j|].
  dependent destruction j; rewrite Vector.to_list_cons; [reflexivity|].
  unfold fin_nat in *; cbn; destruct (Fin.to_nat j) as [k Hk] eqn:Hj; cbn.
  specialize (IH j); rewrite Hj in IH; exact IH.
Qed.

Lemma nth_error_combine_some {A B} (l : list A) (l' : list B) k x y :
  List.nth_error l k = Some x -> List.nth_error l' k = Some y ->
  List.nth_error (List.combine l l') k = Some (x, y).
Proof.
  revert l' k; induction l as [|a l IH]; intros [|b l'] [|k] H H'; cbn in *;
    try discriminate; try congruence.
  apply IH; assumption.
Qed.

Lemma tp_slots_nth_error (p : TaggedPool) (j : Fin.t (tp_size p)) :
  List.nth_error (tp_slots p) (fin_nat j) = Some (tp_threads p $ j, tp_tags p $ j).
Proof.
  unfold tp_slots; apply nth_error_combine_some; apply vector_to_list_nth_error.
Qed.

Lemma filter_firstn_lt {A} (p : A -> bool) (l : list A) k x :
  List.nth_error l k = Some x -> p x = true ->
  List.length (List.filter p (List.firstn k l)) < List.length (List.filter p l).
Proof.
  revert k; induction l as [|a l IH]; intros [|k] Hn Hp; cbn in *; try discriminate.
  - injection Hn as ->; rewrite Hp; cbn; lia.
  - destruct (p a); cbn; [specialize (IH k Hn Hp); lia|exact (IH k Hn Hp)].
Qed.

Lemma owned_by_self (i : side) t : owned_by i (t, i) = true.
Proof. destruct i; reflexivity. Qed.

Lemma proj_pos_lt (i : side) (p : TaggedPool) (j : Fin.t (tp_size p)) :
  (tp_tags p $ j) = i ->
  List.length (List.filter (owned_by i) (List.firstn (fin_nat j) (tp_slots p))) <
    List.length (proj_slots i p).
Proof.
  intro Hj; rewrite proj_slots_filter.
  apply (filter_firstn_lt _ _ _ _ (tp_slots_nth_error p j)).
  rewrite Hj; apply owned_by_self.
Qed.

(** An owned focus is rebased to its rank among its lineage; a foreign focus
    is cleared. *)
Definition proj_focus (i : side) (p : TaggedPool) : option (Fin.t (List.length (proj_slots i p))) :=
  match tp_focus p with
  | Some j =>
      match side_eq_dec (tp_tags p $ j) i with
      | left H => Some (Fin.of_nat_lt (proj_pos_lt i p j H))
      | right _ => None
      end
  | None => None
  end.

Definition project_pool (i : side) (p : TaggedPool) : TaggedPool :=
  {| tp_size := List.length (proj_slots i p);
     tp_threads := Vector.map fst (Vector.of_list (proj_slots i p));
     tp_tags := Vector.map snd (Vector.of_list (proj_slots i p));
     tp_focus := proj_focus i p |}.

Definition project (i : side) (c : OwnedCfg) : OwnedCfg :=
  {| oc_pool := project_pool i (oc_pool c);
     oc_anchor := side_only (oc_anchor c) i managed_empty;
     oc_heap := side_only (oc_heap c) i managed_empty;
     oc_ctx := oc_ctx c;
     oc_base := oc_base c;
     oc_count := side_only (oc_count c) i 0;
     oc_last := side_only (oc_last c) i None |}.

(** A global action as its owner sees it: only an emission's index changes,
    from the global to the local count. *)
Definition project_action (i : side) (c : OwnedCfg) (a : OwnedAction) : OwnedAction :=
  match action_kind a with
  | OAEmit p _ => act (owner a) (OAEmit p (oc_base c + oc_count c i))
  | k => act (owner a) k
  end.

(** ** Configuration equivalence *)

Definition slot_equ (s s' : thread sE Bn * side) : Prop := fst s ≅ fst s' /\ snd s = snd s'.

Definition focus_nat (p : TaggedPool) : option nat := option_map fin_nat (tp_focus p).

Definition tp_equ (p q : TaggedPool) : Prop :=
  List.Forall2 slot_equ (tp_slots p) (tp_slots q) /\ focus_nat p = focus_nat q.

Definition owned_equ (c d : OwnedCfg) : Prop :=
  tp_equ (oc_pool c) (oc_pool d) /\
  (forall i, oc_anchor c i ≈ oc_anchor d i) /\
  (forall i, oc_heap c i ≈ oc_heap d i) /\
  oc_ctx c = oc_ctx d /\ oc_base c = oc_base d /\
  (forall i, oc_count c i = oc_count d i) /\
  (forall i, oc_last c i = oc_last d i).

(** ** Ownership invariant *)

Definition support_le (m r : ManagedHeap) : Prop :=
  (forall a, fst m a <> None -> fst r a <> None) /\
  (forall b, snd m b <> None -> snd r b <> None).

Definition owned_wf (c : OwnedCfg) : Prop :=
  managed_wf (oc_heap c Child) /\ managed_wf (oc_heap c Parent) /\
  managed_wf (oc_anchor c Child) /\ managed_wf (oc_anchor c Parent) /\
  oc_anchor c Child # oc_anchor c Parent /\
  support_le (oc_heap c Child) (oc_anchor c Child) /\
  support_le (oc_heap c Parent) (oc_anchor c Parent) /\
  oc_heap c Child # oc_heap c Parent.

(** ** Admission *)

(** Components may not allocate (first fit is absolute) or write the shared
    context. *)
Definition component_event_ok : forall X, sE X -> Prop :=
  fun X e =>
    match e with
    | inl1 (HAlloc _) => False
    | inr1 (inl1 (Put _)) => False
    | _ => True
    end.

Definition component_ok {A} (p : CProg A) : Prop := prog_ok (okE_thread component_event_ok) p.

(** The address a pending primitive touches lies in reservation [r]. *)
Definition prim_addr_ok (r : ManagedHeap) {Y} (e : sE Y) : Prop :=
  match e with
  | inl1 he =>
      match he with
      | HRead a | HWrite a _ | HCAS a _ _ => fst r a <> None
      | HFree b => b = 0 \/ snd r b <> None
      | HAlloc _ => True
      end
  | inr1 _ => True
  end.

Definition focused_thread (p : TaggedPool) : option (thread sE Bn * side) :=
  match tp_focus p with
  | Some j => Some (tp_threads p $ j, tp_tags p $ j)
  | None => None
  end.

(** Every pending focused primitive of every reachable configuration stays
    inside [r], whether or not it would succeed. *)
Definition confined (r : ManagedHeap) (c0 : OwnedCfg) : Prop :=
  forall c, clos_refl_trans _ owned_next c0 c ->
  forall t i Y (e : sE Y) k,
    focused_thread (oc_pool c) = Some (t, i) ->
    headed t (Vis (inr1 (inr1 e) : CEff Y) k) ->
    prim_addr_ok r e.

Definition admissible (child parent : CProg unit) (h h' : ManagedHeap) (ctx : Ctx.Ctx) (base : nat)
  : Prop :=
  managed_wf h /\ managed_wf h' /\ h # h' /\
  component_ok child /\ component_ok parent /\
  confined h (project Child (init_owned child parent h h' ctx base)) /\
  confined h' (project Parent (init_owned child parent h h' ctx base)).

(** A configuration reachable from an admitted fork, up to [owned_equ]. *)
Definition coupled (c : OwnedCfg) : Prop :=
  exists child parent h h' ctx base d,
    admissible child parent h h' ctx base /\
    clos_refl_trans _ owned_next (init_owned child parent h h' ctx base) d /\
    owned_equ d c.

(** ** Operational adequacy: the instrumented interpreter *)

CoFixpoint instrument_owned (c : OwnedCfg) : ctreeW OwnedAction Bn OwnedCfg :=
  match oc_pool c with
  | Build_TaggedPool n v g f =>
      match n return pool sE Bn n -> Vector.t side n -> option (Fin.t n) ->
                     ctreeW OwnedAction Bn OwnedCfg with
      | 0 => fun _ _ _ => Ret c
      | S n' => fun v g f =>
          match f with
          | None =>
              brS (branchn (S n')) (fun j =>
                Vis (Log (act (g $ j) OASelect))
                  (fun _ => instrument_owned (set_pool c (mk_pool (S n') v g (Some j)))))
          | Some j =>
              match observe (v $ j) with
              | RetF _ =>
                  Vis (Log (act (g $ j) OAReturn))
                    (fun _ => instrument_owned (set_pool c (mk_pool n' (v -- j) (g -- j) None)))
              | StuckF => Stuck
              | BrF _ _ => Stuck
              | StepF t =>
                  Vis (Log (act (g $ j) OAStep))
                    (fun _ => instrument_owned (set_pool c (mk_pool (S n') (v @ j := t) g (Some j))))
              | GuardF t =>
                  Guard (instrument_owned (set_pool c (mk_pool (S n') (v @ j := t) g (Some j))))
              | VisF e k =>
                  match e with
                  | inl1 y =>
                      match y in yieldE Y0 return (Y0 -> thread sE Bn) -> ctreeW OwnedAction Bn OwnedCfg with
                      | Yield => fun k =>
                          Vis (Log (act (g $ j) OAYield))
                            (fun _ => instrument_owned (set_pool c (mk_pool (S n') (v @ j := k tt) g None)))
                      end k
                  | inr1 (inl1 fk) =>
                      match fk in forkE Y0 return (Y0 -> thread sE Bn) -> ctreeW OwnedAction Bn OwnedCfg with
                      | Fork => fun k =>
                          Vis (Log (act (g $ j) OAFork))
                            (fun _ => instrument_owned (set_pool c
                               (mk_pool (S (S n')) (k true :: (v @ j := k false)) ((g $ j) :: g)
                                  (Some (Fin.FS j)))))
                      end k
                  | inr1 (inr1 e') =>
                      match prim_step (g $ j) c e' with
                      | Some (kind, y, c1) =>
                          Vis (Log (act (g $ j) kind))
                            (fun _ => instrument_owned (set_pool c1 (mk_pool (S n') (v @ j := k y) g (Some j))))
                      | None => Stuck
                      end
                  end
              end
          end
      end v g f
  end.

(** Erasure interprets the action log back into the original observations:
    an emission becomes its exact global stamp, a source step a visible step,
    and every other action returns silently.  The interpreter supplies its
    administrative guards; selection already retains its scheduler branch.
    A final configuration returns its joined state. *)
Definition handle_owned@{r +} :
  writerE OwnedAction ~> ctree@{_ _ _ _ r _} (writerE (CSLObs (nat * nat))) Bn :=
  fun _ e =>
    match e in writerE _ Y
      return ctree@{_ _ _ _ r _} (writerE (CSLObs (nat * nat))) Bn Y with
    | Log a =>
        match action_kind a with
        | OAEmit p n => CTree.trigger (Log (inr (stamp p n) : CSLObs (nat * nat)))
        | OAStep => Step (Ret tt)
        | _ => Ret tt
        end
    end.

Definition erase_owned (t : ctreeW OwnedAction Bn OwnedCfg)
  : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit) :=
  interp (M := ctree (writerE (CSLObs (nat * nat))) Bn) handle_owned t >>=
    fun c => Ret (joined_state c, tt).

#[global] Instance erase_owned_proper : Proper (equ eq ==> equ eq) erase_owned.
Proof. intros t u H; unfold erase_owned; rewrite H; reflexivity. Qed.

(** Returned states agree exactly except for extensional heap equality. *)
Definition owned_result_rel : relation (SSig * unit) :=
  fun '(s, x) '(s', x') => x = x' /\ snd s = snd s' /\ csl_memory s ≈ csl_memory s'.

(** ** Lineage-relative transitions *)

Definition own_next (i : side) (c c' : OwnedCfg) : Prop :=
  exists a, owned_step c a c' /\ owner a = i.

Definition foreign_next (i : side) (c c' : OwnedCfg) : Prop :=
  exists a, owned_step c a c' /\ owner a <> i.

(** Finitely many foreign actions, then one action of lineage [i]. *)
Definition weak_next (i : side) (c c' : OwnedCfg) : Prop :=
  exists mid, clos_refl_trans _ (foreign_next i) c mid /\ own_next i mid c'.

(** Every outgoing action is foreign. *)
Definition StutterOnly (i : side) (c : OwnedCfg) : Prop :=
  forall a c', owned_step c a c' -> owner a <> i.

(** The projection can move, and each of its moves is one global action of
    lineage [i]. *)
Definition OwnEnabled (i : side) (c : OwnedCfg) : Prop :=
  hcan_step owned_next (project i c) /\
  forall a' d', owned_step (project i c) a' d' ->
    exists a c', owned_step c a c' /\ owner a = i /\ project_action i c a = a' /\
      owned_equ (project i c') d'.

(** Pending focused primitives of [c] lie in their owner's reservation. *)
Definition head_confined (c : OwnedCfg) : Prop :=
  forall t i Y (e : sE Y) k,
    focused_thread (oc_pool c) = Some (t, i) ->
    headed t (Vis (inr1 (inr1 e) : CEff Y) k) ->
    prim_addr_ok (oc_anchor c i) e.

(** ** Equivalence and transition congruence *)

Lemma Forall2_slot_refl l : List.Forall2 slot_equ l l.
Proof. induction l; constructor; [split; reflexivity|assumption]. Qed.

Lemma Forall2_slot_sym l l' : List.Forall2 slot_equ l l' -> List.Forall2 slot_equ l' l.
Proof.
  induction 1 as [|x y l l' [Ht Hs] _ IH]; constructor; [split; symmetry; assumption|exact IH].
Qed.

Lemma Forall2_slot_trans l1 l2 l3 :
  List.Forall2 slot_equ l1 l2 -> List.Forall2 slot_equ l2 l3 -> List.Forall2 slot_equ l1 l3.
Proof.
  intros H; revert l3; induction H as [|x y l l' Hxy _ IH]; intros l3 H3; [exact H3|].
  inversion H3 as [|? z ? l'' Hyz H3']; subst; constructor.
  - destruct Hxy, Hyz; split; etransitivity; eassumption.
  - apply IH, H3'.
Qed.

#[global] Instance owned_equ_Equivalence : Equivalence owned_equ.
Proof.
  split.
  - intros c; refine (conj (conj (Forall2_slot_refl _) eq_refl)
      (conj _ (conj _ (conj eq_refl (conj eq_refl (conj _ _)))))); intros i;
      first [apply peq_refl|reflexivity].
  - intros c d ((Hs & Hf) & Ea & Eh & Ex & Eb & Ec & El).
    refine (conj (conj (Forall2_slot_sym _ _ Hs) (eq_sym Hf))
      (conj _ (conj _ (conj (eq_sym Ex) (conj (eq_sym Eb) (conj _ _)))))); intros i.
    + apply peq_sym, Ea.
    + apply peq_sym, Eh.
    + symmetry; apply Ec.
    + symmetry; apply El.
  - intros c d e ((Hs & Hf) & Ea & Eh & Ex & Eb & Ec & El)
      ((Hs' & Hf') & Ea' & Eh' & Ex' & Eb' & Ec' & El').
    refine (conj (conj (Forall2_slot_trans _ _ _ Hs Hs') (eq_trans Hf Hf'))
      (conj _ (conj _ (conj (eq_trans Ex Ex') (conj (eq_trans Eb Eb') (conj _ _)))))); intros i.
    + exact (peq_trans _ _ _ (Ea i) (Ea' i)).
    + exact (peq_trans _ _ _ (Eh i) (Eh' i)).
    + exact (eq_trans (Ec i) (Ec' i)).
    + exact (eq_trans (El i) (El' i)).
Qed.

Lemma tp_slots_length p : List.length (tp_slots p) = tp_size p.
Proof. unfold tp_slots; rewrite List.length_combine, !vector_to_list_length; apply Nat.min_id. Qed.

Lemma project_size_partition c :
  tp_size (oc_pool (project Child c)) +
  tp_size (oc_pool (project Parent c)) = tp_size (oc_pool c).
Proof.
  change (List.length (proj_slots Child (oc_pool c)) +
    List.length (proj_slots Parent (oc_pool c)) = tp_size (oc_pool c)).
  rewrite !proj_slots_filter, <- tp_slots_length.
  induction (tp_slots (oc_pool c)) as [|[t i] l IH]; [reflexivity|].
  unfold owned_by in *; destruct i;
    cbn [List.filter side_eqb side_eq_dec snd List.length] in *; lia.
Qed.

Lemma tp_equ_size p q : tp_equ p q -> tp_size p = tp_size q.
Proof.
  intros [H _]; rewrite <- (tp_slots_length p), <- (tp_slots_length q).
  exact (List.Forall2_length H).
Qed.

Lemma slots_Forall2_iff n (v w : pool sE Bn n) (g g' : Vector.t side n) :
  List.Forall2 slot_equ (List.combine (Vector.to_list v) (Vector.to_list g))
    (List.combine (Vector.to_list w) (Vector.to_list g')) <->
  (forall j, (v $ j) ≅ (w $ j)) /\ g = g'.
Proof.
  revert w g g'; induction v as [|x n v IH]; intros w g g'.
  - dependent destruction w; dependent destruction g; dependent destruction g'.
    split; [intros _; split; [intros j; inversion j|reflexivity]|intros _; constructor].
  - dependent destruction w; dependent destruction g; dependent destruction g'.
    rewrite !Vector.to_list_cons; cbn [List.combine]; split.
    + intros H; inversion H as [|? ? ? ? [Ht Hs] Hr]; subst; cbn in Ht, Hs; subst.
      apply IH in Hr as [Hp <-]; split; [|reflexivity].
      intros j; dependent destruction j; [exact Ht|apply Hp].
    + intros [Hp Hg]; apply Vector.cons_inj in Hg as [<- <-]; constructor.
      * split; [exact (Hp Fin.F1)|reflexivity].
      * apply IH; split; [intros j; exact (Hp (Fin.FS j))|reflexivity].
Qed.

Lemma tp_equ_mk n v g f w g' f' :
  tp_equ (mk_pool n v g f) (mk_pool n w g' f') <-> (forall j, (v $ j) ≅ (w $ j)) /\ g = g' /\ f = f'.
Proof.
  unfold tp_equ, tp_slots, focus_nat; cbn [tp_threads tp_tags tp_focus mk_pool].
  rewrite slots_Forall2_iff; split.
  - intros [[Hp Hg] Hf]; split; [exact Hp|split; [exact Hg|]].
    destruct f, f'; cbn in Hf; inversion Hf; [f_equal; apply Fin.to_nat_inj; assumption|reflexivity].
  - intros (Hp & -> & ->); auto.
Qed.

Lemma set_pool_equ c d p q : owned_equ c d -> tp_equ p q -> owned_equ (set_pool c p) (set_pool d q).
Proof. intros [_ H] Hp; exact (conj Hp H). Qed.

Lemma set_heap_equ c d i m m' :
  owned_equ c d -> m ≈ m' -> owned_equ (set_heap c i m) (set_heap d i m').
Proof.
  intros (Ep & Ea & Eh & Ex & Eb & Ec & El) Hm.
  refine (conj Ep (conj Ea (conj _ (conj Ex (conj Eb (conj Ec El)))))).
  intros j; cbn [set_heap oc_heap]; unfold side_upd; destruct (side_eqb j i); [exact Hm|apply Eh].
Qed.

Lemma emit_cfg_equ c d i p : owned_equ c d -> owned_equ (emit_cfg c i p) (emit_cfg d i p).
Proof.
  intros (Ep & Ea & Eh & Ex & Eb & Ec & El).
  refine (conj Ep (conj Ea (conj Eh (conj Ex (conj Eb (conj _ _)))))); intros j; cbn;
    unfold side_upd; destruct (side_eqb j i); rewrite ?Eb, ?Ec; auto.
Qed.

(** Primitives respect [owned_equ]: same kind and response, equivalent result. *)
Lemma prim_step_equ i c d {Y} (e : sE Y) kind y c1 :
  owned_equ c d -> prim_step i c e = Some (kind, y, c1) ->
  exists d1, prim_step i d e = Some (kind, y, d1) /\ owned_equ c1 d1.
Proof.
  intros E H; pose proof E as (_ & _ & Eh & Ex & Eb & Ec & _).
  destruct (Eh i) as [H1 H2].
  destruct e as [he|[se|we]]; [destruct he as [a|a v|sz|b|a ex de]|destruct se|destruct we as [p]];
    cbn in H |- *.
  - rewrite (H1 a) in H; destruct (fst (oc_heap d i) a); inversion H; subst.
    eexists; split; [reflexivity|exact E].
  - rewrite (H1 a) in H; destruct (fst (oc_heap d i) a); inversion H; subst.
    eexists; split; [reflexivity|]; apply set_heap_equ; [exact E|].
    split; [apply upd_heq, H1|exact H2].
  - discriminate.
  - destruct (managed_free (oc_heap c i) b) as [m1|] eqn:Hf; inversion H; subst.
    destruct (managed_free_peq _ _ _ _ (Eh i) Hf) as (m1' & -> & Hm).
    eexists; split; [reflexivity|]; apply set_heap_equ; assumption.
  - rewrite (H1 a) in H; destruct (fst (oc_heap d i) a) as [cur|]; [|discriminate].
    destruct (Nat.eqb cur ex); inversion H; subst.
    + eexists; split; [reflexivity|]; apply set_heap_equ; [exact E|].
      split; [apply upd_heq, H1|exact H2].
    + eexists; split; [reflexivity|exact E].
  - inversion H; subst; rewrite Ex; eexists; split; [reflexivity|exact E].
  - discriminate.
  - inversion H; subst.
    assert (Hg : global_count c = global_count d) by (unfold global_count; rewrite Eb, !Ec; reflexivity).
    rewrite Hg; eexists; split; [reflexivity|apply emit_cfg_equ, E].
Qed.

Lemma headed_equ t t' u : t ≅ t' -> headed t u -> headed t' u.
Proof. intros E [n H]; exists n; etransitivity; [symmetry; exact E|exact H]. Qed.

Lemma sel_step_equ c d n v w g a c' :
  owned_equ c d -> (forall k, (v $ k) ≅ (w $ k)) -> sel_step c n v g a c' ->
  exists d', sel_step d n w g a d' /\ owned_equ c' d'.
Proof.
  intros E Hp (j & -> & ->); eexists; split; [exists j; split; reflexivity|].
  apply set_pool_equ; [exact E|]; apply tp_equ_mk; auto.
Qed.

Lemma focus_step_equ c d n v w g j a c' :
  owned_equ c d -> (forall k, (v $ k) ≅ (w $ k)) -> focus_step c n v g j a c' ->
  exists d', focus_step d n w g j a d' /\ owned_equ c' d'.
Proof.
  intros E Hp S.
  assert (Hj : forall u, headed (v $ j) u -> headed (w $ j) u) by (intros u; apply headed_equ, Hp).
  assert (Hr : forall x, forall k, ((v @ j := x) $ k) ≅ ((w @ j := x) $ k)).
  { intros x; apply (vector_replace_pointwise (fun x y => x ≅ y)); [intros; apply Hp|reflexivity]. }
  destruct S as [(t & Hh & -> & ->)|[(k & Hh & -> & ->)|[(k & Hh & -> & ->)|
    [(Hh & -> & ->)|(Y & e & k & kind & y & c1 & Hh & Hs & -> & ->)]]]].
  - eexists; split; [left; exists t; split; [apply Hj, Hh|split; reflexivity]|].
    apply set_pool_equ; [exact E|]; apply tp_equ_mk; auto.
  - eexists; split; [right; left; exists k; split; [apply Hj, Hh|split; reflexivity]|].
    apply set_pool_equ; [exact E|]; apply tp_equ_mk; auto.
  - eexists; split; [right; right; left; exists k; split; [apply Hj, Hh|split; reflexivity]|].
    apply set_pool_equ; [exact E|]; apply tp_equ_mk; split; [|auto].
    apply (vector_cons_pointwise (fun x y => x ≅ y)); [reflexivity|apply Hr].
  - eexists; split; [right; right; right; left; split; [apply Hj, Hh|split; reflexivity]|].
    apply set_pool_equ; [exact E|]; apply tp_equ_mk; split; [|auto].
    apply (vector_remove_pointwise (fun x y => x ≅ y)); intros; apply Hp.
  - destruct (prim_step_equ _ _ _ _ _ _ _ E Hs) as (d1 & Hs' & E1).
    eexists; split.
    + right; right; right; right; exists Y, e, k, kind, y, d1.
      split; [apply Hj, Hh|split; [exact Hs'|split; reflexivity]].
    + apply set_pool_equ; [exact E1|]; apply tp_equ_mk; auto.
Qed.

Lemma owned_step_equ c d a c' :
  owned_equ c d -> owned_step c a c' -> exists d', owned_step d a d' /\ owned_equ c' d'.
Proof.
  intros E S; pose proof (proj1 E) as Ep.
  destruct c as [[n v g f] an he cx b co la], d as [[n' w g' f'] an' he' cx' b' co' la'].
  cbn [oc_pool] in Ep; pose proof (tp_equ_size _ _ Ep) as Hn; cbn in Hn; subst n'.
  apply tp_equ_mk in Ep as (Hp & <- & <-).
  unfold owned_step in S |- *; destruct n as [|n]; cbn [oc_pool] in S |- *; [contradiction|].
  destruct f as [j|]; [exact (focus_step_equ _ _ _ _ _ _ _ _ _ E Hp S)|exact (sel_step_equ _ _ _ _ _ _ _ _ E Hp S)].
Qed.

Lemma owned_next_equ c d c' :
  owned_equ c d -> owned_next c c' -> exists d', owned_next d d' /\ owned_equ c' d'.
Proof.
  intros E [a S]; destruct (owned_step_equ _ _ _ _ E S) as (d' & S' & E').
  exists d'; split; [exists a|]; assumption.
Qed.

Lemma tp_slots_project i p : tp_slots (project_pool i p) = proj_slots i p.
Proof.
  unfold tp_slots, project_pool; cbn [tp_threads tp_tags].
  rewrite !Vector.to_list_map, !Vector.to_list_of_list_opp.
  induction (proj_slots i p) as [|[x s] l IH]; cbn; [reflexivity|now rewrite IH].
Qed.

Lemma Forall2_slot_filter i l l' :
  List.Forall2 slot_equ l l' ->
  List.Forall2 slot_equ (List.filter (owned_by i) l) (List.filter (owned_by i) l').
Proof.
  induction 1 as [|x y l l' Hxy _ IH]; cbn; [constructor|].
  assert (owned_by i x = owned_by i y) as -> by (unfold owned_by; rewrite (proj2 Hxy); reflexivity).
  destruct (owned_by i y); [constructor|]; assumption.
Qed.

Lemma Forall2_firstn {A B} (R : A -> B -> Prop) k l l' :
  List.Forall2 R l l' -> List.Forall2 R (List.firstn k l) (List.firstn k l').
Proof.
  intros H; revert k; induction H; intros [|k]; cbn; constructor; auto.
Qed.

Lemma focus_nat_project i p :
  focus_nat (project_pool i p) =
  match tp_focus p with
  | Some j =>
      if side_eqb (tp_tags p $ j) i
      then Some (List.length (List.filter (owned_by i) (List.firstn (fin_nat j) (tp_slots p))))
      else None
  | None => None
  end.
Proof.
  unfold focus_nat, project_pool, proj_focus; cbn [tp_focus].
  destruct (tp_focus p) as [j|]; [|reflexivity].
  destruct (side_eq_dec (tp_tags p $ j) i) as [H|H].
  - rewrite (proj2 (side_eqb_spec _ _) H); cbn; unfold fin_nat at 1; rewrite Fin.to_nat_of_nat.
    reflexivity.
  - destruct (side_eqb (tp_tags p $ j) i) eqn:Hb; [apply side_eqb_spec in Hb; contradiction|reflexivity].
Qed.

Lemma tp_equ_project i p q : tp_equ p q -> tp_equ (project_pool i p) (project_pool i q).
Proof.
  intros Hpq; split.
  - rewrite !tp_slots_project, !proj_slots_filter; apply Forall2_slot_filter, Hpq.
  - rewrite !focus_nat_project; pose proof (proj1 Hpq) as Hs.
    destruct p as [n v g f], q as [n' w g' f'].
    pose proof (tp_equ_size _ _ Hpq) as Hn; cbn in Hn; subst n'.
    apply tp_equ_mk in Hpq as (_ & <- & <-); cbn [tp_focus tp_tags tp_size].
    destruct f as [j|]; [|reflexivity].
    destruct (side_eqb (g $ j) i); [|reflexivity].
    f_equal; apply (List.Forall2_length (R := slot_equ)), Forall2_slot_filter, Forall2_firstn, Hs.
Qed.

Lemma project_equ i c d : owned_equ c d -> owned_equ (project i c) (project i d).
Proof.
  intros (Ep & Ea & Eh & Ex & Eb & Ec & El).
  refine (conj (tp_equ_project _ _ _ Ep) (conj _ (conj _ (conj Ex (conj Eb (conj _ _)))))); intros j;
    cbn [project oc_anchor oc_heap oc_count oc_last]; unfold side_only; destruct (side_eqb j i);
    first [apply peq_refl|reflexivity|auto].
Qed.

Lemma managed_wf_peq m m' : m ≈ m' -> managed_wf m -> managed_wf m'.
Proof.
  destruct m as [h al], m' as [h' al']; intros [H1 H2] [W D]; cbn in *; split; cbn.
  - intros base size Hs; rewrite <- H2 in Hs; destruct (W _ _ Hs) as (Hb & Hz & C).
    split; [exact Hb|split; [exact Hz|]]; intros x Hx; rewrite <- H1; auto.
  - intros b1 n1 b2 n2 E1 E2; rewrite <- H2 in E1, E2; eauto.
Qed.

Lemma support_le_peq m m' r r' : m ≈ m' -> r ≈ r' -> support_le m r -> support_le m' r'.
Proof.
  destruct m as [h al], m' as [h' al'], r as [k bl], r' as [k' bl'].
  intros [H1 H2] [K1 K2] [S1 S2]; cbn in *; split; cbn; intros x Hx.
  - rewrite <- K1; apply S1; rewrite H1; exact Hx.
  - rewrite <- K2; apply S2; rewrite H2; exact Hx.
Qed.

Lemma owned_wf_equ c d : owned_equ c d -> owned_wf c -> owned_wf d.
Proof.
  intros (_ & Ea & Eh & _) (W1 & W2 & A1 & A2 & AD & S1 & S2 & D).
  refine (conj (managed_wf_peq _ _ (Eh Child) W1) (conj (managed_wf_peq _ _ (Eh Parent) W2)
    (conj (managed_wf_peq _ _ (Ea Child) A1) (conj (managed_wf_peq _ _ (Ea Parent) A2)
    (conj (pdef_resp _ _ _ _ (Ea Child) (Ea Parent) AD)
    (conj (support_le_peq _ _ _ _ (Eh Child) (Ea Child) S1)
    (conj (support_le_peq _ _ _ _ (Eh Parent) (Ea Parent) S2)
      (pdef_resp _ _ _ _ (Eh Child) (Eh Parent) D)))))))).
Qed.

(** ** Initial configurations *)

Lemma project_init_child child parent h h' ctx base :
  owned_equ (project Child (init_owned child parent h h' ctx base))
    (init_local Child child h ctx base false).
Proof.
  split; [split|].
  - cbn [project oc_pool]; rewrite tp_slots_project; cbn; apply Forall2_slot_refl.
  - cbn [project oc_pool]; rewrite focus_nat_project; reflexivity.
  - refine (conj _ (conj _ (conj eq_refl (conj eq_refl (conj _ _))))); intros [];
      first [apply peq_refl|reflexivity].
Qed.

Lemma project_init_parent child parent h h' ctx base :
  owned_equ (project Parent (init_owned child parent h h' ctx base))
    (init_local Parent parent h' ctx base true).
Proof.
  split; [split|].
  - cbn [project oc_pool]; rewrite tp_slots_project; cbn; apply Forall2_slot_refl.
  - cbn [project oc_pool]; rewrite focus_nat_project; reflexivity.
  - refine (conj _ (conj _ (conj eq_refl (conj eq_refl (conj _ _))))); intros [];
      first [apply peq_refl|reflexivity].
Qed.

(** An unfocused singleton's only action selects it. *)
Lemma init_local_select i p h ctx base a d :
  owned_step (init_local i p h ctx base false) a d <->
    a = act i OASelect /\ d = init_local i p h ctx base true.
Proof.
  unfold owned_step, init_local; cbn [oc_pool]; unfold sel_step; split.
  - intros (j & -> & ->); dependent destruction j; [split; reflexivity|inversion j].
  - intros [-> ->]; exists Fin.F1; split; reflexivity.
Qed.

Lemma support_le_refl m : support_le m m.
Proof. split; auto. Qed.

Lemma init_owned_wf child parent h h' ctx base :
  managed_wf h -> managed_wf h' -> h # h' -> owned_wf (init_owned child parent h h' ctx base).
Proof.
  intros W W' D.
  exact (conj W (conj W' (conj W (conj W' (conj D (conj (support_le_refl h)
    (conj (support_le_refl h') D))))))).
Qed.

(** ** One-step facts *)

Lemma prim_step_facts i c {Y} (e : sE Y) kind y c1 :
  prim_step i c e = Some (kind, y, c1) ->
  kind <> OASelect /\ oc_pool c1 = oc_pool c /\ oc_anchor c1 = oc_anchor c /\
  oc_ctx c1 = oc_ctx c /\ oc_base c1 = oc_base c.
Proof.
  destruct e as [he|[se|we]]; [destruct he|destruct se|destruct we]; cbn; intro H;
    repeat match type of H with context [match ?x with _ => _ end] => destruct x end;
    inversion H; subst; repeat split; discriminate.
Qed.

Lemma support_le_trans m r s : support_le m r -> support_le r s -> support_le m s.
Proof. intros [A1 A2] [B1 B2]; split; auto. Qed.

Lemma support_le_disj m m0 m1 : support_le m m0 -> m0 # m1 -> m # m1.
Proof.
  destruct m as [h al], m0 as [h0 al0], m1 as [h1 al1].
  intros [S1 S2] [D1 D2]; cbn in *; split; cbn; intros x.
  - destruct (D1 x) as [Hx|Hx]; [left|right; exact Hx].
    destruct (h x) eqn:E; [|reflexivity]; exfalso; apply (S1 x); [rewrite E; discriminate|exact Hx].
  - destruct (D2 x) as [Hx|Hx]; [left|right; exact Hx].
    destruct (al x) eqn:E; [|reflexivity]; exfalso; apply (S2 x); [rewrite E; discriminate|exact Hx].
Qed.

Lemma owned_wf_heap c i : owned_wf c -> managed_wf (oc_heap c i).
Proof. intros (W1 & W2 & _); destruct i; assumption. Qed.

Lemma set_heap_wf c i m :
  owned_wf c -> managed_wf m -> support_le m (oc_heap c i) -> owned_wf (set_heap c i m).
Proof.
  intros (W1 & W2 & A1 & A2 & AD & S1 & S2 & D) Wm Sm; destruct i.
  - exact (conj Wm (conj W2 (conj A1 (conj A2 (conj AD (conj (support_le_trans _ _ _ Sm S1)
      (conj S2 (support_le_disj _ _ _ Sm D)))))))).
  - exact (conj W1 (conj Wm (conj A1 (conj A2 (conj AD (conj S1 (conj (support_le_trans _ _ _ Sm S2)
      (pdef_comm _ _ (support_le_disj _ _ _ Sm (pdef_comm _ _ D)))))))))).
Qed.

Lemma write_wf_support (m : ManagedHeap) a v v0 :
  managed_wf m -> fst m a = Some v0 ->
  managed_wf (upd (fst m) a v, snd m) /\ support_le (upd (fst m) a v, snd m) m.
Proof.
  destruct m as [h al]; cbn; intros W Ha; split; [apply managed_write_preserves_wf, W|].
  split; cbn; [|auto]; intros x Hx.
  exact (proj1 (upd_dom h a v x ltac:(rewrite Ha; discriminate)) Hx).
Qed.

Lemma free_wf_support (m m' : ManagedHeap) b :
  managed_wf m -> managed_free m b = Some m' -> managed_wf m' /\ support_le m' m.
Proof.
  intros W Hf; split; [eapply managed_free_preserves_wf; eassumption|].
  destruct m as [h al]; unfold managed_free in Hf; cbn [fst snd] in Hf.
  destruct (Nat.eqb b 0); [injection Hf as <-; apply support_le_refl|].
  destruct (al b) as [[|n]|]; try discriminate; injection Hf as <-.
  split; cbn; intros x Hx; unfold hfree_block, hfree in Hx;
    repeat match type of Hx with context [if ?c then _ else _] => destruct c end;
    first [exact Hx|exfalso; apply Hx; reflexivity].
Qed.

Lemma prim_step_wf i c {Y} (e : sE Y) kind y c1 :
  owned_wf c -> prim_step i c e = Some (kind, y, c1) -> owned_wf c1.
Proof.
  intros W H.
  destruct e as [he|[se|we]]; [destruct he as [a|a v|sz|b|a ex de]|destruct se|destruct we as [p]];
    cbn in H.
  - destruct (fst (oc_heap c i) a); inversion H; subst; exact W.
  - destruct (fst (oc_heap c i) a) eqn:Ha; inversion H; subst.
    destruct (write_wf_support _ a v _ (owned_wf_heap _ i W) Ha) as [Wm Sm].
    apply set_heap_wf; assumption.
  - discriminate.
  - destruct (managed_free (oc_heap c i) b) eqn:Hf; inversion H; subst.
    destruct (free_wf_support _ _ _ (owned_wf_heap _ i W) Hf) as [Wm Sm].
    apply set_heap_wf; assumption.
  - destruct (fst (oc_heap c i) a) eqn:Ha; [|discriminate].
    destruct (Nat.eqb n ex); inversion H; subst; [|exact W].
    destruct (write_wf_support _ a de _ (owned_wf_heap _ i W) Ha) as [Wm Sm].
    apply set_heap_wf; assumption.
  - inversion H; subst; exact W.
  - discriminate.
  - inversion H; subst; exact W.
Qed.

(** Case analysis of one step on a destructed configuration. *)
Local Ltac step_inv S :=
  lazymatch type of S with
  | owned_step ?c _ _ =>
      destruct c as [[n v g f] an he cx b co la]; unfold owned_step in S;
      destruct n as [|n]; cbn [oc_pool] in S; [contradiction|];
      destruct f as [j|];
      [destruct S as [(t & Hh & -> & ->)|[(k & Hh & -> & ->)|[(k & Hh & -> & ->)|
         [(Hh & -> & ->)|(Y & e & k & kind & y & c1 & Hh & Hs & -> & ->)]]]]
      |destruct S as (j & -> & ->)]
  end.

(** Selection changes only the focus. *)
Lemma owned_step_select_only c a c' :
  owned_step c a c' -> action_kind a = OASelect ->
  oc_heap c' = oc_heap c /\ oc_anchor c' = oc_anchor c /\ oc_ctx c' = oc_ctx c /\
  oc_base c' = oc_base c /\ oc_count c' = oc_count c /\ oc_last c' = oc_last c /\
  tp_size (oc_pool c') = tp_size (oc_pool c).
Proof.
  intros S K; step_inv S; try discriminate K.
  - cbn in K; subst kind; destruct (prim_step_facts _ _ _ _ _ _ Hs) as [N _]; contradiction.
  - repeat split.
Qed.

Lemma owned_step_wf c a c' : owned_wf c -> owned_step c a c' -> owned_wf c'.
Proof. intros W S; step_inv S; try exact W; exact (prim_step_wf _ _ _ _ _ _ W Hs). Qed.

(** Anchors, context and base never change. *)
Lemma owned_step_frozen c a c' :
  owned_step c a c' -> oc_anchor c' = oc_anchor c /\ oc_ctx c' = oc_ctx c /\ oc_base c' = oc_base c.
Proof.
  intros S; step_inv S; try (repeat split; fail).
  destruct (prim_step_facts _ _ _ _ _ _ Hs) as (_ & _ & A & X & B); cbn; rewrite A, X, B; repeat split.
Qed.

(** Only the final return of a singleton pool reaches the empty pool. *)
Lemma owned_step_terminal c a c' :
  owned_step c a c' -> tp_size (oc_pool c') = 0 ->
  action_kind a = OAReturn /\ tp_size (oc_pool c) = 1.
Proof. intros S Z; step_inv S; cbn in Z; try discriminate Z; subst n; split; reflexivity. Qed.

Lemma owned_step_empty c a c' : tp_size (oc_pool c) = 0 -> ~ owned_step c a c'.
Proof.
  intros Z S; destruct c as [[n v g f] an he cx b co la]; cbn in Z; subst n.
  unfold owned_step in S; exact S.
Qed.

(** ** Heads of a focused slot

    These characterize [focus_step] once the focused thread is known up to
    guards; successors are exact up to [≅] continuations. *)

(** A head that is not itself a guard. *)
Definition unguarded (u : thread sE Bn) : Prop := forall w, ~ u ≅ Guard w.

(** Finite guard prefixes before unguarded heads are unique. *)
Lemma guards_unique m m' (u u' : thread sE Bn) :
  guards m u ≅ guards m' u' -> unguarded u -> unguarded u' -> u ≅ u'.
Proof.
  intros H Hu Hu'; destruct (guards_cancel _ _ _ _ H) as [(d & Hd & _)|(d & Hd & _)].
  - destruct d; [exact Hd|exfalso; exact (Hu _ Hd)].
  - destruct d; [symmetry; exact Hd|exfalso; exact (Hu' _ Hd)].
Qed.

Lemma headed_unique t u u' : headed t u -> headed t u' -> unguarded u -> unguarded u' -> u ≅ u'.
Proof.
  intros [m H] [m' H']; apply (guards_unique m m').
  etransitivity; [symmetry; exact H|exact H'].
Qed.

Local Ltac unguarded_tac := let w := fresh "w" in let H := fresh "H" in
  intros w H; step in H; cbn in H; inversion H.

(** Two distinct heads cannot be equivalent; [unit] and [bool] differ by
    cardinality. *)
Local Ltac clash Hu :=
  first
  [ solve [step in Hu; cbn in Hu; inversion Hu]
  | let HY := fresh "HY" in let Hb := fresh "Hb" in
    pose proof (equ_vis_invT _ _ _ _ Hu) as HY;
    first [ assert (Hb : forall x y : bool, x = y)
              by (first [rewrite <- HY|rewrite HY]; intros [] []; reflexivity);
            discriminate (Hb true false)
          | subst; apply equ_vis_invE in Hu as [He _]; discriminate He ] ].

Local Ltac focus_uniq H0 :=
  intros [(t & Hh & Ha & Hc)|[(k & Hh & Ha & Hc)|[(k & Hh & Ha & Hc)|
    [(Hh & Ha & Hc)|(Y' & e & k & kind & y & c1 & Hh & Hs & Ha & Hc)]]]];
  pose proof (headed_unique _ _ _ H0 Hh ltac:(unguarded_tac) ltac:(unguarded_tac)) as Hu;
  try clash Hu.

Lemma focus_step_head_step c n v g j t0 m a c' :
  (v $ j) ≅ guards m (Step t0) ->
  focus_step c n v g j a c' <->
    exists t, t ≅ t0 /\ a = act (g $ j) OAStep /\
      c' = set_pool c (mk_pool (S n) (v @ j := t) g (Some j)).
Proof.
  intros Hv; assert (H0 : headed (v $ j) (Step t0)) by (exists m; exact Hv); split.
  - focus_uniq H0.
    exists t; split; [symmetry; apply equ_step_inv, Hu|split; assumption].
  - intros (t & Ht & -> & ->); left; exists t; split; [|split; reflexivity].
    exists m; etransitivity; [exact Hv|]; apply guards_equ; step; constructor; symmetry; exact Ht.
Qed.

Lemma focus_step_head_yield c n v g j k0 m a c' :
  (v $ j) ≅ guards m (Vis (inl1 Yield : CEff unit) k0) ->
  focus_step c n v g j a c' <->
    exists k, (forall x, k x ≅ k0 x) /\ a = act (g $ j) OAYield /\
      c' = set_pool c (mk_pool (S n) (v @ j := k tt) g None).
Proof.
  intros Hv; assert (H0 : headed (v $ j) (Vis (inl1 Yield : CEff unit) k0)) by (exists m; exact Hv).
  split.
  - focus_uniq H0.
    apply equ_vis_invE in Hu as [_ Hk].
    exists k; split; [intros x; symmetry; apply Hk|split; assumption].
  - intros (k & Hk & -> & ->); right; left; exists k; split; [|split; reflexivity].
    exists m; etransitivity; [exact Hv|]; apply guards_equ; step; constructor; intros x.
    symmetry; apply Hk.
Qed.

Lemma focus_step_head_fork c n v g j k0 m a c' :
  (v $ j) ≅ guards m (Vis (inr1 (inl1 Fork) : CEff bool) k0) ->
  focus_step c n v g j a c' <->
    exists k, (forall x, k x ≅ k0 x) /\ a = act (g $ j) OAFork /\
      c' = set_pool c (mk_pool (S (S n)) (k true :: (v @ j := k false)) ((g $ j) :: g)
                        (Some (Fin.FS j))).
Proof.
  intros Hv; assert (H0 : headed (v $ j) (Vis (inr1 (inl1 Fork) : CEff bool) k0))
    by (exists m; exact Hv).
  split.
  - focus_uniq H0.
    apply equ_vis_invE in Hu as [_ Hk].
    exists k; split; [intros x; symmetry; apply Hk|split; assumption].
  - intros (k & Hk & -> & ->); right; right; left; exists k; split; [|split; reflexivity].
    exists m; etransitivity; [exact Hv|]; apply guards_equ; step; constructor; intros x.
    symmetry; apply Hk.
Qed.

Lemma focus_step_head_ret c n v g j m a c' :
  (v $ j) ≅ guards m (Ret tt) ->
  focus_step c n v g j a c' <->
    a = act (g $ j) OAReturn /\ c' = set_pool c (mk_pool n (v -- j) (g -- j) None).
Proof.
  intros Hv; assert (H0 : headed (v $ j) (Ret tt)) by (exists m; exact Hv); split.
  - focus_uniq H0; split; assumption.
  - intros [-> ->]; right; right; right; left; split; [exists m; exact Hv|split; reflexivity].
Qed.

Lemma focus_step_head_prim c n v g j {Y} (e0 : sE Y) k0 m a c' :
  (v $ j) ≅ guards m (Vis (inr1 (inr1 e0) : CEff Y) k0) ->
  focus_step c n v g j a c' <->
    exists k kind y c1, (forall x, k x ≅ k0 x) /\
      prim_step (g $ j) c e0 = Some (kind, y, c1) /\ a = act (g $ j) kind /\
      c' = set_pool c1 (mk_pool (S n) (v @ j := k y) g (Some j)).
Proof.
  intros Hv; assert (H0 : headed (v $ j) (Vis (inr1 (inr1 e0) : CEff Y) k0)) by (exists m; exact Hv).
  split.
  - focus_uniq H0.
    pose proof (equ_vis_invT _ _ _ _ Hu) as HY; subst Y'.
    apply equ_vis_invE in Hu as [He Hk]; injection He as ->.
    exists k, kind, y, c1; split; [intros x; symmetry; apply Hk|split; [exact Hs|split; assumption]].
  - intros (k & kind & y & c1 & Hk & Hs & -> & ->); right; right; right; right.
    exists Y, e0, k, kind, y, c1; split; [|split; [exact Hs|split; reflexivity]].
    exists m; etransitivity; [exact Hv|]; apply guards_equ; step; constructor; intros x.
    symmetry; apply Hk.
Qed.

Lemma focus_step_head_stuck c n v g j m a c' :
  (v $ j) ≅ guards m Stuck -> ~ focus_step c n v g j a c'.
Proof.
  intros Hv; assert (H0 : headed (v $ j) Stuck) by (exists m; exact Hv).
  focus_uniq H0.
Qed.

(** * Projection of the owned action machine onto one lineage.

    Own actions are local actions of the projection; foreign actions leave it
    unchanged up to [owned_equ].  [weak_next] is sound and conditionally
    complete for the projected clock. *)

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.
Local Open Scope list_scope.

(** ** Ordered slot views of the vector pool

    Lists below are only extensional views.  All updates and all transitions
    use the original vectors and finite indices. *)

Local Abbreviation slot := (thread sE Bn * side)%type.

Definition cfg_slots (c : OwnedCfg) : list slot := tp_slots (oc_pool c).
Definition cfg_focus (c : OwnedCfg) : option nat := focus_nat (oc_pool c).

Definition rank {A} (p : A -> bool) (l : list A) (k : nat) : nat :=
  length (filter p (firstn k l)).

Lemma fin_nat_FS {n} (j : Fin.t n) : fin_nat (Fin.FS j) = S (fin_nat j).
Proof. unfold fin_nat; cbn; destruct (Fin.to_nat j); reflexivity. Qed.

Lemma fin_nat_of_nat {n k} (H : k < n) : fin_nat (Fin.of_nat_lt H) = k.
Proof. unfold fin_nat; now rewrite Fin.to_nat_of_nat. Qed.

Lemma fin_nat_injective {n} (j k : Fin.t n) : fin_nat j = fin_nat k -> j = k.
Proof. apply Fin.to_nat_inj. Qed.

Lemma owned_by_other i s (t : thread sE Bn) : s <> i -> owned_by i (t, s) = false.
Proof. destruct i, s; cbn; congruence. Qed.

Lemma owned_by_true i x : owned_by i x = true -> snd x = i.
Proof. apply side_eqb_spec. Qed.

Lemma nth_error_rank {A} (p : A -> bool) l k y :
  nth_error l k = Some y -> p y = true ->
  nth_error (filter p l) (rank p l k) = Some y.
Proof.
  unfold rank; revert k; induction l as [|a l IH]; intros [|k] H Hy; cbn in *; try discriminate.
  - injection H as ->. now rewrite Hy.
  - destruct (p a); cbn; apply IH; auto.
Qed.

Lemma rank_inv {A} (p : A -> bool) l r y : nth_error (filter p l) r = Some y ->
  exists k, nth_error l k = Some y /\ p y = true /\ rank p l k = r.
Proof.
  unfold rank; revert r; induction l as [|a l IH]; intros r H; cbn in *.
  - destruct r; discriminate.
  - destruct (p a) eqn:Ha.
    + destruct r as [|r]; cbn in H.
      * injection H as <-. exists 0; cbn; auto.
      * destruct (IH r H) as (k & Hk & Hy & Hr).
        exists (S k); cbn; rewrite Ha; cbn; auto.
    + destruct (IH r H) as (k & Hk & Hy & Hr).
      exists (S k); cbn; rewrite Ha; auto.
Qed.

Lemma cfg_slots_project i c : cfg_slots (project i c) = filter (owned_by i) (cfg_slots c).
Proof. apply (eq_trans (tp_slots_project i (oc_pool c))), proj_slots_filter. Qed.

Lemma list_cut {A} (l : list A) k x : nth_error l k = Some x ->
  exists pre post, l = pre ++ x :: post /\ length pre = k.
Proof.
  revert k; induction l as [|a l IH]; intros [|k] H; cbn in H; try discriminate.
  - injection H as <-; exists List.nil, l; auto.
  - destruct (IH k H) as (pre & post & -> & Hlen).
    exists (a :: pre), post; cbn; auto.
Qed.

Lemma firstn_cut {A} (pre post : list A) : firstn (length pre) (pre ++ post) = pre.
Proof. induction pre; cbn; congruence. Qed.


Lemma pool_cut p (j : Fin.t (tp_size p)) :
  exists pre post, tp_slots p = pre ++ (tp_threads p $ j, tp_tags p $ j) :: post /\
    length pre = fin_nat j.
Proof. apply list_cut, tp_slots_nth_error. Qed.

(** The only replacement/removal equations are equations of vector views. *)
Lemma slots_replace_view n (v : pool sE Bn n) g j f f' t pre old post :
  tp_slots (mk_pool n v g f) = pre ++ old :: post -> fin_nat j = length pre ->
  tp_slots (mk_pool n (v @ j := t) g f') = pre ++ (t, snd old) :: post.
Proof.
  revert g j f f' t pre old post; induction v as [|a n v IH];
    intros g j f f' t pre old post H Hlen; [inversion j|];
    dependent destruction g; dependent destruction j.
  - destruct pre as [|b pre]; cbn in Hlen; [|lia].
    unfold tp_slots in H |- *; cbn [mk_pool tp_threads tp_tags] in H |- *.
    rewrite ?Vector.to_list_cons in H |- *; cbn in H |- *.
    injection H as <- <-; reflexivity.
  - rewrite fin_nat_FS in Hlen; destruct pre as [|b pre]; cbn in Hlen; [lia|].
    unfold tp_slots in H |- *; cbn [mk_pool tp_threads tp_tags] in H |- *.
    rewrite ?Vector.to_list_cons in H |- *; cbn in H |- *.
    injection H as <- H; f_equal.
    apply (IH g j None None t pre old post); [exact H|lia].
Qed.

Lemma slots_remove_view n (v : pool sE Bn (S n)) g j f f' pre old post :
  tp_slots (mk_pool (S n) v g f) = pre ++ old :: post -> fin_nat j = length pre ->
  tp_slots (mk_pool n (v -- j) (g -- j) f') = pre ++ post.
Proof.
  revert v g j f f' pre old post; induction n as [|n IH];
    intros v g j f f' pre old post H Hlen;
    dependent destruction v; dependent destruction g; dependent destruction j.
  - destruct pre as [|b pre]; cbn in Hlen; [|lia].
    rewrite !vector_remove_head; unfold tp_slots in H |- *;
      cbn [mk_pool tp_threads tp_tags] in H |- *.
    rewrite ?Vector.to_list_cons in H; cbn in H.
    dependent destruction v; dependent destruction g; cbn in H |- *.
    injection H as _ <-; reflexivity.
  - inversion j.
  - destruct pre as [|b pre]; cbn in Hlen; [|lia].
    rewrite !vector_remove_head; unfold tp_slots in H |- *;
      cbn [mk_pool tp_threads tp_tags] in H |- *.
    rewrite ?Vector.to_list_cons in H; cbn in H; now injection H as _ <-.
  - rewrite fin_nat_FS in Hlen; destruct pre as [|b pre]; cbn in Hlen; [lia|].
    rewrite !vector_remove_tail; unfold tp_slots in H |- *;
      cbn [mk_pool tp_threads tp_tags] in H |- *.
    rewrite ?Vector.to_list_cons in H |- *; cbn in H |- *.
    injection H as <- H; f_equal.
    apply (IH v g j None None pre old post); [exact H|lia].
Qed.

Lemma slots_cons n (v : pool sE Bn n) g x s f f' :
  tp_slots (mk_pool (S n) (x :: v)%vector (s :: g)%vector f) =
  (x,s) :: tp_slots (mk_pool n v g f').
Proof. unfold tp_slots; cbn [mk_pool tp_threads tp_tags]; now rewrite ?Vector.to_list_cons. Qed.

(** Every filtered rank has its original finite index, constructively. *)
Lemma project_index i p (j : Fin.t (tp_size p)) : (tp_tags p $ j) = i ->
  exists r : Fin.t (tp_size (project_pool i p)),
    fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) /\
    (tp_threads (project_pool i p) $ r) = (tp_threads p $ j) /\
    (tp_tags (project_pool i p) $ r) = i.
Proof.
  intro Hj; exists (Fin.of_nat_lt (proj_pos_lt i p j Hj)).
  split; [apply fin_nat_of_nat|].
  pose proof (tp_slots_nth_error (project_pool i p)
    (Fin.of_nat_lt (proj_pos_lt i p j Hj))) as Hn.
  rewrite tp_slots_project in Hn.
  rewrite (proj_slots_filter i p) in Hn at 1.
  rewrite fin_nat_of_nat in Hn.
  pose proof (nth_error_rank (owned_by i) _ _ _ (tp_slots_nth_error p j)) as Hr.
  rewrite Hj in Hr; specialize (Hr (owned_by_self i _)); unfold rank in Hr.
  rewrite Hr in Hn; injection Hn as Ht Hg; split; symmetry; assumption.
Qed.

Lemma project_index_inv i p (r : Fin.t (tp_size (project_pool i p))) :
  exists j : Fin.t (tp_size p),
    (tp_tags p $ j) = i /\
    fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) /\
    (tp_threads (project_pool i p) $ r) = (tp_threads p $ j) /\
    (tp_tags (project_pool i p) $ r) = i.
Proof.
  pose proof (tp_slots_nth_error (project_pool i p) r) as Hr.
  rewrite tp_slots_project, proj_slots_filter in Hr.
  destruct (rank_inv _ _ _ _ Hr) as (k & Hk & Ho & Hrank).
  assert (Hlt : k < tp_size p).
  { rewrite <- tp_slots_length; apply nth_error_Some; congruence. }
  exists (Fin.of_nat_lt Hlt); rewrite fin_nat_of_nat.
  pose proof (tp_slots_nth_error p (Fin.of_nat_lt Hlt)) as Hn.
  rewrite fin_nat_of_nat, Hk in Hn; injection Hn as Ht Hs.
  apply owned_by_true in Ho; change ((tp_tags (project_pool i p) $ r) = i) in Ho.
  split.
  - etransitivity; [symmetry; eassumption|exact Ho].
  - split; [symmetry; exact Hrank|split; assumption].
Qed.

Lemma project_focus_owned i p (j : Fin.t (tp_size p)) r :
  tp_focus p = Some j -> (tp_tags p $ j) = i ->
  fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) ->
  tp_focus (project_pool i p) = Some r.
Proof.
  intros Hf Hj Hr; pose proof (focus_nat_project i p) as H.
  rewrite Hf, Hj, (proj2 (side_eqb_spec i i) eq_refl) in H.
  unfold focus_nat in H; destruct (tp_focus (project_pool i p)) as [r'|]; [|discriminate].
  change (Some (fin_nat r') = Some (rank (owned_by i) (tp_slots p) (fin_nat j))) in H.
  injection H as Hnat; f_equal; apply fin_nat_injective.
  exact (eq_trans Hnat (eq_sym Hr)).
Qed.

Lemma project_focus_foreign i p (j : Fin.t (tp_size p)) :
  tp_focus p = Some j -> (tp_tags p $ j) <> i -> tp_focus (project_pool i p) = None.
Proof.
  intros Hf Hj; unfold project_pool, proj_focus; cbn [tp_focus]; rewrite Hf.
  destruct (side_eq_dec (tp_tags p $ j) i); [contradiction|reflexivity].
Qed.

Lemma project_focus_none i p : tp_focus p = None -> tp_focus (project_pool i p) = None.
Proof. unfold project_pool, proj_focus; cbn [tp_focus]; now intros ->. Qed.

Lemma tp_equ_views p q : tp_slots p = tp_slots q -> focus_nat p = focus_nat q -> tp_equ p q.
Proof.
  intros Hs Hf; split; [rewrite Hs; apply Forall2_slot_refl|exact Hf].
Qed.

(** Filtering commutes with the existing vector operations.  The selected
    projected index is its finite ordered rank, not a second scheduler slot. *)
Lemma project_replace_equ i n m (v : pool sE Bn n) g (w : pool sE Bn m) h j r t (focused : bool) :
  tp_slots (mk_pool m w h None) = filter (owned_by i) (tp_slots (mk_pool n v g None)) ->
  (g $ j) = i -> fin_nat r = rank (owned_by i) (tp_slots (mk_pool n v g None)) (fin_nat j) ->
  tp_equ
    (project_pool i (mk_pool n (v @ j := t) g (if focused then Some j else None)))
    (mk_pool m (w @ r := t) h (if focused then Some r else None)).
Proof.
  intros Hq Hj Hr; destruct (pool_cut (mk_pool n v g None) j) as (pre & post & Hcut & Hlen).
  cbn [mk_pool tp_size tp_threads tp_tags] in Hcut.
  assert (Hr' : fin_nat r = length (filter (owned_by i) pre)).
  { rewrite Hr, Hcut.
    transitivity (rank (owned_by i) (pre ++ (v $ j, g $ j) :: post) (length pre)).
    - f_equal; symmetry; exact Hlen.
    - unfold rank; now rewrite firstn_cut. }
  assert (Hqcut : tp_slots (mk_pool m w h None) =
    filter (owned_by i) pre ++ (v $ j, i) :: filter (owned_by i) post).
  { rewrite Hq, Hcut, filter_app; cbn [filter]; now rewrite Hj, owned_by_self. }
  pose proof (slots_replace_view n v g j None None t pre (v $ j,g $ j) post Hcut (eq_sym Hlen)) as Hu.
  pose proof (slots_replace_view m w h r None None t _ _ _ Hqcut Hr') as Hu'.
  apply tp_equ_views.
  - rewrite tp_slots_project, proj_slots_filter.
    change (filter (owned_by i) (tp_slots (mk_pool n (v @ j := t) g None)) =
      tp_slots (mk_pool m (w @ r := t) h None)).
    rewrite Hu, Hu', filter_app; cbn [filter snd]; now rewrite Hj, owned_by_self.
  - rewrite focus_nat_project; destruct focused; cbn [mk_pool tp_focus tp_tags focus_nat].
    + assert (Heq : side_eqb (g $ j) i = true) by (apply side_eqb_spec; exact Hj).
      rewrite Heq at 1.
      change (Some (length (filter (owned_by i) (firstn (fin_nat j)
        (tp_slots (mk_pool n (v @ j := t) g None))))) = Some (fin_nat r)).
      f_equal.
      rewrite Hu; rewrite <- Hlen at 1.
      rewrite firstn_cut; symmetry; exact Hr'.
    + reflexivity.
Qed.

Lemma project_remove_equ i n m (v : pool sE Bn (S n)) g (w : pool sE Bn (S m)) h j r :
  tp_slots (mk_pool (S m) w h None) = filter (owned_by i) (tp_slots (mk_pool (S n) v g None)) ->
  (g $ j) = i -> fin_nat r = rank (owned_by i) (tp_slots (mk_pool (S n) v g None)) (fin_nat j) ->
  tp_equ (project_pool i (mk_pool n (v -- j) (g -- j) None))
    (mk_pool m (w -- r) (h -- r) None).
Proof.
  intros Hq Hj Hr; destruct (pool_cut (mk_pool (S n) v g None) j) as (pre & post & Hcut & Hlen).
  cbn [mk_pool tp_size tp_threads tp_tags] in Hcut.
  assert (Hr' : fin_nat r = length (filter (owned_by i) pre)).
  { rewrite Hr, Hcut.
    transitivity (rank (owned_by i) (pre ++ (v $ j, g $ j) :: post) (length pre)).
    - f_equal; symmetry; exact Hlen.
    - unfold rank; now rewrite firstn_cut. }
  assert (Hqcut : tp_slots (mk_pool (S m) w h None) =
    filter (owned_by i) pre ++ (v $ j,i) :: filter (owned_by i) post).
  { rewrite Hq, Hcut, filter_app; cbn [filter]; now rewrite Hj, owned_by_self. }
  apply tp_equ_views; [|reflexivity].
  rewrite tp_slots_project, proj_slots_filter.
  rewrite (slots_remove_view n v g j None None pre _ post Hcut (eq_sym Hlen)),
    (slots_remove_view m w h r None None _ _ _ Hqcut Hr'), filter_app; reflexivity.
Qed.

Lemma project_fork_equ i n m (v : pool sE Bn (S n)) g (w : pool sE Bn (S m)) h j r x y :
  tp_slots (mk_pool (S m) w h None) = filter (owned_by i) (tp_slots (mk_pool (S n) v g None)) ->
  (g $ j) = i -> (h $ r) = i ->
  fin_nat r = rank (owned_by i) (tp_slots (mk_pool (S n) v g None)) (fin_nat j) ->
  tp_equ
    (project_pool i (mk_pool (S (S n)) (x :: (v @ j := y))%vector ((g $ j) :: g)%vector (Some (Fin.FS j))))
    (mk_pool (S (S m)) (x :: (w @ r := y))%vector ((h $ r) :: h)%vector (Some (Fin.FS r))).
Proof.
  intros Hq Hj Hh Hr.
  pose proof (project_replace_equ i _ _ v g w h j r y true Hq Hj Hr) as [Hu _].
  destruct (pool_cut (mk_pool (S n) v g None) j) as (pre & post & Hcut & Hlen).
  cbn [mk_pool tp_size tp_threads tp_tags] in Hcut.
  pose proof (slots_replace_view _ v g j None None y pre _ post Hcut (eq_sym Hlen)) as Hupd.
  split.
  - rewrite tp_slots_project, proj_slots_filter, (slots_cons _ _ _ _ _ _ None),
      (slots_cons _ _ _ _ _ _ None), Hj, Hh; cbn [filter]; rewrite owned_by_self.
    constructor; [split; reflexivity|].
    rewrite tp_slots_project, proj_slots_filter in Hu; exact Hu.
  - rewrite focus_nat_project; cbn [tp_focus tp_tags mk_pool focus_nat].
    rewrite Hj, (slots_cons _ _ _ _ _ _ None), Hupd, Hj.
    change ((if side_eqb (g $ j) i then
      Some (length (filter (owned_by i)
        (firstn (fin_nat (Fin.FS j)) ((x, i) :: pre ++ (y, i) :: post))))
      else None) = Some (fin_nat (Fin.FS r))).
    assert (Heq : side_eqb (g $ j) i = true) by (apply side_eqb_spec; exact Hj).
    rewrite Heq at 1; rewrite (fin_nat_FS j) at 1; rewrite (fin_nat_FS r) at 1.
    cbn [firstn filter]; rewrite owned_by_self at 1; cbn [length]; f_equal; f_equal.
    rewrite <- Hlen at 1; rewrite firstn_cut; symmetry; unfold rank in Hr.
    rewrite Hcut in Hr; rewrite <- Hlen in Hr at 1; rewrite firstn_cut in Hr; exact Hr.
Qed.

(** Pool-free fields agree pointwise. *)
Definition fields_eq (c d : OwnedCfg) : Prop :=
  (forall j, oc_anchor c j = oc_anchor d j) /\ (forall j, oc_heap c j = oc_heap d j) /\
  oc_ctx c = oc_ctx d /\ oc_base c = oc_base d /\
  (forall j, oc_count c j = oc_count d j) /\ (forall j, oc_last c j = oc_last d j).

Lemma fields_eq_refl c : fields_eq c c.
Proof. repeat split. Qed.

Lemma fields_eq_sym c d : fields_eq c d -> fields_eq d c.
Proof. intros (?&?&?&?&?&?); repeat split; congruence. Qed.

Lemma fields_eq_trans c d e : fields_eq c d -> fields_eq d e -> fields_eq c e.
Proof. intros (?&?&?&?&?&?) (?&?&?&?&?&?); repeat split; congruence. Qed.

Lemma fields_eq_project i c d : fields_eq c d -> fields_eq (project i c) (project i d).
Proof.
  intros (Ha&Hh&?&?&Hc&Hl); unfold project, side_only; repeat split; cbn; auto;
    intro j; destruct (side_eqb j i); auto.
Qed.

Lemma owned_equ_pool_fields c d :
  tp_equ (oc_pool c) (oc_pool d) -> fields_eq c d -> owned_equ c d.
Proof.
  intros Hp (Ha&Hh&?&?&?&?); split; [exact Hp|].
  split; [intro j; rewrite Ha; apply peq_refl|].
  split; [intro j; rewrite Hh; apply peq_refl|]; auto.
Qed.

Lemma owned_equ_intro c d :
  cfg_slots c = cfg_slots d -> cfg_focus c = cfg_focus d -> fields_eq c d -> owned_equ c d.
Proof.
  intros Hs Hf Hfields; apply owned_equ_pool_fields; [apply tp_equ_views; assumption|exact Hfields].
Qed.

Lemma project_set_pool i c p :
  project i (set_pool c p) = set_pool (project i c) (project_pool i p).
Proof. reflexivity. Qed.

Lemma projection_slots i p n w h f :
  project_pool i p = mk_pool n w h f ->
  tp_slots (mk_pool n w h None) = filter (owned_by i) (tp_slots p).
Proof. intro H; rewrite <- (proj_slots_filter i p), <- (tp_slots_project i p), H; reflexivity. Qed.

Lemma projection_focus_none i p :
  tp_focus p = None -> focus_nat (project_pool i p) = None.
Proof. intro H; unfold focus_nat; now rewrite (project_focus_none i p H). Qed.

Lemma project_action_owner i c a : owner (project_action i c a) = owner a.
Proof. unfold project_action; now destruct (action_kind a). Qed.

Lemma project_focused_index i p (j : Fin.t (tp_size p)) :
  tp_focus p = Some j -> (tp_tags p $ j) = i ->
  exists r : Fin.t (tp_size (project_pool i p)),
    fin_nat r = rank (owned_by i) (tp_slots p) (fin_nat j) /\
    (tp_threads (project_pool i p) $ r) = (tp_threads p $ j) /\
    (tp_tags (project_pool i p) $ r) = i /\ tp_focus (project_pool i p) = Some r.
Proof.
  intros Hf Hj; destruct (project_index i p j Hj) as (r & Hr & Ht & Hg).
  exists r; repeat split; auto; eapply project_focus_owned; eauto.
Qed.

Lemma project_select_equ i n m (v : pool sE Bn n) g (w : pool sE Bn m) h j r :
  tp_slots (mk_pool m w h None) = filter (owned_by i) (tp_slots (mk_pool n v g None)) ->
  (g $ j) = i -> fin_nat r = rank (owned_by i) (tp_slots (mk_pool n v g None)) (fin_nat j) ->
  tp_equ (project_pool i (mk_pool n v g (Some j))) (mk_pool m w h (Some r)).
Proof.
  intros Hq Hj Hr; apply tp_equ_views.
  - rewrite tp_slots_project, proj_slots_filter; symmetry; exact Hq.
  - rewrite focus_nat_project.
    change ((if side_eqb (g $ j) i then
      Some (rank (owned_by i) (tp_slots (mk_pool n v g None)) (fin_nat j))
      else None) = Some (fin_nat r)).
    assert (Heq : side_eqb (g $ j) i = true) by (apply side_eqb_spec; exact Hj).
    rewrite Heq at 1; f_equal; symmetry; exact Hr.
Qed.

Lemma foreign_replace_slots i n (v : pool sE Bn n) g j t : (g $ j) <> i ->
  filter (owned_by i) (tp_slots (mk_pool n (v @ j := t) g None)) =
  filter (owned_by i) (tp_slots (mk_pool n v g None)).
Proof.
  intro Hj; destruct (pool_cut (mk_pool n v g None) j) as (pre & post & Hcut & Hlen).
  cbn [mk_pool tp_size tp_threads tp_tags] in Hcut.
  rewrite (slots_replace_view _ _ _ _ _ _ _ _ _ _ Hcut (eq_sym Hlen)), Hcut, !filter_app.
  cbn [filter snd]; now rewrite !owned_by_other by exact Hj.
Qed.

Lemma foreign_remove_slots i n (v : pool sE Bn (S n)) g j : (g $ j) <> i ->
  filter (owned_by i) (tp_slots (mk_pool n (v -- j) (g -- j) None)) =
  filter (owned_by i) (tp_slots (mk_pool (S n) v g None)).
Proof.
  intro Hj; destruct (pool_cut (mk_pool (S n) v g None) j) as (pre & post & Hcut & Hlen).
  cbn [mk_pool tp_size tp_threads tp_tags] in Hcut.
  rewrite (slots_remove_view _ _ _ _ _ _ _ _ _ Hcut (eq_sym Hlen)), Hcut, !filter_app.
  cbn [filter]; now rewrite owned_by_other by exact Hj.
Qed.

Lemma project_foreign_select_equ i n (v : pool sE Bn n) g j : (g $ j) <> i ->
  tp_equ (project_pool i (mk_pool n v g (Some j))) (project_pool i (mk_pool n v g None)).
Proof.
  intro Hj; apply tp_equ_views; [reflexivity|].
  unfold focus_nat; rewrite (project_focus_foreign i (mk_pool n v g (Some j))
    j eq_refl Hj) at 1; reflexivity.
Qed.

Lemma project_foreign_replace_equ i n (v : pool sE Bn n) g j t (focused : bool) : (g $ j) <> i ->
  tp_equ (project_pool i (mk_pool n (v @ j := t) g (if focused then Some j else None)))
    (project_pool i (mk_pool n v g (Some j))).
Proof.
  intro Hj; apply tp_equ_views.
  - rewrite !tp_slots_project, !proj_slots_filter; apply foreign_replace_slots, Hj.
  - unfold focus_nat; rewrite (project_focus_foreign i (mk_pool n v g (Some j))
      j eq_refl Hj) at 1.
    destruct focused.
    + rewrite (project_focus_foreign i (mk_pool n (v @ j := t) g (Some j))
        j eq_refl Hj) at 1; reflexivity.
    + reflexivity.
Qed.

Lemma project_foreign_fork_equ i n (v : pool sE Bn (S n)) g j x y : (g $ j) <> i ->
  tp_equ
    (project_pool i (mk_pool (S (S n)) (x :: (v @ j := y))%vector ((g $ j) :: g)%vector (Some (Fin.FS j))))
    (project_pool i (mk_pool (S n) v g (Some j))).
Proof.
  intro Hj; apply tp_equ_views.
  - rewrite !tp_slots_project, !proj_slots_filter, (slots_cons _ _ _ _ _ _ None).
    cbn [filter]; rewrite owned_by_other by exact Hj; apply foreign_replace_slots, Hj.
  - unfold focus_nat; rewrite (project_focus_foreign i (mk_pool (S n) v g (Some j))
      j eq_refl Hj) at 1.
    rewrite (project_focus_foreign i (mk_pool (S (S n))
      (x :: (v @ j := y))%vector ((g $ j) :: g)%vector (Some (Fin.FS j)))
      (Fin.FS j) eq_refl Hj) at 1; reflexivity.
Qed.

Lemma project_foreign_remove_equ i n (v : pool sE Bn (S n)) g j : (g $ j) <> i ->
  tp_equ (project_pool i (mk_pool n (v -- j) (g -- j) None))
    (project_pool i (mk_pool (S n) v g (Some j))).
Proof.
  intro Hj; apply tp_equ_views.
  - rewrite !tp_slots_project, !proj_slots_filter; apply foreign_remove_slots, Hj.
  - unfold focus_nat; rewrite (project_focus_foreign i (mk_pool (S n) v g (Some j))
      j eq_refl Hj) at 1; reflexivity.
Qed.

(** ** Primitives on the projection *)

Local Ltac fields_tac := unfold fields_eq; cbn; repeat split; try intros []; reflexivity.

Local Ltac destr_inner :=
  match goal with |- context [match ?x with _ => _ end] =>
    lazymatch x with
    | context [match _ with _ => _ end] => fail
    | _ => destruct x
    end
  end.

(** A primitive of lineage [i] behaves identically on its projection. *)
Lemma prim_project i c {Y} (e : sE Y) :
  match prim_step i c e, prim_step i (project i c) e with
  | Some (kind, y, c1), Some (kind', y', c1') =>
      y = y' /\ project_action i c (act i kind) = act i kind' /\ fields_eq c1' (project i c1)
  | None, None => True
  | _, _ => False
  end.
Proof.
  destruct i, e as [[a|a v|sz|b|a ex de]|[[|x]|[p]]]; cbn;
    repeat destr_inner;
    try exact I; (split; [reflexivity|split; [|fields_tac]]);
    unfold project_action, global_count; cbn; now rewrite ?Nat.add_0_r.
Qed.

Lemma prim_foreign s i c {Y} (e : sE Y) kind y c1 :
  s <> i -> prim_step s c e = Some (kind, y, c1) -> fields_eq (project i c1) (project i c).
Proof.
  intros Hs; revert kind y c1; destruct s, i; try congruence;
    destruct e as [[a|a v|sz|b|a ex de]|[[|x]|[p]]]; cbn;
    repeat destr_inner;
    intros kind y c1 H; try discriminate; injection H as <- <- <-; fields_tac.
Qed.

(** ** Direct projection of vector transitions *)

Lemma focus_step_owner c n v g j a c' :
  focus_step c n v g j a c' -> owner a = (g $ j).
Proof.
  intros [(t & _ & -> & _) | [(k & _ & -> & _) | [(k & _ & -> & _) |
    [(_ & -> & _) | (Y & e & k & kind & y & c1 & _ & _ & -> & _)]]]]; reflexivity.
Qed.

Lemma owned_step_focused_owner c a c' : owned_step c a c' ->
  forall j, tp_focus (oc_pool c) = Some j -> owner a = (tp_tags (oc_pool c) $ j).
Proof.
  unfold owned_step; destruct (oc_pool c) as [n v g f]; cbn [tp_focus tp_tags].
  destruct n as [|n]; [intros H; contradiction|].
  destruct f as [k|]; intros H j Hf; [injection Hf as <-|discriminate].
  exact (focus_step_owner _ _ _ _ _ _ _ H).
Qed.

Lemma owned_step_unfocused c a c' :
  tp_focus (oc_pool c) = None -> owned_step c a c' -> action_kind a = OASelect.
Proof.
  unfold owned_step; destruct (oc_pool c) as [n v g f]; cbn [tp_focus].
  destruct n as [|n]; [intros _ H; contradiction|]; destruct f; [discriminate|].
  intros _ (j & -> & _); reflexivity.
Qed.

Lemma unfocused_progress c : tp_focus (oc_pool c) = None ->
  0 < tp_size (oc_pool c) -> hcan_step owned_next c.
Proof.
  unfold hcan_step, owned_next, owned_step; destruct (oc_pool c) as [n v g f];
    cbn [tp_size tp_focus]; destruct n as [|n]; [intros _ H; lia|].
  destruct f; [discriminate|]; intros _ _.
  exists (set_pool c (mk_pool (S n) v g (Some Fin.F1))), (act (g $ Fin.F1) OASelect).
  exists Fin.F1; auto.
Qed.

(** An action of lineage [i] is one local action of its projection. *)
Lemma owned_step_own i c a c' :
  owned_step c a c' -> owner a = i ->
  exists d', owned_step (project i c) (project_action i c a) d' /\ owned_equ (project i c') d'.
Proof.
  intros H Ho; unfold owned_step in H.
  destruct (oc_pool c) as [n v g f] eqn:Hp; rewrite ?Hp in H;
    destruct n as [|n]; [contradiction|].
  destruct f as [j|].
  - assert (Hj : (g $ j) = i) by (rewrite <- Ho; symmetry; exact (focus_step_owner _ _ _ _ _ _ _ H)).
    pose proof (project_focused_index i (mk_pool (S n) v g (Some j)) j eq_refl Hj) as Hi.
    destruct (project_pool i (mk_pool (S n) v g (Some j))) as [m w h fq] eqn:Hq in Hi.
    cbn [tp_size tp_threads tp_tags tp_focus] in Hi.
    destruct Hi as (r & Hr & Ht & Hg & Hf); subst fq.
    destruct m as [|m]; [inversion r|].
    assert (Hpool : oc_pool (project i c) = mk_pool (S m) w h (Some r)).
    { change (project_pool i (oc_pool c) = mk_pool (S m) w h (Some r)); now rewrite Hp. }
    pose proof (projection_slots _ _ _ _ _ _ Hq) as Hslots.
    destruct H as [(t & Hh & -> & ->) | [(k & Hh & -> & ->) | [(k & Hh & -> & ->) |
      [(Hh & -> & ->) | (Y & e & k & kind & y & c1 & Hh & Hprim & -> & ->)]]]].
    + exists (set_pool (project i c) (mk_pool (S m) (w @ r := t) h (Some r))); split.
      * unfold owned_step; rewrite Hpool; cbn; left; exists t; rewrite Hg, Hj, Ht; auto.
      * rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
        apply (project_replace_equ i _ _ v g w h j r t true Hslots Hj Hr).
    + exists (set_pool (project i c) (mk_pool (S m) (w @ r := k tt) h None)); split.
      * unfold owned_step; rewrite Hpool; cbn; right; left; exists k; rewrite Hg, Hj, Ht; auto.
      * rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
        apply (project_replace_equ i _ _ v g w h j r (k tt) false Hslots Hj Hr).
    + exists (set_pool (project i c) (mk_pool (S (S m))
        (k true :: (w @ r := k false))%vector ((h $ r) :: h)%vector (Some (Fin.FS r)))); split.
      * unfold owned_step; rewrite Hpool; cbn; right; right; left; exists k; rewrite Hg, Hj, Ht; auto.
      * rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
        apply (project_fork_equ i _ _ v g w h j r _ _ Hslots Hj Hg Hr).
    + exists (set_pool (project i c) (mk_pool m (w -- r) (h -- r) None)); split.
      * unfold owned_step; rewrite Hpool; cbn; right; right; right; left; rewrite Hg, Hj, Ht; auto.
      * rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
        apply (project_remove_equ i _ _ v g w h j r Hslots Hj Hr).
    + rewrite Hj in Hprim; pose proof (prim_project i c e) as Hpp; rewrite Hprim in Hpp.
      destruct (prim_step i (project i c) e) as [[[kind' y'] c1']|] eqn:Hprim'; [|contradiction].
      destruct Hpp as (<- & Hact & Hfields).
      exists (set_pool c1' (mk_pool (S m) (w @ r := k y) h (Some r))); split.
      * rewrite Hj, Hact; unfold owned_step; rewrite Hpool; cbn; right; right; right; right.
        exists Y, e, k, kind', y, c1'; rewrite Hg, Ht; auto.
      * rewrite project_set_pool; apply owned_equ_pool_fields.
        -- apply (project_replace_equ i _ _ v g w h j r (k y) true Hslots Hj Hr).
        -- apply fields_eq_sym, Hfields.
  - destruct H as (j & -> & ->); cbn [owner act] in Ho.
    pose proof (project_index i (mk_pool (S n) v g None) j Ho) as Hi.
    pose proof (project_focus_none i (mk_pool (S n) v g None) eq_refl) as Hnone.
    destruct (project_pool i (mk_pool (S n) v g None)) as [m w h fq] eqn:Hq in Hi, Hnone.
    cbn [tp_size tp_threads tp_tags tp_focus] in Hi, Hnone; subst fq.
    destruct Hi as (r & Hr & Ht & Hg); destruct m as [|m]; [inversion r|].
    assert (Hpool : oc_pool (project i c) = mk_pool (S m) w h None).
    { change (project_pool i (oc_pool c) = mk_pool (S m) w h None); now rewrite Hp. }
    exists (set_pool (project i c) (mk_pool (S m) w h (Some r))); split.
    + unfold owned_step; rewrite Hpool; cbn; exists r; rewrite Hg, Ho; auto.
    + rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
      apply project_select_equ; [exact (projection_slots _ _ _ _ _ _ Hq)|exact Ho|exact Hr].
Qed.

(** A foreign action leaves the projection unchanged. *)
Lemma owned_step_foreign i c a c' :
  owned_step c a c' -> owner a <> i -> owned_equ (project i c') (project i c).
Proof.
  intros H Ho; unfold owned_step in H.
  destruct (oc_pool c) as [n v g f] eqn:Hp; rewrite ?Hp in H;
    destruct n as [|n]; [contradiction|].
  destruct f as [j|].
  - assert (Hj : (g $ j) <> i) by (rewrite <- (focus_step_owner _ _ _ _ _ _ _ H); exact Ho).
    destruct H as [(t & Hh & -> & ->) | [(k & Hh & -> & ->) | [(k & Hh & -> & ->) |
      [(Hh & -> & ->) | (Y & e & k & kind & y & c1 & Hh & Hprim & -> & ->)]]]];
      rewrite project_set_pool; apply owned_equ_pool_fields; cbn [oc_pool set_pool project]; rewrite ?Hp.
    + apply (project_foreign_replace_equ i _ v g j t true Hj).
    + fields_tac.
    + apply (project_foreign_replace_equ i _ v g j (k tt) false Hj).
    + fields_tac.
    + apply project_foreign_fork_equ, Hj.
    + fields_tac.
    + apply project_foreign_remove_equ, Hj.
    + fields_tac.
    + apply (project_foreign_replace_equ i _ v g j (k y) true Hj).
    + exact (prim_foreign _ _ _ _ _ _ _ Hj Hprim).
  - destruct H as (j & -> & ->); rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
    cbn [oc_pool set_pool project]; rewrite Hp; apply project_foreign_select_equ; exact Ho.
Qed.

(** Every local successor lifts when focus is absent or belongs to [i]. *)
Lemma owned_step_lift i c a' d' :
  (tp_focus (oc_pool c) = None \/
    exists j, tp_focus (oc_pool c) = Some j /\ (tp_tags (oc_pool c) $ j) = i) ->
  owned_step (project i c) a' d' ->
  exists a c', owned_step c a c' /\ owner a = i /\ project_action i c a = a' /\
    owned_equ (project i c') d'.
Proof.
  intros Hfocus Hlocal; destruct (oc_pool c) as [n v g f] eqn:Hp.
  rewrite ?Hp in Hfocus; cbn [tp_focus tp_tags] in Hfocus.
  destruct f as [j|].
  - destruct Hfocus as [Hbad | (j' & Hf & Hj)]; [discriminate|injection Hf as <-].
    destruct n as [|n]; [inversion j|].
    pose proof (project_focused_index i (mk_pool (S n) v g (Some j)) j eq_refl Hj) as Hi.
    destruct (project_pool i (mk_pool (S n) v g (Some j))) as [m w h fq] eqn:Hq in Hi.
    cbn [tp_size tp_threads tp_tags tp_focus] in Hi.
    destruct Hi as (r & Hr & Ht & Hg & Hf); subst fq; destruct m as [|m]; [inversion r|].
    assert (Hpool : oc_pool (project i c) = mk_pool (S m) w h (Some r)).
    { change (project_pool i (oc_pool c) = mk_pool (S m) w h (Some r)); now rewrite Hp. }
    pose proof (projection_slots _ _ _ _ _ _ Hq) as Hslots.
    unfold owned_step in Hlocal; rewrite Hpool in Hlocal; cbn in Hlocal.
    destruct Hlocal as [(t & Hh & -> & ->) | [(k & Hh & -> & ->) | [(k & Hh & -> & ->) |
      [(Hh & -> & ->) | (Y & e & k & kind' & y & c1' & Hh & Hprim' & -> & ->)]]]].
    + exists (act i OAStep), (set_pool c (mk_pool (S n) (v @ j := t) g (Some j))).
      split; [unfold owned_step; rewrite Hp; cbn; left; exists t; rewrite Hj at 1; rewrite <- Ht at 1; auto|].
      split; [reflexivity|split; [now rewrite Hg|]].
      rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
      apply (project_replace_equ i _ _ v g w h j r t true Hslots Hj Hr).
    + exists (act i OAYield), (set_pool c (mk_pool (S n) (v @ j := k tt) g None)).
      split; [unfold owned_step; rewrite Hp; cbn; right; left; exists k; rewrite Hj at 1; rewrite <- Ht at 1; auto|].
      split; [reflexivity|split; [now rewrite Hg|]].
      rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
      apply (project_replace_equ i _ _ v g w h j r (k tt) false Hslots Hj Hr).
    + exists (act i OAFork), (set_pool c (mk_pool (S (S n))
        (k true :: (v @ j := k false))%vector ((g $ j) :: g)%vector (Some (Fin.FS j)))).
      split; [unfold owned_step; rewrite Hp; cbn; right; right; left; exists k; rewrite Hj at 1; rewrite <- Ht at 1; auto|].
      split; [reflexivity|split; [now rewrite Hg|]].
      rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
      apply (project_fork_equ i _ _ v g w h j r _ _ Hslots Hj Hg Hr).
    + exists (act i OAReturn), (set_pool c (mk_pool n (v -- j) (g -- j) None)).
      split; [unfold owned_step; rewrite Hp; cbn; right; right; right; left; rewrite Hj at 1; rewrite <- Ht at 1; auto|].
      split; [reflexivity|split; [now rewrite Hg|]].
      rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
      apply (project_remove_equ i _ _ v g w h j r Hslots Hj Hr).
    + rewrite Hg in Hprim'; pose proof (prim_project i c e) as Hpp; rewrite Hprim' in Hpp.
      destruct (prim_step i c e) as [[[kind y0] c1]|] eqn:Hprim; [|contradiction].
      destruct Hpp as (-> & Hact & Hfields).
      exists (act i kind), (set_pool c1 (mk_pool (S n) (v @ j := k y) g (Some j))).
      split.
      * unfold owned_step; rewrite Hp; cbn; right; right; right; right.
        exists Y, e, k, kind, y, c1; split.
        -- rewrite <- Ht at 1; exact Hh.
        -- split.
           ++ exact (eq_trans (f_equal (fun s => prim_step s c e) Hj) Hprim).
           ++ split; [exact (f_equal (fun s => act s kind) (eq_sym Hj))|reflexivity].
      * split; [reflexivity|split; [now rewrite Hg|]].
        rewrite project_set_pool; apply owned_equ_pool_fields.
        -- apply (project_replace_equ i _ _ v g w h j r (k y) true Hslots Hj Hr).
        -- apply fields_eq_sym, Hfields.
  - pose proof (project_focus_none i (mk_pool n v g None) eq_refl) as Hnone.
    pose proof (project_index_inv i (mk_pool n v g None)) as Hinv.
    destruct (project_pool i (mk_pool n v g None)) as [m w h fq] eqn:Hq in Hnone, Hinv.
    cbn [mk_pool tp_size tp_threads tp_tags tp_focus] in Hnone, Hinv; subst fq.
    assert (Hpool : oc_pool (project i c) = mk_pool m w h None).
    { change (project_pool i (oc_pool c) = mk_pool m w h None); now rewrite Hp. }
    unfold owned_step in Hlocal; rewrite Hpool in Hlocal.
    destruct m as [|m]; [contradiction|]; destruct Hlocal as (r & -> & ->).
    destruct (Hinv r) as (j & Hj & Hr & Ht & Hg).
    destruct n as [|n]; [inversion j|].
    exists (act i OASelect), (set_pool c (mk_pool (S n) v g (Some j))).
    split; [unfold owned_step; rewrite Hp; exists j; rewrite Hj; auto|].
    split; [reflexivity|split; [now rewrite Hg|]].
    rewrite project_set_pool; apply owned_equ_pool_fields; [|fields_tac].
    apply project_select_equ; [exact (projection_slots _ _ _ _ _ _ Hq)|exact Hj|exact Hr].
Qed.

Lemma own_enabled_intro i c :
  (tp_focus (oc_pool c) = None \/
    exists j, tp_focus (oc_pool c) = Some j /\ (tp_tags (oc_pool c) $ j) = i) ->
  hcan_step owned_next (project i c) -> OwnEnabled i c.
Proof. intros Hfocus Hcan; split; [exact Hcan|intros; eapply owned_step_lift; eauto]. Qed.

(** Positive progress excludes a stuck owned focus from the stutter case. *)
Lemma scheduler_shape i c :
  hcan_step owned_next c -> StutterOnly i c \/ OwnEnabled i c.
Proof.
  intros (c' & a & Hstep); destruct (tp_focus (oc_pool c)) as [j|] eqn:Hfocus.
  - destruct (side_eq_dec (tp_tags (oc_pool c) $ j) i) as [Hj|Hj].
    + right; apply own_enabled_intro; [right; exists j; auto|].
      assert (Ho : owner a = i) by (rewrite (owned_step_focused_owner _ _ _ Hstep j Hfocus); exact Hj).
      destruct (owned_step_own i _ _ _ Hstep Ho) as (d & Hd & _).
      exists d, (project_action i c a); exact Hd.
    + left; intros b d Hd; rewrite (owned_step_focused_owner _ _ _ Hd j Hfocus); exact Hj.
  - destruct (tp_size (oc_pool (project i c))) as [|n] eqn:Hsize.
    + left; intros b d Hd Ho.
      destruct (owned_step_own i _ _ _ Hd Ho) as (d' & Hd' & _).
      unfold owned_step in Hd'; destruct (oc_pool (project i c)) as [m w h f] in Hd', Hsize;
        cbn [tp_size] in Hsize.
      subst m; contradiction.
    + right; apply own_enabled_intro; [left; exact Hfocus|].
      apply unfocused_progress; [apply project_focus_none, Hfocus|rewrite Hsize; lia].
Qed.

Lemma stutter_select i c :
  hcan_step owned_next c -> StutterOnly i c ->
  0 < tp_size (oc_pool (project i c)) ->
  tp_focus (oc_pool (project i c)) = None /\ hcan_step owned_next (project i c) /\
  (forall a d, owned_step (project i c) a d -> action_kind a = OASelect).
Proof.
  intros (d & a & Hstep) Hst Hsize.
  assert (Hnone : tp_focus (oc_pool (project i c)) = None).
  { destruct (tp_focus (oc_pool c)) as [j|] eqn:Hfocus.
    - apply project_focus_foreign with j; [exact Hfocus|].
      rewrite <- (owned_step_focused_owner _ _ _ Hstep j Hfocus); exact (Hst _ _ Hstep).
    - apply project_focus_none, Hfocus. }
  split; [exact Hnone|split].
  - apply unfocused_progress; assumption.
  - intros b e He; eapply owned_step_unfocused; eauto.
Qed.

Lemma foreign_star_project i c c' :
  clos_refl_trans _ (foreign_next i) c c' -> owned_equ (project i c') (project i c).
Proof.
  induction 1 as [x y (a & Ha & Ho)|x|x y z _ IH1 _ IH2].
  - eapply owned_step_foreign; eauto.
  - reflexivity.
  - etransitivity; eauto.
Qed.

Lemma weak_next_equ i c d c' :
  owned_equ c d -> weak_next i c c' -> exists d', weak_next i d d' /\ owned_equ c' d'.
Proof.
  intros Heq (mid & Hstar & a & Hst & Ho).
  apply clos_rt_rt1n in Hstar; revert d Heq Hst; induction Hstar as [x|x y z Hxy Hyz IH];
    intros d Heq Hst.
  - destruct (owned_step_equ _ _ _ _ Heq Hst) as (d' & Hd & He).
    exists d'; split; [exists d; split; [apply rt_refl|exists a; auto]|exact He].
  - destruct Hxy as (b & Hb & Hob).
    destruct (owned_step_equ _ _ _ _ Heq Hb) as (d1 & Hd1 & He1).
    destruct (IH d1 He1 Hst) as (d' & (mid' & Hstar' & Hown') & He').
    exists d'; split; [|exact He'].
    exists mid'; split; [|exact Hown'].
    eapply rt_trans; [apply rt_step; exists b; eauto|exact Hstar'].
Qed.

Lemma weak_next_sound i c c' :
  weak_next i c c' -> exists d', owned_next (project i c) d' /\ owned_equ (project i c') d'.
Proof.
  intros (mid & Hstar & a & Hst & Ho).
  destruct (owned_step_own _ _ _ _ Hst Ho) as (d' & Hd & He).
  destruct (owned_step_equ _ _ _ _ (foreign_star_project _ _ _ Hstar) Hd) as (d'' & Hd'' & He'').
  exists d''; split; [exists (project_action i mid a); exact Hd''|etransitivity; eauto].
Qed.

(** One weak successor witnesses that every local successor is realized. *)
Lemma weak_next_complete i c :
  hcan_step (weak_next i) c ->
  forall d', owned_next (project i c) d' -> exists c', weak_next i c c' /\ owned_equ (project i c') d'.
Proof.
  intros (c1 & mid & Hstar & a & Hst & Ho) d' (a' & Hd).
  pose proof (foreign_star_project _ _ _ Hstar) as Hm; symmetry in Hm.
  destruct (owned_step_equ _ _ _ _ Hm Hd) as (d'' & Hd'' & He).
  destruct (scheduler_shape i mid) as [Hstut|[_ Hlift]]; [exists c1, a; exact Hst| |].
  - exfalso; exact (Hstut a c1 Hst Ho).
  - destruct (Hlift _ _ Hd'') as (b & c' & Hb & Hob & _ & He').
    exists c'; split; [exists mid; split; [exact Hstar|exists b; auto]|].
    etransitivity; [exact He'|symmetry; exact He].
Qed.

Lemma reach_project i c0 c :
  clos_refl_trans _ owned_next c0 c ->
  exists d, clos_refl_trans _ owned_next (project i c0) d /\ owned_equ d (project i c).
Proof.
  intros H; apply clos_rt_rtn1 in H; induction H as [|y z (a & Ha) _ (d & Hd & He)].
  - exists (project i c0); split; [apply rt_refl|reflexivity].
  - destruct (side_eq_dec (owner a) i) as [Ho|Ho].
    + destruct (owned_step_own _ _ _ _ Ha Ho) as (e & He1 & He2).
      symmetry in He.
      destruct (owned_step_equ _ _ _ _ He He1) as (e' & He' & Hee).
      exists e'; split; [eapply rt_trans; [exact Hd|apply rt_step; eexists; exact He']|].
      symmetry; etransitivity; eauto.
    + exists d; split; [exact Hd|].
      etransitivity; [exact He|symmetry; eapply owned_step_foreign; eauto].
Qed.

Lemma owned_wf_project i c : owned_wf c -> owned_wf (project i c).
Proof.
  intros (H1&H2&H3&H4&H5&H6&H7&H8); destruct i; unfold owned_wf;
    cbn [project oc_heap oc_anchor side_only side_eqb];
    repeat match goal with |- _ /\ _ => split end;
    first [assumption|apply managed_wf_empty|split; intros ? Hx; exact Hx
          |split; intro; first [left; reflexivity|right; reflexivity]].
Qed.

Lemma project_size_terminal i c :
  tp_size (oc_pool c) = 0 -> tp_size (oc_pool (project i c)) = 0.
Proof.
  intros H; change (length (proj_slots i (oc_pool c)) = 0); rewrite proj_slots_filter.
  pose proof (tp_slots_length (oc_pool c)) as Hl; rewrite H in Hl.
  destruct (tp_slots (oc_pool c)); [reflexivity|discriminate].
Qed.

(** ** Coupling to an admitted fork *)

Lemma coupled_init child parent h h' ctx base :
  admissible child parent h h' ctx base -> coupled (init_owned child parent h h' ctx base).
Proof.
  intros Ha; exists child, parent, h, h', ctx, base, (init_owned child parent h h' ctx base).
  split; [exact Ha|split; [apply rt_refl|reflexivity]].
Qed.

Lemma coupled_equ c d : owned_equ c d -> coupled c -> coupled d.
Proof.
  intros He (ch & pa & h & h' & ctx & base & d0 & Ha & Hr & He0).
  exists ch, pa, h, h', ctx, base, d0; split; [exact Ha|split; [exact Hr|etransitivity; eauto]].
Qed.

Lemma coupled_step c a c' : coupled c -> owned_step c a c' -> coupled c'.
Proof.
  intros (ch & pa & h & h' & ctx & base & d & Ha & Hr & He) Hs; symmetry in He.
  destruct (owned_step_equ _ _ _ _ He Hs) as (d' & Hd' & He').
  exists ch, pa, h, h', ctx, base, d'; split; [exact Ha|split].
  - eapply rt_trans; [exact Hr|apply rt_step; exists a; exact Hd'].
  - symmetry; exact He'.
Qed.

Lemma coupled_weak i c c' : coupled c -> weak_next i c c' -> coupled c'.
Proof.
  intros Hc (mid & Hstar & a & Hs & _); apply (coupled_step mid a c'); [|exact Hs].
  clear Hs; revert Hc; induction Hstar as [x y (b & Hb & _)|x|x y z _ IH1 _ IH2]; intros Hc.
  - eapply coupled_step; eauto.
  - exact Hc.
  - auto.
Qed.

Lemma coupled_wf c : coupled c -> owned_wf c.
Proof.
  intros (ch & pa & h & h' & ctx & base & d & (Hw & Hw' & Hd & _) & Hr & He).
  eapply owned_wf_equ; [exact He|]; clear He.
  apply clos_rt_rtn1 in Hr; induction Hr as [|y z (a & Ha) _ IH].
  - apply init_owned_wf; assumption.
  - eapply owned_step_wf; eauto.
Qed.

Local Close Scope list_scope.

(** * Admission and confinement of forked CoCSL components.

    A component is admitted when its events exclude allocation and context
    writes and every reachable pending primitive stays inside its owner's
    reservation.  [addr_ok] is a static sufficient condition for programs whose
    addresses are literals. *)

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

(** ** Static confinement: literal-address programs *)

Fixpoint addr_ok (r : ManagedHeap) {A} (p : CProg A) : Prop :=
  match p with
  | CRead a => fst r a <> None
  | CWrite a _ => fst r a <> None
  | CFree b => b = 0 \/ snd r b <> None
  | CCAS (CLit a) _ _ => fst r a <> None
  | CCAS _ _ _ => False
  | CFork body => addr_ok r body
  | CBind body next => addr_ok r body /\ forall x, addr_ok r (next x)
  | CUntilNone body => addr_ok r body
  | CIf _ yes no => addr_ok r yes /\ addr_ok r no
  | CWhile _ body => addr_ok r body
  | _ => True
  end.

(** ** Helpers *)

Local Definition okR (r : ManagedHeap) : forall Y, sE Y -> Prop := fun Y e => prim_addr_ok r e.

Local Lemma framable_equ {E B A} (okE : forall Y, E Y -> Prop) (t u : ctree E B A) :
  t ≅ u -> Framable okE t -> Framable okE u.
Proof. intros H Ht; exact (proj1 (framable_chain_equ okE (R := chain_gfp _) t u H) Ht). Qed.

Local Lemma framable_guards {E B A} (okE : forall Y, E Y -> Prop) n (u : ctree E B A) :
  Framable okE (guards n u) -> Framable okE u.
Proof.
  induction n as [|n IH]; cbn [guards]; [easy|intro H].
  apply framable_unfold in H; cbn in H; dependent destruction H; auto.
Qed.

Local Lemma headed_framable r t u :
  Framable (okE_thread (okR r)) t -> headed t u -> Framable (okE_thread (okR r)) u.
Proof. intros Ht [n Hn]; eapply framable_guards, framable_equ; eauto. Qed.

Local Lemma framable_vis_inv {E B A Y} (okE : forall Y, E Y -> Prop) (e : E Y) (k : Y -> ctree E B A) :
  Framable okE (Vis e k) -> okE Y e /\ forall x, Framable okE (k x).
Proof. intro H; apply framable_unfold in H; cbn in H; dependent destruction H; auto. Qed.

Local Lemma framable_step_inv {E B A} (okE : forall Y, E Y -> Prop) (t : ctree E B A) :
  Framable okE (Step t) -> Framable okE t.
Proof. intro H; apply framable_unfold in H; cbn in H; dependent destruction H; auto. Qed.

Local Ltac fr_trig :=
  unfold heap_read, heap_write, heap_free, heap_cas, heap_alloc, source_get, source_put,
    source_yield, source_fork, CTree.trigger;
  apply fr_vis; [cbn; first [exact I|assumption]|intro; apply fr_ret].

Local Lemma exp_framable r e : Framable (okE_thread (okR r)) (denote_exp e).
Proof.
  apply denote_exp_framable.
  induction e; cbn; repeat split; assumption.
Qed.

Local Lemma addr_ok_framable r {A} (p : CProg A) :
  addr_ok r p -> Framable (okE_thread (okR r)) (denote_flow p).
Proof.
  induction p as [a|a v|q v| |body IH|A x|A B body IH next IHnext|A body IH|size|base
    |a expected desired|e|name e|A test yes IHyes no IHno|test body IH];
    cbn [denote_flow addr_ok]; intro Hp.
  - apply framable_bind; [fr_trig|intro x; apply fr_ret].
  - apply framable_bind; [fr_trig|intros []; apply fr_ret].
  - apply framable_bind; [fr_trig|intros []; apply fr_ret].
  - apply framable_bind; [fr_trig|intros []; apply fr_ret].
  - apply framable_bind; [fr_trig|].
    intros []; cbn.
    + apply framable_bind; [exact (IH Hp)|intro flow; apply fr_ret].
    + apply fr_ret.
  - apply fr_ret.
  - destruct Hp as [Hb Hn].
    apply framable_bind; [exact (IH Hb)|].
    intros [x|]; [apply IHnext, Hn|apply fr_ret].
  - apply framable_iter; intros [].
    apply framable_bind; [exact (IH Hp)|].
    intros [[x|]|]; apply fr_ret.
  - apply framable_bind; [fr_trig|intro a; apply fr_ret].
  - apply framable_bind; [fr_trig|intros []; apply fr_ret].
  - destruct a as [|a| | |]; try contradiction; cbn [denote_exp].
    eapply framable_equ; [symmetry; apply bind_ret_l|].
    apply framable_bind; [apply exp_framable|intro old].
    apply framable_bind; [apply exp_framable|intro value].
    apply framable_bind; [fr_trig|intro b; apply fr_ret].
  - apply framable_bind; [apply exp_framable|intro v; apply fr_ret].
  - apply framable_bind; [apply exp_framable|intro v].
    apply framable_bind; [fr_trig|].
    intro ctx; apply framable_bind; [fr_trig|intros []; apply fr_ret].
  - destruct Hp as [Hy Hn].
    apply framable_bind; [apply exp_framable|intro v].
    destruct (CoCSLSyntax.is_true v); auto.
  - apply framable_iter; intros [].
    apply framable_bind; [apply exp_framable|intro v].
    destruct (CoCSLSyntax.is_true v); [|apply fr_ret].
    apply framable_bind; [exact (IH Hp)|].
    intros [[]|]; apply fr_ret.
Qed.

(** Every slot only issues primitives inside [r]. *)
Local Definition confined_pool_ok r (c : OwnedCfg) : Prop := pool_framable (okR r) (tp_threads (oc_pool c)).

Local Lemma confined_pool_ok_step r c a c' : confined_pool_ok r c -> owned_step c a c' -> confined_pool_ok r c'.
Proof.
  unfold confined_pool_ok, owned_step; destruct (oc_pool c) as [n v g f]; cbn.
  destruct n as [|n]; [contradiction|].
  destruct f as [j|]; intros Hv Hs.
  2: { destruct Hs as (j & -> & ->); exact Hv. }
  pose proof (Hv j) as Hj.
  destruct Hs as [(t & Hh & -> & ->)|[(k & Hh & -> & ->)|[(k & Hh & -> & ->)
    |[(Hh & -> & ->)|(Y & e & k & kind & y & c1 & Hh & Hp & -> & ->)]]]]; cbn;
    try (apply (headed_framable r) in Hh; [|exact Hj]).
  - apply pool_framable_replace; [exact Hv|exact (framable_step_inv _ _ Hh)].
  - apply pool_framable_replace; [exact Hv|exact (proj2 (framable_vis_inv _ _ _ Hh) tt)].
  - apply framable_vis_inv in Hh as [_ Hk].
    apply pool_framable_cons; [apply Hk|apply pool_framable_replace; [exact Hv|apply Hk]].
  - apply pool_framable_remove, Hv.
  - apply pool_framable_replace; [exact Hv|exact (proj2 (framable_vis_inv _ _ _ Hh) y)].
Qed.

Local Lemma pool_ok_reach r c c' : clos_refl_trans _ owned_next c c' -> confined_pool_ok r c -> confined_pool_ok r c'.
Proof.
  induction 1 as [c c' [a Hs]| |]; auto.
  intro; eapply confined_pool_ok_step; eauto.
Qed.

Local Lemma forall2_nth_error {A B} (R : A -> B -> Prop) l l' k x y :
  List.Forall2 R l l' -> List.nth_error l k = Some x -> List.nth_error l' k = Some y -> R x y.
Proof.
  intro H; revert k; induction H as [|a b l l' Hab H IH]; intros [|k]; cbn; try discriminate.
  - congruence.
  - apply IH.
Qed.

(** The focused thread is invariant under [tp_equ] up to [≅]. *)
Local Lemma focused_thread_equ p q t i :
  tp_equ p q -> focused_thread q = Some (t, i) ->
  exists t', focused_thread p = Some (t', i) /\ t' ≅ t.
Proof.
  unfold tp_equ, focused_thread, focus_nat; intros [Hs Hf].
  destruct (tp_focus q) as [j|]; [|discriminate]; intro Hq; injection Hq as <- <-.
  destruct (tp_focus p) as [j'|]; cbn in Hf; [|discriminate]; injection Hf as Hf.
  pose proof (tp_slots_nth_error p j') as Hp; pose proof (tp_slots_nth_error q j) as Hq.
  rewrite Hf in Hp; destruct (forall2_nth_error _ _ _ _ _ _ Hs Hp Hq) as [Ht Hi]; cbn in *.
  rewrite Hi; eauto.
Qed.

(** The focused owned thread is the focused thread of the projection. *)
Local Lemma focused_project i p t :
  focused_thread p = Some (t, i) -> focused_thread (project_pool i p) = Some (t, i).
Proof.
  unfold focused_thread at 1; destruct (tp_focus p) as [j|] eqn:Hf; [|discriminate].
  intro H; injection H as Ht Hi.
  destruct (project_focused_index i p j Hf Hi) as (r & _ & Hr & Htag & Hfocus).
  unfold focused_thread; now rewrite Hfocus, Hr, Htag, Ht.
Qed.

(** ** Confinement *)

Lemma confined_equ r c d : owned_equ c d -> confined r c -> confined r d.
Proof.
  intros Hcd Hc d' Hd' t i Y e k Hf Hh.
  assert (exists c', clos_refl_trans _ owned_next c c' /\ owned_equ c' d') as (c' & Hc' & Heq).
  { clear - Hcd Hd'; apply clos_rt_rtn1 in Hd'; induction Hd' as [|y z Hyz _ IH].
    - exists c; split; [apply rt_refl|exact Hcd].
    - destruct IH as (c' & Hc' & Heq).
      destruct (owned_next_equ y c' z (symmetry Heq) Hyz) as (c'' & Hc'' & Hz).
      exists c''; split; [eapply rt_trans; [exact Hc'|apply rt_step, Hc'']|symmetry; exact Hz]. }
  destruct (focused_thread_equ _ _ _ _ (proj1 Heq) Hf) as (t' & Hf' & Ht).
  eapply Hc; [exact Hc'|exact Hf'|eapply headed_equ; [symmetry; exact Ht|exact Hh]].
Qed.

Lemma addr_ok_confined r i p h ctx base focused :
  addr_ok r p -> confined r (init_local i p h ctx base focused).
Proof.
  intros Hp c Hc t j Y e k Hf Hh.
  assert (Hv : confined_pool_ok r c).
  { apply (pool_ok_reach _ _ _ Hc); intro x; dependent destruction x; [|inversion x].
    apply framable_bind; [apply addr_ok_framable, Hp|intro; apply fr_ret]. }
  unfold focused_thread in Hf; destruct (tp_focus (oc_pool c)) as [x|]; [|discriminate].
  injection Hf as <- _.
  exact (proj1 (framable_vis_inv _ _ _ (headed_framable r _ _ (Hv x) Hh))).
Qed.

Lemma admissible_intro child parent h h' ctx base :
  managed_wf h -> managed_wf h' -> h # h' ->
  component_ok child -> component_ok parent ->
  addr_ok h child -> addr_ok h' parent ->
  admissible child parent h h' ctx base.
Proof.
  intros; do 5 (split; [assumption|]); split.
  - eapply confined_equ; [symmetry; apply project_init_child|apply addr_ok_confined; assumption].
  - eapply confined_equ; [symmetry; apply project_init_parent|apply addr_ok_confined; assumption].
Qed.

(** Every reachable pending primitive of an admitted fork is confined to its
    owner's reservation. *)
Lemma admissible_head_confined child parent h h' ctx base d :
  admissible child parent h h' ctx base ->
  clos_refl_trans _ owned_next (init_owned child parent h h' ctx base) d ->
  head_confined d.
Proof.
  intros (_ & _ & _ & _ & _ & HC & HP) Hd t i Y e k Hf Hh.
  assert (Ha : oc_anchor d = oc_anchor (init_owned child parent h h' ctx base)).
  { clear - Hd; induction Hd as [c c' [a Hs]| |]; auto.
    - apply (owned_step_frozen _ _ _ Hs).
    - congruence. }
  rewrite Ha.
  pose proof (focused_project i _ _ Hf) as Hfp.
  destruct (reach_project i _ _ Hd) as (d0 & Hr0 & Heq0).
  destruct (focused_thread_equ _ _ _ _ (proj1 Heq0) Hfp) as (t' & Hf0 & Ht).
  assert (Hh' : headed t' (Vis (inr1 (inr1 e) : CEff Y) k))
    by (eapply headed_equ; [symmetry; exact Ht|exact Hh]).
  destruct i; [exact (HC d0 Hr0 _ _ _ _ _ Hf0 Hh')|exact (HP d0 Hr0 _ _ _ _ _ Hf0 Hh')].
Qed.

From TICL Require Import Lang.CoCSL.Sequential.

(** * Erasure of the owned action machine to the original ND runner.

    Erasable owned configurations erase, label for label, to [interp_schedule_nd sh]
    over their joined heap; returned heaps agree up to [≈]. *)

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

(** The erasure invariant: ownership, admissible events, no hidden branches,
    and confinement of every reachable pending primitive. *)
Definition erasable (c : OwnedCfg) : Prop :=
  owned_wf c /\
  pool_framable component_event_ok (tp_threads (oc_pool c)) /\
  pool_branchfree (tp_threads (oc_pool c)) /\
  (forall d, clos_refl_trans _ owned_next c d -> head_confined d).

(** ** Guard alignment up to a return relation

    [galigned] with returns related by [RV] instead of equal: one node of
    each side after finitely many guards, a silent round consuming at least
    one guard on both sides, and hidden branches aligned branchwise. *)
Section RAlign.
  Context {E B : Type -> Type} {X : Type} (RV : X -> X -> Prop)
    (R : ctree E B X -> ctree E B X -> Prop).

  Inductive ralignF : ctree E B X -> ctree E B X -> Prop :=
  | ralF_guard t u n m t' u' :
      t ≅ guards (S n) t' -> u ≅ guards (S m) u' -> R t' u' -> ralignF t u
  | ralF_ret t u n m r r' :
      t ≅ guards n (Ret r) -> u ≅ guards m (Ret r') -> RV r r' -> ralignF t u
  | ralF_br t u n m {Y} (c : B Y) (k k' : Y -> ctree E B X) :
      t ≅ guards n (Br c k) -> u ≅ guards m (Br c k') ->
      (forall i, ralignF (k i) (k' i)) -> ralignF t u
  | ralF_vis t u n m {Y} (e : E Y) (k k' : Y -> ctree E B X) :
      t ≅ guards n (Vis e k) -> u ≅ guards m (Vis e k') ->
      (forall x, R (k x) (k' x)) -> ralignF t u
  | ralF_stuck t u n m :
      t ≅ guards n Stuck -> u ≅ guards m Stuck -> ralignF t u
  | ralF_step t u n m t' u' :
      t ≅ guards n (Step t') -> u ≅ guards m (Step u') -> R t' u' -> ralignF t u.

  Lemma ralignF_equ t u a b : t ≅ a -> u ≅ b -> ralignF t u -> ralignF a b.
  Proof.
    intros Et Eu H; destruct H as
      [t u n m t' u' El Er H|t u n m r r' El Er H|t u n m Y c k k' El Er H
      |t u n m Y e k k' El Er H|t u n m El Er|t u n m t' u' El Er H].
    - eapply ralF_guard; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
    - eapply ralF_ret; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
    - eapply ralF_br; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
    - eapply ralF_vis; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
    - eapply ralF_stuck; [rewrite <- Et; exact El|rewrite <- Eu; exact Er].
    - eapply ralF_step; [rewrite <- Et; exact El|rewrite <- Eu; exact Er|exact H].
  Qed.

    Lemma ralignF_guards a b t u : ralignF t u -> ralignF (guards a t) (guards b u).
  Proof.
    intro H; destruct H as
      [t u n m t' u' El Er H|t u n m r r' El Er H|t u n m Y c k k' El Er H
      |t u n m Y e k k' El Er H|t u n m El Er|t u n m t' u' El Er H].
    - apply (ralF_guard _ _ (a + n) (b + m) t' u'); [|  |exact H];
        rewrite <- guards_shift; [rewrite El|rewrite Er]; reflexivity.
    - apply (ralF_ret _ _ (a + n) (b + m) r r'); [| |exact H];
        rewrite guards_add; [rewrite El|rewrite Er]; reflexivity.
    - apply (ralF_br _ _ (a + n) (b + m) c k k'); [| |exact H];
        rewrite guards_add; [rewrite El|rewrite Er]; reflexivity.
    - apply (ralF_vis _ _ (a + n) (b + m) e k k'); [| |exact H];
        rewrite guards_add; [rewrite El|rewrite Er]; reflexivity.
    - apply (ralF_stuck _ _ (a + n) (b + m));
        rewrite guards_add; [rewrite El|rewrite Er]; reflexivity.
    - apply (ralF_step _ _ (a + n) (b + m) t' u'); [| |exact H];
        rewrite guards_add; [rewrite El|rewrite Er]; reflexivity.
  Qed.

  (** Where a matched transition lands: an [R] pair or both sides stuck. *)
  Definition ralign_next (t u : ctree E B X) : Prop :=
    (exists t1 u1, t ≅ t1 /\ u ≅ u1 /\ R t1 u1) \/ (t ≅ Stuck /\ u ≅ Stuck).

  Hypothesis Hshape : forall t u, R t u -> ralignF t u.

  Local Ltac head_absurd H := step in H; cbn in H; inversion H.

  Local Ltac ralign_inv A :=
    inversion A as
      [left right n m tl tr El Er Hnext|left right n m r r' El Er Hr
      |left right n m Y c kk kk' El Er Hnext|left right n m Y e kk kk' El Er Hnext
      |left right n m El Er|left right n m tl tr El Er Hnext];
    subst; clear A.

  Lemma ralign_match l T U :
    trans_ l T U ->
    forall u, ralignF (go T) u ->
    exists l' u', trans l' u u' /\ simL RV l l' /\ ralign_next (go U) u'.
  Proof.
    intro TR; induction TR as
      [Y0 c0 pick k0 l target TR IH
      |inner target l TR IH
      |target result Eresult
      |Y0 e0 k0 answer result Eresult
      |value]; intros u A.
    - ralign_inv A.
      + head_absurd El.
      + destruct n; head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El.
        pose proof (equ_br_invT _ _ _ _ El) as HY; subst Y.
        pose proof (equ_br_invE _ _ _ _ El) as [Hc Ek]; subst c.
        assert (Ai : ralignF (go (observe (k0 pick))) (kk' pick)).
        { eapply ralignF_equ; [|reflexivity|exact (Hnext pick)].
          transitivity (k0 pick); [symmetry; exact (Ek pick)|apply ctree_eta]. }
        destruct (IH (kk' pick) Ai) as (l' & next & Tnext & HL & Anext).
        exists l', next; split; [|split; [exact HL|exact Anext]].
        rewrite Er; apply guards_trans; eapply trans_br; [exact Tnext|reflexivity].
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
    - ralign_inv A.
      + cbn [guards] in El; apply equ_guard_inv in El; destruct n as [|n].
        * cbn [guards] in El.
          assert (Ai : ralignF (go (observe inner)) tr).
          { eapply ralignF_equ; [|reflexivity|exact (Hshape _ _ Hnext)].
            transitivity inner; [symmetry; exact El|apply ctree_eta]. }
          destruct (IH tr Ai) as (l' & next & Tnext & HL & Anext).
          exists l', next; split; [rewrite Er; now apply guards_trans|split; assumption].
        * apply IH; eapply ralignF_equ; [apply ctree_eta|reflexivity|].
          eapply ralF_guard; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_inv in El.
        apply IH; eapply ralignF_equ; [apply ctree_eta|reflexivity|].
        eapply ralF_ret; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_inv in El.
        apply IH; eapply ralignF_equ; [apply ctree_eta|reflexivity|].
        eapply ralF_br; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_inv in El.
        apply IH; eapply ralignF_equ; [apply ctree_eta|reflexivity|].
        eapply ralF_vis; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_inv in El.
        apply IH; eapply ralignF_equ; [apply ctree_eta|reflexivity|].
        eapply ralF_stuck; eassumption.
      + destruct n as [|n]; [head_absurd El|].
        cbn [guards] in El; apply equ_guard_inv in El.
        apply IH; eapply ralignF_equ; [apply ctree_eta|reflexivity|].
        eapply ralF_step; eassumption.
    - ralign_inv A.
      + head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El; apply equ_step_inv in El.
        exists τ, tr; split; [rewrite Er; apply guards_trans, trans_step|].
        split; [constructor|left; exists tl, tr; split; [|split; [reflexivity|exact Hnext]]].
        rewrite <- ctree_eta, Eresult; exact El.
    - ralign_inv A.
      + head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El.
        pose proof (equ_vis_invT _ _ _ _ El) as HY; subst Y.
        pose proof (equ_vis_invE _ _ _ _ El) as [He Ek]; subst e.
        exists (obs e0 answer), (kk' answer); split; [rewrite Er; apply guards_trans, trans_vis|].
        split; [constructor|left; exists (kk answer), (kk' answer)].
        split; [|split; [reflexivity|exact (Hnext answer)]].
        rewrite <- ctree_eta, <- Eresult; exact (Ek answer).
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
    - ralign_inv A.
      + head_absurd El.
      + destruct n as [|n]; [|head_absurd El].
        cbn [guards] in El; apply equ_ret_inv in El; subst r.
        exists (val r'), Stuck; split; [rewrite Er; apply guards_trans, trans_ret|].
        split; [now constructor|right; split; reflexivity].
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
      + destruct n; head_absurd El.
  Qed.
End RAlign.

Local Lemma simL_flip {E X} (RV : X -> X -> Prop) l l' :
  simL (E:=E) (flip RV) l l' -> simL RV l' l.
Proof. intro H; destruct H; constructor; assumption. Qed.

Local Lemma ralignF_flip {E B X} RV R (t u : ctree E B X) :
  ralignF RV R t u -> ralignF (flip RV) (flip R) u t.
Proof.
  induction 1 as
    [t u n m t' u' El Er H|t u n m r r' El Er H|t u n m Y c k k' El Er H IH
    |t u n m Y e k k' El Er H|t u n m El Er|t u n m t' u' El Er H].
  - eapply ralF_guard; [exact Er|exact El|exact H].
  - eapply ralF_ret; [exact Er|exact El|exact H].
  - eapply ralF_br; [exact Er|exact El|exact IH].
  - eapply ralF_vis; [exact Er|exact El|exact H].
  - eapply ralF_stuck; [exact Er|exact El].
  - eapply ralF_step; [exact Er|exact El|exact H].
Qed.

(** Every invariant whose pairs align node by node is a bisimulation up to [RV]. *)
Theorem ralign_sbisim {E B X} (RV : X -> X -> Prop) (R : ctree E B X -> ctree E B X -> Prop) :
  (forall t u, R t u -> ralignF RV R t u) ->
  forall t u, R t u -> sbisim (simL RV) t u.
Proof.
  intro Hshape; unfold sbisim; coinduction r CIH; intros t u H; split.
  - intros l t' TR.
    assert (A : ralignF RV R (go (observe t)) u).
    { eapply ralignF_equ; [apply ctree_eta|reflexivity|apply Hshape, H]. }
    destruct (ralign_match RV R Hshape l _ _ TR u A) as (l' & u' & TR' & HL & Hn).
    exists l', u'; split; [exact TR'|split; [|exact HL]].
    destruct Hn as [(t1 & u1 & E1 & E2 & H1)|(E1 & E2)];
      rewrite <- ctree_eta in E1; rewrite E1, E2.
    + apply CIH, H1.
    + apply (b_chain r), is_stuck_sb; apply Stuck_is_stuck.
  - intros l u' TR.
    assert (A : ralignF (flip RV) (flip R) (go (observe u)) t).
    { eapply ralignF_equ; [apply ctree_eta|reflexivity|apply ralignF_flip, Hshape, H]. }
    assert (Hshape' : forall u t, flip R u t -> ralignF (flip RV) (flip R) u t).
    { intros u0 t0 H0; apply ralignF_flip, Hshape, H0. }
    destruct (ralign_match (flip RV) (flip R) Hshape' l _ _ TR t A) as (l' & t' & TR' & HL & Hn).
    exists l', t'; split; [exact TR'|split; [|apply simL_flip, HL]].
    destruct Hn as [(u1 & t1 & E1 & E2 & H1)|(E1 & E2)];
      rewrite <- ctree_eta in E1; cbn; rewrite E1, E2.
    + apply CIH, H1.
    + apply (b_chain r), is_stuck_sb; apply Stuck_is_stuck.
Qed.

(** ** Raw node equations of the original runner, guards kept *)

Local Abbreviation RHS := (interp_schedule_nd (@sh (nat * nat))).

Local Lemma rhs_empty (v : pool sE Bn 0) s : RHS 0 v None s ≅ Ret (s, tt).
Proof.
  unfold interp_schedule_nd.
  rewrite (ctree_eta (schedule 0 v None)), schedule_empty_none.
  rewrite interp_erase_ret, interp_state_ret; reflexivity.
Qed.

Local Lemma rhs_ret n (v : pool sE Bn (S n)) j s :
  observe (v $ j) = RetF tt -> RHS (S n) v (Some j) s ≅ Guard (RHS n (v -- j) None s).
Proof.
  intro H; unfold interp_schedule_nd.
  rewrite (ctree_eta (schedule (S n) v (Some j))), (schedule_focused_ret n v j H).
  rewrite interp_erase_guard, interp_state_guard; reflexivity.
Qed.

Local Lemma rhs_stuck n (v : pool sE Bn (S n)) j s :
  observe (v $ j) = StuckF -> RHS (S n) v (Some j) s ≅ Stuck.
Proof.
  intro H; unfold interp_schedule_nd.
  rewrite (ctree_eta (schedule (S n) v (Some j))), (schedule_focused_stuck n v j H).
  rewrite interp_erase_stuck, interp_state_stuck; reflexivity.
Qed.

Local Lemma rhs_step n (v : pool sE Bn (S n)) j t s :
  observe (v $ j) = StepF t ->
  RHS (S n) v (Some j) s ≅ Step (guards 3 (RHS (S n) (v @ j := t) (Some j) s)).
Proof.
  intro H; unfold interp_schedule_nd.
  rewrite (ctree_eta (schedule (S n) v (Some j))), (schedule_focused_step n v j t H).
  rewrite interp_erase_step, interp_state_step, !interp_state_guard; reflexivity.
Qed.

Local Lemma rhs_guard n (v : pool sE Bn (S n)) j t s :
  observe (v $ j) = GuardF t ->
  RHS (S n) v (Some j) s ≅ Guard (RHS (S n) (v @ j := t) (Some j) s).
Proof.
  intro H; unfold interp_schedule_nd.
  rewrite (ctree_eta (schedule (S n) v (Some j))), (schedule_focused_guard n v j t H).
  rewrite interp_erase_guard, interp_state_guard; reflexivity.
Qed.

Local Lemma rhs_yield n (v : pool sE Bn (S n)) j k s :
  observe (v $ j) = VisF (inl1 Yield) k ->
  RHS (S n) v (Some j) s ≅ Guard (RHS (S n) (v @ j := k tt) None s).
Proof.
  intro H; unfold interp_schedule_nd.
  rewrite (ctree_eta (schedule (S n) v (Some j))), (schedule_focused_yield n v j k H).
  rewrite interp_erase_guard, interp_state_guard; reflexivity.
Qed.

Local Lemma rhs_fork n (v : pool sE Bn (S n)) j k s :
  observe (v $ j) = VisF (inr1 (inl1 Fork)) k ->
  RHS (S n) v (Some j) s ≅
    Guard (RHS (S (S n)) (k true :: (v @ j := k false)) (Some (Fin.FS j)) s).
Proof.
  intro H; unfold interp_schedule_nd.
  rewrite (ctree_eta (schedule (S n) v (Some j))), (schedule_focused_fork n v j k H).
  rewrite interp_erase_spawn, interp_state_guard; reflexivity.
Qed.

Local Lemma rhs_user n (v : pool sE Bn (S n)) j {Y} (e : sE Y) k s :
  observe (v $ j) = VisF (inr1 (inr1 e)) k ->
  RHS (S n) v (Some j) s ≅
    (sh _ e s >>= fun sx => guards 3 (RHS (S n) (v @ j := k (snd sx)) (Some j) (fst sx))).
Proof.
  intro H; unfold interp_schedule_nd.
  rewrite (ctree_eta (schedule (S n) v (Some j))), (schedule_focused_user_event n v j e k H).
  rewrite interp_erase_user, interp_state_vis.
  apply equ_clo_bind_eq; intro sx; cbn [guards].
  rewrite !interp_state_guard; reflexivity.
Qed.

Local Lemma rhs_none n (v : pool sE Bn (S n)) s :
  RHS (S n) v None s ≅
    guards 2 (Br (branchn (S n)) (fun i => guards 3 (Step (guards 3 (RHS (S n) v (Some i) s))))).
Proof.
  unfold interp_schedule_nd.
  rewrite (ctree_eta (schedule (S n) v None)), schedule_no_focus_nonempty.
  rewrite interp_erase_yield, !interp_state_guard; cbn [guards].
  rewrite interp_erase_br, interp_state_br.
  change (Monad.bind (mbr ?c) ?f) with (CTree.bind (branch c : ctreeW (CSLObs (nat * nat)) Bn _) f).
  rewrite bind_branch.
  do 2 apply guard_equ_node; apply br_equ; intro i; cbn [guards].
  rewrite !interp_state_guard, interp_erase_step, interp_state_step, !interp_state_guard.
  reflexivity.
Qed.


Local Lemma erase_owned_equ t u : t ≅ u -> erase_owned t ≅ erase_owned u.
Proof. intro H; unfold erase_owned; rewrite H; reflexivity. Qed.

Local Lemma erase_owned_ret c : erase_owned (Ret c) ≅ Ret (joined_state c, tt).
Proof. unfold erase_owned; rewrite interp_ret_node, bind_ret_l; reflexivity. Qed.

Local Lemma erase_owned_stuck : erase_owned Stuck ≅ Stuck.
Proof. unfold erase_owned; rewrite interp_stuck_node, bind_stuck; reflexivity. Qed.

Local Lemma erase_owned_guard u : erase_owned (Guard u) ≅ Guard (erase_owned u).
Proof. unfold erase_owned; rewrite interp_guard_node, bind_guard; reflexivity. Qed.

Local Lemma erase_owned_step u : erase_owned (Step u) ≅ Step (Guard (erase_owned u)).
Proof. unfold erase_owned; rewrite interp_step_node, bind_step, bind_guard; reflexivity. Qed.

Local Lemma erase_owned_br {Y} (b : Bn Y) k :
  erase_owned (Br b k) ≅ Br b (fun x => Guard (erase_owned (k x))).
Proof.
  unfold erase_owned; rewrite interp_br_node, bind_br.
  apply br_equ; intro x; rewrite bind_guard; reflexivity.
Qed.

Local Lemma erase_owned_log a k :
  erase_owned (Vis (Log a) k) ≅
  match action_kind a with
  | OAEmit p idx =>
      Vis (Log (inr (stamp p idx) : CSLObs (nat * nat)))
        (fun _ => Guard (erase_owned (k tt)))
  | OAStep => Step (Guard (erase_owned (k tt)))
  | _ => Guard (erase_owned (k tt))
  end.
Proof.
  unfold erase_owned at 1; rewrite interp_vis_node, bind_bind.
  cbn [handle_owned]; destruct (action_kind a);
    try solve [rewrite bind_ret_l, bind_guard; reflexivity].
  - rewrite bind_step, bind_ret_l, bind_guard; reflexivity.
  - unfold log; rewrite bind_trigger.
    apply vis_equ_node; intros []; rewrite bind_guard; reflexivity.
Qed.

Local Abbreviation EI c := (erase_owned (instrument_owned c)).

Local Ltac ei_head H :=
  apply erase_owned_equ, observe_eq_equ;
  lazy [instrument_owned observe _observe set_pool mk_pool oc_pool];
  change (_observe (?v $ ?j)) with (observe (v $ j)); rewrite H; reflexivity.

Local Lemma ei_empty c (v : pool sE Bn 0) g :
  EI (set_pool c (mk_pool 0 v g None)) ≅ Ret (joined_state c, tt).
Proof.
  transitivity (erase_owned (Ret (set_pool c (mk_pool 0 v g None)))).
  - apply erase_owned_equ, observe_eq_equ; reflexivity.
  - rewrite erase_owned_ret; reflexivity.
Qed.

Local Lemma ei_none c n v g :
  EI (set_pool c (mk_pool (S n) v g None)) ≅
  Br (branchn (S n)) (fun j =>
    Guard (Step (guards 2 (EI (set_pool c (mk_pool (S n) v g (Some j))))))).
Proof.
  transitivity (erase_owned (Br (branchn (S n)) (fun j =>
    Step (Vis (Log (act (g $ j) OASelect))
      (fun _ => instrument_owned (set_pool c (mk_pool (S n) v g (Some j)))))))).
  - apply erase_owned_equ, observe_eq_equ; reflexivity.
  - rewrite erase_owned_br; apply br_equ; intro j; apply guard_equ_node.
    rewrite erase_owned_step, erase_owned_log; reflexivity.
Qed.

Local Lemma ei_ret c n v g j :
  observe (v $ j) = RetF tt ->
  EI (set_pool c (mk_pool (S n) v g (Some j))) ≅
  Guard (EI (set_pool c (mk_pool n (v -- j) (g -- j) None))).
Proof.
  intro H; transitivity (erase_owned (Vis (Log (act (g $ j) OAReturn))
    (fun _ => instrument_owned (set_pool c (mk_pool n (v -- j) (g -- j) None))))).
  - ei_head H.
  - rewrite erase_owned_log; reflexivity.
Qed.

Local Lemma ei_stuck c n v g j :
  observe (v $ j) = StuckF -> EI (set_pool c (mk_pool (S n) v g (Some j))) ≅ Stuck.
Proof.
  intro H; transitivity (erase_owned Stuck); [ei_head H|apply erase_owned_stuck].
Qed.

Local Lemma ei_step c n v g j t :
  observe (v $ j) = StepF t ->
  EI (set_pool c (mk_pool (S n) v g (Some j))) ≅
  Step (Guard (EI (set_pool c (mk_pool (S n) (v @ j := t) g (Some j))))).
Proof.
  intro H; transitivity (erase_owned (Vis (Log (act (g $ j) OAStep))
    (fun _ => instrument_owned (set_pool c (mk_pool (S n) (v @ j := t) g (Some j)))))).
  - ei_head H.
  - rewrite erase_owned_log; reflexivity.
Qed.

Local Lemma ei_guard c n v g j t :
  observe (v $ j) = GuardF t ->
  EI (set_pool c (mk_pool (S n) v g (Some j))) ≅
  Guard (EI (set_pool c (mk_pool (S n) (v @ j := t) g (Some j)))).
Proof.
  intro H; transitivity (erase_owned
    (Guard (instrument_owned (set_pool c (mk_pool (S n) (v @ j := t) g (Some j)))))).
  - ei_head H.
  - apply erase_owned_guard.
Qed.

Local Lemma ei_yield c n v g j k :
  observe (v $ j) = VisF (inl1 Yield) k ->
  EI (set_pool c (mk_pool (S n) v g (Some j))) ≅
  Guard (EI (set_pool c (mk_pool (S n) (v @ j := k tt) g None))).
Proof.
  intro H; transitivity (erase_owned (Vis (Log (act (g $ j) OAYield))
    (fun _ => instrument_owned (set_pool c (mk_pool (S n) (v @ j := k tt) g None))))).
  - ei_head H.
  - rewrite erase_owned_log; reflexivity.
Qed.

Local Lemma ei_fork c n v g j k :
  observe (v $ j) = VisF (inr1 (inl1 Fork)) k ->
  EI (set_pool c (mk_pool (S n) v g (Some j))) ≅
  Guard (EI (set_pool c (mk_pool (S (S n)) (k true :: (v @ j := k false)) ((g $ j) :: g)
    (Some (Fin.FS j))))).
Proof.
  intro H; transitivity (erase_owned (Vis (Log (act (g $ j) OAFork))
    (fun _ => instrument_owned (set_pool c
      (mk_pool (S (S n)) (k true :: (v @ j := k false)) ((g $ j) :: g) (Some (Fin.FS j))))))).
  - ei_head H.
  - rewrite erase_owned_log; reflexivity.
Qed.

Local Lemma ei_prim c n v g j {Y} (e : sE Y) k :
  observe (v $ j) = VisF (inr1 (inr1 e)) k ->
  EI (set_pool c (mk_pool (S n) v g (Some j))) ≅
  erase_owned (match prim_step (g $ j) (set_pool c (mk_pool (S n) v g (Some j))) e with
    | Some (kind, y, c1) =>
        Vis (Log (act (g $ j) kind))
          (fun _ => instrument_owned (set_pool c1 (mk_pool (S n) (v @ j := k y) g (Some j))))
    | None => Stuck
    end).
Proof. intro H; ei_head H. Qed.

(** ** Primitive reflection on the joined heap *)

(** The runner's state is the joined owned state, heaps up to [≈]. *)
Definition state_rel (s : SSig) (c : OwnedCfg) : Prop :=
  snd s = (oc_ctx c, global_count c) /\ fst s ≈ joined_heap c.

(** A cell or token inside its owner's reservation is looked up in the
    joined heap exactly as in the owner's heap. *)
Lemma joined_lookup c i a :
  owned_wf c -> fst (oc_anchor c i) a <> None -> fst (joined_heap c) a = fst (oc_heap c i) a.
Proof.
  intros (_ & _ & _ & _ & [Dr _] & [SC _] & [SP _] & _) Ha; cbn.
  unfold hunion; destruct i.
  - destruct (fst (oc_heap c Child) a) eqn:Ec; [reflexivity|].
    destruct (fst (oc_heap c Parent) a) eqn:Ep; [|reflexivity].
    exfalso; destruct (Dr a); [contradiction|].
    apply (SP a); congruence.
  - destruct (fst (oc_heap c Child) a) eqn:Ec; [|reflexivity].
    exfalso; destruct (Dr a); [|contradiction].
    apply (SC a); congruence.
Qed.

Lemma joined_token c i b :
  owned_wf c -> snd (oc_anchor c i) b <> None -> snd (joined_heap c) b = snd (oc_heap c i) b.
Proof.
  intros (_ & _ & _ & _ & [_ Dr] & [_ SC] & [_ SP] & _) Ha; cbn.
  unfold hunion; destruct i.
  - destruct (snd (oc_heap c Child) b) eqn:Ec; [reflexivity|].
    destruct (snd (oc_heap c Parent) b) eqn:Ep; [|reflexivity].
    exfalso; destruct (Dr b); [contradiction|].
    apply (SP b); congruence.
  - destruct (snd (oc_heap c Child) b) eqn:Ec; [|reflexivity].
    exfalso; destruct (Dr b); [|contradiction].
    apply (SC b); congruence.
Qed.

(** Writing an owned cell commutes with joining. *)
Lemma joined_write c i a v :
  owned_wf c -> fst (oc_heap c i) a <> None ->
  joined_heap (set_heap c i (upd (fst (oc_heap c i)) a v, snd (oc_heap c i))) ≈
    (upd (fst (joined_heap c)) a v, snd (joined_heap c)).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & [Dh _]) Ha.
  destruct i; split; intro x; cbn; unfold hunion, upd;
    destruct (Nat.eqb_spec x a) as [->|]; try reflexivity.
  destruct (fst (oc_heap c Child) a) eqn:Ec; [|reflexivity].
  exfalso; destruct (Dh a); congruence.
Qed.

Lemma global_count_emit c i p : global_count (emit_cfg c i p) = S (global_count c).
Proof. destruct i; unfold global_count, emit_cfg, side_upd; cbn; lia. Qed.

(** Freeing an owned block commutes with joining. *)
Lemma joined_free c i b m' :
  owned_wf c -> managed_free (oc_heap c i) b = Some m' ->
  exists J, managed_free (joined_heap c) b = Some J /\ J ≈ joined_heap (set_heap c i m').
Proof.
  intros (WC & WP & _ & _ & _ & _ & _ & Dh) Hf; destruct i.
  - destruct (managed_free_pop _ _ _ _ Dh WC Hf) as [(J & HJ & EJ) _].
    exists J; split; [exact HJ|exact EJ].
  - pose proof (pdef_comm _ _ Dh) as Dh'.
    destruct (managed_free_pop _ _ _ _ Dh' WP Hf) as [(J & HJ & EJ) D'].
    destruct (managed_free_peq _ _ _ _ (pop_comm _ _ Dh') HJ) as (J' & HJ' & EJ').
    exists J'; split; [exact HJ'|].
    eapply peq_trans; [apply peq_sym, EJ'|].
    eapply peq_trans; [exact EJ|apply pop_comm, D'].
Qed.

(** A free that faults in its owner's reservation faults in the joined heap. *)
Lemma joined_free_none c i b :
  owned_wf c -> snd (oc_anchor c i) b <> None -> managed_free (oc_heap c i) b = None ->
  managed_free (joined_heap c) b = None.
Proof.
  intros W Hb Hf; unfold managed_free in *.
  destruct (Nat.eqb b 0); [discriminate|].
  rewrite (joined_token c i b W Hb).
  destruct (snd (oc_heap c i) b) as [[|n]|]; congruence.
Qed.

Local Lemma managed_free_none_peq m m' b :
  m ≈ m' -> managed_free m b = None -> managed_free m' b = None.
Proof.
  intros E H; destruct (managed_free m' b) as [m1|] eqn:H'; [|reflexivity].
  destruct (managed_free_peq _ _ _ _ (peq_sym _ _ E) H') as (m2 & H2 & _); congruence.
Qed.

Local Lemma state_lookup s c i a :
  owned_wf c -> state_rel s c -> fst (oc_anchor c i) a <> None ->
  fst (fst s) a = fst (oc_heap c i) a.
Proof.
  intros W [_ [Eh _]] Ha; rewrite (Eh a); exact (joined_lookup c i a W Ha).
Qed.

(** One primitive of lineage [i]: the runner's handler agrees with
    [prim_step] on success and on fault. *)
Lemma prim_reflect i c {Y} (e : sE Y) s :
  owned_wf c -> state_rel s c -> component_event_ok Y e -> prim_addr_ok (oc_anchor c i) e ->
  match prim_step i c e with
  | Some (kind, y, c1) => exists s', state_rel s' c1 /\
      match kind with
      | OAEmit p idx => sh _ e s ≅ (log (inr (stamp p idx) : CSLObs (nat * nat));; Ret (s', y))
      | OAStep => False
      | _ => sh _ e s ≅ Ret (s', y)
      end
  | None => sh _ e s ≅ Stuck
  end.
Proof.
  intros W Hs Hok Ha.
  pose proof Hs as [Hs1 Hs2].
  destruct e as [he|[se|we]]; [destruct he as [a|a v|size|b|a ex de]|destruct se|destruct we as [p]];
    cbn in Hok, Ha |- *; try contradiction.
  - rewrite (state_lookup s c i a W Hs Ha).
    destruct (fst (oc_heap c i) a); [exists s; split; [exact Hs|reflexivity]|reflexivity].
  - rewrite (state_lookup s c i a W Hs Ha).
    destruct (fst (oc_heap c i) a) eqn:Ea; [|reflexivity].
    eexists; split; [|reflexivity]; split; [exact Hs1|].
    eapply peq_trans; [|apply peq_sym, joined_write; [exact W|congruence]].
    split; [apply upd_heq, Hs2|apply Hs2].
  - destruct Ha as [->|Hb].
    + exists s; split; [destruct i; exact Hs|destruct s; reflexivity].
    + destruct (managed_free (oc_heap c i) b) as [m'|] eqn:Hf.
      * destruct (joined_free c i b m' W Hf) as (J & HJ & EJ).
        destruct (managed_free_peq _ _ _ _ (peq_sym _ _ Hs2) HJ) as (J' & HJ' & EJ').
        rewrite HJ'; eexists; split; [|reflexivity]; split; [exact Hs1|].
        eapply peq_trans; [apply peq_sym, EJ'|exact EJ].
      * rewrite (managed_free_none_peq _ _ b (peq_sym _ _ Hs2) (joined_free_none c i b W Hb Hf)).
        reflexivity.
  - rewrite (state_lookup s c i a W Hs Ha).
    destruct (fst (oc_heap c i) a) as [cur|] eqn:Ea; [|reflexivity].
    destruct (Nat.eqb cur ex).
    + eexists; split; [|reflexivity]; split; [exact Hs1|].
      eapply peq_trans; [|apply peq_sym, joined_write; [exact W|congruence]].
      split; [apply upd_heq, Hs2|apply Hs2].
    + exists s; split; [exact Hs|reflexivity].
  - exists s; split; [exact Hs|].
    unfold csl_context; rewrite Hs1; reflexivity.
  - destruct s as [m [ctx cnt]]; cbn in Hs1; injection Hs1 as -> ->.
    eexists; split; [|reflexivity]; split; [rewrite global_count_emit; reflexivity|exact Hs2].
Qed.

(** ** The erasure invariant along the machine *)

Local Definition thread_ok (t : thread sE Bn) : Prop :=
  Framable (okE_thread component_event_ok) t /\ BranchFree t.

Local Lemma thread_ok_equ t u : t ≅ u -> thread_ok t -> thread_ok u.
Proof.
  intros E [F Bf]; split.
  - exact (proj1 (framable_chain_equ _ (R := chain_gfp _) t u E) F).
  - rewrite <- E; exact Bf.
Qed.

Local Lemma thread_ok_guards n t u : t ≅ guards n u -> thread_ok t -> thread_ok u.
Proof.
  revert t; induction n as [|n IH]; intros t E H; cbn [guards] in E.
  - exact (thread_ok_equ _ _ E H).
  - apply thread_ok_equ with (u := Guard (guards n u)) in H; [|exact E].
    destruct H as [F Bf]; apply framable_unfold in F; apply branchfree_unfold in Bf.
    cbn in F, Bf; inversion F; inversion Bf; subst.
    apply (IH (guards n u)); [reflexivity|split; assumption].
Qed.

Local Lemma thread_ok_headed t u : headed t u -> thread_ok t -> thread_ok u.
Proof. intros [n E]; exact (thread_ok_guards n t u E). Qed.

Local Lemma thread_ok_step t : thread_ok (Step t) -> thread_ok t.
Proof.
  intros [F Bf]; apply framable_unfold in F; apply branchfree_unfold in Bf.
  cbn in F, Bf; inversion F; inversion Bf; subst; split; assumption.
Qed.

Local Lemma thread_ok_vis {Y} (e : CEff Y) k x : thread_ok (Vis e k) -> thread_ok (k x).
Proof.
  intros [F Bf]; apply framable_unfold in F; apply branchfree_unfold in Bf.
  cbn in F, Bf; dependent destruction F; dependent destruction Bf; split; auto.
Qed.

Local Lemma thread_ok_vis_ok {Y} (e : sE Y) k :
  thread_ok (Vis (inr1 (inr1 e) : CEff Y) k) -> component_event_ok Y e.
Proof.
  intros [F _]; apply framable_unfold in F; cbn in F; dependent destruction F; exact H.
Qed.

Local Definition pool_ok {n} (v : pool sE Bn n) : Prop :=
  pool_framable component_event_ok v /\ pool_branchfree v.

Local Lemma pool_ok_nth {n} (v : pool sE Bn n) j : pool_ok v -> thread_ok (v $ j).
Proof. intros [F Bf]; split; [apply F|apply Bf]. Qed.

Local Lemma pool_ok_replace {n} (v : pool sE Bn n) j t : pool_ok v -> thread_ok t -> pool_ok (v @ j := t).
Proof.
  intros [F Bf] [Ft Bt]; split;
    [apply pool_framable_replace|apply pool_branchfree_replace]; assumption.
Qed.

Local Lemma pool_ok_remove {n} (v : pool sE Bn (S n)) j : pool_ok v -> pool_ok (v -- j).
Proof.
  intros [F Bf]; split; [apply pool_framable_remove|apply pool_branchfree_remove]; assumption.
Qed.

Local Lemma pool_ok_cons {n} t (v : pool sE Bn n) : thread_ok t -> pool_ok v -> pool_ok (t :: v).
Proof.
  intros [Ft Bt] [F Bf]; split; [apply pool_framable_cons|apply pool_branchfree_cons]; assumption.
Qed.

Local Lemma set_pool_eta c : set_pool c (oc_pool c) = c.
Proof. destruct c; reflexivity. Qed.

Local Lemma pool_ok_step c a c' :
  pool_ok (tp_threads (oc_pool c)) -> owned_step c a c' -> pool_ok (tp_threads (oc_pool c')).
Proof.
  destruct c as [[n v g [j|]] an hp ctx base cnt last]; intros Hp Hs;
    destruct n as [|n]; cbn in Hs; try contradiction.
  - destruct Hs as [(t & Hh & -> & ->)|[(k & Hh & -> & ->)|[(k & Hh & -> & ->)
      |[(Hh & -> & ->)|(Y & e & k & kind & y & c1 & Hh & Hpr & -> & ->)]]]]; cbn;
      pose proof (thread_ok_headed _ _ Hh (pool_ok_nth _ j Hp)) as Ht.
    + apply pool_ok_replace; [exact Hp|apply thread_ok_step, Ht].
    + apply pool_ok_replace; [exact Hp|apply (thread_ok_vis _ _ _ Ht)].
    + apply pool_ok_cons; [apply (thread_ok_vis _ _ _ Ht)|].
      apply pool_ok_replace; [exact Hp|apply (thread_ok_vis _ _ _ Ht)].
    + apply pool_ok_remove, Hp.
    + apply pool_ok_replace; [exact Hp|apply (thread_ok_vis _ _ _ Ht)].
  - destruct Hs as (j & -> & ->); exact Hp.
Qed.

Lemma erasable_step c a c' : erasable c -> owned_step c a c' -> erasable c'.
Proof.
  intros (W & F & Bf & Cf) Hs.
  destruct (pool_ok_step c a c' (conj F Bf) Hs) as [F' Bf'].
  split; [exact (owned_step_wf _ _ _ W Hs)|split; [exact F'|split; [exact Bf'|]]].
  intros d Hd; apply Cf; eapply rt_trans; [apply rt_step; exists a; exact Hs|exact Hd].
Qed.

(** *** Forgetting a guard of the focused slot *)

Local Lemma vector_remove_replace {A n} (v : Vector.t A (S n)) j x :
  vector_remove (Vector.replace v j x) j = vector_remove v j.
Proof.
  revert v j; induction n as [|n IH]; intros v j;
    dependent destruction v; dependent destruction j; cbn [Vector.replace Vector.caseS' Vector.caseS].
  - rewrite !vector_remove_head; reflexivity.
  - inversion j.
  - rewrite !vector_remove_head; reflexivity.
  - rewrite !vector_remove_tail, IH; reflexivity.
Qed.

Local Lemma headed_guard t t' u : t ≅ Guard t' -> headed t' u -> headed t u.
Proof. intros E [n Hn]; exists (S n); cbn [guards]; rewrite E; apply guard_equ_node, Hn. Qed.

Local Lemma prim_step_repool i c p q {Y} (e : sE Y) kind y c1 :
  prim_step i (set_pool c p) e = Some (kind, y, c1) ->
  prim_step i (set_pool c q) e = Some (kind, y, set_pool c1 q).
Proof.
  destruct e as [he|[se|we]]; [destruct he as [a|a v|size|b|a ex de]|destruct se|destruct we];
    cbn; intro H; try discriminate.
  - destruct (fst (oc_heap c i) a); [|discriminate]; injection H as <- <- <-; reflexivity.
  - destruct (fst (oc_heap c i) a); [|discriminate]; injection H as <- <- <-; reflexivity.
  - destruct (managed_free (oc_heap c i) b); [|discriminate]; injection H as <- <- <-; reflexivity.
  - destruct (fst (oc_heap c i) a); [|discriminate].
    destruct (Nat.eqb _ ex); injection H as <- <- <-; reflexivity.
  - injection H as <- <- <-; reflexivity.
  - injection H as <- <- <-; reflexivity.
Qed.

(** Forgetting a leading guard of the focused slot keeps every action. *)
Local Lemma strip_step c n v g j t a d :
  observe (v $ j) = GuardF t ->
  owned_step (set_pool c (mk_pool (S n) (v @ j := t) g (Some j))) a d ->
  owned_step (set_pool c (mk_pool (S n) v g (Some j))) a d.
Proof.
  intros H Hs; pose proof (observe_equ_go _ _ H) as E.
  change (focus_step (set_pool c (mk_pool (S n) (v @ j := t) g (Some j))) n (v @ j := t) g j a d) in Hs.
  change (focus_step (set_pool c (mk_pool (S n) v g (Some j))) n v g j a d).
  unfold focus_step in Hs |- *; rewrite Vector.nth_replace_eq in Hs.
  destruct Hs as [(t1 & Hh & -> & ->)|[(k & Hh & -> & ->)|[(k & Hh & -> & ->)
    |[(Hh & -> & ->)|(Y & e & k & kind & y & c1 & Hh & Hpr & -> & ->)]]]];
    pose proof (headed_guard _ _ _ E Hh) as Hh'.
  - left; exists t1; split; [exact Hh'|split; [reflexivity|]].
    rewrite Vector.replace_replace_eq; reflexivity.
  - right; left; exists k; split; [exact Hh'|split; [reflexivity|]].
    rewrite Vector.replace_replace_eq; reflexivity.
  - right; right; left; exists k; split; [exact Hh'|split; [reflexivity|]].
    rewrite Vector.replace_replace_eq; reflexivity.
  - right; right; right; left; split; [exact Hh'|split; [reflexivity|]].
    rewrite vector_remove_replace; reflexivity.
  - right; right; right; right.
    exists Y, e, k, kind, y, (set_pool c1 (mk_pool (S n) v g (Some j))).
    split; [exact Hh'|split; [exact (prim_step_repool _ _ _ _ _ _ _ _ Hpr)|split; [reflexivity|]]].
    rewrite Vector.replace_replace_eq; reflexivity.
Qed.

Local Lemma strip_head_confined c n v g j t :
  observe (v $ j) = GuardF t ->
  head_confined (set_pool c (mk_pool (S n) v g (Some j))) ->
  head_confined (set_pool c (mk_pool (S n) (v @ j := t) g (Some j))).
Proof.
  intros H Hc t0 i Y e k Hf Hh; cbn in Hf; rewrite Vector.nth_replace_eq in Hf.
  injection Hf as <- <-.
  apply (Hc (v $ j) (g $ j) Y e k eq_refl).
  exact (headed_guard _ _ _ (observe_equ_go _ _ H) Hh).
Qed.

Lemma erasable_guard c n v g j t :
  observe (v $ j) = GuardF t ->
  erasable (set_pool c (mk_pool (S n) v g (Some j))) ->
  erasable (set_pool c (mk_pool (S n) (v @ j := t) g (Some j))).
Proof.
  intros H (W & F & Bf & Cf).
  destruct (pool_ok_replace v j t (conj F Bf)) as [F' Bf'].
  { apply (thread_ok_guards 1 (v $ j)); [exact (observe_equ_go _ _ H)|exact (pool_ok_nth v j (conj F Bf))]. }
  split; [exact W|split; [exact F'|split; [exact Bf'|]]].
  intros d Hd; apply clos_rt_rt1n in Hd; destruct Hd as [|d1 d2 [a Ha] Hrest].
  - apply (strip_head_confined _ _ _ _ _ _ H), Cf, rt_refl.
  - apply Cf; eapply rt_trans; [apply rt_step; exists a; eapply strip_step; eassumption|].
    apply clos_rt1n_rt, Hrest.
Qed.

(** ** Erasure *)

Local Lemma headed_obs t ot : observe t = ot -> headed t (go ot).
Proof. intro H; exists 0; exact (observe_equ_go _ _ H). Qed.

(** Pairs of guard-padded erasures and runners of one erasable
    configuration, its state joined up to [≈]. *)
Local Definition erase_rel (t u : ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)) : Prop :=
  exists c s a b, erasable c /\ state_rel s c /\
    t ≅ guards a (EI c) /\
    u ≅ guards b (RHS (tp_size (oc_pool c)) (tp_threads (oc_pool c)) (tp_focus (oc_pool c)) s).

Local Ltac erase_next c' s' a b :=
  exists c', s', a, b; split; [|split; [|split; reflexivity]].

Local Lemma erase_shape c p s :
  erasable (set_pool c p) -> state_rel s c ->
  ralignF owned_result_rel erase_rel (EI (set_pool c p)) (RHS (tp_size p) (tp_threads p) (tp_focus p) s).
Proof.
  intros He Hs; pose proof He as (W & F & Bf & Cf).
  destruct p as [[|n] v g [j|]]; cbn [tp_size tp_threads tp_focus] in *.
  - inversion j.
  - apply (ralF_ret _ _ _ _ 0 0 (joined_state c, tt) (s, tt));
      [apply (ei_empty c v g)|apply rhs_empty|].
    change (tt = tt /\ snd (joined_state c) = snd s /\ csl_memory (joined_state c) ≈ csl_memory s).
    split; [reflexivity|split; [symmetry; apply Hs|apply peq_sym, Hs]].
  - pose proof (pool_ok_nth v j (conj F Bf)) as Ht.
    destruct (observe (v $ j)) as [[]| |t|t|Y e k|Y b k] eqn:H.
    + apply (ralF_guard _ _ _ _ 0 0 _ _ (ei_ret c n v g j H) (rhs_ret n v j s H)).
      erase_next (set_pool c (mk_pool n (v -- j) (g -- j) None)) s 0 0; [|exact Hs].
      eapply erasable_step; [exact He|].
      right; right; right; left; split; [exact (headed_obs _ _ H)|split; reflexivity].
    + exact (ralF_stuck _ _ _ _ 0 0 (ei_stuck c n v g j H) (rhs_stuck n v j s H)).
    + apply (ralF_step _ _ _ _ 0 0 _ _ (ei_step c n v g j t H) (rhs_step n v j t s H)).
      erase_next (set_pool c (mk_pool (S n) (v @ j := t) g (Some j))) s 1 3; [|exact Hs].
      eapply erasable_step; [exact He|].
      left; exists t; split; [exact (headed_obs _ _ H)|split; reflexivity].
    + apply (ralF_guard _ _ _ _ 0 0 _ _ (ei_guard c n v g j t H) (rhs_guard n v j t s H)).
      erase_next (set_pool c (mk_pool (S n) (v @ j := t) g (Some j))) s 0 0; [|exact Hs].
      exact (erasable_guard c n v g j t H He).
    + destruct e as [y|[fk|e]]; [destruct y|destruct fk|].
      * apply (ralF_guard _ _ _ _ 0 0 _ _ (ei_yield c n v g j k H) (rhs_yield n v j k s H)).
        erase_next (set_pool c (mk_pool (S n) (v @ j := k tt) g None)) s 0 0; [|exact Hs].
        eapply erasable_step; [exact He|].
        right; left; exists k; split; [exact (headed_obs _ _ H)|split; reflexivity].
      * apply (ralF_guard _ _ _ _ 0 0 _ _ (ei_fork c n v g j k H) (rhs_fork n v j k s H)).
        erase_next (set_pool c (mk_pool (S (S n)) (k true :: (v @ j := k false)) ((g $ j) :: g)
          (Some (Fin.FS j)))) s 0 0; [|exact Hs].
        eapply erasable_step; [exact He|].
        right; right; left; exists k; split; [exact (headed_obs _ _ H)|split; reflexivity].
      * assert (Hok : component_event_ok Y e).
        { apply (thread_ok_vis_ok e k), (thread_ok_equ (v $ j)); [exact (observe_equ_go _ _ H)|exact Ht]. }
        assert (Ha : prim_addr_ok (oc_anchor c (g $ j)) e).
        { exact (Cf _ (rt_refl _ _ _) (v $ j) (g $ j) Y e k eq_refl (headed_obs _ _ H)). }
        pose proof (prim_reflect (g $ j) (set_pool c (mk_pool (S n) v g (Some j))) e s W Hs Hok Ha) as Hr.
        eapply ralignF_equ; [symmetry; apply (ei_prim c n v g j e k H)|symmetry; apply (rhs_user n v j e k s H)|].
        destruct (prim_step (g $ j) (set_pool c (mk_pool (S n) v g (Some j))) e)
          as [[[kind y] c1]|] eqn:Hp.
        -- destruct Hr as (s' & Hs' & Hr).
           assert (Hc1 : erasable (set_pool c1 (mk_pool (S n) (v @ j := k y) g (Some j)))).
           { eapply erasable_step; [exact He|].
             right; right; right; right; exists Y, e, k, kind, y, c1.
             split; [exact (headed_obs _ _ H)|split; [exact Hp|split; reflexivity]]. }
           destruct kind as [| | | | | | | | | |q idx]; cbn in Hr; try contradiction;
             try (apply (ralF_guard _ _ _ _ 0 2
                    (EI (set_pool c1 (mk_pool (S n) (v @ j := k y) g (Some j))))
                    (RHS (S n) (v @ j := k y) (Some j) s'));
                  [rewrite erase_owned_log; reflexivity|rewrite Hr, bind_ret_l; reflexivity|];
                  erase_next (set_pool c1 (mk_pool (S n) (v @ j := k y) g (Some j))) s' 0 0;
                  [exact Hc1|exact Hs']).
           apply (ralF_vis _ _ _ _ 0 0 (Log (inr (stamp q idx) : CSLObs (nat * nat)))
             (fun _ => Guard (EI (set_pool c1 (mk_pool (S n) (v @ j := k y) g (Some j)))))
             (fun _ => guards 3 (RHS (S n) (v @ j := k y) (Some j) s'))).
           ++ rewrite erase_owned_log; reflexivity.
           ++ rewrite Hr, bind_bind; unfold log; rewrite bind_trigger.
              cbn [guards]; apply vis_equ_node; intro x; rewrite bind_ret_l; reflexivity.
           ++ intros _; erase_next (set_pool c1 (mk_pool (S n) (v @ j := k y) g (Some j))) s' 1 3;
                [exact Hc1|exact Hs'].
        -- apply (ralF_stuck _ _ _ _ 0 0); [apply erase_owned_stuck|].
           rewrite Hr, bind_stuck; reflexivity.
    + exfalso; destruct Ht as [_ Hb]; apply branchfree_unfold in Hb; rewrite H in Hb; inversion Hb.
  - apply (ralF_br _ _ _ _ 0 2 _ _ _ (ei_none c n v g) (rhs_none n v s)).
    intro i; apply (ralF_step _ _ _ _ 1 3 _ _ (reflexivity _) (reflexivity _)).
    erase_next (set_pool c (mk_pool (S n) v g (Some i))) s 2 3; [|exact Hs].
    eapply erasable_step; [exact He|]; exists i; split; reflexivity.
Qed.

Theorem owned_erasure (c : OwnedCfg) :
  erasable c ->
  sbisim (simL owned_result_rel)
    (erase_owned (instrument_owned c))
    (interp_schedule_nd sh (tp_size (oc_pool c)) (tp_threads (oc_pool c))
       (tp_focus (oc_pool c)) (joined_state c)).
Proof.
  intro He; apply (ralign_sbisim owned_result_rel erase_rel).
  - intros t u (c0 & s & a & b & He0 & Hs & Et & Eu).
    rewrite <- (set_pool_eta c0) in He0.
    pose proof (erase_shape c0 (oc_pool c0) s He0 Hs) as Hsh; rewrite set_pool_eta in Hsh.
    eapply ralignF_equ; [symmetry; exact Et|symmetry; exact Eu|].
    apply ralignF_guards, Hsh.
  - exists c, (joined_state c), 0, 0; split; [exact He|split; [|split; reflexivity]].
    split; [reflexivity|apply peq_refl].
Qed.

(** ** Admission and coupling give erasability *)

Local Lemma denote_thread_ok p : component_ok p -> thread_ok (denote p).
Proof.
  intro Hp; split; [|apply denote_branchfree].
  unfold denote; apply framable_bind; [apply denote_flow_framable, Hp|intro; apply fr_ret].
Qed.

Lemma admissible_erasable child parent h h' ctx base :
  admissible child parent h h' ctx base -> erasable (init_owned child parent h h' ctx base).
Proof.
  intro Ha; pose proof Ha as (Wh & Wh' & D & Oc & Op & _).
  assert (Hp : pool_ok [denote child; denote parent]).
  { apply pool_ok_cons; [apply denote_thread_ok, Oc|].
    apply pool_ok_cons; [apply denote_thread_ok, Op|split; intro i; inversion i]. }
  destruct Hp as [F Bf].
  split; [apply init_owned_wf; assumption|split; [exact F|split; [exact Bf|]]].
  intros d Hd; exact (admissible_head_confined _ _ _ _ _ _ _ Ha Hd).
Qed.

Lemma erasable_reach c d : erasable c -> clos_refl_trans _ owned_next c d -> erasable d.
Proof.
  intros He H; induction H as [x y [a Ha]|x|x y z _ IH1 _ IH2];
    [exact (erasable_step x a y He Ha)|exact He|exact (IH2 (IH1 He))].
Qed.

Local Lemma Forall2_nth_error_r {A B} (P : A -> B -> Prop) l1 l2 k y :
  List.Forall2 P l1 l2 -> List.nth_error l2 k = Some y ->
  exists x, List.nth_error l1 k = Some x /\ P x y.
Proof.
  intro H; revert k; induction H as [|x0 y0 l1 l2 Hxy _ IH]; intros [|k] Hk; cbn in *;
    try discriminate; [injection Hk as <-; eauto|eauto].
Qed.

(** Every slot of [q] has an equivalent slot at the same position in [p]. *)
Lemma tp_equ_slot p q (j : Fin.t (tp_size q)) :
  tp_equ p q ->
  exists j0 : Fin.t (tp_size p), fin_nat j0 = fin_nat j /\
    (tp_threads p $ j0) ≅ (tp_threads q $ j) /\ (tp_tags p $ j0) = (tp_tags q $ j).
Proof.
  intros [HF _].
  destruct (Forall2_nth_error_r _ _ _ _ _ HF (tp_slots_nth_error q j)) as ([t s] & Hn & [Ht Hs]).
  assert (Hlt : fin_nat j < tp_size p).
  { rewrite <- tp_slots_length; apply List.nth_error_Some; congruence. }
  assert (Hj0 : fin_nat (Fin.of_nat_lt Hlt) = fin_nat j).
  { unfold fin_nat; rewrite Fin.to_nat_of_nat; reflexivity. }
  exists (Fin.of_nat_lt Hlt); split; [exact Hj0|].
  pose proof (tp_slots_nth_error p (Fin.of_nat_lt Hlt)) as Hp; rewrite Hj0, Hn in Hp.
  injection Hp as -> ->; split; assumption.
Qed.

Local Lemma prim_addr_ok_peq r r' {Y} (e : sE Y) : r ≈ r' -> prim_addr_ok r e -> prim_addr_ok r' e.
Proof.
  intros [E1 E2]; destruct e as [he|]; [destruct he as [a|a v|size|b|a ex de]|]; cbn; try tauto.
  - now rewrite <- (E1 a).
  - now rewrite <- (E1 a).
  - now rewrite <- (E2 b).
  - now rewrite <- (E1 a).
Qed.

Local Lemma head_confined_equ c d : owned_equ c d -> head_confined c -> head_confined d.
Proof.
  intros (Ep & Ea & _) Hc t i Y e k Hf Hh.
  unfold focused_thread in Hf; destruct (tp_focus (oc_pool d)) as [j|] eqn:Hj; [|discriminate].
  injection Hf as <- <-.
  destruct (tp_equ_slot (oc_pool c) (oc_pool d) j Ep) as (j0 & Hn & Et & Eg).
  assert (Hfc : tp_focus (oc_pool c) = Some j0).
  { destruct Ep as [_ Hfn]; unfold focus_nat in Hfn; rewrite Hj in Hfn.
    destruct (tp_focus (oc_pool c)) as [j1|]; cbn in Hfn; [|discriminate].
    injection Hfn as Hfn; f_equal; apply Fin.to_nat_inj; unfold fin_nat in *; congruence. }
  apply (prim_addr_ok_peq (oc_anchor c (tp_tags (oc_pool d) $ j))); [apply Ea|].
  rewrite <- Eg; apply (Hc (tp_threads (oc_pool c) $ j0) _ Y e k).
  - unfold focused_thread; rewrite Hfc; reflexivity.
  - eapply headed_equ; [symmetry; exact Et|exact Hh].
Qed.

Local Lemma reach_equ a b x :
  owned_equ a b -> clos_refl_trans _ owned_next a x ->
  exists y, clos_refl_trans _ owned_next b y /\ owned_equ x y.
Proof.
  intros E H; revert b E; induction H as [x y Hxy|x|x y z _ IH1 _ IH2]; intros b E.
  - destruct (owned_next_equ x b y E Hxy) as (y' & H' & E').
    exists y'; split; [apply rt_step, H'|exact E'].
  - exists b; split; [apply rt_refl|exact E].
  - destruct (IH1 b E) as (y' & H1 & E1); destruct (IH2 y' E1) as (z' & H2 & E2).
    exists z'; split; [eapply rt_trans; eassumption|exact E2].
Qed.

Lemma erasable_equ c d : owned_equ c d -> erasable c -> erasable d.
Proof.
  intros E (W & F & Bf & Cf).
  assert (Hd : forall j, thread_ok (tp_threads (oc_pool d) $ j)).
  { intro j; destruct (tp_equ_slot _ _ j (proj1 E)) as (j0 & _ & Et & _).
    exact (thread_ok_equ _ _ Et (pool_ok_nth _ j0 (conj F Bf))). }
  split; [exact (owned_wf_equ c d E W)|split; [intro j; apply Hd|split; [intro j; apply Hd|]]].
  intros x Hx; destruct (reach_equ d c x (symmetry E) Hx) as (y & Hy & Exy).
  exact (head_confined_equ y x (symmetry Exy) (Cf y Hy)).
Qed.

Lemma coupled_erasable c : coupled c -> erasable c.
Proof.
  intros (child & parent & h & h' & ctx & base & d & Ha & Hd & E).
  exact (erasable_equ d c E (erasable_reach _ d (admissible_erasable _ _ _ _ _ _ Ha) Hd)).
Qed.

Theorem owned_fork_erasure (child : CProg unit) (k : unit -> CProg unit) h h' ctx base :
  admissible child (k tt) h h' ctx base ->
  sbisim (simL owned_result_rel)
    (erase_owned (instrument_owned (init_owned child (k tt) h h' ctx base)))
    (run_nd (CBind (CFork child) k) (h ⊎ h', (ctx, base))).
Proof.
  intro Ha; pose proof (owned_erasure _ (admissible_erasable _ _ _ _ _ _ Ha)) as Hs.
  change (joined_state (init_owned child (k tt) h h' ctx base)) with (h ⊎ h', (ctx, base + 0 + 0)) in Hs.
  rewrite !Nat.add_0_r in Hs.
  apply (sbisim_clos_sb (L := simL owned_result_rel) (c := chain_gfp _)).
  econstructor; [reflexivity|exact Hs|symmetry; apply run_nd_fork_bind].
Qed.

(** * Operational adequacy of the instrumented owned interpreter.

    [instrument_owned] logs exactly the actions of [owned_step]: one logged
    action (a selection additionally takes its scheduler branch first) is one
    [owned_step], up to [owned_equ] and [≅]. *)

Import CTreeNotations VectorNotations.
Local Open Scope ctree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope pcm_scope.

Definition instr_next (c : OwnedCfg) (a : OwnedAction) (T : ctreeW OwnedAction Bn OwnedCfg) : Prop :=
  trans (obs (Log a) tt) (instrument_owned c) T \/
  exists U, trans τ (instrument_owned c) U /\ trans (obs (Log a) tt) U T.

(** ** Tree shapes *)

Local Definition shape {E B X} (o : ctree' E B X) : nat :=
  match o with
  | RetF _ => 0 | StuckF => 1 | StepF _ => 2 | GuardF _ => 3 | VisF _ _ => 4 | BrF _ _ => 5
  end.

Local Lemma equ_shape {E B X} (t u : ctree E B X) : t ≅ u -> shape (observe t) = shape (observe u).
Proof. intros H. __step_in_equ H. destruct H; reflexivity. Qed.

Local Lemma eta_obs {E B X} (t : ctree E B X) o : observe t = o -> t ≅ go o.
Proof. intros H. apply observe_equ_eq. exact H. Qed.

Local Lemma headed_shape t u :
  headed t u -> (forall t', observe t <> GuardF t') -> shape (observe t) = shape (observe u).
Proof.
  intros [[|m] H] Hng; cbn [guards] in H; apply equ_shape in H; [exact H|].
  exfalso. cbn in H. destruct (observe t); try discriminate. eapply Hng; reflexivity.
Qed.

(** Heads that the scheduler acts on. *)
Local Definition head_ok (u : thread sE Bn) : Prop :=
  shape (observe u) = 0 \/ shape (observe u) = 2 \/ shape (observe u) = 4.

Local Lemma headed_strip t t' u : t ≅ Guard t' -> head_ok u -> headed t u -> headed t' u.
Proof.
  intros Ht Hu [[|m] Hm]; cbn [guards] in Hm.
  - apply equ_shape in Hm. apply equ_shape in Ht. cbn in Ht. rewrite Ht in Hm.
    unfold head_ok in Hu. lia.
  - exists m. apply equ_guard_inv. rewrite <- Ht. exact Hm.
Qed.

Local Lemma headed_add t t' u : t ≅ Guard t' -> headed t' u -> headed t u.
Proof.
  intros Ht [m Hm]. exists (S m). rewrite Ht. exact (guards_equ 1 _ _ Hm).
Qed.

(** ** Vectors and configurations *)

Local Lemma remove_replace {A n} (v : Vector.t A (S n)) (j : Fin.t (S n)) x :
  ((v @ j := x) -- j) = (v -- j).
Proof.
  revert v j; induction n; intros v j; dependent destruction v; dependent destruction j.
  - cbn. rewrite !vector_remove_head. reflexivity.
  - inversion j.
  - cbn. rewrite !vector_remove_head. reflexivity.
  - cbn. rewrite !vector_remove_tail, IHn. reflexivity.
Qed.

Local Lemma set_pool_twice c p q : set_pool (set_pool c p) q = set_pool c q.
Proof. reflexivity. Qed.

Local Lemma prim_step_set_pool i c p {Y} (e : sE Y) :
  prim_step i (set_pool c p) e =
  option_map (fun r => (fst (fst r), snd (fst r), set_pool (snd r) p)) (prim_step i c e).
Proof.
  destruct e as [he|[se|we]]; [destruct he|destruct se|destruct we]; cbn;
    repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
    reflexivity.
Qed.

Local Lemma forall2_slots m (v1 v2 : pool sE Bn m) (g : Vector.t side m) :
  (forall i, (v1 $ i) ≅ (v2 $ i)) ->
  List.Forall2 slot_equ (List.combine (Vector.to_list v1) (Vector.to_list g))
    (List.combine (Vector.to_list v2) (Vector.to_list g)).
Proof.
  revert v1 v2 g; induction m; intros v1 v2 g H;
    dependent destruction v1; dependent destruction v2; dependent destruction g.
  - constructor.
  - rewrite !Vector.to_list_cons. cbn [List.combine]. constructor.
    + split; [exact (H Fin.F1)|reflexivity].
    + apply IHm. intros i. exact (H (Fin.FS i)).
Qed.

Local Lemma owned_equ_pool c m (v1 v2 : pool sE Bn m) g f :
  (forall i, (v1 $ i) ≅ (v2 $ i)) ->
  owned_equ (set_pool c (mk_pool m v1 g f)) (set_pool c (mk_pool m v2 g f)).
Proof.
  intros H. split; [split; [apply forall2_slots, H|reflexivity]|].
  cbn. repeat split; intros; reflexivity.
Qed.

Local Lemma replace_pointwise {n} (v : pool sE Bn n) j (x y : thread sE Bn) :
  x ≅ y -> forall i, ((v @ j := x) $ i) ≅ ((v @ j := y) $ i).
Proof. intros H. apply vector_replace_pointwise; [intros; reflexivity|exact H]. Qed.

Local Lemma guard_dec {E B X} (o : ctree' E B X) : {t | o = GuardF t} + {forall t, o <> GuardF t}.
Proof. destruct o; try (right; intros ? H; discriminate H). left; eexists; reflexivity. Qed.

(** ** Unfolding [instrument_owned] *)

Local Ltac instr_unfold c Hp :=
  destruct c as [p an hp ctx bs cnt l]; cbn in Hp; subst p;
  apply observe_equ_eq; unfold observe at 1; cbn -[prim_step].

Local Lemma instr_nil c v g f :
  oc_pool c = mk_pool 0 v g f -> instrument_owned c ≅ Ret c.
Proof. intros Hp. instr_unfold c Hp. reflexivity. Qed.

Local Lemma instr_sel c n v g :
  oc_pool c = mk_pool (S n) v g None ->
  instrument_owned c ≅ brS (branchn (S n)) (fun j =>
    Vis (Log (act (g $ j) OASelect))
      (fun _ => instrument_owned (set_pool c (mk_pool (S n) v g (Some j))))).
Proof. intros Hp. instr_unfold c Hp. reflexivity. Qed.

Local Lemma instr_guard c n v g j t :
  oc_pool c = mk_pool (S n) v g (Some j) -> observe (v $ j) = GuardF t ->
  observe (instrument_owned c) =
    GuardF (instrument_owned (set_pool c (mk_pool (S n) (v @ j := t) g (Some j)))).
Proof.
  intros Hp E. destruct c as [p an hp ctx bs cnt l]; cbn in Hp; subst p.
  unfold observe at 1; cbn -[prim_step]. rewrite E. reflexivity.
Qed.

Local Lemma instr_ret c n v g j r :
  oc_pool c = mk_pool (S n) v g (Some j) -> observe (v $ j) = RetF r ->
  instrument_owned c ≅ Vis (Log (act (g $ j) OAReturn))
    (fun _ => instrument_owned (set_pool c (mk_pool n (v -- j) (g -- j) None))).
Proof. intros Hp E. instr_unfold c Hp. rewrite E. reflexivity. Qed.

Local Lemma instr_stuck c n v g j :
  oc_pool c = mk_pool (S n) v g (Some j) -> observe (v $ j) = StuckF ->
  instrument_owned c ≅ Stuck.
Proof. intros Hp E. instr_unfold c Hp. rewrite E. reflexivity. Qed.

Local Lemma instr_br c n v g j X (br : Bn X) k :
  oc_pool c = mk_pool (S n) v g (Some j) -> observe (v $ j) = BrF br k ->
  instrument_owned c ≅ Stuck.
Proof. intros Hp E. instr_unfold c Hp. rewrite E. reflexivity. Qed.

Local Lemma instr_step c n v g j t :
  oc_pool c = mk_pool (S n) v g (Some j) -> observe (v $ j) = StepF t ->
  instrument_owned c ≅ Vis (Log (act (g $ j) OAStep))
    (fun _ => instrument_owned (set_pool c (mk_pool (S n) (v @ j := t) g (Some j)))).
Proof. intros Hp E. instr_unfold c Hp. rewrite E. reflexivity. Qed.

Local Lemma instr_yield c n v g j k :
  oc_pool c = mk_pool (S n) v g (Some j) -> observe (v $ j) = VisF (inl1 Yield : CEff unit) k ->
  instrument_owned c ≅ Vis (Log (act (g $ j) OAYield))
    (fun _ => instrument_owned (set_pool c (mk_pool (S n) (v @ j := k tt) g None))).
Proof. intros Hp E. instr_unfold c Hp. rewrite E. reflexivity. Qed.

Local Lemma instr_fork c n v g j k :
  oc_pool c = mk_pool (S n) v g (Some j) -> observe (v $ j) = VisF (inr1 (inl1 Fork) : CEff bool) k ->
  instrument_owned c ≅ Vis (Log (act (g $ j) OAFork))
    (fun _ => instrument_owned (set_pool c
       (mk_pool (S (S n)) (k true :: (v @ j := k false)) ((g $ j) :: g) (Some (Fin.FS j))))).
Proof. intros Hp E. instr_unfold c Hp. rewrite E. reflexivity. Qed.

Local Lemma instr_prim c n v g j Y (e : sE Y) k kind y c1 :
  oc_pool c = mk_pool (S n) v g (Some j) -> observe (v $ j) = VisF (inr1 (inr1 e) : CEff Y) k ->
  prim_step (g $ j) c e = Some (kind, y, c1) ->
  instrument_owned c ≅ Vis (Log (act (g $ j) kind))
    (fun _ => instrument_owned (set_pool c1 (mk_pool (S n) (v @ j := k y) g (Some j)))).
Proof. intros Hp E P. instr_unfold c Hp. rewrite E, P. reflexivity. Qed.

Local Lemma instr_prim_none c n v g j Y (e : sE Y) k :
  oc_pool c = mk_pool (S n) v g (Some j) -> observe (v $ j) = VisF (inr1 (inr1 e) : CEff Y) k ->
  prim_step (g $ j) c e = None ->
  instrument_owned c ≅ Stuck.
Proof. intros Hp E P. instr_unfold c Hp. rewrite E, P. reflexivity. Qed.

(** ** [owned_step] by pool shape *)

Local Lemma owned_step_nil c v g f a c' : oc_pool c = mk_pool 0 v g f -> ~ owned_step c a c'.
Proof. intros Hp. unfold owned_step. rewrite Hp. cbn. tauto. Qed.

Local Lemma owned_step_sel c n v g a c' :
  oc_pool c = mk_pool (S n) v g None -> owned_step c a c' <-> sel_step c n v g a c'.
Proof. intros Hp. unfold owned_step. rewrite Hp. reflexivity. Qed.

Local Lemma owned_step_focus c n v g j a c' :
  oc_pool c = mk_pool (S n) v g (Some j) -> owned_step c a c' <-> focus_step c n v g j a c'.
Proof. intros Hp. unfold owned_step. rewrite Hp. reflexivity. Qed.

(** ** Focused steps through one guard *)

Local Lemma focus_step_headed c n v g j a c' :
  focus_step c n v g j a c' -> exists u, head_ok u /\ headed (v $ j) u.
Proof.
  intros [[t [H _]]|[[k [H _]]|[[k [H _]]|[[H _]|[Y [e [k [kind [y [c1 [H _]]]]]]]]]]];
    eexists; (split; [|exact H]); unfold head_ok; cbn; auto.
Qed.

(** Consuming the focused slot's leading guard does not change its actions. *)
Local Lemma focus_step_guard c n v g j t a c' :
  observe (v $ j) = GuardF t ->
  focus_step c n v g j a c' <->
  focus_step (set_pool c (mk_pool (S n) (v @ j := t) g (Some j))) n (v @ j := t) g j a c'.
Proof.
  intros E. pose proof (eta_obs _ _ E) as Hv.
  assert (Hok : forall u, shape (observe u) = 0 \/ shape (observe u) = 2 \/ shape (observe u) = 4 -> head_ok u)
    by (intros; assumption).
  unfold focus_step. rewrite Vector.nth_replace_eq, remove_replace.
  split.
  - intros [[t' [Hh [-> ->]]]|[[k [Hh [-> ->]]]|[[k [Hh [-> ->]]]|[[Hh [-> ->]]|
            [Y [e [k [kind [y [c1 [Hh [P [-> ->]]]]]]]]]]]]].
    + left. exists t'. rewrite Vector.replace_replace_eq.
      split; [eapply headed_strip; eauto; apply Hok; cbn; auto|split; reflexivity].
    + right; left. exists k. rewrite Vector.replace_replace_eq.
      split; [eapply headed_strip; eauto; apply Hok; cbn; auto|split; reflexivity].
    + right; right; left. exists k. rewrite Vector.replace_replace_eq.
      split; [eapply headed_strip; eauto; apply Hok; cbn; auto|split; reflexivity].
    + right; right; right; left.
      split; [eapply headed_strip; eauto; apply Hok; cbn; auto|split; reflexivity].
    + right; right; right; right.
      exists Y, e, k, kind, y, (set_pool c1 (mk_pool (S n) (v @ j := t) g (Some j))).
      rewrite Vector.replace_replace_eq, prim_step_set_pool, P.
      split; [eapply headed_strip; eauto; apply Hok; cbn; auto|split; [reflexivity|split; reflexivity]].
  - intros [[t' [Hh [-> ->]]]|[[k [Hh [-> ->]]]|[[k [Hh [-> ->]]]|[[Hh [-> ->]]|
            [Y [e [k [kind [y [c1 [Hh [P [-> ->]]]]]]]]]]]]];
      try rewrite Vector.replace_replace_eq.
    + left. exists t'. split; [eapply headed_add; eauto|split; reflexivity].
    + right; left. exists k. split; [eapply headed_add; eauto|split; reflexivity].
    + right; right; left. exists k. split; [eapply headed_add; eauto|split; reflexivity].
    + right; right; right; left. split; [eapply headed_add; eauto|split; reflexivity].
    + right; right; right; right.
      rewrite prim_step_set_pool in P.
      destruct (prim_step (g $ j) c e) as [[[kind' y'] c1']|] eqn:P'; cbn in P; inversion P; subst.
      exists Y, e, k, kind, y, c1'.
      split; [eapply headed_add; eauto|split; [exact P'|split; reflexivity]].
Qed.

(** A focused slot whose head is not a guard: one logged action or stuck. *)
Local Lemma head_char c n v g j :
  oc_pool c = mk_pool (S n) v g (Some j) ->
  (forall t, observe (v $ j) <> GuardF t) ->
  (exists a0 d0, instrument_owned c ≅ Vis (Log a0) (fun _ => instrument_owned d0) /\
     focus_step c n v g j a0 d0 /\
     forall a c', focus_step c n v g j a c' -> a = a0 /\ owned_equ c' d0) \/
  (instrument_owned c ≅ Stuck /\ forall a c', ~ focus_step c n v g j a c').
Proof.
  intros Hp Hng. destruct (observe (v $ j)) eqn:E.
  - destruct r. left. eexists _, _. split; [exact (instr_ret _ _ _ _ _ _ Hp E)|].
    split; [apply (focus_step_head_ret c n v g j 0 _ _ (eta_obs _ _ E)); auto|].
    intros a c' Hs. apply (focus_step_head_ret c n v g j 0 a c' (eta_obs _ _ E)) in Hs as [-> ->].
    split; reflexivity.
  - right. split; [exact (instr_stuck _ _ _ _ _ Hp E)|].
    intros a c'. exact (focus_step_head_stuck c n v g j 0 a c' (eta_obs _ _ E)).
  - left. eexists _, _. split; [exact (instr_step _ _ _ _ _ _ Hp E)|].
    split; [apply (focus_step_head_step c n v g j t 0 _ _ (eta_obs _ _ E)); eauto|].
    intros a c' Hs. apply (focus_step_head_step c n v g j t 0 a c' (eta_obs _ _ E)) in Hs
      as [t' [Ht [-> ->]]].
    split; [reflexivity|apply owned_equ_pool, replace_pointwise, Ht].
  - exfalso. exact (Hng _ eq_refl).
  - destruct e as [y|[fk|e']].
    + destruct y. left. eexists _, _. split; [exact (instr_yield _ _ _ _ _ _ Hp E)|].
      split; [apply (focus_step_head_yield c n v g j k 0 _ _ (eta_obs _ _ E));
              exists k; split; [reflexivity|split; reflexivity]|].
      intros a c' Hs. apply (focus_step_head_yield c n v g j k 0 a c' (eta_obs _ _ E)) in Hs
        as [k' [Hk [-> ->]]].
      split; [reflexivity|apply owned_equ_pool, replace_pointwise, Hk].
    + destruct fk. left. eexists _, _. split; [exact (instr_fork _ _ _ _ _ _ Hp E)|].
      split; [apply (focus_step_head_fork c n v g j k 0 _ _ (eta_obs _ _ E));
              exists k; split; [reflexivity|split; reflexivity]|].
      intros a c' Hs. apply (focus_step_head_fork c n v g j k 0 a c' (eta_obs _ _ E)) in Hs
        as [k' [Hk [-> ->]]].
      split; [reflexivity|apply owned_equ_pool, vector_cons_pointwise; [apply Hk|]].
      apply replace_pointwise, Hk.
    + destruct (prim_step (g $ j) c e') as [[[kind y] c1]|] eqn:P.
      * left. eexists _, _. split; [exact (instr_prim _ _ _ _ _ _ _ _ _ _ _ Hp E P)|].
        split; [apply (focus_step_head_prim c n v g j e' k 0 _ _ (eta_obs _ _ E));
                exists k, kind, y, c1; split; [reflexivity|split; [exact P|split; reflexivity]]|].
        intros a c' Hs. apply (focus_step_head_prim c n v g j e' k 0 a c' (eta_obs _ _ E)) in Hs
          as [k' [kind' [y' [c1' [Hk [P' [-> ->]]]]]]].
        rewrite P in P'. inversion P'; subst.
        split; [reflexivity|apply owned_equ_pool, replace_pointwise, Hk].
      * right. split; [exact (instr_prim_none _ _ _ _ _ _ _ _ Hp E P)|].
        intros a c' Hs. apply (focus_step_head_prim c n v g j e' k 0 a c' (eta_obs _ _ E)) in Hs
          as [k' [kind' [y' [c1' [Hk [P' _]]]]]].
        rewrite P in P'. discriminate.
  - right. split; [exact (instr_br _ _ _ _ _ _ _ _ Hp E)|].
    intros a c' Hs. apply focus_step_headed in Hs as [u [Hu Hh]].
    apply headed_shape in Hh; [|intros t' E'; rewrite E in E'; discriminate].
    rewrite E in Hh. unfold head_ok in Hu. cbn in Hh. lia.
Qed.

(** ** Both directions for a focused pool *)

Local Lemma fwd_focus m : forall c n v g j u a c',
  oc_pool c = mk_pool (S n) v g (Some j) -> head_ok u -> (v $ j) ≅ guards m u ->
  focus_step c n v g j a c' ->
  exists d T, owned_equ c' d /\ trans (obs (Log a) tt) (instrument_owned c) T /\
    T ≅ instrument_owned d.
Proof.
  induction m; intros c n v g j u a c' Hp Hu Hm Hs.
  - assert (Hng : forall t, observe (v $ j) <> GuardF t).
    { intros t E. apply equ_shape in Hm. rewrite E in Hm. cbn in Hm. unfold head_ok in Hu. lia. }
    destruct (head_char c n v g j Hp Hng) as [[a0 [d0 [Heq [_ Huniq]]]]|[_ Hno]].
    + destruct (Huniq _ _ Hs) as [-> Hd]. exists d0, (instrument_owned d0).
      split; [exact Hd|split; [|reflexivity]]. rewrite Heq.
      exact (trans_vis (Log a0) tt (fun _ => instrument_owned d0)).
    + exfalso. exact (Hno _ _ Hs).
  - cbn [guards] in Hm. destruct (guard_dec (observe (v $ j))) as [[t E]|Hng].
    + pose proof (eta_obs _ _ E) as Hv. cbn in Hv.
      assert (Ht : t ≅ guards m u) by (apply equ_guard_inv; rewrite <- Hv; exact Hm).
      apply (focus_step_guard _ _ _ _ _ _ _ _ E) in Hs.
      destruct (IHm (set_pool c (mk_pool (S n) (v @ j := t) g (Some j))) n (v @ j := t) g j u a c' eq_refl Hu ltac:(rewrite Vector.nth_replace_eq; exact Ht) Hs)
        as [d [T [Hd [Htr HT]]]].
      exists d, T. split; [exact Hd|split; [|exact HT]].
      rewrite (observe_equ_eq _ _ _ _ (Guard _) (instr_guard _ _ _ _ _ _ Hp E)).
      apply trans_guard. exact Htr.
    + exfalso. apply equ_shape in Hm. cbn in Hm.
      destruct (observe (v $ j)); try discriminate. exact (Hng _ eq_refl).
Qed.

Local Lemma bwd_head c n v g j l oT :
  oc_pool c = mk_pool (S n) v g (Some j) -> (forall t, observe (v $ j) <> GuardF t) ->
  trans_ l (observe (instrument_owned c)) oT ->
  exists a c' d, l = obs (Log a) tt /\ focus_step c n v g j a c' /\ owned_equ c' d /\
    go oT ≅ instrument_owned d.
Proof.
  intros Hp Hng Htr. change (trans l (instrument_owned c) (go oT)) in Htr.
  destruct (head_char c n v g j Hp Hng) as [[a0 [d0 [Heq [Hs _]]]]|[Heq _]]; rewrite Heq in Htr.
  - apply trans_vis_inv in Htr as [[] [HT ->]].
    exists a0, d0, d0. split; [reflexivity|split; [exact Hs|split; [reflexivity|exact HT]]].
  - exfalso. eapply trans_stuck_inv. exact Htr.
Qed.

Local Lemma bwd_aux l ot oT : trans_ l ot oT -> forall c n v g j,
  oc_pool c = mk_pool (S n) v g (Some j) -> ot = observe (instrument_owned c) ->
  exists a c' d, l = obs (Log a) tt /\ focus_step c n v g j a c' /\ owned_equ c' d /\
    go oT ≅ instrument_owned d.
Proof.
  intros Htr. induction Htr; intros cfg n v g j Hp Hot;
    (destruct (guard_dec (observe (v $ j))) as [[t0 E]|Hng];
      [rewrite (instr_guard _ _ _ _ _ _ Hp E) in Hot; try discriminate Hot
      |apply (bwd_head cfg n v g j); [exact Hp|exact Hng|rewrite <- Hot; econstructor; eauto]]).
  injection Hot as ->.
  destruct (IHHtr (set_pool cfg (mk_pool (S n) (v @ j := t0) g (Some j))) n (v @ j := t0) g j eq_refl eq_refl) as [a [c' [d [Hl [Hs Hd]]]]].
  exists a, c', d. split; [exact Hl|split; [|exact Hd]].
  apply (focus_step_guard _ _ _ _ _ _ _ _ E). exact Hs.
Qed.

Theorem instrument_owned_adequate c a :
  (forall c', owned_step c a c' ->
     exists d T, owned_equ c' d /\ instr_next c a T /\ T ≅ instrument_owned d) /\
  (forall T, instr_next c a T ->
     exists c' d, owned_step c a c' /\ owned_equ c' d /\ T ≅ instrument_owned d).
Proof.
  destruct (oc_pool c) as [n v g f] eqn:Hp. revert v g f Hp.
  destruct n as [|n]; intros v g f Hp; change (oc_pool c = mk_pool _ v g f) in Hp.
  - split.
    + intros c' Hs. exfalso. exact (owned_step_nil _ _ _ _ _ _ Hp Hs).
    + intros T [Htr|[U [Htr _]]]; rewrite (instr_nil _ _ _ _ Hp) in Htr;
        apply trans_ret_inv in Htr as [_ Hl]; discriminate Hl.
  - destruct f as [j|].
    + split.
      * intros c' Hs. apply (owned_step_focus _ _ _ _ _ _ _ Hp) in Hs.
        destruct (focus_step_headed _ _ _ _ _ _ _ Hs) as [u [Hu [m Hm]]].
        destruct (fwd_focus m _ _ _ _ _ u _ _ Hp Hu Hm Hs) as [d [T [Hd [Htr HT]]]].
        exists d, T. split; [exact Hd|split; [left; exact Htr|exact HT]].
      * intros T [Htr|[U [Htr _]]];
          destruct (bwd_aux _ _ _ Htr c n v g j Hp eq_refl) as [a' [c' [d [Hl [Hs [Hd HT]]]]]];
          [|discriminate Hl].
        apply obs_eq_inv in Hl as [Hl _]. injection Hl as <-.
        exists c', d. split; [apply (owned_step_focus _ _ _ _ _ _ _ Hp); exact Hs|split; [exact Hd|]].
        rewrite (ctree_eta T). exact HT.
    + split.
      * intros c' Hs. apply (owned_step_sel _ _ _ _ _ _ Hp) in Hs as [j [-> ->]].
        eexists _, _. split; [reflexivity|split; [|reflexivity]].
        right. eexists. split; [rewrite (instr_sel _ _ _ _ Hp); apply (trans_brS _ _ j)|].
        exact (trans_vis (Log _) tt (fun _ => instrument_owned (set_pool c (mk_pool (S n) v g (Some j))))).
      * intros T [Htr|[U [Htr Htr']]]; rewrite (instr_sel _ _ _ _ Hp) in Htr;
          apply trans_brS_inv in Htr as [j [HU Hl]]; [discriminate Hl|].
        rewrite HU in Htr'. apply trans_vis_inv in Htr' as [[] [HT Hl']].
        apply obs_eq_inv in Hl' as [Hl' _]. injection Hl' as ->.
        eexists _, _. split; [apply (owned_step_sel _ _ _ _ _ _ Hp); exists j; split; reflexivity|].
        split; [reflexivity|exact HT].
Qed.
