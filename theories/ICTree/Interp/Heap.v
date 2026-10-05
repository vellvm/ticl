(** * Checked heap accesses, malloc and whole-block free, in one handler.

    The handler is polymorphic in its OUTPUT effect [F] and in an untouched
    auxiliary state [Sigma]; the managed memory (data heap and live
    allocation extents, [ManagedHeap]) is the first component of the
    interpretation state.  Instrumented interpreters instantiate [F] with a
    writer effect and [Sigma] with their own bookkeeping; a pure client may
    instantiate [F := void] and [Sigma := unit].

    The algorithm is fixed: allocation starts at address 1, rejects size 0,
    searches the immutable data snapshot for the first free positive block,
    keeps rejected candidates silent, records the allocated extent, and
    preserves [aux].  A missing read/write/CAS is [stuck], and a failed CAS
    leaves the whole state unchanged.  Free releases exactly the recorded
    block at a live base ([managed_free]): freeing [0] is a no-op, and every
    other free (interior pointer, unknown base, double free) is [stuck].
    There is no least-address axiom, no fuel, and no failure fallback. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad.

From Coinduction Require Import coinduction.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Interp.State.Mod
  ICTree.Events.Heap
  Events.Core.

From TICL Require Export Events.HeapModel.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

(** Setoid rewriting through [≅] and [~] needs [equ]/[sbisim] to be
    typeclass-transparent, exactly as elsewhere in this development.  Both
    unfold to the Coinduction companion [t], which that library keeps
    typeclass-opaque -- but only as an [#[export]] setting, so it is in
    effect solely in modules that IMPORT [coinduction], not in modules that
    merely require it transitively.  Without that import the transparency
    below lets resolution unfold past [t] into the lattice machinery, and at
    the generic effect type [F] of this module a single [reflexivity] costs
    tens of seconds instead of milliseconds.  That is why [coinduction] is
    imported explicitly above. *)
Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.

(** The immutable snapshot is searched without fuel or heap instrumentation.
    Every rejected candidate is silent; only success changes the heap. *)
CoFixpoint alloc_search {F : Type} {HF : Encode F} {Sigma : Type}
  (h : Heap) (size candidate : nat) (aux : Sigma)
  : ictree F (nat * (Heap * Sigma)) :=
  match size with
  | 0 => stuck
  | S _ =>
      if block_freeb h candidate size
      then Ret (candidate, (hunion (hblock candidate size) h, aux))
      else Guard (alloc_search h size (S candidate) aux)
  end.

(** The state is [((h,allocs),aux)]: data heap, live extents, auxiliary
    state.  Allocation reuses the heap returned by [alloc_search] and only
    adds the extent record; free is exactly [managed_free]. *)
Definition heap_handler {F : Type} {HF : Encode F} {Sigma : Type}
  : heapE ~> stateT (ManagedHeap * Sigma) (ictree F) :=
  fun e =>
    mkStateT (fun s =>
      match e return ictree F (encode e * (ManagedHeap * Sigma)) with
      | HRead a => match fst (fst s) a with
                   | Some v => Ret (v,s)
                   | None => stuck
                   end
      | HWrite a v => match fst (fst s) a with
                      | Some _ => Ret (tt,((upd (fst (fst s)) a v,snd (fst s)),snd s))
                      | None => stuck
                      end
      | HAlloc size =>
          alloc_search (fst (fst s)) size 1 (snd s) >>= fun '(base,(h',aux')) =>
            Ret (base,((h',upd (snd (fst s)) base size),aux'))
      | HFree base => match managed_free (fst s) base with
                      | Some memory' => Ret (tt,(memory',snd s))
                      | None => stuck
                      end
      | HCAS a expected desired =>
          match fst (fst s) a with
          | None => stuck
          | Some current =>
              if Nat.eqb current expected
              then Ret (true,((upd (fst (fst s)) a desired,snd (fst s)),snd s))
              else Ret (false,s)
          end
      end).

(** ** Raw handler equations.

    These are the canonical response certificates a first-yield segment
    discharges; they are handler equations, not interpreter equations. *)
Section HandlerEquations.
  Context {F : Type} {HF : Encode F} {Sigma : Type}.

  Lemma heap_handler_rd_some : forall a h allocs (aux : Sigma) v,
    h a = Some v ->
    runStateT (heap_handler (F:=F) (HRead a)) ((h,allocs),aux) ≅
      Ret (v,((h,allocs),aux)).
  Proof. intros a h allocs aux v H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_rd_none : forall a h allocs (aux : Sigma),
    h a = None ->
    runStateT (heap_handler (F:=F) (HRead a)) ((h,allocs),aux) ≅ stuck.
  Proof. intros a h allocs aux H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_wr_some : forall a h allocs (aux : Sigma) v w,
    h a = Some w ->
    runStateT (heap_handler (F:=F) (HWrite a v)) ((h,allocs),aux) ≅
      Ret (tt,((upd h a v,allocs),aux)).
  Proof. intros a h allocs aux v w H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_wr_none : forall a h allocs (aux : Sigma) v,
    h a = None ->
    runStateT (heap_handler (F:=F) (HWrite a v)) ((h,allocs),aux) ≅ stuck.
  Proof. intros a h allocs aux v H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_cas_success a expected desired h allocs (aux : Sigma) :
    h a = Some expected ->
    runStateT (heap_handler (F:=F) (HCAS a expected desired)) ((h,allocs),aux) ≅
      Ret (true,((upd h a desired,allocs),aux)).
  Proof. intro H; cbn; rewrite H, Nat.eqb_refl; reflexivity. Qed.

  Lemma heap_handler_cas_failure a expected desired current h allocs (aux : Sigma) :
    h a = Some current -> current <> expected ->
    runStateT (heap_handler (F:=F) (HCAS a expected desired)) ((h,allocs),aux) ≅
      Ret (false,((h,allocs),aux)).
  Proof.
    intros H N; cbn; rewrite H.
    apply Nat.eqb_neq in N; rewrite N; reflexivity.
  Qed.

  Lemma heap_handler_cas_missing a expected desired h allocs (aux : Sigma) :
    h a = None ->
    runStateT (heap_handler (F:=F) (HCAS a expected desired)) ((h,allocs),aux) ≅
      (stuck : ictree F (bool * (ManagedHeap * Sigma))).
  Proof. intro H; cbn; rewrite H; reflexivity. Qed.

  (** A successful free releases exactly the recorded block. *)
  Lemma heap_handler_free base (memory memory' : ManagedHeap) (aux : Sigma) :
    managed_free memory base = Some memory' ->
    runStateT (heap_handler (F:=F) (HFree base)) (memory,aux) ≅
      Ret (tt,(memory',aux)).
  Proof. intro H; cbn; rewrite H; reflexivity. Qed.

  (** Interior-pointer, unknown-base and double frees are faults. *)
  Lemma heap_handler_free_invalid base (memory : ManagedHeap) (aux : Sigma) :
    managed_free memory base = None ->
    runStateT (heap_handler (F:=F) (HFree base)) (memory,aux) ≅
      (stuck : ictree F (unit * (ManagedHeap * Sigma))).
  Proof. intro H; cbn; rewrite H; reflexivity. Qed.
End HandlerEquations.

(** ** Allocation search *)
Section AllocSearch.
  Context {F : Type} {HF : Encode F} {Sigma : Type}.

  Lemma unfold_alloc_search h size candidate (aux : Sigma) :
    alloc_search (F:=F) h size candidate aux ≅
    match size with
    | 0 => stuck
    | S _ => if block_freeb h candidate size
             then Ret (candidate, (hunion (hblock candidate size) h, aux))
             else Guard (alloc_search (F:=F) h size (S candidate) aux)
    end.
  Proof. step; cbn; unfold observe; cbn; reflexivity. Qed.

  Lemma alloc_search_first h size start base (aux : Sigma) :
    Nat.lt 0 size -> Nat.le start base -> block_free h base size ->
    (forall j, Nat.le start j -> Nat.lt j base -> ~ block_free h j size) ->
    alloc_search (F:=F) h size start aux ~
      Ret (base, (hunion (hblock base size) h, aux)).
  Proof.
    intros Pos L Free First; destruct size as [|size]; [lia |].
    remember (base - start) as distance eqn:D.
    revert start L First D.
    induction distance as [|distance IH]; intros start L First D.
    - assert (start = base) by lia; subst start.
      rewrite unfold_alloc_search.
      apply block_freeb_spec in Free; rewrite Free; reflexivity.
    - assert (Test : block_freeb h start (S size) = false).
      { destruct (block_freeb h start (S size)) eqn:T; [|reflexivity].
        exfalso; apply (First start); try lia; apply block_freeb_spec; exact T. }
      rewrite unfold_alloc_search, Test.
      etransitivity; [apply sb_guard |].
      apply IH; [lia | |lia].
      intros j J B; apply First; lia.
  Qed.

  Lemma alloc_search_no_space h size start (aux : Sigma) :
    Nat.lt 0 size ->
    (forall j, Nat.le start j -> ~ block_free h j size) ->
    alloc_search (F:=F) h size start aux ≅
      (stuck : ictree F (nat * (Heap * Sigma))).
  Proof.
    intros Pos Full; destruct size as [|size]; [lia |].
    revert start Full; __coinduction_equ R CIH; intros start Full.
    assert (Test : block_freeb h start (S size) = false).
    { destruct (block_freeb h start (S size)) eqn:T; [|reflexivity].
      exfalso; apply (Full start); [lia | apply block_freeb_spec; exact T]. }
    rewrite unfold_alloc_search, Test, unfold_stuck.
    constructor; apply CIH; intros j J; apply Full; lia.
  Qed.

  Lemma heap_handler_alloc_zero h allocs (aux : Sigma) :
    runStateT (heap_handler (F:=F) (HAlloc 0)) ((h,allocs),aux) ≅
      (stuck : ictree F (nat * (ManagedHeap * Sigma))).
  Proof.
    cbn [runStateT heap_handler fst snd].
    rewrite (unfold_alloc_search h 0 1 aux).
    apply bind_stuck_equ.
  Qed.

  (** Malloc returns the first-fit base and records its extent. *)
  Lemma heap_handler_alloc_first h allocs size base (aux : Sigma) :
    Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    runStateT (heap_handler (F:=F) (HAlloc size)) ((h,allocs),aux) ~
      Ret (base, (managed_alloc (h,allocs) base size, aux)).
  Proof.
    intros Pos B Free First.
    cbn [runStateT heap_handler fst snd].
    rewrite (alloc_search_first h size 1 base aux); try assumption; try lia.
    rewrite bind_ret_l; reflexivity.
  Qed.

  (** A finite heap always admits a first-fit witness. *)
  Lemma heap_handler_alloc_finite h allocs size (aux : Sigma) :
    heap_finite h -> Nat.lt 0 size ->
    exists base,
      Nat.lt 0 base /\ block_free h base size /\
      (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) /\
      runStateT (heap_handler (F:=F) (HAlloc size)) ((h,allocs),aux) ~
        Ret (base, (managed_alloc (h,allocs) base size, aux)).
  Proof.
    intros [B Bound] Pos.
    assert (Search : forall distance start,
      Nat.max 1 B = (start + distance)%nat ->
      exists base, Nat.le start base /\ block_free h base size /\
        (forall j, Nat.le start j -> Nat.lt j base -> ~ block_free h j size)).
    { induction distance as [|distance IH]; intros start D.
      - exists start; split; [lia |]; split.
        + eapply heap_bounded_block_free; [exact Bound |lia].
        + intros j J L; lia.
      - destruct (block_freeb h start size) eqn:T.
        + exists start; split; [lia |]; split.
          * apply block_freeb_spec; exact T.
          * intros j J L; lia.
        + destruct (IH (S start) ltac:(lia)) as (base & L & F0 & First).
          exists base; split; [lia |]; split; [exact F0 |].
          intros j J Lt Free; destruct (Nat.eq_dec j start) as [E|E].
          * subst j; apply block_freeb_spec in Free; congruence.
          * apply (First j); try lia; exact Free. }
    destruct (Search (Nat.max 1 B - 1) 1 ltac:(lia))
      as (base & L & F0 & First).
    exists base; split; [lia |]; split; [exact F0 |]; split.
    - intros j J Lt; apply First; lia.
    - apply heap_handler_alloc_first; try assumption; try lia.
  Qed.
End AllocSearch.

(** ** Lifting through [interp_state].

    Adding another effect handler leaves the checked memory paths unchanged;
    [other] is arbitrary. *)
Section HeapInterp.
  Context {F G : Type} {HF : Encode F} {HG : Encode G} {Sigma : Type}
    (other : G ~> stateT (ManagedHeap * Sigma) (ictree F)).

  Lemma interp_heap_rd {X} : forall a h allocs (aux : Sigma) v
    (k : nat -> ictree (heapE + G) X),
    h a = Some v ->
    interp_state (h_sum heap_handler other) (x <- heap_read a;; k x) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k v) ((h,allocs),aux).
  Proof.
    intros a h allocs aux v k H.
    unfold heap_read, ICtree.trigger, resum, ReSum_inl, resum_ret, ReSumRet_inl.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_rd_some (F:=F) a h allocs aux v H), bind_ret_l.
    apply sb_guard.
  Qed.

  Lemma interp_heap_wr {X} : forall a h allocs (aux : Sigma) v w
    (k : unit -> ictree (heapE + G) X),
    h a = Some w ->
    interp_state (h_sum heap_handler other) (x <- heap_write a v;; k x) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k tt) ((upd h a v,allocs),aux).
  Proof.
    intros a h allocs aux v w k H.
    unfold heap_write, ICtree.trigger, resum, ReSum_inl, resum_ret, ReSumRet_inl.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_wr_some (F:=F) a h allocs aux v w H), bind_ret_l.
    apply sb_guard.
  Qed.

  Lemma interp_heap_wr_present {X} : forall a h allocs (aux : Sigma) v
    (k : unit -> ictree (heapE + G) X),
    h a <> None ->
    interp_state (h_sum heap_handler other) (x <- heap_write a v;; k x) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k tt) ((upd h a v,allocs),aux).
  Proof.
    intros a h allocs aux v k H; destruct (h a) as [w |] eqn:Ha; [| contradiction].
    eapply interp_heap_wr; eauto.
  Qed.

  Lemma interp_heap_rd_stuck a h allocs (aux : Sigma) :
    h a = None ->
    interp_state (h_sum heap_handler other) (heap_read (E:=heapE + G) a) ((h,allocs),aux)
      ≅ (stuck : ictree F (nat * (ManagedHeap * Sigma))).
  Proof.
    intro H; unfold heap_read, ICtree.trigger.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_rd_none (F:=F) a h allocs aux H).
    apply bind_stuck_equ.
  Qed.

  Lemma interp_heap_wr_stuck a v h allocs (aux : Sigma) :
    h a = None ->
    interp_state (h_sum heap_handler other) (heap_write (E:=heapE + G) a v) ((h,allocs),aux)
      ≅ (stuck : ictree F (unit * (ManagedHeap * Sigma))).
  Proof.
    intro H; unfold heap_write, ICtree.trigger.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_wr_none (F:=F) a h allocs aux v H).
    apply bind_stuck_equ.
  Qed.

  Lemma interp_heap_cas_success {X} a expected desired h allocs (aux : Sigma)
    (k : bool -> ictree (heapE + G) X) :
    h a = Some expected ->
    interp_state (h_sum heap_handler other)
      (b <- heap_cas a expected desired;; k b) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k true) ((upd h a desired,allocs),aux).
  Proof.
    intro H; unfold heap_cas, ICtree.trigger; rewrite bind_vis;
      setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_cas_success (F:=F) a expected desired h allocs aux H),
      bind_ret_l.
    apply sb_guard.
  Qed.

  Lemma interp_heap_cas_failure {X} a expected desired current h allocs (aux : Sigma)
    (k : bool -> ictree (heapE + G) X) :
    h a = Some current -> current <> expected ->
    interp_state (h_sum heap_handler other)
      (b <- heap_cas a expected desired;; k b) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k false) ((h,allocs),aux).
  Proof.
    intros H N; unfold heap_cas, ICtree.trigger; rewrite bind_vis;
      setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_cas_failure (F:=F) a expected desired current h allocs aux H N),
      bind_ret_l.
    apply sb_guard.
  Qed.

  Lemma interp_heap_cas_missing {X} a expected desired h allocs (aux : Sigma)
    (k : bool -> ictree (heapE + G) X) :
    h a = None ->
    interp_state (h_sum heap_handler other)
      (b <- heap_cas a expected desired;; k b) ((h,allocs),aux) ~
      (stuck : ictree F (X * (ManagedHeap * Sigma))).
  Proof.
    intro H; unfold heap_cas, ICtree.trigger; rewrite bind_vis;
      setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_cas_missing (F:=F) a expected desired h allocs aux H).
    rewrite bind_stuck_equ; reflexivity.
  Qed.

  Lemma interp_heap_alloc_zero h allocs (aux : Sigma) :
    interp_state (h_sum heap_handler other) (heap_alloc (E:=heapE + G) 0) ((h,allocs),aux)
      ≅ (stuck : ictree F (nat * (ManagedHeap * Sigma))).
  Proof.
    unfold heap_alloc, ICtree.trigger, resum, resum_ret, ReSum_inl, ReSumRet_inl.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_alloc_zero (F:=F) h allocs aux).
    apply bind_stuck_equ.
  Qed.

  Lemma interp_heap_alloc_first {X} h allocs size base (aux : Sigma)
    (k : nat -> ictree (heapE + G) X) :
    Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    interp_state (h_sum heap_handler other) (a <- heap_alloc size;; k a) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k base)
        (managed_alloc (h,allocs) base size,aux).
  Proof.
    intros Pos B Free First.
    unfold heap_alloc, ICtree.trigger, resum, ReSum_inl, resum_ret, ReSumRet_inl;
      rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_alloc_first (F:=F) h allocs size base aux Pos B Free First),
      bind_ret_l.
    apply sb_guard.
  Qed.

  (** A valid free continues with the released memory. *)
  Lemma interp_heap_free {X} base (memory memory' : ManagedHeap) (aux : Sigma)
    (k : unit -> ictree (heapE + G) X) :
    managed_free memory base = Some memory' ->
    interp_state (h_sum heap_handler other) (x <- heap_free base;; k x) (memory,aux) ~
      interp_state (h_sum heap_handler other) (k tt) (memory',aux).
  Proof.
    intro H; unfold heap_free, ICtree.trigger, resum, ReSum_inl, resum_ret, ReSumRet_inl.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_free (F:=F) base memory memory' aux H), bind_ret_l.
    apply sb_guard.
  Qed.

  (** An invalid free never runs its continuation. *)
  Lemma interp_heap_free_invalid {X} base (memory : ManagedHeap) (aux : Sigma)
    (k : unit -> ictree (heapE + G) X) :
    managed_free memory base = None ->
    interp_state (h_sum heap_handler other) (x <- heap_free base;; k x) (memory,aux) ~
      (stuck : ictree F (X * (ManagedHeap * Sigma))).
  Proof.
    intro H; unfold heap_free, ICtree.trigger; rewrite bind_vis;
      setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_free_invalid (F:=F) base memory aux H).
    rewrite bind_stuck_equ; reflexivity.
  Qed.
End HeapInterp.
