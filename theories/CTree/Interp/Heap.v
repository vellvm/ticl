(** * Checked heap accesses, malloc and whole-block free, in one handler.

    The handler is polymorphic in its OUTPUT effect [F], its branch signature
    [B] and in an untouched auxiliary state [Sigma]; the managed memory (data
    heap and live allocation extents, [ManagedHeap]) is the first component of
    the interpretation state.  Instrumented interpreters instantiate [F] with a
    writer effect and [Sigma] with their own bookkeeping; a pure client may
    instantiate [F := void1] and [Sigma := unit].

    The algorithm is fixed: allocation starts at address 1, rejects size 0,
    searches the immutable data snapshot for the first free positive block,
    keeps rejected candidates silent, records the allocated extent, and
    preserves [aux].  A missing read/write/CAS is [Stuck], and a failed CAS
    leaves the whole state unchanged.  Free releases exactly the recorded
    block at a live base ([managed_free]): freeing [0] is a no-op, and every
    other free (interior pointer, unknown base, double free) is [Stuck].
    There is no least-address axiom, no fuel, and no failure fallback.

    State-transformer results follow ITree's [stateT]: state first, [(s, x)]. *)

From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.

From Coinduction Require Import all.

From TICL Require Import
  CTree.Core
  CTree.Interp.State.Mod
  CTree.Events.Heap.

From TICL Require Export Events.HeapModel.

Import CTreeNotations.
Local Open Scope ctree_scope.

(** The immutable snapshot is searched without fuel or heap instrumentation.
    Every rejected candidate is silent; only success changes the heap. *)
CoFixpoint alloc_search {F B : Type -> Type} {Sigma : Type}
  (h : Heap) (size candidate : nat) (aux : Sigma)
  : ctree F B ((Heap * Sigma) * nat) :=
  match size with
  | 0 => Stuck
  | S _ =>
      if block_freeb h candidate size
      then Ret ((hunion (hblock candidate size) h, aux), candidate)
      else Guard (alloc_search h size (S candidate) aux)
  end.

(** The state is [((h,allocs),aux)]: data heap, live extents, auxiliary
    state.  Allocation reuses the heap returned by [alloc_search] and only
    adds the extent record; free is exactly [managed_free]. *)
Definition heap_handler {F B : Type -> Type} {Sigma : Type}
  : heapE ~> stateT (ManagedHeap * Sigma) (ctree F B) :=
  fun _ e s =>
    match e in heapE X return ctree F B ((ManagedHeap * Sigma) * X) with
    | HRead a => match fst (fst s) a with
                 | Some v => Ret (s,v)
                 | None => Stuck
                 end
    | HWrite a v => match fst (fst s) a with
                    | Some _ => Ret (((upd (fst (fst s)) a v,snd (fst s)),snd s),tt)
                    | None => Stuck
                    end
    | HAlloc size =>
        alloc_search (fst (fst s)) size 1 (snd s) >>= fun '((h',aux'),base) =>
          Ret (((h',upd (snd (fst s)) base size),aux'),base)
    | HFree base => match managed_free (fst s) base with
                    | Some memory' => Ret ((memory',snd s),tt)
                    | None => Stuck
                    end
    | HCAS a expected desired =>
        match fst (fst s) a with
        | None => Stuck
        | Some current =>
            if Nat.eqb current expected
            then Ret (((upd (fst (fst s)) a desired,snd (fst s)),snd s),true)
            else Ret (s,false)
        end
    end.

(** ** Raw handler equations.

    These are the canonical response certificates a first-yield segment
    discharges; they are handler equations, not interpreter equations. *)
Section HandlerEquations.
  Context {F B : Type -> Type} {Sigma : Type}.

  Lemma heap_handler_rd_some : forall a h allocs (aux : Sigma) v,
    h a = Some v ->
    heap_handler (F:=F) (B:=B) _ (HRead a) ((h,allocs),aux) ≅
      Ret (((h,allocs),aux),v).
  Proof. intros a h allocs aux v H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_rd_none : forall a h allocs (aux : Sigma),
    h a = None ->
    heap_handler (F:=F) (B:=B) _ (HRead a) ((h,allocs),aux) ≅ Stuck.
  Proof. intros a h allocs aux H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_wr_some : forall a h allocs (aux : Sigma) v w,
    h a = Some w ->
    heap_handler (F:=F) (B:=B) _ (HWrite a v) ((h,allocs),aux) ≅
      Ret (((upd h a v,allocs),aux),tt).
  Proof. intros a h allocs aux v w H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_wr_none : forall a h allocs (aux : Sigma) v,
    h a = None ->
    heap_handler (F:=F) (B:=B) _ (HWrite a v) ((h,allocs),aux) ≅ Stuck.
  Proof. intros a h allocs aux v H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_cas_success a expected desired h allocs (aux : Sigma) :
    h a = Some expected ->
    heap_handler (F:=F) (B:=B) _ (HCAS a expected desired) ((h,allocs),aux) ≅
      Ret (((upd h a desired,allocs),aux),true).
  Proof. intro H; cbn; rewrite H, Nat.eqb_refl; reflexivity. Qed.

  Lemma heap_handler_cas_failure a expected desired current h allocs (aux : Sigma) :
    h a = Some current -> current <> expected ->
    heap_handler (F:=F) (B:=B) _ (HCAS a expected desired) ((h,allocs),aux) ≅
      Ret (((h,allocs),aux),false).
  Proof.
    intros H N; cbn; rewrite H.
    apply Nat.eqb_neq in N; rewrite N; reflexivity.
  Qed.

  Lemma heap_handler_cas_missing a expected desired h allocs (aux : Sigma) :
    h a = None ->
    heap_handler (F:=F) (B:=B) _ (HCAS a expected desired) ((h,allocs),aux) ≅ Stuck.
  Proof. intro H; cbn; rewrite H; reflexivity. Qed.

  (** A successful free releases exactly the recorded block. *)
  Lemma heap_handler_free base (memory memory' : ManagedHeap) (aux : Sigma) :
    managed_free memory base = Some memory' ->
    heap_handler (F:=F) (B:=B) _ (HFree base) (memory,aux) ≅
      Ret ((memory',aux),tt).
  Proof. intro H; cbn; rewrite H; reflexivity. Qed.

  (** Interior-pointer, unknown-base and double frees are faults. *)
  Lemma heap_handler_free_invalid base (memory : ManagedHeap) (aux : Sigma) :
    managed_free memory base = None ->
    heap_handler (F:=F) (B:=B) _ (HFree base) (memory,aux) ≅ Stuck.
  Proof. intro H; cbn; rewrite H; reflexivity. Qed.
End HandlerEquations.

(** ** Allocation search *)
Section AllocSearch.
  Context {F B : Type -> Type} {Sigma : Type}.

  Lemma unfold_alloc_search h size candidate (aux : Sigma) :
    alloc_search (F:=F) (B:=B) h size candidate aux ≅
    match size with
    | 0 => Stuck
    | S _ => if block_freeb h candidate size
             then Ret ((hunion (hblock candidate size) h, aux), candidate)
             else Guard (alloc_search (F:=F) (B:=B) h size (S candidate) aux)
    end.
  Proof. step; cbn; unfold observe; cbn; reflexivity. Qed.

  Lemma alloc_search_first h size start base (aux : Sigma) :
    Nat.lt 0 size -> Nat.le start base -> block_free h base size ->
    (forall j, Nat.le start j -> Nat.lt j base -> ~ block_free h j size) ->
    alloc_search (F:=F) (B:=B) h size start aux ~
      (Ret ((hunion (hblock base size) h, aux), base) : ctree F B _).
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
      intros j J B'; apply First; lia.
  Qed.

  (** With no suitable block anywhere, the search silently diverges. *)
  Lemma alloc_search_no_space h size start (aux : Sigma) :
    Nat.lt 0 size ->
    (forall j, Nat.le start j -> ~ block_free h j size) ->
    alloc_search (F:=F) (B:=B) h size start aux ≅ CTree.spin.
  Proof.
    intros Pos Full; destruct size as [|size]; [lia |].
    revert start Full; __coinduction_equ R CIH; intros start Full.
    assert (Test : block_freeb h start (S size) = false).
    { destruct (block_freeb h start (S size)) eqn:T; [|reflexivity].
      exfalso; apply (Full start); [lia | apply block_freeb_spec; exact T]. }
    rewrite unfold_alloc_search, Test.
    change (equb eq (elem R) (GuardF (alloc_search h (S size) (S start) aux)) (GuardF CTree.spin)).
    constructor; apply CIH; intros j J; apply Full; lia.
  Qed.

  Lemma heap_handler_alloc_zero h allocs (aux : Sigma) :
    heap_handler (F:=F) (B:=B) _ (HAlloc 0) ((h,allocs),aux) ≅ Stuck.
  Proof.
    cbn [heap_handler fst snd].
    rewrite (unfold_alloc_search h 0 1 aux).
    apply bind_stuck.
  Qed.

  (** Malloc returns the first-fit base and records its extent. *)
  Lemma heap_handler_alloc_first h allocs size base (aux : Sigma) :
    Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    heap_handler (F:=F) (B:=B) _ (HAlloc size) ((h,allocs),aux) ~
      (Ret ((managed_alloc (h,allocs) base size, aux), base) : ctree F B _).
  Proof.
    intros Pos B' Free First.
    cbn [heap_handler fst snd].
    rewrite (alloc_search_first h size 1 base aux); try assumption; try lia.
    rewrite bind_ret_l; reflexivity.
  Qed.

  (** A finite heap always admits a first-fit witness. *)
  Lemma heap_handler_alloc_finite h allocs size (aux : Sigma) :
    heap_finite h -> Nat.lt 0 size ->
    exists base,
      Nat.lt 0 base /\ block_free h base size /\
      (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) /\
      heap_handler (F:=F) (B:=B) _ (HAlloc size) ((h,allocs),aux) ~
        (Ret ((managed_alloc (h,allocs) base size, aux), base) : ctree F B _).
  Proof.
    intros [B' Bound] Pos.
    assert (Search : forall distance start,
      Nat.max 1 B' = (start + distance)%nat ->
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
    destruct (Search (Nat.max 1 B' - 1) 1 ltac:(lia))
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
  Context {F G B : Type -> Type} {Sigma : Type}
    (other : G ~> stateT (ManagedHeap * Sigma) (ctree F B)).

  (** One heap event under [interp_state]: the trigger's administrative guard
      disappears and the handler answers. *)
  Local Ltac heap_event :=
    rewrite interp_state_bind, interp_state_trigger_bind, subevent_left; cbn [h_sum].

  Lemma interp_heap_rd {X} : forall a h allocs (aux : Sigma) v
    (k : nat -> ctree (heapE +' G) B X),
    h a = Some v ->
    interp_state (h_sum heap_handler other) (x <- heap_read a;; k x) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k v) ((h,allocs),aux).
  Proof.
    intros a h allocs aux v k H; unfold heap_read; heap_event.
    rewrite (heap_handler_rd_some a h allocs aux v H), bind_ret_l; reflexivity.
  Qed.

  Lemma interp_heap_wr {X} : forall a h allocs (aux : Sigma) v w
    (k : unit -> ctree (heapE +' G) B X),
    h a = Some w ->
    interp_state (h_sum heap_handler other) (x <- heap_write a v;; k x) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k tt) ((upd h a v,allocs),aux).
  Proof.
    intros a h allocs aux v w k H; unfold heap_write; heap_event.
    rewrite (heap_handler_wr_some a h allocs aux v w H), bind_ret_l; reflexivity.
  Qed.

  Lemma interp_heap_wr_present {X} : forall a h allocs (aux : Sigma) v
    (k : unit -> ctree (heapE +' G) B X),
    h a <> None ->
    interp_state (h_sum heap_handler other) (x <- heap_write a v;; k x) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k tt) ((upd h a v,allocs),aux).
  Proof.
    intros a h allocs aux v k H; destruct (h a) as [w |] eqn:Ha; [| contradiction].
    eapply interp_heap_wr; eauto.
  Qed.

  Lemma interp_heap_rd_stuck a h allocs (aux : Sigma) :
    h a = None ->
    interp_state (h_sum heap_handler other) (heap_read (E:=heapE +' G) (B:=B) a) ((h,allocs),aux)
      ≅ Stuck.
  Proof.
    intro H; unfold heap_read.
    rewrite interp_state_trigger, subevent_left; cbn [h_sum].
    rewrite (heap_handler_rd_none a h allocs aux H).
    apply bind_stuck.
  Qed.

  Lemma interp_heap_wr_stuck a v h allocs (aux : Sigma) :
    h a = None ->
    interp_state (h_sum heap_handler other) (heap_write (E:=heapE +' G) (B:=B) a v) ((h,allocs),aux)
      ≅ Stuck.
  Proof.
    intro H; unfold heap_write.
    rewrite interp_state_trigger, subevent_left; cbn [h_sum].
    rewrite (heap_handler_wr_none a h allocs aux v H).
    apply bind_stuck.
  Qed.

  Lemma interp_heap_cas_success {X} a expected desired h allocs (aux : Sigma)
    (k : bool -> ctree (heapE +' G) B X) :
    h a = Some expected ->
    interp_state (h_sum heap_handler other)
      (b <- heap_cas a expected desired;; k b) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k true) ((upd h a desired,allocs),aux).
  Proof.
    intro H; unfold heap_cas; heap_event.
    rewrite (heap_handler_cas_success a expected desired h allocs aux H), bind_ret_l;
      reflexivity.
  Qed.

  Lemma interp_heap_cas_failure {X} a expected desired current h allocs (aux : Sigma)
    (k : bool -> ctree (heapE +' G) B X) :
    h a = Some current -> current <> expected ->
    interp_state (h_sum heap_handler other)
      (b <- heap_cas a expected desired;; k b) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k false) ((h,allocs),aux).
  Proof.
    intros H N; unfold heap_cas; heap_event.
    rewrite (heap_handler_cas_failure a expected desired current h allocs aux H N),
      bind_ret_l; reflexivity.
  Qed.

  Lemma interp_heap_cas_missing {X} a expected desired h allocs (aux : Sigma)
    (k : bool -> ctree (heapE +' G) B X) :
    h a = None ->
    interp_state (h_sum heap_handler other)
      (b <- heap_cas a expected desired;; k b) ((h,allocs),aux) ~ (Stuck : ctree F B ((ManagedHeap * Sigma) * X)).
  Proof.
    intro H; unfold heap_cas; heap_event.
    rewrite (heap_handler_cas_missing a expected desired h allocs aux H), bind_stuck;
      reflexivity.
  Qed.

  Lemma interp_heap_alloc_zero h allocs (aux : Sigma) :
    interp_state (h_sum heap_handler other) (heap_alloc (E:=heapE +' G) (B:=B) 0) ((h,allocs),aux)
      ≅ Stuck.
  Proof.
    unfold heap_alloc.
    rewrite interp_state_trigger, subevent_left; cbn [h_sum].
    rewrite (heap_handler_alloc_zero h allocs aux).
    apply bind_stuck.
  Qed.

  Lemma interp_heap_alloc_first {X} h allocs size base (aux : Sigma)
    (k : nat -> ctree (heapE +' G) B X) :
    Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    interp_state (h_sum heap_handler other) (a <- heap_alloc size;; k a) ((h,allocs),aux) ~
      interp_state (h_sum heap_handler other) (k base)
        (managed_alloc (h,allocs) base size,aux).
  Proof.
    intros Pos B' Free First; unfold heap_alloc; heap_event.
    rewrite (heap_handler_alloc_first h allocs size base aux Pos B' Free First),
      bind_ret_l; reflexivity.
  Qed.

  (** A valid free continues with the released memory. *)
  Lemma interp_heap_free {X} base (memory memory' : ManagedHeap) (aux : Sigma)
    (k : unit -> ctree (heapE +' G) B X) :
    managed_free memory base = Some memory' ->
    interp_state (h_sum heap_handler other) (x <- heap_free base;; k x) (memory,aux) ~
      interp_state (h_sum heap_handler other) (k tt) (memory',aux).
  Proof.
    intro H; unfold heap_free; heap_event.
    rewrite (heap_handler_free base memory memory' aux H), bind_ret_l; reflexivity.
  Qed.

  (** An invalid free never runs its continuation. *)
  Lemma interp_heap_free_invalid {X} base (memory : ManagedHeap) (aux : Sigma)
    (k : unit -> ctree (heapE +' G) B X) :
    managed_free memory base = None ->
    interp_state (h_sum heap_handler other) (x <- heap_free base;; k x) (memory,aux) ~ (Stuck : ctree F B ((ManagedHeap * Sigma) * X)).
  Proof.
    intro H; unfold heap_free; heap_event.
    rewrite (heap_handler_free_invalid base memory aux H), bind_stuck; reflexivity.
  Qed.
End HeapInterp.
