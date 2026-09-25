(** * Checked heap accesses and constructive allocation, in one handler.

    The handler is polymorphic in its OUTPUT effect [F] and in an untouched
    auxiliary state [Sigma]; the heap itself is the first component of the
    interpretation state.  Instrumented interpreters instantiate [F] with a
    writer effect and [Sigma] with their own bookkeeping; a pure client may
    instantiate [F := void] and [Sigma := unit].

    The algorithm is fixed: allocation starts at address 1, rejects size 0,
    searches the immutable snapshot for the first free positive block, keeps
    rejected candidates silent, preserves [aux], propagates a missing
    read/write/CAS as [stuck], leaves the whole state unchanged on a failed
    CAS, and lets a free of an absent cell succeed.  There is no least-address
    axiom, no fuel, and no failure fallback. *)

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

Definition heap_handler {F : Type} {HF : Encode F} {Sigma : Type}
  : heapE ~> stateT (Heap * Sigma) (ictree F) :=
  fun e =>
    mkStateT (fun s =>
      match e return ictree F (encode e * (Heap * Sigma)) with
      | HRead a => match fst s a with
                   | Some v => Ret (v,s)
                   | None => stuck
                   end
      | HWrite a v => match fst s a with
                      | Some _ => Ret (tt,(upd (fst s) a v,snd s))
                      | None => stuck
                      end
      | HAlloc size => alloc_search (fst s) size 1 (snd s)
      | HFree a => Ret (tt,(hfree a (fst s),snd s))
      | HCAS a expected desired =>
          match fst s a with
          | None => stuck
          | Some current =>
              if Nat.eqb current expected
              then Ret (true,(upd (fst s) a desired,snd s))
              else Ret (false,s)
          end
      end).

(** ** Raw handler equations.

    These are the canonical response certificates a first-yield segment
    discharges; they are handler equations, not interpreter equations. *)
Section HandlerEquations.
  Context {F : Type} {HF : Encode F} {Sigma : Type}.

  Lemma heap_handler_rd_some : forall a h (aux : Sigma) v,
    h a = Some v ->
    runStateT (heap_handler (F:=F) (HRead a)) (h,aux) ≅ Ret (v,(h,aux)).
  Proof. intros a h aux v H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_rd_none : forall a h (aux : Sigma),
    h a = None ->
    runStateT (heap_handler (F:=F) (HRead a)) (h,aux) ≅ stuck.
  Proof. intros a h aux H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_wr_some : forall a h (aux : Sigma) v w,
    h a = Some w ->
    runStateT (heap_handler (F:=F) (HWrite a v)) (h,aux) ≅
      Ret (tt,(upd h a v,aux)).
  Proof. intros a h aux v w H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_wr_none : forall a h (aux : Sigma) v,
    h a = None ->
    runStateT (heap_handler (F:=F) (HWrite a v)) (h,aux) ≅ stuck.
  Proof. intros a h aux v H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_cas_success a expected desired h (aux : Sigma) :
    h a = Some expected ->
    runStateT (heap_handler (F:=F) (HCAS a expected desired)) (h,aux) ≅
      Ret (true,(upd h a desired,aux)).
  Proof. intro H; cbn; rewrite H, Nat.eqb_refl; reflexivity. Qed.

  Lemma heap_handler_cas_failure a expected desired current h (aux : Sigma) :
    h a = Some current -> current <> expected ->
    runStateT (heap_handler (F:=F) (HCAS a expected desired)) (h,aux) ≅
      Ret (false,(h,aux)).
  Proof.
    intros H N; cbn; rewrite H.
    apply Nat.eqb_neq in N; rewrite N; reflexivity.
  Qed.

  Lemma heap_handler_cas_missing a expected desired h (aux : Sigma) :
    h a = None ->
    runStateT (heap_handler (F:=F) (HCAS a expected desired)) (h,aux) ≅
      (stuck : ictree F (bool * (Heap * Sigma))).
  Proof. intro H; cbn; rewrite H; reflexivity. Qed.

  Lemma heap_handler_free a h (aux : Sigma) :
    runStateT (heap_handler (F:=F) (HFree a)) (h,aux) ≅
      Ret (tt,(hfree a h,aux)).
  Proof. reflexivity. Qed.
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

  Lemma heap_handler_alloc_zero h (aux : Sigma) :
    runStateT (heap_handler (F:=F) (HAlloc 0)) (h,aux) ≅
      (stuck : ictree F (nat * (Heap * Sigma))).
  Proof. exact (unfold_alloc_search h 0 1 aux). Qed.

  Lemma heap_handler_alloc_first h size base (aux : Sigma) :
    Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    runStateT (heap_handler (F:=F) (HAlloc size)) (h,aux) ~
      Ret (base, (hunion (hblock base size) h, aux)).
  Proof.
    intros Pos B Free First.
    apply (alloc_search_first h size 1 base aux); try assumption; try lia.
  Qed.

  (** A finite heap always admits a first-fit witness. *)
  Lemma heap_handler_alloc_finite h size (aux : Sigma) :
    heap_finite h -> Nat.lt 0 size ->
    exists base,
      Nat.lt 0 base /\ block_free h base size /\
      (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) /\
      runStateT (heap_handler (F:=F) (HAlloc size)) (h,aux) ~
        Ret (base, (hunion (hblock base size) h, aux)).
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
    (other : G ~> stateT (Heap * Sigma) (ictree F)).

  Lemma interp_heap_rd {X} : forall a h (aux : Sigma) v
    (k : nat -> ictree (heapE + G) X),
    h a = Some v ->
    interp_state (h_sum heap_handler other) (x <- heap_read a;; k x) (h,aux) ~
      interp_state (h_sum heap_handler other) (k v) (h,aux).
  Proof.
    intros a h aux v k H.
    unfold heap_read, ICtree.trigger, resum, ReSum_inl, resum_ret, ReSumRet_inl.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_rd_some (F:=F) a h aux v H), bind_ret_l.
    apply sb_guard.
  Qed.

  Lemma interp_heap_wr {X} : forall a h (aux : Sigma) v w
    (k : unit -> ictree (heapE + G) X),
    h a = Some w ->
    interp_state (h_sum heap_handler other) (x <- heap_write a v;; k x) (h,aux) ~
      interp_state (h_sum heap_handler other) (k tt) (upd h a v,aux).
  Proof.
    intros a h aux v w k H.
    unfold heap_write, ICtree.trigger, resum, ReSum_inl, resum_ret, ReSumRet_inl.
    rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_wr_some (F:=F) a h aux v w H), bind_ret_l.
    apply sb_guard.
  Qed.

  Lemma interp_heap_wr_present {X} : forall a h (aux : Sigma) v
    (k : unit -> ictree (heapE + G) X),
    h a <> None ->
    interp_state (h_sum heap_handler other) (x <- heap_write a v;; k x) (h,aux) ~
      interp_state (h_sum heap_handler other) (k tt) (upd h a v,aux).
  Proof.
    intros a h aux v k H; destruct (h a) as [w |] eqn:Ha; [| contradiction].
    eapply interp_heap_wr; eauto.
  Qed.

  Lemma interp_heap_rd_stuck a h (aux : Sigma) :
    h a = None ->
    interp_state (h_sum heap_handler other) (heap_read (E:=heapE + G) a) (h,aux)
      ≅ (stuck : ictree F (nat * (Heap * Sigma))).
  Proof.
    intro H; unfold heap_read, ICtree.trigger.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_rd_none (F:=F) a h aux H).
    apply bind_stuck_equ.
  Qed.

  Lemma interp_heap_wr_stuck a v h (aux : Sigma) :
    h a = None ->
    interp_state (h_sum heap_handler other) (heap_write (E:=heapE + G) a v) (h,aux)
      ≅ (stuck : ictree F (unit * (Heap * Sigma))).
  Proof.
    intro H; unfold heap_write, ICtree.trigger.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_wr_none (F:=F) a h aux v H).
    apply bind_stuck_equ.
  Qed.

  Lemma interp_heap_cas_success {X} a expected desired h (aux : Sigma)
    (k : bool -> ictree (heapE + G) X) :
    h a = Some expected ->
    interp_state (h_sum heap_handler other)
      (b <- heap_cas a expected desired;; k b) (h,aux) ~
      interp_state (h_sum heap_handler other) (k true) (upd h a desired,aux).
  Proof.
    intro H; unfold heap_cas, ICtree.trigger; rewrite bind_vis;
      setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_cas_success (F:=F) a expected desired h aux H),
      bind_ret_l.
    apply sb_guard.
  Qed.

  Lemma interp_heap_cas_failure {X} a expected desired current h (aux : Sigma)
    (k : bool -> ictree (heapE + G) X) :
    h a = Some current -> current <> expected ->
    interp_state (h_sum heap_handler other)
      (b <- heap_cas a expected desired;; k b) (h,aux) ~
      interp_state (h_sum heap_handler other) (k false) (h,aux).
  Proof.
    intros H N; unfold heap_cas, ICtree.trigger; rewrite bind_vis;
      setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_cas_failure (F:=F) a expected desired current h aux H N),
      bind_ret_l.
    apply sb_guard.
  Qed.

  Lemma interp_heap_cas_missing {X} a expected desired h (aux : Sigma)
    (k : bool -> ictree (heapE + G) X) :
    h a = None ->
    interp_state (h_sum heap_handler other)
      (b <- heap_cas a expected desired;; k b) (h,aux) ~
      (stuck : ictree F (X * (Heap * Sigma))).
  Proof.
    intro H; unfold heap_cas, ICtree.trigger; rewrite bind_vis;
      setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_cas_missing (F:=F) a expected desired h aux H).
    rewrite bind_stuck_equ; reflexivity.
  Qed.

  Lemma interp_heap_alloc_zero h (aux : Sigma) :
    interp_state (h_sum heap_handler other) (heap_alloc (E:=heapE + G) 0) (h,aux)
      ≅ (stuck : ictree F (nat * (Heap * Sigma))).
  Proof.
    unfold heap_alloc, ICtree.trigger, resum, resum_ret, ReSum_inl, ReSumRet_inl.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_alloc_zero (F:=F) h aux).
    apply bind_stuck_equ.
  Qed.

  Lemma interp_heap_alloc_first {X} h size base (aux : Sigma)
    (k : nat -> ictree (heapE + G) X) :
    Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
    interp_state (h_sum heap_handler other) (a <- heap_alloc size;; k a) (h,aux) ~
      interp_state (h_sum heap_handler other) (k base)
        (hunion (hblock base size) h,aux).
  Proof.
    intros Pos B Free First.
    unfold heap_alloc, ICtree.trigger, resum, ReSum_inl, resum_ret, ReSumRet_inl;
      rewrite bind_vis; setoid_rewrite bind_ret_l.
    rewrite interp_state_vis; cbn [h_sum].
    rewrite (heap_handler_alloc_first (F:=F) h size base aux Pos B Free First),
      bind_ret_l.
    apply sb_guard.
  Qed.
End HeapInterp.
