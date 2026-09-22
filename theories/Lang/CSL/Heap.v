From Stdlib Require Import
  List
  Lia
  Arith.PeanoNat.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Interp.State.Mod
  ICTree.Events.State
  ICTree.Events.Writer
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.State
  Logic.Core.

From TICL Require Export Lang.CSL.Pcm.

Definition upd (h : Heap) (a v : nat) : Heap :=
  fun x => if Nat.eqb x a then Some v else h x.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.

Local Typeclasses Transparent equ.
Local Typeclasses Transparent sbisim.

(** ** The queue-tagged observation alphabet *)

Record SObs : Type := SPop { stag: nat ; sval: nat ; sidx: nat }.

(** ** Events *)

Variant sE : Type :=
  | SRd (a: nat)
  | SWr (a: nat) (v: nat)
  | SEmit (q: nat) (v: nat)
  | SAlloc (size: nat)
  | SCAS (a expected desired : nat).

Global Instance encode_sE: Encode sE :=
  fun e => match e with
           | SRd _ => nat | SWr _ _ => unit | SEmit _ _ => unit
           | SAlloc _ => nat
           | SCAS _ _ _ => bool
           end.

Definition srd (a: nat) : ictree sE nat := Vis (SRd a) (fun x: nat => Ret x).
Definition swr (a v: nat) : ictree sE unit := Vis (SWr a v) (fun _: unit => Ret tt).
Definition semit (q v: nat) : ictree sE unit :=
  Vis (SEmit q v) (fun _: unit => Ret tt).
Definition salloc (size : nat) : ictree sE nat :=
  Vis (SAlloc size) (fun a => Ret a).
Definition scas (a expected desired : nat) : ictree sE bool :=
  Vis (SCAS a expected desired) (fun b => Ret b).

(** Interpretation state: the SHARED heap (which holds both queues and the
    outer frame) and one GLOBAL occurrence counter. *)
Notation SSig := (Heap * nat)%type.

(** The immutable snapshot is searched without fuel or heap instrumentation.
    Every rejected candidate is silent; only success changes the shared heap. *)
Fixpoint block_freeb (h : Heap) (base size : nat) : bool :=
  match size with
  | 0 => true
  | S rest =>
      match h base with
      | None => block_freeb h (S base) rest
      | Some _ => false
      end
  end.

CoFixpoint alloc_search (h : Heap) (size candidate c : nat)
  : ictreeW SObs (nat * SSig) :=
  match size with
  | 0 => stuck
  | S _ =>
      if block_freeb h candidate size
      then Ret (candidate, (hunion (hblock candidate size) h, c))
      else Guard (alloc_search h size (S candidate) c)
  end.

(** ** Checked accesses and constructive allocation in one shared handler. *)
Definition sh: sE ~> stateT SSig (ictreeW SObs) :=
  fun e =>
    mkStateT (fun s =>
                match e return ictreeW SObs (encode e * SSig) with
                | SRd a => match fst s a with
                          | Some v => Ret (v, s)
                          | None => ICtree.stuck
                          end
                | SWr a v => match fst s a with
                            | Some _ => Ret (tt, (upd (fst s) a v, snd s))
                            | None => ICtree.stuck
                            end
                | SEmit q v => log (SPop q v (snd s)) ;; Ret (tt, (fst s, S (snd s)))
                | SAlloc size => alloc_search (fst s) size 1 (snd s)
                | SCAS a expected desired =>
                    match fst s a with
                    | None => stuck
                    | Some current =>
                        if Nat.eqb current expected
                        then Ret (true, (upd (fst s) a desired, snd s))
                        else Ret (false, s)
                    end
                end).

(** *** Handler equations *)

Lemma sh_rd_some: forall a h c v,
    h a = Some v -> runStateT (sh (SRd a)) (h, c) ≅ Ret (v, (h, c)).
Proof. intros a h c v H; cbn; rewrite H; reflexivity. Qed.

Lemma sh_rd_none: forall a h c,
    h a = None -> runStateT (sh (SRd a)) (h, c) ≅ ICtree.stuck.
Proof. intros a h c H; cbn; rewrite H; reflexivity. Qed.

Lemma sh_wr_some: forall a h c v w,
    h a = Some w -> runStateT (sh (SWr a v)) (h, c) ≅ Ret (tt, (upd h a v, c)).
Proof. intros a h c v w H; cbn; rewrite H; reflexivity. Qed.

Lemma sh_emit: forall q v h c,
    runStateT (sh (SEmit q v)) (h, c) ≅ (log (SPop q v c) ;; Ret (tt, (h, S c))).
Proof. intros; cbn; reflexivity. Qed.

Lemma sh_cas_success a expected desired h c :
  h a = Some expected ->
  runStateT (sh (SCAS a expected desired)) (h,c) ≅
    Ret (true,(upd h a desired,c)).
Proof. intro H; cbn; rewrite H, Nat.eqb_refl; reflexivity. Qed.

Lemma sh_cas_failure a expected desired current h c :
  h a = Some current -> current <> expected ->
  runStateT (sh (SCAS a expected desired)) (h,c) ≅ Ret (false,(h,c)).
Proof.
  intros H N; cbn; rewrite H.
  apply Nat.eqb_neq in N; rewrite N; reflexivity.
Qed.

Lemma sh_cas_missing a expected desired h c :
  h a = None ->
  runStateT (sh (SCAS a expected desired)) (h,c) ≅
    (stuck : ictreeW SObs (bool * SSig)).
Proof. intro H; cbn; rewrite H; reflexivity. Qed.

(** *** Lifting through [interp_state] *)

Lemma sinterp_rd {X}: forall a h c v (k: nat -> ictree sE X),
    h a = Some v ->
    interp_state sh (x <- srd a ;; k x) (h, c) ~ interp_state sh (k v) (h, c).
Proof.
  intros a h c v k H.
  unfold srd; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis.
  rewrite (sh_rd_some a h c v H), bind_ret_l.
  apply sb_guard.
Qed.

Lemma sinterp_wr {X}: forall a h c v w (k: unit -> ictree sE X),
    h a = Some w ->
    interp_state sh (x <- swr a v ;; k x) (h, c)
    ~ interp_state sh (k tt) (upd h a v, c).
Proof.
  intros a h c v w k H.
  unfold swr; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis.
  rewrite (sh_wr_some a h c v w H), bind_ret_l.
  apply sb_guard.
Qed.

Lemma sinterp_wr' {X}: forall a h c v (k: unit -> ictree sE X),
    h a <> None ->
    interp_state sh (x <- swr a v ;; k x) (h, c)
    ~ interp_state sh (k tt) (upd h a v, c).
Proof.
  intros a h c v k H; destruct (h a) as [w |] eqn:E; [| contradiction].
  eapply sinterp_wr; eauto.
Qed.

Lemma sinterp_emit {X}: forall q v h c (k: unit -> ictree sE X),
    interp_state sh (x <- semit q v ;; k x) (h, c)
    ~ (log (SPop q v c) ;; interp_state sh (k tt) (h, S c)).
Proof.
  intros q v h c k.
  unfold semit; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis, sh_emit, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l; apply sb_guard.
Qed.

Lemma sinterp_cas_success {X} a expected desired h c
  (k : bool -> ictree sE X) :
  h a = Some expected ->
  interp_state sh (b <- scas a expected desired;; k b) (h,c) ~
    interp_state sh (k true) (upd h a desired,c).
Proof.
  intro H; unfold scas; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis, (sh_cas_success a expected desired h c H), bind_ret_l.
  apply sb_guard.
Qed.

Lemma sinterp_cas_failure {X} a expected desired current h c
  (k : bool -> ictree sE X) :
  h a = Some current -> current <> expected ->
  interp_state sh (b <- scas a expected desired;; k b) (h,c) ~
    interp_state sh (k false) (h,c).
Proof.
  intros H N; unfold scas; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis,
    (sh_cas_failure a expected desired current h c H N), bind_ret_l.
  apply sb_guard.
Qed.

Lemma sinterp_cas_missing {X} a expected desired h c
  (k : bool -> ictree sE X) :
  h a = None ->
  interp_state sh (b <- scas a expected desired;; k b) (h,c) ~
    (stuck : ictreeW SObs (X * SSig)).
Proof.
  intro H; unfold scas; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis, (sh_cas_missing a expected desired h c H).
  rewrite bind_stuck_equ; reflexivity.
Qed.

(** An out-of-footprint read cannot step. *)
Lemma sinterp_rd_nostep {X}: forall a h c (k: nat -> ictree sE X) w,
    h a = None ->
    ~ can_step (interp_state sh (x <- srd a ;; k x) (h, c)) w.
Proof.
  intros a h c k w H.
  unfold srd; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis, (sh_rd_none a h c H).
  intro Hs; apply can_step_bind in Hs as [(t' & w' & TR & _) | (y & w' & TR & _)];
    revert TR; apply ktrans_stuck.
Qed.

Lemma sh_wr_none : forall a h c v,
    h a = None -> runStateT (sh (SWr a v)) (h,c) ≅ stuck.
Proof. intros a h c v H; cbn; rewrite H; reflexivity. Qed.

Lemma sinterp_srd_stuck a h c :
  h a = None ->
  interp_state sh (srd a) (h,c) ≅ (stuck : ictreeW SObs (nat * SSig)).
Proof.
  intro H; unfold srd.
  rewrite interp_state_vis, (sh_rd_none a h c H).
  apply bind_stuck_equ.
Qed.

Lemma sinterp_swr_stuck a v h c :
  h a = None ->
  interp_state sh (swr a v) (h,c) ≅ (stuck : ictreeW SObs (unit * SSig)).
Proof.
  intro H; unfold swr.
  rewrite interp_state_vis, (sh_wr_none a h c v H).
  apply bind_stuck_equ.
Qed.

Lemma upd_pcm h a v : heq (upd h a v) (Pcm.hupd a v h).
Proof.
  intro x; unfold upd, Pcm.hupd.
  destruct (Nat.eqb_spec x a); destruct (Nat.eq_dec a x); congruence.
Qed.

(** ** Allocation laws *)

Lemma block_freeb_spec h base size :
  block_freeb h base size = true <-> block_free h base size.
Proof.
  revert base; induction size as [|size IH]; intro base.
  - split; [intros _ offset O; lia | reflexivity].
  - cbn [block_freeb]; destruct (h base) as [v|] eqn:E.
    + split; [discriminate | intro F].
      specialize (F 0 ltac:(lia)); rewrite Nat.add_0_r, E in F; discriminate.
    + rewrite IH; split.
      * intros F [|offset] O.
        -- now rewrite Nat.add_0_r.
        -- replace (base + S offset)%nat with (S base + offset)%nat by lia; apply F; lia.
      * intros F offset O.
        replace (S base + offset)%nat with (base + S offset)%nat by lia; apply F; lia.
Qed.

Lemma unfold_alloc_search h size candidate c :
  alloc_search h size candidate c ≅
  match size with
  | 0 => stuck
  | S _ => if block_freeb h candidate size
           then Ret (candidate, (hunion (hblock candidate size) h, c))
           else Guard (alloc_search h size (S candidate) c)
  end.
Proof.
  step; cbn; unfold observe; cbn; reflexivity.
Qed.

Lemma alloc_search_first h size start base c :
  Nat.lt 0 size -> Nat.le start base -> block_free h base size ->
  (forall j, Nat.le start j -> Nat.lt j base -> ~ block_free h j size) ->
  alloc_search h size start c ~
    Ret (base, (hunion (hblock base size) h, c)).
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

Lemma sh_alloc_zero h c :
  runStateT (sh (SAlloc 0)) (h,c) ≅
    (stuck : ictreeW SObs (nat * SSig)).
Proof. apply unfold_alloc_search. Qed.

Lemma sh_alloc_first h size base c :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  runStateT (sh (SAlloc size)) (h,c) ~
    Ret (base, (hunion (hblock base size) h, c)).
Proof.
  intros Pos B F First; apply alloc_search_first; try assumption; try lia.
Qed.

Lemma sh_alloc_finite h size c :
  heap_finite h -> Nat.lt 0 size ->
  exists base,
    Nat.lt 0 base /\ block_free h base size /\
    (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) /\
    runStateT (sh (SAlloc size)) (h,c) ~
      Ret (base, (hunion (hblock base size) h, c)).
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
      + destruct (IH (S start) ltac:(lia)) as (base & L & F & First).
        exists base; split; [lia |]; split; [exact F |].
        intros j J Lt Free; destruct (Nat.eq_dec j start) as [E|E].
        * subst j; apply block_freeb_spec in Free; congruence.
        * apply (First j); try lia; exact Free. }
  destruct (Search (Nat.max 1 B - 1) 1 ltac:(lia))
    as (base & L & F & First).
  exists base; split; [lia |]; split; [exact F |]; split.
  - intros j J Lt; apply First; lia.
  - apply sh_alloc_first; try assumption; try lia.
Qed.

Lemma sinterp_salloc_zero h c :
  interp_state sh (salloc 0) (h,c) ≅
    (stuck : ictreeW SObs (nat * SSig)).
Proof.
  unfold salloc; rewrite interp_state_vis, sh_alloc_zero.
  apply bind_stuck_equ.
Qed.

Lemma sinterp_alloc_first {X} h size base c (k : nat -> ictree sE X) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  interp_state sh (a <- salloc size;; k a) (h,c) ~
    interp_state sh (k base) (hunion (hblock base size) h,c).
Proof.
  intros Pos B F First.
  unfold salloc; rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis, (sh_alloc_first h size base c Pos B F First), bind_ret_l.
  apply sb_guard.
Qed.

Lemma heap_finite_upd h a v : heap_finite h -> heap_finite (upd h a v).
Proof.
  intros [B Bound]; exists (Nat.max B (S a)); intros x X.
  unfold upd; destruct (Nat.eqb_spec x a); [lia | apply Bound; lia].
Qed.

Lemma alloc_search_no_space h size start c :
  Nat.lt 0 size ->
  (forall j, Nat.le start j -> ~ block_free h j size) ->
  alloc_search h size start c ≅ (stuck : ictreeW SObs (nat * SSig)).
Proof.
  intros Pos Full; destruct size as [|size]; [lia |].
  revert start Full; __coinduction_equ R CIH; intros start Full.
  assert (Test : block_freeb h start (S size) = false).
  { destruct (block_freeb h start (S size)) eqn:T; [|reflexivity].
    exfalso; apply (Full start); [lia | apply block_freeb_spec; exact T]. }
  rewrite unfold_alloc_search, Test, unfold_stuck.
  constructor; apply CIH; intros j J; apply Full; lia.
Qed.
