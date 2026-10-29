From Stdlib Require Import List Arith.PeanoNat.
From Coinduction Require Import all.
From TICL Require Import
  CTree.Core
  CTree.Events.Writer
  Logic.World.

Unset Implicit Arguments.
Import CTree CTreeNotations CoindNotations ListNotations.
Local Open Scope ctree_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(** * Finite observation traces and their operational laws. *)

Definition emit_list {W : Type} {B : Type -> Type} {X : Type} (xs : list W) (t : ctreeW W B X) : ctreeW W B X :=
  List.fold_right (fun o k => log o;; k) t xs.

(** The observations produced by one step, which emits at most one. *)
Definition event_obs {W} (event : option W) : list W :=
  match event with None => [] | Some o => [o] end.

Definition label_logs {W} (labels : list (@label (writerE W))) : list W :=
  List.flat_map (fun l => match l with obs (Log o) _ => [o] | _ => [] end) labels.

Definition label_taus {W} (labels : list (@label (writerE W))) : nat :=
  List.length (List.filter (fun l => match l with τ => true | _ => false end) labels).

Fixpoint after_logs {W} (xs : list W) (w : World (writerE W)) : World (writerE W) :=
  match xs with
  | [] => w
  | o :: rest => after_logs rest (Obs (Log o) tt)
  end.

Lemma after_logs_not_done {W} (xs : list W) w : not_done w -> not_done (after_logs xs w).
Proof.
  revert w; induction xs as [|o rest IH]; intros w Hd; cbn [after_logs].
  - exact Hd.
  - apply IH; constructor.
Qed.

Lemma emit_list_cons {W : Type} {B : Type -> Type} {X : Type} o xs (t : ctreeW W B X) :
  emit_list (o :: xs) t ≅ Vis (Log o) (fun _ => emit_list xs t).
Proof.
  change ((log o ;; emit_list xs t) ≅ Vis (Log o) (fun _ => emit_list xs t)).
  unfold log; rewrite bind_trigger; reflexivity.
Qed.

Lemma emit_list_app {W : Type} {B : Type -> Type} {X : Type} xs ys (t : ctreeW W B X) :
  emit_list (xs ++ ys) t = emit_list xs (emit_list ys t).
Proof. unfold emit_list; rewrite List.fold_right_app; reflexivity. Qed.

Lemma emit_list_equ {W : Type} {B : Type -> Type} {X : Type} xs (t u : ctreeW W B X) :
  t ≅ u -> emit_list xs t ≅ emit_list xs u.
Proof.
  intro E; induction xs as [|o xs IH]; [exact E|].
  rewrite !emit_list_cons; step; constructor; intro x; exact IH.
Qed.

Lemma emit_list_sbisim {W : Type} {B : Type -> Type} {X : Type} xs (t u : ctreeW W B X) :
  t ~ u -> emit_list xs t ~ emit_list xs u.
Proof.
  intro E; induction xs as [|o xs IH]; [exact E|].
  rewrite !emit_list_cons; apply sb_vis; intro x; exact IH.
Qed.

Lemma emit_list_bind {W : Type} {B : Type -> Type} {X Y : Type} xs (t : ctreeW W B X)
  (k : X -> ctreeW W B Y) :
  emit_list xs t >>= k ≅ emit_list xs (t >>= k).
Proof.
  induction xs as [|o xs IH]; [reflexivity|].
  change (((log o ;; emit_list xs t) >>= k) ≅
    (log o ;; emit_list xs (t >>= k))).
  etransitivity; [apply bind_bind|].
  apply equ_clo_bind_eq; intros []; exact IH.
Qed.

Lemma emit_list_ret_bind {W : Type} {B : Type -> Type} {X Y : Type} xs (x : X) (k : X -> ctreeW W B Y) :
  emit_list xs (Ret x) >>= k ≅ emit_list xs (k x).
Proof.
  etransitivity; [apply emit_list_bind|].
  apply emit_list_equ, bind_ret_l.
Qed.

(** Return values are observable labels, including when they contain heaps.
    This proves equality of actual responses; it never identifies merely
    pointwise-equal heap functions. *)
Lemma emit_list_ret_injective {W : Type} {B : Type -> Type} {X : Type} (xs ys : list W) (x y : X) :
  emit_list (B := B) xs (Ret x) ~ emit_list (B := B) ys (Ret y) -> xs = ys /\ x = y.
Proof.
  revert ys; induction xs as [|o xs IH]; intros [|p ys] E.
  - split; [reflexivity|]. exact (sbisim_ret_inv E).
  - rewrite emit_list_cons in E.
    exfalso; exact (sbisim_ret_vis_inv E).
  - rewrite emit_list_cons in E.
    exfalso; eapply sbisim_ret_vis_inv; symmetry; exact E.
  - rewrite !emit_list_cons in E.
    pose proof (sbisim_vis_inv tt E) as [Eo Etail].
    injection Eo as Eo; subst p.
    destruct (IH ys (Etail tt)) as [-> ->]; auto.
Qed.

Lemma emit_list_ret_not_stuck {W : Type} {B : Type -> Type} {X : Type} xs (x : X) :
  ~ (emit_list (B := B) xs (Ret x) ~ (Stuck : ctreeW W B X)).
Proof.
  intro E.
  assert (S : is_stuck (emit_list xs (Ret x))) by (rewrite E; apply Stuck_is_stuck).
  destruct xs as [|o xs].
  - apply (S (val x) Stuck), trans_ret.
  - apply (S (obs (Log o) tt) (emit_list xs (Ret x))).
    rewrite emit_list_cons.
    exact (trans_vis (Log o) tt (fun _ => emit_list xs (Ret x))).
Qed.

Lemma emit_list_chain {W : Type} {B : Type -> Type} {X : Type} {R : Chain (@sb (writerE W) (writerE W) B B X X eq)}
  logs (t u : ctreeW W B X) :
  `R t u -> `R (emit_list logs t) (emit_list logs u).
Proof.
  intro H; induction logs as [|o rest IH]; [exact H|].
  (* [vis_chain] rather than [sb_chain_bind_eq]: the latter pins the result
     universe of [X] to that of [writerE], which rejects large state types. *)
  rewrite !emit_list_cons; apply vis_chain; intros []; exact IH.
Qed.

Inductive finite_steps {E B : Type -> Type} {X : Type} :
  ctree E B X -> list (@label E) -> ctree E B X -> Prop :=
| finite_steps_nil t : finite_steps t [] t
| finite_steps_cons t u v l labels :
    trans l t u -> finite_steps u labels v -> finite_steps t (l :: labels) v.

Definition turn_labels {W} (event : option W) : list (@label (writerE W)) :=
  match event with None => [τ] | Some o => [τ; obs (Log o) tt] end.

Lemma turn_labels_nonempty {W} (event : option W) : turn_labels event <> [].
Proof. destruct event; discriminate. Qed.

Lemma finite_steps_app {E B : Type -> Type} {X : Type}
  (t u v : ctree E B X) left right :
  finite_steps t left u -> finite_steps u right v ->
  finite_steps t (left ++ right) v.
Proof.
  intros H; induction H; intro Htail; cbn [List.app];
    [exact Htail|econstructor; eauto].
Qed.

Lemma finite_steps_sbisim {E B : Type -> Type} {X : Type}
  (t t' : ctree E B X) labels :
  finite_steps t labels t' -> forall u : ctree E B X, t ~ u ->
  exists u', finite_steps u labels u' /\ t' ~ u'.
Proof.
  intro H; induction H as [t|t mid last l labels Hstep Htail IH]; intros u Eeq.
  - exists u; split; [constructor|exact Eeq].
  - step in Eeq; destruct Eeq as [Hf _]; cbn in Hf.
    destruct (Hf _ _ Hstep) as (l' & mid' & Hstep' & Emid & <-).
    destruct (IH mid' Emid) as (last' & Htail' & Elast).
    exists last'; split; [econstructor; eassumption|exact Elast].
Qed.

Lemma finite_steps_emit_list {W : Type} {B : Type -> Type} {X : Type} logs (t : ctreeW W B X) :
  finite_steps (emit_list logs t) (List.map (fun o => obs (Log o) tt) logs) t.
Proof.
  induction logs as [|o logs IH]; [constructor|].
  cbn [List.map]; econstructor; [|exact IH].
  rewrite emit_list_cons.
  exact (trans_vis (Log o) tt (fun _ => emit_list logs t)).
Qed.

(** * Realizing an infinite sequence of finite label chunks.

    Each chunk must be NONEMPTY: an empty chunk cannot witness progress of a
    stuck tree, so the productivity of the realization is genuine. *)
CoInductive realizes {E B : Type -> Type} {X : Type}
  (chunks : nat -> list (@label E)) (k : nat) (t : ctree E B X) : Prop :=
| realizes_next next :
    chunks k <> [] ->
    finite_steps t (chunks k) next ->
    realizes chunks (S k) next -> realizes chunks k t.

(** Any tree bisimilar to a root of a chunked sequence realizes its suffix. *)
Lemma realizes_from_steps {E B : Type -> Type} {X : Type}
  (chunks : nat -> list (@label E)) (roots : nat -> ctree E B X) :
  (forall k, chunks k <> []) ->
  (forall k, exists next,
     finite_steps (roots k) (chunks k) next /\ next ~ roots (S k)) ->
  forall k (t : ctree E B X), t ~ roots k -> realizes chunks k t.
Proof.
  intros Hne Hstep; cofix CIH; intros k t Eeq.
  destruct (Hstep k) as (next & Hsteps & Enext).
  assert (Esym : roots k ~ t) by (symmetry; exact Eeq).
  destruct (finite_steps_sbisim _ _ _ Hsteps t Esym) as (next' & Hsteps' & Enext').
  eapply realizes_next; [apply Hne|exact Hsteps'|].
  apply CIH; transitivity next; [symmetry; exact Enext'|exact Enext].
Qed.

(** * Guard/log alignment and finite prefixes. *)

Fixpoint rr_guards {W : Type} {B : Type -> Type} {X : Type} (n : nat) (t : ctreeW W B X) : ctreeW W B X :=
  match n with 0 => t | S n => Guard (rr_guards n t) end.

Lemma rr_guards_trans {W : Type} {B : Type -> Type} {X : Type} n l (t u : ctreeW W B X) :
  trans l t u -> trans l (rr_guards n t) u.
Proof. intro H; induction n; cbn [rr_guards]; [exact H|now apply trans_guard]. Qed.

(** This proof relation consumes a guard on BOTH sides in a silent round.
    Its finite prefixes cannot turn silent divergence into a visible event. *)
CoInductive rr_aligned {W : Type} {B : Type -> Type} {X : Type} : ctreeW W B X -> ctreeW W B X -> Prop :=
| rr_align_guard t u n m t' u' :
    t ≅ rr_guards (S n) t' -> u ≅ rr_guards (S m) u' ->
    rr_aligned t' u' -> rr_aligned t u
| rr_align_log t u n m o t' u' :
    t ≅ rr_guards n (Vis (Log o) (fun _ => t')) ->
    u ≅ rr_guards m (Vis (Log o) (fun _ => u')) ->
    rr_aligned t' u' -> rr_aligned t u.

Lemma rr_aligned_equ {W : Type} {B : Type -> Type} {X : Type} (t u a b : ctreeW W B X) :
  t ≅ a -> u ≅ b -> rr_aligned t u -> rr_aligned a b.
Proof.
  intros Et Eu H; destruct H as [t u n m t' u' El Er H|t u n m o t' u' El Er H].
  - eapply rr_align_guard; [| |exact H].
    + transitivity t; [symmetry; exact Et|exact El].
    + transitivity u; [symmetry; exact Eu|exact Er].
  - eapply rr_align_log; [| |exact H].
    + transitivity t; [symmetry; exact Et|exact El].
    + transitivity u; [symmetry; exact Eu|exact Er].
Qed.

Lemma rr_aligned_sym {W : Type} {B : Type -> Type} {X : Type} : forall t u : ctreeW W B X,
  rr_aligned t u -> rr_aligned u t.
Proof.
  cofix IH; intros t u H;
    destruct H as [t u n m t' u' El Er H|t u n m o t' u' El Er H].
  - eapply rr_align_guard; [exact Er|exact El|apply IH; exact H].
  - eapply rr_align_log; [exact Er|exact El|apply IH; exact H].
Qed.

(** An aligned tree is, up to [≅], a stack of guards over a guard or a log,
    so neither [Br], [Step] nor [Ret] can appear at its head. *)
Lemma rr_aligned_match {W : Type} {B : Type -> Type} {X : Type} l T U :
  @trans_ (writerE W) B X l T U ->
  forall u, rr_aligned (go T) u ->
  exists u', trans l u u' /\ rr_aligned (go U) u'.
Proof.
  intro TR; induction TR as
    [Y c pick k l target TR IH
    |inner target l TR IH
    |target result Eresult
    |Y e k answer result Eresult
    |value]; intros u A.
  - inversion A as [left right n m tl tr El Er Hnext|left right n m o tl tr El Er Hnext];
      subst; clear A; destruct n; step in El; cbn [rr_guards observe] in El; inversion El.
  - inversion A as [left right n m tl tr El Er Hnext|left right n m o tl tr El Er Hnext];
      subst; clear A; rename Hnext into A.
    + apply equ_guard_inv in El; destruct n as [|n].
      * cbn [rr_guards] in El.
        assert (Ai : rr_aligned (go (observe inner)) tr).
        { eapply rr_aligned_equ; [|reflexivity|exact A].
          transitivity inner; [symmetry; exact El|apply ctree_eta]. }
        destruct (IH tr Ai) as (next & Tnext & Anext).
        exists next; split; [rewrite Er; now apply rr_guards_trans|exact Anext].
      * apply IH; eapply rr_aligned_equ; [apply ctree_eta|reflexivity|].
        eapply rr_align_guard; eassumption.
    + destruct n as [|n].
      * cbn [rr_guards] in El; step in El; cbn in El; inversion El.
      * apply equ_guard_inv in El.
        apply IH; eapply rr_aligned_equ; [apply ctree_eta|reflexivity|].
        eapply rr_align_log; eassumption.
  - inversion A as [left right n m tl tr El Er Hnext|left right n m o tl tr El Er Hnext];
      subst; clear A; destruct n; step in El; cbn [rr_guards observe] in El; inversion El.
  - destruct e as [o]; destruct answer.
    inversion A as [left right n m tl tr El Er Hnext|left right n m p tl tr El Er Hnext];
      subst; clear A; rename Hnext into A.
    + step in El; cbn [rr_guards] in El; inversion El.
    + destruct n as [|n].
      * cbn [rr_guards] in El.
        pose proof (equ_vis_invE _ _ _ _ El) as [Ep Ek]; injection Ep as Ep; subst p.
        exists tr; split.
        -- rewrite Er; apply rr_guards_trans.
           exact (trans_vis (Log o) tt (fun _ => tr)).
        -- eapply rr_aligned_equ; [|reflexivity|exact A].
           transitivity (k tt); [symmetry; exact (Ek tt)|].
           transitivity result; [exact Eresult|apply ctree_eta].
      * step in El; cbn [rr_guards] in El; inversion El.
  - inversion A as [left right n m tl tr El Er Hnext|left right n m o tl tr El Er Hnext];
      subst; clear A; destruct n; step in El; cbn [rr_guards observe] in El; inversion El.
Qed.

Lemma rr_aligned_trans {W : Type} {B : Type -> Type} {X : Type} (t u next : ctreeW W B X) l :
  rr_aligned t u -> trans l t next ->
  exists other, trans l u other /\ rr_aligned next other.
Proof.
  intros A TR.
  assert (Ae : rr_aligned (go (observe t)) u).
  { eapply rr_aligned_equ; [apply ctree_eta|reflexivity|exact A]. }
  destruct (rr_aligned_match l (observe t) (observe next) TR u Ae)
    as (other & To & Ao).
  exists other; split; [exact To|].
  eapply rr_aligned_equ; [symmetry; apply ctree_eta|reflexivity|exact Ao].
Qed.

Lemma rr_aligned_sbisim {W : Type} {B : Type -> Type} {X : Type} : forall t u : ctreeW W B X,
  rr_aligned t u -> t ~ u.
Proof.
  unfold sbisim; coinduction R IH.
  intros t u A; split; intros l next TR.
  - destruct (rr_aligned_trans t u next l A TR) as (other & To & Ao).
    exists l, other; split; [exact To|]; split; [now apply IH|reflexivity].
  - destruct (rr_aligned_trans u t next l (rr_aligned_sym t u A) TR)
      as (other & To & Ao).
    exists l, other; split; [exact To|]; split.
    + apply IH, rr_aligned_sym; exact Ao.
    + reflexivity.
Qed.

Lemma rr_guards_equ {W : Type} {B : Type -> Type} {X : Type} n (t u : ctreeW W B X) :
  t ≅ u -> rr_guards n t ≅ rr_guards n u.
Proof.
  intro E; induction n; cbn [rr_guards]; [exact E|step; constructor; assumption].
Qed.
Lemma rr_guards_add {W : Type} {B : Type -> Type} {X : Type} n m (t : ctreeW W B X) :
  rr_guards (n + m) t = rr_guards n (rr_guards m t).
Proof. induction n; cbn [rr_guards Nat.add]; [reflexivity|now rewrite IHn]. Qed.
Lemma rr_guards_guard {W : Type} {B : Type -> Type} {X : Type} n (t : ctreeW W B X) :
  rr_guards n (Guard t) = rr_guards (S n) t.
Proof. induction n; cbn [rr_guards]; [reflexivity|now rewrite IHn]. Qed.

(** A finite proof prefix, not an additional evaluator or scheduler. *)
Inductive rr_token {W : Type} := RRGuard | RRLog (o : W).
Fixpoint rr_prefix {W : Type} {B : Type -> Type} {X : Type} (word : list (@rr_token W)) (t : ctreeW W B X) : ctreeW W B X :=
  match word with
  | [] => t
  | RRGuard :: rest => Guard (rr_prefix rest t)
  | RRLog o :: rest => Vis (Log o) (fun _ => rr_prefix rest t)
  end.
Fixpoint rr_prefix_events {W} (word : list (@rr_token W)) : list W :=
  match word with
  | [] => []
  | RRGuard :: rest => rr_prefix_events rest
  | RRLog o :: rest => o :: rr_prefix_events rest
  end.
Lemma rr_prefix_app {W : Type} {B : Type -> Type} {X : Type} left right (t : ctreeW W B X) :
  rr_prefix (left ++ right) t = rr_prefix left (rr_prefix right t).
Proof.
  induction left as [|[|o] rest IH]; cbn [List.app rr_prefix];
    [reflexivity|now rewrite IH|now rewrite IH].
Qed.
Lemma rr_prefix_equ {W : Type} {B : Type -> Type} {X : Type} word (t u : ctreeW W B X) :
  t ≅ u -> rr_prefix word t ≅ rr_prefix word u.
Proof.
  intro E; induction word as [|[|o] rest IH]; cbn [rr_prefix].
  - exact E.
  - step; constructor; assumption.
  - step; constructor; intros []; exact IH.
Qed.
Lemma rr_prefix_events_app {W} (left right : list (@rr_token W)) :
  rr_prefix_events (left ++ right) = rr_prefix_events left ++ rr_prefix_events right.
Proof.
  induction left as [|[|o] rest IH]; cbn [List.app rr_prefix_events];
    [reflexivity|exact IH|now rewrite IH].
Qed.
Lemma rr_prefix_events_logs {W} (logs : list W) : rr_prefix_events (List.map RRLog logs) = logs.
Proof. induction logs; cbn [List.map rr_prefix_events]; [reflexivity|now rewrite IHlogs]. Qed.
Lemma rr_prefix_emit {W : Type} {B : Type -> Type} {X : Type} logs (t : ctreeW W B X) :
  rr_prefix (List.map RRLog logs) t ≅ emit_list logs t.
Proof.
  induction logs as [|o rest IH]; [reflexivity|].
  cbn [List.map rr_prefix]; rewrite emit_list_cons.
  step; constructor; intros []; exact IH.
Qed.
Lemma rr_prefix_no_events {W : Type} {B : Type -> Type} {X : Type} word (t : ctreeW W B X) :
  rr_prefix_events word = [] -> rr_prefix word t = rr_guards (List.length word) t.
Proof.
  induction word as [|[|o] rest IH]; cbn [rr_prefix_events rr_prefix List.length rr_guards];
    intro E; [reflexivity|now rewrite IH|discriminate].
Qed.
Lemma rr_prefix_one_event {W : Type} {B : Type -> Type} {X : Type} word o (t : ctreeW W B X) :
  rr_prefix_events word = [o] -> exists n m,
  rr_prefix word t ≅ rr_guards n (Vis (Log o) (fun _ => rr_guards m t)).
Proof.
  induction word as [|[|p] rest IH]; cbn [rr_prefix_events]; intro E; [discriminate| |].
  - destruct (IH E) as (n & m & H).
    exists (S n), m; cbn [rr_prefix rr_guards]; step; constructor; assumption.
  - injection E as Ep Er; subst p.
    exists 0, (List.length rest); cbn [rr_prefix rr_guards].
    step; constructor; intros []; rewrite (rr_prefix_no_events rest t Er); reflexivity.
Qed.

(** * Repeating finite observation batches.

    One public representation of a log loop: each round emits the finite
    batch of its index and advances the index.  Batches may be empty, but an
    empty batch cannot satisfy the productivity premise of the coinduction
    below -- no dummy log is inserted. *)
Definition emit_batches {W : Type} {B : Type -> Type} {I X : Type}
  (batch : I -> list W) (next : I -> I) (i : I) : ctreeW W B X :=
  CTree.iter (fun j => emit_list (batch j) (Ret (@inl I X (next j)))) i.

(** The RAW unfolding: the administrative guard of [iter] is retained. *)
Lemma emit_batches_unfold {W : Type} {B : Type -> Type} {I X : Type} (batch : I -> list W) (next : I -> I) i :
  (emit_batches batch next i : ctreeW W B X) ≅
    emit_list (batch i) (Guard (emit_batches batch next (next i))).
Proof.
  unfold emit_batches at 1; rewrite unfold_iter.
  rewrite emit_list_ret_bind; reflexivity.
Qed.

(** The same unfolding after absorbing the administrative guard. *)
Lemma emit_batches_unfold_sbisim {W : Type} {B : Type -> Type} {I X : Type} (batch : I -> list W) (next : I -> I) i :
  (emit_batches batch next i : ctreeW W B X) ~
    emit_list (batch i) (emit_batches batch next (next i) : ctreeW W B X).
Proof.
  rewrite emit_batches_unfold.
  apply emit_list_sbisim, sb_guard.
Qed.

(** A root family that emits its own batch each round IS the batch loop.
    The nonempty-batch premise is essential: silent self-equations alone do
    not justify this coinduction. *)
Lemma emit_batches_bisim {W : Type} {B : Type -> Type} {I X : Type} (batch : I -> list W) (next : I -> I)
  (Inv : I -> Prop) (root : I -> ctreeW W B X)
  (Hnext : forall i, Inv i -> Inv (next i))
  (Hnonempty : forall i, Inv i -> batch i <> [])
  (Hroot : forall i, Inv i -> root i ~ emit_list (batch i) (root (next i))) :
  forall i, Inv i -> root i ~ (emit_batches batch next i : ctreeW W B X).
Proof.
  unfold sbisim; coinduction R IH; intros i Hi.
  assert (Hstep : sb eq `R
      (emit_list (batch i) (root (next i)))
      (emit_list (batch i) (emit_batches batch next (next i) : ctreeW W B X))).
  { destruct (batch i) as [|o rest] eqn:Eb;
      [exfalso; exact (Hnonempty i Hi Eb) |].
    rewrite !emit_list_cons.
    apply step_sb_vis; intros []; exists tt; split; try reflexivity;
      apply emit_list_chain; apply IH, Hnext, Hi. }
  transitivity (emit_list (batch i) (root (next i)));
    [apply (gfp_bchain R), (Hroot i Hi) |].
  transitivity (emit_list (batch i) (emit_batches batch next (next i) : ctreeW W B X));
    [exact Hstep |].
  apply (gfp_bchain R); symmetry.
  exact (emit_batches_unfold_sbisim batch next i).
Qed.
