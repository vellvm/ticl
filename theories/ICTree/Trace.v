From Stdlib Require Import List Arith.PeanoNat.
From Coinduction Require Import coinduction rel tactics.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Trans ICTree.Events.Writer Logic.World.

Unset Implicit Arguments.
Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(** * Finite observation traces and their operational laws. *)

Definition emit_list {W X} (xs : list W) (t : ictreeW W X) : ictreeW W X :=
  List.fold_right (fun o k => log o;; k) t xs.

(** The observations produced by one step, which emits at most one. *)
Definition event_obs {W} (event : option W) : list W :=
  match event with None => [] | Some o => [o] end.

Definition label_logs {W} (labels : list (@label (writerE W) _)) : list W :=
  List.flat_map (fun l => match l with obs (Log o) _ => [o] | _ => [] end) labels.

Definition label_taus {W} (labels : list (@label (writerE W) _)) : nat :=
  List.length (List.filter (fun l => match l with tau => true | _ => false end) labels).

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

Lemma emit_list_nil {W X} (t : ictreeW W X) : emit_list [] t = t.
Proof. reflexivity. Qed.

Lemma emit_list_cons {W X} o xs (t : ictreeW W X) :
  emit_list (o :: xs) t ≅ Vis (Log o) (fun _ => emit_list xs t).
Proof.
  change ((log o ;; emit_list xs t) ≅ Vis (Log o) (fun _ => emit_list xs t)).
  unfold log, ICtree.trigger; rewrite bind_vis.
  step; constructor; intros []; rewrite bind_ret_l; reflexivity.
Qed.

Lemma emit_list_app {W X} xs ys (t : ictreeW W X) :
  emit_list (xs ++ ys) t = emit_list xs (emit_list ys t).
Proof. unfold emit_list; rewrite List.fold_right_app; reflexivity. Qed.

Lemma emit_list_equ {W X} xs (t u : ictreeW W X) :
  t ≅ u -> emit_list xs t ≅ emit_list xs u.
Proof.
  intro E; induction xs as [|o xs IH]; [exact E|].
  rewrite !emit_list_cons; step; constructor; intro x; exact IH.
Qed.

Lemma emit_list_sbisim {W X} xs (t u : ictreeW W X) :
  t ~ u -> emit_list xs t ~ emit_list xs u.
Proof.
  intro E; induction xs as [|o xs IH]; [exact E|].
  rewrite !emit_list_cons; apply sb_vis; intro x; exact IH.
Qed.

Lemma emit_list_bind {W X Y} xs (t : ictreeW W X)
  (k : X -> ictreeW W Y) :
  emit_list xs t >>= k ≅ emit_list xs (t >>= k).
Proof.
  induction xs as [|o xs IH]; [reflexivity|].
  change (((log o ;; emit_list xs t) >>= k) ≅
    (log o ;; emit_list xs (t >>= k))).
  etransitivity; [apply bind_bind|].
  apply equ_clo_bind_eq; intros []; exact IH.
Qed.

Lemma emit_list_ret_bind {W X Y} xs (x : X) (k : X -> ictreeW W Y) :
  emit_list xs (Ret x) >>= k ≅ emit_list xs (k x).
Proof.
  etransitivity; [apply emit_list_bind|].
  apply emit_list_equ, bind_ret_l.
Qed.

(** Return values are observable labels, including when they contain heaps.
    This proves equality of actual responses; it never identifies merely
    pointwise-equal heap functions. *)
Lemma emit_list_ret_injective {W X} (xs ys : list W) (x y : X) :
  emit_list xs (Ret x) ~ emit_list ys (Ret y) -> xs = ys /\ x = y.
Proof.
  revert ys; induction xs as [|o xs IH]; intros [|p ys] E.
  - split; [reflexivity|]. exact (@sbisim_ret_inv (writerE W) _ X x y E).
  - rewrite emit_list_cons in E.
    exfalso; exact (@sbisim_ret_vis_inv (writerE W) _ X x (Log p)
      (fun _ => emit_list ys (Ret y)) E).
  - rewrite emit_list_cons in E.
    exfalso; eapply (@sbisim_ret_vis_inv (writerE W) _ X y (Log o)
      (fun _ => emit_list xs (Ret x))); symmetry; exact E.
  - rewrite !emit_list_cons in E.
    pose proof (@sbisim_vis_invT (writerE W) _ X
      (Log o) (Log p) (fun _ => emit_list xs (Ret x))
      (fun _ => emit_list ys (Ret y)) tt E) as [_ Eo].
    injection Eo as Eo; subst p.
    pose proof (@sbisim_vis_invE (writerE W) _ X (Log o)
      (fun _ => emit_list xs (Ret x)) (fun _ => emit_list ys (Ret y))
      tt E tt) as Etail.
    destruct (IH ys Etail) as [-> ->]; auto.
Qed.

Lemma emit_list_ret_not_stuck {W X} xs (x : X) :
  ~ (emit_list xs (Ret x) ~ (stuck : ictreeW W X)).
Proof.
  intro E; apply sbisim_stuck_is_stuck in E.
  destruct xs as [|o xs].
  - apply E; exists (val x), stuck; apply trans_ret.
  - apply E; exists (obs (Log o) tt), (emit_list xs (Ret x)).
    rewrite emit_list_cons.
    exact (@trans_vis (writerE W) _ X (Log o) tt (fun _ => emit_list xs (Ret x))).
Qed.

Lemma emit_list_st {W X} (R : ictreeW W X -> ictreeW W X -> Prop)
  logs t u :
  coinduction.t (sb eq) R t u -> coinduction.t (sb eq) R (emit_list logs t) (emit_list logs u).
Proof.
  intro H; induction logs as [|o rest IH]; [exact H|].
  change (coinduction.t (sb eq) R (log o ;; emit_list rest t) (log o ;; emit_list rest u)).
  apply st_clo_bind_eq; [reflexivity|intros []; exact IH].
Qed.

Inductive finite_steps {E : Type} {HE : Encode E} {X : Type} :
  ictree E X -> list (@label E HE) -> ictree E X -> Prop :=
| finite_steps_nil t : finite_steps t [] t
| finite_steps_cons t u v l labels :
    trans l t u -> finite_steps u labels v -> finite_steps t (l :: labels) v.

Definition turn_labels {W} (event : option W) : list (@label (writerE W) _) :=
  match event with None => [tau] | Some o => [tau; obs (Log o) tt] end.

Lemma turn_labels_nonempty {W} (event : option W) : turn_labels event <> [].
Proof. destruct event; discriminate. Qed.

Lemma finite_steps_app {E : Type} {HE : Encode E} {X : Type}
  (t u v : ictree E X) left right :
  finite_steps t left u -> finite_steps u right v ->
  finite_steps t (left ++ right) v.
Proof.
  intros H; induction H; intro Htail; cbn [List.app];
    [exact Htail|econstructor; eauto].
Qed.

Lemma finite_steps_sbisim {E : Type} {HE : Encode E} {X : Type}
  (t t' : ictree E X) labels :
  finite_steps t labels t' -> forall u : ictree E X, t ~ u ->
  exists u', finite_steps u labels u' /\ t' ~ u'.
Proof.
  intro H; induction H as [t|t mid last l labels Hstep Htail IH]; intros u Eeq.
  - exists u; split; [constructor|exact Eeq].
  - destruct (sbisim_trans t u mid l eq Eeq Hstep)
      as (l' & mid' & Hstep' & El & Emid).
    subst l'; destruct (IH mid' Emid) as (last' & Htail' & Elast).
    exists last'; split; [econstructor; eassumption|exact Elast].
Qed.

Lemma finite_steps_emit_list {W X} logs (t : ictreeW W X) :
  finite_steps (emit_list logs t) (List.map (fun o => obs (Log o) tt) logs) t.
Proof.
  induction logs as [|o logs IH]; [constructor|].
  cbn [List.map]; econstructor; [|exact IH].
  rewrite emit_list_cons.
  exact (@trans_vis (writerE W) _ X (Log o) tt (fun _ => emit_list logs t)).
Qed.

(** * Guard/log alignment and finite prefixes. *)

Fixpoint rr_guards {W X} (n : nat) (t : ictreeW W X) : ictreeW W X :=
  match n with 0 => t | S n => Guard (rr_guards n t) end.

Lemma rr_guards_trans {W X} n l (t u : ictreeW W X) :
  trans l t u -> trans l (rr_guards n t) u.
Proof. intro H; induction n; cbn [rr_guards]; [exact H|now apply trans_guard]. Qed.

(** This proof relation consumes a guard on BOTH sides in a silent round.
    Its finite prefixes cannot turn silent divergence into a visible event. *)
CoInductive rr_aligned {W X} : ictreeW W X -> ictreeW W X -> Prop :=
| rr_align_guard t u n m t' u' :
    t ≅ rr_guards (S n) t' -> u ≅ rr_guards (S m) u' ->
    rr_aligned t' u' -> rr_aligned t u
| rr_align_log t u n m o t' u' :
    t ≅ rr_guards n (Vis (Log o) (fun _ => t')) ->
    u ≅ rr_guards m (Vis (Log o) (fun _ => u')) ->
    rr_aligned t' u' -> rr_aligned t u.

Lemma rr_aligned_equ {W X} (t u a b : ictreeW W X) :
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

Lemma rr_aligned_sym {W X} : forall t u : ictreeW W X,
  rr_aligned t u -> rr_aligned u t.
Proof.
  cofix IH; intros t u H;
    destruct H as [t u n m t' u' El Er H|t u n m o t' u' El Er H].
  - eapply rr_align_guard; [exact Er|exact El|apply IH; exact H].
  - eapply rr_align_log; [exact Er|exact El|apply IH; exact H].
Qed.

Lemma rr_aligned_match {W X} l T U :
  @trans_ (writerE W) _ X l T U ->
  forall u, rr_aligned (go T) u ->
  exists u', trans l u u' /\ rr_aligned (go U) u'.
Proof.
  intro TR; induction TR as
    [l inner target TR IH
    |n pick k result Eresult
    |e k answer result Eresult
    |result value Eresult]; intros u A.
  - inversion A as [left right n m tl tr El Er Hnext|left right n m o tl tr El Er Hnext];
      subst; clear A; rename Hnext into A.
    + apply equ_guard_invE in El; destruct n as [|n].
      * cbn [rr_guards] in El.
        assert (Ai : rr_aligned (go (observe inner)) tr).
        { eapply rr_aligned_equ; [|reflexivity|exact A].
          transitivity inner; [symmetry; exact El|apply ictree_eta]. }
        destruct (IH tr Ai) as (next & Tnext & Anext).
        exists next; split; [rewrite Er; now apply rr_guards_trans|exact Anext].
      * apply IH; eapply rr_aligned_equ; [apply ictree_eta|reflexivity|].
        eapply rr_align_guard; eassumption.
    + destruct n as [|n].
      * cbn [rr_guards] in El; step in El; cbn in El; inversion El.
      * apply equ_guard_invE in El.
        apply IH; eapply rr_aligned_equ; [apply ictree_eta|reflexivity|].
        eapply rr_align_log; eassumption.
  - inversion A as [left right p q tl tr El Er Hnext|left right p q o tl tr El Er Hnext];
      subst; clear A; rename Hnext into A.
    + step in El; cbn [rr_guards] in El; inversion El.
    + destruct p; step in El; cbn [rr_guards] in El; inversion El.
  - destruct e as [o]; destruct answer.
    inversion A as [left right n m tl tr El Er Hnext|left right n m p tl tr El Er Hnext];
      subst; clear A; rename Hnext into A.
    + step in El; cbn [rr_guards] in El; inversion El.
    + destruct n as [|n].
      * cbn [rr_guards] in El.
        pose proof (equ_vis_invT El) as [_ Ep]; injection Ep as Ep; subst p.
        pose proof (equ_vis_invE El tt) as Ek.
        exists tr; split.
        -- rewrite Er; apply rr_guards_trans.
           exact (@trans_vis (writerE W) _ X (Log o) tt (fun _ => tr)).
        -- eapply rr_aligned_equ; [|reflexivity|exact A].
           transitivity (k tt); [symmetry; exact Ek|].
           transitivity result; [exact Eresult|apply ictree_eta].
      * step in El; cbn [rr_guards] in El; inversion El.
  - inversion A as [left right n m tl tr El Er Hnext|left right n m o tl tr El Er Hnext];
      subst; clear A; rename Hnext into A.
    + step in El; cbn [rr_guards] in El; inversion El.
    + destruct n; step in El; cbn [rr_guards] in El; inversion El.
Qed.

Lemma rr_aligned_trans {W X} (t u next : ictreeW W X) l :
  rr_aligned t u -> trans l t next ->
  exists other, trans l u other /\ rr_aligned next other.
Proof.
  intros A TR.
  assert (Ae : rr_aligned (go (observe t)) u).
  { eapply rr_aligned_equ; [apply ictree_eta|reflexivity|exact A]. }
  destruct (rr_aligned_match l (observe t) (observe next) TR u Ae)
    as (other & To & Ao).
  exists other; split; [exact To|].
  eapply rr_aligned_equ; [symmetry; apply ictree_eta|reflexivity|exact Ao].
Qed.

Lemma rr_aligned_sbisim {W X} : forall t u : ictreeW W X,
  rr_aligned t u -> t ~ u.
Proof.
  unfold sbisim; apply_coinduction; fold_sbisim.
  intros R IH t u A; split; intros l next TR.
  - destruct (rr_aligned_trans t u next l A TR) as (other & To & Ao).
    exists l, other; split; [exact To|]; split; [now apply IH|reflexivity].
  - destruct (rr_aligned_trans u t next l (rr_aligned_sym t u A) TR)
      as (other & To & Ao).
    exists l, other; split; [exact To|]; split.
    + apply IH, rr_aligned_sym; exact Ao.
    + reflexivity.
Qed.

Lemma rr_guards_equ {W X} n (t u : ictreeW W X) :
  t ≅ u -> rr_guards n t ≅ rr_guards n u.
Proof.
  intro E; induction n; cbn [rr_guards]; [exact E|step; constructor; assumption].
Qed.
Lemma rr_guards_add {W X} n m (t : ictreeW W X) :
  rr_guards (n + m) t = rr_guards n (rr_guards m t).
Proof. induction n; cbn [rr_guards Nat.add]; [reflexivity|now rewrite IHn]. Qed.
Lemma rr_guards_guard {W X} n (t : ictreeW W X) :
  rr_guards n (Guard t) = rr_guards (S n) t.
Proof. induction n; cbn [rr_guards]; [reflexivity|now rewrite IHn]. Qed.

(** A finite proof prefix, not an additional evaluator or scheduler. *)
Inductive rr_token {W : Type} := RRGuard | RRLog (o : W).
Fixpoint rr_prefix {W X} (word : list (@rr_token W)) (t : ictreeW W X) : ictreeW W X :=
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
Lemma rr_prefix_app {W X} left right (t : ictreeW W X) :
  rr_prefix (left ++ right) t = rr_prefix left (rr_prefix right t).
Proof.
  induction left as [|[|o] rest IH]; cbn [List.app rr_prefix];
    [reflexivity|now rewrite IH|now rewrite IH].
Qed.
Lemma rr_prefix_equ {W X} word (t u : ictreeW W X) :
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
Lemma rr_prefix_emit {W X} logs (t : ictreeW W X) :
  rr_prefix (List.map RRLog logs) t ≅ emit_list logs t.
Proof.
  induction logs as [|o rest IH]; [reflexivity|].
  cbn [List.map rr_prefix]; rewrite emit_list_cons.
  step; constructor; intros []; exact IH.
Qed.
Lemma rr_prefix_no_events {W X} word (t : ictreeW W X) :
  rr_prefix_events word = [] -> rr_prefix word t = rr_guards (List.length word) t.
Proof.
  induction word as [|[|o] rest IH]; cbn [rr_prefix_events rr_prefix List.length rr_guards];
    intro E; [reflexivity|now rewrite IH|discriminate].
Qed.
Lemma rr_prefix_one_event {W X} word o (t : ictreeW W X) :
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
