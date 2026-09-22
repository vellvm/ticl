From Stdlib Require Import Fin Vector.
From ExtLib Require Import Data.Monads.StateMonad.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Yield ICTree.Events.State ICTree.Events.Writer
  ICTree.Interp.Refine ICTree.Interp.Yield.Mod
  ICTree.Interp.Yield.RoundRobin Utils.Vectors.

Import ICtree ICTreeNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.

Lemma modulo_picks :
  rr_pick 1 0 = Fin.F1 /\
  rr_pick 1 1 = Fin.FS Fin.F1 /\
  rr_pick 1 2 = Fin.F1 /\
  rr_pick 0 3 = Fin.F1.
Proof. repeat split; reflexivity. Qed.

Lemma guard_retains_cursor :
  runStateT (round_robin (Guard (Ret tt) : ictreeW nat unit)) 4 ≅
  Guard (Ret (tt,4)).
Proof.
  change (refine_rr (Guard (Ret tt) : ictreeW nat unit) 4 ≅ Guard (Ret (tt,4))).
  rewrite unfold_refine_rr; cbn [observe].
  apply guard_equ_node; rewrite unfold_refine_rr; reflexivity.
Qed.

Lemma event_retains_cursor :
  runStateT (round_robin (Vis (Log 7) (fun _ => Ret tt))) 4 ≅
  Vis (Log 7) (fun _ => Ret (tt,4)).
Proof.
  change (refine_rr (Vis (Log 7) (fun _ => Ret tt)) 4 ≅
    Vis (Log 7) (fun _ => Ret (tt,4))).
  rewrite unfold_refine_rr; cbn [observe].
  apply vis_equ_node; intros []; rewrite unfold_refine_rr; reflexivity.
Qed.

Lemma singleton_branch_advances_cursor :
  runStateT (round_robin (Br 0 (fun _ => Ret tt) : ictreeW nat unit)) 4 ≅
  Guard (Ret (tt,5)).
Proof.
  change (refine_rr (Br 0 (fun _ => Ret tt) : ictreeW nat unit) 4 ≅
    Guard (Ret (tt,5))).
  rewrite unfold_refine_rr; cbn [observe].
  apply guard_equ_node; rewrite unfold_refine_rr; reflexivity.
Qed.

Lemma scheduled_two_selects {E : Type} {HE : Encode E} (ts : pool E 2) m :
  refine_rr (schedule 2 ts None) m ≅
  Vis (inl Yield) (fun _ =>
    Guard (refine_rr (schedule 2 ts (Some (rr_pick 1 m))) (S m))).
Proof.
  rewrite unfold_refine_rr, schedule_no_focus_nonempty.
  apply vis_equ_node; intros []; rewrite unfold_refine_rr; reflexivity.
Qed.

Definition raw_add (delta : nat) : thread (stateE nat) :=
  Vis (inr (inr Get)) (fun x =>
    Vis (inr (inr (Put ((x + delta)%nat)))) (fun _ => Ret tt)).
Definition counter_thread (delta : nat) : thread (stateE nat) :=
  raw_add delta;; Vis (inl Yield) (fun _ => raw_add delta).
Definition counter_fork : thread (stateE nat) :=
  Vis (inr (inl Fork))
    (fun child : bool => counter_thread (if child then 10 else 1)).

Local Ltac counter_observe :=
  lazy [observe _observe Vector.nth Vector.replace Vector.caseS' raw_add
    counter_thread ICtree.bind ICtree.subst' rr_pick]; reflexivity.

Local Ltac counter_get :=
  erewrite interp_schedule_rr_user with (e := Get) by counter_observe;
  cbn [h_stateW runStateT]; rewrite bind_ret_l.

Local Ltac counter_put :=
  erewrite interp_schedule_rr_user by counter_observe;
  cbn [h_stateW runStateT]; rewrite bind_bind;
  apply sbisim_clo_bind_eq; [reflexivity|];
  intros []; rewrite bind_ret_l.

Lemma shared_counter_round_robin :
  interp_schedule_rr h_stateW 1 [counter_fork]%vector (Some Fin.F1) 0 0 ~
  (log 1;; log 11;; log 12;; log 22;; Ret (tt,22)).
Proof.
  erewrite interp_schedule_rr_fork by reflexivity.
  counter_get; counter_put.
  erewrite interp_schedule_rr_yield by counter_observe.
  rewrite interp_schedule_rr_select.
  counter_get; counter_put.
  erewrite interp_schedule_rr_yield by counter_observe.
  rewrite interp_schedule_rr_select.
  counter_get; counter_put.
  erewrite interp_schedule_rr_ret by counter_observe.
  change (interp_schedule_rr h_stateW 1
    ([raw_add 10; Ret tt]%vector -- Fin.FS Fin.F1) None 2 12 ~
    (log 22;; Ret (tt,22))).
  rewrite vector_remove_tail, vector_remove_head.
  rewrite interp_schedule_rr_select.
  counter_get; counter_put.
  erewrite interp_schedule_rr_ret by counter_observe.
  change (interp_schedule_rr h_stateW 0
    ([Ret tt]%vector -- Fin.F1) None 3 22 ~ Ret (tt,22)).
  rewrite vector_remove_head, interp_schedule_rr_empty; reflexivity.
Qed.
