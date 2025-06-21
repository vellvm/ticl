From ExtLib Require Export
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Monad.

From TICL Require Import
  Classes
  ICTree.Core
  ICTree.Interp.Core
  Events.Core
  ICTree.Events.Writer
  ICTree.Logic.Trans
  ICTree.Events.State
  ICTree.Equ
  ICTree.SBisim.

From Coinduction Require Import
  coinduction.
From Stdlib Require Import Morphisms.

Import ICTreeNotations.
Local Open Scope ictree_scope.

Set Implicit Arguments.
Generalizable All Variables.

(*| Lemmas about state |*)
Definition interp_state `{Encode E} `{Encode F} {W}
  (h : E ~> stateT W (ictree F)) {X} (t: ictree E X) (w: W) :
  ictree F (X*W) := runStateT (interp h t) w.

Definition instr_stateE {Σ X} (t: ictree (stateE Σ) X) (σ: Σ): ictreeW Σ (X * Σ) :=
  interp_state h_stateW t σ.

(*| Unfolding of [interp_state] given state [s] *)
Notation interp_state_ h t s :=
  (match observe t with
   | RetF r => Ret (r, s)
   | VisF e k => (runStateT (h e) s) >>=
                  (fun '(x, s') => Guard (interp_state h (k x) s'))
   | GuardF t => Guard (interp_state h t s)
   | BrF n k => Br n (fun xs => Guard (interp_state h (k xs) s))
   end)%function.

Lemma unfold_interp_state `{Encode E} `{Encode F} `(h: E ~> stateT W (ictree F))
  {X} (t: ictree E X) (w : W) :
  interp_state h t w ≅ interp_state_ h t w.
Proof.
  unfold interp_state.  
  unfold interp, iter, MonadIter_stateT, MonadIter_ictree.
  setoid_rewrite unfold_iter at 1.
  cbn.
  rewrite bind_bind.
  desobs t; cbn.
  - now repeat (cbn; rewrite ?bind_ret_l).
  - unfold mbr, MonadBr_ictree.
    rewrite ?bind_bind, ?bind_branch.
    apply br_equ; intros.
    now cbn; rewrite ?bind_ret_l.
  - rewrite ?bind_bind, ?bind_ret_l; cbn.
    reflexivity.
  - rewrite ?bind_bind.
    upto_bind_equ.
    destruct x1 eqn:Hx1.
    rewrite ?bind_ret_l; cbn.
    reflexivity.
Qed.

#[global] Instance equ_interp_state `{Encode E} `{Encode F} W (h: E ~> stateT W (ictree F)) {X}:
  Proper (@equ E _ X X eq ==> eq ==> equ eq) (interp_state h).
Proof.
  unfold Proper, respectful.
  coinduction ? IH; intros * EQ1 * <-.
  rewrite !unfold_interp_state.
  step in EQ1; inv EQ1; auto.
  - cbn. upto_bind_equ.
    destruct x1.
    constructor; intros.
    apply IH; auto.
    apply H3.
  - cbn.
    constructor; intros.
    apply IH; auto.
  - cbn.
    constructor.
    intros i.
    step.
    econstructor.
    apply IH; auto.
    apply H3.
Qed.

Lemma interp_state_ret `{Encode E} `{Encode F} W (h: E ~> stateT W (ictree F)) {X} (w : W) (r : X) :
  (interp_state h (Ret r) w) ≅ (Ret (r, w)).
Proof.
  rewrite ictree_eta. reflexivity.
Qed.

Lemma interp_state_vis `{Encode E} `{Encode F} `(h: E ~> stateT W (ictree F)) {X}  
  (e : E) (k : encode e -> ictree E X) (w : W) :
  interp_state h (Vis e k) w ≅ runStateT (h e) w >>=
    (fun '(x, w') => Guard (interp_state h (k x) w')).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

Lemma interp_state_trigger `{Encode E} `{Encode F} `(h: E ~> stateT W (ictree F)) (e : E) (w : W) :
  interp_state h (ICtree.trigger e) w ≅ runStateT (h (resum e)) w >>= fun x => Guard (Ret x).
Proof.
  unfold ICtree.trigger.
  rewrite interp_state_vis.
  upto_bind_equ.
  destruct x1.
  step; constructor.
  rewrite interp_state_ret.
  reflexivity.
Qed.  

Lemma interp_state_br `{Encode E} `{Encode F} `(h: E ~> stateT W (ictree F)) {X}
  (n : nat) (k : fin' n -> ictree E X) (w : W) :
  interp_state h (Br n k) w ≅ Br n (fun x => Guard (interp_state h (k x) w)).
Proof. rewrite !unfold_interp_state; reflexivity. Qed.

Lemma interp_state_tau `{Encode E} `{Encode F} `(h: E ~> stateT W (ictree F)) {X}
  (t : ictree E X) (w : W) :
  interp_state h (Guard t) w ≅ Guard ((interp_state h t w)).
Proof. rewrite !unfold_interp_state; reflexivity. Qed.

Definition h_resum `{Encode E1}`{Encode E2}`{Encode F}`{ReSum E1 E2}`{ReSumRet E1 E2} {W}
  (h: E2 ~> stateT W (ictree F)): E1 ~> stateT W (ictree F) :=
  fun (e: E1) =>
    mkStateT
      (fun w => runStateT (h (resum e)) w >>= fun '(x, w) => Ret (resum_ret e x, w)).

Lemma interp_state_resumICtree`{Encode E1}`{Encode E2}`{Encode F}
  `{ReSum E1 E2}`{ReSumRet E1 E2} {X} `(h: E2 ~> stateT W (ictree F)):
  forall (t : ictree E1 X) (w : W),
    interp_state h (resumICtree t) w ≅ interp_state (h_resum h) t w.
Proof.
  coinduction RR CIH; intros.
  rewrite unfold_resumICtree, unfold_interp_state.
  setoid_rewrite unfold_interp_state.
  cbn.
  desobs t; cbn.
  - reflexivity.
  - constructor.
    intro i.
    step.
    constructor.
    apply CIH.
  - constructor.
    apply CIH.
  - cbn.
    rewrite bind_bind.
    upto_bind_equ.
    destruct x.
    rewrite bind_ret_l.
    constructor.
    apply CIH.
Qed.

Lemma interp_state_ret_inv `{Encode E} `{Encode F}
  `(h: E ~> stateT W (ictree F)) {X}: forall s (t : ictree E X) r,
    interp_state h t s ≅ Ret r -> t ≅ Ret (fst r) /\ s = snd r.
Proof.
  intros.
  setoid_rewrite (ictree_eta t) in H1.
  setoid_rewrite (ictree_eta t).
  destruct (observe t) eqn:?.
  - rewrite interp_state_ret in H1. step in H1. inv H1. split; reflexivity.
  - rewrite interp_state_br in H1. step in H1. inv H1.
  - rewrite interp_state_tau in H1. step in H1. inv H1.
  - rewrite interp_state_vis in H1. apply ret_equ_bind in H1 as (? & ? & ?).
    destruct x.
    step in H2.
    inv H2.
Qed.

Arguments interp_state: simpl never.
Local Typeclasses Transparent equ.
Lemma interp_state_bind `{Encode E} `{Encode F} `(h : E ~> stateT W (ictree F))
  {A B} (t : ictree E A) (k : A -> ictree E B) (s : W) :
  interp_state h (t >>= k) s ≅ interp_state h t s >>= fun '(x, s) => interp_state h (k x) s.
Proof.
  revert s t.
  coinduction ? IH; intros.
  rewrite (ictree_eta t).
  rewrite unfold_bind, unfold_interp_state.
  destruct (observe t) eqn:Hobs; cbn.
  - rewrite interp_state_ret, bind_ret_l.
    cbn.
    rewrite unfold_interp_state.
    reflexivity.
  - rewrite interp_state_br.
    rewrite bind_br.
    setoid_rewrite bind_guard.
    constructor; intro i.
    step; econstructor; intros.
    apply IH.
  - rewrite interp_state_tau.
    rewrite bind_guard.
    constructor.
    apply IH.
  - rewrite interp_state_vis, bind_bind.
    upto_bind_equ; destruct x.
    rewrite bind_guard.
    constructor.
    apply IH.
Qed.

Lemma interp_state_map `{Encode E} `{Encode F} `(h : E ~> stateT W (ictree F))
  {A B} (t : ictree E A) (f : A -> B) (s : W) :
  interp_state h (ICtree.map f t) s ≅ ICtree.map (fun '(x, s) => (f x, s)) (interp_state h t s).
Proof.
  unfold ICtree.map.
  rewrite interp_state_bind.
  upto_bind_equ.
  destruct x1.
  apply interp_state_ret.
Qed.

Lemma interp_state_unfold_iter `{Encode E} `{Encode F}
  `(h : E ~> stateT W (ictree F)) {I R}
  (k : I -> ictree E (I + R)) (i: I) (s: W) :
  interp_state h (ICtree.iter k i) s ≅ interp_state h (k i) s >>= fun '(x, s) =>
      match x with
      | inl l => Guard (interp_state h (iter k l) s)
      | inr r => Ret (r, s)
      end.
Proof.
  Opaque interp_state.
  setoid_rewrite unfold_iter.
  rewrite interp_state_bind.
  upto_bind_equ.
  unfold iter, MonadIter_ictree. 
  destruct x1 as [[l | r] s'].
  - rewrite interp_state_tau.
    reflexivity.
  - rewrite interp_state_ret.
    reflexivity.
Qed.

Lemma interp_state_get {S}: forall (s: S),
  interp_state h_stateW get s ~ Ret (s, s).
Proof.
  intros.
  rewrite unfold_interp_state.
  cbn.
  rewrite bind_ret_l, sb_guard.
  rewrite interp_state_ret.
  reflexivity.
Qed.

Lemma interp_state_put {S}: forall (s s': S),
  interp_state h_stateW (put s') s ~ log s' ;; Ret (tt, s').
Proof with eauto.
  intros.
  rewrite unfold_interp_state.
  cbn.
  rewrite bind_bind.
  __upto_bind_sbisim...
  intros [].
  rewrite bind_ret_l.
  rewrite sb_guard, interp_state_ret.
  reflexivity.
Qed.

Lemma instr_state_bind {S A B} (t : ictree (stateE S) A) (k : A -> ictree (stateE S) B) (s : S) :
  instr_stateE (t >>= k) s ≅ instr_stateE t s >>= fun '(x, s) => instr_stateE (k x) s.
Proof.
  unfold instr_stateE.
  apply interp_state_bind.
Qed.

Lemma instr_state_map {S A B} (t : ictree (stateE S) A) (f : A -> B) (s : S) :
  instr_stateE (ICtree.map f t) s ≅ ICtree.map (fun '(x, s) => (f x, s)) (instr_stateE t s).
Proof.
  unfold instr_stateE.
  apply interp_state_map.
Qed.

Lemma instr_state_unfold_iter{S I R}
  (k : I -> ictree (stateE S) (I + R)) (i: I) (s: S) :
  instr_stateE (ICtree.iter k i) s ≅ instr_stateE (k i) s >>= fun '(x, s) =>
      match x with
      | inl l => Guard (instr_stateE (iter k l) s)
      | inr r => Ret (r, s)
      end.
Proof.
  unfold instr_stateE.
  apply interp_state_unfold_iter.
Qed.

Lemma instr_state_get {S}: forall (s: S),
  instr_stateE get s ~ Ret (s, s).
Proof.
  unfold instr_stateE.
  apply interp_state_get.
Qed.

Lemma instr_state_put {S}: forall (s s': S),
  instr_stateE (put s') s ~ log s' ;; Ret (tt, s').
Proof with eauto.
  unfold instr_stateE.
  apply interp_state_put.
Qed.
