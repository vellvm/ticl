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

(** * Interpreting state events *)
(** This section contains the main lemmas about interpreting state events.
    The main result is that the interpretation of a state event is equivalent to the interpretation of the corresponding
    event in the state monad. *)
Definition interp_state `{Encode E} `{Encode F} {W}
  (h : E ~> stateT W (ictree F)) {X} (t: ictree E X) (w: W) :
  ictree F (X*W) := runStateT (interp h t) w.

Definition instr_stateE {Σ X} (t: ictree (stateE Σ) X) (σ: Σ): ictreeW Σ (X * Σ) :=
  interp_state h_stateW t σ.

Notation interp_state_ h t s :=
  (match observe t with
   | RetF r => Ret (r, s)
   | VisF e k => (runStateT (h e) s) >>=
                  (fun '(x, s') => Guard (interp_state h (k x) s'))
   | GuardF t => Guard (interp_state h t s)
   | BrF n k => Br n (fun xs => Guard (interp_state h (k xs) s))
   end)%function.

(** Unfolding of [interp_state] given state [s] *)
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

(** Definition [interp_state] is equality preserving. *)
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

(** [interp_state] applied on return values. *)
Lemma interp_state_ret `{Encode E} `{Encode F} W (h: E ~> stateT W (ictree F)) {X} (w : W) (r : X) :
  (interp_state h (Ret r) w) ≅ (Ret (r, w)).
Proof.
  rewrite ictree_eta. reflexivity.
Qed.

(** [interp_state] applied on visible events, interpreting the event and the state leaving behind a guard. *)
Lemma interp_state_vis `{Encode E} `{Encode F} `(h: E ~> stateT W (ictree F)) {X}  
  (e : E) (k : encode e -> ictree E X) (w : W) :
  interp_state h (Vis e k) w ≅ runStateT (h e) w >>=
    (fun '(x, w') => Guard (interp_state h (k x) w')).
Proof.
  rewrite unfold_interp_state; reflexivity.
Qed.

(** [interp_state] applied on trigger events, interpreting the event and the state leaving behind a guard. *)
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

(** A trigger's administrative guard disappears under strong bisimulation. *)
Local Typeclasses Transparent equ.
Lemma interp_state_trigger_bind {E F} {HE : Encode E} {HF : Encode F} {W X}
  (h : E ~> stateT W (ictree F)) (e : E)
  (k : (encode e * W)%type -> ictree F X) (s : W) :
  (interp_state h (@ICtree.trigger E E HE HE ReSum_refl ReSumRet_refl e) s >>= k) ~
  (runStateT (h e) s >>= k).
Proof.
  rewrite interp_state_trigger, bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intro result].
  rewrite bind_guard, sb_guard, bind_ret_l; reflexivity.
Qed.
Local Typeclasses Opaque equ.

(** [interp_state] applied on branch events commutes with the branching structure. *)
Lemma interp_state_br `{Encode E} `{Encode F} `(h: E ~> stateT W (ictree F)) {X}
  (n : nat) (k : fin' n -> ictree E X) (w : W) :
  interp_state h (Br n k) w ≅ Br n (fun x => Guard (interp_state h (k x) w)).
Proof. rewrite !unfold_interp_state; reflexivity. Qed.

(** [interp_state] applied on guard events, commutes with the guard structure. *)
Lemma interp_state_tau `{Encode E} `{Encode F} `(h: E ~> stateT W (ictree F)) {X}
  (t : ictree E X) (w : W) :
  interp_state h (Guard t) w ≅ Guard ((interp_state h t w)).
Proof. rewrite !unfold_interp_state; reflexivity. Qed.

(** [interp_state] applied on bind, commutes with the bind structure. *)
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

(** [interp_state] applied on iteration, unfolds the iteration structure and commutes the interpretation inside the loop body. *)
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

(** [interp_state] applied on get, returns the state. *)
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

(** [interp_state] applied on put, interprets the event and the state leaving behind a log event. *)
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

(** [instr_state] applied on iteration, unfolds the iteration structure and interprets the loop body. *)
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

(** * Interpreting one indexed emission.

    [h_indexed] leaves exactly one observation and advances the shared
    occurrence counter once; the untouched auxiliary state and the other
    handler are arbitrary.  This is the interpretation-level companion of the
    raw equation [h_indexed_log]. *)
Local Typeclasses Transparent equ.
Lemma interp_indexed_emit {A Sigma E X} {HE : Encode E}
  (other : E ~> stateT (Sigma * nat) (ictreeW (indexed A)))
  (a : A) (s : Sigma) (c : nat)
  (k : unit -> ictree (E + writerE A) X) :
  interp_state (h_sum other h_indexed)
    ((ICtree.trigger (Log a) : ictree (E + writerE A) unit) >>= k) (s,c) ~
  (log (stamp a c);; interp_state (h_sum other h_indexed) (k tt) (s,S c)).
Proof.
  unfold ICtree.trigger, resum, resum_ret, ReSum_inr, ReSumRet_inr;
    rewrite bind_vis; setoid_rewrite bind_ret_l.
  rewrite interp_state_vis; cbn [h_sum].
  rewrite (h_indexed_log (Sigma:=Sigma) a s c), bind_bind.
  apply sbisim_clo_bind_eq; [reflexivity | intros []].
  rewrite bind_ret_l; apply sb_guard.
Qed.
Local Typeclasses Opaque equ.
