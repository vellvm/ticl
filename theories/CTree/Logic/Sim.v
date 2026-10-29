From Stdlib Require Import Basics Classes.SetoidClass Classes.RelationPairs.
From TICL Require Import CTree.Core CTree.Events.Writer Logic.Kripke
  Logic.Setoid Logic.Simulation Logic.Semantics CTree.Logic.Trans.

Generalizable All Variables.
Import CTree CTreeNotations TiclNotations CoindNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.

Section ConditionalSimulation.
  Context {E B: Type -> Type} {X: Type}.

  (** Labels related by simulation: τ and observations are equal; return values are [RV]-related. *)
  Variant simL (RV: X -> X -> Prop) : @label E -> @label E -> Prop :=
  | SimLTau : simL RV τ τ
  | SimLObs {Y} (e: E Y) (v: Y) : simL RV (obs e v) (obs e v)
  | SimLVal (x x': X) : RV x x' -> simL RV (val x) (val x').

  (** A tree can make an LTS transition. *)
  Definition can_trans (t: ctree E B X) : Prop := exists l t', trans l t t'.

  (** Transition availability respects tree equivalence. *)
  #[global] Instance can_trans_equ : Proper (equ eq ==> iff) can_trans.
  Proof.
    intros t u H; split; intros (l & v & HT); exists l, v;
      [rewrite <- H|rewrite H]; exact HT.
  Qed.


  (** Conditional LTS simulation: forward always, backward only from a tree that can transition. *)
  Program Definition csimF (RV: X -> X -> Prop) : mon (ctree E B X -> ctree E B X -> Prop) :=
    {| body R t t' :=
      (forall l t1, trans l t t1 -> exists l' t1', trans l' t' t1' /\ simL RV l l' /\ R t1 t1') /\
      (can_trans t -> forall l' t1', trans l' t' t1' ->
        exists l t1, trans l t t1 /\ simL RV l l' /\ R t1 t1') |}.
  Next Obligation.
    rename H0 into Hf, H1 into Hb; split.
    - intros l t1 HT; destruct (Hf _ _ HT) as (l' & t1' & HT' & HL & HR).
      exists l', t1'; repeat split; auto; now apply H.
    - intros HC l' t1' HT'; destruct (Hb HC _ _ HT') as (l & t1 & HT & HL & HR).
      exists l, t1; repeat split; auto; now apply H.
  Qed.

  (** Greatest fixed point of conditional simulation, matching the hypotheses of [Logic.Simulation]. *)
  Definition csim RV := gfp (csimF RV).

  (** Every simulation chain stage respects tree equivalence. *)
  #[global] Instance csim_chain_equ RV {R: Chain (csimF RV)} :
    Proper (equ eq ==> equ eq ==> iff) `R.
  Proof.
    apply tower.
    - intros T HT t u Htu t' u' Htu'; split; intros H S HS;
        apply (HT S HS t u Htu t' u' Htu'); apply H, HS.
    - intros R0 IH t u Htu t' u' Htu'; cbn; split; intros [Hf Hb]; split.
      + intros l v HT; rewrite <- Htu in HT.
        destruct (Hf _ _ HT) as (l' & v' & HT' & HL & HR).
        exists l', v'; repeat split; auto; now rewrite <- Htu'.
      + intros HC l' v' HT'; rewrite <- Htu in HC; rewrite <- Htu' in HT'.
        setoid_rewrite <- Htu; exact (Hb HC _ _ HT').
      + intros l v HT; rewrite Htu in HT.
        destruct (Hf _ _ HT) as (l' & v' & HT' & HL & HR).
        exists l', v'; repeat split; auto; now rewrite Htu'.
      + intros HC l' v' HT'; rewrite Htu in HC; rewrite Htu' in HT'.
        setoid_rewrite Htu; exact (Hb HC _ _ HT').
  Qed.


  (** A stuck source conditionally simulates every target. *)
  Lemma csim_stuck_l RV {R: Chain (csimF RV)} t' : `R Stuck t'.
  Proof.
    apply (b_chain R); split.
    - intros l t HT; exfalso; eapply trans_stuck_inv; eauto.
    - intros (l & t & HT); exfalso; eapply trans_stuck_inv; eauto.
  Qed.


  (** Leading silent guards preserve transition availability. *)
  Lemma can_trans_guard t : can_trans (Guard t) <-> can_trans t.
  Proof.
    split; intros (l & u & HT); exists l, u;
      [now apply trans_guard_inv in HT|now apply trans_guard].
  Qed.


  (** Forward [Logic.Simulation] hypothesis, read off [ktrans_]. *)
  Lemma csim_ktrans_l RV t t' w u z : csim RV t t' ->
    |t, w| ↦ |u, z| -> exists u' z', |t', w| ↦ |u', z'| /\ csim RV u u' /\ simW RV z z'.
  Proof.
    intros HS HT; step in HS; destruct HS as [Hf Hb].
    ddestruction HT;
      edestruct Hf as (l' & u' & HT' & HL & HR); [eassumption| |eassumption| |eassumption| |eassumption| ];
      ddestruction HL.
    - exists u', w; repeat split; auto; [now apply KtransTau|now apply simW_refl].
    - exists u', (Obs e v); repeat split; auto; [now apply KtransObs|constructor].
    - exists u', (Done x'); repeat split; auto; [now apply KtransDone|now constructor].
    - exists u', (Finish e v x'); repeat split; auto; [now apply KtransFinish|now constructor].
  Qed.

  (** Conditional backward [Logic.Simulation] hypothesis, read off [ktrans_]. *)
  Lemma csim_ktrans_r RV t t' w u' z' : csim RV t t' -> can_step t w ->
    |t', w| ↦ |u', z'| -> exists u z, |t, w| ↦ |u, z| /\ csim RV u u' /\ simW RV z z'.
  Proof.
    intros HS (v & z & Hcan) HT.
    assert (HC: can_trans t).
    { apply ktrans_trans in Hcan as (l & Hcan & _); now exists l, v. }
    step in HS; destruct HS as [Hf Hb]; specialize (Hb HC).
    ddestruction HT;
      edestruct Hb as (l & u & HT0 & HL & HR); [eassumption| |eassumption| |eassumption| |eassumption| ];
      ddestruction HL.
    - exists u, w; repeat split; auto; [now apply KtransTau|now apply simW_refl].
    - exists u, (Obs e v0); repeat split; auto; [now apply KtransObs|constructor].
    - exists u, (Done x0); repeat split; auto; [now apply KtransDone|now constructor].
    - exists u, (Finish e v0 x0); repeat split; auto; [now apply KtransFinish|now constructor].
  Qed.

  (** Prefix formulas transport unchanged along conditional tree simulation. *)
  Theorem ticll_csim RV (φ: ticll E) t t' w : csim RV t t' ->
    <( t, w |= φ )> -> <( t', w |= φ )>.
  Proof. eapply ticll_sim; [apply csim_ktrans_l|apply csim_ktrans_r]. Qed.

  (** Suffix formulas transport with [framer] across related worlds. *)
  Theorem ticlr_csim RV (ψ: ticlr E X) :
    (forall x y1 y2, RV x y1 -> RV x y2 -> y1 = y2) -> forall t t' w w',
    csim RV t t' -> simW RV w w' -> <[ t, w |= ψ ]> -> <[ t', w' |= {framer RV ψ} ]>.
  Proof.
    intros Hunique; eapply ticlr_sim;
      [apply csim_ktrans_l|apply csim_ktrans_r|exact Hunique].
  Qed.
End ConditionalSimulation.

(** Unconditional bisimulation supplies both conditional simulation matches. *)
Theorem sbisim_csim {E B X} (RV : X -> X -> Prop)
    (t u : ctree E B X) :
  sbisim (simL RV) t u -> csim RV t u.
Proof.
  revert t u; unfold csim; coinduction R IH.
  intros t u H; step in H; destruct H as [Hf Hb]; split.
  - intros l t' HT.
    destruct (Hf _ _ HT) as (l' & u' & HU & HR & HL).
    exists l', u'; split; [exact HU|split; [exact HL|now apply IH]].
  - intros _ l' u' HU.
    destruct (Hb _ _ HU) as (l & t' & HT & HR & HL).
    exists l, t'; split; [exact HT|split; [exact HL|now apply IH]].
Qed.

(** A finite chain of [Guard]s ending in a visible [Step]: a hidden branch visible to [trans]. *)
Inductive guards_to_step {E B X} : ctree E B X -> Prop :=
| GtsStep t u : observe t = StepF u -> guards_to_step t
| GtsGuard t u : observe t = GuardF u -> guards_to_step u -> guards_to_step t.

(** Finite guarded-step prefixes respect tree equivalence. *)
Lemma guards_to_step_equ {E B X} (t u: ctree E B X) :
  t ≅ u -> guards_to_step t -> guards_to_step u.
Proof.
  intros Heq HG; revert u Heq; induction HG; intros v Heq;
    step in Heq; change (equb eq (equ eq) (observe t) (observe v)) in Heq;
    rewrite H in Heq; ddestruction Heq.
  - eapply GtsStep; symmetry; eassumption.
  - eapply GtsGuard; [symmetry; eassumption|eapply IHHG; eauto].
Qed.

(** A guarded-step prefix can transition. *)
Lemma guards_to_step_can_trans {E B X} (t: ctree E B X) :
  guards_to_step t -> can_trans t.
Proof.
  induction 1.
  - exists τ, u; change (trans_ τ (observe t) (observe u)); rewrite H; constructor; reflexivity.
  - destruct IHguards_to_step as (l & v & HT).
    exists l, v; change (trans_ l (observe t) (observe v)); rewrite H; now constructor.
Qed.

(** A leading guard preserves a guarded-step prefix. *)
Lemma guards_to_step_guard {E B X} (t: ctree E B X) :
  guards_to_step t -> guards_to_step (Guard t).
Proof. intro H; eapply GtsGuard; [reflexivity|exact H]. Qed.

(** Binding preserves a guarded-step prefix. *)
Lemma guards_to_step_bind {E B X Y} (t: ctree E B X) (k: X -> ctree E B Y) :
  guards_to_step t -> guards_to_step (CTree.bind t k).
Proof.
  induction 1.
  - eapply GtsStep; unfold observe at 1; cbn; now rewrite H.
  - eapply GtsGuard; [unfold observe at 1; cbn; now rewrite H|exact IHguards_to_step].
Qed.

Section Framable.
  Context {E B: Type -> Type} (okE: forall Y, E Y -> Prop).

  (** One framable node: events satisfy [okE] and hidden children are guarded-step prefixes. *)
  Variant framableF {A} (R: ctree E B A -> Prop) : ctree' E B A -> Prop :=
  | FrRetF x : framableF R (RetF x)
  | FrStuckF : framableF R StuckF
  | FrStepF t : R t -> framableF R (StepF t)
  | FrGuardF t : R t -> framableF R (GuardF t)
  | FrVisF {Y} (e: E Y) k : okE Y e -> (forall x, R (k x)) -> framableF R (VisF e k)
  | FrBrF {Y} (c: B Y) k : (forall y, guards_to_step (k y)) ->
      (forall y, R (k y)) -> framableF R (BrF c k).

  (** Monotone observation operator for framability. *)
  Program Definition fframable {A} : mon (ctree E B A -> Prop) :=
    {| body R t := framableF R (observe t) |}.
  Next Obligation.
    destruct H0; constructor; intros; auto; apply H; auto.
  Qed.

  (** Trees with admissible events and guarded hidden branches; closed under bind and iteration. *)
  Definition Framable {A} : ctree E B A -> Prop := gfp fframable.

  (** Expose exactly one framable node. *)
  Lemma framable_unfold {A} (t: ctree E B A) :
    Framable t <-> framableF Framable (observe t).
  Proof. symmetry; exact (gfp_fp fframable t). Qed.

  (** Every framability chain stage respects tree equivalence. *)
  #[global] Instance framable_chain_equ {A} {R: Chain (@fframable A)} :
    Proper (equ eq ==> iff) `R.
  Proof.
    apply tower.
    - intros T HT t u Htu; split; intros H S HS;
        apply (HT S HS t u Htu); apply H, HS.
    - intros R' IH t u Htu; step in Htu; cbn.
      change (equb eq (equ eq) (observe t) (observe u)) in Htu.
      split; intro H; revert Htu;
        [remember (observe u) as ou | remember (observe t) as ot];
        destruct H; intro Htu; ddestruction Htu; try rename REL into Hq;
        constructor; intros; eauto;
        first [apply (IH _ _ (Hq _)) | apply (IH _ _ Hq) |
          eapply guards_to_step_equ; [apply Hq|] |
          eapply guards_to_step_equ; [symmetry; apply Hq|]]; auto.
  Qed.


  (** Returns are framable. *)
  Lemma fr_ret {A} (x: A) : Framable (Ret x: ctree E B A).
  Proof. apply framable_unfold; constructor. Qed.

  (** Stuck trees are framable. *)
  Lemma fr_stuck {A} : Framable (Stuck: ctree E B A).
  Proof. apply framable_unfold; constructor. Qed.


  (** A leading guard preserves framability. *)
  Lemma fr_guard {A} (t: ctree E B A) : Framable t -> Framable (Guard t).
  Proof. intro H; apply framable_unfold; now constructor. Qed.

  (** An admissible event with framable continuations is framable. *)
  Lemma fr_vis {A Y} (e: E Y) (k: Y -> ctree E B A) :
    okE Y e -> (forall x, Framable (k x)) -> Framable (Vis e k).
  Proof. intros; apply framable_unfold; now constructor. Qed.


  (** Bind preserves framability into every chain stage. *)
  Lemma framable_bind_chain {X A} {R: Chain (@fframable A)} :
    forall (t: ctree E B X) (k: X -> ctree E B A),
      Framable t -> (forall x, `R (k x)) -> `R (CTree.bind t k).
  Proof.
    apply tower.
    - intros T HT t k Ht Hk S HS; apply HT; auto; intro x; apply Hk, HS.
    - intros R' IH t k Ht Hk; apply framable_unfold in Ht.
      cbn; unfold observe; cbn.
      destruct Ht; cbn.
      + apply Hk.
      + apply FrStuckF.
      + apply FrStepF; apply IH; auto; intro; apply (b_chain R'), Hk.
      + apply FrGuardF; apply IH; auto; intro; apply (b_chain R'), Hk.
      + apply FrVisF; auto; intro; apply IH; auto; intro; apply (b_chain R'), Hk.
      + apply FrBrF.
        * intro; apply guards_to_step_bind; auto.
        * intro; apply IH; auto; intro; apply (b_chain R'), Hk.
  Qed.

  (** Bind preserves framability. *)
  Lemma framable_bind {X A} (t: ctree E B X) (k: X -> ctree E B A) :
    Framable t -> (forall x, Framable (k x)) -> Framable (CTree.bind t k).
  Proof. apply framable_bind_chain. Qed.

  (** Iteration of framable bodies is framable. *)
  Lemma framable_iter {I A} (body: I -> ctree E B (I + A)) :
    (forall i, Framable (body i)) -> forall i, Framable (CTree.iter body i).
  Proof.
    intro Hbody; unfold Framable; coinduction R IH; intro i.
    rewrite unfold_iter.
    apply (framable_bind_chain (R := chain_b R)); [apply Hbody|].
    intros [i'|a]; cbn; constructor; apply IH.
  Qed.
End Framable.


(** One-node simulation shape up to [S], avoiding coinduction through silent guards. *)
Variant csim_shape {E B X} (RV : X -> X -> Prop)
    (S : ctree E B X -> ctree E B X -> Prop) :
    ctree' E B X -> ctree' E B X -> Prop :=
| CsStuckF v : csim_shape RV S StuckF v
| CsRetF x x' : RV x x' -> csim_shape RV S (RetF x) (RetF x')
| CsStepF t t' : S t t' -> csim_shape RV S (StepF t) (StepF t')
| CsGuardF t t' : S t t' -> csim_shape RV S (GuardF t) (GuardF t')
| CsVisF {Y} (e : E Y) k k' :
    (forall y, S (k y) (k' y)) -> csim_shape RV S (VisF e k) (VisF e k')
| CsBrF {Y} (c : B Y) k k' :
    (forall y, can_trans (k y)) -> (forall y, S (k y) (k' y)) ->
    csim_shape RV S (BrF c k) (BrF c k').

Section StructuralSimulation.
  Context {E B : Type -> Type} {X : Type} (RV : X -> X -> Prop)
    (S : ctree E B X -> ctree E B X -> Prop).
  Hypothesis Hshape : forall t t', S t t' ->
    csim_shape RV S (observe t) (observe t').

  (** Structural matching transports a transition forward by finite induction on [trans_]. *)
  Lemma csim_shape_trans_l {R : Chain (csimF RV)}
      (HS : forall t t', S t t' -> `R t t') :
    forall l ot ou, trans_ l ot ou -> forall ot', csim_shape RV S ot ot' ->
      exists l' u', trans_ l' ot' (observe u') /\
        simL RV l l' /\ `R (go ou) u'.
  Proof.
    intros l ot ou HT; induction HT; intros ot' Hsh; ddestruction Hsh.
    - destruct (IHHT _ (Hshape _ _ (H0 x))) as (l' & u' & HT' & HL & HR).
      exists l', u'; split; [eapply Transbr with (x := x); exact HT' | auto].
    - destruct (IHHT _ (Hshape _ _ H)) as (l' & u' & HT' & HL & HR).
      exists l', u'; split; [now constructor | auto].
    - exists τ, t'; split; [constructor; reflexivity |].
      split; [constructor |].
      rewrite <- ctree_eta, H; now apply HS.
    - exists (obs e x), (k' x); split; [constructor; reflexivity |].
      split; [constructor |].
      rewrite <- ctree_eta, <- H; apply HS, H0.
    - exists (val x'), Stuck; split; [constructor |].
      split; [now constructor | apply csim_stuck_l].
  Qed.
(** Structural matching transports a transition backward when the source can transition. *)
Lemma csim_shape_trans_r {R : Chain (csimF RV)}
      (HS : forall t t', S t t' -> `R t t') :
    forall l' ot' ou', trans_ l' ot' ou' ->
      forall ot, csim_shape RV S ot ot' -> can_trans (go ot) ->
      exists l u, trans_ l ot (observe u) /\
        simL RV l l' /\ `R u (go ou').
  Proof.
    intros l' ot' ou' HT; induction HT; intros ot Hsh HC;
      ddestruction Hsh;
      try solve [destruct HC as (l0 & u0 & HT0);
        exfalso; eapply trans_stuck_inv; exact HT0].
    - destruct (IHHT _ (Hshape _ _ (H0 x)) (H x)) as (l0 & u & HT0 & HL & HR).
      exists l0, u; split; [eapply Transbr with (x := x); exact HT0 | auto].
    - assert (HC0 : can_trans (go (observe t0))).
      { rewrite <- ctree_eta; exact (proj1 (can_trans_guard t0) HC). }
      destruct (IHHT _ (Hshape _ _ H) HC0) as (l0 & u & HT0 & HL & HR).
      exists l0, u; split; [now constructor | auto].
    - exists τ, t0; split; [constructor; reflexivity |].
      split; [constructor |].
      rewrite <- ctree_eta, H; now apply HS.
    - exists (obs e x), (k0 x); split; [constructor; reflexivity |].
      split; [constructor |].
      rewrite <- ctree_eta, <- H; apply HS, H0.
    - exists (val x), Stuck; split; [constructor |].
      split; [now constructor | apply csim_stuck_l].
  Qed.

  (** Every invariant pair with matching observations is a simulation, by finite induction on [trans_]. *)
  Theorem csim_structural : forall t t', S t t' -> csim RV t t'.
  Proof.
    unfold csim; apply (tower (b := csimF RV)
      (P := fun R => forall t t', S t t' -> R t t')).
    - intros T HT t t' H U HU; apply HT; auto.
    - intros R IH t t' H; split.
      + intros l u HT.
        destruct (csim_shape_trans_l IH _ _ _ HT _ (Hshape _ _ H))
          as (l' & u' & HT' & HL & HR).
        exists l', u'; split; [exact HT' | split; [exact HL |]].
        now rewrite <- ctree_eta in HR.
      + intros HC l' u' HT'.
        assert (HC0 : can_trans (go (observe t))).
        { now rewrite <- ctree_eta. }
        destruct (csim_shape_trans_r IH _ _ _ HT' _ (Hshape _ _ H) HC0)
          as (l & u & HT & HL & HR).
        exists l, u; split; [exact HT | split; [exact HL |]].
        now rewrite <- ctree_eta in HR.
  Qed.
End StructuralSimulation.
Section StructuralCongruence.
  Context {E B : Type -> Type} {X : Type} (RV : X -> X -> Prop)
    (S : ctree E B X -> ctree E B X -> Prop).
  Context (HS : Proper (equ eq ==> equ eq ==> iff) S).

  (** Transport structural shapes along tree equivalence on both sides. *)
  Local Lemma csim_shape_transport ot1 ot2 ou1 ou2 :
    going (equ eq) ot1 ou1 -> going (equ eq) ot2 ou2 ->
    csim_shape RV S ot1 ot2 -> csim_shape RV S ou1 ou2.
  Proof.
    intros [H1] [H2] Hsh; step in H1; step in H2.
    change (equb eq (equ eq) ot1 ou1) in H1.
    change (equb eq (equ eq) ot2 ou2) in H2.
    destruct Hsh; ddestruction H1; try solve [constructor];
      ddestruction H2; constructor.
    - assumption.
    - eapply HS; [symmetry; eassumption | symmetry; eassumption | eassumption].
    - eapply HS; [symmetry; eassumption | symmetry; eassumption | eassumption].
    - intro y; eapply HS; [symmetry; eauto | symmetry; eauto | auto].
    - intro y; rewrite <- (REL y); auto.
    - intro y; eapply HS; [symmetry; eauto | symmetry; eauto | auto].
  Qed.

  (** Structural simulation shapes respect equivalence of observations. *)
  #[global] Instance csim_shape_equ :
    Proper (going (equ eq) ==> going (equ eq) ==> iff) (csim_shape RV S).
  Proof.
    intros ot1 ou1 H1 ot2 ou2 H2; split; intro Hsh.
    - eapply csim_shape_transport; eauto.
    - eapply csim_shape_transport; [symmetry; exact H1 | symmetry; exact H2 | exact Hsh].
  Qed.
End StructuralCongruence.
