From Stdlib Require Import List Relations Arith.PeanoNat Lia Classes.Morphisms
  Program.Equality.
From Coinduction Require Import all.
From TICL Require Import CTree.Interp.CSL.Owned
  CTree.Interp.Yield.SBisim CTree.Interp.Yield.Nondeterministic
  CTree.Interp.State.Mod CTree.Interp.Yield.Mod CTree.Logic.Trans CTree.Trace
  CTree.Logic.CanStep CTree.Logic.EG
  Logic.World Logic.Setoid Logic.Semantics Utils.Pcm Utils.Execution Utils.Relations.

Import CTreeNotations ListNotations Kripke.
Local Open Scope ctree_scope.
Local Open Scope pcm_scope.
Local Open Scope nat_scope.

Definition AsepWorld := World (writerE (CSLObs (nat * nat))).
Definition AsepTree := ctreeW (CSLObs (nat * nat)) Bn (SSig * unit).
Definition AsepPred := AsepTree -> AsepWorld -> Prop.
Definition AsepRet := SSig * unit -> AsepWorld -> Prop.

Definition state_sat (I : OwnedCfg -> assn ManagedHeap) : OwnedCfg -> Prop :=
  fun c => owned_wf c /\ I c (joined_heap c).

Definition state_obligation (i : side) (P : OwnedCfg -> Prop) (c : OwnedCfg)
  : assn ManagedHeap := fun h => h ≈ oc_heap c i /\ P (project i c).

Lemma state_split_iff (P Q : OwnedCfg -> Prop) c :
  state_sat (fun d => asep (state_obligation Child P d)
                          (state_obligation Parent Q d)) c <->
  owned_wf c /\ P (project Child c) /\ Q (project Parent c).
Proof.
  split; intros (Hwf & Hsplit); split; [exact Hwf| |exact Hwf|].
  - pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hd).
    unfold state_obligation, joined_heap in Hsplit.
    exact (proj1 (asep_pinned _ _ _ _ Hd) Hsplit).
  - pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hd).
    unfold state_obligation, joined_heap.
    exact (proj2 (asep_pinned _ _ _ _ Hd) Hsplit).
Qed.

Lemma state_split_proper (P Q : OwnedCfg -> Prop) :
  Proper (owned_equ ==> iff) P -> Proper (owned_equ ==> iff) Q ->
  Proper (owned_equ ==> iff)
    (state_sat (fun c => asep (state_obligation Child P c) (state_obligation Parent Q c))).
Proof.
  intros HP HQ c d E.
  assert (Hwf : owned_wf c <-> owned_wf d).
  { split; [exact (owned_wf_equ c d E)|exact (owned_wf_equ d c (symmetry E))]. }
  rewrite (state_split_iff P Q c), (state_split_iff P Q d), Hwf,
    (HP _ _ (project_equ Child c d E)),
    (HQ _ _ (project_equ Parent c d E)).
  reflexivity.
Qed.

Lemma state_split_forget (A B : assn ManagedHeap) c :
  AProper A -> AProper B ->
  state_sat (fun d => asep
    (state_obligation Child (fun e => A (csl_memory (joined_state e))) d)
    (state_obligation Parent (fun e => B (csl_memory (joined_state e))) d)) c ->
  asep A B (csl_memory (joined_state c)).
Proof.
  intros HA HB HI.
  destruct (proj1 (state_split_iff _ _ c) HI) as (Hwf & HC & HP).
  rewrite !owned_joined_state_project in HC, HP.
  change (A (oc_heap c Child)) in HC; change (B (oc_heap c Parent)) in HP.
  exists (oc_heap c Child), (oc_heap c Parent).
  destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hd).
  split; [exact Hd|]; split; [apply peq_refl|]; split; assumption.
Qed.

Record AsepState := {
  as_cfg : OwnedCfg;
  as_global : AsepWorld;
  as_local : side -> AsepWorld
}.

Definition asep_state_ok (s : AsepState) : Prop :=
  active_erasable (as_cfg s) /\ not_done (as_global s) /\
  forall i, not_done (as_local s i).

Definition asep_advance (s : AsepState) (a : OwnedAction)
    (d : OwnedCfg) : AsepState :=
  {| as_cfg := d;
     as_global := after_logs (action_logs a (joined_heap d)) (as_global s);
     as_local := fun i =>
       if side_eqb (owner a) i then
         after_logs
           (action_logs (project_action i (as_cfg s) a)
             (joined_heap (project i d))) (as_local s i)
       else as_local s i |}.

Definition asep_step (s : AsepState) (a : OwnedAction)
    (s' : AsepState) : Prop :=
  owned_step (as_cfg s) a (as_cfg s') /\
  s' = asep_advance s a (as_cfg s').

Definition asep_closed (I : AsepState -> Prop) : Prop :=
  forall s a s', asep_state_ok s -> I s -> asep_step s a s' -> I s'.

Definition local_obligation (i : side) (P : AsepPred)
    (s : AsepState) : assn ManagedHeap :=
  state_obligation i
    (fun c => P (owned_interp c) (as_local s i)) (as_cfg s).

Definition asep_at (I : AsepState -> Prop) (P Q : AsepPred)
    (s : AsepState) : Prop :=
  asep_state_ok s /\ I s /\
  asep (local_obligation Child P s) (local_obligation Parent Q s)
    (joined_heap (as_cfg s)).

Definition asep_sat (I : AsepState -> Prop) (P Q : AsepPred) : AsepPred :=
  fun t w => exists s,
    t ~ owned_interp (as_cfg s) /\ w = as_global s /\ asep_at I P Q s.

Definition asep_pred_ok (P : AsepPred) : Prop :=
  (forall t w, P t w -> not_done w) /\
  Proper (sbisim eq ==> eq ==> iff) P.

Lemma asep_state_ok_step (s : AsepState) (a : OwnedAction) (s' : AsepState) :
  asep_state_ok s -> asep_step s a s' -> asep_state_ok s'.
Proof.
  intros (He & Hw & Hl) (Hs & E).
  pose proof (active_erasable_step _ _ _ He Hs) as He'.
  unfold asep_state_ok; split; [exact He'|].
  rewrite E; cbn [asep_advance as_global as_local as_cfg]; split; [apply after_logs_not_done, Hw|].
  intro i; cbn [asep_advance as_local];
    destruct (side_eqb (owner a) i); [apply after_logs_not_done|]; apply Hl.
Qed.

Lemma asep_closed_true : asep_closed (fun _ => True).
Proof. intros s a s' Hok HI Hs; constructor. Qed.

Lemma local_obligation_proper (i : side) (P : AsepPred) (s : AsepState) :
  AProper (local_obligation i P s).
Proof.
  intros h h' E (Hpin & HP); split;
    [eapply peq_trans; [apply peq_sym; exact E|exact Hpin]|exact HP].
Qed.

Lemma asep_local_pinned (s : AsepState) (P Q : AsepPred) :
  owned_wf (as_cfg s) ->
  (asep (local_obligation Child P s) (local_obligation Parent Q s)
     (joined_heap (as_cfg s)) <->
   P (owned_interp (project Child (as_cfg s))) (as_local s Child) /\
   Q (owned_interp (project Parent (as_cfg s))) (as_local s Parent)).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hd).
  unfold local_obligation, state_obligation, joined_heap; apply asep_pinned, Hd.
Qed.

Lemma asep_at_intro (I : AsepState -> Prop) (P Q : AsepPred) (s : AsepState) :
  asep_state_ok s -> I s ->
  P (owned_interp (project Child (as_cfg s))) (as_local s Child) ->
  Q (owned_interp (project Parent (as_cfg s))) (as_local s Parent) ->
  asep_at I P Q s.
Proof.
  intros Hok HI HC HP; split; [exact Hok|]; split; [exact HI|].
  apply (proj2 (asep_local_pinned s P Q (proj1 (proj1 (proj1 Hok))))); auto.
Qed.

Lemma asep_at_inv (I : AsepState -> Prop) (P Q : AsepPred) (s : AsepState) :
  asep_at I P Q s ->
  asep_state_ok s /\ owned_wf (as_cfg s) /\ I s /\
  P (owned_interp (project Child (as_cfg s))) (as_local s Child) /\
  Q (owned_interp (project Parent (as_cfg s))) (as_local s Parent).
Proof.
  intros (Hok & HI & Hsep).
  pose proof (proj1 (proj1 (proj1 Hok))) as Hwf.
  apply (proj1 (asep_local_pinned s P Q Hwf)) in Hsep.
  exact (conj Hok (conj Hwf (conj HI Hsep))).
Qed.

Lemma asep_sat_intro (I : AsepState -> Prop) (P Q : AsepPred) (s : AsepState) :
  asep_at I P Q s ->
  asep_sat I P Q (owned_interp (as_cfg s)) (as_global s).
Proof. intro H; exists s; split; [reflexivity|auto]. Qed.

Lemma asep_sat_inv (I : AsepState -> Prop) (P Q : AsepPred) t w :
  asep_sat I P Q t w -> exists s,
  t ~ owned_interp (as_cfg s) /\ w = as_global s /\
  asep_state_ok s /\ owned_wf (as_cfg s) /\ I s /\
  P (owned_interp (project Child (as_cfg s))) (as_local s Child) /\
  Q (owned_interp (project Parent (as_cfg s))) (as_local s Parent).
Proof.
  intros (s & Et & Ew & H); exists s; split; [exact Et|].
  split; [exact Ew|apply asep_at_inv, H].
Qed.

Lemma asep_sat_pred_ok (I : AsepState -> Prop) (P Q : AsepPred) :
  asep_pred_ok (asep_sat I P Q).
Proof.
  split.
  - intros t w (s & Et & -> & Hok & HI & Hsep); exact (proj1 (proj2 Hok)).
  - intros t u E w v <-; split; intros (s & Et & Ew & H); exists s;
      split; [etransitivity; [symmetry; exact E|exact Et]|auto|
              etransitivity; [exact E|exact Et]|auto].
Qed.

Lemma asep_sat_mono (I J : AsepState -> Prop) (P P' Q Q' : AsepPred) :
  (forall s, I s -> J s) ->
  (forall t w, P t w -> P' t w) ->
  (forall t w, Q t w -> Q' t w) ->
  forall t w, asep_sat I P Q t w -> asep_sat J P' Q' t w.
Proof.
  intros HI HP HQ t w H.
  apply asep_sat_inv in H as (s & Et & Ew & Hok & Hwf & Hinv & HC & HPar).
  exists s; split; [exact Et|]; split; [exact Ew|].
  apply asep_at_intro; auto.
Qed.

Lemma asep_pred_ok_entails {b : bool}
  (p : ticl_at (writerE (CSLObs (nat * nat))) (SSig * unit) b) :
  asep_pred_ok (entails (SSig * unit) b p).
Proof.
  split.
  - intros t w H; eapply ticl_not_done; exact H.
  - intros t u E w v Ew.
    exact (@proper_entails_meq ctree (writerE (CSLObs (nat * nat))) Bn _ (SSig * unit)
      (sbisim eq) _ _ b p t u E w v Ew).
Qed.

Lemma asep_pred_transport P : asep_pred_ok P -> forall t u w,
  t ~ u -> P t w -> P u w.
Proof. intros [_ HP] t u w E H; exact (proj1 (HP t u E w w eq_refl) H). Qed.

Lemma asep_pred_ok_anc P Q :
  asep_pred_ok P -> asep_pred_ok Q -> asep_pred_ok (anc P Q).
Proof.
  intros [HP EP] [HQ EQ]; split.
  - intros t w [H _]; eauto.
  - intros t u E w v <-; exact (proper_ax_equ (meq := sbisim eq)
      (HP := EP) (HQ := EQ) t u E w w eq_refl).
Qed.

Lemma asep_pred_ok_enc P Q :
  asep_pred_ok P -> asep_pred_ok Q -> asep_pred_ok (enc P Q).
Proof.
  intros [HP EP] [HQ EQ]; split.
  - intros t w [H _]; eauto.
  - intros t u E w v <-; exact (proper_ex_equ (meq := sbisim eq)
      (HP := EP) (HQ := EQ) t u E w w eq_refl).
Qed.

Lemma asep_pred_ok_agc P : asep_pred_ok P -> asep_pred_ok (agc P).
Proof.
  intros [HP EP]; split.
  - intros t w H; step in H; exact (HP t w (proj1 H)).
  - intros t u E w v <-; exact (proper_ag_equ (meq := sbisim eq)
      (HP := EP) t u E w w eq_refl).
Qed.

Definition owner_visible (i : side) (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) : Prop :=
  owner a = i /\ erase_action_label a (joined_heap c') <> None.

Definition asep_silent (s s' : AsepState) : Prop :=
  exists a, asep_step s a s' /\
    erase_action_label a (joined_heap (as_cfg s')) = None.

Definition asep_frontier (s s' : AsepState) : Prop :=
  exists mid a,
    clos_refl_trans _ asep_silent s mid /\
    asep_step mid a s' /\
    erase_action_label a (joined_heap (as_cfg s')) <> None.

Lemma asep_silent_lift (s : AsepState) (d : OwnedCfg) :
  clos_refl_trans _ silent_next (as_cfg s) d ->
  exists s', clos_refl_trans _ asep_silent s s' /\ as_cfg s' = d.
Proof.
  intro H; remember (as_cfg s) as c eqn:E; revert s E.
  induction H as [c d (a & Hs & Hl)|c|c d e H1 IH1 H2 IH2]; intros s E.
  - subst c; exists (asep_advance s a d); split; [|reflexivity].
    apply rt_step; exists a; split; [split; [exact Hs|reflexivity]|exact Hl].
  - exists s; split; [apply rt_refl|symmetry; exact E].
  - destruct (IH1 s E) as (mid & Hmid & Emid).
    destruct (IH2 mid (eq_sym Emid)) as (s' & Hs' & Es').
    exists s'; split; [eapply rt_trans; eauto|exact Es'].
Qed.

Lemma asep_silent_cfg s s' :
  clos_refl_trans _ asep_silent s s' ->
  clos_refl_trans _ silent_next (as_cfg s) (as_cfg s').
Proof.
  intro H; induction H as [s s' (a & (Hs & E) & Hl)|s|s mid s' H1 IH1 H2 IH2].
  - apply rt_step; exists a; auto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma asep_silent_worlds (s s' : AsepState) :
  clos_refl_trans _ asep_silent s s' ->
  as_global s' = as_global s /\ forall i, as_local s' i = as_local s i.
Proof.
  intro H; induction H as [s s' (a & (Hs & E) & Hl)|s|s mid s' H1 IH1 H2 IH2].
  - rewrite E; cbn [asep_advance as_global as_local as_cfg]; split.
    + unfold action_logs; rewrite Hl; reflexivity.
    + intro i; cbn [asep_advance as_global as_local as_cfg];
      destruct (side_eqb (owner a) i); [|reflexivity].
      unfold action_logs; rewrite (proj2 (owned_project_label_none i (as_cfg s) a
        (joined_heap (as_cfg s')) (joined_heap (project i (as_cfg s')))) Hl).
      reflexivity.
  - split; reflexivity.
  - destruct IH1 as [Eg El], IH2 as [Eg' El']; split; [congruence|].
    intro i; rewrite El', El; reflexivity.
Qed.

Lemma asep_closed_silent (I : AsepState -> Prop) (s s' : AsepState) :
  asep_closed I -> asep_state_ok s -> I s ->
  clos_refl_trans _ asep_silent s s' -> asep_state_ok s' /\ I s'.
Proof.
  intros Hclosed Hok HI H; revert Hok HI.
  induction H as [s s' (a & Hs & Hl)|s|s mid s' H1 IH1 H2 IH2]; intros Hok HI.
  - split; [eapply asep_state_ok_step|eapply Hclosed]; eauto.
  - auto.
  - destruct (IH1 Hok HI); apply IH2; assumption.
Qed.

Lemma asep_closed_frontier (I : AsepState -> Prop) (s s' : AsepState) :
  asep_closed I -> asep_state_ok s -> I s ->
  asep_frontier s s' -> asep_state_ok s' /\ I s'.
Proof.
  intros Hclosed Hok HI (mid & a & Hsil & Hs & Hl).
  destruct (asep_closed_silent I s mid Hclosed Hok HI Hsil) as [Hokm HIm].
  split; [eapply asep_state_ok_step|eapply Hclosed]; eauto.
Qed.

Lemma asep_invisible (s : AsepState) (a : OwnedAction) (s' : AsepState) i :
  asep_state_ok s -> asep_step s a s' ->
  ~ owner_visible i (as_cfg s) a (as_cfg s') ->
  owned_interp (project i (as_cfg s)) ~ owned_interp (project i (as_cfg s')) /\
  as_local s' i = as_local s i.
Proof.
  intros (He & Hw & Hl) (Hs & E) Hnot.
  destruct (side_eq_dec (owner a) i) as [Ho|Ho].
  - assert (Hnone : erase_action_label a (joined_heap (as_cfg s')) = None).
    { destruct (erase_action_label a (joined_heap (as_cfg s'))) as [l|] eqn:El;
        [exfalso; apply Hnot; split; [exact Ho|rewrite El; discriminate]|reflexivity]. }
    split.
    + eapply owned_silent_local; [exact He|apply rt_step; exists a; auto].
    + rewrite E; cbn [asep_advance as_global as_local as_cfg]; rewrite (proj2 (side_eqb_spec _ _) Ho).
      unfold action_logs; rewrite (proj2 (owned_project_label_none i (as_cfg s) a
        (joined_heap (as_cfg s')) (joined_heap (project i (as_cfg s')))) Hnone).
      reflexivity.
  - split.
    + apply owned_interp_equ; symmetry; eapply owned_step_foreign; eauto.
    + rewrite E; cbn [asep_advance as_global as_local as_cfg]; destruct (side_eqb (owner a) i) eqn:Eb;
        [apply side_eqb_spec in Eb; contradiction|reflexivity].
Qed.

Lemma asep_local_step_inv (s : AsepState) (a : OwnedAction)
    (s' : AsepState) (i : side) :
  asep_state_ok s -> asep_step s a s' ->
  (owned_interp (project i (as_cfg s)) ~ owned_interp (project i (as_cfg s')) /\
   as_local s' i = as_local s i) \/
  exists u,
    ktrans (owned_interp (project i (as_cfg s))) (as_local s i)
      u (as_local s' i) /\
    u ~ owned_interp (project i (as_cfg s')).
Proof.
  intros Hok Hstep.
  destruct (side_eq_dec (owner a) i) as [Ho|Ho];
    destruct (erase_action_label a (joined_heap (as_cfg s'))) as [l|] eqn:Hl.
  - right; destruct (owned_owner_ktrans _ _ _ i (as_local s i)
      (proj1 Hok) (proj1 Hstep) Ho ltac:(rewrite Hl; discriminate)
      (proj2 (proj2 Hok) i)) as (u & Hu & Eu).
    exists u; split; [|exact Eu].
    rewrite (proj2 Hstep); cbn [asep_advance as_global as_local as_cfg];
      rewrite (proj2 (side_eqb_spec _ _) Ho); exact Hu.
  - left; eapply asep_invisible; eauto; intros [_ H]; contradiction.
  - left; eapply asep_invisible; eauto; intros [H _]; contradiction.
  - left; eapply asep_invisible; eauto; intros [H _]; contradiction.
Qed.

Lemma asep_visible_forward_owner (s : AsepState) t' w' :
  asep_state_ok s ->
  ktrans (owned_interp (as_cfg s)) (as_global s) t' w' -> not_done w' ->
  exists s' u i, asep_frontier s s' /\ t' ~ owned_interp (as_cfg s') /\
    w' = as_global s' /\
    ktrans (owned_interp (project i (as_cfg s))) (as_local s i) u (as_local s' i) /\
    u ~ owned_interp (project i (as_cfg s')) /\
    owned_interp (project (other i) (as_cfg s')) ~
      owned_interp (project (other i) (as_cfg s)) /\
    as_local s' (other i) = as_local s (other i).
Proof.
  intros Hok HT Hw'.
  destruct Hok as (He & Hw & Hl).
  destruct (owned_ktrans_forward _ _ _ _ (proj1 He) Hw HT Hw')
    as (d & a & d' & l & Hp & Hs & Hlabel & Et & Ew).
  destruct (asep_silent_lift s d Hp) as (mid & Hmid & Ed).
  destruct (asep_silent_worlds _ _ Hmid) as (Eg & El).
  pose proof (proj1 (asep_closed_silent _ _ _ asep_closed_true
    (conj He (conj Hw Hl)) I Hmid)) as Hokm.
  assert (Hsm : owned_step (as_cfg mid) a d') by (rewrite Ed; exact Hs).
  destruct (owned_owner_ktrans _ a d' (owner a) (as_local mid (owner a))
    (proj1 Hokm) Hsm eq_refl ltac:(congruence) (proj2 (proj2 Hokm) _))
    as (u & Hu & Eu).
  assert (Em : owned_interp (project (owner a) (as_cfg mid)) ~
    owned_interp (project (owner a) (as_cfg s))).
  { rewrite Ed; symmetry; eapply owned_silent_local; eauto. }
  rewrite El in Hu.
  destruct (ktrans_semiproper _ _ _ _ _ Em Hu) as (v & Hv & Euv).
  exists (asep_advance mid a d'), v, (owner a).
  split.
  - exists mid, a; split; [exact Hmid|]; split.
    + split; [exact Hsm|reflexivity].
    + change (erase_action_label a (joined_heap d') <> None); rewrite Hlabel; discriminate.
  - split; [exact Et|]; split; [cbn [asep_advance as_global as_local as_cfg]; rewrite Eg; exact Ew|].
    split.
    + cbn [asep_advance as_global as_local as_cfg]; rewrite (proj2 (side_eqb_spec _ _) eq_refl), El; exact Hv.
    + split; [etransitivity; [symmetry; exact Euv|exact Eu]|]; split.
      * cbn [asep_advance as_global as_local as_cfg]; transitivity (owned_interp (project (other (owner a)) (as_cfg mid))).
        -- apply owned_interp_equ; eapply owned_step_foreign;
             [exact Hsm|destruct (owner a); discriminate].
        -- rewrite Ed; symmetry; eapply owned_silent_local; eauto.
      * cbn [asep_advance as_global as_local as_cfg]; destruct (owner a); cbn [other side_eqb]; apply El.
Qed.

Lemma asep_local_lift (s : AsepState) i u v :
  asep_state_ok s -> owned_side_ready i (as_cfg s) ->
  ktrans (owned_interp (project i (as_cfg s))) (as_local s i) u v -> not_done v ->
  exists s' t' w', asep_frontier s s' /\ owned_side_ready i (as_cfg s') /\
    ktrans (owned_interp (as_cfg s)) (as_global s) t' w' /\
    t' ~ owned_interp (as_cfg s') /\ u ~ owned_interp (project i (as_cfg s')) /\
    w' = as_global s' /\ v = as_local s' i /\
    owned_interp (project (other i) (as_cfg s')) ~
      owned_interp (project (other i) (as_cfg s)) /\
    as_local s' (other i) = as_local s (other i).
Proof.
  intros Hok Hready HT Hlive; destruct Hok as (He & Hw & Hl).
  destruct (owned_ktrans_forward _ _ _ _ (owned_active_local _ i He) (Hl i) HT Hlive)
    as (d & a & d' & l & Hp & Hs & Hlabel & Eu & Ev).
  destruct (owned_local_silent_lift_cfg i _ _ Hp (as_cfg s) (reflexivity _) Hready)
    as (c & Hc & Hreadyc & Ec & Eforeign).
  destruct (owned_step_equ d (project i c) a d' (symmetry Ec) Hs) as (q & Hq & Eq).
  destruct (owned_step_lift i c a q Hreadyc Hq) as (b & c' & Hb & Ho & Ha & Ep).
  assert (Epost : owned_equ (project i c') d').
  { etransitivity; [exact Ep|symmetry; exact Eq]. }
  assert (Hvisible : erase_action_label b (joined_heap c') <> None).
  { intro Hnone; apply (proj2 (owned_project_label_none i c b (joined_heap c')
      (joined_heap d'))) in Hnone; rewrite Ha in Hnone; congruence. }
  destruct (erase_action_label b (joined_heap c')) as [lg|] eqn:Hlg; [|contradiction].
  destruct (owned_interp_visible _ c b c' lg (proj1 He) Hc Hb Hlg)
    as (t' & Ht' & Et').
  destruct (asep_silent_lift s c Hc) as (mid & Hmid & Ecm).
  destruct (asep_silent_worlds _ _ Hmid) as (Eg & El).
  assert (Hbm : owned_step (as_cfg mid) b c') by (rewrite Ecm; exact Hb).
  exists (asep_advance mid b c'), t',
    (as_global (asep_advance mid b c')).
  split.
  - exists mid, b; split; [exact Hmid|]; split.
    + split; [exact Hbm|reflexivity].
    + change (erase_action_label b (joined_heap c') <> None); rewrite Hlg; discriminate.
  - split; [cbn; eapply owned_side_ready_step; eauto|]; split.
    + cbn [asep_advance as_global as_local as_cfg]; rewrite Eg; eapply owned_label_ktrans;
        [exact Hlg|exact Ht'|exact Hw].
    + split; [exact Et'|]; split.
      * cbn [asep_advance as_global as_local as_cfg]; etransitivity;
          [exact Eu|apply owned_interp_equ; symmetry; exact Epost].
      * split; [reflexivity|]; split.
        -- cbn [asep_advance as_global as_local as_cfg]; rewrite Ho, (proj2 (side_eqb_spec i i) eq_refl), Ecm, Ha, El.
           rewrite (joined_heap_equ _ _ Epost); exact Ev.
        -- split.
           ++ cbn [asep_advance as_global as_local as_cfg]; apply owned_interp_equ; etransitivity; [|exact Eforeign].
              eapply owned_step_foreign; [exact Hb|rewrite Ho; destruct i; discriminate].
           ++ cbn [asep_advance as_global as_local as_cfg]; rewrite Ho; destruct i; cbn [other side_eqb]; apply El.
Qed.

Lemma asep_terminal_forward (s : AsepState) t' w' :
  asep_state_ok s ->
  ktrans (owned_interp (as_cfg s)) (as_global s) t' w' -> ~ not_done w' ->
  exists s', clos_refl_trans _ asep_silent s s' /\
    as_global s' = as_global s /\ (forall i, as_local s' i = as_local s i) /\
    tp_size (oc_pool (as_cfg s')) = 0 /\ t' ~ (Stuck : AsepTree) /\
    done_with (fun r predecessor => r = (joined_state (as_cfg s'), tt) /\
      predecessor = as_global s) w'.
Proof.
  intros Hok HT Hnd.
  destruct (owned_ktrans_terminal _ _ _ _ (proj1 (proj1 Hok)) HT Hnd)
    as (d & Hp & Hempty & Et & Hd).
  destruct (asep_silent_lift s d Hp) as (s' & Hsil & Ed).
  destruct (asep_silent_worlds _ _ Hsil) as (Eg & El).
  exists s'; split; [exact Hsil|]; split; [exact Eg|]; split; [exact El|].
  rewrite Ed; repeat split; assumption.
Qed.

Lemma asep_auc_live P R : asep_pred_ok P -> asep_pred_ok R ->
  forall t w, auc P R t w -> not_done w.
Proof.
  intros HP HR t w H; destruct H as [t w H|t w (H & _)];
    [exact (proj1 HR _ _ H)|exact (proj1 HP _ _ H)].
Qed.

Lemma asep_euc_live P R : asep_pred_ok P -> asep_pred_ok R ->
  forall t w, euc P R t w -> not_done w.
Proof.
  intros HP HR t w H; destruct H as [t w H|t w (H & _)];
    [exact (proj1 HR _ _ H)|exact (proj1 HP _ _ H)].
Qed.

Lemma asep_pred_ok_auc P R :
  asep_pred_ok P -> asep_pred_ok R -> asep_pred_ok (auc P R).
Proof.
  intros HP HR; split; [apply asep_auc_live; assumption|].
  intros t u E w v <-.
  exact (proper_au_equ (meq := sbisim eq) (HP := proj2 HP)
    (HQ := proj2 HR) t u E w w eq_refl).
Qed.

Lemma asep_pred_ok_euc P R :
  asep_pred_ok P -> asep_pred_ok R -> asep_pred_ok (euc P R).
Proof.
  intros HP HR; split; [apply asep_euc_live; assumption|].
  intros t u E w v <-.
  exact (proper_eu_equ (meq := sbisim eq) (HP := proj2 HP)
    (HQ := proj2 HR) t u E w w eq_refl).
Qed.

Lemma asep_can_step_frontier c w :
  erasable c -> can_step (owned_interp c) w ->
  (exists u v, ktrans (owned_interp c) w u v /\ not_done v) \/
  exists d, clos_refl_trans _ silent_next c d /\ tp_size (oc_pool d) = 0.
Proof.
  intros He (u & v & HT); inversion HT; subst.
  - left; exists u, v; auto.
  - left; exists u, (Obs e v0); split; [exact HT|constructor].
  - right; destruct (owned_interp_val_forward c x u He H) as (d & Hp & H0 & _ & _).
    exists d; auto.
  - right; destruct (owned_interp_val_forward c x u He H) as (d & Hp & H0 & _ & _).
    exists d; auto.
Qed.

Lemma asep_local_terminal_lift (s : AsepState) i d :
  owned_side_ready i (as_cfg s) ->
  clos_refl_trans _ silent_next (project i (as_cfg s)) d -> tp_size (oc_pool d) = 0 ->
  exists s', clos_refl_trans _ asep_silent s s' /\
    as_global s' = as_global s /\ (forall j, as_local s' j = as_local s j) /\
    tp_size (oc_pool (project i (as_cfg s'))) = 0 /\
    tp_focus (oc_pool (as_cfg s')) = None /\
    owned_equ (project (other i) (as_cfg s')) (project (other i) (as_cfg s)).
Proof.
  intros Hr Hp H0.
  destruct (owned_local_silent_lift_cfg i _ _ Hp (as_cfg s) (reflexivity _) Hr)
    as (c & Hc & Hready & Ec & Eforeign).
  assert (Hempty : tp_size (oc_pool (project i c)) = 0).
  { rewrite (tp_equ_size _ _ (proj1 Ec)); exact H0. }
  destruct (asep_silent_lift s c Hc) as (s' & Hsil & Ecm).
  destruct (asep_silent_worlds _ _ Hsil) as (Eg & El).
  exists s'; split; [exact Hsil|]; split; [exact Eg|]; split; [exact El|].
  rewrite Ecm; split; [exact Hempty|]; split;
    [eapply owned_side_ready_empty; eauto|exact Eforeign].
Qed.

Lemma asep_empty_can_step c w :
  erasable c -> not_done w -> tp_size (oc_pool c) = 0 -> can_step (owned_interp c) w.
Proof.
  intros He Hw H0; rewrite (owned_interp_terminal c He H0); destruct Hw as [|Y e v].
  - exists Stuck, (Done (joined_state c,tt)); apply KtransDone, trans_ret.
  - exists Stuck, (Finish e v (joined_state c,tt)); apply KtransFinish, trans_ret.
Qed.

Lemma asep_progress_ready (s : AsepState) i :
  asep_state_ok s -> owned_side_ready i (as_cfg s) ->
  can_step (owned_interp (project i (as_cfg s))) (as_local s i) ->
  can_step (owned_interp (project (other i) (as_cfg s))) (as_local s (other i)) ->
  can_step (owned_interp (as_cfg s)) (as_global s).
Proof.
  intros Hok Hr Hi Ho; pose proof (proj1 Hok) as He.
  destruct (asep_can_step_frontier _ _ (owned_active_local _ i He) Hi)
    as [(u & v & HT & Hlive)|(d & Hp & H0)].
  - destruct (asep_local_lift s i u v Hok Hr HT Hlive)
      as (s' & t' & w' & _ & _ & Ht & _); exists t', w'; exact Ht.
  - destruct (asep_local_terminal_lift s i d Hr Hp H0)
      as (mid & Hsil & Eg & El & Hempty & Hfocus & Eforeign).
    pose proof (asep_silent_cfg _ _ Hsil) as Hcfg.
    rewrite (owned_interp_silent _ _ (proj1 He) Hcfg), <- Eg.
    pose proof (proj1 (asep_closed_silent _ _ _ asep_closed_true Hok I Hsil)) as Hokm.
    pose proof (proj1 Hokm) as Hem.
    assert (Hother : can_step (owned_interp (project (other i) (as_cfg mid)))
      (as_local mid (other i))).
    { rewrite (owned_interp_equ _ _ Eforeign), El; exact Ho. }
    destruct (asep_can_step_frontier _ _ (owned_active_local _ (other i) Hem) Hother)
      as [(u & v & HT & Hlive)|(d' & Hp' & H0')].
    + destruct (asep_local_lift mid (other i) u v Hokm (or_introl Hfocus) HT Hlive)
        as (s' & t' & w' & _ & _ & Ht & _); exists t', w'; exact Ht.
    + destruct (asep_local_terminal_lift mid (other i) d' (or_introl Hfocus) Hp' H0')
        as (s' & Hsil' & Eg' & El' & Hempty' & Hfocus' & Eforeign').
      rewrite (owned_interp_silent _ _ (proj1 Hem) (asep_silent_cfg _ _ Hsil')), <- Eg'.
      pose proof (proj1 (asep_closed_silent _ _ _ asep_closed_true Hokm I Hsil')) as Hok'.
      apply asep_empty_can_step; [exact (proj1 (proj1 Hok'))|exact (proj1 (proj2 Hok'))|].
      assert (Hi' : tp_size (oc_pool (project i (as_cfg s'))) = 0).
      { assert (Hii : other (other i) = i) by (destruct i; reflexivity).
        rewrite Hii in Eforeign'; rewrite (tp_equ_size _ _ (proj1 Eforeign')); exact Hempty. }
      pose proof (project_size_partition (as_cfg s')) as Hpart.
      destruct i; cbn [other] in Hempty'; rewrite Hi', Hempty' in Hpart;
        symmetry; exact Hpart.
Qed.

Lemma asep_progress (s : AsepState) :
  asep_state_ok s ->
  can_step (owned_interp (project Child (as_cfg s))) (as_local s Child) ->
  can_step (owned_interp (project Parent (as_cfg s))) (as_local s Parent) ->
  can_step (owned_interp (as_cfg s)) (as_global s).
Proof.
  intros Hok HC HP.
  destruct (tp_focus (oc_pool (as_cfg s))) as [j|] eqn:Hfocus.
  - remember (Vector.nth (tp_tags (oc_pool (as_cfg s))) j) as i eqn:Hi.
    assert (Hr : owned_side_ready i (as_cfg s)).
    { right; exists j; split; [exact Hfocus|symmetry; exact Hi]. }
    apply (asep_progress_ready s i Hok Hr); destruct i; cbn [other]; assumption.
  - apply (asep_progress_ready s Child Hok (or_introl Hfocus)); assumption.
Qed.

Lemma asep_anc_live (s : AsepState) i P R (u : AsepTree) (v : AsepWorld) :
  asep_state_ok s ->
  anc P R (owned_interp (project i (as_cfg s))) (as_local s i) ->
  (forall t w, R t w -> not_done w) ->
  ktrans (owned_interp (as_cfg s)) (as_global s) u v -> not_done v.
Proof.
  intros Hok HC HR HT.
  assert (Hcontra : ~ not_done v -> False).
  { intro Hdead.
    destruct (asep_terminal_forward s u v Hok HT Hdead)
      as (s' & Hsil & Eg & El & Hempty & _).
    pose proof (proj1 Hok) as He.
    pose proof (proj1 (asep_closed_silent _ _ _ asep_closed_true Hok I Hsil)) as Hok'.
    pose proof (asep_silent_cfg _ _ Hsil) as Hcfg.
    assert (E : owned_interp (project i (as_cfg s)) ~
      (Ret (joined_state (project i (as_cfg s')),tt) : AsepTree)).
    { etransitivity; [eapply owned_silent_local; eauto|apply owned_interp_terminal;
        [eapply owned_active_local; exact (proj1 Hok')|apply project_size_terminal, Hempty]]. }
    destruct HC as (_ & _ & Hnext).
    assert (Hret : exists t' w', ktrans
      (Ret (joined_state (project i (as_cfg s')),tt) : AsepTree) (as_local s i) t' w' /\
      ~ not_done w').
    { destruct (proj2 (proj2 Hok) i) as [|Y e x].
      - exists Stuck, (Done (joined_state (project i (as_cfg s')),tt));
          split; [apply KtransDone, trans_ret|intro H; inversion H].
      - exists Stuck, (Finish e x (joined_state (project i (as_cfg s')),tt));
          split; [apply KtransFinish, trans_ret|intro H; inversion H]. }
    destruct Hret as (t' & w' & Ht & Hdead').
    destruct (ktrans_semiproper _ _ _ _ _ (symmetry E) Ht) as (q & Hq & _).
    exact (Hdead' (HR q w' (Hnext q w' Hq))). }
  destruct v; try constructor; exfalso; apply Hcontra; intro H; inversion H.
Qed.

Theorem asep_anc_compose (I : AsepState -> Prop) (P P' Q Q' : AsepPred) t w :
  asep_closed I ->
  asep_pred_ok P -> asep_pred_ok P' -> asep_pred_ok Q -> asep_pred_ok Q' ->
  asep_sat I (anc P P') (anc Q Q') t w ->
  anc (asep_sat I P Q)
    (fun u v => asep_sat I P' Q u v \/ asep_sat I P Q' u v) t w.
Proof.
  intros Hclosed HP HP' HQ HQ' H.
  apply asep_sat_inv in H as (s & Et & -> & Hok & Hwf & HI & HC & HPar).
  split.
  - exists s; split; [exact Et|]; split; [reflexivity|].
    apply asep_at_intro; [exact Hok|exact HI|exact (proj1 HC)|exact (proj1 HPar)].
  - split.
    + rewrite Et; eapply asep_progress;
        [exact Hok|exact (proj1 (proj2 HC))|exact (proj1 (proj2 HPar))].
    + intros u v HT.
      destruct (ktrans_semiproper _ _ _ _ _ Et HT) as (q & Hq & Eu).
      pose proof (asep_anc_live s Child P P' q v Hok HC (proj1 HP') Hq) as Hv.
      destruct (asep_visible_forward_owner s q v Hok Hq Hv)
        as (s' & r & i & Hfront & Eq & Ev & Hlocal & Er & Ef & Ew).
      destruct (asep_closed_frontier I s s' Hclosed Hok HI Hfront) as [Hok' HI'].
      destruct i; [left|right]; exists s'; split;
        [etransitivity; [exact Eu|exact Eq]| |etransitivity; [exact Eu|exact Eq]|];
        split; [exact Ev| |exact Ev|]; apply asep_at_intro;
        try exact Hok'; try exact HI'; cbn [other] in Ef, Ew.
      * eapply asep_pred_transport; [exact HP'|exact Er|apply (proj2 (proj2 HC)), Hlocal].
      * rewrite Ew; eapply asep_pred_transport; [exact HQ|symmetry; exact Ef|exact (proj1 HPar)].
      * rewrite Ew; eapply asep_pred_transport; [exact HP|symmetry; exact Ef|exact (proj1 HC)].
      * eapply asep_pred_transport; [exact HQ'|exact Er|apply (proj2 (proj2 HPar)), Hlocal].
Qed.

Lemma asep_enc_ready (s : AsepState) i (P R : AsepPred) :
  asep_state_ok s -> owned_side_ready i (as_cfg s) -> asep_pred_ok R ->
  enc P R (owned_interp (project i (as_cfg s))) (as_local s i) ->
  exists s' q, asep_frontier s s' /\
    ktrans (owned_interp (as_cfg s)) (as_global s) q (as_global s') /\
    q ~ owned_interp (as_cfg s') /\
    R (owned_interp (project i (as_cfg s'))) (as_local s' i) /\
    owned_interp (project (other i) (as_cfg s')) ~
      owned_interp (project (other i) (as_cfg s)) /\
    as_local s' (other i) = as_local s (other i).
Proof.
  intros Hok Hready HR (_ & r & v & HT & Hpost).
  destruct (asep_local_lift s i r v Hok Hready HT (proj1 HR r v Hpost))
    as (s' & q & w' & Hfront & _ & Hq & Eq & Er & Ew & Ev & Ef & El).
  subst w' v; exists s', q; split; [exact Hfront|]; split; [exact Hq|].
  split; [exact Eq|]; split.
  - eapply asep_pred_transport; [exact HR|exact Er|exact Hpost].
  - split; assumption.
Qed.

Theorem asep_enc_compose (I : AsepState -> Prop) (P P' Q Q' : AsepPred) t w :
  asep_closed I ->
  asep_pred_ok P -> asep_pred_ok P' -> asep_pred_ok Q -> asep_pred_ok Q' ->
  asep_sat I (enc P P') (enc Q Q') t w ->
  enc (asep_sat I P Q)
    (fun u v => asep_sat I P' Q u v \/ asep_sat I P Q' u v) t w.
Proof.
  intros Hclosed HP HP' HQ HQ' H.
  apply asep_sat_inv in H as (s & Et & -> & Hok & Hwf & HI & HC & HPar).
  split.
  - exists s; split; [exact Et|]; split; [reflexivity|].
    apply asep_at_intro; [exact Hok|exact HI|exact (proj1 HC)|exact (proj1 HPar)].
  - assert (Hready : exists i, owned_side_ready i (as_cfg s)).
    { destruct (tp_focus (oc_pool (as_cfg s))) as [j|] eqn:Hf.
      - exists (Vector.nth (tp_tags (oc_pool (as_cfg s))) j); right; exists j; auto.
      - exists Child; left; exact Hf. }
    destruct Hready as ([|] & Hready).
    + destruct (asep_enc_ready s Child P P' Hok Hready HP' HC)
        as (s' & q & Hfront & HT & Eq & Hpost & Ef & Ew).
      destruct (ktrans_semiproper _ _ _ _ _ (symmetry Et) HT) as (r & HTr & Er).
      destruct (asep_closed_frontier I s s' Hclosed Hok HI Hfront) as [Hok' HI'].
      exists r, (as_global s'); split; [exact HTr|]; left.
      exists s'; split; [etransitivity; [symmetry; exact Er|exact Eq]|].
      split; [reflexivity|]; apply asep_at_intro; [exact Hok'|exact HI'|exact Hpost|].
      cbn [other] in Ef, Ew; rewrite Ew; eapply asep_pred_transport;
        [exact HQ|symmetry; exact Ef|exact (proj1 HPar)].
    + destruct (asep_enc_ready s Parent Q Q' Hok Hready HQ' HPar)
        as (s' & q & Hfront & HT & Eq & Hpost & Ef & Ew).
      destruct (ktrans_semiproper _ _ _ _ _ (symmetry Et) HT) as (r & HTr & Er).
      destruct (asep_closed_frontier I s s' Hclosed Hok HI Hfront) as [Hok' HI'].
      exists r, (as_global s'); split; [exact HTr|]; right.
      exists s'; split; [etransitivity; [symmetry; exact Er|exact Eq]|].
      split; [reflexivity|]; apply asep_at_intro; [exact Hok'|exact HI'| |exact Hpost].
      cbn [other] in Ef, Ew; rewrite Ew; eapply asep_pred_transport;
        [exact HP|symmetry; exact Ef|exact (proj1 HC)].
Qed.

(** Next with a true guard still advances only one lineage on the shared run. *)
Corollary asep_ax_compose (I : AsepState -> Prop) (P Q : AsepPred) t w :
  asep_closed I -> asep_pred_ok P -> asep_pred_ok Q ->
  asep_sat I
    (anc (entails (SSig * unit) false (CNow (fun _ => True))) P)
    (anc (entails (SSig * unit) false (CNow (fun _ => True))) Q) t w ->
  anc (entails (SSig * unit) false (CNow (fun _ => True)))
    (fun u v =>
      asep_sat I P (entails (SSig * unit) false (CNow (fun _ => True))) u v \/
      asep_sat I (entails (SSig * unit) false (CNow (fun _ => True))) Q u v) t w.
Proof.
  intros Hclosed HP HQ H.
  destruct (asep_anc_compose I
    (entails (SSig * unit) false (CNow (fun _ => True))) P
    (entails (SSig * unit) false (CNow (fun _ => True))) Q t w Hclosed
    (asep_pred_ok_entails (b:=false) _) HP
    (asep_pred_ok_entails (b:=false) _) HQ H) as (_ & Hcan & Hnext).
  split; [apply ticl_now; split; [constructor|eapply can_step_not_done; exact Hcan]|].
  split; assumption.
Qed.

Corollary asep_ex_compose (I : AsepState -> Prop) (P Q : AsepPred) t w :
  asep_closed I -> asep_pred_ok P -> asep_pred_ok Q ->
  asep_sat I
    (enc (entails (SSig * unit) false (CNow (fun _ => True))) P)
    (enc (entails (SSig * unit) false (CNow (fun _ => True))) Q) t w ->
  enc (entails (SSig * unit) false (CNow (fun _ => True)))
    (fun u v =>
      asep_sat I P (entails (SSig * unit) false (CNow (fun _ => True))) u v \/
      asep_sat I (entails (SSig * unit) false (CNow (fun _ => True))) Q u v) t w.
Proof.
  intros Hclosed HP HQ H.
  destruct (asep_enc_compose I
    (entails (SSig * unit) false (CNow (fun _ => True))) P
    (entails (SSig * unit) false (CNow (fun _ => True))) Q t w Hclosed
    (asep_pred_ok_entails (b:=false) _) HP
    (asep_pred_ok_entails (b:=false) _) HQ H) as (_ & u & v & HT & Hnext).
  split; [apply ticl_now; split; [constructor|]|exists u,v; auto].
  eapply can_step_not_done; exists u,v; exact HT.
Qed.

Theorem asep_agc_compose (I : AsepState -> Prop) (P Q : AsepPred) t w :
  asep_closed I -> asep_pred_ok P -> asep_pred_ok Q ->
  asep_sat I (agc P) (agc Q) t w -> agc (asep_sat I P Q) t w.
Proof.
  intros Hclosed HP HQ; revert t w.
  coinduction R CIH; intros t w H.
  apply asep_sat_inv in H as (s & Et & Ew & Hok & Hwf & HI & HC & HPar).
  pose proof HC as HCstep; pose proof HPar as HPstep; step in HCstep; step in HPstep.
  assert (Hnext : asep_sat I (anc P (agc P)) (anc Q (agc Q)) t w).
  { exists s; split; [exact Et|]; split; [exact Ew|].
    apply asep_at_intro; assumption. }
  destruct (asep_anc_compose I P (agc P) Q (agc Q) t w Hclosed
    HP (asep_pred_ok_agc P HP) HQ (asep_pred_ok_agc Q HQ) Hnext) as (Hnow & Hcan & _).
  split; [exact Hnow|]; split; [exact Hcan|].
  intros u v HT; subst w.
  destruct (ktrans_semiproper _ _ _ _ _ Et HT) as (q & Hq & Eu).
  pose proof (asep_anc_live s Child P (agc P) q v Hok HCstep
    (proj1 (asep_pred_ok_agc P HP)) Hq) as Hlive.
  destruct (asep_visible_forward_owner s q v Hok Hq Hlive)
    as (s' & r & i & Hfront & Eq & Ev & HTi & Er & Ef & Eworld).
  destruct (asep_closed_frontier I s s' Hclosed Hok HI Hfront) as [Hok' HI'].
  apply CIH; exists s'; split; [etransitivity; [exact Eu|exact Eq]|].
  split; [exact Ev|]; apply asep_at_intro; [exact Hok'|exact HI'| |];
    destruct i; cbn [other] in Ef, Eworld.
  - eapply asep_pred_transport; [apply asep_pred_ok_agc, HP|exact Er|].
    apply (proj2 (proj2 HCstep)), HTi.
  - rewrite Eworld; eapply asep_pred_transport;
      [apply asep_pred_ok_agc, HP|symmetry; exact Ef|exact HC].
  - rewrite Eworld; eapply asep_pred_transport;
      [apply asep_pred_ok_agc, HQ|symmetry; exact Ef|exact HPar].
  - eapply asep_pred_transport; [apply asep_pred_ok_agc, HQ|exact Er|].
    apply (proj2 (proj2 HPstep)), HTi.
Qed.

Definition asep_ret (I : AsepState -> Prop) (RC RP : AsepRet) : AsepRet :=
  fun r w => exists s,
    asep_state_ok s /\ I s /\ tp_size (oc_pool (as_cfg s)) = 0 /\
    owned_result_rel (joined_state (as_cfg s), tt) r /\ w = as_global s /\
    asep
      (state_obligation Child
        (fun c => RC (joined_state c, tt) (as_local s Child)) (as_cfg s))
      (state_obligation Parent
        (fun c => RP (joined_state c, tt) (as_local s Parent)) (as_cfg s))
      (joined_heap (as_cfg s)).

Definition asep_until_guard (I : AsepState -> Prop) (P Q : AsepPred)
    (RC RP : AsepRet) : AsepPred :=
  fun t w =>
    asep_sat I P Q t w \/
    asep_sat I (entails (SSig * unit) true (CRet RC)) Q t w \/
    asep_sat I P (entails (SSig * unit) true (CRet RP)) t w.

Lemma asep_ret_elim (I : AsepState -> Prop) (RC RP : AsepRet) st w :
  asep_ret I RC RP (st,tt) w -> exists s,
    asep_state_ok s /\ I s /\ tp_size (oc_pool (as_cfg s)) = 0 /\
    owned_wf (as_cfg s) /\ st = joined_state (as_cfg s) /\ w = as_global s /\
    RC (local_state Child (as_cfg s),tt) (as_local s Child) /\
    RP (local_state Parent (as_cfg s),tt) (as_local s Parent).
Proof.
  intros (s & Hok & HI & Ht & Hresult & Hw & Hsep).
  pose proof (proj1 (proj1 (proj1 Hok))) as Hwf.
  pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hd).
  unfold state_obligation, joined_heap in Hsep.
  apply (proj1 (asep_pinned _ _ _ _ Hd)) in Hsep as [HC HP].
  rewrite !owned_joined_state_project in HC, HP.
  assert (Es : st = joined_state (as_cfg s)).
  { destruct st as [h aux]; destruct Hresult as (_ & Ex & Eh).
    change ((oc_ctx (as_cfg s), global_count (as_cfg s)) = aux) in Ex.
    change (joined_heap (as_cfg s) ≈ h) in Eh.
    unfold joined_state; rewrite (managed_heap_ext _ _ Eh), Ex; reflexivity. }
  exists s; exact (conj Hok (conj HI (conj Ht (conj Hwf (conj Es (conj Hw (conj HC HP))))))).
Qed.

Lemma asep_ret_no_live R (t : AsepTree) w u v :
  entails (SSig * unit) true (CRet R) t w -> ktrans t w u v -> ~ not_done v.
Proof.
  intros (x & HR & _ & _ & Hnext) HT Hv.
  specialize (Hnext u v HT); inversion Hnext; subst; inversion Hv.
Qed.

Lemma asep_at_auc_ret_step (I : AsepState -> Prop) (P Q : AsepPred)
    (RC RP : AsepRet) (s : AsepState) (a : OwnedAction) (s' : AsepState) :
  asep_closed I -> asep_pred_ok P -> asep_pred_ok Q ->
  asep_at I (auc P (entails (SSig * unit) true (CRet RC)))
    (auc Q (entails (SSig * unit) true (CRet RP))) s ->
  asep_step s a s' ->
  asep_at I (auc P (entails (SSig * unit) true (CRet RC)))
    (auc Q (entails (SSig * unit) true (CRet RP))) s'.
Proof.
  intros Hclosed HP HQ H Hstep.
  apply asep_at_inv in H as (Hok & Hwf & HI & HC & HPar).
  pose proof (asep_state_ok_step _ _ _ Hok Hstep) as Hok'.
  assert (Hlocal : forall i A R, asep_pred_ok A ->
    auc A (entails (SSig * unit) true (CRet R))
      (owned_interp (project i (as_cfg s))) (as_local s i) ->
    auc A (entails (SSig * unit) true (CRet R))
      (owned_interp (project i (as_cfg s'))) (as_local s' i)).
  { intros i A R HA HU.
    destruct (asep_local_step_inv s a s' i Hok Hstep) as [(Et & Ew)|(u & HT & Eu)].
    - rewrite Ew; eapply asep_pred_transport;
        [apply asep_pred_ok_auc; [exact HA|apply asep_pred_ok_entails]|exact Et|exact HU].
    - destruct HU as [t w HR|t w (_ & _ & Hnext)].
      + exfalso; eapply asep_ret_no_live; [exact HR|exact HT|exact (proj2 (proj2 Hok') i)].
      + eapply asep_pred_transport;
          [apply asep_pred_ok_auc; [exact HA|apply asep_pred_ok_entails]|exact Eu|apply Hnext, HT]. }
  apply asep_at_intro.
  - exact Hok'.
  - exact (Hclosed s a s' Hok HI Hstep).
  - exact (Hlocal Child P RC HP HC).
  - exact (Hlocal Parent Q RP HQ HPar).
Qed.

Lemma asep_auc_ret_empty (c : OwnedCfg) (P : AsepPred) (R : AsepRet) w :
  erasable c -> tp_size (oc_pool c) = 0 -> asep_pred_ok P ->
  auc P (entails (SSig * unit) true (CRet R)) (owned_interp c) w ->
  entails (SSig * unit) true (CRet R) (owned_interp c) w.
Proof.
  intros He H0 HP HU.
  inversion HU as [t w0 HR|t w0 Hstep]; subst; [exact HR|].
  destruct Hstep as (HG & (u & v & HT) & Hnext).
  exfalso.
    assert (Hret : entails (SSig * unit) true (CRet (fun _ _ => True)) (owned_interp c) w).
    { rewrite (owned_interp_terminal c He H0); apply ret_ret;
        [exact (proj1 HP _ _ HG)|constructor]. }
    eapply asep_ret_no_live; [exact Hret|exact HT|].
    exact (asep_auc_live P (entails (SSig * unit) true (CRet R))
      HP (asep_pred_ok_entails (b := true) (CRet R)) u v (Hnext u v HT)).
Qed.

Lemma asep_ret_local_frontier c R w :
  erasable c -> entails (SSig * unit) true (CRet R) (owned_interp c) w ->
  exists d, clos_refl_trans _ silent_next c d /\ tp_size (oc_pool d) = 0.
Proof.
  intros He HR; pose proof HR as (x & _ & _ & Hcan & _).
  destruct (asep_can_step_frontier c w He Hcan)
    as [(u & v & HT & Hv)|Hdone]; [|exact Hdone].
  exfalso; eapply asep_ret_no_live; eauto.
Qed.

Lemma asep_ret_value R (x : SSig * unit) w :
  entails (SSig * unit) true (CRet R) (Ret x : AsepTree) w -> R x w.
Proof.
  intros (r & HR & _ & (u & v & HT) & Hall).
  specialize (Hall u v HT); apply done_of_eq in Hall.
  assert (Hd : done_eq r v).
  { eapply done_with_mono; [|exact Hall]; intros y p (E & _); exact E. }
  destruct (ktrans_done_eq_inv _ _ _ _ _ HT Hd) as (Hval & _).
  apply trans_ret_inv in Hval as (_ & Hval).
  apply val_eq_inv in Hval; subst r; exact HR.
Qed.

Lemma asep_ret_empty c R w :
  erasable c -> tp_size (oc_pool c) = 0 ->
  entails (SSig * unit) true (CRet R) (owned_interp c) w ->
  R (joined_state c,tt) w.
Proof.
  intros He H0 HR; apply (asep_ret_value R (joined_state c,tt) w).
  rewrite <- (owned_interp_terminal c He H0); exact HR.
Qed.

Lemma asep_ret_unfocused_empty c R w :
  erasable c -> tp_focus (oc_pool c) = None ->
  entails (SSig * unit) true (CRet R) (owned_interp c) w ->
  tp_size (oc_pool c) = 0.
Proof.
  intros He Hf HR; destruct (asep_ret_local_frontier c R w He HR) as (d & Hp & H0).
  rewrite (owned_silent_unfocused c d Hp Hf); exact H0.
Qed.

Lemma asep_ret_frontier (s : AsepState) (RC RP : AsepRet) :
  asep_state_ok s ->
  (entails (SSig * unit) true (CRet RC)
     (owned_interp (project Child (as_cfg s))) (as_local s Child) /\
   entails (SSig * unit) true (CRet RP)
     (owned_interp (project Parent (as_cfg s))) (as_local s Parent)) ->
  exists s', clos_refl_trans _ asep_silent s s' /\
    as_global s' = as_global s /\ (forall i, as_local s' i = as_local s i) /\
    tp_size (oc_pool (as_cfg s')) = 0 /\
    owned_interp (as_cfg s) ~ (Ret (joined_state (as_cfg s'),tt) : AsepTree) /\
    RC (local_state Child (as_cfg s'),tt) (as_local s' Child) /\
    RP (local_state Parent (as_cfg s'),tt) (as_local s' Parent).
Proof.
  intros Hok Hpair; pose proof (proj1 Hok) as He.
  set (R := fun i : side => match i with Child => RC | Parent => RP end).
  assert (Hlocal : forall i, entails (SSig * unit) true (CRet (R i))
    (owned_interp (project i (as_cfg s))) (as_local s i)).
  { intros []; exact (proj1 Hpair) || exact (proj2 Hpair). }
  assert (Hend : exists s', clos_refl_trans _ asep_silent s s' /\
    tp_size (oc_pool (as_cfg s')) = 0).
  { destruct (tp_focus (oc_pool (as_cfg s))) as [j|] eqn:Hfocus.
    - set (i := Vector.nth (tp_tags (oc_pool (as_cfg s))) j).
      assert (Hi : Vector.nth (tp_tags (oc_pool (as_cfg s))) j = i) by reflexivity.
      assert (Hr : owned_side_ready i (as_cfg s)) by (right; exists j; auto).
      assert (Hfo : tp_focus (oc_pool (project (other i) (as_cfg s))) = None).
      { apply (project_focus_foreign (other i) (oc_pool (as_cfg s)) j Hfocus).
        rewrite Hi; destruct i; discriminate. }
      assert (Ho : tp_size (oc_pool (project (other i) (as_cfg s))) = 0).
      { eapply asep_ret_unfocused_empty;
          [eapply owned_active_local; exact He|exact Hfo|apply Hlocal]. }
      destruct (asep_ret_local_frontier _ (R i) _ (owned_active_local _ i He) (Hlocal i))
        as (d & Hp & H0).
      destruct (asep_local_terminal_lift s i d Hr Hp H0)
        as (s' & Hsil & Eg & El & Hempty & Hf & Eother).
      exists s'; split; [exact Hsil|].
      assert (Ho' : tp_size (oc_pool (project (other i) (as_cfg s'))) = 0).
      { rewrite (tp_equ_size _ _ (proj1 Eother)); exact Ho. }
      pose proof (project_size_partition (as_cfg s')) as Hpart.
      destruct i; cbn [other] in Ho'; rewrite Hempty, Ho' in Hpart; symmetry; exact Hpart.
    - assert (Hempty : forall i, tp_size (oc_pool (project i (as_cfg s))) = 0).
      { intro i; eapply asep_ret_unfocused_empty;
          [eapply owned_active_local; exact He|apply project_focus_none, Hfocus|apply Hlocal]. }
      exists s; split; [apply rt_refl|].
      pose proof (project_size_partition (as_cfg s)) as Hpart.
      rewrite (Hempty Child), (Hempty Parent) in Hpart; symmetry; exact Hpart. }
  destruct Hend as (s' & Hsil & Hempty).
  pose proof (asep_silent_cfg _ _ Hsil) as Hcfg.
  destruct (asep_silent_worlds _ _ Hsil) as (Eg & El).
  pose proof (proj1 (asep_closed_silent _ _ _ asep_closed_true Hok I Hsil)) as Hok'.
  pose proof (proj1 Hok') as He'.
  exists s'; split; [exact Hsil|]; split; [exact Eg|]; split; [exact El|].
  split; [exact Hempty|]; split.
  - etransitivity; [apply owned_interp_silent; [exact (proj1 He)|exact Hcfg]|].
    apply owned_interp_terminal; [exact (proj1 He')|exact Hempty].
  - assert (Hpost : forall i, R i (local_state i (as_cfg s'),tt) (as_local s' i)).
    { intro i; rewrite <- owned_joined_state_project; eapply asep_ret_empty.
      - eapply owned_active_local; exact He'.
      - apply project_size_terminal, Hempty.
      - rewrite <- (owned_silent_local _ _ i He Hcfg), El; apply Hlocal. }
    split; [exact (Hpost Child)|exact (Hpost Parent)].
Qed.

Theorem asep_ret_compose (I : AsepState -> Prop) (RC RP : AsepRet) t w :
  asep_closed I ->
  asep_sat I (entails (SSig * unit) true (CRet RC))
    (entails (SSig * unit) true (CRet RP)) t w ->
  entails (SSig * unit) true (CRet (asep_ret I RC RP)) t w.
Proof.
  intros Hclosed H.
  apply asep_sat_inv in H as (s & Et & -> & Hok & Hwf & HI & HC & HP).
  destruct (asep_ret_frontier s RC RP Hok (conj HC HP))
    as (s' & Hsil & Eg & El & H0 & Eret & HC' & HP').
  destruct (asep_closed_silent I s s' Hclosed Hok HI Hsil) as [Hok' HI'].
  rewrite Et, Eret; apply ret_ret; [exact (proj1 (proj2 Hok))|].
  exists s'; split; [exact Hok'|]; split; [exact HI'|]; split; [exact H0|]; split.
  - unfold owned_result_rel; repeat split; reflexivity.
  - split; [symmetry; exact Eg|].
    pose proof (proj1 (proj1 (proj1 Hok'))) as (_ & _ & _ & _ & _ & _ & _ & Hd).
    unfold state_obligation, joined_heap; apply (proj2 (asep_pinned _ _ _ _ Hd)).
    rewrite !owned_joined_state_project; split; assumption.
Qed.

Lemma asep_until_guard_proper (I : AsepState -> Prop)
    (P Q : AsepPred) (RC RP : AsepRet) :
  Proper (sbisim eq ==> eq ==> iff) (asep_until_guard I P Q RC RP).
Proof.
  intros t u E w v <-; unfold asep_until_guard.
  rewrite (proj2 (asep_sat_pred_ok I P Q) t u E w w eq_refl),
    (proj2 (asep_sat_pred_ok I (entails (SSig * unit) true (CRet RC)) Q) t u E w w eq_refl),
    (proj2 (asep_sat_pred_ok I P (entails (SSig * unit) true (CRet RP))) t u E w w eq_refl).
  reflexivity.
Qed.

Lemma asep_until_au_proper (I : AsepState -> Prop) (P Q : AsepPred) (RC RP : AsepRet) :
  Proper (sbisim eq ==> eq ==> iff)
    (auc (asep_until_guard I P Q RC RP)
      (entails (SSig * unit) true (CRet (asep_ret I RC RP)))).
Proof.
  intros t u E w v <-.
  exact (proper_au_equ (meq := sbisim eq)
    (HP := asep_until_guard_proper I P Q RC RP)
    (HQ := proj2 (asep_pred_ok_entails (b := true) (CRet (asep_ret I RC RP))))
    t u E w w eq_refl).
Qed.

Lemma asep_until_eu_proper (I : AsepState -> Prop) (P Q : AsepPred) (RC RP : AsepRet) :
  Proper (sbisim eq ==> eq ==> iff)
    (euc (asep_until_guard I P Q RC RP)
      (entails (SSig * unit) true (CRet (asep_ret I RC RP)))).
Proof.
  intros t u E w v <-.
  exact (proper_eu_equ (meq := sbisim eq)
    (HP := asep_until_guard_proper I P Q RC RP)
    (HQ := proj2 (asep_pred_ok_entails (b := true) (CRet (asep_ret I RC RP))))
    t u E w w eq_refl).
Qed.

Lemma asep_ret_can_step R (t : AsepTree) (w : AsepWorld) :
  entails (SSig * unit) true (CRet R) t w -> can_step t w.
Proof. intros (r & HR & Hnd & Hcan & _); exact Hcan. Qed.

Lemma asep_until_guard_live (I : AsepState -> Prop) (P Q : AsepPred) (RC RP : AsepRet) t w :
  asep_until_guard I P Q RC RP t w -> not_done w.
Proof.
  intros [H|[H|H]]; eapply (proj1 (asep_sat_pred_ok _ _ _)); exact H.
Qed.

(** The nested inductions decrease the Child and Parent AU derivations.
    Their current views carry the ordinary invariant through each frontier. *)
Lemma asep_until_auc (I : AsepState -> Prop) (P Q : AsepPred) (RC RP : AsepRet) :
  asep_closed I -> asep_pred_ok P -> asep_pred_ok Q ->
  forall s, asep_state_ok s -> I s ->
    auc P (entails (SSig * unit) true (CRet RC))
      (owned_interp (project Child (as_cfg s))) (as_local s Child) ->
    auc Q (entails (SSig * unit) true (CRet RP))
      (owned_interp (project Parent (as_cfg s))) (as_local s Parent) ->
    auc (asep_until_guard I P Q RC RP)
      (entails (SSig * unit) true (CRet (asep_ret I RC RP)))
      (owned_interp (as_cfg s)) (as_global s).
Proof.
  intros Hclosed HP HQ s0 Hok0 HI0 HC0 HP0.
  set (G := asep_until_guard I P Q RC RP).
  change (auc G
    (entails (SSig * unit) true (CRet (asep_ret I RC RP)))
    (owned_interp (as_cfg s0)) (as_global s0)).
  pose proof (asep_pred_ok_entails (b := true) (CRet RC)) as HRC.
  pose proof (asep_pred_ok_entails (b := true) (CRet RP)) as HRP.
  pose proof (asep_pred_ok_auc P _ HP HRC) as HAC.
  pose proof (asep_pred_ok_auc Q _ HQ HRP) as HAP.
  pose proof (asep_until_au_proper I P Q RC RP) as HAU.
  assert (Hmain : forall tc wc,
    auc P (entails (SSig * unit) true (CRet RC)) tc wc ->
    forall s, asep_state_ok s -> I s ->
      tc ~ owned_interp (project Child (as_cfg s)) ->
      wc = as_local s Child ->
      auc Q (entails (SSig * unit) true (CRet RP))
        (owned_interp (project Parent (as_cfg s))) (as_local s Parent) ->
      auc G (entails (SSig * unit) true (CRet (asep_ret I RC RP)))
        (owned_interp (as_cfg s)) (as_global s)).
  { refine (auc_ind (fun tc wc => _) _ _).
    - intros tc wc HC.
      assert (Hparent : forall tp wp,
        auc Q (entails (SSig * unit) true (CRet RP)) tp wp ->
        forall s, asep_state_ok s -> I s ->
          tc ~ owned_interp (project Child (as_cfg s)) ->
          wc = as_local s Child ->
          tp ~ owned_interp (project Parent (as_cfg s)) ->
          wp = as_local s Parent ->
          auc G (entails (SSig * unit) true (CRet (asep_ret I RC RP)))
            (owned_interp (as_cfg s)) (as_global s)).
      { refine (auc_ind (fun tp wp => _) _ _).
        + intros tp wp HPret s Hok HI EC EW EP EWp; subst wc wp.
          apply MatchA; eapply asep_ret_compose; [exact Hclosed|].
          apply asep_sat_intro; apply asep_at_intro; [exact Hok|exact HI| |]; eapply asep_pred_transport; eauto.
        + intros tp wp HPstep IHp s Hok HI EC EW EP EWp; subst wc wp.
          pose proof (proj1 (proj1 (proj1 Hok))) as Hwf.
          assert (HCz : entails (SSig * unit) true (CRet RC)
            (owned_interp (project Child (as_cfg s))) (as_local s Child)).
          { eapply asep_pred_transport; eauto. }
          pose proof (asep_pred_transport _ (asep_pred_ok_anc Q _ HQ HAP)
            _ _ _ EP HPstep) as HPz.
          apply StepA; split.
          * unfold G; right; left.
            apply asep_sat_intro; apply asep_at_intro; [exact Hok|exact HI| |]; [exact HCz|exact (proj1 HPz)].
          * split.
            -- eapply asep_progress;
                 [exact Hok|exact (asep_ret_can_step _ _ _ HCz)|
                  exact (proj1 (proj2 HPz))].
            -- intros u v HT.
               pose proof (asep_anc_live s Parent Q _ u v
                 Hok HPz (proj1 HAP) HT) as Hlive.
               destruct (asep_visible_forward_owner s u v
                 Hok HT Hlive)
                 as (s' & r & i & Hfront & Eu & Ev & Hmove & Er & Ef & Ewf).
               destruct (asep_closed_frontier I s s' Hclosed Hok HI Hfront) as [Hok' HI'].
               destruct i.
               ++ exfalso; eapply asep_ret_no_live; [exact HCz|exact Hmove|].
                  exact (proj2 (proj2 Hok') Child).
               ++ cbn [other] in Ef, Ewf.
                  rewrite Ev.
                  apply (proj2 (HAU u _ Eu _ _ eq_refl)).
                  destruct (ktrans_semiproper _ _ _ _ _ (symmetry EP) Hmove)
                    as (r' & Hr' & Er').
                  apply (proj2 (proj2 IHp) r' (as_local s' Parent) Hr' s').
                  ** exact Hok'.
                  ** exact HI'.
                  ** etransitivity; [exact EC|symmetry; exact Ef].
                  ** rewrite Ewf; reflexivity.
                  ** etransitivity; [symmetry; exact Er'|exact Er].
                  ** reflexivity. }
      intros s Hok HI EC EW HPz.
      eapply Hparent;
        [exact HPz|exact Hok|exact HI|exact EC|exact EW|reflexivity|reflexivity].
    - intros tc wc HCstep IHc.
      assert (Hparent : forall tp wp,
        auc Q (entails (SSig * unit) true (CRet RP)) tp wp ->
        forall s, asep_state_ok s -> I s ->
          tc ~ owned_interp (project Child (as_cfg s)) ->
          wc = as_local s Child ->
          tp ~ owned_interp (project Parent (as_cfg s)) ->
          wp = as_local s Parent ->
          auc G (entails (SSig * unit) true (CRet (asep_ret I RC RP)))
            (owned_interp (as_cfg s)) (as_global s)).
      { refine (auc_ind (fun tp wp => _) _ _).
        + intros tp wp HPret s Hok HI EC EW EP EWp; subst wc wp.
          pose proof (proj1 (proj1 (proj1 Hok))) as Hwf.
          pose proof (asep_pred_transport _ (asep_pred_ok_anc P _ HP HAC)
            _ _ _ EC HCstep) as HCz.
          assert (HPz : entails (SSig * unit) true (CRet RP)
            (owned_interp (project Parent (as_cfg s))) (as_local s Parent)).
          { eapply asep_pred_transport; eauto. }
          apply StepA; split.
          * unfold G; right; right.
            apply asep_sat_intro; apply asep_at_intro; [exact Hok|exact HI| |]; [exact (proj1 HCz)|exact HPz].
          * split.
            -- eapply asep_progress;
                 [exact Hok|exact (proj1 (proj2 HCz))|
                  exact (asep_ret_can_step _ _ _ HPz)].
            -- intros u v HT.
               pose proof (asep_anc_live s Child P _ u v
                 Hok HCz (proj1 HAC) HT) as Hlive.
               destruct (asep_visible_forward_owner s u v
                 Hok HT Hlive)
                 as (s' & r & i & Hfront & Eu & Ev & Hmove & Er & Ef & Ewf).
               destruct (asep_closed_frontier I s s' Hclosed Hok HI Hfront) as [Hok' HI'].
               destruct i.
               ++ cbn [other] in Ef, Ewf.
                  rewrite Ev.
                  apply (proj2 (HAU u _ Eu _ _ eq_refl)).
                  destruct (ktrans_semiproper _ _ _ _ _ (symmetry EC) Hmove)
                    as (r' & Hr' & Er').
                  apply (proj2 (proj2 IHc) r' (as_local s' Child) Hr' s').
                  ** exact Hok'.
                  ** exact HI'.
                  ** etransitivity; [symmetry; exact Er'|exact Er].
                  ** reflexivity.
                  ** apply MatchA; rewrite Ewf.
                     eapply asep_pred_transport; [exact HRP|symmetry; exact Ef|exact HPz].
               ++ exfalso; eapply asep_ret_no_live; [exact HPz|exact Hmove|].
                  exact (proj2 (proj2 Hok') Parent).
        + intros tp wp HPstep IHp s Hok HI EC EW EP EWp; subst wc wp.
          pose proof (proj1 (proj1 (proj1 Hok))) as Hwf.
          pose proof (asep_pred_transport _ (asep_pred_ok_anc P _ HP HAC)
            _ _ _ EC HCstep) as HCz.
          pose proof (asep_pred_transport _ (asep_pred_ok_anc Q _ HQ HAP)
            _ _ _ EP HPstep) as HPz.
          apply StepA; split.
          * unfold G; left.
            apply asep_sat_intro; apply asep_at_intro; [exact Hok|exact HI| |]; [exact (proj1 HCz)|exact (proj1 HPz)].
          * split.
            -- eapply asep_progress;
                 [exact Hok|exact (proj1 (proj2 HCz))|exact (proj1 (proj2 HPz))].
            -- intros u v HT.
               pose proof (asep_anc_live s Child P _ u v
                 Hok HCz (proj1 HAC) HT) as Hlive.
               destruct (asep_visible_forward_owner s u v
                 Hok HT Hlive)
                 as (s' & r & i & Hfront & Eu & Ev & Hmove & Er & Ef & Ewf).
               destruct (asep_closed_frontier I s s' Hclosed Hok HI Hfront) as [Hok' HI'].
               destruct i; cbn [other] in Ef, Ewf; rewrite Ev;
                 apply (proj2 (HAU u _ Eu _ _ eq_refl)).
               ++ destruct (ktrans_semiproper _ _ _ _ _ (symmetry EC) Hmove)
                    as (r' & Hr' & Er').
                  apply (proj2 (proj2 IHc) r' (as_local s' Child) Hr' s').
                  ** exact Hok'.
                  ** exact HI'.
                  ** etransitivity; [symmetry; exact Er'|exact Er].
                  ** reflexivity.
                  ** rewrite Ewf; eapply asep_pred_transport; [exact HAP|symmetry; exact Ef|].
                     apply StepA; exact HPz.
               ++ destruct (ktrans_semiproper _ _ _ _ _ (symmetry EP) Hmove)
                    as (r' & Hr' & Er').
                  apply (proj2 (proj2 IHp) r' (as_local s' Parent) Hr' s').
                  ** exact Hok'.
                  ** exact HI'.
                  ** etransitivity; [exact EC|symmetry; exact Ef].
                  ** rewrite Ewf; reflexivity.
                  ** etransitivity; [symmetry; exact Er'|exact Er].
                  ** reflexivity. }
      intros s Hok HI EC EW HPz.
      eapply Hparent;
        [exact HPz|exact Hok|exact HI|exact EC|exact EW|reflexivity|reflexivity]. }
  eapply Hmain;
    [exact HC0|exact Hok0|exact HI0|reflexivity|reflexivity|exact HP0].
Qed.

Theorem asep_auc_ret_compose (I : AsepState -> Prop) (P Q : AsepPred) (RC RP : AsepRet) t w :
  asep_closed I -> asep_pred_ok P -> asep_pred_ok Q ->
  asep_sat I (auc P (entails (SSig * unit) true (CRet RC)))
    (auc Q (entails (SSig * unit) true (CRet RP))) t w ->
  auc (asep_until_guard I P Q RC RP)
    (entails (SSig * unit) true (CRet (asep_ret I RC RP))) t w.
Proof.
  intros Hclosed HP HQ H.
  apply asep_sat_inv in H as (s & Et & -> & Hok & Hwf & HI & HC & HPar).
  apply (proj2 (asep_until_au_proper I P Q RC RP t _ Et _ _ eq_refl)).
  eapply asep_until_auc; eauto.
Qed.

(** Finite existential-until ranks count retained local raw transitions. *)
Fixpoint asep_euc_rank (P R : AsepPred) (n : nat) : AsepPred :=
  match n with
  | 0 => R
  | S k => enc P (asep_euc_rank P R k)
  end.

Lemma asep_euc_rank_ok P R n :
  asep_pred_ok P -> asep_pred_ok R -> asep_pred_ok (asep_euc_rank P R n).
Proof.
  intros HP HR; induction n; cbn; [exact HR|apply asep_pred_ok_enc; assumption].
Qed.

Lemma asep_euc_rank_exists P R t w :
  euc P R t w -> exists n, asep_euc_rank P R n t w.
Proof.
  revert t w; refine (euc_ind (fun t w => exists n, asep_euc_rank P R n t w) _ _).
  - intros t w HR; exists 0; exact HR.
  - intros t w (HP & u & v & HT & _ & n & Hn).
    exists (S n); split; [exact HP|]; exists u, v; auto.
Qed.

(** Focus release uses erased-silent owned actions without consuming a
    native return transition or changing either predecessor world. *)
Lemma asep_ret_release (s : AsepState) i R :
  asep_state_ok s ->
  entails (SSig * unit) true (CRet R)
    (owned_interp (project i (as_cfg s))) (as_local s i) ->
  exists s', clos_refl_trans _ asep_silent s s' /\
    as_global s' = as_global s /\ (forall j, as_local s' j = as_local s j) /\
    owned_side_ready (other i) (as_cfg s').
Proof.
  intros Hok HR; pose proof (proj1 Hok) as He.
  destruct (tp_focus (oc_pool (as_cfg s))) as [j|] eqn:Hf.
  - destruct (side_eq_dec (Vector.nth (tp_tags (oc_pool (as_cfg s))) j) i) as [Hi|Hi].
    + destruct (asep_ret_local_frontier _ R _ (owned_active_local _ i He) HR)
        as (d & Hd & H0).
      destruct (asep_local_terminal_lift s i d (or_intror (ex_intro _ j (conj Hf Hi))) Hd H0)
        as (s' & Hsil & Eg & El & _ & Hnone & _).
      exists s'; split; [exact Hsil|]; split; [exact Eg|]; split; [exact El|].
      left; exact Hnone.
    + exists s; split; [apply rt_refl|]; split; [reflexivity|]; split; [intro k; reflexivity|].
      right; exists j; split; [exact Hf|].
      destruct i, (Vector.nth (tp_tags (oc_pool (as_cfg s))) j); cbn [other] in *; congruence.
  - exists s; split; [apply rt_refl|]; split; [reflexivity|]; split; [intro k; reflexivity|].
    left; exact Hf.
Qed.

Lemma asep_until_eu_lift (I : AsepState -> Prop) (P Q : AsepPred) RC RP s i A R :
  asep_closed I -> asep_state_ok s -> I s ->
  asep_until_guard I P Q RC RP (owned_interp (as_cfg s)) (as_global s) ->
  owned_side_ready i (as_cfg s) -> asep_pred_ok R ->
  enc A R (owned_interp (project i (as_cfg s))) (as_local s i) ->
  (forall s', asep_state_ok s' -> I s' ->
    R (owned_interp (project i (as_cfg s'))) (as_local s' i) ->
    owned_interp (project (other i) (as_cfg s')) ~
      owned_interp (project (other i) (as_cfg s)) ->
    as_local s' (other i) = as_local s (other i) ->
    euc (asep_until_guard I P Q RC RP)
      (entails (SSig * unit) true (CRet (asep_ret I RC RP)))
      (owned_interp (as_cfg s')) (as_global s')) ->
  euc (asep_until_guard I P Q RC RP)
    (entails (SSig * unit) true (CRet (asep_ret I RC RP)))
    (owned_interp (as_cfg s)) (as_global s).
Proof.
  intros Hclosed Hok HI Hguard Hready HR Henc Hnext.
  destruct (asep_enc_ready s i A R Hok Hready HR Henc)
    as (s' & q & Hfront & Hq & Eq & Hpost & Ef & Ew).
  destruct (asep_closed_frontier I s s' Hclosed Hok HI Hfront) as [Hok' HI'].
  apply StepE; split; [exact Hguard|].
  exists q, (as_global s'); split; [exact Hq|].
  apply (proj2 (asep_until_eu_proper I P Q RC RP q _ Eq _ _ eq_refl)).
  apply Hnext; assumption.
Qed.

Lemma asep_until_euc_rank (I : AsepState -> Prop) (P Q : AsepPred) RC RP :
  asep_closed I -> asep_pred_ok P -> asep_pred_ok Q ->
  forall r s v, asep_state_ok v -> I v ->
    asep_euc_rank P (entails (SSig * unit) true (CRet RC)) r
      (owned_interp (project Child (as_cfg v))) (as_local v Child) ->
    asep_euc_rank Q (entails (SSig * unit) true (CRet RP)) s
      (owned_interp (project Parent (as_cfg v))) (as_local v Parent) ->
    euc (asep_until_guard I P Q RC RP)
      (entails (SSig * unit) true (CRet (asep_ret I RC RP)))
      (owned_interp (as_cfg v)) (as_global v).
Proof.
  intros Hclosed HP HQ.
  pose proof (asep_pred_ok_entails (b := true) (CRet RC)) as HRC.
  pose proof (asep_pred_ok_entails (b := true) (CRet RP)) as HRP.
  induction r as [|r IHr]; induction s as [|s IHs]; intros v Hok HI HC HPz.
  - apply MatchE; eapply asep_ret_compose; [exact Hclosed|].
    apply asep_sat_intro; apply asep_at_intro; assumption.
  - pose proof (proj1 Hok) as He.
    destruct (asep_ret_release v Child RC Hok HC)
      as (mid & Hsil & Eglobal & Elocal & Hready).
    destruct (asep_closed_silent I v mid Hclosed Hok HI Hsil) as [Hokm HIm].
    pose proof (owned_interp_silent _ _ (proj1 He) (asep_silent_cfg _ _ Hsil)) as Eg.
    assert (HCk : entails (SSig * unit) true (CRet RC)
      (owned_interp (project Child (as_cfg mid))) (as_local mid Child)).
    { rewrite (Elocal Child); eapply asep_pred_transport;
        [exact HRC|exact (owned_silent_local (as_cfg v) (as_cfg mid) Child He (asep_silent_cfg _ _ Hsil))|exact HC]. }
    assert (HPk : asep_euc_rank Q (entails (SSig * unit) true (CRet RP)) (S s)
      (owned_interp (project Parent (as_cfg mid))) (as_local mid Parent)).
    { rewrite (Elocal Parent); eapply asep_pred_transport;
        [apply asep_euc_rank_ok; assumption|exact (owned_silent_local (as_cfg v) (as_cfg mid) Parent He (asep_silent_cfg _ _ Hsil))|exact HPz]. }
    rewrite <- Eglobal.
    apply (proj2 (asep_until_eu_proper I P Q RC RP _ _ Eg _ _ eq_refl)).
    eapply (asep_until_eu_lift I P Q RC RP mid Parent Q
      (asep_euc_rank Q (entails (SSig * unit) true (CRet RP)) s)).
    + exact Hclosed.
    + exact Hokm.
    + exact HIm.
    + right; left; apply asep_sat_intro; apply asep_at_intro; [exact Hokm|exact HIm| |]; [exact HCk|exact (proj1 HPk)].
    + exact Hready.
    + apply asep_euc_rank_ok; assumption.
    + exact HPk.
    + intros v' Hok' HI' Hpost Ef Ew; cbn [other] in Ef, Ew.
      apply IHs; [exact Hok'|exact HI'| |exact Hpost].
      cbn; rewrite Ew; eapply asep_pred_transport;
        [exact HRC|symmetry; exact Ef|exact HCk].
  - pose proof (proj1 Hok) as He.
    destruct (asep_ret_release v Parent RP Hok HPz)
      as (mid & Hsil & Eglobal & Elocal & Hready).
    destruct (asep_closed_silent I v mid Hclosed Hok HI Hsil) as [Hokm HIm].
    pose proof (owned_interp_silent _ _ (proj1 He) (asep_silent_cfg _ _ Hsil)) as Eg.
    assert (HCk : asep_euc_rank P (entails (SSig * unit) true (CRet RC)) (S r)
      (owned_interp (project Child (as_cfg mid))) (as_local mid Child)).
    { rewrite (Elocal Child); eapply asep_pred_transport;
        [apply asep_euc_rank_ok; assumption|exact (owned_silent_local (as_cfg v) (as_cfg mid) Child He (asep_silent_cfg _ _ Hsil))|exact HC]. }
    assert (HPk : entails (SSig * unit) true (CRet RP)
      (owned_interp (project Parent (as_cfg mid))) (as_local mid Parent)).
    { rewrite (Elocal Parent); eapply asep_pred_transport;
        [exact HRP|exact (owned_silent_local (as_cfg v) (as_cfg mid) Parent He (asep_silent_cfg _ _ Hsil))|exact HPz]. }
    rewrite <- Eglobal.
    apply (proj2 (asep_until_eu_proper I P Q RC RP _ _ Eg _ _ eq_refl)).
    eapply (asep_until_eu_lift I P Q RC RP mid Child P
      (asep_euc_rank P (entails (SSig * unit) true (CRet RC)) r)).
    + exact Hclosed.
    + exact Hokm.
    + exact HIm.
    + right; right; apply asep_sat_intro; apply asep_at_intro; [exact Hokm|exact HIm| |]; [exact (proj1 HCk)|exact HPk].
    + exact Hready.
    + apply asep_euc_rank_ok; assumption.
    + exact HCk.
    + intros v' Hok' HI' Hpost Ef Ew; cbn [other] in Ef, Ew.
      apply (IHr 0); [exact Hok'|exact HI'|exact Hpost|].
      cbn; rewrite Ew; eapply asep_pred_transport;
        [exact HRP|symmetry; exact Ef|exact HPk].
  - assert (Hready : exists i, owned_side_ready i (as_cfg v)).
    { destruct (tp_focus (oc_pool (as_cfg v))) as [j|] eqn:Hf.
      - exists (Vector.nth (tp_tags (oc_pool (as_cfg v))) j); right; exists j; auto.
      - exists Child; left; exact Hf. }
    destruct Hready as ([|] & Hready).
    + eapply (asep_until_eu_lift I P Q RC RP v Child P
        (asep_euc_rank P (entails (SSig * unit) true (CRet RC)) r)).
      * exact Hclosed.
      * exact Hok.
      * exact HI.
      * left; apply asep_sat_intro; apply asep_at_intro; [exact Hok|exact HI| |]; [exact (proj1 HC)|exact (proj1 HPz)].
      * exact Hready.
      * apply asep_euc_rank_ok; assumption.
      * exact HC.
      * intros v' Hok' HI' Hpost Ef Ew; cbn [other] in Ef, Ew.
        apply (IHr (S s)); [exact Hok'|exact HI'|exact Hpost|].
        rewrite Ew; eapply asep_pred_transport;
          [apply asep_euc_rank_ok; assumption|symmetry; exact Ef|exact HPz].
    + eapply (asep_until_eu_lift I P Q RC RP v Parent Q
        (asep_euc_rank Q (entails (SSig * unit) true (CRet RP)) s)).
      * exact Hclosed.
      * exact Hok.
      * exact HI.
      * left; apply asep_sat_intro; apply asep_at_intro; [exact Hok|exact HI| |]; [exact (proj1 HC)|exact (proj1 HPz)].
      * exact Hready.
      * apply asep_euc_rank_ok; assumption.
      * exact HPz.
      * intros v' Hok' HI' Hpost Ef Ew; cbn [other] in Ef, Ew.
        apply IHs; [exact Hok'|exact HI'| |exact Hpost].
        rewrite Ew; eapply asep_pred_transport;
          [apply asep_euc_rank_ok; assumption|symmetry; exact Ef|exact HC].
Qed.

Theorem asep_euc_ret_compose (I : AsepState -> Prop) (P Q : AsepPred) RC RP t w :
  asep_closed I -> asep_pred_ok P -> asep_pred_ok Q ->
  asep_sat I (euc P (entails (SSig * unit) true (CRet RC)))
    (euc Q (entails (SSig * unit) true (CRet RP))) t w ->
  euc (asep_until_guard I P Q RC RP)
    (entails (SSig * unit) true (CRet (asep_ret I RC RP))) t w.
Proof.
  intros Hclosed HP HQ H.
  apply asep_sat_inv in H as (v & Et & -> & Hok & Hwf & HI & HC & HPar).
  destruct (asep_euc_rank_exists _ _ _ _ HC) as (r & Hr).
  destruct (asep_euc_rank_exists _ _ _ _ HPar) as (s & Hs).
  apply (proj2 (asep_until_eu_proper I P Q RC RP t _ Et _ _ eq_refl)).
  exact (asep_until_euc_rank I P Q RC RP Hclosed HP HQ r s v Hok HI Hr Hs).
Qed.

Corollary asep_af_ret_compose (I : AsepState -> Prop) (RC RP : AsepRet) t w :
  asep_closed I ->
  asep_sat I
    (entails (SSig * unit) true (Cu Q_A (CNow (fun _ => True)) (CRet RC)))
    (entails (SSig * unit) true (Cu Q_A (CNow (fun _ => True)) (CRet RP))) t w ->
  entails (SSig * unit) true
    (Cu Q_A (CNow (fun _ => True)) (CRet (asep_ret I RC RP))) t w.
Proof.
  intros Hclosed H; apply ticl_au.
  pose proof (asep_auc_ret_compose I
    (entails (SSig * unit) false (CNow (fun _ => True)))
    (entails (SSig * unit) false (CNow (fun _ => True))) RC RP t w Hclosed
    (asep_pred_ok_entails (b := false) _) (asep_pred_ok_entails (b := false) _) H) as HU.
  eapply auc_mono_l; [|exact HU].
  intros u v HG; apply ticl_now; split; [constructor|eapply asep_until_guard_live; exact HG].
Qed.

Corollary asep_ef_ret_compose (I : AsepState -> Prop) (RC RP : AsepRet) t w :
  asep_closed I ->
  asep_sat I
    (entails (SSig * unit) true (Cu Q_E (CNow (fun _ => True)) (CRet RC)))
    (entails (SSig * unit) true (Cu Q_E (CNow (fun _ => True)) (CRet RP))) t w ->
  entails (SSig * unit) true
    (Cu Q_E (CNow (fun _ => True)) (CRet (asep_ret I RC RP))) t w.
Proof.
  intros Hclosed H; apply ticl_eu.
  pose proof (asep_euc_ret_compose I
    (entails (SSig * unit) false (CNow (fun _ => True)))
    (entails (SSig * unit) false (CNow (fun _ => True))) RC RP t w Hclosed
    (asep_pred_ok_entails (b := false) _) (asep_pred_ok_entails (b := false) _) H) as HU.
  eapply euc_mono_l; [|exact HU].
  intros u v HG; apply ticl_now; split; [constructor|eapply asep_until_guard_live; exact HG].
Qed.

Theorem asep_egc_run (I : AsepState -> Prop) (P Q : AsepPred)
    (s0 : AsepState) (e : Execution AsepState OwnedAction unit) :
  asep_pred_ok P -> asep_pred_ok Q ->
  execution_valid (fun a s (_ : unit) s' => asep_step s a s') (eq s0) e ->
  (forall n, asep_at I P Q (states e n)) ->
  (forall i, infinitely (fun n =>
    owner_visible i (as_cfg (states e n)) (selected e n)
      (as_cfg (states e (S n))))) ->
  egc (asep_sat I P Q) (owned_interp (as_cfg s0)) (as_global s0) /\
  asep_sat I (egc P) (egc Q) (owned_interp (as_cfg s0)) (as_global s0).
Proof.
  intros HP HQ [H0 Hrun] Hassn Hinf.
  assert (Hok : forall n, asep_state_ok (states e n)).
  { intro n; exact (proj1 (Hassn n)). }
  assert (Hpair : forall n,
    P (owned_interp (project Child (as_cfg (states e n)))) (as_local (states e n) Child) /\
    Q (owned_interp (project Parent (as_cfg (states e n)))) (as_local (states e n) Parent)).
  { intro n; pose proof (asep_at_inv I P Q (states e n) (Hassn n)) as H.
    exact (proj2 (proj2 (proj2 H))). }
  assert (Hdec : forall i n,
    {owner_visible i (as_cfg (states e n)) (selected e n) (as_cfg (states e (S n)))} +
    {~ owner_visible i (as_cfg (states e n)) (selected e n) (as_cfg (states e (S n)))}).
  { intros i n; unfold owner_visible.
    destruct (side_eq_dec (owner (selected e n)) i);
      destruct (erase_action_label (selected e n) (joined_heap (as_cfg (states e (S n)))));
      [left|right|right|right]; intuition discriminate. }
  assert (Hlocal : forall i, egc (match i with Child => P | Parent => Q end)
    (owned_interp (project i (as_cfg s0))) (as_local s0 i)).
  { intro i; rewrite H0.
    unshelve eapply (egc_of_sequence
      (fun n => owned_interp (project i (as_cfg (states e n))))
      (fun n => as_local (states e n) i)
      (fun n => owner_visible i (as_cfg (states e n)) (selected e n) (as_cfg (states e (S n))))
      (match i with Child => P | Parent => Q end) _ _ _ _ _ _ 0).
    - apply Hdec.
    - apply Hinf.
    - intro n; destruct i; [exact (proj1 (Hpair n))|exact (proj2 (Hpair n))].
    - destruct i; [exact (proj2 HP)|exact (proj2 HQ)].
    - intros n Hn; eapply asep_invisible; [apply Hok|apply Hrun|exact Hn].
    - intros n [Ho Hv].
      destruct (owned_owner_ktrans _ _ _ i (as_local (states e n) i)
        (proj1 (Hok n)) (proj1 (Hrun n)) Ho Hv (proj2 (proj2 (Hok n)) i)) as (u & Hu & Eu).
      exists u; split; [|exact Eu].
      rewrite (proj2 (Hrun n)); cbn [asep_advance as_global as_local as_cfg];
        rewrite (proj2 (side_eqb_spec _ _) Ho); exact Hu. }
  split.
  - rewrite H0.
    unshelve eapply (egc_of_sequence
      (fun n => owned_interp (as_cfg (states e n)))
      (fun n => as_global (states e n))
      (fun n => erase_action_label (selected e n) (joined_heap (as_cfg (states e (S n)))) <> None)
      (asep_sat I P Q) _ _ _ _ _ _ 0).
    + intro n; cbn beta; destruct (erase_action_label (selected e n)
        (joined_heap (as_cfg (states e (S n))))); [left; discriminate|right; tauto].
    + intro n; destruct (Hinf Child n) as (m & Hm & _ & Hv); exists m; auto.
    + intro n; apply asep_sat_intro, Hassn.
    + exact (proj2 (asep_sat_pred_ok I P Q)).
    + intros n Hn; cbn beta in Hn.
      assert (Hnone : erase_action_label (selected e n)
        (joined_heap (as_cfg (states e (S n)))) = None).
      { destruct (erase_action_label (selected e n)
          (joined_heap (as_cfg (states e (S n))))) eqn:E; [|reflexivity].
        exfalso; apply Hn; discriminate. }
      split.
      * apply owned_interp_silent; [exact (proj1 (proj1 (Hok n)))|].
        apply rt_step; exists (selected e n); split; [exact (proj1 (Hrun n))|exact Hnone].
      * rewrite (proj2 (Hrun n)); cbn [asep_advance as_global as_local as_cfg]; unfold action_logs; rewrite Hnone; reflexivity.
    + intros n Hv; cbn beta in Hv.
      destruct (erase_action_label (selected e n)
        (joined_heap (as_cfg (states e (S n))))) as [l|] eqn:Hl; [|contradiction].
      destruct (owned_interp_visible (as_cfg (states e n)) (as_cfg (states e n)) (selected e n)
        (as_cfg (states e (S n))) l (proj1 (proj1 (Hok n))) (rt_refl _ _ _)
        (proj1 (Hrun n)) Hl) as (u & Hu & Eu).
      exists u; split; [|exact Eu].
      rewrite (proj2 (Hrun n)); cbn [asep_advance as_global as_local as_cfg]; eapply owned_label_ktrans;
        [exact Hl|exact Hu|exact (proj1 (proj2 (Hok n)))].
  - apply asep_sat_intro, asep_at_intro.
    + rewrite H0; apply Hok.
    + rewrite H0; exact (proj1 (proj2 (Hassn 0))).
    + exact (Hlocal Child).
    + exact (Hlocal Parent).
Qed.
