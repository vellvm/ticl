From Stdlib Require Import List Lia.
From Coinduction Require Import all.
From TICL Require Export CTree.Trace.
From TICL Require Import
  CTree.Core
  CTree.Events.Writer
  CTree.Logic.Trans
  CTree.Logic.CanStep
  CTree.Logic.Sim
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.AG
  CTree.Logic.Bind
  CTree.Logic.Iter
  Logic.Core.

Unset Implicit Arguments.
Import CTree CTreeNotations TiclNotations ListNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.
Local Typeclasses Transparent equ sbisim.


(** A visible scheduler step is productive but preserves the observation
    world.  Iterating only these steps never creates a visible event. *)
Lemma ag_step_family {E B : Type -> Type} {I X : Type}
  (family : I -> ctree E B X) (next : I -> I)
  (Hstep : forall i, family i ~ Step (family (next i))) :
  forall i w, not_done w -> <( {family i}, w |=L AG ⊤ )>.
Proof.
  setoid_rewrite unfold_entails_ag.
  coinduction R CIH; intros i w Hw.
  rewrite Hstep; split; [apply ticl_now; split; [constructor|exact Hw]|].
  split; [apply can_step_step; exact Hw|].
  intros t' w' HT; apply ktrans_step in HT as (Et & -> & _).
  rewrite Et; apply CIH; exact Hw.
Qed.

Lemma step_family_no_ef_visible {W : Type} {B : Type -> Type} {I X : Type}
  (family : I -> ctreeW W B X) (next : I -> I)
  (Hstep : forall i, family i ~ Step (family (next i))) (P : W -> Prop) :
  forall i, ~ <( {family i}, Pure |=L EF visW {P} )>.
Proof.
  intros i HE; ticl_normalize in HE.
  assert (H : forall (t : ctreeW W B X) w,
    euc (entails X false <( ⊤ )>)
      (entails X false <( visW {P} )>) t w ->
    forall j, t ~ family j -> w = Pure -> False).
  { apply (euc_ind (fun t w => forall j, t ~ family j -> w = Pure -> False)).
    - intros t w Hv j Et ->; apply ticl_vis in Hv; inversion Hv.
    - intros t w (_ & t' & w' & HT & _ & IH) j Et ->.
      assert (E : t ~ Step (family (next j))) by (rewrite Et, Hstep; reflexivity).
      destruct (ktrans_semiproper _ _ _ _ _ E HT) as (u & HU & Erel).
      apply ktrans_step in HU as (Eu & <- & _).
      eapply IH; [rewrite Erel, Eu; reflexivity|reflexivity]. }
  eapply H; [exact HE|reflexivity|reflexivity].
Qed.

(** Logged scheduler families remain productive while changing the world. *)
Lemma ag_log_family {W : Type} {B : Type -> Type} {I X : Type}
  (family : I -> ctreeW W B X) (next : I -> I) (pick : I -> W)
  (Hlog : forall i, family i ~ Vis (Log (pick i)) (fun _ => family (next i))) :
  forall i w, not_done w -> <( {family i}, w |=L AG ⊤ )>.
Proof.
  setoid_rewrite unfold_entails_ag.
  coinduction R CIH; intros i w Hw.
  rewrite Hlog; split; [apply ticl_now; split; [constructor|exact Hw]|].
  split; [apply can_step_vis; [exact tt|exact Hw]|].
  intros t' w' HT; apply ktrans_vis in HT as ([] & -> & Et & _).
  rewrite <- Et; apply CIH; constructor.
Qed.

(** A family logging only rejected payloads cannot reach a matching event. *)
Lemma log_family_no_ef_visible {W : Type} {B : Type -> Type} {I X : Type}
  (family : I -> ctreeW W B X) (next : I -> I) (pick : I -> W)
  (Hlog : forall i, family i ~ Vis (Log (pick i)) (fun _ => family (next i)))
  (P : W -> Prop) (Hreject : forall i, ~ P (pick i)) :
  forall i, ~ <( {family i}, Pure |=L EF visW {P} )>.
Proof.
  intros i HE; ticl_normalize in HE.
  assert (H : forall (t : ctreeW W B X) w,
    euc (entails X false <( ⊤ )>)
      (entails X false <( visW {P} )>) t w ->
    forall j, t ~ family j ->
      (w = Pure \/ exists k, w = Obs (Log (pick k)) tt) -> False).
  { apply (euc_ind (fun t w => forall j, t ~ family j ->
      (w = Pure \/ exists k, w = Obs (Log (pick k)) tt) -> False)).
    - intros t w Hv j Et [->|(k & ->)]; apply ticl_vis in Hv;
        dependent destruction Hv; cbn in *; eapply Hreject; eassumption.
    - intros t w (_ & t' & w' & HT & _ & IH) j Et Hw.
      assert (E : t ~ Vis (Log (pick j)) (fun _ => family (next j)))
        by (rewrite Et, Hlog; reflexivity).
      destruct (ktrans_semiproper _ _ _ _ _ E HT) as (u & HU & Erel).
      apply ktrans_vis in HU as ([] & -> & Eu & _).
      eapply IH; [rewrite Erel, <- Eu; reflexivity|].
      right; exists j; reflexivity. }
  eapply H; [exact HE|reflexivity|now left].
Qed.
(** Productive universal recurrence of actual transition labels. *)
Unset Elimination Schemes.
Inductive eventually_label {E B : Type -> Type} {X : Type}
    (P : @label E -> Prop) : ctree E B X -> Prop :=
| eventually_label_intro t :
    can_trans t ->
    (forall l u, trans l t u -> P l \/ eventually_label P u) ->
    eventually_label P t.
Set Elimination Schemes.

Definition eventually_label_ind :
  forall {E B : Type -> Type} {X : Type}
    (P : @label E -> Prop) (R : ctree E B X -> Prop),
    (forall t, can_trans t ->
      (forall l u, trans l t u ->
        P l \/ (eventually_label P u /\ R u)) -> R t) ->
    forall t, eventually_label P t -> R t :=
  fun E B X P R Hstep =>
  fix F t (H : eventually_label P t) {struct H} : R t :=
    match H with
    | @eventually_label_intro _ _ _ _ t0 Hcan Hnext =>
        Hstep t0 Hcan
          (fun l u HT =>
             match Hnext l u HT with
             | or_introl Hit => or_introl Hit
             | or_intror Continue =>
                 or_intror (conj Continue (F u Continue))
             end)
    end.

CoInductive recurrent_label {E B : Type -> Type} {X : Type}
    (P : @label E -> Prop) : ctree E B X -> Prop :=
| recurrent_label_intro t :
    eventually_label P t ->
    (forall l u, trans l t u -> recurrent_label P u) ->
    recurrent_label P t.

Definition log_label {W : Type} (P : W -> Prop)
    (l : @label (writerE W)) : Prop :=
  match l with
  | obs (Log o) _ => P o
  | _ => False
  end.

Lemma eventually_label_sbisim {E B : Type -> Type} {X : Type}
    (P : @label E -> Prop) (t u : ctree E B X) :
  t ~ u -> eventually_label P t -> eventually_label P u.
Proof.
  intros Heq H.
  refine (eventually_label_ind P
    (fun t => forall u, t ~ u -> eventually_label P u) _ t H u Heq).
  intros t0 Hcan Hnext u0 Heq0;
  rename t0 into source, u0 into target, Heq0 into Eeq; step in Eeq; destruct Eeq as [Hf Hb]; cbn in Hf, Hb.
  constructor.
  - destruct Hcan as (l & v & HT).
    destruct (Hf _ _ HT) as (l' & v' & HT' & Ev & <-).
    exists l, v'; exact HT'.
  - intros l v HT.
    destruct (Hb _ _ HT) as (l' & v' & HT' & Ev & <-).
    destruct (Hnext _ _ HT') as [Hit|[Htail IH]].
    + left; exact Hit.
    + right; apply IH; exact Ev.
Qed.

Lemma recurrent_label_sbisim {E B : Type -> Type} {X : Type}
    (P : @label E -> Prop) (t u : ctree E B X) :
  t ~ u -> recurrent_label P t -> recurrent_label P u.
Proof.
  revert t u; cofix CIH; intros t u Heq H.
  destruct H as [t Hhit Hnext]; constructor.
  - eapply eventually_label_sbisim; eassumption.
  - intros l v HT; step in Heq; destruct Heq as [_ Hb]; cbn in Hb.
    destruct (Hb _ _ HT) as (l' & v' & HT' & Ev & <-).
    eapply CIH; [exact Ev|eapply Hnext; exact HT'].
Qed.

(** A false remembered target forces a future matching label. *)
Lemma af_vis_eventually_label
    {W X : Type} {B : Type -> Type}
    (P Q : W -> Prop)
    (P_dec : forall o, {P o} + {~ P o})
    (Q_P : forall o, Q o -> P o)
    (t : ctreeW W B X) (w : World (writerE W)) :
  ~ <( t, w |=L visW {Q} )> ->
  <( t, w |=L AF visW {Q} )> ->
  eventually_label (log_label P) t.
Proof.
  intros Hfalse Haf.
  change (auc (entails X false <( ⊤ )>)
    (entails X false <( visW {Q} )>) t w) in Haf.
  revert Hfalse.
  refine (auc_ind
    (fun t w => ~ <( t, w |=L visW {Q} )> ->
      eventually_label (log_label P) t) _ _ t w Haf).
  - intros t0 w0 Hmatch Hfalse; contradiction.
  - intros t0 w0 (Htop & Hcan & Hnext) (_ & _ & IH) Hfalse.
    apply ticl_not_done in Htop.
    constructor.
    + destruct Hcan as (u & w' & HT).
      apply ktrans_trans in HT as (l & HT & _); exists l, u; exact HT.
    + intros l u HT; destruct l as [|Y e response|Y result].
      * right; apply (IH u w0); [apply KtransTau; assumption|exact Hfalse].
      * destruct e as [o]; destruct response.
        destruct (P_dec o) as [Hit|Hmiss].
        -- left; exact Hit.
        -- right; apply (IH u (Obs (Log o) tt)).
           ++ apply KtransObs; assumption.
           ++ intro H; apply ticl_vis in H; dependent destruction H.
              apply Hmiss, Q_P; assumption.
      * pose proof (trans_val_invT HT) as HXY; subst Y.
        exfalso; inversion Htop; subst.
        -- pose proof (Hnext u (Done result) (KtransDone _ _ _ HT)) as Hdone.
           change <( u, {Done result} |=L AF visW {Q} )> in Hdone;
           apply ticl_not_done in Hdone; inversion Hdone.
        -- pose proof (Hnext u (Finish e v result)
             (KtransFinish _ _ _ _ _ HT)) as Hdone.
           change <( u, {Finish e v result} |=L AF visW {Q} )> in Hdone;
           apply ticl_not_done in Hdone; inversion Hdone.
Qed.

(** Refresh proof-private targets at every continuation, including hits. *)
Theorem agaf_family_recurrent_label
    {W X : Type} {B : Type -> Type}
    (P : W -> Prop) (Q : nat -> W -> Prop)
    (P_dec : forall o, {P o} + {~ P o})
    (Q_P : forall k o, Q k o -> P o)
    (Q_separates : forall o, exists k, ~ Q k o)
    (t : ctreeW W B X) (w : World (writerE W)) :
  (forall k, <( t, w |=L AG (AF visW {Q k}) )>) ->
  recurrent_label (log_label P) t.
Proof.
  revert t w; cofix CIH; intros t w Hfamily.
  pose proof (ticl_not_done _ _ _ _ _ (Hfamily 0)) as Hlive.
  assert (Hcutoff : exists k, ~ <( t, w |=L visW {Q k} )>).
  { inversion Hlive; subst.
    - exists 0; intro H; apply ticl_vis in H; inversion H.
    - destruct e as [o]; destruct v.
      destruct (Q_separates o) as (k & Hmiss).
      exists k; intro H; apply ticl_vis in H; dependent destruction H.
      contradiction. }
  destruct Hcutoff as (k & Hfalse); constructor.
  - eapply af_vis_eventually_label; [exact P_dec|apply Q_P|exact Hfalse|].
    pose proof (Hfamily k) as H; step in H; destruct H as [Haf _]; exact Haf.
  - intros l u HT; destruct l as [|Y e response|Y result].
    + apply (CIH u w); intro k'.
      pose proof (Hfamily k') as H; step in H; destruct H as [_ [_ Hnext]].
      change (agc (entails X false <( AF visW {Q k'} )>) u w).
      apply Hnext, KtransTau; assumption.
    + apply (CIH u (Obs e response)); intro k'.
      pose proof (Hfamily k') as H; step in H; destruct H as [_ [_ Hnext]].
      change (agc (entails X false <( AF visW {Q k'} )>) u (Obs e response)).
      apply Hnext, KtransObs; assumption.
    + pose proof (trans_val_invT HT) as HXY; subst Y.
      exfalso; pose proof (Hfamily 0) as H; step in H; destruct H as [_ [_ Hnext]].
      inversion Hlive; subst.
      * pose proof (Hnext u (Done result) (KtransDone _ _ _ HT)) as Hdone.
        change <( u, {Done result} |=L AG (AF visW {Q 0}) )> in Hdone;
        apply ticl_not_done in Hdone; inversion Hdone.
      * pose proof (Hnext u (Finish e v result)
          (KtransFinish _ _ _ _ _ HT)) as Hdone.
        change <( u, {Finish e v result} |=L AG (AF visW {Q 0}) )> in Hdone;
        apply ticl_not_done in Hdone; inversion Hdone.
Qed.

(** * Temporal properties of finite observation prefixes. *)

Lemma f_emit_list {W : Type} {B : Type -> Type} {X : Type} {b : bool}
  (q : ticlq) (xs : list W) (t : ctreeW W B X) w
  (ψ : ticl_at (writerE W) X b) :
  not_done w ->
  entails X b (Cu q (CNow (fun _ => True)) ψ) t (after_logs xs w) ->
  entails X b (Cu q (CNow (fun _ => True)) ψ) (emit_list xs t) w.
Proof.
  revert w; induction xs as [|o rest IH]; intros w Hd H; [exact H|].
  change (entails X b (Cu q (CNow (fun _ => True)) ψ)
    (log o ;; emit_list rest t) w).
  destruct q; [apply (af_log (b:=b)) | apply (ef_log (b:=b))];
    [exact Hd | apply IH; [constructor|exact H] |
     exact Hd | apply IH; [constructor|exact H]].
Qed.

Lemma af_emit_list {W : Type} {B : Type -> Type} {X : Type} xs (t : ctreeW W B X) w P :
  not_done w ->
  <( t, {after_logs xs w} |=L AF visW {P} )> ->
  <( {emit_list xs t}, w |=L AF visW {P} )>.
Proof.
  apply (f_emit_list (b:=false) Q_A).
Qed.

Lemma agaf_emit_list {W : Type} {B : Type -> Type} {X : Type} xs (t : ctreeW W B X) w P :
  not_done w ->
  <( t, {after_logs xs w} |=L AG (AF visW {P}) )> ->
  <( {emit_list xs t}, w |=L AG (AF visW {P}) )>.
Proof.
  revert w; induction xs as [|o rest IH]; intros w Hd H; [exact H|].
  assert (Htail : <( {emit_list rest t}, {Obs (Log o) tt}
    |=L AG (AF visW {P}) )>).
  { apply IH; [constructor|exact H]. }
  assert (Haf : <( {emit_list rest t}, {Obs (Log o) tt} |=L AF visW {P} )>).
  { pose proof Htail as HH; cdestruct HH; assumption. }
  assert (Hprefix : <( {emit_list (o :: rest) t}, w |=L AF visW {P} )>).
  { change <( {log o ;; emit_list rest t}, w |=L AF visW {P} )>.
    apply (af_log (b:=false)); assumption. }
  change <( {log o ;; emit_list rest t}, w |=L AG (AF visW {P}) )>.
  apply (proj2 (ag_log_iff o (emit_list rest t) w _)); split.
  - exact Hprefix.
  - exact Htail.
Qed.

Lemma af_emit_list_member {W : Type} {B : Type -> Type} {X : Type} xs (t : ctreeW W B X) w P o :
  not_done w -> List.In o xs -> P o ->
  <( {emit_list xs t}, w |=L AF visW {P} )>.
Proof.
  revert w; induction xs as [|a rest IH]; intros w Hd Hin HP;
    [contradiction|].
  change <( {log a ;; emit_list rest t}, w |=L AF visW {P} )>.
  apply (af_log (b:=false)); [exact Hd|].
  destruct Hin as [<-|Hin].
  - cleft; apply ticl_vis; constructor; exact HP.
  - apply IH; [constructor|exact Hin|exact HP].
Qed.

Lemma af_emit_list_ret {W : Type} {B : Type -> Type} {X : Type} xs (r : X) w (Q : X -> World (writerE W) -> Prop) :
  not_done w -> Q r (after_logs xs w) ->
  <( {emit_list (B := B) xs (Ret r)}, w |=R AF ret {Q} )>.
Proof.
  intros Hd HQ; apply (f_emit_list (b:=true) Q_A); [exact Hd|].
  cleft; apply ret_ret; [apply after_logs_not_done; exact Hd|exact HQ].
Qed.

(** Removing a finite log prefix retains the complete nested formula on the
    actual tail at the final observation world. *)
Lemma ag_emit_list_suffix {W : Type} {B : Type -> Type} {X : Type}
  (xs : list W) (t : ctreeW W B X) w (φ : ticll (writerE W)) :
  <( {emit_list xs t}, w |=L AG φ )> ->
  <( t, {after_logs xs w} |=L AG φ )>.
Proof.
  revert w; induction xs as [|o rest IH]; intros w H; [exact H|].
  change <( {log o ;; emit_list rest t}, w |=L AG φ )> in H.
  apply (proj1 (ag_log_iff o (emit_list rest t) w φ)) in H as [_ Htail].
  exact (IH (Obs (Log o) tt) Htail).
Qed.

Lemma ag_emit_list_stuck {W : Type} {B : Type -> Type} {X : Type}
  (xs : list W) w (φ : ticll (writerE W)) :
  ~ <( {emit_list xs (Stuck : ctreeW W B X)}, w |=L AG φ )>.
Proof.
  intro H; eapply ag_stuck; eapply ag_emit_list_suffix; exact H.
Qed.

(** * Retained observations cannot masquerade as later ones.

    The world [Obs (Log (stamp a j)) tt] carries occurrence index [j], so it
    does not satisfy a freshness predicate bounded below by [S j]: an [AF] of
    that formula cannot be discharged by the world already in hand.  The
    payload [A] and the return type [X] are arbitrary. *)
Lemma indexed_excludes_retained {A : Type} {B : Type -> Type} {X : Type} (t : ctreeW (indexed A) B X) P a j :
  ~ <( t, {Obs (Log (stamp a j)) tt}
       |=L visW {indexed_after P (S j)} )>.
Proof.
  intro H; apply ticl_vis in H.
  dependent destruction H.
  destruct H as (_ & Hle); cbn in Hle; lia.
Qed.

(** * Recurrence for repeating finite observation batches.

    Derived structural rules over the one public log-loop representation
    [CTree.Trace.emit_batches]: [AF] by the existing [(u_iter_prefix_nat Q_A)], and
    [AG AF] by coinduction over every finite suffix of a batch. *)
Section EmitBatches.
  Context {W I X : Type} {B : Type -> Type}
    (batch : I -> list W) (next : I -> I)
    (Inv : I -> Prop) (rank : I -> nat) (P : W -> Prop)
    (Hnext : forall i, Inv i -> Inv (next i))
    (Hnonempty : forall i, Inv i -> batch i <> [])
    (Hprogress : forall i, Inv i ->
      (exists o, List.In o (batch i) /\ P o) \/ rank (next i) < rank i).

  Lemma emit_batches_af : forall i w, Inv i -> not_done w ->
    <( {(emit_batches batch next i : ctreeW W B X)}, {w} |=L AF visW {P} )>.
  Proof.
    intros i w Hi Hd; unfold emit_batches.
    eapply (u_iter_prefix_nat Q_A) with (Ri := fun j (_ : World (writerE W)) => Inv j)
      (f := fun j (_ : World (writerE W)) => rank j).
    - exact Hd.
    - exact Hi.
    - intros j v Hv Hj.
      destruct (Hprogress j Hj) as [(o & Hin & HP) | Hlt].
      + left; eapply af_emit_list_member; [exact Hv | exact Hin | exact HP].
      + right; apply af_emit_list_ret; [exact Hv |].
        exists (next j); split; [reflexivity |].
        split; [apply after_logs_not_done; exact Hv |].
        split; [apply Hnext; exact Hj | exact Hlt].
  Qed.

  (** The invariant is closed under suffixes: a tree is bisimilar to a
      remaining suffix of the current batch followed by the loop.  Each
      coinductive step is guarded by a real log, exposed either from the
      suffix itself or, when it is empty, from the next nonempty batch. *)
  Lemma emit_batches_agaf : forall i w, Inv i -> not_done w ->
    <( {(emit_batches batch next i : ctreeW W B X)}, {w} |=L AG (AF visW {P}) )>.
  Proof.
    intros i w Hi Hd.
    assert (Hsuffix : forall (t : ctreeW W B X) v,
      (exists j suffix, Inv j /\ not_done v /\
        t ~ emit_list suffix (emit_batches batch next j : ctreeW W B X)) ->
      <( t, v |=L AG (AF visW {P}) )>).
    { coinduction R CIH; intros t v (j & suffix & Hj & Hv & Ht).
      assert (Haf : <( t, v |=L AF visW {P} )>).
      { ticl_normalize; rewrite Ht; apply af_emit_list; [exact Hv|].
        apply emit_batches_af; [exact Hj|apply after_logs_not_done; exact Hv]. }
      assert (Hexp : exists o rest j', Inv j' /\
        t ~ emit_list (o :: rest) (emit_batches batch next j' : ctreeW W B X)).
      { destruct suffix as [|o rest].
        - destruct (batch j) as [|o rest] eqn:Eb; [exfalso; exact (Hnonempty j Hj Eb)|].
          exists o, rest, (next j); split; [apply Hnext, Hj|].
          rewrite Ht; cbn [emit_list fold_right].
          rewrite emit_batches_unfold_sbisim, Eb; reflexivity.
        - exists o, rest, j; split; [exact Hj|exact Ht]. }
      destruct Hexp as (o & rest & j' & Hj' & Ht').
      rewrite Ht', emit_list_cons.
      ticl_normalize in Haf;
      rewrite Ht', emit_list_cons in Haf.
      split; [exact Haf|]; split.
      - apply can_step_vis; [exact tt|exact Hv].
      - intros t' w' Htr.
        apply ktrans_vis in Htr as ([] & -> & Heq & _).
        rewrite <- Heq; apply CIH; exists j', rest; split; [exact Hj'|].
        split; [constructor|reflexivity]. }
    apply Hsuffix; exists i, []; split; [exact Hi|]; split; [exact Hd|reflexivity].
  Qed.
End EmitBatches.
