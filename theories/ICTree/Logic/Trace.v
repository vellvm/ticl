From Stdlib Require Import List Lia.
From Coinduction Require Import coinduction.
From TICL Require Export ICTree.Trace.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Events.Writer
  ICTree.Logic.Trans ICTree.Logic.CanStep ICTree.Logic.AX ICTree.Logic.AF
  ICTree.Logic.AG ICTree.Logic.Bind ICTree.Logic.Iter Logic.Core.

Unset Implicit Arguments.
Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.
Local Typeclasses Transparent equ sbisim.

(** * Temporal properties of finite observation prefixes. *)

Lemma af_emit_list {W X} xs (t : ictreeW W X) w P :
  not_done w ->
  <( t, {after_logs xs w} |= AF visW {P} )> ->
  <( {emit_list xs t}, w |= AF visW {P} )>.
Proof.
  revert w; induction xs as [|o rest IH]; intros w Hd H; [exact H|].
  change <( {log o ;; emit_list rest t}, w |= AF visW {P} )>.
  apply afl_log; [exact Hd|].
  apply IH; [constructor|exact H].
Qed.

Lemma agaf_emit_list {W X} xs (t : ictreeW W X) w P :
  not_done w ->
  <( t, {after_logs xs w} |= AG (AF visW {P}) )> ->
  <( {emit_list xs t}, w |= AG (AF visW {P}) )>.
Proof.
  revert w; induction xs as [|o rest IH]; intros w Hd H; [exact H|].
  assert (Htail : <( {emit_list rest t}, {Obs (Log o) tt}
    |= AG (AF visW {P}) )>).
  { apply IH; [constructor|exact H]. }
  assert (Haf : <( {emit_list rest t}, {Obs (Log o) tt} |= AF visW {P} )>).
  { pose proof Htail as HH; cdestruct HH; assumption. }
  assert (Hprefix : <( {emit_list (o :: rest) t}, w |= AF visW {P} )>).
  { change <( {log o ;; emit_list rest t}, w |= AF visW {P} )>.
    apply afl_log; assumption. }
  change <( {log o ;; emit_list rest t}, w |= AG (AF visW {P}) )>.
  apply (proj2 (ag_log_iff o (emit_list rest t) w _)); split.
  - exact Hprefix.
  - exact Htail.
Qed.

Lemma af_emit_list_member {W X} xs (t : ictreeW W X) w P o :
  not_done w -> List.In o xs -> P o ->
  <( {emit_list xs t}, w |= AF visW {P} )>.
Proof.
  revert w; induction xs as [|a rest IH]; intros w Hd Hin HP;
    [contradiction|].
  change <( {log a ;; emit_list rest t}, w |= AF visW {P} )>.
  apply afl_log; [exact Hd|].
  destruct Hin as [<-|Hin].
  - cleft; apply ticll_vis; constructor; exact HP.
  - apply IH; [constructor|exact Hin|exact HP].
Qed.

Lemma af_emit_list_ret {W X} xs (r : X) w (Q : X -> World (writerE W) -> Prop) :
  not_done w -> Q r (after_logs xs w) ->
  <[ {emit_list xs (Ret r)}, w |= AF AX done {Q} ]>.
Proof.
  revert w; induction xs as [|o rest IH]; intros w Hd HQ.
  - cleft; apply axr_ret; assumption.
  - change <[ {log o ;; emit_list rest (Ret r)}, w |= AF AX done {Q} ]>.
    apply afr_log; [exact Hd|].
    apply IH; [constructor|exact HQ].
Qed.

(** * Retained observations cannot masquerade as later ones.

    The world [Obs (Log (stamp a j)) tt] carries occurrence index [j], so it
    does not satisfy a freshness predicate bounded below by [S j]: an [AF] of
    that formula cannot be discharged by the world already in hand.  The
    payload [A] and the return type [X] are arbitrary. *)
Lemma indexed_excludes_retained {A X} (t : ictreeW (indexed A) X) P a j :
  ~ <( t, {Obs (Log (stamp a j)) tt}
       |= visW {indexed_after P (S j)} )>.
Proof.
  intro H; apply ticll_vis in H.
  inversion H as [e0 v0 Hphi Heq]; subst.
  destruct v0; destruct Hphi as (_ & Hle); cbn in Hle; lia.
Qed.

(** * Recurrence for repeating finite observation batches.

    Derived structural rules over the one public log-loop representation
    [ICTree.Trace.emit_batches]: [AF] by the existing [aul_iter_nat], and
    [AG AF] by coinduction over every finite suffix of a batch. *)
Section EmitBatches.
  Context {W I X : Type}
    (batch : I -> list W) (next : I -> I)
    (Inv : I -> Prop) (rank : I -> nat) (P : W -> Prop)
    (Hnext : forall i, Inv i -> Inv (next i))
    (Hnonempty : forall i, Inv i -> batch i <> [])
    (Hprogress : forall i, Inv i ->
      (exists o, List.In o (batch i) /\ P o) \/ rank (next i) < rank i).

  Lemma emit_batches_af : forall i w, Inv i -> not_done w ->
    <( {(emit_batches batch next i : ictreeW W X)}, {w} |= AF visW {P} )>.
  Proof.
    intros i w Hi Hd; unfold emit_batches.
    eapply aul_iter_nat with (Ri := fun j (_ : World (writerE W)) => Inv j)
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
    <( {(emit_batches batch next i : ictreeW W X)}, {w} |= AG (AF visW {P}) )>.
  Proof.
    intros i w Hi Hd.
    assert (Hsuffix : forall (t : ictreeW W X) v,
      (exists j suffix, Inv j /\ not_done v /\
        t ~ emit_list suffix (emit_batches batch next j : ictreeW W X)) ->
      <( t, v |= AG (AF visW {P}) )>).
    { coinduction R CIH; intros t v (j & suffix & Hj & Hv & Ht).
      assert (Haf : <( t, v |= AF visW {P} )>).
      { rewrite Ht; apply af_emit_list; [exact Hv|].
        apply emit_batches_af; [exact Hj|apply after_logs_not_done; exact Hv]. }
      assert (Hexp : exists o rest j', Inv j' /\
        t ~ emit_list (o :: rest) (emit_batches batch next j' : ictreeW W X)).
      { destruct suffix as [|o rest].
        - destruct (batch j) as [|o rest] eqn:Eb; [exfalso; exact (Hnonempty j Hj Eb)|].
          exists o, rest, (next j); split; [apply Hnext, Hj|].
          rewrite Ht; cbn [emit_list fold_right].
          rewrite emit_batches_unfold_sbisim, Eb; reflexivity.
        - exists o, rest, j; split; [exact Hj|exact Ht]. }
      destruct Hexp as (o & rest & j' & Hj' & Ht').
      rewrite Ht', emit_list_cons.
      rewrite Ht', emit_list_cons in Haf.
      split; [exact Haf|]; split.
      - apply can_step_vis; [exact tt|exact Hv].
      - intros t' w' Htr.
        apply ktrans_vis in Htr as ([] & -> & <- & _).
        apply CIH; exists j', rest; split; [exact Hj'|].
        split; [constructor|reflexivity]. }
    apply Hsuffix; exists i, []; split; [exact Hi|]; split; [exact Hd|reflexivity].
  Qed.
End EmitBatches.
