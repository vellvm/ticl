From Stdlib Require Import List.
From TICL Require Export ICTree.Trace.
From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Events.Writer
  ICTree.Logic.Trans ICTree.Logic.AX ICTree.Logic.AF ICTree.Logic.AG
  ICTree.Logic.Bind Logic.Core.

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
