From Stdlib Require Import Fin Program.Equality.

From TICL Require Export
  ICTree.Interp.Yield.SBisim.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Events.Yield
  ICTree.Interp.Yield.Mod
  Lang.Yield.Syntax
  Lang.Yield.Denote
  Lang.Yield.Interp.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

(** * Scheduler-visible denotation respects thread bisimilarity *)

(** Two source statements with strongly-bisimilar thread denotations yield
    strongly-bisimilar scheduler-visible computations.  This is the singleton
    instance of [sbisim_schedule] for the start-up pool of [scheduled_visible]. *)
Corollary sbisim_scheduled_visible (s1 s2 : YStmt) :
  denote_stmt s1 ~ denote_stmt s2 ->
  scheduled_visible s1 ~ scheduled_visible s2.
Proof.
  intro Hs.
  unfold scheduled_visible.
  apply sbisim_schedule.
  intro i.
  dependent destruction i.
  - exact Hs.
  - inversion i.
Qed.
