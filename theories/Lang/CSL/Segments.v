(** * Source-instruction first-yield rules.

    Everything structural about first-yield segments — the inductive, its
    inversion laws, guard transport, determinism, branch-freedom and the
    scheduling equations — is owned by [ICTree.Interp.Yield.Segments] and is
    polymorphic in the handler and the response relation.  What remains here
    is exactly the [CProg]-dependent layer: one rule per source instruction,
    stated at the CSL handler [sh] in EXACT mode, plus the raw normalization
    tactic those rules are applied through. *)

From Stdlib Require Import List Arith.PeanoNat Fin Vector
  Classes.Morphisms Classes.RelationClasses Program.Equality.
From ExtLib Require Import Data.Monads.StateMonad.
From TICL Require Import
  Lang.CSL.Syntax Lang.CSL.Heap Lang.CSL.Denote Lang.CSL.Interp
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Trans ICTree.Trace
  ICTree.Events.Writer ICTree.Events.Yield ICTree.Interp.State.Mod
  ICTree.Interp.Refine ICTree.Interp.Yield.Mod ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin ICTree.Interp.Yield.Nondeterministic
  Utils.Vectors.

From TICL Require Export ICTree.Interp.Yield.Segments.

Import ICtree ICTreeNotations ListNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope list_scope.

(** ** The two response-relation instances.

    Naming them is not a compatibility layer: they are the two arguments the
    generic segment theory is instantiated at. *)
Notation csl_sb :=
  (fun X (t u : ictreeW (indexed (nat * nat)) X) => t ~ u).
Notation csl_equ :=
  (fun X (t u : ictreeW (indexed (nat * nat)) X) => t ≅ u).
(** ** Source-instruction rules, in exact mode. *)

Lemma exact_source_bind {A B} (p : CProg A) (next : A -> CProg B)
  (K : option B -> thread sE) sigma logs target sigma' :
  segment_to sh csl_equ (denote_flow p >>= fun flow =>
    match flow with None => K None | Some x => denote_flow (next x) >>= K end)
    sigma logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CBind p next) >>= K) sigma logs target sigma'.
Proof.
  intro H; eapply segment_to_equ; [apply source_raw_bind|exact H].
Qed.

Lemma exact_source_ret {A} (x : A) (K : option A -> thread sE)
  sigma logs target sigma' :
  segment_to sh csl_equ (K (Some x)) sigma logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CRet x) >>= K) sigma logs target sigma'.
Proof.
  intro H; eapply segment_to_equ; [apply source_raw_ret|exact H].
Qed.

Lemma exact_source_until {A} (body : CProg (option A))
  (K : option unit -> thread sE) sigma logs target sigma' :
  segment_to sh csl_equ (denote_flow body >>= until_tail body K)
    sigma logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CUntilNone body) >>= K)
    sigma logs target sigma'.
Proof.
  intro H; eapply segment_to_equ; [apply source_raw_until|exact H].
Qed.

Lemma exact_source_read a v (K : option nat -> thread sE)
  h c logs target sigma' :
  h a = Some v ->
  segment_to sh csl_equ (K (Some v)) (h,c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CRead a) >>= K) (h,c) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HRead a)))) (fun v => K (Some v))).
  - apply source_raw_read_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HRead a)))) (fun v => K (Some v)))
      (h,c) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list]; rewrite (heap_handler_rd_some a h c v Hr); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_write a v (K : option unit -> thread sE)
  h c logs target sigma' :
  h a <> None ->
  segment_to sh csl_equ (K (Some tt)) (upd h a v,c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CWrite a v) >>= K) (h,c) logs target sigma'.
Proof.
  intros Hp (residual & Hseg & Htail).
  destruct (h a) as [w|] eqn:Hw; [|contradiction].
  exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HWrite a v)))) (fun _ => K (Some tt))).
  - apply source_raw_write_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HWrite a v)))) (fun _ => K (Some tt)))
      (h,c) ([] ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite (heap_handler_wr_some a h c v w Hw); reflexivity.
  - reflexivity.
Qed.

(** The raw handler equation [h_indexed_log] is the response certificate here;
    [interp_indexed_emit] is an interpretation equation and cannot discharge
    this premise. *)
Lemma exact_source_emit tag block (K : option unit -> thread sE)
  h c logs target sigma' :
  segment_to sh csl_equ (K (Some tt)) (h,S c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CEmit tag block) >>= K) (h,c)
    (stamp (tag,block) c :: logs) target sigma'.
Proof.
  intros (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inr (Log (tag,block))))) (fun _ => K (Some tt))).
  - apply source_raw_emit_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inr (Log (tag,block))))) (fun _ => K (Some tt)))
      (h,c) ([stamp (tag,block) c] ++ logs) residual sigma').
    eapply segment_user with (result := tt); [|exact Hseg].
    cbn [emit_list]; rewrite (h_indexed_log (Sigma:=Heap) (tag,block) h c);
      reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_cas_success a expected desired
  (K : option bool -> thread sE) h c logs target sigma' :
  h a = Some expected ->
  segment_to sh csl_equ (K (Some true)) (upd h a desired,c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CCAS a expected desired) >>= K)
    (h,c) logs target sigma'.
Proof.
  intros Hr (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b))).
  - apply source_raw_cas_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b)))
      (h,c) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list];
      rewrite (heap_handler_cas_success a expected desired h c Hr); reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_cas_failure a expected desired current
  (K : option bool -> thread sE) h c logs target sigma' :
  h a = Some current -> current <> expected ->
  segment_to sh csl_equ (K (Some false)) (h,c) logs target sigma' ->
  segment_to sh csl_equ (denote_flow (CCAS a expected desired) >>= K)
    (h,c) logs target sigma'.
Proof.
  intros Hr Hne (residual & Hseg & Htail); exists residual; split; [|exact Htail].
  eapply segment_equ with (u' := residual)
    (u := Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b))).
  - apply source_raw_cas_head.
  - change (ThreadSegment sh csl_equ
      (Vis (inr (inr (inl (HCAS a expected desired)))) (fun b => K (Some b)))
      (h,c) ([] ++ logs) residual sigma').
    eapply segment_user; [|exact Hseg].
    cbn [emit_list];
      rewrite (heap_handler_cas_failure a expected desired current h c Hr Hne);
      reflexivity.
  - reflexivity.
Qed.

Lemma exact_source_yield (K : option unit -> thread sE) sigma target :
  guard_equ (K (Some tt)) target ->
  segment_to sh csl_equ (denote_flow CYield >>= K) sigma [] target sigma.
Proof.
  intro Htail; exists (K (Some tt)); split; [|exact Htail].
  eapply segment_equ with (u := Vis (inl Yield) (fun _ => K (Some tt))).
  - apply source_raw_yield_head.
  - apply segment_yield.
  - reflexivity.
Qed.

(** Finite syntax normalization is used only for raw equ and leading guards.
    It never changes a scheduler focus or invokes pool sbisim congruence. *)
Ltac csl_raw_equ :=
  cbn beta iota zeta;
  first [reflexivity |
    lazymatch goal with
    | |- (denote_flow (CBind _ _) >>= _) ≅ _ =>
        etransitivity; [apply source_raw_bind|]; csl_raw_equ
    | |- (denote_flow (CRet _) >>= _) ≅ _ =>
        etransitivity; [apply source_raw_ret|]; csl_raw_equ
    | |- ((?t >>= ?k) >>= ?j) ≅ _ =>
        etransitivity; [apply bind_bind|]; csl_raw_equ
    | |- (Ret _ >>= _) ≅ _ =>
        etransitivity; [apply bind_ret_l|]; csl_raw_equ
    | |- _ ≅ (denote_flow (CBind _ _) >>= _) => symmetry; csl_raw_equ
    | |- _ ≅ (denote_flow (CRet _) >>= _) => symmetry; csl_raw_equ
    | |- _ ≅ ((_ >>= _) >>= _) => symmetry; csl_raw_equ
    | |- _ ≅ (Ret _ >>= _) => symmetry; csl_raw_equ
    | |- Guard _ ≅ Guard _ => apply guard_equ_node; csl_raw_equ
    end].
