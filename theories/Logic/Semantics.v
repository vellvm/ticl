
(*|
=========================================
Modal logics over kripke semantics
=========================================
|*)
From Coq Require Import
  Basics
  FunctionalExtensionality
  Classes.RelationPairs.

From Coinduction Require Import
  coinduction lattice.

From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad.

From CTree Require Import
  Events.Core
  Events.WriterE
  Utils.Utils
  Logic.Kripke.

From CTree Require Export
  Logic.Syntax.

From Equations Require Import Equations.

Generalizable All Variables.

(*| CTL logic shallow embedding, based on kripke semantics |*)
Section Shallow.
  Context `{KMS: Kripke M E} {X: Type}.

  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Local Open Scope ctl_scope.

  (*| Shallow strong/weak forall [next] modality |*)
  Definition cax (p: MP) (t: MS) (w: World E): Prop :=    
    can_step t w /\
      forall t' w', [t,w] ↦ [t', w'] -> p t' w'.
  
  Definition cex(p: MP) (t: MS) (w: World E): Prop :=
    exists t' w', [t, w] ↦ [t', w'] /\ p t' w'.
  
  Hint Unfold cax cex: core.

  Unset Elimination Schemes.
  (* Forall strong until *)
  Inductive cau (p q: MP): MP :=
  | MatchA: forall t w,       
      q t w ->    (* Matches [q] now; done *)
      cau p q t w
  | StepA:  forall t w,
      p t w ->    (* Matches [p] now; steps to [m'] *)
      cax (cau p q) t w ->
      cau p q t w.

  (* Exists strong until *)
  Inductive ceu(p q: MP): MP :=
  | MatchE: forall t w,
      q t w ->    (* Matches [q] now; done *)
      ceu p q t w
  | StepE: forall t w,
      p t w ->    (* Matches [p] now; steps to [m'] *)
      cex (ceu p q) t w ->
      ceu p q t w.

  (* Custom induction schemes for [cau, ceu] *)
  Definition cau_ind :
    forall [p q: MP] (P : MP),
      (forall t w, q t w -> P t w) -> (* base *)
      (forall t w,
          p t w ->          (* [p] now*)
          cax (cau p q) t w ->
          cax P t w ->
         P t w) ->
      forall t w, cau p q t w -> P t w :=
    fun p q P Hbase Hstep =>
      fix F (t : MS) (w: World E) (c : cau p q t w) {struct c}: P t w :=
      match c with
      | MatchA _ _ t w y => Hbase t w y
      | @StepA _ _ t w Hp (conj Hs HtrP) =>
          Hstep t w Hp
            (conj Hs HtrP)
            (conj Hs (fun t' w' tr => F t' w' (HtrP t' w' tr)))
      end.

  Definition ceu_ind :
    forall [p q: MP] (P : MP),
      (forall t w, q t w -> P t w) -> (* base *)
      (forall t w,
          p t w ->          (* [p] now*)
          cex (ceu p q) t w ->
          cex P t w ->
         P t w) ->
      forall t w, ceu p q t w -> P t w :=
    fun p q P Hbase Hstep =>
      fix F (t : MS) (w: World E) (c : ceu p q t w) {struct c}: P t w :=
      match c with
      | MatchE _ _ t w y => Hbase t w y
      | @StepE _ _ t w y (ex_intro _ t' (ex_intro _ w' (conj tr h))) =>
          Hstep t w y
            (ex_intro _ t'
               (ex_intro _ w'
                  (conj tr h))) (ex_intro _  t' (ex_intro _ w' (conj tr (F t' w' h))))
      end.
  Set Elimination Schemes.

  Arguments impl /.  
  (* Always globally *)
  (* Matches [p] now; all paths step to (t', s') *)
  Program Definition cagF p: mon MP :=
    {| body := fun R t w => p t w /\ cax R t w |}.
  Next Obligation.
    repeat red; intros; destruct H0; split; destruct H1; auto.
  Qed.
  
  Program Definition cegF p: mon MP :=
    {| body := fun R t w => p t w /\ cex R t w |}.
  Next Obligation.
    repeat red; intros; destruct H0 as [H0 (t' & w' & TR & Hx)]; split; auto.
    exists t', w'; auto.
  Qed.      

End Shallow.

(* Companion notations *)
Notation cag p := (gfp (cagF p)).
Notation ceg p := (gfp (cegF p)).
Notation cagt p  := (t (cagF p)).
Notation cegt p  := (t (cegF p)).
Notation cagbt p := (bt (cagF p)).
Notation cegbt p := (bt (cegF p)).
Notation cagT p  := (T (cagF p)).
Notation cegT p  := (T (cegF p)).
Notation cagbT p := (bT (cagF p)).
Notation cegbT p := (bT (cegF p)).
#[global] Hint Constructors ceu cau: ctl.

(*| Semantics of ctl entailment |*)
Section Entailment.
  Context `{KMS: Kripke M E}.
  Notation MS X := (M E HE X).
  Notation MP X := (M E HE X -> World E -> Prop).

  Equations entailsL(φ: ctll E): forall X, MP X := {
      entailsL (CNowL φ) => fun _ _ w => φ w /\ not_done w;
      entailsL (CuL Q_A p q) => fun X => cau (entailsL p X) (entailsL q X);
      entailsL (CuL Q_E p q) => fun X => ceu (entailsL p X) (entailsL q X);
      entailsL (CxL Q_A φ) => fun X => cax (entailsL φ X);
      entailsL (CxL Q_E φ) => fun X => cex (entailsL φ X);
      entailsL (Cg Q_A φ) => fun X => cag (entailsL φ X);
      entailsL (Cg Q_E φ) => fun X => ceg (entailsL φ X);
      entailsL (CAndL p q) => fun X t w => entailsL p X t w /\ entailsL q X t w;
      entailsL (COrL p q) => fun X t w => entailsL p X t w \/ entailsL q X t w;
      entailsL (CImplL p q) => fun X t w => entailsL p X t w -> entailsL q X t w      
    }.

  Equations entailsR{X}(φ: ctlr E X): MP X := {
      entailsR (CDone φ) => fun _ => done_with φ;
      entailsR (CuR Q_A p q) => cau (entailsL p X) (entailsR q);
      entailsR (CuR Q_E p q) => ceu (entailsL p X) (entailsR q);
      entailsR (CxR Q_A φ) => cax (entailsR φ);
      entailsR (CxR Q_E φ) => cex (entailsR φ);
      entailsR (CAndR p q) => fun t w => entailsL p X t w /\ entailsR q t w;
      entailsR (COrR p q) => fun t w => entailsL p X t w \/ entailsR q t w;
      entailsR (CImplR p q) => fun t w => entailsL p X t w -> entailsR q t w;
    }.

End Entailment.

(* Entailment notation *)
Import CtlNotations.
Local Open Scope ctl_scope.

Notation " t , w  |= φ " := (entailsL φ _ t w)
                              (in custom ctll at level 80,
                                  φ custom ctll,
                                  right associativity): ctl_scope.

Notation " t , w  |= φ " := (entailsR φ t w)
                              (in custom ctlr at level 80,
                                  φ custom ctlr,
                                  right associativity): ctl_scope.


(*| Base constructors of logical formulas |*)
Lemma ctll_now `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (φ: World E -> Prop),
    <( t, w |= now φ )> <-> φ w /\ not_done w.
Proof. reflexivity. Qed.
Global Hint Resolve ctll_now: ctll.

Lemma ctll_pure `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E),
    <( t, w |= pure )> <-> w = Pure.
Proof.
  intros; simp entailsF; split; intros. 
  - now destruct H.
  - subst; split; now constructor. 
Qed.
Global Hint Resolve ctll_pure: ctll.

Lemma ctll_vis `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) φ,
    <( t, w |= vis φ )> <-> vis_with φ w.
Proof.
  intros; simp entailsF; split; intros.
  - now destruct H.
  - split; inv H; now constructor. 
Qed.
Global Hint Resolve ctll_vis: ctll.

Lemma ctlr_done `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (φ: X -> World E -> Prop),
    <[ t, w |= done φ ]> <-> done_with φ w.
Proof. intros; simp entailsF; auto. Qed.
Global Hint Resolve ctlr_done: ctlr.

Lemma ctlr_done_eq `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (r:X),
    <[ t, w |= done= r w ]> <-> done_with (fun r' w' => r=r' /\ w=w') w.
Proof. intros; simp entailsF; auto. Qed. 
Global Hint Resolve ctlr_done_eq: ctlr.

Lemma ctll_finish `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) φ,
    <[ t, w |= finish φ ]> <-> done_with (X:=X) (finish_with φ) w.
Proof. intros; simp entailsF; auto. Qed. 
Global Hint Resolve ctll_finish: ctlr.

(*| AX, WX, EX unfold |*)
Lemma ctll_ax `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctll E),
    <( t, w |= AX p )> <-> can_step t w /\ forall t' w', [t, w] ↦ [t',w'] -> <( t',w' |= p )>.
Proof. intros; now simp entailsF. Qed.

Lemma ctll_ex `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctll E),
    <( t,w |= EX p )> <-> exists t' w', [t,w] ↦ [t',w'] /\ <( t',w' |= p )>.
Proof. intros; now simp entailsF. Qed.
Global Hint Resolve ctll_ax ctll_ex: ctl.

Lemma ctlr_ax `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctlr E X),
    <[ t, w |= AX p ]> <-> can_step t w /\ forall t' w', [t, w] ↦ [t',w'] -> <[ t',w' |= p ]>.
Proof. intros; now simp entailsF. Qed.

Lemma ctlr_ex `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctlr E X),
    <[ t,w |= EX p ]> <-> exists t' w', [t,w] ↦ [t',w'] /\ <[ t',w' |= p ]>.
Proof. intros; now simp entailsF. Qed.
Global Hint Resolve ctll_ax ctll_ex: ctl.

(* [AX φ] is stronger than [EX φ] *)
Lemma ctll_ax_ex `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctll E),
    <( t, w |= AX p )> -> <( t, w |= EX p )>.
Proof.
  intros.
  rewrite ctll_ax, ctll_ex in *.
  destruct H as ((m' & w' & TR) & ?).
  exists m', w'; auto.
Qed.

(* [AF φ] is stronger than [EF φ] *)
Lemma ctll_af_ef `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctll E),
    <( t, w |= AF p )> -> <( t, w |= EF p )>.
Proof.
  intros.
  simp entailsL in *.
  induction H.
  - now apply MatchE. 
  - destruct H0 as ((m' & ? & ?) & ?).
    destruct H1 as ((? & ? & ?) &  ?).
    apply StepE; auto.
    exists x0, x1; split; auto.
Qed.

(*| Bot is false |*)
Lemma ctll_sound `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= ⊥ )>.
Proof. now intros * []. Qed. 

(*| Ex-falso |*)
Lemma ctll_ex_falso `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E) (p: ctll E),
    <( t, w |= ⊥ -> p )>.
Proof.
  cbn.
  intros; simp entailsL.
  now intros [].
Qed.

(*| Top is True |*)
Lemma ctll_top `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    not_done w -> <( t, w |= ⊤ )>.
Proof.
  cbn.
  simp entailsL; intros; auto.
Qed.

Lemma ctlr_top `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    is_done w -> <[ t, w |= ⊤ ]>.
Proof.
  cbn.
  simp entailsL; intros; auto.
Qed.

(*| Cannot exist path such that eventually Bot |*)
Lemma ctll_sound_ef `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= EF ⊥ )>.
Proof.
  intros * Contra.
  simp entailsF in Contra.
  induction Contra.
  - contradiction.
  - now destruct H1 as (? & ? & ? & ?).
Qed.

(*| Cannot have all paths such that eventually always Bot |*)
Lemma ctll_sound_af `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= AF ⊥ )>.
Proof.
  intros * Contra.
  apply ctll_af_ef in Contra.
  apply ctll_sound_ef in Contra.
  contradiction.
Qed.

(*| Semantic equivalence of formulas |*)
Definition equiv_ctl {M} `{HE: Encode E} {K: Kripke M E} X: relation (ctlf E) :=
  fun p q => forall (t: M E HE X) (w: World E), entailsF p t w <-> entailsF q t w.

Section EquivCtlEquivalence.
  Context `{K: Kripke M E} {X: Type}.
  Notation equiv_ctl := (@equiv_ctl M E HE K X).

  Global Instance Equivalence_equiv_ctl:
    Equivalence equiv_ctl.
  Proof.
    constructor.
    - intros P x; reflexivity.
    - intros P Q H' x; symmetry; auto.
    - intros P Q R H0' H1' x; etransitivity; auto.
  Qed.

  (*| [equiv_ctl] proper under [equiv_ctl] |*)
  Global Add Parametric Morphism : equiv_ctl with signature
         equiv_ctl ==> equiv_ctl ==> iff as equiv_ctll_equiv.
  Proof.
    intros p q EQpq p' q' EQpq'; split;
      intros EQpp'; split; intro BASE; cbn in *.
    - symmetry in EQpq'; apply EQpq'.
      symmetry in EQpp'; apply EQpp'.
      now apply EQpq.
    - symmetry in EQpq'; apply EQpq.
      apply EQpp'.
      now apply EQpq'.
    - apply EQpq'.
      symmetry in EQpp'; apply EQpp'.
      symmetry in EQpq; now apply EQpq.
    - apply EQpq.
      apply EQpp'.
      symmetry in EQpq'; now apply EQpq'.
  Qed.
End EquivCtlEquivalence.
