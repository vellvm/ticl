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
  Logic.Kripke
  Logic.Syntax.

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

Notation cag p := (gfp (cagF p)).
Notation ceg p := (gfp (cegF p)).

Section Entailment.
  Context `{KMS: Kripke M E}.

  (* Two types of formulas requires a typeclass for denotation *)
  Polymorphic Class Entails {X} (Φ: Type): Type :=
    entails: Φ -> M E HE X -> World E -> Prop.

  Fixpoint entailsL X (φ: ctll E) : M E HE X -> World E -> Prop :=
    let fix entailsP (φ: CBool (ctll E)) :=
      match φ with
      | CBase cp => entailsL X cp
      | CAnd φ ψ => fun m w => entailsP φ m w /\ entailsP ψ m w
      | COr φ ψ => fun m w => entailsP φ m w \/ entailsP ψ m w
      | CImpl φ ψ => fun m w => entailsP φ m w -> entailsP ψ m w
      | CNot φ => fun m w => entailsP φ m w -> False
      end in
    match φ with
    | CNowL ψ => fun _ w => ψ w /\ not_done w
    | CgL Q_A p => cag (entailsL X p)
    | CgL Q_E p => ceg (entailsL X p)
    | CxL Q_A p => cax (entailsL X p)
    | CxL Q_E p => cex (entailsL X p)
    | CuL Q_A p q => cau (entailsL X p) (entailsL X q)
    | CuL Q_E p q => ceu (entailsL X p) (entailsL X q)
    | CBoolL p => entailsP p
    end.

  Fixpoint entailsR {X} (φ: ctlr E X): M E HE X -> World E -> Prop :=
    let fix entailsP (φ: CBool (ctlr E X)) :=
      match φ with
      | CBase cp => entailsR cp
      | CAnd φ ψ => fun m w => entailsP φ m w /\ entailsP ψ m w
      | COr φ ψ => fun m w => entailsP φ m w \/ entailsP ψ m w
      | CImpl φ ψ => fun m w => entailsP φ m w -> entailsP ψ m w
      | CNot φ => fun m w => entailsP φ m w -> False
      end in
    match φ with
    | CNowR ψ => fun _ w => ψ w /\ not_done w
    | CDoneR ψ => fun _ => done_with ψ
    | CxR Q_A p => cax (entailsR p)
    | CxR Q_E p => cex (entailsR p)
    | CuR Q_A p q => cau (entailsL X p) (entailsR q)
    | CuR Q_E p q => ceu (entailsL X p) (entailsR q)           
    | CBoolR p => entailsP p
    end.

  Global Instance EntailsL {X} : Entails (ctll E) :=
    fun (φ: ctll E) => entailsL X φ.

  Global Instance EntailsR {X}: Entails (ctlr E X) :=
    fun (φ: ctlr E X) => entailsR φ.

  Lemma unfold_entailsL {X}: forall (φ: ctll E),
      entailsL X φ = match φ with
                   | CBase p => fun _ => p
                   | CDone p => fun _ => done_with p
                   | CAnd φ ψ => fun t w => entailsF φ t w /\ entailsF ψ t w
                   | COr φ ψ => fun t w => entailsF φ t w \/ entailsF ψ t w
                   | CImpl φ ψ => fun t w => entailsF φ t w-> entailsF ψ t w
                   | CAX φ => cax (entailsF φ)
                   | CEX φ => cex (entailsF φ)
                   | CAU φ ψ => cau (entailsF φ) (entailsF ψ)
                   | CEU φ ψ => ceu (entailsF φ) (entailsF ψ)
                   | CAG φ => cag (entailsF φ)
                   | CEG φ => ceg (entailsF φ)
                   end.
  Proof. destruct φ; reflexivity. Qed.
  Global Opaque entailsF.
Section Entailment.
  Context `{KMS: Kripke M E} {X: Type}.
  Notation MS := (M HE X).

  (* Entailment inductively on formulas *)
  Fixpoint entailsF(φ: ctlf E X): MS -> World E -> Prop :=
    match φ with
    | CBase p => fun _ => p
    | CDone p => fun _ => done_with p
    | CAnd φ ψ => fun t w => entailsF φ t w /\ entailsF ψ t w
    | COr φ ψ => fun t w => entailsF φ t w \/ entailsF ψ t w
    | CImpl φ ψ => fun t w => entailsF φ t w -> entailsF ψ t w
    | CAX φ => cax (entailsF φ)
    | CEX φ => cex (entailsF φ)
    | CAU φ ψ => cau (entailsF φ) (entailsF ψ)
    | CEU φ ψ => ceu (entailsF φ) (entailsF ψ)
    | CAG φ => cag (entailsF φ)
    | CEG φ => ceg (entailsF φ)
    end.

  Lemma unfold_entailsF: forall (φ: ctlf E X),
      entailsF φ = match φ with
                   | CBase p => fun _ => p
                   | CDone p => fun _ => done_with p
                   | CAnd φ ψ => fun t w => entailsF φ t w /\ entailsF ψ t w
                   | COr φ ψ => fun t w => entailsF φ t w \/ entailsF ψ t w
                   | CImpl φ ψ => fun t w => entailsF φ t w-> entailsF ψ t w
                   | CAX φ => cax (entailsF φ)
                   | CEX φ => cex (entailsF φ)
                   | CAU φ ψ => cau (entailsF φ) (entailsF ψ)
                   | CEU φ ψ => ceu (entailsF φ) (entailsF ψ)
                   | CAG φ => cag (entailsF φ)
                   | CEG φ => ceg (entailsF φ)
                   end.
  Proof. destruct φ; reflexivity. Qed.
  Global Opaque entailsF.
End Entailment.

Module CtlNotations.

  Local Open Scope ctl_scope. 
  Delimit Scope ctl_scope with ctl.

  Notation "<( e )>" := e (at level 0, e custom ctl at level 95) : ctl_scope.
  Notation "( x )" := x (in custom ctl, x at level 99) : ctl_scope.
  Notation "{ x }" := x (in custom ctl at level 0, x constr): ctl_scope.
  Notation "x" := x (in custom ctl at level 0, x constr at level 0) : ctl_scope.
  Notation " t , w  |= φ " := (entailsF φ t w)
                                (in custom ctl at level 80,
                                    φ custom ctl,
                                    right associativity):
      ctl_scope.

  Notation "|- φ " := (entailsF φ) (in custom ctl at level 80,
                                       φ custom ctl, only parsing): ctl_scope.

  (* Temporal syntax: base predicates *)
  Notation "'base' p" :=
    (CBase p)
      (in custom ctl at level 74): ctl_scope.
  
  Notation "'now' p" :=
    (CBase (fun w => p w /\ not_done w))
      (in custom ctl at level 74): ctl_scope.
  
  Notation "'done' R" :=
    (CDone R)
      (in custom ctl at level 74): ctl_scope.
  
  Notation "'done=' r w" :=
    (CDone (fun r' w' => r = r' /\ w = w'))
      (in custom ctl at level 74): ctl_scope.
  
  Notation "'pure'" :=
    (CBase (fun w => w = Pure))
      (in custom ctl at level 74): ctl_scope.

  Notation "'vis' R" :=
    (CBase (vis_with R))
      (in custom ctl at level 74): ctl_scope.
  
  Notation "'finish' R" :=
    (CDone (finish_with R))
      (in custom ctl at level 74): ctl_scope.
  
  Notation "'visW' R" :=
    (CBase (vis_with (fun pat : writerE _ =>
                       let 'Log v as x := pat return (encode x -> Prop) in
                       fun 'tt => R v)))
      (in custom ctl at level 75): ctl_scope.

  Notation "'finishW' R" :=
    (CDone (finish_with (fun '(x, s) (pat : writerE _) =>
                           let 'Log w as u := pat return (encode u -> Prop) in
                           fun 'tt => R x s w)))
      (in custom ctl at level 75): ctl_scope.

  Notation "⊤" := (CBase (fun _ => True)) (in custom ctl at level 76): ctl_scope.
  Notation "⊥" := (CBase (fun _ => False)) (in custom ctl at level 76): ctl_scope.
  
  (* Temporal syntax: inductive *)
  Notation "'EX' p" := (CEX p) (in custom ctl at level 75): ctl_scope.
  Notation "'AX' p" := (CAX p) (in custom ctl at level 75): ctl_scope.

  Notation "p 'EU' q" := (CEU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AU' q" := (CAU p q) (in custom ctl at level 75): ctl_scope.
  
  Notation "'EG' p" := (CEG p) (in custom ctl at level 75): ctl_scope.
  Notation "'AG' p" := (CAG p) (in custom ctl at level 75): ctl_scope.
  
  (* Syntactic sugar [AF, EF] is finally *)
  Notation "'EF' p" := (CEU <( ⊤ )> p) (in custom ctl at level 74): ctl_scope.
  Notation "'AF' p" := (CAU <( ⊤ )> p) (in custom ctl at level 74): ctl_scope.
  
  (* Propositional syntax *)
  Notation "p '/\' q" := (CAnd p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '\/' q" := (COr p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '->' q" := (CImpl p q)
                           (in custom ctl at level 78, right associativity): ctl_scope.
  Notation " ¬ p" := (CImpl p <( ⊥ )>) (in custom ctl at level 76): ctl_scope.
  Notation "p '<->' q" := (CAnd (CImpl p q) (CImpl q p)) (in custom ctl at level 77): ctl_scope.

  (* Companion notations *)
  Notation cagt p  := (t (cagF p)).
  Notation cegt p  := (t (cegF p)).
  Notation cagbt p := (bt (cagF p)).
  Notation cegbt p := (bt (cegF p)).
  Notation cagT p  := (T (cagF p)).
  Notation cegT p  := (T (cegF p)).
  Notation cagbT p := (bT (cagF p)).
  Notation cegbT p := (bT (cegF p)).
  #[global] Hint Constructors ceu cau: ctl.
  
End CtlNotations.

Import CtlNotations.
Local Open Scope ctl_scope.

(*| Base constructors of logical formulas |*)
Lemma ctl_base `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (φ: World E -> Prop),
    <( t, w |= base φ )> <-> φ w.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve ctl_base: ctl.

Lemma ctl_now `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (φ: World E -> Prop),
    <( t, w |= now φ )> <-> φ w /\ not_done w.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve ctl_now: ctl.

Lemma ctl_pure `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E),
    <( t, w |= pure )> <-> w = Pure.
Proof.
  intros; rewrite unfold_entailsF; split; intros.
  - now destruct H.
  - subst; split; now constructor. 
Qed.
Global Hint Resolve ctl_pure: ctl.

Lemma ctl_vis `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) φ,
    <( t, w |= vis φ )> <-> vis_with φ w. 
Proof.
  intros; rewrite unfold_entailsF; split; intros.
  - now destruct H.
  - inv H; now constructor. 
Qed.
Global Hint Resolve ctl_vis: ctl.

Lemma ctl_done `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (φ: X -> World E -> Prop),
    <( t, w |= done φ )> <-> done_with φ w.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve ctl_done: ctl.

Lemma ctl_done_eq `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (r:X),
    <( t, w |= done= r w )> <-> done_with (fun r' w' => r=r' /\ w=w') w.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve ctl_done_eq: ctl.

Lemma ctl_finish `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) φ,
    <( t, w |= finish φ )> <-> done_with (finish_with φ) w.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve ctl_finish: ctl.

(*| AX, WX, EX unfold |*)
Lemma unfold_ax `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctlf E X),
    <( t, w |= AX p )> <-> can_step t w /\ forall t' w', [t, w] ↦ [t',w'] -> <( t',w' |= p )>.
Proof. intros; now rewrite unfold_entailsF. Qed.

Lemma unfold_ex `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctlf E X),
    <( t,w |= EX p )> <-> exists t' w', [t,w] ↦ [t',w'] /\ <( t',w' |= p )>.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve unfold_ax unfold_ex: ctl.

(* [AX φ] is stronger than [EX φ] *)
Lemma ctl_ax_ex `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctlf E X),
    <( t, w |= AX p )> -> <( t, w |= EX p )>.
Proof.
  intros.
  rewrite unfold_ax, unfold_ex in *.
  destruct H as ((m' & w' & TR) & ?).
  exists m', w'; auto.
Qed.

(* [AF φ] is stronger than [EF φ] *)
Lemma ctl_af_ef `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctlf E X),
    <( t, w |= AF p )> -> <( t, w |= EF p )>.
Proof.
  intros.
  rewrite unfold_entailsF in *.
  induction H.
  - now apply MatchE. 
  - destruct H0 as ((m' & ? & ?) & ?).
    destruct H1 as ((? & ? & ?) &  ?).
    apply StepE; auto.
    exists x0, x1; split; auto.
Qed.

(*| Bot is false |*)
Lemma ctl_sound `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= ⊥ )>.
Proof. intros * []. Qed.

(*| Ex-falso |*)
Lemma ctl_ex_falso `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E) (p: ctlf E X),
    <( t, w |= ⊥ -> p )>.
Proof. intros; rewrite unfold_entailsF; intro CONTRA; contradiction. Qed.

(*| Top is True |*)
Lemma ctl_top `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    <( t, w |= ⊤ )>.
Proof. reflexivity. Qed. 

(*| Cannot exist path such that eventually Bot |*)
Lemma ctl_sound_ef `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= EF ⊥ )>.
Proof.
  intros * Contra.
  rewrite unfold_entailsF in Contra.
  induction Contra.
  - contradiction.
  - now destruct H1 as (? & ? & ? & ?).
Qed.

(*| Cannot have all paths such that eventually always Bot |*)
Lemma ctl_sound_af `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= AF ⊥ )>.
Proof.
  intros * Contra.
  apply ctl_af_ef in Contra.
  apply ctl_sound_ef in Contra.
  contradiction.
Qed.

(*| Semantic equivalence of formulas |*)
Definition equiv_ctl {M} `{HE: Encode E} {K: Kripke M E}{X}: relation (ctlf E X) :=
  fun p q => forall (t: M E HE X) (w: World E), entailsF p t w <-> entailsF q t w.

Infix "⩸" := equiv_ctl (at level 58, left associativity): ctl_scope.

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
         equiv_ctl ==> equiv_ctl ==> iff as equiv_ctl_equiv.
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
