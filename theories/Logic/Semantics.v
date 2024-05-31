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
  Utils.Utils.

From CTree Require Export
  Logic.Kripke.

Set Implicit Arguments.
Generalizable All Variables.

(*| CTL logic shallow embedding, based on kripke semantics |*)
Section Shallow.
  Context `{KMS: Kripke M W} {X: Type}.
  Notation MP := (M X -> World W -> Prop).
  Local Open Scope ctl_scope.

  (*| Shallow strong/weak forall [next] modality |*)
  Definition cax (p: MP) (t: M X) (w: World W): Prop :=    
    can_step t w /\
      forall t' w', [t,w] ↦ [t', w'] -> p t' w'.
  
  Definition cex(p: MP) (t: M X) (w: World W): Prop :=
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
      fix F (t : M X) (w: World W) (c : cau p q t w) {struct c}: P t w :=
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
      fix F (t : M X) (w: World W) (c : ceu p q t w) {struct c}: P t w :=
      match c with
      | MatchE _ _ t w y => Hbase t w y
      | @StepE _ _ t w y (ex_intro _ t' (ex_intro _ w' (conj tr h))) =>
          Hstep t w y
            (ex_intro _ t'
               (ex_intro _ w'
                  (conj tr h))) (ex_intro _  t' (ex_intro _ w' (conj tr (F t' w' h))))
      end.
  Set Elimination Schemes.
  
  (* Forall release *)
  Variant carF (p q R: MP): MP :=
  | RMatchA: forall t w,       
      q t w ->  (* Matches [q] now; done *)
      p t w ->  (* Matches [p] as well *)
      carF p q R t w
  | RStepA:  forall t w,
      p t w ->    (* Matches [p] now; steps to (t', s') *)
      cax R t w ->
      carF p q R t w.

  (* Exists release *)
  Variant cerF (p q R: MP): MP :=
  | RMatchE: forall t w,
      q t w ->       (* Matches [q] now; done *)
      p t w ->       (* Matches [p] as well *)
      cerF p q R t w
  | RStepE: forall t w,
      p t w ->    (* Matches [p] now; steps to (t', s') *)
      cex R t w ->
      cerF p q R t w.

  Hint Constructors cau ceu carF cerF: core.

  (*| Global (coinductives) |*)
  Program Definition car_ p q: mon MP :=
    {| body := fun R m => carF p q R m |}.
  Next Obligation.
    repeat red; unfold impl; intros.
    destruct H0; auto; cbn in H0.
    apply RStepA; unfold cax in *; intuition.
  Qed.
  
  Program Definition cer_ p q: mon MP :=
    {| body := fun R m => cerF p q R m |}.
  Next Obligation.
    repeat red; unfold impl.
    intros.
    destruct H0.
    - now apply RMatchE.
    - destruct H1 as (t' & w' & TR' & H').
      apply RStepE; auto.
      exists t', w'; auto.
  Qed.      

End Shallow.

Section Syntax.
  Context {W: Type} `{HW: Encode W}.

  Inductive ctlf{X: Type}: bool -> Type :=
  | CTop: ctlf false
  | CBottom: ctlf false
  | CNow  (p: World W -> Prop): ctlf false      (* Does not terminate *)
  | CDone (p: X -> World W -> Prop): ctlf true   (* Checks termination *)
  | CAX   {b}: ctlf b -> ctlf b
  | CEX   {b}: ctlf b -> ctlf b
  | CAnd  {a b}: ctlf a -> ctlf b -> ctlf (a || b)
  | COr   {a b}: ctlf a -> ctlf b -> ctlf (a || b)
  | CImpl {a b}: ctlf a -> ctlf b -> ctlf (a || b)
  | CAU   {b}: ctlf false -> ctlf b -> ctlf b
  | CEU   {b}: ctlf false -> ctlf b -> ctlf b
  | CAR   {b}: ctlf false -> ctlf b -> ctlf b
  | CER   {b}: ctlf false -> ctlf b -> ctlf b.
End Syntax.

Arguments ctlf W {HW} X b.

Notation car p q := (gfp (car_ p q)).
Notation cer p q := (gfp (cer_ p q)).

Section Entailment.
  Context `{KMS: Kripke M W} {X: Type}.

  (* Entailment inductively on formulas *)
  Fixpoint entailsF{b} (φ: ctlf W X b): M X -> World W -> Prop :=
    match φ with
    | CTop => fun _ _ => True
    | CBottom => fun _ _ => False
    | CNow p => fun _ w => p w /\ not_done w
    | CDone p => fun _ => done_with p
    | CAnd φ ψ => fun t w => entailsF φ t w /\ entailsF ψ t w
    | COr φ ψ => fun t w => entailsF φ t w \/ entailsF ψ t w
    | CImpl φ ψ => fun t w => entailsF φ t w -> entailsF ψ t w
    | CAX φ => cax (entailsF φ)
    | CEX φ => cex (entailsF φ)
    | CAU φ ψ => cau (entailsF φ) (entailsF ψ)
    | CEU φ ψ => ceu (entailsF φ) (entailsF ψ)
    | CAR φ ψ => car (entailsF φ) (entailsF ψ)
    | CER φ ψ => cer (entailsF φ) (entailsF ψ)
    end.

  Lemma unfold_entailsF {b}: forall (φ: ctlf W X b),
      entailsF φ = match φ with
                   | CTop => fun _ _ => True
                   | CBottom => fun _ _ => False
                   | CNow p => fun _ w => p w /\ not_done w
                   | CDone p => fun _ => done_with p
                   | CAnd φ ψ => fun t w => entailsF φ t w /\ entailsF ψ t w
                   | COr φ ψ => fun t w => entailsF φ t w \/ entailsF ψ t w
                   | CImpl φ ψ => fun t w => entailsF φ t w-> entailsF ψ t w
                   | CAX φ => cax (entailsF φ)
                   | CEX φ => cex (entailsF φ)
                   | CAU φ ψ => cau (entailsF φ) (entailsF ψ)
                   | CEU φ ψ => ceu (entailsF φ) (entailsF ψ)
                   | CAR φ ψ => car (entailsF φ) (entailsF ψ)
                   | CER φ ψ => cer (entailsF φ) (entailsF ψ)
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
  Notation "'now' p" :=
    (CNow p)
      (in custom ctl at level 74): ctl_scope.
  Notation "'done' R" :=
    (CDone R)
      (in custom ctl at level 74): ctl_scope.
  Notation "'done=' r w" :=
    (CDone (fun r' w' => r = r' /\ w = w'))
      (in custom ctl at level 74): ctl_scope.
  
  Notation "'pure'" :=
    (CNow (fun w => w = Pure))
      (in custom ctl at level 74): ctl_scope.
  Notation "'vis' R" :=
    (CNow (vis_with R))
      (in custom ctl at level 74): ctl_scope.
  
  Notation "'finish' R" :=
    (CDone (finish_with R))
      (in custom ctl at level 74): ctl_scope.
  
  Notation "'visW' \ v , y " :=
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log v as x := pat return (encode x -> Prop) in
                       fun 'tt => y)))
      (in custom ctl at level 75,
          v binder,
          y constr, left associativity): ctl_scope.

  Notation "'finishW' \ v x , y " :=
    (CDone (finish_with (fun x (pat : writerE _) =>
                           let 'Log v as u := pat return (encode u -> Prop) in
                           fun 'tt => y)))
      (in custom ctl at level 75,
          v binder,
          x binder,
          y constr, left associativity): ctl_scope.

  Notation "⊤" := (CTop) (in custom ctl at level 76): ctl_scope.
  Notation "⊥" := (CBottom) (in custom ctl at level 76): ctl_scope.
  
  (* Temporal syntax: inductive *)
  Notation "'EX' p" := (CEX p) (in custom ctl at level 75): ctl_scope.
  Notation "'AX' p" := (CAX p) (in custom ctl at level 75): ctl_scope.

  Notation "p 'EU' q" := (CEU p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AU' q" := (CAU p q) (in custom ctl at level 75): ctl_scope.
  
  Notation "p 'ER' q" := (CER p q) (in custom ctl at level 75): ctl_scope.
  Notation "p 'AR' q" := (CAR p q) (in custom ctl at level 75): ctl_scope.
  
  Notation "'EF' p" := (CEU (CNow (fun _=> True)) p) (in custom ctl at level 74): ctl_scope.
  Notation "'AF' p" := (CAU (CNow (fun _=> True)) p) (in custom ctl at level 74): ctl_scope.
  Notation "'EG' p" := (CER p (CNow (fun _=>False))) (in custom ctl at level 74): ctl_scope.
  Notation "'AG' p" := (CAR p (CNow (fun _=>False))) (in custom ctl at level 74): ctl_scope.
  
  (* Propositional syntax *)
  Notation "p '/\' q" := (CAnd p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '\/' q" := (COr p q) (in custom ctl at level 77, left associativity): ctl_scope.
  Notation "p '->' q" := (CImpl p q)
                           (in custom ctl at level 78, right associativity): ctl_scope.
  Notation " ¬ p" := (CImpl p (CNow (fun _ => False))) (in custom ctl at level 76): ctl_scope.
  Notation "p '<->' q" := (CAnd (CImpl p q) (CImpl q p)) (in custom ctl at level 77): ctl_scope.

  (* Companion notations *)
  Notation cart p q := (t (car_ p q)).
  Notation cert p q := (t (cer_ p q)).
  Notation carbt p q := (bt (car_ p q)).
  Notation cerbt p q:= (bt (cer_ p q)).
  Notation carT p q := (T (car_ p q)).
  Notation cerT p q := (T (cer_ p q)).
  Notation carbT p q := (bT (car_ p q)).
  Notation cerbT p q := (bT (cer_ p q)).
  #[global] Hint Constructors ceu cau carF cerF: ctl.
  
End CtlNotations.

Import CtlNotations.
Local Open Scope ctl_scope.

(*| Base constructors of logical formulas |*)
Lemma ctl_now `{KMS: Kripke M W} X:
  forall (t: M X) (w: World W) (φ: World W -> Prop),
    <( t, w |= now φ )> <-> φ w /\ not_done w.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve ctl_now: ctl.

Lemma ctl_pure `{KMS: Kripke M W} X:
  forall (t: M X) (w: World W),
    <( t, w |= pure )> <-> w = Pure.
Proof.
  intros; rewrite unfold_entailsF; split; intros.
  - now destruct H.
  - subst; split; now constructor. 
Qed.
Global Hint Resolve ctl_pure: ctl.

Lemma ctl_vis `{KMS: Kripke M W} X:
  forall (t: M X) (w: World W) φ,
    <( t, w |= vis φ )> <-> vis_with φ w. 
Proof.
  intros; rewrite unfold_entailsF; split; intros.
  - now destruct H.
  - inv H; split; now constructor.
Qed.
Global Hint Resolve ctl_vis: ctl.

Lemma ctl_done `{KMS: Kripke M W} X:
  forall (t: M X) (w: World W) (φ: X -> World W -> Prop),
    <( t, w |= done φ )> <-> done_with φ w.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve ctl_done: ctl.

Lemma ctl_done_eq `{KMS: Kripke M W} X:
  forall (t: M X) (w: World W) (r:X),
    <( t, w |= done= r w )> <-> done_with (fun r' w' => r=r' /\ w=w') w.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve ctl_done_eq: ctl.

Lemma ctl_finish `{KMS: Kripke M W} X:
  forall (t: M X) (w: World W) φ,
    <( t, w |= finish φ )> <-> done_with (finish_with φ) w.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve ctl_finish: ctl.

(*| AX, WX, EX unfold |*)
Lemma unfold_ax `{KMS: Kripke M W} X:
  forall (t: M X) (w: World W) b (p: ctlf W X b),
    <( t, w |= AX p )> <-> can_step t w /\ forall t' w', [t, w] ↦ [t',w'] -> <( t',w' |= p )>.
Proof. intros; now rewrite unfold_entailsF. Qed.

Lemma unfold_ex `{KMS: Kripke M W} X:
  forall (t: M X) (w: World W) b (p: ctlf W X b),
    <( t,w |= EX p )> <-> exists t' w', [t,w] ↦ [t',w'] /\ <( t',w' |= p )>.
Proof. intros; now rewrite unfold_entailsF. Qed.
Global Hint Resolve unfold_ax unfold_ex: ctl.

(* [AX φ] is stronger than [EX φ] *)
Lemma ctl_ax_ex `{KMS: Kripke M W} X:
  forall (t: M X) (w: World W) b (p: ctlf W X b),
    <( t, w |= AX p )> -> <( t, w |= EX p )>.
Proof.
  intros.
  rewrite unfold_ax, unfold_ex in *.
  destruct H as ((m' & w' & TR) & ?).
  exists m', w'; auto.
Qed.

(* [AF φ] is stronger than [EF φ] *)
Lemma ctl_af_ef `{KMS: Kripke M W} X:
  forall (t: M X) (w: World W) b (p: ctlf W X b),
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
Lemma ctl_sound `{KMS: Kripke M W} X: forall (t: M X) (w: World W),
    ~ <( t, w |= ⊥ )>.
Proof. intros * []. Qed.

(*| Ex-falso |*)
Lemma ctl_ex_falso `{KMS: Kripke M W} X: forall (t: M X) (w: World W) b (p: ctlf W X b),
    <( t, w |= ⊥ -> p )>.
Proof. intros; rewrite unfold_entailsF; intro CONTRA; contradiction. Qed.

(*| Top is True |*)
Lemma ctl_top `{KMS: Kripke M W} X: forall (t: M X) (w: World W),
    <( t, w |= ⊤ )>.
Proof. reflexivity. Qed. 

(*| Cannot exist path such that eventually Bot |*)
Lemma ctl_sound_ef `{KMS: Kripke M W} X: forall (t: M X) (w: World W),
    ~ <( t, w |= EF ⊥ )>.
Proof.
  intros * Contra.
  rewrite unfold_entailsF in Contra.
  induction Contra.
  - contradiction.
  - now destruct H1 as (? & ? & ? & ?).
Qed.

(*| Cannot have all paths such that eventually always Bot |*)
Lemma ctl_sound_af `{KMS: Kripke M W} X: forall (t: M X) (w: World W),
    ~ <( t, w |= AF ⊥ )>.
Proof.
  intros * Contra.
  apply ctl_af_ef in Contra.
  apply ctl_sound_ef in Contra.
  contradiction.
Qed.

(*| Semantic equivalence of formulas |*)
Definition equiv_ctl {M} `{HE: Encode W} {K: Kripke M W}{X} {b}: relation (ctlf W X b) :=
  fun p q => forall (t: M X) (w: World W), entailsF p t w <-> entailsF q t w.

Infix "⩸" := equiv_ctl (at level 58, left associativity): ctl_scope.

Section EquivCtlEquivalence.
  Context {M: Type -> Type} `{HE: Encode W} {K: Kripke M W} {X: Type} {b: bool}.
  Notation equiv_ctl := (@equiv_ctl M W HE K X b).

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
