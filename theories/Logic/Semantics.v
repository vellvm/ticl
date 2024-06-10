
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
  coinduction lattice tactics.

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

  Definition entailsL X : ctll E -> MP X := 
    fix entailsL (φ: ctll E): MP X :=
      match φ with
      | (CNow φ) => fun _ w => φ w /\ not_done w
      | (CProp p) => fun _ _ => p
      | (CuL Q_A p q) => cau (entailsL p) (entailsL q)
      | (CuL Q_E p q) => ceu (entailsL p) (entailsL q)
      | (CxL Q_A φ) => cax (entailsL φ)
      | (CxL Q_E φ) => cex (entailsL φ)
      | (Cg Q_A φ) => cag (entailsL φ)
      | (Cg Q_E φ) => ceg (entailsL φ)
      | (CAndL p q) => fun t w => entailsL p t w /\ entailsL q t w
      | (COrL p q) => fun t w => entailsL p t w \/ entailsL q t w
      | (CImplL p q) => fun t w => entailsL p t w -> entailsL q t w
      end.

  Definition entailsR {X}: ctlr E X -> MP X := 
    fix entailsR (φ: ctlr E X): MP X :=
      match φ with
      | (CDone φ) => fun _ => done_with φ
      | (CuR Q_A p q) => cau (entailsL X p) (entailsR q)
      | (CuR Q_E p q) => ceu (entailsL X p) (entailsR q)
      | (CxR Q_A φ) => cax (entailsR φ)
      | (CxR Q_E φ) => cex (entailsR φ)
      | (CAndR p q) => fun t w => entailsL X p t w /\ entailsR q t w
      | (COrR p q) => fun t w => entailsR p t w \/ entailsR q t w
      | (CImplR p q) => fun t w => entailsR p t w -> entailsR q t w
      end.

  Lemma unfold_entailsL {X}: forall (t: M E HE X) (w: World E) (φ: ctll E),
      entailsL X φ t w = match φ with
                         | (CNow φ) => φ w /\ not_done w
                         | (CProp p) => p
                         | (CuL Q_A p q) => cau (entailsL X p) (entailsL X q) t w
                         | (CuL Q_E p q) => ceu (entailsL X p) (entailsL X q) t w
                         | (CxL Q_A φ) => cax (entailsL X φ) t w
                         | (CxL Q_E φ) => cex (entailsL X φ) t w
                         | (Cg Q_A φ) => cag (entailsL X φ) t w
                         | (Cg Q_E φ) => ceg (entailsL X φ) t w
                         | (CAndL p q) => entailsL X p t w /\ entailsL X q t w
                         | (COrL p q) => entailsL X p t w \/ entailsL X q t w
                         | (CImplL p q) => entailsL X p t w -> entailsL X q t w
                         end.
  Proof. intros; unfold entailsL; destruct φ; auto; destruct q; auto. Qed.

  Lemma unfold_entailsR {X}: forall (t: M E HE X) (w: World E) (φ: ctlr E X),
      entailsR φ t w = match φ with
                       | (CDone φ) => done_with φ w
                       | (CuR Q_A p q) => cau (entailsL X p) (entailsR q) t w
                       | (CuR Q_E p q) => ceu (entailsL X p) (entailsR q) t w
                       | (CxR Q_A φ) => cax (entailsR φ) t w
                       | (CxR Q_E φ) => cex (entailsR φ) t w
                       | (CAndR p q) => entailsL X p t w /\ entailsR q t w
                       | (COrR p q) => entailsR p t w \/ entailsR q t w
                       | (CImplR p q) => entailsR p t w -> entailsR q t w
                       end.
  Proof. intros; unfold entailsR; destruct φ; auto; destruct q; auto. Qed.

  Global Opaque entailsL.
  Global Opaque entailsR.
End Entailment.

(* Entailment notation *)
Import CtlNotations.
Local Open Scope ctl_scope.

Notation " t , w  |= φ " := (entailsL _ φ t w)
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

Lemma ctll_prop `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (φ: Prop),
    <( t, w |= prop φ )> <-> φ.
Proof. intros; rewrite unfold_entailsL; reflexivity. Qed.
Global Hint Resolve ctll_prop: ctll.

Lemma ctll_pure `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E),
    <( t, w |= pure )> <-> w = Pure.
Proof.
  intros; split; intros. 
  - now destruct H.
  - subst; split; now constructor. 
Qed.
Global Hint Resolve ctll_pure: ctll.

Lemma ctll_vis `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) φ,
    <( t, w |= vis φ )> <-> vis_with φ w.
Proof.
  intros; split; intros.
  - now destruct H.
  - split; inv H; now constructor. 
Qed.
Global Hint Resolve ctll_vis: ctll.

Lemma ctlr_done `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (φ: X -> World E -> Prop),
    <[ t, w |= done φ ]> <-> done_with φ w.
Proof. intros; auto. Qed.
Global Hint Resolve ctlr_done: ctlr.

Lemma ctlr_done_eq `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (r:X),
    <[ t, w |= done= r w ]> <-> done_with (fun r' w' => r=r' /\ w=w') w.
Proof. intros; auto. Qed. 
Global Hint Resolve ctlr_done_eq: ctlr.

Lemma ctlr_finish `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) φ,
    <[ t, w |= finish φ ]> <-> done_with (X:=X) (finish_with φ) w.
Proof. intros; auto. Qed. 
Global Hint Resolve ctlr_finish: ctlr.

(*| AX, WX, EX unfold |*)
Lemma ctll_ax `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctll E),
    <( t, w |= AX p )> <-> can_step t w /\ forall t' w', [t, w] ↦ [t',w'] -> <( t',w' |= p )>.
Proof. intros; auto. Qed.

Lemma ctll_ex `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctll E),
    <( t,w |= EX p )> <-> exists t' w', [t,w] ↦ [t',w'] /\ <( t',w' |= p )>.
Proof. intros; auto. Qed.
Global Hint Resolve ctll_ax ctll_ex: ctl.

Lemma ctlr_ax `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctlr E X),
    <[ t, w |= AX p ]> <-> can_step t w /\ forall t' w', [t, w] ↦ [t',w'] -> <[ t',w' |= p ]>.
Proof. intros; auto. Qed.

Lemma ctlr_ex `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctlr E X),
    <[ t,w |= EX p ]> <-> exists t' w', [t,w] ↦ [t',w'] /\ <[ t',w' |= p ]>.
Proof. intros; auto. Qed.
Global Hint Resolve ctlr_ax ctlr_ex: ctl.

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
Lemma ctll_au_eu `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p q: ctll E),
    <( t, w |= p AU q )> -> <( t, w |= p EU q )>.
Proof.
  intros.
  rewrite unfold_entailsL in *.
  induction H.
  - now apply MatchE. 
  - destruct H0 as ((m' & ? & ?) & ?).
    destruct H1 as ((? & ? & ?) &  ?).
    apply StepE; auto.
    exists x0, x1; split; auto.
Qed.

Lemma ctlr_ax_ex `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctlr E X),
    <[ t, w |= AX p ]> -> <[ t, w |= EX p ]>.
Proof.
  intros.
  rewrite ctlr_ax, ctlr_ex in *.
  destruct H as ((m' & w' & TR) & ?).
  exists m', w'; auto.
Qed.

(* [AF φ] is stronger than [EF φ] *)
Lemma ctlr_au_eu `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ctll E) (q: ctlr E X),
    <[ t, w |= p AU q ]> -> <[ t, w |= p EU q ]>.
Proof.
  intros.
  rewrite unfold_entailsR in *.
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
  intros; rewrite unfold_entailsL.
  now intros [].
Qed.

(*| Top is True |*)
Lemma ctll_top `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    <( t, w |= ⊤ )>.
Proof.
  intros.
  now apply ctll_prop.
Qed.

(*| Cannot exist path such that eventually Bot |*)
Lemma ctll_sound_ef `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= EF ⊥ )>.
Proof.
  intros * Contra.
  rewrite unfold_entailsL in Contra.
  induction Contra.
  - contradiction.
  - now destruct H1 as (? & ? & ? & ?).
Qed.

(*| Cannot have all paths such that eventually always Bot |*)
Lemma ctll_sound_af `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= AF ⊥ )>.
Proof.
  intros * Contra.
  apply ctll_au_eu in Contra.
  apply ctll_sound_ef in Contra.
  contradiction.
Qed.

(* Basic tactics, more automated ones defined in [Tactics.v] after [Congruence.v] is done *)
#[global] Tactic Notation "step" "in" ident(H) :=
  (lazymatch type of H with
   | @entailsL ?M ?W ?HE ?KMS ?X (Cg ?q ?φ) ?t ?w =>
       rewrite unfold_entailsL in H; step_in H
   end || step_in H).

#[global] Ltac step :=
  first [
      lazymatch goal with
      | |- @entailsL ?M ?W ?HE ?KMS ?X (Cg ?q ?φ) ?t ?w =>
          rewrite unfold_entailsL; red; step_
      end | red; step_ ].

#[global] Ltac cinduction H0 :=
  match type of H0 with
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL ?q ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsL in H0; induction H0
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR ?q ?φ ?ψ) ?t ?w =>
      rewrite unfold_entailsR in H0; induction H0
  end.

#[global] Ltac coinduction_g R CIH :=
  let R' := fresh R in
  setoid_rewrite unfold_entailsL;
  coinduction R' CIH;
  try change (cag (entailsL ?X ?p) ?t ?w) with <( t, w |= AG p )> in *;
  try change (ceg (entailsL ?X ?p) ?t ?w) with <( t, w |= EG p )> in *.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  (coinduction_g R H || coinduction R H).
