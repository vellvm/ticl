
(*|
=========================================
Modal logics over kripke semantics
=========================================
|*)
From Stdlib Require Import
  Basics
  FunctionalExtensionality
  Classes.RelationPairs.

From Coinduction Require Import
  coinduction lattice tactics.

From ExtLib Require Import
  Structures.Monad
  Data.Monads.StateMonad.

From TICL Require Import
  Events.Core
  Events.WriterE
  Utils.Utils
  Logic.Kripke.

From TICL Require Export
  Logic.Syntax.

Generalizable All Variables.

(*| TICL logic shallow embedding, based on kripke semantics |*)
Section Shallow.
  Context `{KMS: Kripke M E} {X: Type}.

  Notation MS := (M E HE X).
  Notation MP := (MS -> World E -> Prop).
  Local Open Scope ticl_scope.

  (*| Binary shallow strong/weak forall [next] modality |*)
  Definition anc (p q: MP) (t: MS) (w: World E): Prop :=
    p t w /\
      can_step t w /\
      (forall t' w', |t,w| ↦ |t', w'| -> q t' w').
  
  Definition enc(p q: MP) (t: MS) (w: World E): Prop :=
    p t w /\
      exists t' w', |t, w| ↦ |t', w'| /\ q t' w'.
  Hint Unfold anc enc: core.

  Unset Elimination Schemes.
  (* Forall strong until *)
  Inductive auc (p q: MP): MP :=
  | MatchA: forall t w,       
      q t w ->    (* Matches [q] now; done *)
      auc p q t w
  | StepA:  forall t w,
      anc p (auc p q) t w -> (* Matches [p] now; steps to [m'] *)
      auc p q t w.

  (* Exists strong until *)
  Inductive euc(p q: MP): MP :=
  | MatchE: forall t w,
      q t w ->    (* Matches [q] now; done *)
      euc p q t w
  | StepE: forall t w,
      enc p (euc p q) t w -> (* Matches [p] now; steps to [m'] *)
      euc p q t w.

  (* Custom induction schemes for [auc, euc] *)
  Definition auc_ind :
    forall [p q: MP] (P : MP),
      (forall t w, q t w -> P t w) -> (* base *)
      (forall t w, (* step *)
          anc p (auc p q) t w ->
          anc p P t w ->
         P t w) ->
      forall t w, auc p q t w -> P t w :=
    fun p q P Hbase Hstep =>
      fix F (t : MS) (w: World E) (c : auc p q t w) {struct c}: P t w :=
      match c with
      | MatchA _ _ t w y => Hbase t w y
      | @StepA _ _ t w (conj Hp (conj Hs HtrP)) =>
          Hstep t w
            (conj Hp (conj Hs HtrP))
            (conj Hp (conj Hs (fun t' w' tr => F t' w' (HtrP t' w' tr))))
      end.

  Definition euc_ind :
    forall [p q: MP] (P : MP),
      (forall t w, q t w -> P t w) -> (* base *)
      (forall t w, (* step *)
          p t w /\
            (exists t' w', |t, w| ↦ |t', w'|
                      /\ euc p q t' w'
                      /\ P t' w') ->
          P t w) ->
      forall t w, euc p q t w -> P t w :=
    fun p q P Hbase Hstep =>
      fix F (t : MS) (w: World E) (c : euc p q t w) {struct c}: P t w :=
      match c with
      | MatchE _ _ t w y => Hbase t w y
      | @StepE _ _ t w (conj Hp (ex_intro _ t' (ex_intro _ w' (conj tr h)))) =>
          Hstep t w
            (conj Hp
               (ex_intro _ t'
                  (ex_intro _ w' (conj tr
                                    (conj h
                                       (F t' w' h))))))

      end.
    
  Set Elimination Schemes.

  Arguments impl /.  
  (* Always globally *)
  (* Matches [p] now; all paths step to (t', s') *)
  Program Definition agcF p: mon MP :=
    {| body := anc p |}.
  Next Obligation.
    repeat red; intros; destruct H0; split; destruct H1; auto.
  Qed.
  
  Program Definition egcF p: mon MP :=
    {| body := enc p |}.
  Next Obligation.
    repeat red; intros; destruct H0 as [H0 (t' & w' & TR & Hx)]; split; auto.
    exists t', w'; auto.
  Qed.      

End Shallow.

(* Companion notations *)
Notation agc p   := (gfp (agcF p)).
Notation egc p   := (gfp (egcF p)).
Notation agct p  := (t (agcF p)).
Notation egct p  := (t (egcF p)).
Notation agcbt p := (bt (agcF p)).
Notation egcbt p := (bt (egcF p)).
Notation agcT p  := (T (agcF p)).
Notation egcT p  := (T (egcF p)).
Notation agcbT p := (bT (agcF p)).
Notation egcbT p := (bT (egcF p)).
#[global] Hint Constructors euc auc: ticl.

(*| Semantics of ticl entailment |*)
Section Entailment.
  Context `{KMS: Kripke M E}.
  Notation MS X := (M E HE X).
  Notation MP X := (M E HE X -> World E -> Prop).

  Definition entailsL X : ticll E -> MP X := 
    fix entailsL (φ: ticll E): MP X :=
      match φ with
      | (CNow φ) => fun _ w => φ w /\ not_done w
      | (CuL Q_A p q) => auc (entailsL p) (entailsL q)
      | (CuL Q_E p q) => euc (entailsL p) (entailsL q)
      | (CxL Q_A p q) => anc (entailsL p) (entailsL q)
      | (CxL Q_E p q) => enc (entailsL p) (entailsL q)
      | (Cg Q_A φ) => agc (entailsL φ)
      | (Cg Q_E φ) => egc (entailsL φ)
      | (CAndL p q) => fun t w => entailsL p t w /\ entailsL q t w
      | (COrL p q) => fun t w => entailsL p t w \/ entailsL q t w
      end.

  Definition entailsR {X}: ticlr E X -> MP X := 
    fix entailsR (φ: ticlr E X): MP X :=
      match φ with
      | (CDone φ) => fun _ => done_with φ
      | (CuR Q_A p q) => auc (entailsL X p) (entailsR q)
      | (CuR Q_E p q) => euc (entailsL X p) (entailsR q)
      | (CxR Q_A p q) => anc (entailsL X p) (entailsR q)
      | (CxR Q_E p q) => enc (entailsL X p) (entailsR q)
      | (CAndR p q) => fun t w => entailsR p t w /\ entailsR q t w
      | (COrR p q) => fun t w => entailsR p t w \/ entailsR q t w
      | (CImplR p q) => fun t w => entailsL X p t w -> entailsR q t w
      end.

  Lemma unfold_entailsL {X}: forall (t: M E HE X) (w: World E) (φ: ticll E),
      entailsL X φ t w = match φ with
                         | (CNow φ) => φ w /\ not_done w
                         | (CuL Q_A p q) => auc (entailsL X p) (entailsL X q) t w
                         | (CuL Q_E p q) => euc (entailsL X p) (entailsL X q) t w
                         | (CxL Q_A p q) => anc (entailsL X p) (entailsL X q) t w
                         | (CxL Q_E p q) => enc (entailsL X p) (entailsL X q) t w
                         | (Cg Q_A φ) => agc (entailsL X φ) t w
                         | (Cg Q_E φ) => egc (entailsL X φ) t w
                         | (CAndL p q) => entailsL X p t w /\ entailsL X q t w
                         | (COrL p q) => entailsL X p t w \/ entailsL X q t w
                         end.
  Proof. intros; unfold entailsL; destruct φ; auto; destruct q; auto. Qed.

  Lemma unfold_entailsR {X}: forall (t: M E HE X) (w: World E) (φ: ticlr E X),
      entailsR φ t w = match φ with
                       | (CDone φ) => done_with φ w
                       | (CuR Q_A p q) => auc (entailsL X p) (entailsR q) t w
                       | (CuR Q_E p q) => euc (entailsL X p) (entailsR q) t w
                       | (CxR Q_A p q) => anc (entailsL X p) (entailsR q) t w
                       | (CxR Q_E p q) => enc (entailsL X p) (entailsR q) t w
                       | (CAndR p q) => entailsR p t w /\ entailsR q t w
                       | (COrR p q) => entailsR p t w \/ entailsR q t w
                       | (CImplR p q) => entailsL X p t w -> entailsR q t w
                       end.
  Proof. intros; unfold entailsR; destruct φ; auto; destruct q; auto. Qed.

  Global Opaque entailsL.
  Global Opaque entailsR.
End Entailment.

(* Entailment notation *)
Import TiclNotations.
Local Open Scope ticl_scope.

Notation " t , w  |= φ " := (entailsL _ φ t w)
                              (in custom ticll at level 80,
                                  φ custom ticll,
                                  right associativity): ticl_scope.

Notation " t , w  |= φ " := (entailsR φ t w)
                              (in custom ticlr at level 80,
                                  φ custom ticlr,
                                  right associativity): ticl_scope.

(*| Base constructors of logical formulas |*)
Lemma ticll_now `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (φ: World E -> Prop),
    <( t, w |= now φ )> <-> φ w /\ not_done w.
Proof. reflexivity. Qed.
Global Hint Resolve ticll_now: ticll.

Lemma ticll_pure `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E),
    <( t, w |= pure )> <-> w = Pure.
Proof.
  intros; split; intros. 
  - now destruct H.
  - subst; split; now constructor. 
Qed.
Global Hint Resolve ticll_pure: ticll.

Lemma ticll_vis `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) φ,
    <( t, w |= vis φ )> <-> vis_with φ w.
Proof.
  intros; split; intros.
  - now destruct H.
  - split; inv H; now constructor. 
Qed.
Global Hint Resolve ticll_vis: ticll.

Lemma ticlr_done `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (φ: X -> World E -> Prop),
    <[ t, w |= done φ ]> <-> done_with φ w.
Proof. intros; auto. Qed.
Global Hint Resolve ticlr_done: ticlr.

Lemma ticlr_done_eq `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (r:X),
    <[ t, w |= done= r w ]> <-> done_with (fun r' w' => r=r' /\ w=w') w.
Proof. intros; auto. Qed. 
Global Hint Resolve ticlr_done_eq: ticlr.

Lemma ticlr_finish `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) φ,
    <[ t, w |= finish φ ]> <-> done_with (X:=X) (finish_with φ) w.
Proof. intros; auto. Qed. 
Global Hint Resolve ticlr_finish: ticlr.

(*| AN, WX, EN unfold |*)
Lemma ticll_an `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p q: ticll E),
    <( t, w |= p AN q )> <-> <( t, w |= p)> /\ can_step t w /\ forall t' w', |t, w| ↦ |t',w'| -> <( t',w' |= q )>.
Proof. intros; auto. Qed.

Lemma ticll_en `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p q: ticll E),
    <( t,w |= p EN q )> <-> <( t, w|= p)> /\ exists t' w', |t,w| ↦ |t',w'| /\ <( t',w' |= q )>.
Proof. intros; auto. Qed.
Global Hint Resolve ticll_an ticll_en: ticl.

Lemma ticlr_an `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ticll E) (q: ticlr E X),
    <[ t, w |= p AN q ]> <-> <( t, w |= p)> /\ can_step t w /\ forall t' w', |t, w| ↦ |t',w'| -> <[ t',w' |= q ]>.
Proof. intros; auto. Qed.

Lemma ticlr_en `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ticll E) (q: ticlr E X),
    <[ t,w |= p EN q ]> <-> <( t, w |= p )> /\ exists t' w', |t,w| ↦ |t',w'| /\ <[ t',w' |= q ]>.
Proof. intros; eauto. Qed.
Global Hint Resolve ticlr_an ticlr_en: ticl.

(*| Propositional statements |*)
Lemma ticll_and  `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p q: ticll E),
    <( t, w |= p /\ q )> <-> <( t, w |= p )> /\ <( t, w |= q )>.
Proof. intros; rewrite unfold_entailsL; reflexivity. Qed.

Lemma ticll_or  `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p q: ticll E),
    <( t, w |= p \/ q )> <-> <( t, w |= p )> \/ <( t, w |= q )>.
Proof. intros; rewrite unfold_entailsL; reflexivity. Qed.

Lemma ticlr_and  `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p q: ticlr E X),
    <[ t, w |= p /\ q ]> <-> <[ t, w |= p ]> /\ <[ t, w |= q ]>.
Proof. intros; rewrite unfold_entailsR; reflexivity. Qed.

Lemma ticlr_or  `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p q: ticlr E X),
    <[ t, w |= p \/ q ]> <-> <[ t, w |= p ]> \/ <[ t, w |= q ]>.
Proof. intros; rewrite unfold_entailsR; reflexivity. Qed.

Lemma ticlr_impll  `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ticll E) (q: ticlr E X),
    <[ t, w |= p -> q ]> <-> <( t, w |= p )> -> <[ t, w |= q ]>.
Proof. intros t w p q; rewrite unfold_entailsR; intros [H H']; auto. Qed. 

(* [AN φ] is stronger than [EN φ] *)
Lemma ticll_an_en `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p q: ticll E),
    <( t, w |= p AN q )> -> <( t, w |= p EN q )>.
Proof.
  intros.
  rewrite ticll_an, ticll_en in *.
  destruct H as (Hp & (m' & w' & TR) & ?).
  split; [|exists m', w']; auto.
Qed.

(* [AF φ] is stronger than [EF φ] *)
Lemma ticll_au_eu `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p q: ticll E),
    <( t, w |= p AU q )> -> <( t, w |= p EU q )>.
Proof.
  intros.
  rewrite unfold_entailsL in *.
  induction H.
  - now apply MatchE. 
  - destruct H as (Hp & _ & ?).
    destruct H0 as (_ & (? & ? & ?) &  ?).
    apply StepE; split; auto.
    exists x, x0; split; auto.
Qed.

Lemma ticlr_an_en `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ticll E) (q: ticlr E X),
    <[ t, w |= p AN q ]> -> <[ t, w |= p EN q ]>.
Proof.
  intros.
  rewrite ticlr_an, ticlr_en in *.
  destruct H as (H & (m' & w' & TR) & ?).
  intuition.
  exists m', w'; auto.
Qed.

(* [AF φ] is stronger than [EF φ] *)
Lemma ticlr_au_eu `{KMS: Kripke M E} X:
  forall (t: M E HE X) (w: World E) (p: ticll E) (q: ticlr E X),
    <[ t, w |= p AU q ]> -> <[ t, w |= p EU q ]>.
Proof.
  intros.
  rewrite unfold_entailsR in *.
  induction H.
  - now apply MatchE. 
  - destruct H as (Hp & _ & ?).
    destruct H0 as (_ & (? & ? & ?) &  ?).
    apply StepE; split; auto.
    exists x, x0; split; auto.
Qed.

(* [AN φ] implies [AU φ] *)
Lemma ticlr_an_au `{KMS: Kripke M E} X: forall (t: M E HE X) w φ ψ,
    <[ t, w |= φ AN ψ ]> ->
    <[ t, w |= φ AU ψ ]>.
Proof.
  intros.
  rewrite ticlr_an in H.
  destruct H as (H & (m' & w' & TR) & ?).
  rewrite unfold_entailsR.
  apply StepA; split; auto.
  split.
  - now (exists m', w').
  - intros.
    apply MatchA; auto.
Qed.

Lemma ticlr_en_eu `{KMS: Kripke M E} X: forall (t: M E HE X) w φ ψ,
    <[ t, w |= φ EN ψ ]> ->
    <[ t, w |= φ EU ψ ]>.
Proof.
  intros.
  rewrite ticlr_en in H.
  destruct H as (H & (m' & w' & TR & ?)).
  rewrite unfold_entailsR.
  apply StepE; split; auto.
  exists m', w'; intuition.
Qed.
  
(*| Bot is false |*)
Lemma ticll_sound `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= ⊥ )>.
Proof. now intros * []. Qed. 

(*| Ex-falso |*)
Lemma ticlr_exfalso `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E) (p: ticlr E X),
    <[ t, w |= ⊥ -> p ]>.
Proof.
  cbn.
  intros; rewrite unfold_entailsR.
  now intros [].
Qed.

(*| Top is True |*)
Lemma ticll_top `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    not_done w -> <( t, w |= ⊤ )>.
Proof.
  intros.
  now apply ticll_now.
Qed.

Lemma ticlr_top `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    is_done X w -> <[ t, w |= ⫪ ]>.
Proof.
  intros.
  apply ticlr_done.
  inv H; now constructor.
Qed.

(*| Cannot exist path such that eventually Bot |*)
Lemma ticll_sound_ef `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= EF ⊥ )>.
Proof.
  intros * Contra.
  rewrite unfold_entailsL in Contra.
  induction Contra.
  - rewrite ticll_now in H; intuition. 
  - now destruct H as (? & ? & ? & ? & ?).
Qed.

(*| Cannot have all paths such that eventually always Bot |*)
Lemma ticll_sound_af `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <( t, w |= AF ⊥ )>.
Proof.
  intros * Contra.
  apply ticll_au_eu in Contra.
  apply ticll_sound_ef in Contra.
  contradiction.
Qed.

(*| Cannot exist path such that eventually Bot |*)
Lemma ticlr_sound_ef `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <[ t, w |= EF ⫫ ]>.
Proof.
  intros * Contra.
  rewrite unfold_entailsR in Contra.
  induction Contra.
  - rewrite ticlr_done in H; now ddestruction H.
  - now destruct H as (? & ? & ? & ? & ?).
Qed.

(*| Cannot have all paths such that eventually always Bot |*)
Lemma ticlr_sound_af `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E),
    ~ <[ t, w |= AF ⫫ ]>.
Proof.
  intros * Contra.
  apply ticlr_au_eu in Contra.
  apply ticlr_sound_ef in Contra.
  contradiction.
Qed.

Lemma anc_not_done `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E) p q,
    anc p q t w ->
    not_done w.
Proof.
  intros.
  destruct H as (? & ? & ?).
  now apply can_step_not_done with t.
Qed.

Lemma enc_not_done `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E) p q,
    enc p q t w ->
    not_done w.
Proof.
  intros.
  destruct H as (? & ? & ? & ? & ?).
  now apply ktrans_not_done with t x x0.
Qed.
Hint Resolve enc_not_done anc_not_done: ticl.

(* Here the syntax separation becomes semantically apparent *)
Lemma ticll_not_done `{KMS: Kripke M E} X: forall (t: M E HE X) (w: World E) (p: ticll E),
    <( t, w |= p )> ->
    not_done w.
Proof.
  intros.
  hinduction p before X; intros;
    rewrite unfold_entailsL in H; eauto; try destruct q; try solve [ destruct H; eauto].
  - destruct H; eauto.
    now apply anc_not_done in H. 
  - destruct H; eauto.
    now apply enc_not_done in H.
  - step in H; destruct H, H0.
    now apply can_step_not_done with t.
  - step in H; destruct H, H0 as (t' & w' & TR & ?).
    now apply ktrans_not_done with t t' w'.
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
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_A ?φ ?ψ) ?t ?w =>
      let Hau := fresh "Hau" in
      let HInd := fresh "HInd" in
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      rewrite unfold_entailsL in H0; induction H0 as [? ? Hp | ? ? Hau HInd]; 
      [| destruct Hau as (Hp & Hs & Hau), HInd as (_ & _ & HInd)]
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL Q_E ?φ ?ψ) ?t ?w =>
      let Heu := fresh "Heu" in
      let HInd := fresh "HInd" in
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite unfold_entailsL in H0; induction H0 as [? ? Hp | ? ? Heu];
      [| destruct Heu as (Hp & t' & w' & TR' & Heu & HInd)]
  | @entailsL ?M ?W ?HE ?KMS ?X (CuL ?c ?φ ?ψ) ?t ?w =>
      is_var c; destruct c; cinduction H0
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_A ?φ ?ψ) ?t ?w =>
      let Hau := fresh "Hau" in
      let HInd := fresh "HInd" in
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      rewrite unfold_entailsR in H0; induction H0 as [? ? Hp | ? ? Hau HInd]; 
      [| destruct Hau as (Hp & Hs & Hau), HInd as (_ & _ & HInd)]
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR Q_E ?φ ?ψ) ?t ?w =>
      let Hau := fresh "Hau" in
      let HInd := fresh "HInd" in
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite unfold_entailsR in H0; induction H0 as [? ? Hp | ? ? Heu];
      [| destruct Heu as (Hp & t' & w' & TR' & Heu & HInd)]
  | @entailsR ?M ?W ?HE ?KMS ?X (CuR ?c ?φ ?ψ) ?t ?w =>
      is_var c; destruct c; cinduction H0
  end.

#[global] Ltac coinduction_g R CIH :=
  let R' := fresh R in
  first [rewrite unfold_entailsL | setoid_rewrite unfold_entailsL];
  coinduction R' CIH;
  try change (agc (entailsL ?X ?p) ?t ?w) with <( t, w |= AG p )> in *;
  try change (egc (entailsL ?X ?p) ?t ?w) with <( t, w |= EG p )> in *.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  (coinduction_g R H || coinduction R H).
