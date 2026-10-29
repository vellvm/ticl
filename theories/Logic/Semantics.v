
(*|
=========================================
Modal logics over kripke semantics
=========================================
|*)
From Stdlib Require Import
  Basics
  FunctionalExtensionality
  Classes.RelationPairs.

From Coinduction Require Import all.

From ExtLib Require Import
  Structures.Monad.

From TICL Require Import
  Events.WriterE
  Utils.Utils
  Logic.Kripke.

From TICL Require Export Logic.Syntax.

Generalizable All Variables.

(** * TICL logic shallow embedding, based on kripke semantics *)
(** We define Ticl as a shallow embedding over a Kripke model [M] parametrized by an event type [E].
    The embedding is based on the Kripke semantics of Ticl.
    The embedding is shallow, meaning we use the metalanguage of the Rocq proof assistant
    to define base predicates (e.g., [MP]) and predicate transformers (e.g., [anc], [enc], [auc], [euc], [agc], [egc]),
    that take a prediate [MP] and put it under a modality, giving a new predicate [MP].
    
    In this section we give the formal meaning of the Ticl formulas.
    *)
Section Shallow.
  Context `{KMS: Kripke M E B} {X: Type}.

  Abbreviation MS := (M E B X).
  Abbreviation MP := (MS -> World E -> Prop).
  Local Open Scope ticl_scope.

  (** ** Binary shallow forall [next] modality *)
  (** [anc] says that [p] holds now, [q] holds next, the tree [t] and world [w] must have at least one transition [can_step t w].
      Furthermore, for all transitions [|t,w| ↦ |t', w'|], [q] must hold.
  *)
  Definition anc (p q: MP) (t: MS) (w: World E): Prop :=
    p t w /\
      can_step t w /\
      (forall t' w', |t,w| ↦ |t', w'| -> q t' w').
  
  (** ** Binary shallow exists [next] modality *)
  (** [enc] says that [p] holds now, [q] holds next, the tree [t] and world [w] must have at least one transition [|t,w| ↦ |t', w'|],
      and [q] must hold for the transition.
  *)
  Definition enc(p q: MP) (t: MS) (w: World E): Prop :=
    p t w /\
      exists t' w', |t, w| ↦ |t', w'| /\ q t' w'.
  Hint Unfold anc enc: core.

  Unset Elimination Schemes.

  (** ** Forall strong until *)
  (** [auc] is simply the least fixpoint of [anc]. 
      In the base case, [auc p q t w] says that [q] holds now.
      In the inductive case, [auc p q t w] says that [anc p (auc p q) t w] holds,
      meaning [p] holds now and [auc p q] holds next.

      As this is an inductive predicate, there are a finite number of constructors, so this is a well-founded definition.
    *)
  Inductive auc (p q: MP): MP :=
  | MatchA: forall t w,       
      q t w ->    (* Matches [q] now; done *)
      auc p q t w
  | StepA:  forall t w,
      anc p (auc p q) t w -> (* Matches [p] now; steps to [m'] *)
      auc p q t w.

  (** ** Exists strong until *)
  (** [euc] is simply the least fixpoint of [enc]. 
      In the base case, [euc p q t w] says that [q] holds now.
      In the inductive case, [euc p q t w] says that [enc p (euc p q) t w] holds,
      meaning [p] holds now and [euc p q] holds next.

      As this is an inductive predicate, there are a finite number of constructors, so this is a well-founded definition.
    *)
  Inductive euc(p q: MP): MP :=
  | MatchE: forall t w,
      q t w ->    (* Matches [q] now; done *)
      euc p q t w
  | StepE: forall t w,
      enc p (euc p q) t w -> (* Matches [p] now; steps to [m'] *)
      euc p q t w.

  (** ** Custom induction schemes for [auc, euc] *)
  (** [auc_ind] is the custom induction scheme for [auc].
      It is used to prove properties about [auc] by induction on the structure of the [auc] predicate.

      Rocq has a hard time generating induction schemes under quantifiers (e.g., [forall t w, ...], [exists t w, ...]),
      so we define our own induction schemes here.
  *)
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

  (** [euc_ind] is the custom induction scheme for [euc].
      It is used to prove properties about [euc] by induction on the structure of the [euc] predicate.
  *)
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

  (** Map only the successor predicate, preserving prefix and progress. *)
  Lemma anc_mono_r (p q q' : MP) :
    (forall t w, q t w -> q' t w) ->
    forall t w, anc p q t w -> anc p q' t w.
  Proof.
    intros Hqq' t w (Hp & Hs & Htr).
    split; [exact Hp | split; [exact Hs |]].
    intros t' w' TR; apply Hqq'; now apply (Htr t' w' TR).
  Qed.

  (** Map until leaves without changing its prefix or transition evidence. *)
  Lemma auc_mono_r (p q q' : MP) :
    (forall t w, q t w -> q' t w) ->
    forall t w, auc p q t w -> auc p q' t w.
  Proof.
    intros Hqq'.
    apply (auc_ind (fun t w => auc p q' t w)).
    - intros t w Hq; apply MatchA; now apply Hqq'.
    - intros t w Hstep IH; now apply StepA.
  Qed.

  Arguments impl /.  

  (** ** Forall Always modality (AG) *)
  (** [agcF] is a monotone endomorphism used to define [agc], the greatest fixpoint of [anc].
      Intuitively [p] must hold now and [agc p] must hold next, to infinitely many steps. *)
  Program Definition agcF p: mon MP :=
    {| body := anc p |}.
  Next Obligation.
    repeat red; intros; destruct H0; split; destruct H1; auto.
  Qed.

  (** ** Exists Always modality (EG) *)
  (** [egcF] is a monotone endomorphism used to define [egc], the greatest fixpoint of [enc].
      Intuitively [p] must hold now and [egc p] must hold next, to infinitely many steps. *)
  Program Definition egcF p: mon MP :=
    {| body := enc p |}.
  Next Obligation.
    repeat red; intros; destruct H0 as [H0 (t' & w' & TR & Hx)]; split; auto.
    exists t', w'; auto.
  Qed.      

End Shallow.

Register Scheme auc_ind as ind_nodep for auc.
Register Scheme euc_ind as ind_nodep for euc.

(** Greatest fixpoint notations *)
Abbreviation agc p   := (gfp (agcF p)).
Abbreviation egc p   := (gfp (egcF p)).
#[global] Hint Constructors euc auc: ticl.

(** * Semantics of TICL entailment *)
(** We define the semantics of TICL entailment as a fixpoint over the structure of the TICL formulas. *)
Section Entailment.
  Context `{KMS: Kripke M E B}.
  Abbreviation MS X := (M E B X).
  Abbreviation MP X := (M E B X -> World E -> Prop).

  (** ** Semantics of TICL prefix formulas *)
  (** [entailsL] is the semantics of TICL prefix formulas, denoted to [MP X], a predicate over [M E B X * World E]
      in the metalanguage of the Rocq proof assistant.
  *)
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

  (** ** Semantics of TICL suffix formulas *)
  (** [entailsR] is the semantics of TICL suffix formulas, denoted to [MP X], a predicate over [M E B X * World E]
      in the metalanguage of the Rocq proof assistant.
  *)
  Definition entailsR {X}: ticlr E X -> MP X := 
    fix entailsR (φ: ticlr E X): MP X :=
      match φ with
      | (CRet φ) => fun t w => exists x, φ x w /\ anc (fun _ w => not_done w) (fun _ => done_of x w) t w
      | (CuR Q_A p q) => auc (entailsL X p) (entailsR q)
      | (CuR Q_E p q) => euc (entailsL X p) (entailsR q)
      | (CxR Q_A p q) => anc (entailsL X p) (entailsR q)
      | (CxR Q_E p q) => enc (entailsL X p) (entailsR q)
      | (CAndR p q) => fun t w => entailsR p t w /\ entailsR q t w
      | (COrR p q) => fun t w => entailsR p t w \/ entailsR q t w
      end.

  (** ** Unfolding of [entailsL]. 
  This is defined in anger, because Rocq's evaluation [cbn] and [cbv] has a hard time figuring out when to stop. *)
  Lemma unfold_entailsL {X}: forall (t: M E B X) (w: World E) (φ: ticll E),
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

  (** ** Unfolding of [entailsR]. *) 
  Lemma unfold_entailsR {X}: forall (t: M E B X) (w: World E) (φ: ticlr E X),
      entailsR φ t w = match φ with
                       | (CRet φ) => exists x, φ x w /\ anc (fun _ w => not_done w) (fun _ => done_of x w) t w
                       | (CuR Q_A p q) => auc (entailsL X p) (entailsR q) t w
                       | (CuR Q_E p q) => euc (entailsL X p) (entailsR q) t w
                       | (CxR Q_A p q) => anc (entailsL X p) (entailsR q) t w
                       | (CxR Q_E p q) => enc (entailsL X p) (entailsR q) t w
                       | (CAndR p q) => entailsR p t w /\ entailsR q t w
                       | (COrR p q) => entailsR p t w \/ entailsR q t w
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

(** * Base constructors of logical formulas and some basic equivalences. *)
Lemma ticll_now `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (φ: World E -> Prop),
    <( t, w |= now φ )> <-> φ w /\ not_done w.
Proof. reflexivity. Qed.
Create HintDb ticll.
Global Hint Resolve ticll_now: ticll.

Lemma ticll_pure `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E),
    <( t, w |= pure )> <-> w = Pure.
Proof.
  intros; split; intros. 
  - now destruct H.
  - subst; split; now constructor. 
Qed.
Global Hint Resolve ticll_pure: ticll.

Lemma ticll_vis `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) φ,
    <( t, w |= vis φ )> <-> vis_with φ w.
Proof.
  intros; split; intros.
  - now destruct H.
  - split; inv H; now constructor. 
Qed.
Global Hint Resolve ticll_vis: ticll.

Create HintDb ticlr.

Lemma ticlr_ret `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (φ: X -> World E -> Prop),
    <[ t, w |= ret φ ]> <-> exists x, φ x w /\ anc (fun _ w => not_done w) (fun _ => done_of x w) t w.
Proof. intros; rewrite unfold_entailsR; reflexivity. Qed.
Global Hint Resolve ticlr_ret: ticlr.

(** Native return implies a terminal postcondition after its final transition.
    The postcondition is evaluated at the unchanged predecessor world. *)
Lemma ret_done_next `{KMS: Kripke M E B} {X}
    (R : X -> World E -> Prop) (t : M E B X) w :
  entailsR (CRet R) t w ->
  anc (entailsL X (CNow (fun _ => True)))
    (fun _ wd => done_with R wd) t w.
Proof.
  intros H; apply ticlr_ret in H as (x & HR & Hd & Hs & Htr).
  split; [rewrite unfold_entailsL; now split | split; [exact Hs |]].
  intros t' w' TR; destruct (Htr t' w' TR); constructor; exact HR.
Qed.

(** Universal eventual native return includes the final value transition. *)
Lemma af_ret_done `{KMS: Kripke M E B} {X}
    (R : X -> World E -> Prop) (t : M E B X) w :
  entailsR (CuR Q_A (CNow (fun _ => True)) (CRet R)) t w ->
  auc (entailsL X (CNow (fun _ => True)))
    (fun _ wd => done_with R wd) t w.
Proof.
  rewrite unfold_entailsR; revert t w.
  apply (auc_ind (fun t w =>
    auc (entailsL X (CNow (fun _ => True)))
      (fun _ wd => done_with R wd) t w)).
  - intros t w HR; apply ret_done_next in HR as (Hp & Hs & Htr).
    apply StepA; split; [exact Hp | split; [exact Hs |]].
    intros t' w' TR; apply MatchA; now apply (Htr t' w' TR).
  - intros t w Hstep IH; now apply StepA.
Qed.

(** Existential eventual native return includes one final value transition. *)
Lemma ef_ret_done `{KMS: Kripke M E B} {X}
    (R : X -> World E -> Prop) (t : M E B X) w :
  entailsR (CuR Q_E (CNow (fun _ => True)) (CRet R)) t w ->
  euc (entailsL X (CNow (fun _ => True)))
    (fun _ wd => done_with R wd) t w.
Proof.
  rewrite unfold_entailsR; revert t w.
  apply (euc_ind (fun t w =>
    euc (entailsL X (CNow (fun _ => True)))
      (fun _ wd => done_with R wd) t w)).
  - intros t w HR; apply ret_done_next in HR as (Hp & (t' & w' & TR) & Htr).
    apply StepE; split; [exact Hp | exists t', w'; split; [exact TR |]].
    apply MatchE; now apply (Htr t' w' TR).
  - intros t w (Hp & t' & w' & TR & _ & IH).
    apply StepE; split; [exact Hp | exists t', w'; now split].
Qed.

(*| AN, WX, EN unfold |*)
Lemma ticll_an `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p q: ticll E),
    <( t, w |= p AN q )> <-> <( t, w |= p)> /\ can_step t w /\ forall t' w', |t, w| ↦ |t',w'| -> <( t',w' |= q )>.
Proof. intros; auto. Qed.

Lemma ticll_en `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p q: ticll E),
    <( t,w |= p EN q )> <-> <( t, w|= p)> /\ exists t' w', |t,w| ↦ |t',w'| /\ <( t',w' |= q )>.
Proof. intros; auto. Qed.
Global Hint Resolve ticll_an ticll_en: ticl.

Lemma ticlr_an `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p: ticll E) (q: ticlr E X),
    <[ t, w |= p AN q ]> <-> <( t, w |= p)> /\ can_step t w /\ forall t' w', |t, w| ↦ |t',w'| -> <[ t',w' |= q ]>.
Proof. intros; auto. Qed.

Lemma ticlr_en `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p: ticll E) (q: ticlr E X),
    <[ t,w |= p EN q ]> <-> <( t, w |= p )> /\ exists t' w', |t,w| ↦ |t',w'| /\ <[ t',w' |= q ]>.
Proof. intros; eauto. Qed.
Global Hint Resolve ticlr_an ticlr_en: ticl.

(*| Propositional statements |*)
Lemma ticll_and  `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p q: ticll E),
    <( t, w |= p /\ q )> <-> <( t, w |= p )> /\ <( t, w |= q )>.
Proof. intros; rewrite unfold_entailsL; reflexivity. Qed.

Lemma ticll_or  `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p q: ticll E),
    <( t, w |= p \/ q )> <-> <( t, w |= p )> \/ <( t, w |= q )>.
Proof. intros; rewrite unfold_entailsL; reflexivity. Qed.

Lemma ticlr_and  `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p q: ticlr E X),
    <[ t, w |= p /\ q ]> <-> <[ t, w |= p ]> /\ <[ t, w |= q ]>.
Proof. intros; rewrite unfold_entailsR; reflexivity. Qed.

Lemma ticlr_or  `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p q: ticlr E X),
    <[ t, w |= p \/ q ]> <-> <[ t, w |= p ]> \/ <[ t, w |= q ]>.
Proof. intros; rewrite unfold_entailsR; reflexivity. Qed.

(** [AN φ] is stronger than [EN φ] *)
Lemma ticll_an_en `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p q: ticll E),
    <( t, w |= p AN q )> -> <( t, w |= p EN q )>.
Proof.
  intros.
  rewrite ticll_an, ticll_en in *.
  destruct H as (Hp & (m' & w' & TR) & ?).
  split; [|exists m', w']; auto.
Qed.

(** [AF φ] is stronger than [EF φ] *)
Lemma ticll_au_eu `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p q: ticll E),
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

Lemma ticlr_an_en `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p: ticll E) (q: ticlr E X),
    <[ t, w |= p AN q ]> -> <[ t, w |= p EN q ]>.
Proof.
  intros.
  rewrite ticlr_an, ticlr_en in *.
  destruct H as (H & (m' & w' & TR) & ?).
  intuition.
  exists m', w'; auto.
Qed.

(** [AF φ] is stronger than [EF φ] *)
Lemma ticlr_au_eu `{KMS: Kripke M E B} X:
  forall (t: M E B X) (w: World E) (p: ticll E) (q: ticlr E X),
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

(** [AN φ] implies [AU φ] *)
Lemma ticlr_an_au `{KMS: Kripke M E B} X: forall (t: M E B X) w φ ψ,
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

Lemma ticlr_en_eu `{KMS: Kripke M E B} X: forall (t: M E B X) w φ ψ,
    <[ t, w |= φ EN ψ ]> ->
    <[ t, w |= φ EU ψ ]>.
Proof.
  intros.
  rewrite ticlr_en in H.
  destruct H as (H & (m' & w' & TR & ?)).
  rewrite unfold_entailsR.
  apply StepE; split; auto.
  exists m', w'; split; auto.
  now apply MatchE.
Qed.
  
(** * Soundness of TICL formulas *)
(** Bot is false *)
Lemma ticll_sound `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    ~ <( t, w |= ⊥ )>.
Proof. now intros * []. Qed. 

(** Prefix truth holds exactly at nonterminal worlds. *)
Lemma ticll_top `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    not_done w -> <( t, w |= ⊤ )>.
Proof.
  intros.
  now apply ticll_now.
Qed.


(** Cannot exist path such that eventually Bot.
    This is a strong statement, it shows that [False] cannot eventually appear.
    This is contrary to partial correctness logics where [False] can appear after infinite loops. *)
Lemma ticll_sound_ef `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    ~ <( t, w |= EF ⊥ )>.
Proof.
  intros * Contra.
  rewrite unfold_entailsL in Contra.
  induction Contra.
  - rewrite ticll_now in H; intuition. 
  - now destruct H as (? & ? & ? & ? & ?).
Qed.

(** Cannot have all paths such that eventually always Bot. *)
Lemma ticll_sound_af `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    ~ <( t, w |= AF ⊥ )>.
Proof.
  intros * Contra.
  apply ticll_au_eu in Contra.
  apply ticll_sound_ef in Contra.
  contradiction.
Qed.

(** Cannot exist path such that eventually Bot. *)
Lemma ticlr_sound_ef `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    ~ <[ t, w |= EF ret {fun _ _ => False} ]>.
Proof.
  intros * Contra.
  rewrite unfold_entailsR in Contra.
  induction Contra.
  - apply ticlr_ret in H as (x & HF & _); contradiction.
  - now destruct H as (? & ? & ? & ? & ?).
Qed.

(** Cannot have all paths such that eventually always Bot. *)
Lemma ticlr_sound_af `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    ~ <[ t, w |= AF ret {fun _ _ => False} ]>.
Proof.
  intros * Contra.
  apply ticlr_au_eu in Contra.
  apply ticlr_sound_ef in Contra.
  contradiction.
Qed.

(** Eventual terminal postconditions rule out infinite paths: every [ktrans]
    path from [t, w] is finite, whatever branch is taken. *)
Theorem af_done_accessible `{Kripke M E B} {X}
    (R : X -> World E -> Prop) (t : M E B X) (w : World E) :
  auc (entailsL X (CNow (fun _ => True)))
    (fun _ wd => done_with R wd) t w -> Acc kripke_step (t, w).
Proof.
  revert t w.
  apply (auc_ind (fun t w => Acc kripke_step (t, w))).
  - intros t w Hdone; constructor; intros [u w'] TR; cbn in TR.
    apply ktrans_not_done in TR; inversion Hdone; subst; inversion TR.
  - intros t w _ (_ & _ & IH); constructor; intros [u w'] TR.
    exact (IH u w' TR).
Qed.

Lemma anc_not_done `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E) p q,
    anc p q t w ->
    not_done w.
Proof.
  intros.
  destruct H as (? & ? & ?).
  now apply can_step_not_done with t.
Qed.

Lemma enc_not_done `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E) p q,
    enc p q t w ->
    not_done w.
Proof.
  intros.
  destruct H as (? & ? & ? & ? & ?).
  now apply ktrans_not_done with t x x0.
Qed.
Hint Resolve enc_not_done anc_not_done: ticl.

(** * Prefix formulas hold for [not_done] worlds *)
(** Prefix atoms carry nonterminal evidence, preserved by their temporal rules. *)
Lemma ticll_not_done `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E) (p: ticll E),
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

(** * Basic tactics *)
(** More automated ones defined in [Tactics.v] after [Congruence.v] *)
#[global] Tactic Notation "step" "in" ident(H) :=
  (lazymatch type of H with
   | @entailsL ?M ?E ?B ?KMS ?X (Cg ?q ?φ) ?t ?w =>
       rewrite unfold_entailsL in H; step_in H
   end || step_in H).

#[global] Ltac step :=
  first [
      lazymatch goal with
      | |- @entailsL ?M ?E ?B ?KMS ?X (Cg ?q ?φ) ?t ?w =>
          rewrite unfold_entailsL; step_
      end | step_ | red; step_ ].

#[global] Ltac cinduction H0 :=
  match type of H0 with
  | @entailsL ?M ?E ?B ?KMS ?X (CuL Q_A ?φ ?ψ) ?t ?w =>
      let Hau := fresh "Hau" in
      let HInd := fresh "HInd" in
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      rewrite unfold_entailsL in H0; induction H0 as [? ? Hp | ? ? Hau HInd]; 
      [| destruct Hau as (Hp & Hs & Hau), HInd as (_ & _ & HInd)]
  | @entailsL ?M ?E ?B ?KMS ?X (CuL Q_E ?φ ?ψ) ?t ?w =>
      let Heu := fresh "Heu" in
      let HInd := fresh "HInd" in
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite unfold_entailsL in H0; induction H0 as [? ? Hp | ? ? Heu];
      [| destruct Heu as (Hp & t' & w' & TR' & Heu & HInd)]
  | @entailsL ?M ?E ?B ?KMS ?X (CuL ?c ?φ ?ψ) ?t ?w =>
      is_var c; destruct c; cinduction H0
  | @entailsR ?M ?E ?B ?KMS ?X (CuR Q_A ?φ ?ψ) ?t ?w =>
      let Hau := fresh "Hau" in
      let HInd := fresh "HInd" in
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      rewrite unfold_entailsR in H0; induction H0 as [? ? Hp | ? ? Hau HInd]; 
      [| destruct Hau as (Hp & Hs & Hau), HInd as (_ & _ & HInd)]
  | @entailsR ?M ?E ?B ?KMS ?X (CuR Q_E ?φ ?ψ) ?t ?w =>
      let Hau := fresh "Hau" in
      let HInd := fresh "HInd" in
      let Hp := fresh "Hp" in
      let Hs := fresh "Hs" in
      let t' := fresh "t" in
      let w' := fresh "w" in
      let TR' := fresh "TR" in
      rewrite unfold_entailsR in H0; induction H0 as [? ? Hp | ? ? Heu];
      [| destruct Heu as (Hp & t' & w' & TR' & Heu & HInd)]
  | @entailsR ?M ?E ?B ?KMS ?X (CuR ?c ?φ ?ψ) ?t ?w =>
      is_var c; destruct c; cinduction H0
  end.

(** Unfold only the [AG]/[EG] heads, leaving the other connectives alone.
    Used by [coinduction] to expose the [gfp] under binders. *)
Lemma unfold_entailsL_ag `{KMS: Kripke M E B} X: forall (t: M E B X) w φ,
    <( t, w |= AG φ )> = agc (entailsL X φ) t w.
Proof. intros; now rewrite unfold_entailsL. Qed.

Lemma unfold_entailsL_eg `{KMS: Kripke M E B} X: forall (t: M E B X) w φ,
    <( t, w |= EG φ )> = egc (entailsL X φ) t w.
Proof. intros; now rewrite unfold_entailsL. Qed.

(** [coinduction R CIH] on a goal [forall ..., H -> <( t, w |= AG φ )>].
    The [gfp] of the conclusion is found by backtracking over the [gfp]
    occurrences of the goal: [gfp_prop] + [apply_ptower] only succeed when the
    abstracted [gfp] is the one in head position of the conclusion. *)
#[global] Ltac coinduction_g R CIH :=
  let R' := fresh R in
  first [rewrite unfold_entailsL | setoid_rewrite unfold_entailsL | idtac];
  repeat setoid_rewrite unfold_entailsL_ag;
  repeat setoid_rewrite unfold_entailsL_eg;
  match goal with
  | |- context [gfp ?b] =>
      pattern (gfp b); apply gfp_prop; intro R'; apply_ptower R' O; intros CIH
  end;
  try change (agc (entailsL ?X ?p) ?t ?w) with <( t, w |= AG p )> in *;
  try change (egc (entailsL ?X ?p) ?t ?w) with <( t, w |= EG p )> in *.

#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  (coinduction_g R H || coinduction R H).
