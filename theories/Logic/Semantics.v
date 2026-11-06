
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

From Equations Require Import Equations.
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

  (** Select the existing next and until semantics by their quantifier. *)
  Definition qnext (q: ticlq) (p r: MP): MP :=
    match q with Q_A => anc p r | Q_E => enc p r end.

  Definition quntil (q: ticlq) (p r: MP): MP :=
    match q with Q_A => auc p r | Q_E => euc p r end.

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

  Lemma enc_mono_r (p q q': MP) :
    (forall t w, q t w -> q' t w) ->
    forall t w, enc p q t w -> enc p q' t w.
  Proof.
    intros Hqq' t w (Hp & t' & w' & TR & Hq).
    split; [exact Hp | exists t', w'; split; [exact TR | now apply Hqq']].
  Qed.

  Lemma euc_mono_r (p q q': MP) :
    (forall t w, q t w -> q' t w) ->
    forall t w, euc p q t w -> euc p q' t w.
  Proof.
    intros Hqq'.
    apply (euc_ind (fun t w => euc p q' t w)).
    - intros t w Hq; apply MatchE; now apply Hqq'.
    - intros t w (Hp & t' & w' & TR & Hsource & IH).
      apply StepE; split; [exact Hp | exists t', w'; now split].
  Qed.

  Lemma euc_endpoint_exists (p q : MP) t w :
    euc p q t w -> exists u z, q u z.
  Proof.
    intro H; refine (euc_ind (fun _ _ => exists u z, q u z) _ _ t w H).
    - intros u z Hq; exists u,z; exact Hq.
    - intros u z (_ & v & y & _ & _ & IH); exact IH.
  Qed.

  (** Weaken the guard while preserving the same finite endpoint. *)
  Lemma auc_mono_l (p p' q: MP) :
    (forall t w, p t w -> p' t w) ->
    forall t w, auc p q t w -> auc p' q t w.
  Proof.
    intros Hpp'.
    apply (auc_ind (fun t w => auc p' q t w)).
    - intros t w Hq; now apply MatchA.
    - intros t w Hstep (Hp & Hs & IH).
      apply StepA; split; [now apply Hpp' | now split].
  Qed.

  Lemma euc_mono_l (p p' q: MP) :
    (forall t w, p t w -> p' t w) ->
    forall t w, euc p q t w -> euc p' q t w.
  Proof.
    intros Hpp'.
    apply (euc_ind (fun t w => euc p' q t w)).
    - intros t w Hq; now apply MatchE.
    - intros t w (Hp & t' & w' & TR & Hsource & IH).
      apply StepE; split; [now apply Hpp' | exists t', w'; now split].
  Qed.

  (** Flatten finite until segments with the same guard. *)
  Lemma auc_join (p q: MP) :
    forall t w, auc p (auc p q) t w -> auc p q t w.
  Proof.
    apply (auc_ind (fun t w => auc p q t w)).
    - intros t w Hq; exact Hq.
    - intros t w Hstep IH; now apply StepA.
  Qed.

  Lemma euc_join (p q: MP) :
    forall t w, euc p (euc p q) t w -> euc p q t w.
  Proof.
    apply (euc_ind (fun t w => euc p q t w)).
    - intros t w Hq; exact Hq.
    - intros t w (Hp & t' & w' & TR & Hsource & IH).
      apply StepE; split; [exact Hp | exists t', w'; now split].
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

  Equations entails (X : Type) (b : bool) (p : ticl_at E X b) : MP X :=
  entails X false (CNow p) := fun _ w => p w /\ not_done w;
  entails X true (CRet p) := fun t w =>
    exists x, p x w /\
      anc (fun _ w => not_done w) (fun _ => done_of x w) t w;
  entails X b (Cu Q_A p r) := auc (entails X false p) (entails X b r);
  entails X b (Cu Q_E p r) := euc (entails X false p) (entails X b r);
  entails X b (Cx Q_A p r) := anc (entails X false p) (entails X b r);
  entails X b (Cx Q_E p r) := enc (entails X false p) (entails X b r);
  entails X false (Cg Q_A p) := agc (entails X false p);
  entails X false (Cg Q_E p) := egc (entails X false p);
  entails X b (CAnd p r) := fun t w => entails X b p t w /\ entails X b r t w;
  entails X b (COr p r) := fun t w => entails X b p t w \/ entails X b r t w.

  (** One layer only: recursive children continue to use [entails]. *)
  Equations entails_step (X : Type) (b : bool) (p : ticl_at E X b) : MP X :=
  entails_step X false (CNow p) := fun _ w => p w /\ not_done w;
  entails_step X true (CRet p) := fun t w =>
    exists x, p x w /\
      anc (fun _ w => not_done w) (fun _ => done_of x w) t w;
  entails_step X b (Cu Q_A p r) := auc (entails X false p) (entails X b r);
  entails_step X b (Cu Q_E p r) := euc (entails X false p) (entails X b r);
  entails_step X b (Cx Q_A p r) := anc (entails X false p) (entails X b r);
  entails_step X b (Cx Q_E p r) := enc (entails X false p) (entails X b r);
  entails_step X false (Cg Q_A p) := agc (entails X false p);
  entails_step X false (Cg Q_E p) := egc (entails X false p);
  entails_step X b (CAnd p r) := fun t w => entails X b p t w /\ entails X b r t w;
  entails_step X b (COr p r) := fun t w => entails X b p t w \/ entails X b r t w.

  Lemma unfold_entails : forall X b (p : ticl_at E X b) t w,
      entails X b p t w = entails_step X b p t w.
  Proof.
    intro X; apply (@ticl_at_ind E X
      (fun b p => forall t w, entails X b p t w = entails_step X b p t w));
      intros; try destruct q; reflexivity.
  Qed.
  Global Opaque entails.

  Definition entailsL (X : Type) (p : ticll E) : MP X :=
    entails X false p.
  Definition entailsR {X : Type} (p : ticlr E X) : MP X :=
    entails X true p.
End Entailment.

(* Entailment notation *)
Import TiclNotations.
Local Open Scope ticl_scope.

Notation "t , w |=L p" := (@entails _ _ _ _ _ false p t w)
  (in custom ticl at level 80, p custom ticl,
   right associativity, only printing) : ticl_scope.
Notation "t , w |=R p" := (@entails _ _ _ _ _ true p t w)
  (in custom ticl at level 80, p custom ticl,
   right associativity, only printing) : ticl_scope.
Notation "t , w |=L p" := (entailsL _ p t w)
  (in custom ticl at level 80, p custom ticl,
   right associativity) : ticl_scope.
Notation "t , w |=R p" := (entailsR p t w)
  (in custom ticl at level 80, p custom ticl,
   right associativity) : ticl_scope.

Ltac ticl_normalize := cbv beta zeta delta [entailsL entailsR].
Tactic Notation "ticl_normalize" "in" hyp(H) :=
  cbv beta zeta delta [entailsL entailsR] in H.

(** * Constructor laws, shared across modes. *)
Lemma ticl_now `{KMS : Kripke M E B} X : forall (t : M E B X) w p,
  entails X false (CNow p) t w <-> p w /\ not_done w.
Proof. reflexivity. Qed.
Lemma ticl_pure `{KMS : Kripke M E B} X : forall (t : M E B X) w,
  <( t,w |=L pure )> <-> w = Pure.
Proof. intros; ticl_normalize; rewrite ticl_now; split; [intros []; assumption | intros ->; now split; constructor]. Qed.
Lemma ticl_vis `{KMS : Kripke M E B} X : forall (t : M E B X) w p,
  <( t,w |=L vis p )> <-> vis_with p w.
Proof. intros; ticl_normalize; rewrite ticl_now; split; [intros []; assumption | intro H; split; [exact H | inv H; constructor]]. Qed.
Lemma ticl_ret `{KMS : Kripke M E B} X : forall (t : M E B X) w (p : X -> World E -> Prop),
  entails X true (CRet p) t w <-> exists x, p x w /\ anc (fun _ w => not_done w) (fun _ => done_of x w) t w.
Proof. intros; rewrite unfold_entails; reflexivity. Qed.
#[global] Hint Resolve ticl_now ticl_pure ticl_vis ticl_ret : ticl.

Lemma ticl_an `{KMS : Kripke M E B} X b : forall (t : M E B X) w (p : ticll E) (r : ticl_at E X b),
  entails X b (Cx Q_A p r) t w <-> entails X false p t w /\ can_step t w /\ forall t' w', ktrans t w t' w' -> entails X b r t' w'.
Proof. destruct b; reflexivity. Qed.

Lemma ticl_en `{KMS : Kripke M E B} X b : forall (t : M E B X) w (p : ticll E) (r : ticl_at E X b),
  entails X b (Cx Q_E p r) t w <-> entails X false p t w /\ exists t' w', ktrans t w t' w' /\ entails X b r t' w'.
Proof. destruct b; reflexivity. Qed.

Lemma ticl_au `{KMS : Kripke M E B} X b : forall (t : M E B X) w (p : ticll E) (r : ticl_at E X b),
  entails X b (Cu Q_A p r) t w <-> auc (entails X false p) (entails X b r) t w.
Proof. destruct b; reflexivity. Qed.

Lemma ticl_eu `{KMS : Kripke M E B} X b : forall (t : M E B X) w (p : ticll E) (r : ticl_at E X b),
  entails X b (Cu Q_E p r) t w <-> euc (entails X false p) (entails X b r) t w.
Proof. destruct b; reflexivity. Qed.

Lemma ticl_and `{KMS : Kripke M E B} X b : forall (t : M E B X) w (p r : ticl_at E X b),
  entails X b (CAnd p r) t w <-> entails X b p t w /\ entails X b r t w.
Proof. destruct b; reflexivity. Qed.

Lemma ticl_or `{KMS : Kripke M E B} X b : forall (t : M E B X) w (p r : ticl_at E X b),
  entails X b (COr p r) t w <-> entails X b p t w \/ entails X b r t w.
Proof. destruct b; reflexivity. Qed.

#[global] Hint Resolve ticl_an ticl_en : ticl.
Lemma ticl_an_en `{KMS : Kripke M E B} X b : forall (t : M E B X) w (p : ticll E) (r : ticl_at E X b),
  entails X b (Cx Q_A p r) t w -> entails X b (Cx Q_E p r) t w.
Proof.
  intros * H; apply ticl_an in H as (Hp & (t' & w' & TR) & Hnext).
  apply ticl_en; split; [exact Hp | exists t', w'; auto].
Qed.
Lemma ticl_au_eu `{KMS : Kripke M E B} X b : forall (t : M E B X) w (p : ticll E) (r : ticl_at E X b),
  entails X b (Cu Q_A p r) t w -> entails X b (Cu Q_E p r) t w.
Proof.
  intros * H; apply ticl_au in H; apply ticl_eu; induction H.
  - now apply MatchE.
  - destruct H as (Hp & _ & ?); destruct H0 as (_ & (t' & w' & TR) & IH).
    apply StepE; split; [exact Hp | exists t', w'; auto].
Qed.
Lemma ticl_an_au `{KMS : Kripke M E B} X b : forall (t : M E B X) w (p : ticll E) (r : ticl_at E X b),
  entails X b (Cx Q_A p r) t w -> entails X b (Cu Q_A p r) t w.
Proof.
  intros * H; apply ticl_an in H as (Hp & Hs & Hnext); apply ticl_au.
  apply StepA; split; [exact Hp | split; [exact Hs |]]; intros; apply MatchA; eauto.
Qed.
Lemma ticl_en_eu `{KMS : Kripke M E B} X b : forall (t : M E B X) w (p : ticll E) (r : ticl_at E X b),
  entails X b (Cx Q_E p r) t w -> entails X b (Cu Q_E p r) t w.
Proof.
  intros * H; apply ticl_en in H as (Hp & t' & w' & TR & Hr); apply ticl_eu.
  apply StepE; split; [exact Hp | exists t', w'; split; [exact TR | now apply MatchE]].
Qed.
Lemma unfold_entails_ag `{KMS : Kripke M E B} X : forall (t : M E B X) w p,
  entails X false (Cg Q_A p) t w = agc (entails X false p) t w.
Proof. reflexivity. Qed.
Lemma unfold_entails_eg `{KMS : Kripke M E B} X : forall (t : M E B X) w p,
  entails X false (Cg Q_E p) t w = egc (entails X false p) t w.
Proof. reflexivity. Qed.
Lemma anc_not_done `{KMS : Kripke M E B} X : forall (t : M E B X) w p q,
  anc p q t w -> not_done w.
Proof. intros * (_ & Hs & _); now apply can_step_not_done with t. Qed.
Lemma enc_not_done `{KMS : Kripke M E B} X : forall (t : M E B X) w p q,
  enc p q t w -> not_done w.
Proof. intros * (_ & t' & w' & TR & _); now apply ktrans_not_done with t t' w'. Qed.
#[global] Hint Resolve enc_not_done anc_not_done : ticl.
Lemma ticl_not_done `{KMS : Kripke M E B} X : forall b (t : M E B X) w (p : ticl_at E X b),
  entails X b p t w -> not_done w.
Proof.
  assert (H : forall b (p : ticl_at E X b) (t : M E B X) w, entails X b p t w -> not_done w).
  { apply (@ticl_at_ind E X (fun b p => forall t w, entails X b p t w -> not_done w)).
    - intros p t w H; apply ticl_now in H; tauto.
    - intros p t w H; apply ticl_ret in H as (x & _ & Hd & _); exact Hd.
    - intros b q p IHp r IHr t w H; destruct q.
      + apply ticl_au in H; destruct H as [t w Hr | t w (Hp & _)]; eauto.
      + apply ticl_eu in H; destruct H as [t w Hr | t w (Hp & _)]; eauto.
    - intros b q p IHp r IHr t w H; destruct q.
      + apply ticl_an in H as (Hp & _); eauto.
      + apply ticl_en in H as (Hp & _); eauto.
    - intros q p IHp t w H; destruct q.
      + rewrite unfold_entails_ag in H; change (agc (entails X false p) t w) in H.
        step in H; destruct H as (Hp & _); eauto.
      + rewrite unfold_entails_eg in H; change (egc (entails X false p) t w) in H.
        step in H; destruct H as (Hp & _); eauto.
    - intros b p IHp r IHr t w H; apply ticl_and in H; destruct H; eauto.
    - intros b p IHp r IHr t w H; apply ticl_or in H; destruct H; eauto. }
  intros; eauto.
Qed.

(** Native return implies a terminal postcondition after its final transition.
    The postcondition is evaluated at the unchanged predecessor world. *)
Lemma ret_done_next `{KMS: Kripke M E B} {X}
    (R : X -> World E -> Prop) (t : M E B X) w :
  entails X true (CRet R) t w ->
  anc (entails X false (CNow (fun _ => True)))
    (fun _ wd => done_with R wd) t w.
Proof.
  intros H; apply ticl_ret in H as (x & HR & Hd & Hs & Htr).
  split; [rewrite unfold_entails; now split | split; [exact Hs |]].
  intros t' w' TR; destruct (Htr t' w' TR); constructor; exact HR.
Qed.

(** Universal eventual native return includes the final value transition. *)
Lemma af_ret_done `{KMS: Kripke M E B} {X}
    (R : X -> World E -> Prop) (t : M E B X) w :
  entails X true (Cu Q_A (CNow (fun _ => True)) (CRet R)) t w ->
  auc (entails X false (CNow (fun _ => True)))
    (fun _ wd => done_with R wd) t w.
Proof.
  rewrite ticl_au; revert t w.
  apply (auc_ind (fun t w =>
    auc (entails X false (CNow (fun _ => True)))
      (fun _ wd => done_with R wd) t w)).
  - intros t w HR; apply ret_done_next in HR as (Hp & Hs & Htr).
    apply StepA; split; [exact Hp | split; [exact Hs |]].
    intros t' w' TR; apply MatchA; now apply (Htr t' w' TR).
  - intros t w Hstep IH; now apply StepA.
Qed.

(** Existential eventual native return includes one final value transition. *)
Lemma ef_ret_done `{KMS: Kripke M E B} {X}
    (R : X -> World E -> Prop) (t : M E B X) w :
  entails X true (Cu Q_E (CNow (fun _ => True)) (CRet R)) t w ->
  euc (entails X false (CNow (fun _ => True)))
    (fun _ wd => done_with R wd) t w.
Proof.
  rewrite ticl_eu; revert t w.
  apply (euc_ind (fun t w =>
    euc (entails X false (CNow (fun _ => True)))
      (fun _ wd => done_with R wd) t w)).
  - intros t w HR; apply ret_done_next in HR as (Hp & (t' & w' & TR) & Htr).
    apply StepE; split; [exact Hp | exists t', w'; split; [exact TR |]].
    apply MatchE; now apply (Htr t' w' TR).
  - intros t w (Hp & t' & w' & TR & _ & IH).
    apply StepE; split; [exact Hp | exists t', w'; now split].
Qed.


(** * Soundness of TICL formulas *)
(** Bot is false *)
Lemma ticll_sound `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    ~ <( t, w |=L ⊥ )>.
Proof. now intros * []. Qed. 

(** Prefix truth holds exactly at nonterminal worlds. *)
Lemma ticll_top `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    not_done w -> <( t, w |=L ⊤ )>.
Proof.
  intros.
  now apply ticl_now.
Qed.


(** Cannot exist path such that eventually Bot.
    This is a strong statement, it shows that [False] cannot eventually appear.
    This is contrary to partial correctness logics where [False] can appear after infinite loops. *)
Lemma ticll_sound_ef `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    ~ <( t, w |=L EF ⊥ )>.
Proof.
  intros * Contra.
  apply ticl_eu in Contra.
  induction Contra.
  - rewrite ticl_now in H; intuition. 
  - now destruct H as (? & ? & ? & ? & ?).
Qed.

(** Cannot have all paths such that eventually always Bot. *)
Lemma ticll_sound_af `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    ~ <( t, w |=L AF ⊥ )>.
Proof.
  intros * Contra.
  apply ticl_au_eu in Contra.
  apply ticll_sound_ef in Contra.
  contradiction.
Qed.

(** Cannot exist path such that eventually Bot. *)
Lemma ticlr_sound_ef `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    ~ <( t, w |=R EF ret {fun _ _ => False} )>.
Proof.
  intros * Contra.
  apply ticl_eu in Contra.
  induction Contra.
  - apply ticl_ret in H as (x & HF & _); contradiction.
  - now destruct H as (? & ? & ? & ? & ?).
Qed.

(** Cannot have all paths such that eventually always Bot. *)
Lemma ticlr_sound_af `{KMS: Kripke M E B} X: forall (t: M E B X) (w: World E),
    ~ <( t, w |=R AF ret {fun _ _ => False} )>.
Proof.
  intros * Contra.
  apply ticl_au_eu in Contra.
  apply ticlr_sound_ef in Contra.
  contradiction.
Qed.

(** Eventual terminal postconditions rule out infinite paths: every [ktrans]
    path from [t, w] is finite, whatever branch is taken. *)
Theorem af_done_accessible `{Kripke M E B} {X}
    (R : X -> World E -> Prop) (t : M E B X) (w : World E) :
  auc (entails X false (CNow (fun _ => True)))
    (fun _ wd => done_with R wd) t w -> Acc kripke_step (t, w).
Proof.
  revert t w.
  apply (auc_ind (fun t w => Acc kripke_step (t, w))).
  - intros t w Hdone; constructor; intros [u w'] TR; cbn in TR.
    apply ktrans_not_done in TR; inversion Hdone; subst; inversion TR.
  - intros t w _ (_ & _ & IH); constructor; intros [u w'] TR.
    exact (IH u w' TR).
Qed.


(** * Quotation-aware basic tactics. *)
#[global] Tactic Notation "step" "in" ident(H) :=
  ticl_normalize in H;
  (lazymatch type of H with
   | @entails ?M ?E ?B ?K ?X false (Cg ?q ?p) ?t ?w =>
       first [rewrite unfold_entails_ag in H | rewrite unfold_entails_eg in H |
         destruct q; [rewrite unfold_entails_ag in H | rewrite unfold_entails_eg in H]]; step_in H
   end || step_in H).
#[global] Ltac step :=
  ticl_normalize;
  first [lazymatch goal with
    | |- @entails ?M ?E ?B ?K ?X false (Cg ?q ?p) ?t ?w =>
        first [rewrite unfold_entails_ag | rewrite unfold_entails_eg |
          destruct q; [rewrite unfold_entails_ag | rewrite unfold_entails_eg]]; step_
    end | step_ | red; step_].
#[global] Ltac cinduction H0 :=
  ticl_normalize in H0;
  match type of H0 with
  | @entails ?M ?E ?B ?K ?X ?b (Cu Q_A ?p ?r) ?t ?w =>
      let Hau := fresh "Hau" in let HInd := fresh "HInd" in
      let Hp := fresh "Hp" in let Hs := fresh "Hs" in
      apply ticl_au in H0; induction H0 as [? ? Hp | ? ? Hau HInd];
      [| destruct Hau as (Hp & Hs & Hau), HInd as (_ & _ & HInd)]
  | @entails ?M ?E ?B ?K ?X ?b (Cu Q_E ?p ?r) ?t ?w =>
      let Heu := fresh "Heu" in let HInd := fresh "HInd" in
      let Hp := fresh "Hp" in let Hs := fresh "Hs" in
      let t' := fresh "t" in let w' := fresh "w" in let TR' := fresh "TR" in
      apply ticl_eu in H0; induction H0 as [? ? Hp | ? ? Heu];
      [| destruct Heu as (Hp & t' & w' & TR' & Heu & HInd)]
  | @entails ?M ?E ?B ?K ?X ?b (Cu ?q ?p ?r) ?t ?w =>
      is_var q; destruct q; cinduction H0
  end.
#[global] Ltac coinduction_g R CIH :=
  ticl_normalize;
  let R' := fresh R in
  repeat setoid_rewrite unfold_entails_ag;
  repeat setoid_rewrite unfold_entails_eg;
  match goal with
  | |- context [gfp ?b] =>
      pattern (gfp b); apply gfp_prop; intro R'; apply_ptower R' O; intros CIH
  end;
  repeat match goal with H : _ |- _ =>
    progress (first [setoid_rewrite <- unfold_entails_ag in H |
      setoid_rewrite <- unfold_entails_eg in H])
  end;
  repeat setoid_rewrite <- unfold_entails_ag;
  repeat setoid_rewrite <- unfold_entails_eg.
#[global] Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  (coinduction_g R H || coinduction R H).
