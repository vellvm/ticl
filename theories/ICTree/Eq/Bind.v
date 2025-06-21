From Stdlib Require Import
     Basics
     Program.Equality
     Classes.SetoidClass
     Classes.RelationPairs
     Vectors.Fin.

From Coinduction Require Import
     coinduction rel tactics.

From TICL Require Import
  ICTree.Core
  Events.Core
  ICTree.Eq.Core
  Utils.Utils.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

Generalizable All Variables.

(*| Up-to bind principle (unary) |*)
Section Bind_ctx1.
  Context {E:Type} `{HE: Encode E} {X Y: Type}.

  Definition bind_ctx1 (R: ictree E X -> Prop) (S: (X -> ictree E Y) -> Prop):
    ictree E Y -> Prop :=
    (sup R
       (fun x => sup S
                (fun k => (fun t => t = bind x k)))).
    
  Lemma leq_bind_ctx1:
    forall R S S', @bind_ctx1 R S <= S' <->
                (forall x, R x -> forall k, S k -> S' (bind x k)).
  Proof.
    intros. unfold bind_ctx1.
    setoid_rewrite sup_spec.
    setoid_rewrite sup_spec.
    firstorder congruence.
  Qed.
  
  Lemma in_bind_ctx1 (R : ictree E X -> Prop) (S : (X -> ictree E Y) -> Prop) x f :
    R x -> S f -> @bind_ctx1 R S (bind x f).
  Proof. intros. epose proof (proj1 (leq_bind_ctx1 R S _)). apply H1; auto. Qed.

  #[global] Opaque bind_ctx1.
End Bind_ctx1.

(*|
Up-to bind principle (binary)
~~~~~~~~~~~~~~~~~~~~
Consider two computations explicitely built as sequences
[t >>= k] and [u >>= l]. When trying to prove that they are
bisimilar via a coinductive proof, one is faced with a goal
of the shape:
[t_equ RR r (t >>= k) (u >>= l)]
One can of course case analysis on the structure of [t] and [u]
to make progress in the proof.
But if we know from another source that [t ≅ u], we would like
to be able to simply "match" these prefixes, and continue the
coinductive proof over the continuations.
Such a reasoning is dubbed "up-to bind" reasoning, which we
prove sound in the following.

More formally, this corresponds as always to establishing that
the appropriate function is a valid enhancement. The function
in question here is:
f R = {(bind t k, bind u l) | equ SS t u /\ forall x y, SS x y -> R (k x) (l x)}

|*)

Section Bind_ctx2.
  Context {E F :Type} `{HE: Encode E} `{HF: Encode F} {X X' Y Y': Type}.

  (*|
Most general contextualisation function associated to bind].
Can be read more digestly as, where R is a relation on ictrees
(the prefixes of the binds) and S on the continuations:
bind_ctx2 R S = {(bind t k, bind t' k') | R t t' /\ S k k'}

Note that at this point, this is more general that what we are
interested in: we will specialize [R] and [S] for our purpose,
first here w.r.t. to [equ], later w.r.t. to other relations over
[ictree]s.

Remark: the Coinduction library provides generic binary contexts
[binary_ctx], but whose both arguments are at the same types.
We could provide an heterogeneous version of [binary_ctx] and have
[bind_ctx] be an instance of it to avoid having to rethink in terms
of [sup_all] locally.
|*)

  Definition bind_ctx2
    (R: rel (ictree E X) (ictree F X'))
    (S: rel (X -> ictree E Y) (X' -> ictree F Y')):
    rel (ictree E Y) (ictree F Y') :=
    sup_all (fun x => sup (R x)
                     (fun x' => sup_all
                               (fun k => sup (S k)
                                        (fun k' =>
                                           pairH (bind x k) (bind x' k'))))).

  (*|
Two lemmas to interact with [bind_ctx] before making it opaque:
- [leq_bind_ctx] specifies relations above the context
- [in_bind_ctx] specifies how to populate it
|*)
  Lemma leq_bind_ctx2:
    forall R S S', bind_ctx2 R S <= S' <->
                (forall x x', R x x' -> forall k k', S k k' -> S' (bind x k) (bind x' k')).
  Proof.
    intros.
    unfold bind_ctx2.
    setoid_rewrite sup_all_spec.
    setoid_rewrite sup_spec.
    setoid_rewrite sup_all_spec.
    setoid_rewrite sup_spec.
    setoid_rewrite <-leq_pairH.
    firstorder.
  Qed.

  Lemma in_bind_ctx2 (R S :rel _ _) x x' y y':
    R x x' -> S y y' -> bind_ctx2 R S (bind x y) (bind x' y').
  Proof. intros. now apply ->leq_bind_ctx2. Qed.
  #[global] Opaque bind_ctx2.

End Bind_ctx2.

(*|
Specialization of [bind_ctx2] to the [equ]-based closure we are
looking for, and the proof of validity of the principle. As
always with the companion, we prove that it is valid by proving
that it si below the companion.
|*)


(*|
Specialization of [bind_ctx2] to the [equ]-based closure we are
looking for, and the proof of validity of the principle. As
always with the companion, we prove that it is valid by proving
that it si below the companion.
|*)
Section Equ_bind_ctx.

  Context `{HE: Encode E} {X1 X2 Y1 Y2: Type}.

  (*|
Specialization of [bind_ctx2] to a function acting with [equ] on the bound value,
and with the argument (pointwise) on the continuation.
|*)
  Program Definition bind_ctx_equ r: mon (rel (ictree E Y1) (ictree E Y2)) :=
    {|body := fun R => @bind_ctx2 E E HE HE X1 X2 Y1 Y2 (equ r) (pointwise r R) |}.
  Next Obligation.
    repeat red; intros.
    apply (@leq_bind_ctx2 E E HE HE X1 X2 Y1 Y2 (equ r) (pointwise r x)).
    intros ?? H' ?? H''.
    apply in_bind_ctx2. apply H'. intros t t' HS. apply H, H'', HS.
    apply H0.
  Qed.

  (*| The resulting enhancing function gives a valid up-to technique |*)
  Lemma bind_ctx_equ_t (SS : rel X1 X2) (RR : rel Y1 Y2): bind_ctx_equ SS <= et RR.
  Proof.
    apply Coinduction. intros R. apply (leq_bind_ctx2 _).
    intros x x' xx' k k' kk'.
    step in xx'.
    cbn; unfold observe; cbn.
    destruct xx'.
    - cbn in *.
      generalize (kk' _ _ H).
      apply (fequ RR).
      apply id_T.
    - constructor; intros ?. apply (fTf_Tf (fequ _)).
      apply in_bind_ctx2. apply H.
      red; intros. apply (b_T (fequ _)), kk'; auto.
    - constructor. apply (fTf_Tf (fequ _)).
      apply in_bind_ctx2. apply H.
      red; intros. apply (b_T (fequ _)), kk'; auto.
    - constructor. intro a. apply (fTf_Tf (fequ _)).
      apply in_bind_ctx2. apply H.
      red; intros. apply (b_T (fequ _)), kk'; auto.
  Qed.

End Equ_bind_ctx.


(*|
Expliciting the reasoning rule provided by the up-to principle.
|*)

Lemma et_clo_bind `{HE: Encode E} (X1 X2 Y1 Y2 : Type) :
	forall (t1 : ictree E X1) (t2 : ictree E X2) (k1 : X1 -> ictree E Y1) (k2 : X2 -> ictree E Y2)
    (S : rel X1 X2) (R : rel Y1 Y2) RR,
		equ S t1 t2 ->
    (forall x1 x2, S x1 x2 -> et R RR (k1 x1) (k2 x2)) ->
    et R RR (bind t1 k1) (bind t2 k2)
.
Proof.
  intros.
  apply (ft_t (bind_ctx_equ_t S R)).
  now apply in_bind_ctx2.
Qed.

Lemma et_clo_bind_eq `{HE: Encode E} (X Y1 Y2 : Type) :
	forall (t : ictree E X) (k1 : X -> ictree E Y1) (k2 : X -> ictree E Y2)
    (R : rel Y1 Y2) RR,
    (forall x, et R RR (k1 x) (k2 x)) ->
    et R RR (bind t k1) (bind t k2)
.
Proof.
  intros * EQ.
  apply (ft_t (bind_ctx_equ_t (X2 := X) eq R)).
  apply in_bind_ctx2.
  reflexivity.
  intros ? ? <-.
  apply EQ.
Qed.

(*|
And in particular, we get the proper instance justifying rewriting [equ]
to the left of a [bind].
|*)
#[global] Instance bind_equ_cong :
 forall `{HE: Encode E} (X Y : Type) (R : rel Y Y) RR,
   Proper (equ (@eq X) ==> pointwise_relation X (et R RR) ==> et R RR) (@bind E HE X Y).
Proof.
  repeat red. intros.
  eapply et_clo_bind; eauto.
  intros ? ? <-; auto.
Qed.

(*|
Specializing these congruence lemmas at the [sbisim] level for equational proofs
|*)
Lemma equ_clo_bind `{HE: Encode E} (X1 X2 Y1 Y2 : Type) :
	forall (t1 : ictree E X1) (t2 : ictree E X2) (k1 : X1 -> ictree E Y1) (k2 : X2 -> ictree E Y2)
    (S : rel X1 X2) (R : rel Y1 Y2),
		equ S t1 t2 ->
    (forall x1 x2, S x1 x2 -> equ R (k1 x1) (k2 x2)) ->
    equ R (bind t1 k1) (bind t2 k2)
.
Proof.
  intros.
  apply (ft_t (bind_ctx_equ_t S R)).
  now apply in_bind_ctx2.
Qed.

Lemma equ_clo_bind_eq `{HE: Encode E} (X Y1 Y2 : Type) :
	forall (t : ictree E X) (k1 : X -> ictree E Y1) (k2 : X -> ictree E Y2)
    (R : rel Y1 Y2),
    (forall x, equ R (k1 x) (k2 x)) ->
    equ R (bind t k1) (bind t k2).
Proof.
  intros * EQ.
  apply (ft_t (bind_ctx_equ_t (X2 := X) eq R)).
  apply in_bind_ctx2.
  reflexivity.
  intros ? ? <-.
  apply EQ.
Qed.

Ltac __upto_bind_equ' SS :=
  match goal with
    (* Out of a coinductive proof --- terminology abuse, this is simply using the congruence of the relation, not a upto *)
    |- @equ ?E ?HE ?R1 ?R2 ?RR (ICtree.bind (X := ?T1) _ _) (ICtree.bind (X := ?T2) _ _) =>
      apply (@equ_clo_bind E HE T1 T2 R1 R2 _ _ _ _ SS RR)

    (* Upto when unguarded *)
  | |- body (t (@fequ ?E ?HE ?R1 ?R2 ?RR)) ?R (ICtree.bind (X := ?T1) _ _) (ICtree.bind (X := ?T2) _ _) =>
        apply (ft_t (@bind_ctx_equ_t E HE T1 T2 R1 R2 SS RR)), in_bind_ctx2

    (* Upto when guarded *)
  | |- body (bt (@fequ ?E ?HE ?R1 ?R2 ?RR)) ?R (ICtree.bind (X := ?T1) _ _) (ICtree.bind (X := ?T2) _ _) =>
      apply (fbt_bt (@bind_ctx_equ_t E HE T1 T2 R1 R2 SS RR)), in_bind_ctx2
  end.
Tactic Notation "__upto_bind_equ" uconstr(eq) := __upto_bind_equ' eq.

Ltac __eupto_bind_equ :=
  match goal with
    (* Out of a coinductive proof --- terminology abuse, this is simply using the congruence of the relation, not a upto *)
    |- @equ ?E ?HE ?R1 ?R2 ?RR (ICtree.bind (X := ?T1) _ _) (ICtree.bind (X := ?T2) _ _) =>
      eapply (@equ_clo_bind E HE T1 T2 R1 R2 _ _ _ _ _ RR)

    (* Upto when unguarded *)
  | |- body (t (@fequ ?E ?HE ?R1 ?R2 ?RR)) ?R (ICtree.bind (X := ?T1) _ _) (ICtree.bind (X := ?T2) _ _) =>
        eapply (ft_t (@bind_ctx_equ_t E HE T1 T2 R1 R2 _ RR)), in_bind_ctx2

    (* Upto when guarded *)
  | |- body (bt (@fequ ?E ?HE ?R1 ?R2 ?RR)) ?R (ICtree.bind (X := ?T1) _ _) (ICtree.bind (X := ?T2) _ _) =>
      eapply (fbt_bt (@bind_ctx_equ_t E HE T1 T2 R1 R2 _ RR)), in_bind_ctx2
  end.

Ltac upto_bind_equ :=
  __upto_bind_equ eq; [reflexivity | intros ? ? <-].


(*|
Up-to [equ eq] bisimulations
----------------------------
The transitivity of the [et R] gives us "equ bisimulation up-to equ". Looking forward,
in order to establish "up-to equ" principles for other bisimulations, we define here the
associated enhancing function.
|*)

(*| Binary enchancing function up-to-equ |*)
Variant equ_clos_body {E F X1 X2} {HE: Encode E} {HF: Encode F}
  (R : rel (ictree E X1) (ictree F X2)) : (rel (ictree E X1) (ictree F X2)) :=
  | Equ_clos : forall t t' u' u
                 (Equt : t ≅ t')
                 (HR : R t' u')
                 (Equu : u' ≅ u),
      equ_clos_body R t u.

Program Definition equ_clos {E F X1 X2} {HE: Encode E} {HF: Encode F}: mon (rel (ictree E X1) (ictree F X2)) :=
  {| body := @equ_clos_body E F X1 X2 HE HF |}.
Next Obligation.
  unfold impl; repeat red; intros.
  inv H0; econstructor; eauto.
Qed.

(*|
Sufficient condition to prove compatibility only over the simulation
|*)
Lemma equ_clos2_sym {E C X} : compat converse (@equ_clos E E C C X X).
Proof.
  intros R t u EQ; inv EQ.
  apply Equ_clos with u' t'; intuition.
Qed.

(*| Even eta-laws for coinductive data-structures are not valid w.r.t. to [eq]
  in Coq. We however do recover them w.r.t. [equ]. |*)
Lemma ictree_eta {E R} {HE: Encode E} (t : ictree E R) : t ≅ go (observe t).
Proof. step; now cbn. Qed.

Lemma unfold_stuck {E R} {HE: Encode E}: @stuck E _ R ≅ Guard stuck.
Proof. exact (ictree_eta stuck). Qed.

Lemma unfold_spin {E R} {HE: Encode E}: @spin E _ R ≅ step spin.
Proof. exact (ictree_eta spin). Qed.

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | VisF e ke => Vis e (fun x => bind (ke x) k)
  | GuardF t => Guard (bind t k)
  | BrF n ke => Br n (fun x => bind (ke x) k)
  end (only parsing).

Lemma unfold_bind {E R S} {HE: Encode E} (t : ictree E R) (k : R -> ictree E S): bind t k ≅ bind_ t k.
Proof. step; now cbn. Qed.

Notation iter_ step i :=
  (lr <- step%function i;;
   match lr with
   | inl l => Guard (iter step l)
   | inr r => Ret r
   end)%ictree (only parsing).

Lemma unfold_iter {E R I} {HE: Encode E} (step : I -> ictree E (I + R)) i:
  iter step i ≅ iter_ step i.
Proof. step; now cbn. Qed.

(*| Monadic laws |*)
Lemma bind_ret_l {E X Y} {HE: Encode E}: forall (x : X) (k : X -> ictree E Y),
    Ret x >>= k ≅ k x.
Proof.
  intros; now rewrite unfold_bind.
Qed.

(* Giving in to [subst'] anger and defining the monad lemmas again *)
Lemma subst_ret_l {E X Y} {HE: Encode E}: forall (x : X) (k : X -> ictree E Y),
    subst' k (RetF x) ≅ k x.
Proof.
  intros; step; cbn.
  replace (observe (subst' k (RetF x))) with (observe (k x)); reflexivity.
Qed.

Lemma bind_ret_r {E X} {HE: Encode E}: forall (t : ictree E X),
    x <- t;; Ret x ≅ t.
Proof.
  coinduction R CIH.
  intros t;
  rewrite unfold_bind.
  cbn*; desobs t; constructor; auto.
Qed.

Lemma subst_ret_r {E X} {HE: Encode E}: forall (t : ictree E X),
    subst' (fun x => Ret x) (observe t) ≅ t.
Proof.
  intros.
  replace (subst' (fun x: X => Ret x) (observe t)) with (x <- t ;; Ret x) by reflexivity.
  apply bind_ret_r.
Qed.

Lemma bind_bind {E X Y Z} {HE: Encode E}: forall (t : ictree E X) (k : X -> ictree E Y) (l : Y -> ictree E Z),
    (t >>= k) >>= l ≅ t >>= (fun x => k x >>= l).
Proof.
  coinduction R CIH; intros.
  pose proof (ictree_eta t).
  rewrite H.
  rewrite (ictree_eta t). cbn*.
  desobs t; cbn.
  - reflexivity.
  - constructor; intros; apply CIH.
  - constructor; intros; apply CIH.
  - constructor; intros; apply CIH.
Qed.

(*| Structural rules |*)
Lemma bind_vis {E Y Z} (e : E) {HE: Encode E} (k : encode e -> ictree E Y) (g : Y -> ictree E Z):
  Vis e k >>= g ≅ Vis e (fun x => k x >>= g).
Proof.
  now rewrite unfold_bind.
Qed.

Lemma bind_trigger {Y: Type} `{ReSumRet E1 E2} (e : E1) (k : encode e -> ictree E2 Y) :
  trigger e >>= k ≅ Vis (resum e) (fun x: encode (resum e) => k (resum_ret e x)) .
Proof.
  unfold trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma bind_br {E n Y Z} {HE: Encode E} (k : fin' n -> ictree E Y) (g : Y -> ictree E Z):
  Br n k >>= g ≅ Br n (fun x => k x >>= g).
Proof. now rewrite unfold_bind. Qed.

Lemma bind_branch : forall {E n X} {HE: Encode E} (k : fin' n -> ictree E X),
    branch n >>= k ≅ Br n k.
Proof.
  intros. rewrite unfold_bind. cbn. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma bind_guard {E X Y} {HE: Encode E} (t : ictree E X) (g : X -> ictree E Y):
  Guard t >>= g ≅ Guard (t >>= g).
Proof. now rewrite unfold_bind. Qed.

Lemma vis_equ_bind {E X Y} {HE: Encode E}:
  forall (t : ictree E X) (e : E) k (k' : encode e -> ictree E Y),
    x <- t;; k' x ≅ Vis e k ->
    (exists r, t ≅ Ret r) \/
  exists k0, t ≅ Vis e k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left. exists x. rewrite ictree_eta, Heqi. reflexivity.
  - rewrite (ictree_eta t), Heqi, bind_br in H;step in H; inv H.
  - rewrite (ictree_eta t), Heqi, bind_guard in H;step in H; inv H.
  - rewrite (ictree_eta t), Heqi, bind_vis in H.
    apply equ_vis_invT in H as ?; subst.
    destruct H0; subst.
    pose proof (equ_vis_invE H).
    right. exists k0. split.
    + rewrite (ictree_eta t), Heqi. reflexivity.
    + cbn in H1. symmetry in H1. apply H1.
Qed.

Lemma br_equ_bind {E n X Y} {HE: Encode E}:
  forall (t : ictree E X) k (k' : X -> ictree E Y),
  x <- t;; k' x ≅ Br n k ->
  (exists r, t ≅ Ret r) \/
  exists k0, t ≅ Br n k0 /\ forall x, k x ≅ x <- k0 x;; k' x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left; exists x; rewrite ictree_eta, Heqi; reflexivity.
  - rewrite (ictree_eta t), Heqi, bind_br in H.
    pose proof (equ_br_invT H) as ->.
    pose proof (equ_br_invE H).
    right. exists k0.
    split; cbn in H0. 
    + rewrite (ictree_eta t), Heqi.
      reflexivity.
    + cbn in H0. symmetry in H0. apply H0.
  - rewrite (ictree_eta t), Heqi, bind_guard in H.
    step in H; cbn in H; dependent destruction H.
  - rewrite (ictree_eta t), Heqi, bind_vis in H. step in H. inv H.
Qed.

Lemma tau_equ_bind {E X Y} {HE: Encode E}:
  forall (t: ictree E Y) (k: Y -> ictree E X) t',
    x <- t;; k x ≅ Guard t' ->
    (exists r, t ≅ Ret r) \/
      exists t0, t ≅ Guard t0 /\ t' ≅ x <- t0 ;; k x.
Proof.
  intros.
  destruct (observe t) eqn:?.
  - left; exists x; rewrite ictree_eta, Heqi; reflexivity.
  - rewrite (ictree_eta t), Heqi, bind_br in H.
    step in H; cbn in H; dependent destruction H.
  - rewrite (ictree_eta t), Heqi, bind_guard in H.
    pose proof (equ_guard_invE H).
    right. exists t0.
    split. 
    + rewrite (ictree_eta t), Heqi.
      reflexivity.
    + now symmetry in H0. 
  - rewrite (ictree_eta t), Heqi, bind_vis in H.
    step in H; cbn in H; dependent destruction H.
Qed.

Lemma ret_equ_bind {E X Y} {HE: Encode E}:
  forall (t : ictree E Y) (k : Y -> ictree E X) r,
  x <- t;; k x ≅ Ret r ->
  exists r1, t ≅ Ret r1 /\ k r1 ≅ Ret r.
Proof.
  intros. setoid_rewrite (ictree_eta t) in H. setoid_rewrite (ictree_eta t).
  destruct (observe t) eqn:?.
  - rewrite bind_ret_l in H. eauto.
  - rewrite bind_br in H. step in H. inv H.
  - rewrite bind_guard in H. step in H. inv H.
  - rewrite bind_vis in H. step in H. inv H.
Qed.

(*| Map |*)
Lemma map_map {E R S T} {HE: Encode E}: forall (f : R -> S) (g : S -> T) (t : ictree E R),
    map g (map f t) ≅ map (fun x => g (f x)) t.
Proof.
  unfold map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma bind_map {E R S T} {HE: Encode E}: forall (f : R -> S) (k: S -> ictree E T) (t : ictree E R),
    bind (map f t) k ≅ bind t (fun x => k (f x)).
Proof.
  unfold map. intros. rewrite bind_bind. setoid_rewrite bind_ret_l. reflexivity.
Qed.

Lemma map_bind {E X Y Z} {HE: Encode E} (t: ictree E X) (k: X -> ictree E Y) (f: Y -> Z) :
  (map f (bind t k)) ≅ bind t (fun x => map f (k x)).
Proof.
  intros. unfold map. apply bind_bind.
Qed.

Lemma map_ret {E X Y} {HE: Encode E} (f : X -> Y) (x : X) :
    map f (Ret x: ictree E X) ≅ Ret (f x).
Proof.
  intros. unfold map.
  rewrite bind_ret_l; reflexivity.
Qed.

(*| Forever |*)
Lemma unfold_forever {E X Y} {HE: Encode E}: forall (k: X -> ictree E X)(i: X),
    forever Y k i ≅ r <- k i ;; Guard (forever Y k r).
Proof.
  intros k i.
  unfold forever. 
  rewrite unfold_iter.
  rewrite bind_map.
  reflexivity.
Qed.

Lemma br_equ': forall n (E: Type) {HE: Encode E} R (k k': fin' n -> ictree E R) Q,
    (forall t, k t (≅ Q) (k' t)) ->
    Br n k (≅ Q) Br n k'.
Proof.
  intros * EQ.
  step; econstructor; auto.
Qed.

Lemma br_equ: forall n (E: Type) {HE: Encode E} R (k k': fin' n -> ictree E R),
    (forall t, k t ≅ k' t) ->
    Br n k ≅ Br n k'.
Proof.
  intros n E HE R k k'.
  exact (@br_equ' n E HE R k k' eq).
Qed.

#[global] Instance proper_equ_forever{E X Y} {HE: Encode E}:
  Proper (pointwise_relation X (@equ E HE X X eq) ==> eq ==> @equ E HE Y Y eq) (forever Y).
Proof.
  unfold Proper, respectful; intros; subst.
  revert y0; coinduction R CIH; intros.
  rewrite (unfold_forever x), (unfold_forever y).
  rewrite H.
  upto_bind_equ.
  econstructor; apply CIH.
Qed.

#[global] Instance proper_equ_map{E X Y} {HE: Encode E} (f: X -> Y):
  Proper (equ eq ==> equ eq) (map f).
Proof.
  unfold Proper, respectful; intros; subst.
  unfold map.
  now rewrite H.
Qed.


#[global] Instance proper_equ_resumICtree {X} `{Encode E1} `{Encode E2}
  `{ReSum E1 E2} `{ReSumRet E1 E2}:
  Proper (equ eq ==> equ eq) (@resumICtree E1 E2 _ _ _ _ X).
Proof with auto.
  unfold Proper, respectful.
  coinduction R CIH; intros.
  rewrite ?unfold_resumICtree.
  step in H6; cbn in H6; inv H6; constructor...
Qed.

Lemma resumICtree_bind{E1 E2 : Type} `{ReSumRet E1 E2}
  {X Y}: forall (t: ictree E1 X) (k : X -> ictree E1 Y),
  resumICtree (x <- t ;; k x) ≅ x <- resumICtree t ;; resumICtree (k x).
Proof with eauto.
  coinduction RR CIH; intros.
  rewrite (ictree_eta t).
  desobs t.
  - rewrite bind_ret_l.
    setoid_rewrite unfold_resumICtree; cbn.
    rewrite bind_ret_l...
  - rewrite bind_br.
    setoid_rewrite resumICtree_br.
    rewrite bind_br.
    constructor.
    intros i.
    apply CIH.
  - rewrite bind_guard.
    setoid_rewrite resumICtree_guard.
    rewrite bind_guard.
    constructor.
    apply CIH.
  - rewrite bind_vis.
    setoid_rewrite resumICtree_vis.
    rewrite bind_vis.
    constructor.
    intros.
    apply CIH.
Qed.  

(*| Inversion of [≅] hypotheses |*)
Ltac subst_hyp_in EQ h :=
  match type of EQ with
  | ?x = ?x => clear EQ
  | ?x = ?y => subst x || subst y || rewrite EQ in h
  end.

Ltac ictree_head_in t h :=
  match t with
  | step ?t =>
      change (step t) with (Br 1 (fun _ => t)) in h
  | @ICtree.trigger ?E ?B ?R ?e =>
      change t with (Vis e (fun x => Ret x) : ictree E R) in h
  | @ICtree.branch ?E ?B ?vis ?X ?b =>
      change t with (Br vis b (fun x => Ret x) : ictree E X) in h
  | _ => idtac
  end.

Ltac inv_equ h :=
  match type of h with
  | ?t ≅ ?u => ictree_head_in t h; ictree_head_in u h;
      try solve [ step in h; inv h; (idtac || invert) ]
  end;
  match type of h with
  | Ret _ ≅ Ret _ =>
      apply equ_ret_inv in h;
      subst
  | Vis _ _ ≅ Vis _ _ =>
      let EQt := fresh "EQt" in
      let EQe := fresh "EQe" in
      let EQ := fresh "EQ" in
      apply equ_vis_invT in h as EQt;
      subst_hyp_in EQt h;
      apply equ_vis_invE in h as [EQe EQ];
      subst
  | Guard _ ≅ Guard _ =>
      let EQt := fresh "EQt" in
      let EQ := fresh "EQ" in
      apply equ_br_invE in h as [EQt EQ];
      subst
  | Br _ _ _ ≅ Br _ _ _ =>
      let EQt := fresh "EQt" in
      let EQb := fresh "EQb" in
      let EQe := fresh "EQe" in
      let EQ := fresh "EQ" in
      apply equ_br_invT in h as EQt;
      destruct EQt as [EQt EQb];
      subst_hyp_in EQt h;
      subst_hyp_in EQb h;
      apply equ_br_invE in h as [EQe EQ];
      subst
  end.

Ltac inv_equ_one :=
  multimatch goal with
  | [ h : _ ≅ _ |- _ ] =>
      inv_equ h
  end.

Ltac inv_equ_all := repeat inv_equ_one.

Tactic Notation "inv_equ" hyp(h) := inv_equ h.
Tactic Notation "inv_equ" := inv_equ_all.
