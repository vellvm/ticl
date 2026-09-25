From Stdlib Require Import Arith.PeanoNat Fin Morphisms Program.Equality.
From ExtLib Require Import Data.Monads.StateMonad.
From Coinduction Require Import coinduction rel tactics.
From TICL Require Import ICTree.Core ICTree.Equ.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.
Local Typeclasses Transparent equ.

Definition rr_pick (n cursor : nat) : Fin.t (S n) :=
  @Fin.of_nat_lt (cursor mod S n) (S n)
    (Nat.mod_upper_bound cursor (S n) (Nat.neq_succ_0 n)).

(** Compare numeric choices, not the proof arguments of finite indices. *)
Lemma rr_pick_mod_congr n cursor cursor' :
  cursor mod S n = cursor' mod S n -> rr_pick n cursor = rr_pick n cursor'.
Proof.
  intro Hmod; apply Fin.to_nat_inj; unfold rr_pick.
  rewrite !Fin.to_nat_of_nat; exact Hmod.
Qed.

CoFixpoint refine_rr {E : Type} `{Encode E} {A : Type}
  (t : ictree E A) (cursor : nat) : ictree E (A * nat) :=
  match observe t with
  | RetF x => Ret (x,cursor)
  | GuardF t' => Guard (refine_rr t' cursor)
  | BrF n k => Guard (refine_rr (k (rr_pick n cursor)) (S cursor))
  | VisF e k => Vis e (fun x => refine_rr (k x) cursor)
  end.

Definition round_robin {E : Type} `{Encode E} {A : Type}
  (t : ictree E A) : stateT nat (ictree E) A :=
  mkStateT (fun cursor => refine_rr t cursor).

Definition run_round_robin {E : Type} `{Encode E} {A : Type}
  (t : ictree E A) (cursor : nat) : ictree E A :=
  result <- runStateT (round_robin t) cursor;; Ret (fst result).

Lemma unfold_refine_rr {E : Type} `{Encode E} {A : Type}
  (t : ictree E A) (cursor : nat) :
  refine_rr t cursor ≅
  match observe t with
  | RetF x => Ret (x,cursor)
  | GuardF t' => Guard (refine_rr t' cursor)
  | BrF n k => Guard (refine_rr (k (rr_pick n cursor)) (S cursor))
  | VisF e k => Vis e (fun x => refine_rr (k x) cursor)
  end.
Proof. step; now cbn. Qed.

Lemma unfold_run_round_robin {E : Type} `{Encode E} {A : Type}
  (t : ictree E A) (m : nat) :
  run_round_robin t m ≅
  match observe t with
  | RetF x => Ret x
  | GuardF t' => Guard (run_round_robin t' m)
  | BrF n k => Guard (run_round_robin (k (rr_pick n m)) (S m))
  | VisF e k => Vis e (fun x => run_round_robin (k x) m)
  end.
Proof.
  unfold run_round_robin, round_robin; cbn [runStateT].
  rewrite unfold_refine_rr.
  destruct (observe t); cbn; rewrite ?bind_ret_l, ?bind_guard, ?bind_vis;
    reflexivity.
Qed.

#[global] Instance refine_rr_equ {E : Type} {HE : Encode E} {A : Type} :
  Proper (equ eq ==> eq ==> equ eq) (@refine_rr E HE A).
Proof.
  unfold Proper, respectful.
  coinduction R IH; intros t u Htu m m' <-.
  rewrite !unfold_refine_rr.
  step in Htu.
  destruct Htu as [x y Hxy|e k1 k2 Hk|t1 t2 Ht|b k1 k2 Hk]; cbn.
  - subst; reflexivity.
  - constructor; intro x; apply IH; [exact (Hk x)|reflexivity].
  - constructor; apply IH; [exact Ht|reflexivity].
  - constructor; apply IH; [exact (Hk (rr_pick b m))|reflexivity].
Qed.

#[global] Instance run_round_robin_equ {E : Type} {HE : Encode E} {A : Type} :
  Proper (equ eq ==> eq ==> equ eq) (@run_round_robin E HE A).
Proof.
  intros t u Htu m m' <-.
  unfold run_round_robin, round_robin; cbn [runStateT].
  now rewrite Htu.
Qed.

Section BranchFreedom.
  Context {E : Type} {HE : Encode E} {A : Type}.

  Variant branchfreeF (R : ictree E A -> Prop) : ictree' E A -> Prop :=
  | BfRetF x : branchfreeF R (RetF x)
  | BfGuardF t : R t -> branchfreeF R (GuardF t)
  | BfVisF e k : (forall x, R (k x)) -> branchfreeF R (VisF e k).

  Program Definition fbranchfree : mon (ictree E A -> Prop) :=
    {| body R t := branchfreeF R (observe t) |}.
  Next Obligation.
    unfold pointwise_relation, Basics.impl, Proper, respectful in *.
    intros R S HRS t Ht; destruct Ht; constructor; auto.
  Qed.

  Definition BranchFree : ictree E A -> Prop := gfp fbranchfree.

  Lemma branchfree_unfold t :
    BranchFree t <-> branchfreeF BranchFree (observe t).
  Proof. exact (gfp_fp fbranchfree t). Qed.
End BranchFreedom.

Section BranchFreeLaws.
  Context {E : Type} {HE : Encode E}.

  Lemma bf_ret {A} (x : A) : BranchFree (Ret x : ictree E A).
  Proof. apply branchfree_unfold; constructor. Qed.

  Lemma bf_guard {A} (t : ictree E A) :
    BranchFree t -> BranchFree (Guard t).
  Proof. intro Ht; apply branchfree_unfold; now constructor. Qed.

  Lemma bf_vis {A} e (k : encode e -> ictree E A) :
    (forall x, BranchFree (k x)) -> BranchFree (Vis e k).
  Proof. intro Hk; apply branchfree_unfold; now constructor. Qed.

  Lemma branchfree_equ_impl {A} : forall (t u : ictree E A),
    t ≅ u -> BranchFree t -> BranchFree u.
  Proof.
    change (forall (t u : ictree E A),
      t ≅ u -> BranchFree t -> gfp fbranchfree u).
    apply_coinduction; intros R IH t u Htu Ht.
    change (branchfreeF (coinduction.t fbranchfree R) (observe u)).
    apply branchfree_unfold in Ht.
    step in Htu.
    change (equF eq (equ eq) (observe t) (observe u)) in Htu.
    remember (observe t) as ot in *.
    remember (observe u) as ou in *.
    destruct Htu; dependent destruction Ht;
      constructor; intros; eapply IH; eauto.
  Qed.

  #[global] Instance branchfree_equ {A} :
    Proper (equ eq ==> iff) (@BranchFree E HE A).
  Proof.
    intros t u Htu; split; intro Hbf.
    - eapply branchfree_equ_impl; [exact Htu|exact Hbf].
    - eapply branchfree_equ_impl; [symmetry; exact Htu|exact Hbf].
  Qed.

  Lemma branchfree_bind {A B} (t : ictree E A) (k : A -> ictree E B) :
    BranchFree t -> (forall x, BranchFree (k x)) -> BranchFree (ICtree.bind t k).
  Proof.
    revert t k.
    change (forall (t : ictree E A) (k : A -> ictree E B),
      BranchFree t -> (forall x, BranchFree (k x)) ->
      gfp fbranchfree (ICtree.bind t k)).
    apply_coinduction; intros R IH t k Ht Hk.
    change (branchfreeF (coinduction.t fbranchfree R)
      (observe (match observe t with
       | RetF x => k x
       | BrF n ke => Br n (fun x => ICtree.bind (ke x) k)
       | GuardF r => Guard (ICtree.bind r k)
       | VisF e ke => Vis e (fun x => ICtree.bind (ke x) k)
       end))).
    apply branchfree_unfold in Ht.
    remember (observe t) as ot in *.
    destruct Ht as [x|r Hr|e ke Hke]; cbn.
    - apply (gfp_bt fbranchfree R), Hk.
    - constructor; apply IH; [exact Hr|exact Hk].
    - constructor; intro x; apply IH; [exact (Hke x)|exact Hk].
  Qed.

  Lemma branchfree_iter {I A} (body : I -> ictree E (I + A)) :
    (forall i, BranchFree (body i)) -> forall i, BranchFree (ICtree.iter body i).
  Proof.
    intro Hbody.
    set (next := fun lr : I + A =>
      match lr with
      | inl i => Guard (ICtree.iter body i)
      | inr a => Ret a
      end).
    assert (Hclosed : forall t : ictree E A,
      ((exists i, t ≅ ICtree.iter body i) \/
       (exists r : ictree E (I + A), BranchFree r /\ t ≅ (r >>= next))) ->
      BranchFree t).
    {
      change (forall t : ictree E A,
        ((exists i, t ≅ ICtree.iter body i) \/
         (exists r : ictree E (I + A), BranchFree r /\ t ≅ (r >>= next))) ->
        gfp fbranchfree t).
      apply_coinduction; intros R IH t Ht.
      change (branchfreeF (coinduction.t fbranchfree R) (observe t)).
      assert (Hr : exists r : ictree E (I + A),
        BranchFree r /\ t ≅ (r >>= next)).
      {
        destruct Ht as [[i Ht]|Ht]; auto.
        exists (body i); split; auto.
        rewrite Ht, unfold_iter; reflexivity.
      }
      destruct Hr as [r [Hr Htr]].
      apply branchfree_unfold in Hr.
      rewrite (ictree_eta r) in Htr.
      remember (observe r) as node in Htr, Hr.
      destruct Hr as [lr|r' Hbf|e ke Hbf]; cbn in Htr.
      - rewrite bind_ret_l in Htr.
        destruct lr as [i|a]; unfold next in Htr; cbn in Htr.
        + step in Htr.
          change (equF eq (equ eq) (observe t)
            (GuardF (ICtree.iter body i))) in Htr.
          remember (observe t) as ot in *; clear Heqot.
          inversion Htr; subst.
          constructor; apply IH; left; eauto.
        + step in Htr.
          change (equF eq (equ eq) (observe t) (RetF a)) in Htr.
          remember (observe t) as ot in *; clear Heqot.
          inversion Htr; subst; constructor.
      - rewrite bind_guard in Htr; step in Htr.
        change (equF eq (equ eq) (observe t)
          (GuardF (r' >>= next))) in Htr.
        remember (observe t) as ot in *; clear Heqot.
        inversion Htr; subst.
        constructor; apply IH; right; eauto.
      - rewrite bind_vis in Htr; step in Htr.
        change (equF eq (equ eq) (observe t)
          (VisF e (fun x => ke x >>= next))) in Htr.
        remember (observe t) as ot in *; clear Heqot.
        dependent destruction Htr.
        constructor; intro x; apply IH; right; eauto.
    }
    intro i; apply Hclosed; left; exists i; reflexivity.
  Qed.
End BranchFreeLaws.

Lemma rr_pick_even n : Nat.even n = true -> rr_pick 1 n = Fin.F1.
Proof.
  intro Hn; apply Nat.even_spec in Hn; destruct Hn as [k ->].
  transitivity (rr_pick 1 0); [apply rr_pick_mod_congr|reflexivity].
  change ((2 * k) mod 2 = 0).
  rewrite Nat.mul_comm; apply Nat.mod_mul; discriminate.
Qed.

Lemma rr_pick_odd n : Nat.even n = false -> rr_pick 1 n = Fin.FS Fin.F1.
Proof.
  intro Hn.
  assert (Ho : Nat.odd n = true) by (unfold Nat.odd; now rewrite Hn).
  apply Nat.odd_spec in Ho; destruct Ho as [k ->].
  transitivity (rr_pick 1 1); [apply rr_pick_mod_congr|reflexivity].
  change ((2 * k + 1) mod 2 = 1).
  rewrite Nat.Div0.add_mod.
  rewrite (Nat.mul_comm 2 k), Nat.mod_mul by discriminate.
  reflexivity.
Qed.
