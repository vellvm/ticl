From Stdlib Require Import Arith.PeanoNat Fin Morphisms Program.Equality.
From Coinduction Require Import all.
From TICL Require Import CTree.Core.

Import CTreeNotations CoindNotations.
Local Open Scope ctree_scope.

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

(** Round-robin refinement of finite ([Bn]) branches: every branch node picks
    the alternative selected by the cursor and advances it; a branch with no
    alternative is [Stuck].  Guards, steps and events leave the cursor alone. *)
CoFixpoint refine_rr {E : Type -> Type} {A : Type}
  (t : ctree E Bn A) (cursor : nat) : ctree E Bn (A * nat) :=
  match observe t with
  | RetF x => Ret (x,cursor)
  | StuckF => Stuck
  | StepF t' => Step (refine_rr t' cursor)
  | GuardF t' => Guard (refine_rr t' cursor)
  | VisF e k => Vis e (fun x => refine_rr (k x) cursor)
  | BrF c k =>
      match c in Bn Y return (Y -> ctree E Bn A) -> ctree E Bn (A * nat) with
      | branchn 0 => fun _ => Stuck
      | branchn (S n) => fun k => Guard (refine_rr (k (rr_pick n cursor)) (S cursor))
      end k
  end.

(** The cursor as state: ITree's [stateT S M A := S -> M (S * A)]. *)
Definition round_robin {E : Type -> Type} {A : Type}
  (t : ctree E Bn A) : stateT nat (ctree E Bn) A :=
  fun cursor => CTree.map (fun r => (snd r, fst r)) (refine_rr t cursor).

Definition run_round_robin {E : Type -> Type} {A : Type}
  (t : ctree E Bn A) (cursor : nat) : ctree E Bn A :=
  CTree.map fst (refine_rr t cursor).

Lemma unfold_refine_rr {E : Type -> Type} {A : Type}
  (t : ctree E Bn A) (cursor : nat) :
  refine_rr t cursor ≅
  match observe t with
  | RetF x => Ret (x,cursor)
  | StuckF => Stuck
  | StepF t' => Step (refine_rr t' cursor)
  | GuardF t' => Guard (refine_rr t' cursor)
  | VisF e k => Vis e (fun x => refine_rr (k x) cursor)
  | BrF c k =>
      match c in Bn Y return (Y -> ctree E Bn A) -> ctree E Bn (A * nat) with
      | branchn 0 => fun _ => Stuck
      | branchn (S n) => fun k => Guard (refine_rr (k (rr_pick n cursor)) (S cursor))
      end k
  end.
Proof. step; now cbn. Qed.

Lemma unfold_run_round_robin {E : Type -> Type} {A : Type}
  (t : ctree E Bn A) (m : nat) :
  run_round_robin t m ≅
  match observe t with
  | RetF x => Ret x
  | StuckF => Stuck
  | StepF t' => Step (run_round_robin t' m)
  | GuardF t' => Guard (run_round_robin t' m)
  | VisF e k => Vis e (fun x => run_round_robin (k x) m)
  | BrF c k =>
      match c in Bn Y return (Y -> ctree E Bn A) -> ctree E Bn A with
      | branchn 0 => fun _ => Stuck
      | branchn (S n) => fun k => Guard (run_round_robin (k (rr_pick n m)) (S m))
      end k
  end.
Proof.
  unfold run_round_robin, CTree.map.
  rewrite unfold_refine_rr.
  destruct (observe t) as [x| |t'|t'|Y e k|Y c k]; cbn [fst];
    rewrite ?bind_ret_l, ?bind_stuck, ?bind_step, ?bind_guard, ?bind_vis;
    try reflexivity.
  destruct c as [[|n]]; rewrite ?bind_stuck, ?bind_guard; reflexivity.
Qed.

#[global] Instance refine_rr_equ {E : Type -> Type} {A : Type} :
  Proper (equ eq ==> eq ==> equ eq) (@refine_rr E A).
Proof.
  unfold Proper, respectful.
  __coinduction_equ R IH; intros t u Htu m m' <-.
  rewrite !unfold_refine_rr.
  step in Htu.
  destruct Htu as [x y Hxy| |t1 t2 Ht|t1 t2 Ht|Y e k1 k2 Hk|Y c k1 k2 Hk]; cbn.
  - subst; reflexivity.
  - constructor.
  - constructor; apply IH; [exact Ht|reflexivity].
  - constructor; apply IH; [exact Ht|reflexivity].
  - constructor; intro x; apply IH; [exact (Hk x)|reflexivity].
  - destruct c as [[|n]]; constructor; apply IH; [exact (Hk _)|reflexivity].
Qed.

#[global] Instance run_round_robin_equ {E : Type -> Type} {A : Type} :
  Proper (equ eq ==> eq ==> equ eq) (@run_round_robin E A).
Proof.
  intros t u Htu m m' <-; unfold run_round_robin; now rewrite Htu.
Qed.

(** * Branch-free trees: no [Br] node anywhere (steps and [Stuck] allowed). *)
Section BranchFreedom.
  Context {E B : Type -> Type}.

  Variant branchfreeF {A} (R : ctree E B A -> Prop) : ctree' E B A -> Prop :=
  | BfRetF x : branchfreeF R (RetF x)
  | BfStuckF : branchfreeF R StuckF
  | BfStepF t : R t -> branchfreeF R (StepF t)
  | BfGuardF t : R t -> branchfreeF R (GuardF t)
  | BfVisF {Y} (e : E Y) k : (forall x, R (k x)) -> branchfreeF R (VisF e k).

  Program Definition fbranchfree {A} : mon (ctree E B A -> Prop) :=
    {| body R t := branchfreeF R (observe t) |}.
  Next Obligation.
    destruct H0; constructor; intros; apply H; auto.
  Qed.

  Definition BranchFree {A} : ctree E B A -> Prop := gfp fbranchfree.

  Lemma branchfree_unfold {A} (t : ctree E B A) :
    BranchFree t <-> branchfreeF BranchFree (observe t).
  Proof. symmetry; exact (gfp_fp fbranchfree t). Qed.

  (** Every element of the tower is closed under [≅]. *)
  #[global] Instance branchfree_chain_equ {A} {R : Chain (@fbranchfree A)} :
    Proper (equ eq ==> iff) `R.
  Proof.
    apply tower.
    - intros ? INC t u Htu; split; intros H x Hx; apply (INC x Hx t u Htu); apply H, Hx.
    - intros R' IH t u Htu; step in Htu; cbn.
      change (equb eq (equ eq) (observe t) (observe u)) in Htu.
      split; intro H; revert Htu;
        [remember (observe u) as ou | remember (observe t) as ot];
        destruct H; intro Htu; dependent destruction Htu; try rename REL into Hq;
        constructor; intros; first [apply (IH _ _ (Hq _)) | apply (IH _ _ Hq)]; auto.
  Qed.

  #[global] Instance branchfree_bchain_equ {A} {R : Chain (@fbranchfree A)} :
    Proper (equ eq ==> iff) (fbranchfree `R) := branchfree_chain_equ (R := chain_b R).

  #[global] Instance branchfree_equ {A} : Proper (equ eq ==> iff) (@BranchFree A) :=
    branchfree_chain_equ (R := chain_gfp _).

  Lemma branchfree_equ_impl {A} : forall (t u : ctree E B A),
    t ≅ u -> BranchFree t -> BranchFree u.
  Proof. intros t u Htu; now rewrite Htu. Qed.

  Lemma bf_ret {A} (x : A) : BranchFree (Ret x : ctree E B A).
  Proof. apply branchfree_unfold; constructor. Qed.

  Lemma bf_stuck {A} : BranchFree (Stuck : ctree E B A).
  Proof. apply branchfree_unfold; constructor. Qed.

  Lemma bf_step {A} (t : ctree E B A) : BranchFree t -> BranchFree (Step t).
  Proof. intro Ht; apply branchfree_unfold; now constructor. Qed.

  Lemma bf_vis {A Y} (e : E Y) (k : Y -> ctree E B A) :
    (forall x, BranchFree (k x)) -> BranchFree (Vis e k).
  Proof. intro Hk; apply branchfree_unfold; now constructor. Qed.

  (** Up-to-bind: binding a branch-free tree to branch-free continuations. *)
  Lemma branchfree_bind_chain {X A} {R : Chain (@fbranchfree A)} :
    forall (t : ctree E B X) (k : X -> ctree E B A),
      BranchFree t -> (forall x, `R (k x)) -> `R (CTree.bind t k).
  Proof.
    apply tower.
    - intros ? INC t k Ht Hk ? ?; apply INC; auto.
      intro x; apply leq_infx in H; apply H, Hk.
    - intros R' IH t k Ht Hk; apply branchfree_unfold in Ht.
      cbn; unfold observe; cbn.
      destruct Ht; cbn; try (now apply Hk);
        constructor; intros; apply IH; auto; intro; apply (b_chain R'), Hk.
  Qed.

  Lemma branchfree_bind {X A} (t : ctree E B X) (k : X -> ctree E B A) :
    BranchFree t -> (forall x, BranchFree (k x)) -> BranchFree (CTree.bind t k).
  Proof. apply branchfree_bind_chain. Qed.

  Lemma branchfree_iter {I A} (body : I -> ctree E B (I + A)) :
    (forall i, BranchFree (body i)) -> forall i, BranchFree (CTree.iter body i).
  Proof.
    intro Hbody; unfold BranchFree; coinduction R IH; intro i.
    rewrite unfold_iter.
    apply (branchfree_bind_chain (R := chain_b R)); [apply Hbody|].
    intros [i'|a]; cbn; constructor; apply IH.
  Qed.
End BranchFreedom.

Lemma rr_pick_even n : Nat.even n = true -> rr_pick 1 n = Fin.F1.
Proof.
  intro Hn; apply Nat.even_spec in Hn; destruct Hn as [k ->].
  transitivity (rr_pick 1 0); [apply rr_pick_mod_congr|reflexivity].
  change ((2 * k) mod 2 = 0).
  rewrite Nat.mul_comm; apply Nat.Div0.mod_mul.
Qed.

Lemma rr_pick_odd n : Nat.even n = false -> rr_pick 1 n = Fin.FS Fin.F1.
Proof.
  intro Hn.
  assert (Ho : Nat.odd n = true) by (unfold Nat.odd; now rewrite Hn).
  apply Nat.odd_spec in Ho; destruct Ho as [k ->].
  transitivity (rr_pick 1 1); [apply rr_pick_mod_congr|reflexivity].
  change ((2 * k + 1) mod 2 = 1).
  rewrite Nat.Div0.add_mod.
  rewrite (Nat.mul_comm 2 k), Nat.Div0.mod_mul.
  reflexivity.
Qed.
