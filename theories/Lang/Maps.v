
From Stdlib Require Import
  Nat
  Strings.String.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList
  Data.String.

From TICL Require Import Utils.

Module Ctx.
  Definition Ctx := alist string nat.

  Definition assert1 c (m: Ctx) (p: nat -> Prop) :=
    exists v, lookup c m = Some v /\ p v.

  Definition assert2 c1 c2 (m: Ctx) (r: nat -> nat -> Prop) :=
    exists v1 v2, lookup c1 m = Some v1 /\ lookup c2 m = Some v2 /\ r v1 v2.

  (*| Map equations |*)
  Lemma lookup_add_eq: forall c (v: nat) m,
    lookup c (add c v m) = Some v.
  Proof with auto.
    intros.  
    pose proof (mapsto_add_eq (R:=@eq string) (V:=nat) m c v).
    now apply mapsto_lookup in H.
  Qed.

  Lemma lookup_add_neq: forall c r (v: nat) m,
    r <> c ->
    lookup c (add r v m) = lookup c m.
  Proof with auto.
    intros.
    destruct (lookup c (add r v m)) eqn:Hc;
      destruct (lookup c m) eqn: Hr; rewrite ?mapsto_lookup in *.
    - apply mapsto_add_neq with (R:=eq) in Hc...
      rewrite <- mapsto_lookup in *.
      rewrite Hc in Hr; inv Hr...
    - apply mapsto_add_neq with (R:=eq) in Hc...
      rewrite <- mapsto_lookup in Hc.
      rewrite Hc in Hr; inv Hr.
    - rewrite mapsto_add_neq with (R:=eq) in Hr. 
      rewrite <- mapsto_lookup in Hr.
      rewrite Hc in Hr; inv Hr.
      apply H.
    - reflexivity.
      Unshelve.
      exact eq.
      typeclasses eauto.
      typeclasses eauto.
      typeclasses eauto.
      typeclasses eauto.
  Qed.

  Lemma assert1_add_eq: forall c (v: nat) m p,
      p v ->
      assert1 c (add c v m) p.
  Proof with eauto.
    intros.
    unfold assert1.
    pose proof (mapsto_add_eq (R:=@eq string) (V:=nat) m c v).
    apply mapsto_lookup in H0.
    rewrite H0...
  Qed.

  Lemma assert1_add_neq: forall c1 c2 (v: nat) m p,
      assert1 c1 m p ->
      c1 <> c2 ->
      assert1 c1 (add c2 v m) p.
  Proof with eauto.
    intros.
    unfold assert1 in *.
    destruct H as (v1 & Hc1 & Hv1).    
    exists v1; split...
    rewrite mapsto_lookup with (R:=@eq string) in Hc1 |- *.
    apply mapsto_add_neq with (R:=@eq string)...
    Unshelve.
    typeclasses eauto.
  Qed.
  
  Lemma assert2_add_l: forall c1 c2 (v1 v2: nat) m p,
      c1 <> c2 ->
      p v1 v2 ->
      assert2 c1 c2 (add c1 v1 (add c2 v2 m)) p.
  Proof with eauto.
    intros.
    unfold assert2.
    pose proof (mapsto_add_eq (R:=@eq string) (V:=nat) (add c2 v2 m) c1 v1) as H1.
    apply mapsto_lookup in H1.
    assert (H2: lookup c2 (add c1 v1 (add c2 v2 m)) = Some v2).
    - rewrite mapsto_lookup with (R:=eq).
      apply mapsto_add_neq...
      apply mapsto_add_eq.
    - exists v1, v2.
      rewrite H1, H2...
      Unshelve.
      typeclasses eauto.
  Qed.
End Ctx.
