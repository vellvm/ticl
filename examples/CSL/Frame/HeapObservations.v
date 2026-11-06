(** * Observable heap mutations of the actual CoCSL interpreter. *)
From Stdlib Require Import List Arith.PeanoNat Lia FunctionalExtensionality Vector.
From Coinduction Require Import all.
From Equations Require Import Equations.
From examples Require Import CSL.Frame.Shared CSL.Queue.Operations CSL.Queue.Representation
  CSL.Queue.Layout CSL.Queue.Sequential CSL.Queue.Program CSL.Queue.Shared CSL.Queue.Trace
  CSL.Allocator.Layout CSL.Allocator.Program CSL.Allocator.Model
  CSL.Allocator.Execution CSL.Allocator.Liveness.
From TICL Require Import CTree.Trace CTree.Logic.Trace CTree.Logic.State
  CTree.Logic.EF CTree.Logic.EX CTree.Logic.Yield CTree.Interp.Yield.Policy
  CTree.Interp.Yield.Execution Logic.Simulation Utils.Execution Utils.Lists.
From TICL Require Import CTree.Logic.AG CTree.Logic.AF CTree.Logic.Bind
  CTree.Logic.Trans CTree.Logic.CanStep CTree.Logic.Sim.

Import CTree CTreeNotations TiclNotations CoindNotations ListNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Local Open Scope list_scope.
Local Open Scope pcm_scope.

Definition mutation_probe : CProg unit :=
  CBind (CWrite 1 9) (fun _ =>
  CBind (CCAS (CLit 1) (CLit 9) (CLit 11)) (fun _ =>
  CBind (CCAS (CLit 1) (CLit 9) (CLit 12)) (fun _ =>
  CBind (CRead 1) (fun value =>
  CBind (CEmit 7 value) (fun _ =>
  CBind (CFree 0) (fun _ =>
  CBind (CAlloc 2) (fun base =>
  CBind (CFree base) (fun _ => CRet tt)))))))).

Definition mutation_body : CProg (option unit) :=
  CBind (CWrite 1 1) (fun _ =>
  CBind (CWrite 1 2) (fun _ => CRet (Some tt))).
Definition mutation_loop : CProg unit := CUntilNone mutation_body.
Definition mutation_spin : CProg unit :=
  CUntilNone (CBind CYield (fun _ => CRet (Some tt : option unit))).

Definition mutation_store (memory : ManagedHeap) (value : nat) : ManagedHeap :=
  (upd (fst memory) 1 value, snd memory).
Definition mutation_next (memory : ManagedHeap) : ManagedHeap :=
  mutation_store (mutation_store memory 1) 2.
Definition mutation_logs (memory : ManagedHeap) : list (CSLObs (nat * nat)) :=
  [CSLHeap (mutation_store memory 1); CSLHeap (mutation_next memory)].




Definition probe_written : ManagedHeap := (upd (hsingle 1 0) 1 9,hemp).
Definition probe_cas : ManagedHeap := (upd (fst probe_written) 1 11,hemp).
Definition probe_allocated : ManagedHeap := managed_alloc probe_cas 2 2.
Definition probe_freed : ManagedHeap :=
  (hfree_block 2 2 (fst probe_allocated),hfree 2 (snd probe_allocated)).
Definition probe_logs : list (CSLObs (nat * nat)) :=
  [CSLHeap probe_written; CSLHeap probe_cas; CSLEmit (stamp (7,11) 5);
   CSLHeap probe_allocated; CSLHeap probe_freed].

Theorem mutation_probe_spec ctx :
  instr_flow_erased mutation_probe ((hsingle 1 0,hemp),(ctx,5)) ~
    emit_list probe_logs
      (Ret ((probe_freed,(ctx,6)),Some tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)) /\
  length probe_logs = 5 /\
  fst probe_written 1 = Some 9 /\ fst probe_cas 1 = Some 11 /\
  fst probe_allocated 1 = Some 11 /\ fst probe_allocated 2 = Some 0 /\
  fst probe_allocated 3 = Some 0 /\ snd probe_allocated 2 = Some 2 /\
  fst probe_freed 1 = Some 11 /\ fst probe_freed 2 = None /\
  fst probe_freed 3 = None /\ heq (snd probe_freed) hemp /\
  block_free (fst probe_cas) 2 2 /\
  (forall j, 0 < j -> j < 2 -> ~ block_free (fst probe_cas) j 2).
Proof.
  assert (F : block_free (fst probe_cas) 2 2).
  { intros offset H; unfold probe_cas, probe_written; cbn [fst].
    rewrite !upd_neq by lia; apply hsingle_neq; lia. }
  assert (First : forall j, 0 < j -> j < 2 -> ~ block_free (fst probe_cas) j 2).
  { intros j Hj Hlt H; assert (j=1) by lia; subst j.
    specialize (H 0 ltac:(lia)); rewrite Nat.add_0_r in H.
    unfold probe_cas in H; cbn [fst] in H; rewrite upd_eq in H; discriminate. }
  split.
  - unfold mutation_probe, probe_logs; cbn [emit_list List.fold_right].
    rewrite instr_flow_write by discriminate.
    rewrite !log_vis; apply sb_vis; intros [].
    rewrite instr_flow_cas_value with (current:=9) by apply upd_eq; cbn [Nat.eqb].
    rewrite !log_vis; apply sb_vis; intros [].
    rewrite instr_flow_cas_value with (current:=11) by apply upd_eq; cbn [Nat.eqb].
    rewrite instr_flow_read with (v:=11) by apply upd_eq.
    rewrite instr_flow_emit.
    rewrite !log_vis; apply sb_vis; intros [].
    rewrite instr_flow_free with (memory':=probe_cas) by reflexivity.
    rewrite instr_flow_alloc_first with (base:=2) by (try lia; assumption).
    rewrite !log_vis; apply sb_vis; intros [].
    rewrite instr_flow_free with (memory':=probe_freed) by reflexivity.
    rewrite !log_vis; apply sb_vis; intros [].
    rewrite instr_flow_ret; reflexivity.
  - repeat split; try reflexivity; try assumption.
    intro address; unfold probe_freed, probe_allocated, probe_cas, probe_written,
      managed_alloc, hfree, hemp; cbn [fst snd].
    destruct (Nat.eq_dec 2 address) as [E|N]; [reflexivity|].
    unfold upd; rewrite (proj2 (Nat.eqb_neq address 2)) by congruence; reflexivity.
Qed.

Theorem same_value_mutations_visible memory ctx c a value :
  fst memory a = Some value ->
  (instr_flow_erased (CBind (CWrite a value) (fun _ => CRet tt)) (memory,(ctx,c)) ~
    emit_list [CSLHeap (upd (fst memory) a value,snd memory)]
      (Ret (((upd (fst memory) a value,snd memory),(ctx,c)),Some tt) :
        ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))) /\
  (instr_flow_erased (CBind (CCAS (CLit a) (CLit value) (CLit value)) (fun _ => CRet tt)) (memory,(ctx,c)) ~
    emit_list [CSLHeap (upd (fst memory) a value,snd memory)]
      (Ret (((upd (fst memory) a value,snd memory),(ctx,c)),Some tt) :
        ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))) /\
  (instr_flow_erased (CBind (CCAS (CLit a) (CLit (S value)) (CLit value)) (fun _ => CRet tt)) (memory,(ctx,c)) ~
    (Ret ((memory,(ctx,c)),Some tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))) /\
  (instr_flow_erased (CBind (CRead a) (fun _ => CBind (CFree 0) (fun _ => CRet tt))) (memory,(ctx,c)) ~
    (Ret ((memory,(ctx,c)),Some tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))).
Proof.
  destruct memory as [h al]; intro H; cbn [fst] in H; repeat split.
  - rewrite instr_flow_write by (cbn; rewrite H; discriminate).
    cbn [emit_list List.fold_right].
    rewrite !log_vis; apply sb_vis; intros [].
    rewrite instr_flow_ret; reflexivity.
  - rewrite instr_flow_cas_value with (current:=value) by exact H.
    rewrite Nat.eqb_refl.
    cbn [emit_list List.fold_right].
    rewrite !log_vis; apply sb_vis; intros [].
    rewrite instr_flow_ret; reflexivity.
  - rewrite instr_flow_cas_value with (current:=value) by exact H.
    rewrite (proj2 (Nat.eqb_neq value (S value))) by lia.
    rewrite instr_flow_ret; reflexivity.
  - rewrite instr_flow_read with (v:=value) by exact H.
    rewrite instr_flow_free with (memory':=(h,al)) by reflexivity.
    rewrite instr_flow_ret; reflexivity.
Qed.


Theorem fault_prefix_preserved ctx c :
  (instr_flow_erased (CBind (CRead 2) (fun _ => CRet tt)) ((hsingle 1 0,hemp),(ctx,c)) ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))) /\
  (instr_flow_erased (CBind (CWrite 2 1) (fun _ => CRet tt)) ((hsingle 1 0,hemp),(ctx,c)) ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))) /\
  (instr_flow_erased (CBind (CCAS (CLit 2) (CLit 0) (CLit 1)) (fun _ => CRet tt)) ((hsingle 1 0,hemp),(ctx,c)) ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))) /\
  (instr_flow_erased (CBind (CAlloc 0) (fun _ => CRet tt)) ((hsingle 1 0,hemp),(ctx,c)) ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))) /\
  (forall base, base <> 0 ->
    instr_flow_erased (CBind (CFree base) (fun _ => CRet tt)) ((hsingle 1 0,hemp),(ctx,c)) ~
      (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))) /\
  (instr_flow_erased (CBind (CWrite 1 9) (fun _ => CBind (CRead 2) (fun _ => CRet tt)))
      ((hsingle 1 0,hemp),(ctx,c)) ~ log (CSLHeap probe_written);;
        (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))).
Proof.
  assert (Missing : hsingle 1 0 2 = None) by (apply hsingle_neq; lia).
  repeat split.
  - apply instr_flow_read_missing, Missing.
  - apply instr_flow_write_missing, Missing.
  - apply instr_flow_cas_missing, Missing.
  - apply instr_flow_alloc_zero.
  - intros base N; apply instr_flow_free_invalid.
    unfold managed_free; cbn; rewrite (proj2 (Nat.eqb_neq base 0) N); reflexivity.
  - rewrite instr_flow_write by discriminate.
    rewrite !log_vis; apply sb_vis; intros [].
    rewrite instr_flow_read_missing by reflexivity.
    reflexivity.
Qed.

Lemma mutation_loop_round_nd memory ctx c :
  fst memory 1 <> None ->
  run_nd mutation_loop (memory,(ctx,c)) ~
    emit_list (mutation_logs memory)
      (run_nd mutation_loop (mutation_next memory,(ctx,c))).
Proof.
  destruct memory as [h al]; intro H.
  unfold run_nd, run_nd_pool, csl_pool, denote.
  cbn [Vector.map].
  change ([denote_flow mutation_loop;; Ret tt]%vector : pool sE Bn 1) with
    (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow mutation_loop >>= fun _ => Ret tt)).
  unfold mutation_loop at 1; rewrite interp_nd_source_until_none.
  unfold mutation_body at 1; rewrite interp_nd_source_bind.
  rewrite interp_nd_source_write_present by exact H.
  cbn [mutation_logs mutation_store mutation_next fst snd emit_list List.fold_right].
  rewrite !log_vis; apply sb_vis; intros [].
  rewrite interp_nd_source_bind.
  rewrite interp_nd_source_write_present by (rewrite upd_eq; discriminate).
  rewrite !log_vis; apply sb_vis; intros [].
  rewrite interp_nd_source_ret.
  erewrite (interp_schedule_nd_guard sh) by (rewrite Vector.nth_replace_eq; reflexivity).
  cbn [Vector.replace]; reflexivity.
Qed.

Lemma mutation_loop_round_rr memory ctx c :
  fst memory 1 <> None ->
  run_rr mutation_loop (memory,(ctx,c)) ~
    emit_list (List.map inl (mutation_logs memory))
      (run_rr mutation_loop (mutation_next memory,(ctx,c))).
Proof.
  destruct memory as [h al]; intro H.
  unfold run_rr, run_rr_pool, csl_pool, denote.
  cbn [Vector.map].
  change ([denote_flow mutation_loop;; Ret tt]%vector : pool sE Bn 1) with
    (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow mutation_loop >>= fun _ => Ret tt)).
  unfold mutation_loop at 1; rewrite interp_rr_until_none.
  unfold mutation_body at 1; rewrite interp_rr_bind.
  rewrite interp_rr_write_present by exact H.
  cbn [mutation_logs mutation_store mutation_next fst snd emit_list List.fold_right List.map].
  rewrite !log_vis; apply sb_vis; intros [].
  rewrite interp_rr_bind.
  rewrite interp_rr_write_present by (rewrite upd_eq; discriminate).
  rewrite !log_vis; apply sb_vis; intros [].
  rewrite interp_rr_ret.
  erewrite interp_schedule_rr_guard by (rewrite Vector.nth_replace_eq; reflexivity).
  cbn [Vector.replace]; reflexivity.
Qed.

(** Counted snapshots follow chronological standard iteration. *)
Definition mutation_round_logs n memory : list (CSLObs (nat * nat)) :=
  List.flat_map (fun j => mutation_logs (Nat.iter j mutation_next memory)) (List.seq 0 n).
Definition mutation_after n memory : ManagedHeap :=
  Nat.iter n mutation_next memory.

Lemma mutation_next_present memory : fst (mutation_next memory) 1 <> None.
Proof. discriminate. Qed.

Lemma mutation_round_logs_length n memory : length (mutation_round_logs n memory) = 2*n.
Proof.
  unfold mutation_round_logs.
  rewrite flat_map_fixed_length with (k:=2).
  - now rewrite seq_length.
  - intros; reflexivity.
Qed.

Lemma mutation_loop_batches_nd memory ctx c :
  fst memory 1 <> None ->
  run_nd mutation_loop (memory,(ctx,c)) ~
    (emit_batches mutation_logs mutation_next memory :
      ctreeW (CSLObs (nat * nat)) Bn (SSig * unit)).
Proof.
  apply (emit_batches_bisim mutation_logs mutation_next
    (fun m => fst m 1 <> None) (fun m => run_nd mutation_loop (m,(ctx,c)))).
  - intros; apply mutation_next_present.
  - intros; discriminate.
  - intros; apply mutation_loop_round_nd; assumption.
Qed.

Lemma mutation_loop_batches_rr memory ctx c :
  fst memory 1 <> None ->
  run_rr mutation_loop (memory,(ctx,c)) ~
    (emit_batches (fun m => List.map inl (mutation_logs m)) mutation_next memory :
      ctreeW rr_obs Bn (SSig * unit)).
Proof.
  apply (emit_batches_bisim (fun m => List.map inl (mutation_logs m)) mutation_next
    (fun m => fst m 1 <> None) (fun m => run_rr mutation_loop (m,(ctx,c)))).
  - intros; apply mutation_next_present.
  - intros; discriminate.
  - intros; apply mutation_loop_round_rr; assumption.
Qed.

Theorem mutation_loop_prefix_nd n ctx c :
  run_nd mutation_loop ((hsingle 1 0,hemp),(ctx,c)) ~
  emit_list (mutation_round_logs n (hsingle 1 0,hemp))
    (run_nd mutation_loop (mutation_after n (hsingle 1 0,hemp),(ctx,c))) /\
  length (mutation_round_logs n (hsingle 1 0,hemp)) = 2*n.
Proof.
  split; [|apply mutation_round_logs_length].
  rewrite mutation_loop_batches_nd by discriminate.
  unfold mutation_round_logs, mutation_after.
  etransitivity; [apply emit_batches_prefix_sbisim|].
  apply emit_list_sbisim; symmetry; apply mutation_loop_batches_nd.
  apply (@Nat.iter_invariant n ManagedHeap mutation_next
    (fun m => fst m 1 <> None)).
  - intros; apply mutation_next_present.
  - discriminate.
Qed.

Theorem mutation_loop_prefix_rr n ctx c :
  run_rr mutation_loop ((hsingle 1 0,hemp),(ctx,c)) ~
  emit_list (List.map inl (mutation_round_logs n (hsingle 1 0,hemp)))
    (run_rr mutation_loop (mutation_after n (hsingle 1 0,hemp),(ctx,c))) /\
  length (mutation_round_logs n (hsingle 1 0,hemp)) = 2*n.
Proof.
  split; [|apply mutation_round_logs_length].
  rewrite mutation_loop_batches_rr by discriminate.
  assert (Elogs : List.map (@inl (CSLObs (nat * nat)) nat)
      (mutation_round_logs n (hsingle 1 0,hemp)) =
    List.flat_map (fun j => List.map inl
      (mutation_logs (Nat.iter j mutation_next (hsingle 1 0,hemp)))) (List.seq 0 n)).
  { unfold mutation_round_logs; induction (List.seq 0 n) as [|j rest IH]; cbn;
      [reflexivity|rewrite IH; reflexivity]. }
  rewrite Elogs; unfold mutation_after.
  etransitivity; [apply emit_batches_prefix_sbisim|].
  apply emit_list_sbisim; symmetry; apply mutation_loop_batches_rr.
  apply (@Nat.iter_invariant n ManagedHeap mutation_next
    (fun m => fst m 1 <> None)).
  - intros; apply mutation_next_present.
  - discriminate.
Qed.


Lemma mutation_batches_agaf {X} memory w value :
  (value=1 \/ value=2) -> fst memory 1 <> None -> not_done w ->
  <( {(emit_batches mutation_logs mutation_next memory :
      ctreeW (CSLObs (nat * nat)) Bn X)}, w
    |=L AG (AF visW {csl_heap (fun m => fst m 1 = Some value)}) )>.
Proof.
  intros V H Hw.
  eapply (emit_batches_agaf mutation_logs mutation_next (fun m => fst m 1 <> None)
    (fun _ => 0) (csl_heap (fun m => fst m 1 = Some value))).
  - intros; apply mutation_next_present.
  - intros; discriminate.
  - intros m Hm; left; destruct V as [-> | ->].
    + exists (CSLHeap (mutation_store m 1)); split; [left; reflexivity|].
      cbn [csl_heap mutation_store fst]; apply upd_eq.
    + exists (CSLHeap (mutation_next m)); split; [right; left; reflexivity|].
      cbn [csl_heap mutation_next mutation_store fst]; apply upd_eq.
  - exact H.
  - exact Hw.
Qed.

Theorem mutation_loop_agaf_nd value ctx c :
  (value=1 \/ value=2) ->
  <( {run_nd mutation_loop ((hsingle 1 0,hemp),(ctx,c))}, Pure
    |=L AG (AF visW {csl_heap (fun m => fst m 1 = Some value)}) )>.
Proof.
  intro V.
  (** The inner eventuality is a source loop proof; its finite body reaches
      either requested snapshot before a new loop-head cutpoint is needed. *)
  assert (HAF : forall n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      h allocs ctx' c' w,
      h 1 <> None -> not_done w ->
      <( {interp_schedule_nd sh (S n)
        (ts @ i := (denote_flow (CUntilNone mutation_body) >>= fun _ => Ret tt))
        (Some i) ((h,allocs),(ctx',c'))}, w
        |=L AF visW {csl_heap (fun m => fst m 1 = Some value)} )>).
  { intros n0 ts0 i0 h0 allocs0 ctx0 c0 w0 H0 Hw0.
    eapply (af_csl_nd_until_none_wf (b:=false) mutation_body (fun _ => Ret tt)
      (fun (_ : nat) _ _ _ sigma w => fst (csl_memory sigma) 1 <> None /\ not_done w)
      lt <( visW {csl_heap (fun m => fst m 1 = Some value)} )>) with (g:=0).
    - apply lt_wf.
    - intros g n ts i [[h allocs] [ctx' c']] w [H1 Hw].
      cbn [csl_memory fst] in H1.
      lazymatch goal with |- quntil _ _ ?Cut _ _ =>
        assert (HC : Proper (sbisim eq ==> eq ==> iff) Cut)
          by (intros t u Et z z' ->; setoid_rewrite Et; reflexivity)
      end.
      lazymatch goal with |- quntil ?q ?P ?Cut _ _ =>
        change (quntil q P Cut
          (interp_schedule_nd sh (S n)
            (ts @ i := (denote_flow
              (CBind (CWrite 1 1) (fun _ =>
                CBind (CWrite 1 2) (fun _ => CRet (Some tt)))) >>=
              until_tail mutation_body (fun _ => Ret tt)))
            (Some i) ((h,allocs),(ctx',c'))) w)
      end.
      rewrite u_csl_nd_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_nd_write by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      right; split; [apply ticll_top; exact Hw|].
      destruct V as [E|E]; subst value.
      + rewrite quntil_unfold; left; left.
        apply ticl_vis; constructor; cbn [csl_heap fst]; apply upd_eq.
      + rewrite u_csl_nd_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        rewrite u_csl_nd_write by
          (first [rewrite upd_eq; discriminate | assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        right; split; [apply ticll_top; constructor|].
        rewrite quntil_unfold; left; left.
        apply ticl_vis; constructor; cbn [csl_heap fst]; apply upd_eq.
    - split; assumption.
  }
  change <( {interp_schedule_nd sh 1
    (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 :=
      (denote_flow (CUntilNone mutation_body) >>= fun _ => Ret tt))
    (Some Fin.F1) ((hsingle 1 0,hemp),(ctx,c))}, Pure
    |=L AG (AF visW {csl_heap (fun m => fst m 1 = Some value)}) )>.
  eapply (ag_csl_nd_until_none mutation_body (fun _ => Ret tt)
    (fun (_ : unit) _ _ _ sigma w => fst (csl_memory sigma) 1 <> None /\ not_done w)
    <( AF visW {csl_heap (fun m => fst m 1 = Some value)} )>) with (g:=tt).
  - intros [] n ts i [[h allocs] [ctx' c']] w [H1 Hw].
    cbn [csl_memory fst] in H1.
    (** Returning from the body resumes its actual guarded loop continuation,
        not a native return of the scheduled pool. *)
    assert (Htail : <( {interp_schedule_nd sh (S n)
      (ts @ i := (denote_flow (CRet (Some tt)) >>=
        until_tail mutation_body (fun _ => Ret tt)))
      (Some i) ((upd (upd h 1 1) 1 2,allocs),(ctx',c'))},
      {Obs (Log (CSLHeap (upd (upd h 1 1) 1 2,allocs))) tt}
      |=L AF visW {csl_heap (fun m => fst m 1 = Some value)} )>).
    { lazymatch goal with |- entailsL _ _ ?t ?z =>
        change (quntil Q_A (entails (SSig * unit) false <( ⊤ )>)
          (entails (SSig * unit) false <( visW {csl_heap (fun m => fst m 1 = Some value)} )>) t z)
      end.
      rewrite (u_csl_nd_ret (A:=option unit)) by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      cbn [until_tail].
      rewrite u_csl_nd_guard by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      pose proof (HAF n ts i (upd (upd h 1 1) 1 2) allocs ctx' c'
        (Obs (Log (CSLHeap (upd (upd h 1 1) 1 2,allocs))) tt)
        ltac:(rewrite upd_eq; discriminate) ltac:(constructor)) as Hfuture.
      apply ticl_au in Hfuture; exact Hfuture.
    }
    assert (Hremaining : <( {interp_schedule_nd sh (S n)
      (ts @ i := (denote_flow
        (CBind (CWrite 1 2) (fun _ => CRet (Some tt))) >>=
        until_tail mutation_body (fun _ => Ret tt)))
      (Some i) ((upd h 1 1,allocs),(ctx',c'))},
      {Obs (Log (CSLHeap (upd h 1 1,allocs))) tt}
      |=L AF visW {csl_heap (fun m => fst m 1 = Some value)} )>).
    { lazymatch goal with |- entailsL _ _ ?t ?z =>
        change (quntil Q_A (entails (SSig * unit) false <( ⊤ )>)
          (entails (SSig * unit) false <( visW {csl_heap (fun m => fst m 1 = Some value)} )>) t z)
      end.
      rewrite u_csl_nd_bind by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_nd_write by
        (first [rewrite upd_eq; discriminate | typeclasses eauto |
          intros; eapply ticl_not_done; eassumption]).
      right; split; [apply ticll_top; constructor|].
      apply ticl_au in Htail; exact Htail.
    }
    lazymatch goal with |- qnext _ _ (quntil _ _ ?Cut) _ _ =>
      assert (HC : Proper (sbisim eq ==> eq ==> iff) Cut)
        by (intros t u Et z z' ->; setoid_rewrite Et; reflexivity)
    end.
    lazymatch goal with |- qnext ?q ?P ?Q _ _ =>
      change (qnext q P Q
        (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow
            (CBind (CWrite 1 1) (fun _ =>
              CBind (CWrite 1 2) (fun _ => CRet (Some tt)))) >>=
            until_tail mutation_body (fun _ => Ret tt)))
          (Some i) ((h,allocs),(ctx',c'))) w)
    end.
    rewrite x_csl_nd_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
    rewrite x_csl_nd_write by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
    split.
    + apply (af_log (b:=false)); [exact Hw|exact Hremaining].
    + rewrite u_csl_nd_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_nd_write by
        (first [rewrite upd_eq; discriminate | assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      right; split.
      * apply (af_log (b:=false)); [constructor|exact Htail].
      * rewrite u_csl_nd_ret by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        cbn [until_tail].
        rewrite u_csl_nd_guard by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        rewrite quntil_unfold; left; left.
        exists tt, n, ts, i,
          ((upd (upd h 1 1) 1 2,allocs),(ctx',c')).
        split; [ split; [discriminate|constructor] | reflexivity ].
  - split; [discriminate|constructor].
Qed.

Theorem mutation_loop_agaf_rr value ctx c :
  (value=1 \/ value=2) ->
  <( {run_rr mutation_loop ((hsingle 1 0,hemp),(ctx,c))}, Pure
    |=L AG (AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value))}) )>.
Proof.
  intro V.
  (** The inner eventuality is a source loop proof; its finite body reaches
      either requested snapshot before a new loop-head cutpoint is needed. *)
  assert (HAF : forall n (ts : pool sE Bn (S n)) (i : Fin.t (S n)) (cursor : nat)
      h allocs ctx' c' w,
      h 1 <> None -> not_done w ->
      <( {interp_schedule_rr sh (S n)
        (ts @ i := (denote_flow (CUntilNone mutation_body) >>= fun _ => Ret tt))
        (Some i) cursor ((h,allocs),(ctx',c'))}, w
        |=L AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value))} )>).
  { intros n0 ts0 i0 cursor0 h0 allocs0 ctx0 c0 w0 H0 Hw0.
    eapply (af_csl_rr_until_none_wf (b:=false) mutation_body (fun _ => Ret tt)
      (fun (_ : nat) _ _ _ _ sigma w => fst (csl_memory sigma) 1 <> None /\ not_done w)
      lt <( visW {fair_obs (csl_heap (fun m => fst m 1 = Some value))} )>) with (g:=0).
    - apply lt_wf.
    - intros g n ts i cursor [[h allocs] [ctx' c']] w [H1 Hw].
      cbn [csl_memory fst] in H1.
      lazymatch goal with |- quntil _ _ ?Cut _ _ =>
        assert (HC : Proper (sbisim eq ==> eq ==> iff) Cut)
          by (intros t u Et z z' ->; setoid_rewrite Et; reflexivity)
      end.
      lazymatch goal with |- quntil ?q ?P ?Cut _ _ =>
        change (quntil q P Cut
          (interp_schedule_rr sh (S n)
            (ts @ i := (denote_flow
              (CBind (CWrite 1 1) (fun _ =>
                CBind (CWrite 1 2) (fun _ => CRet (Some tt)))) >>=
              until_tail mutation_body (fun _ => Ret tt)))
            (Some i) cursor ((h,allocs),(ctx',c'))) w)
      end.
      rewrite u_csl_rr_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_rr_write by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      right; split; [apply ticll_top; exact Hw|].
      destruct V as [E|E]; subst value.
      + rewrite quntil_unfold; left; left.
        apply ticl_vis; constructor; cbn [fair_obs csl_heap fst]; apply upd_eq.
      + rewrite u_csl_rr_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        rewrite u_csl_rr_write by
          (first [rewrite upd_eq; discriminate | assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        right; split; [apply ticll_top; constructor|].
        rewrite quntil_unfold; left; left.
        apply ticl_vis; constructor; cbn [fair_obs csl_heap fst]; apply upd_eq.
    - split; assumption.
  }
  change <( {interp_schedule_rr sh 1
    (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 :=
      (denote_flow (CUntilNone mutation_body) >>= fun _ => Ret tt))
    (Some Fin.F1) 0 ((hsingle 1 0,hemp),(ctx,c))}, Pure
    |=L AG (AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value))}) )>.
  eapply (ag_csl_rr_until_none mutation_body (fun _ => Ret tt)
    (fun (_ : unit) _ _ _ _ sigma w => fst (csl_memory sigma) 1 <> None /\ not_done w)
    <( AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value))} )>) with (g:=tt).
  - intros [] n ts i cursor [[h allocs] [ctx' c']] w [H1 Hw].
    cbn [csl_memory fst] in H1.
    (** Returning from the body resumes its actual guarded loop continuation,
        not a native return of the scheduled pool. *)
    assert (Htail : <( {interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow (CRet (Some tt)) >>=
        until_tail mutation_body (fun _ => Ret tt)))
      (Some i) cursor ((upd (upd h 1 1) 1 2,allocs),(ctx',c'))},
      {Obs (Log (inl (CSLHeap (upd (upd h 1 1) 1 2,allocs)))) tt}
      |=L AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value))} )>).
    { lazymatch goal with |- entailsL _ _ ?t ?z =>
        change (quntil Q_A (entails (SSig * unit) false <( ⊤ )>)
          (entails (SSig * unit) false <( visW {fair_obs (csl_heap (fun m => fst m 1 = Some value))} )>) t z)
      end.
      rewrite (u_csl_rr_ret (A:=option unit)) by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      cbn [until_tail].
      rewrite u_csl_rr_guard by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      pose proof (HAF n ts i cursor (upd (upd h 1 1) 1 2) allocs ctx' c'
        (Obs (Log (inl (CSLHeap (upd (upd h 1 1) 1 2,allocs)))) tt)
        ltac:(rewrite upd_eq; discriminate) ltac:(constructor)) as Hfuture.
      apply ticl_au in Hfuture; exact Hfuture.
    }
    assert (Hremaining : <( {interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow
        (CBind (CWrite 1 2) (fun _ => CRet (Some tt))) >>=
        until_tail mutation_body (fun _ => Ret tt)))
      (Some i) cursor ((upd h 1 1,allocs),(ctx',c'))},
      {Obs (Log (inl (CSLHeap (upd h 1 1,allocs)))) tt}
      |=L AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value))} )>).
    { lazymatch goal with |- entailsL _ _ ?t ?z =>
        change (quntil Q_A (entails (SSig * unit) false <( ⊤ )>)
          (entails (SSig * unit) false <( visW {fair_obs (csl_heap (fun m => fst m 1 = Some value))} )>) t z)
      end.
      rewrite u_csl_rr_bind by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_rr_write by
        (first [rewrite upd_eq; discriminate | typeclasses eauto |
          intros; eapply ticl_not_done; eassumption]).
      right; split; [apply ticll_top; constructor|].
      apply ticl_au in Htail; exact Htail.
    }
    lazymatch goal with |- qnext _ _ (quntil _ _ ?Cut) _ _ =>
      assert (HC : Proper (sbisim eq ==> eq ==> iff) Cut)
        by (intros t u Et z z' ->; setoid_rewrite Et; reflexivity)
    end.
    lazymatch goal with |- qnext ?q ?P ?Q _ _ =>
      change (qnext q P Q
        (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow
            (CBind (CWrite 1 1) (fun _ =>
              CBind (CWrite 1 2) (fun _ => CRet (Some tt)))) >>=
            until_tail mutation_body (fun _ => Ret tt)))
          (Some i) cursor ((h,allocs),(ctx',c'))) w)
    end.
    rewrite x_csl_rr_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
    rewrite x_csl_rr_write by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
    split.
    + apply (af_log (b:=false)); [exact Hw|exact Hremaining].
    + rewrite u_csl_rr_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_rr_write by
        (first [rewrite upd_eq; discriminate | assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      right; split.
      * apply (af_log (b:=false)); [constructor|exact Htail].
      * rewrite u_csl_rr_ret by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        cbn [until_tail].
        rewrite u_csl_rr_guard by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        rewrite quntil_unfold; left; left.
        exists tt, n, ts, i, cursor,
          ((upd (upd h 1 1) 1 2,allocs),(ctx',c')).
        split; [ split; [discriminate|constructor] | reflexivity ].
  - split; [discriminate|constructor].
Qed.

Definition spin_rr_at cursor s :=
  interp_schedule_rr sh 1 [denote mutation_spin]%vector (Some Fin.F1) cursor s.

Lemma mutation_spin_round_rr cursor s : spin_rr_at cursor s ~
  Vis (Log (inr 0)) (fun _ => spin_rr_at (S cursor) s).
Proof.
  unfold spin_rr_at, denote at 1.
  change ([denote_flow mutation_spin;; Ret tt]%vector : pool sE Bn 1) with
    (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow mutation_spin >>= fun _ => Ret tt)).
  unfold mutation_spin at 1; rewrite interp_rr_until_none, interp_rr_bind, interp_rr_yield.
  rewrite interp_schedule_rr_select.
  rewrite rr_pick_0; cbn [slot_index]; apply sb_vis; intros [].
  rewrite interp_rr_ret.
  erewrite interp_schedule_rr_guard by (rewrite Vector.nth_replace_eq; reflexivity).
  cbn [Vector.replace]; reflexivity.
Qed.

Lemma mutation_spin_round_nd s : run_nd mutation_spin s ~ Step (run_nd mutation_spin s).
Proof.
  unfold run_nd, run_nd_pool, csl_pool, denote at 1.
  cbn [Vector.map].
  change ([denote_flow mutation_spin;; Ret tt]%vector : pool sE Bn 1) with
    (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 := (denote_flow mutation_spin >>= fun _ => Ret tt)).
  unfold mutation_spin at 1; rewrite interp_nd_source_until_none,
    interp_nd_source_bind, interp_nd_source_yield, interp_schedule_nd_select.
  apply sb_br_l with (y:=Fin.F1); intro i.
  assert (Hi : i=Fin.F1) by (dependent destruction i; [reflexivity|inversion i]).
  subst i; apply sb_step.
  rewrite interp_nd_source_ret.
  erewrite (interp_schedule_nd_guard sh) by (rewrite Vector.nth_replace_eq; reflexivity).
  cbn [Vector.replace]; reflexivity.
Qed.

Section SilentSteps.
  Context {J X : Type} (root : J -> ctreeW (CSLObs (nat * nat)) Bn X)
    (next : J -> J)
    (Hstep : forall i, root i ~ Step (root (next i))).

  Lemma step_only_ag i w : not_done w -> <( {root i}, w |=L AG ⊤ )>.
  Proof. exact (ag_step_family root next Hstep i w). Qed.

  Lemma step_only_no_heap i :
    ~ <( {root i}, Pure |=L EF visW {csl_heap (fun _ => True)} )>.
  Proof. apply (step_family_no_ef_visible root next Hstep). Qed.
End SilentSteps.

Theorem mutation_spin_no_heap_nd ctx c :
  <( {run_nd mutation_spin ((hsingle 1 0,hemp),(ctx,c))}, Pure |=L AG ⊤ )> /\
  ~ <( {run_nd mutation_spin ((hsingle 1 0,hemp),(ctx,c))}, Pure
       |=L EF visW {csl_heap (fun _ => True)} )>.
Proof.
  split.
  - exact (step_only_ag (fun _ : unit => run_nd mutation_spin ((hsingle 1 0,hemp),(ctx,c)))
      (fun x => x) (fun _ => mutation_spin_round_nd _) tt Pure ltac:(constructor)).
  - exact (step_only_no_heap (fun _ : unit => run_nd mutation_spin ((hsingle 1 0,hemp),(ctx,c)))
      (fun x => x) (fun _ => mutation_spin_round_nd _) tt).
Qed.

Theorem mutation_spin_no_heap_rr ctx c :
  <( {run_rr mutation_spin ((hsingle 1 0,hemp),(ctx,c))}, Pure |=L AG ⊤ )> /\
  ~ <( {run_rr mutation_spin ((hsingle 1 0,hemp),(ctx,c))}, Pure
       |=L EF visW {fair_obs (csl_heap (fun _ => True))} )>.
Proof.
  split.
  - exact (ag_log_family (fun cursor => spin_rr_at cursor ((hsingle 1 0,hemp),(ctx,c))) S
      (fun _ => inr 0) (fun cursor => mutation_spin_round_rr cursor _)
      0 Pure ltac:(constructor)).
  - exact (log_family_no_ef_visible
      (fun cursor => spin_rr_at cursor ((hsingle 1 0,hemp),(ctx,c))) S
      (fun _ => inr 0) (fun cursor => mutation_spin_round_rr cursor _)
      (fair_obs (csl_heap (fun _ => True))) ltac:(intros cursor H; exact H) 0).
Qed.

Theorem empty_log_pool_selection ctx c :
  run_nd mutation_spin ((hsingle 1 0,hemp),(ctx,c)) ~
    Step (run_nd mutation_spin ((hsingle 1 0,hemp),(ctx,c))) /\
  turn_labels ([] : list (CSLObs (nat * nat))) = [τ] /\
  <( {run_nd mutation_spin ((hsingle 1 0,hemp),(ctx,c))}, Pure |=L AG ⊤ )>.
Proof.
  split; [apply mutation_spin_round_nd|split; [reflexivity|]].
  exact (proj1 (mutation_spin_no_heap_nd ctx c)).
Qed.

Theorem mutation_observation_replaced ctx c :
  (forall (t : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)),
    ~ <( t, Pure |=L visW {csl_heap (fun _ => True)} )>) /\
  (forall (t : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)),
    <( t, {Obs (Log (CSLHeap probe_written)) tt} |=L
      visW {csl_heap (fun m => fst m 1 = Some 9)} )>) /\
  (forall (t : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)),
    ~ <( t, {Obs (Log (CSLEmit (stamp (7,9) c)) : writerE (CSLObs (nat * nat)) unit) tt}
      |=L visW {csl_heap (fun _ => True)} )>) /\
  instr_flow_erased (CBind (CWrite 1 9) (fun _ =>
      CBind (CEmit 7 9) (fun _ => CRet tt))) ((hsingle 1 0,hemp),(ctx,c)) ~
    emit_list [CSLHeap probe_written; CSLEmit (stamp (7,9) c)]
      (Ret ((probe_written,(ctx,S c)),Some tt) : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)).
Proof.
  split; [intros t H; apply ticl_vis in H; inversion H|].
  split.
  - intro t; apply ticl_vis; constructor; cbn [csl_heap probe_written fst]; apply upd_eq.
  - split.
    + intros t H; apply ticl_vis in H; dependent destruction H; contradiction.
    + rewrite instr_flow_write by discriminate.
      cbn [emit_list List.fold_right]; rewrite !log_vis; apply sb_vis; intros [].
      rewrite instr_flow_emit; rewrite !log_vis; apply sb_vis; intros [].
      rewrite instr_flow_ret; reflexivity.
Qed.

Definition mutation_frame : ManagedHeap := region 2 7.
Definition mutation_framed_memory : ManagedHeap := region 1 0 ⊎ mutation_frame.

Lemma mutation_framed_initial :
  fst mutation_framed_memory 1 <> None /\ fst mutation_framed_memory 2 = Some 7.
Proof. split; cbn [mutation_framed_memory mutation_frame region pop fst snd hunion hsingle]; discriminate || reflexivity. Qed.

Lemma mutation_framed_batches_agaf {X} memory w value :
  (value=1 \/ value=2) -> fst memory 1 <> None -> fst memory 2=Some 7 -> not_done w ->
  <( {(emit_batches mutation_logs mutation_next memory :
      ctreeW (CSLObs (nat * nat)) Bn X)}, w
    |=L AG (AF visW {csl_heap (fun m => fst m 1 = Some value /\ fst m 2=Some 7)}) )>.
Proof.
  intros V H1 H2 Hw.
  eapply (emit_batches_agaf mutation_logs mutation_next
    (fun m => fst m 1 <> None /\ fst m 2=Some 7) (fun _ => 0)
    (csl_heap (fun m => fst m 1=Some value /\ fst m 2=Some 7))).
  - intros m [H H']; split; [apply mutation_next_present|].
    exact H'.
  - intros; discriminate.
  - intros m [H H']; left; destruct V as [-> | ->].
    + exists (CSLHeap (mutation_store m 1)); split; [left; reflexivity|].
      cbn [csl_heap mutation_store fst]; split; [apply upd_eq|exact H'].
    + exists (CSLHeap (mutation_next m)); split; [right; left; reflexivity|].
      cbn [csl_heap mutation_next mutation_store fst]; split; [apply upd_eq|].
      exact H'.
  - split; assumption.
  - exact Hw.
Qed.

Theorem mutation_loop_framed_nd value ctx c :
  (value=1 \/ value=2) ->
  <( {run_nd mutation_loop (frame_state mutation_frame (own 1 0 ctx c))}, Pure
    |=L AG (AF visW {csl_heap (fun m => fst m 1=Some value /\ fst m 2=Some 7)}) )>.
Proof.
  intro V.
  (** The inner eventuality is a source loop proof; its finite body reaches
      either requested snapshot before a new loop-head cutpoint is needed. *)
  assert (HAF : forall n (ts : pool sE Bn (S n)) (i : Fin.t (S n))
      h allocs ctx' c' w,
      h 1 <> None -> h 2 = Some 7 -> not_done w ->
      <( {interp_schedule_nd sh (S n)
        (ts @ i := (denote_flow (CUntilNone mutation_body) >>= fun _ => Ret tt))
        (Some i) ((h,allocs),(ctx',c'))}, w
        |=L AF visW {csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7)} )>).
  { intros n0 ts0 i0 h0 allocs0 ctx0 c0 w0 H0 H20 Hw0.
    eapply (af_csl_nd_until_none_wf (b:=false) mutation_body (fun _ => Ret tt)
      (fun (_ : nat) _ _ _ sigma w => fst (csl_memory sigma) 1 <> None /\ fst (csl_memory sigma) 2 = Some 7 /\ not_done w)
      lt <( visW {csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7)} )>) with (g:=0).
    - apply lt_wf.
    - intros g n ts i [[h allocs] [ctx' c']] w [H1 [H2 Hw]].
      cbn [csl_memory fst] in H1, H2.
      lazymatch goal with |- quntil _ _ ?Cut _ _ =>
        assert (HC : Proper (sbisim eq ==> eq ==> iff) Cut)
          by (intros t u Et z z' ->; setoid_rewrite Et; reflexivity)
      end.
      lazymatch goal with |- quntil ?q ?P ?Cut _ _ =>
        change (quntil q P Cut
          (interp_schedule_nd sh (S n)
            (ts @ i := (denote_flow
              (CBind (CWrite 1 1) (fun _ =>
                CBind (CWrite 1 2) (fun _ => CRet (Some tt)))) >>=
              until_tail mutation_body (fun _ => Ret tt)))
            (Some i) ((h,allocs),(ctx',c'))) w)
      end.
      rewrite u_csl_nd_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_nd_write by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      right; split; [apply ticll_top; exact Hw|].
      destruct V as [E|E]; subst value.
      + rewrite quntil_unfold; left; left.
        apply ticl_vis; constructor; cbn [csl_heap fst]; split; [apply upd_eq|exact H2].
      + rewrite u_csl_nd_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        rewrite u_csl_nd_write by
          (first [rewrite upd_eq; discriminate | assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        right; split; [apply ticll_top; constructor|].
        rewrite quntil_unfold; left; left.
        apply ticl_vis; constructor; cbn [csl_heap fst]; split; [apply upd_eq|exact H2].
    - repeat split; assumption.
  }
  change <( {interp_schedule_nd sh 1
    (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 :=
      (denote_flow (CUntilNone mutation_body) >>= fun _ => Ret tt))
    (Some Fin.F1) (mutation_framed_memory,(ctx,c))}, Pure
    |=L AG (AF visW {csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7)}) )>.
  eapply (ag_csl_nd_until_none mutation_body (fun _ => Ret tt)
    (fun (_ : unit) _ _ _ sigma w => fst (csl_memory sigma) 1 <> None /\ fst (csl_memory sigma) 2 = Some 7 /\ not_done w)
    <( AF visW {csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7)} )>) with (g:=tt).
  - intros [] n ts i [[h allocs] [ctx' c']] w [H1 [H2 Hw]].
    cbn [csl_memory fst] in H1, H2.
    (** Returning from the body resumes its actual guarded loop continuation,
        not a native return of the scheduled pool. *)
    assert (Htail : <( {interp_schedule_nd sh (S n)
      (ts @ i := (denote_flow (CRet (Some tt)) >>=
        until_tail mutation_body (fun _ => Ret tt)))
      (Some i) ((upd (upd h 1 1) 1 2,allocs),(ctx',c'))},
      {Obs (Log (CSLHeap (upd (upd h 1 1) 1 2,allocs))) tt}
      |=L AF visW {csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7)} )>).
    { lazymatch goal with |- entailsL _ _ ?t ?z =>
        change (quntil Q_A (entails (SSig * unit) false <( ⊤ )>)
          (entails (SSig * unit) false <( visW {csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7)} )>) t z)
      end.
      rewrite (u_csl_nd_ret (A:=option unit)) by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      cbn [until_tail].
      rewrite u_csl_nd_guard by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      pose proof (HAF n ts i (upd (upd h 1 1) 1 2) allocs ctx' c'
        (Obs (Log (CSLHeap (upd (upd h 1 1) 1 2,allocs))) tt)
        ltac:(rewrite upd_eq; discriminate) H2 ltac:(constructor)) as Hfuture.
      apply ticl_au in Hfuture; exact Hfuture.
    }
    assert (Hremaining : <( {interp_schedule_nd sh (S n)
      (ts @ i := (denote_flow
        (CBind (CWrite 1 2) (fun _ => CRet (Some tt))) >>=
        until_tail mutation_body (fun _ => Ret tt)))
      (Some i) ((upd h 1 1,allocs),(ctx',c'))},
      {Obs (Log (CSLHeap (upd h 1 1,allocs))) tt}
      |=L AF visW {csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7)} )>).
    { lazymatch goal with |- entailsL _ _ ?t ?z =>
        change (quntil Q_A (entails (SSig * unit) false <( ⊤ )>)
          (entails (SSig * unit) false <( visW {csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7)} )>) t z)
      end.
      rewrite u_csl_nd_bind by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_nd_write by
        (first [rewrite upd_eq; discriminate | typeclasses eauto |
          intros; eapply ticl_not_done; eassumption]).
      right; split; [apply ticll_top; constructor|].
      apply ticl_au in Htail; exact Htail.
    }
    lazymatch goal with |- qnext _ _ (quntil _ _ ?Cut) _ _ =>
      assert (HC : Proper (sbisim eq ==> eq ==> iff) Cut)
        by (intros t u Et z z' ->; setoid_rewrite Et; reflexivity)
    end.
    lazymatch goal with |- qnext ?q ?P ?Q _ _ =>
      change (qnext q P Q
        (interp_schedule_nd sh (S n)
          (ts @ i := (denote_flow
            (CBind (CWrite 1 1) (fun _ =>
              CBind (CWrite 1 2) (fun _ => CRet (Some tt)))) >>=
            until_tail mutation_body (fun _ => Ret tt)))
          (Some i) ((h,allocs),(ctx',c'))) w)
    end.
    rewrite x_csl_nd_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
    rewrite x_csl_nd_write by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
    split.
    + apply (af_log (b:=false)); [exact Hw|exact Hremaining].
    + rewrite u_csl_nd_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_nd_write by
        (first [rewrite upd_eq; discriminate | assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      right; split.
      * apply (af_log (b:=false)); [constructor|exact Htail].
      * rewrite u_csl_nd_ret by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        cbn [until_tail].
        rewrite u_csl_nd_guard by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        rewrite quntil_unfold; left; left.
        exists tt, n, ts, i,
          ((upd (upd h 1 1) 1 2,allocs),(ctx',c')).
        split; [ repeat split; try discriminate; try exact H2; constructor | reflexivity ].
  - split; [exact (proj1 mutation_framed_initial)|split; [exact (proj2 mutation_framed_initial)|constructor]].
Qed.

Theorem mutation_loop_framed_rr value ctx c :
  (value=1 \/ value=2) ->
  <( {run_rr mutation_loop (frame_state mutation_frame (own 1 0 ctx c))}, Pure
    |=L AG (AF visW {fair_obs (csl_heap (fun m => fst m 1=Some value /\ fst m 2=Some 7))}) )>.
Proof.
  intro V.
  (** The inner eventuality is a source loop proof; its finite body reaches
      either requested snapshot before a new loop-head cutpoint is needed. *)
  assert (HAF : forall n (ts : pool sE Bn (S n)) (i : Fin.t (S n)) (cursor : nat)
      h allocs ctx' c' w,
      h 1 <> None -> h 2 = Some 7 -> not_done w ->
      <( {interp_schedule_rr sh (S n)
        (ts @ i := (denote_flow (CUntilNone mutation_body) >>= fun _ => Ret tt))
        (Some i) cursor ((h,allocs),(ctx',c'))}, w
        |=L AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7))} )>).
  { intros n0 ts0 i0 cursor0 h0 allocs0 ctx0 c0 w0 H0 H20 Hw0.
    eapply (af_csl_rr_until_none_wf (b:=false) mutation_body (fun _ => Ret tt)
      (fun (_ : nat) _ _ _ _ sigma w => fst (csl_memory sigma) 1 <> None /\ fst (csl_memory sigma) 2 = Some 7 /\ not_done w)
      lt <( visW {fair_obs (csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7))} )>) with (g:=0).
    - apply lt_wf.
    - intros g n ts i cursor [[h allocs] [ctx' c']] w [H1 [H2 Hw]].
      cbn [csl_memory fst] in H1, H2.
      lazymatch goal with |- quntil _ _ ?Cut _ _ =>
        assert (HC : Proper (sbisim eq ==> eq ==> iff) Cut)
          by (intros t u Et z z' ->; setoid_rewrite Et; reflexivity)
      end.
      lazymatch goal with |- quntil ?q ?P ?Cut _ _ =>
        change (quntil q P Cut
          (interp_schedule_rr sh (S n)
            (ts @ i := (denote_flow
              (CBind (CWrite 1 1) (fun _ =>
                CBind (CWrite 1 2) (fun _ => CRet (Some tt)))) >>=
              until_tail mutation_body (fun _ => Ret tt)))
            (Some i) cursor ((h,allocs),(ctx',c'))) w)
      end.
      rewrite u_csl_rr_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_rr_write by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      right; split; [apply ticll_top; exact Hw|].
      destruct V as [E|E]; subst value.
      + rewrite quntil_unfold; left; left.
        apply ticl_vis; constructor; cbn [fair_obs csl_heap fst]; split; [apply upd_eq|exact H2].
      + rewrite u_csl_rr_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        rewrite u_csl_rr_write by
          (first [rewrite upd_eq; discriminate | assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        right; split; [apply ticll_top; constructor|].
        rewrite quntil_unfold; left; left.
        apply ticl_vis; constructor; cbn [fair_obs csl_heap fst]; split; [apply upd_eq|exact H2].
    - repeat split; assumption.
  }
  change <( {interp_schedule_rr sh 1
    (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 :=
      (denote_flow (CUntilNone mutation_body) >>= fun _ => Ret tt))
    (Some Fin.F1) 0 (mutation_framed_memory,(ctx,c))}, Pure
    |=L AG (AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7))}) )>.
  eapply (ag_csl_rr_until_none mutation_body (fun _ => Ret tt)
    (fun (_ : unit) _ _ _ _ sigma w => fst (csl_memory sigma) 1 <> None /\ fst (csl_memory sigma) 2 = Some 7 /\ not_done w)
    <( AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7))} )>) with (g:=tt).
  - intros [] n ts i cursor [[h allocs] [ctx' c']] w [H1 [H2 Hw]].
    cbn [csl_memory fst] in H1, H2.
    (** Returning from the body resumes its actual guarded loop continuation,
        not a native return of the scheduled pool. *)
    assert (Htail : <( {interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow (CRet (Some tt)) >>=
        until_tail mutation_body (fun _ => Ret tt)))
      (Some i) cursor ((upd (upd h 1 1) 1 2,allocs),(ctx',c'))},
      {Obs (Log (inl (CSLHeap (upd (upd h 1 1) 1 2,allocs)))) tt}
      |=L AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7))} )>).
    { lazymatch goal with |- entailsL _ _ ?t ?z =>
        change (quntil Q_A (entails (SSig * unit) false <( ⊤ )>)
          (entails (SSig * unit) false <( visW {fair_obs (csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7))} )>) t z)
      end.
      rewrite (u_csl_rr_ret (A:=option unit)) by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      cbn [until_tail].
      rewrite u_csl_rr_guard by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      pose proof (HAF n ts i cursor (upd (upd h 1 1) 1 2) allocs ctx' c'
        (Obs (Log (inl (CSLHeap (upd (upd h 1 1) 1 2,allocs)))) tt)
        ltac:(rewrite upd_eq; discriminate) H2 ltac:(constructor)) as Hfuture.
      apply ticl_au in Hfuture; exact Hfuture.
    }
    assert (Hremaining : <( {interp_schedule_rr sh (S n)
      (ts @ i := (denote_flow
        (CBind (CWrite 1 2) (fun _ => CRet (Some tt))) >>=
        until_tail mutation_body (fun _ => Ret tt)))
      (Some i) cursor ((upd h 1 1,allocs),(ctx',c'))},
      {Obs (Log (inl (CSLHeap (upd h 1 1,allocs)))) tt}
      |=L AF visW {fair_obs (csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7))} )>).
    { lazymatch goal with |- entailsL _ _ ?t ?z =>
        change (quntil Q_A (entails (SSig * unit) false <( ⊤ )>)
          (entails (SSig * unit) false <( visW {fair_obs (csl_heap (fun m => fst m 1 = Some value /\ fst m 2 = Some 7))} )>) t z)
      end.
      rewrite u_csl_rr_bind by
        (first [typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_rr_write by
        (first [rewrite upd_eq; discriminate | typeclasses eauto |
          intros; eapply ticl_not_done; eassumption]).
      right; split; [apply ticll_top; constructor|].
      apply ticl_au in Htail; exact Htail.
    }
    lazymatch goal with |- qnext _ _ (quntil _ _ ?Cut) _ _ =>
      assert (HC : Proper (sbisim eq ==> eq ==> iff) Cut)
        by (intros t u Et z z' ->; setoid_rewrite Et; reflexivity)
    end.
    lazymatch goal with |- qnext ?q ?P ?Q _ _ =>
      change (qnext q P Q
        (interp_schedule_rr sh (S n)
          (ts @ i := (denote_flow
            (CBind (CWrite 1 1) (fun _ =>
              CBind (CWrite 1 2) (fun _ => CRet (Some tt)))) >>=
            until_tail mutation_body (fun _ => Ret tt)))
          (Some i) cursor ((h,allocs),(ctx',c'))) w)
    end.
    rewrite x_csl_rr_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
    rewrite x_csl_rr_write by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
    split.
    + apply (af_log (b:=false)); [exact Hw|exact Hremaining].
    + rewrite u_csl_rr_bind by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      rewrite u_csl_rr_write by
        (first [rewrite upd_eq; discriminate | assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
      right; split.
      * apply (af_log (b:=false)); [constructor|exact Htail].
      * rewrite u_csl_rr_ret by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        cbn [until_tail].
        rewrite u_csl_rr_guard by (first [assumption | typeclasses eauto | intros; eapply ticl_not_done; eassumption]).
        rewrite quntil_unfold; left; left.
        exists tt, n, ts, i, cursor,
          ((upd (upd h 1 1) 1 2,allocs),(ctx',c')).
        split; [ repeat split; try discriminate; try exact H2; constructor | reflexivity ].
  - split; [exact (proj1 mutation_framed_initial)|split; [exact (proj2 mutation_framed_initial)|constructor]].
Qed.

Theorem mutation_return_framed ctx c w : not_done w ->
  <( {instr_flow_erased (CWrite 1 1) (frame_state mutation_frame (own 1 0 ctx c))}, w
    |=R AX ret {frame_post mutation_frame (Qwrite 1 ctx c)} )> /\
  (forall s' r w', frame_post mutation_frame (Qwrite 1 ctx c) (s',r) w' ->
    r=Some tt /\ csl_memory s' ≈ region 1 1 ⊎ mutation_frame /\ snd s'=(ctx,c) /\
    w'=Obs (Log (CSLHeap (csl_memory s'))) tt).
Proof.
  intro Hw; split.
  - apply (write_ax_ret_framed 1 2 0 7 ctx c); [exact Hw|].
    apply frame_rel_state, region_frame_inv; lia.
  - intros; apply (frame_post_write 1 2 7 ctx c); assumption.
Qed.

Definition heap_cell2_absent : World (writerE (CSLObs (nat * nat))) -> Prop :=
  fun w => exists memory, w=Obs (Log (CSLHeap memory)) tt /\ fst memory 2=None.

Theorem exact_heap_prefix_not_stable :
  ~ prefix_stable (frameER mutation_frame) (frameRV (X:=unit) mutation_frame)
      (CNow heap_cell2_absent).
Proof.
  intro H; simp prefix_stable in H.
  assert (HR : frameER (A:=nat * nat) mutation_frame unit (Log (CSLHeap (region 1 1)))
    (Log (CSLHeap (region 1 1 ⊎ mutation_frame)))).
  { split; [apply region_disj; lia|split; [apply managed_wf_preallocated|apply peq_refl]]. }
  specialize (H (Obs (Log (CSLHeap (region 1 1))) tt)
    (Obs (Log (CSLHeap (region 1 1 ⊎ mutation_frame))) tt)
    ltac:(constructor) ltac:(constructor; exact HR)).
  assert (HP : heap_cell2_absent (Obs (Log (CSLHeap (region 1 1))) tt)).
  { exists (region 1 1); split; [reflexivity|apply hsingle_neq; lia]. }
  destruct (H HP) as (memory & E & Hnone).
  injection E as E; subst memory.
  cbn [mutation_frame region pop fst snd hunion hsingle] in Hnone; discriminate.
Qed.

Theorem emission_prefix_stable fr (P : indexed (nat * nat) -> Prop) :
  prefix_stable (frameER fr) (frameRV (X:=unit) fr)
    <( AG (AF visW {fun o => match o with CSLEmit emission => P emission | _ => False end}) )>.
Proof.
  simp prefix_stable; split; [intros; exact I|].
  intros w w' _ HW HP.
  destruct HP as [Y e v HP]; dependent destruction e; destruct v.
  match goal with o : CSLObs _ |- _ => destruct o as [memory|context|emission] end; try contradiction.
  assert (HS : simW (frameER fr) (frameRV (X:=unit) fr)
    (Obs (Log (CSLEmit emission)) tt) (Obs (Log (CSLEmit emission)) tt))
    by (constructor; apply frameER_emit).
  pose proof (simW_not_done_right_unique (frameER fr) (frameRV (X:=unit) fr)
    (frameER_right_unique fr) (Obs (Log (CSLEmit emission)) tt) w'
    (Obs (Log (CSLEmit emission)) tt) ltac:(constructor) HW HS) as E.
  rewrite E; constructor; exact HP.
Qed.

Theorem finish_heap_predecessor_framed ctx c :
  simW (frameER (A:=nat * nat) mutation_frame) (frameRV (X:=option unit) mutation_frame)
    (Finish (Log (CSLHeap (region 1 1))) tt (own 1 1 ctx c,Some tt))
    (Finish (Log (CSLHeap (region 1 1 ⊎ mutation_frame))) tt
      (frame_state mutation_frame (own 1 1 ctx c),Some tt)) /\
  done_with (frame_post mutation_frame (Qwrite 1 ctx c))
    (Finish (Log (CSLHeap (region 1 1 ⊎ mutation_frame))) tt
      (frame_state mutation_frame (own 1 1 ctx c),Some tt)) /\
  region 1 1 <> region 1 1 ⊎ mutation_frame.
Proof.
  assert (HI : frame_inv mutation_frame (own 1 1 ctx c)).
  { apply region_frame_inv; lia. }
  assert (HE : frameER (A:=nat * nat) mutation_frame unit (Log (CSLHeap (region 1 1)))
    (Log (CSLHeap (region 1 1 ⊎ mutation_frame)))).
  { split; [exact (proj1 HI)|split; [exact (proj2 HI)|apply peq_refl]]. }
  assert (HR : frameRV mutation_frame (own 1 1 ctx c,Some tt)
    (frame_state mutation_frame (own 1 1 ctx c),Some tt)).
  { split; [reflexivity|apply frame_rel_state; exact HI]. }
  assert (HF : simW (frameER (A:=nat * nat) mutation_frame) (frameRV (X:=option unit) mutation_frame)
    (Finish (Log (CSLHeap (region 1 1))) tt (own 1 1 ctx c,Some tt))
    (Finish (Log (CSLHeap (region 1 1 ⊎ mutation_frame))) tt
      (frame_state mutation_frame (own 1 1 ctx c),Some tt))).
  { constructor; assumption. }
  split; [exact HF|split].
  - eapply (sim_done_with (frameER mutation_frame) (frameRV (X:=option unit) mutation_frame)
      (Qwrite 1 ctx c)); [exact HF|].
    constructor; repeat split; try reflexivity; apply peq_refl.
  - intro E; pose proof (f_equal (fun m => fst m 2) E) as H.
    cbn [mutation_frame region pop fst snd hunion hsingle] in H; discriminate.
Qed.

Definition two_log_body (_ : unit) : ctree (stateE bool) Bn (unit + unit) :=
  put true;; put false;; Ret (inl tt).

Lemma two_log_body_run sigma :
  interp_state (h_stateW (B:=Bn)) (two_log_body tt) sigma ~
    emit_list [true;false] (Ret (false,@inl unit unit tt) : ctreeW bool Bn (bool * (unit + unit))).
Proof.
  unfold two_log_body; rewrite interp_state_bind, interp_state_put.
  rewrite bind_bind; setoid_rewrite bind_ret_l.
  cbn [emit_list List.fold_right fst]; rewrite !log_vis; apply sb_vis; intros [].
  rewrite interp_state_bind, interp_state_put, bind_bind.
  setoid_rewrite bind_ret_l; rewrite !log_vis; apply sb_vis; intros [].
  rewrite interp_state_ret; reflexivity.
Qed.

Theorem two_log_iterator_recurrence sigma w : not_done w ->
  <( {interp_state (h_stateW (B:=Bn)) (CTree.iter two_log_body tt) sigma}, w
    |=L AG (AF visW {fun value : bool => value=true}) )>.
Proof.
  intro Hw.
  eapply (ag_state_iter_logs (h_stateW (B:=Bn)) (X:=unit) (I:=unit)
    (fun _ _ => True) two_log_body <( AF visW {fun value : bool => value=true} )>).
  - intros [] sigma' _; exists tt, false, [true;false].
    split; [discriminate|split; [apply two_log_body_run|exact I]].
  - intros o t v Hv H; rewrite <- (log_vis o t).
    apply (af_log (b:=false)); assumption.
  - intros [] sigma' v _ Hv.
    rewrite interp_state_unfold_iter, two_log_body_run, emit_list_ret_bind.
    eapply af_emit_list_member; [exact Hv|left; reflexivity|reflexivity].
  - exact I.
  - exact Hw.
Qed.

Theorem two_log_detached_suffix_no_target :
  ~ <( {(log false;; Ret (false,tt) : ctreeW bool Bn (bool * unit))}, Pure
     |=L EF visW {fun value : bool => value=true} )>.
Proof.
  rewrite log_vis; intro H.
  apply (proj2 (eu_vis (b:=false) (Log false) (fun _ => Ret (false,tt)) Pure
    <( ⊤ )> <( visW {fun value : bool => value=true} )>)) in H.
  destruct H as [H|[_ [[] H]]].
  - apply ticl_vis in H; inversion H.
  - apply (proj2 (eu_ret (b:=false) (false,tt) (Obs (Log false) tt)
      <( ⊤ )> <( visW {fun value : bool => value=true} )>)) in H.
    cdestruct H.
    + apply ticl_vis in H; dependent destruction H; discriminate.
    + eapply (en_ret (b:=false)); exact H.
Qed.

Theorem invalid_and_double_free_prefix ctx c :
  let allocated := managed_alloc managed_empty 1 2 in
  let freed := (hfree_block 1 2 (fst allocated),hfree 1 (snd allocated)) in
  (instr_flow_erased (CBind (CFree 2) (fun _ => CRet tt)) (allocated,(ctx,c)) ~
    (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))) /\
  (instr_flow_erased (CBind (CAlloc 2) (fun base =>
      CBind (CFree base) (fun _ => CBind (CFree base) (fun _ => CRet tt))))
      (managed_empty,(ctx,c)) ~ emit_list [CSLHeap allocated;CSLHeap freed]
        (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit))).
Proof.
  intros allocated freed; split.
  - apply instr_flow_free_invalid; reflexivity.
  - rewrite instr_flow_alloc_first with (base:=1).
    2:lia. 2:lia. 2:{ intros offset H; reflexivity. } 2:{ intros j Hj Hlt; lia. }
    cbn [emit_list List.fold_right]; rewrite !log_vis; apply sb_vis; intros [].
    rewrite instr_flow_free with (memory':=freed) by reflexivity.
    rewrite !log_vis; apply sb_vis; intros [].
    apply instr_flow_free_invalid; reflexivity.
Qed.

Definition queue_probe_heap : Heap := new_queue_heap 1 [10;20] hemp.
Definition queue_probe_allocs : AllocationTable := upd hemp 1 6.
Definition queue_probe_view (o : CSLObs (nat * nat)) :=
  match o with
  | CSLHeap memory => Some (fst memory 1,fst memory 2,fst memory 4,fst memory 6)
  | _ => None
  end.

Theorem queue_snapshot_prefix ctx c :
  run_rr (allocated_shared_queue [10;20]) (managed_empty,(ctx,c)) ~
    emit_list (List.map inl (new_queue_logs 1 [10;20] managed_empty))
      (Vis (Log (inr 0)) (fun _ =>
       emit_list (List.map inl (queue_turn_logs (CSLEmit (stamp (2,10) c))
          1 3 5 5 (queue_probe_heap,queue_probe_allocs)))
       (Vis (Log (inr 1)) (fun _ =>
        emit_list (List.map inl (queue_turn_logs (CSLEmit (stamp (1,20) (S c)))
          1 5 3 3 (qstep 1 [3;5] queue_probe_heap,queue_probe_allocs)))
         (run_rr_pool [worker 2 1;worker 1 1]%vector None 2
           ((qstepN 1 2 [3;5] queue_probe_heap,queue_probe_allocs),(ctx,S (S c)))))))) /\
  length (new_queue_logs (A:=nat * nat) 1 [10;20] managed_empty)=7 /\
  List.map queue_probe_view (new_queue_logs 1 [10;20] managed_empty) =
    [Some (Some 0,Some 0,Some 0,Some 0);
     Some (Some 5,Some 0,Some 0,Some 0);
     Some (Some 5,Some 3,Some 0,Some 0);
     Some (Some 5,Some 3,Some 0,Some 0);
     Some (Some 5,Some 3,Some 5,Some 0);
     Some (Some 5,Some 3,Some 5,Some 0);
     Some (Some 5,Some 3,Some 5,Some 0)] /\
  List.map queue_probe_view (queue_turn_logs (CSLEmit (stamp (2,10) c))
      1 3 5 5 (queue_probe_heap,queue_probe_allocs)) =
    [None;Some (Some 5,Some 5,Some 5,Some 0);
     Some (Some 5,Some 5,Some 5,Some 3);
     Some (Some 5,Some 5,Some 0,Some 3);
     Some (Some 3,Some 5,Some 0,Some 3)].
Proof.
  split.
  - rewrite run_rr_allocated_shared_queue; apply emit_list_sbisim.
    unfold shared_queue; rewrite run_rr_two_forks.
    pose proof (allocated_shared_queue_rep [10;20]) as Hq0.
    change (qrep 1 [3;5] [10;20] queue_probe_heap) in Hq0.
    pose proof (qstep_qrep 1 [3;5] [10;20] queue_probe_heap Hq0 ltac:(discriminate)) as Hq1.
    change (qrep 1 [5;3] [20;10] (qstep 1 [3;5] queue_probe_heap)) in Hq1.
    rewrite (run_rr_pool_select [worker 2 1;worker 1 1]%vector 0), (rr_pick_even 0 eq_refl).
    cbn [slot_index]; apply sb_vis; intros [].
    etransitivity; [exact (run_rr_pool_turn [worker 2 1;worker 1 1]%vector Fin.F1 1 _ _ _
      (exact_worker_turn 2 1 3 [5] 10 [20] queue_probe_heap queue_probe_allocs ctx c Hq0))|].
    apply emit_list_sbisim.
    rewrite (run_rr_pool_select [worker 2 1;worker 1 1]%vector 1), (rr_pick_odd 1 eq_refl).
    cbn [slot_index]; apply sb_vis; intros [].
    etransitivity; [exact (run_rr_pool_turn [worker 2 1;worker 1 1]%vector (Fin.FS Fin.F1) 2 _ _ _
      (exact_worker_turn 1 1 5 [3] 20 [10] (qstep 1 [3;5] queue_probe_heap)
        queue_probe_allocs ctx (S c) Hq1))|].
    apply emit_list_sbisim; reflexivity.
  - repeat split; reflexivity.
Qed.

Definition allocator_probe_script : list Actor :=
  [Owner;Owner;Owner;Owner;Owner;Remote1;Remote1;Remote1;Remote0;Remote0;
   Remote0;Remote0;Remote1;Owner;Owner;Owner;Owner;Owner;Owner].

Fixpoint allocator_probe_snapshots (h : Heap) (writes : list (nat * nat))
  : list (CSLObs (nat * nat)) :=
  match writes with
  | [] => []
  | (address,value)::rest =>
      CSLHeap (upd h address value,upd hemp 1 (page_size 2)) ::
        allocator_probe_snapshots (upd h address value) rest
  end.
Definition allocator_probe_mutations :=
  allocator_probe_snapshots (aheap (initial_state 2 0))
    [(1,0);(3,0);(2,8);(4,6);(2,0);(5,8);(5,0);(9,2);(8,0);(4,0);
     (7,1);(6,0);(1,6);(1,0);(3,6);(6,0);(2,6);(3,0);(2,0);(4,6)].
Definition allocator_probe_turn i : list (CSLObs (nat * nat)) :=
  (match i with
   | 1 => firstn 2 allocator_probe_mutations
   | 3 => firstn 2 (skipn 2 allocator_probe_mutations)
   | 4 => firstn 2 (skipn 4 allocator_probe_mutations)
   | 5 => firstn 2 (skipn 6 allocator_probe_mutations)
   | 7 => firstn 1 (skipn 8 allocator_probe_mutations)
   | 8 => firstn 2 (skipn 9 allocator_probe_mutations)
   | 10 => firstn 1 (skipn 11 allocator_probe_mutations)
   | 11 => firstn 1 (skipn 12 allocator_probe_mutations)
   | 14 => firstn 2 (skipn 13 allocator_probe_mutations)
   | 15 => firstn 3 (skipn 15 allocator_probe_mutations)
   | 17 => firstn 2 (skipn 18 allocator_probe_mutations)
   | _ => [] end) ++
  (match i with
   | 3 => [CSLEmit (stamp (tag_alloc,6) 0)]
   | 4 => [CSLEmit (stamp (tag_alloc,8) 1)]
   | 11 => [CSLEmit (stamp (tag_retire,6) 2)]
   | 12 => [CSLEmit (stamp (tag_retry,8) 3)]
   | 15 => [CSLEmit (stamp (tag_reclaim,6) 4)]
   | 17 => [CSLEmit (stamp (tag_alloc,6) 5)]
   | _ => [] end).
Definition allocator_probe_logs := List.concat (List.map allocator_probe_turn (List.seq 0 19)).

Theorem allocator_snapshot_prefix ctx :
  length (new_page_logs (A:=nat * nat) 1 2 managed_empty)=8 /\
  csl_emissions allocator_probe_logs =
    [stamp (tag_alloc,6) 0;stamp (tag_alloc,8) 1;stamp (tag_retire,6) 2;
     stamp (tag_retry,8) 3;stamp (tag_reclaim,6) 4;stamp (tag_alloc,6) 5] /\
  (forall i, i<19 -> exists middle logs next,
    run_turns (turn 1) (fun xs => xs) (firstn i allocator_probe_script) (initial_state 2 0)=
      Some (middle,logs) /\
    turn 1 (List.nth i allocator_probe_script Remote1) middle=Some (next,allocator_probe_turn i)) /\
  (exists last labels residual,
    run_turns (turn 1) (fun xs => xs) allocator_probe_script (initial_state 2 0)=
      Some (last,allocator_probe_logs) /\
    label_logs labels=new_page_logs 1 2 managed_empty ++ allocator_probe_logs /\
    label_taus labels=19 /\
    finite_steps (run_nd (allocator_program 2) (managed_empty,(ctx,0))) labels residual /\
    residual ~ (model_nd 2 actor_of_slot (turn 1) last :
      ctreeW (CSLObs (nat * nat)) Bn (SSig * unit))).
Proof.
  split; [reflexivity|split; [reflexivity|split]].
  - intros i Hi; do 19 (destruct i as [|i];
      [eexists; eexists; eexists; split; vm_compute; reflexivity|]); lia.
  - assert (Hrun : exists last,
      run_turns (turn 1) (fun xs => xs) allocator_probe_script (initial_state 2 0)=
        Some (last,allocator_probe_logs)).
    { eexists; vm_compute; reflexivity. }
    destruct Hrun as [last Hrun].
    destruct (run_turns_realizes_source 2 ctx 0 allocator_probe_script last allocator_probe_logs Hrun)
      as (labels & residual & _ & Hlogs & Htaus & Hsteps & E).
    exists last, labels, residual; repeat split; assumption.
Qed.

Definition allocator_partial_state : AState :=
  {| aheap:=hsingle 4 6; aallocs:=hemp; acount:=0;
     owner_state:=ORead; remote0_state:=RPoll; remote1_state:=RPoll |}.

Theorem allocator_partial_fault_prefix :
  instr_flow_erased (client_round 1 false) ((hsingle 4 6,hemp),(List.nil,0)) ~
    log (CSLHeap (upd (hsingle 4 6) 4 0,hemp));;
      (Stuck : ctreeW (CSLObs (nat * nat)) Bn (SSig * option (option unit))) /\
  turn 1 Remote0 allocator_partial_state=None.
Proof.
  split.
  - unfold client_round; rewrite instr_flow_read with (v:=6) by apply hsingle_eq.
    cbn [Nat.eqb]; rewrite instr_flow_write by discriminate.
    rewrite !log_vis; apply sb_vis; intros [].
    apply instr_flow_write_missing; reflexivity.
  - reflexivity.
Qed.

Theorem initialization_fault_prefix ctx c :
  run_rr (CBind (new_queue [10;20]) (fun _ =>
    CBind (CRead 100) (fun _ => CRet tt))) (managed_empty,(ctx,c)) ~
      emit_list (List.map inl (new_queue_logs 1 [10;20] managed_empty))
        (Stuck : ctreeW rr_obs Bn (SSig * unit)).
Proof.
  unfold run_rr, run_rr_pool, csl_pool, denote.
  cbn [Vector.map].
  change ([denote_flow (CBind (new_queue [10;20]) (fun _ =>
    CBind (CRead 100) (fun _ => CRet tt)));; Ret tt]%vector : pool sE Bn 1) with
    (([Ret tt]%vector : pool sE Bn 1) @ Fin.F1 :=
      (denote_flow (CBind (new_queue [10;20]) (fun _ =>
        CBind (CRead 100) (fun _ => CRet tt))) >>= fun _ => Ret tt)).
  rewrite interp_rr_bind, interp_rr_new_queue_empty.
  apply emit_list_sbisim.
  rewrite interp_rr_bind; apply interp_rr_read_missing; reflexivity.
Qed.


Theorem allocation_no_space_silent ctx c :
  instr_flow_erased (CBind (CAlloc 1) (fun _ => CRet tt))
    (((fun _ => Some 0),hemp),(ctx,c)) ~
      (CTree.spin : ctreeW (CSLObs (nat * nat)) Bn (SSig * option unit)).
Proof.
  apply instr_flow_alloc_no_space; [lia|].
  intros j Hj H; specialize (H 0 ltac:(lia)); discriminate.
Qed.

CoFixpoint empty_log_thread : thread sE Bn :=
  Vis (inl1 Yield) (fun _ : unit => Guard empty_log_thread).

Lemma empty_log_thread_unfold :
  empty_log_thread ≅ Vis (inl1 Yield) (fun _ : unit => Guard empty_log_thread).
Proof. rewrite ctree_eta at 1; reflexivity. Qed.

Theorem empty_log_closed_turns :
  ClosedTurns sh [empty_log_thread]%vector (fun (_ : unit) (_ : SSig) => True).
Proof.
  intros [] sigma i _.
  assert (Hi : i=Fin.F1) by (dependent destruction i; [reflexivity|inversion i]).
  subst i; exists tt, sigma, []; split; [|exact I].
  cbn [Vector.nth]; exists (Guard empty_log_thread); split.
  - eapply segment_equ; [apply empty_log_thread_unfold|apply segment_yield|reflexivity].
  - apply guard_equ_left, guard_equ_equ; reflexivity.
Qed.

Theorem empty_log_pool_invariance_nd_rr s focus cursor w wr : not_done w -> not_done wr ->
  <( {interp_schedule_nd sh 1 [empty_log_thread]%vector focus s}, w |=L AG ⊤ )> /\
  <( {interp_schedule_rr sh 1 [empty_log_thread]%vector focus cursor s}, wr |=L AG ⊤ )>.
Proof.
  intros Hw Hwr; split.
  - eapply (ag_pool_nd_invariance sh [empty_log_thread]%vector
      (fun (_ : unit) (_ : SSig) => True) <( ⊤ )>) with (g:=tt).
    + exact empty_log_closed_turns.
    + intros o t v Hv H; apply ticll_top; exact Hv.
    + intros g sigma f v _ Hv; apply ticll_top; exact Hv.
    + exact I.
    + exact Hw.
  - eapply (ag_pool_rr_invariance sh [empty_log_thread]%vector
      (fun (_ : unit) (_ : SSig) => True) <( ⊤ )>) with (g:=tt).
    + exact empty_log_closed_turns.
    + intros o t v Hv H; apply ticll_top; exact Hv.
    + intros g sigma f m v _ Hv; apply ticll_top; exact Hv.
    + exact I.
    + exact Hwr.
Qed.

Module EventRecurrenceControls.
  Import VectorNotations.
  Local Open Scope list_scope.

  Definition repeat_emit_7 : ctreeW nat Bn unit :=
    emit_batches (fun _ : unit => [7]) (fun x => x) tt.
  Definition once_then_silent : ctreeW nat Bn unit :=
    log 7;; CTree.spinS.
  Definition emit_or_silent : ctreeW nat Bn unit :=
    BrS (branchn 2)
      (fun i => Vector.nth [repeat_emit_7; CTree.spinS]%vector i).
  Local Definition L : @label (writerE nat) -> Prop :=
    log_label (fun n : nat => n = 7).

  Theorem repeat_plain_payload_recurrent :
    recurrent_label L repeat_emit_7.
  Proof.
    assert (Eloop : repeat_emit_7 ~ Vis (Log 7) (fun _ : unit => repeat_emit_7)).
    { unfold repeat_emit_7 at 1.
      rewrite emit_batches_unfold_sbisim, emit_list_cons.
      cbn [emit_list List.fold_right]; reflexivity. }
    assert (Hrec : forall t : ctreeW nat Bn unit,
      t ~ repeat_emit_7 -> recurrent_label L t).
    { cofix CIH; intros t Et.
      assert (Evis : t ~ Vis (Log 7) (fun _ : unit => repeat_emit_7)).
      { transitivity repeat_emit_7; [exact Et | exact Eloop]. }
      constructor.
      - eapply eventually_label_sbisim.
        + symmetry; exact Evis.
        + constructor.
          * exists (obs (Log 7) tt), repeat_emit_7; apply trans_vis.
          * intros l u HT.
            apply trans_vis_inv in HT as ([] & _ & ->).
            left; unfold L, log_label; reflexivity.
      - intros l u HT.
        destruct (sbisim_trans_l _ _ _ _ Evis HT) as (u' & HT' & Eu).
        apply trans_vis_inv in HT' as ([] & Erest & _).
        apply CIH.
        transitivity u'; [exact Eu |].
        rewrite Erest; reflexivity. }
    apply Hrec; reflexivity.
  Qed.

  Local Lemma spinS_not_recurrent :
    ~ recurrent_label L (CTree.spinS : ctreeW nat Bn unit).
  Proof.
    intro H; inversion H as [t Hhit Hfuture]; subst.
    assert (Hcontra : forall t : ctreeW nat Bn unit,
      eventually_label L t -> t ≅ CTree.spinS -> False).
    { apply (eventually_label_ind L
        (fun t => t ≅ (CTree.spinS : ctreeW nat Bn unit) -> False)).
      intros t Hcan Hnext Et.
      assert (HT : trans τ t (CTree.spinS : ctreeW nat Bn unit)).
      { rewrite Et; rewrite unfold_spinS at 1; apply trans_step. }
      destruct (Hnext _ _ HT) as [Hit | [_ IH]].
      - exact Hit.
      - apply IH; reflexivity. }
    eapply Hcontra; [exact Hhit | reflexivity].
  Qed.

  Theorem retained_payload_not_recurrent :
    <( once_then_silent, Pure
      |=L AG (AF visW {fun n : nat => n = 7}) )> /\
    ~ recurrent_label L once_then_silent.
  Proof.
    split.
    - unfold once_then_silent.
      apply (proj2 (ag_log_iff 7
        (CTree.spinS : ctreeW nat Bn unit) Pure
        <( AF visW {fun n : nat => n = 7} )>)).
      split.
      + apply (af_log (b:=false)); [constructor |].
        cleft; apply ticl_vis; constructor; reflexivity.
      + change (agc (entails unit false <( AF visW {fun n : nat => n = 7} )>)
          (CTree.spinS : ctreeW nat Bn unit) (Obs (Log 7) tt)).
        coinduction R CIH; rewrite unfold_spinS; split.
        * cleft; apply ticl_vis; constructor; reflexivity.
        * split.
          -- apply can_step_step; constructor.
          -- intros t' w' HT; apply ktrans_step in HT as (Et & <- & _).
             rewrite Et; exact CIH.
    - intro H; inversion H as [t Hhit Hnext]; subst.
      apply spinS_not_recurrent.
      apply (Hnext (obs (Log 7) tt)
        (CTree.spinS : ctreeW nat Bn unit)).
      unfold once_then_silent, log; rewrite bind_vis; setoid_rewrite bind_ret_l.
      exact (trans_vis (Log 7) tt
        (fun _ : unit => (CTree.spinS : ctreeW nat Bn unit))).
  Qed.

  Theorem universal_recurrence_rejects_silent_branch :
    ~ recurrent_label L emit_or_silent.
  Proof.
    intro H; inversion H as [t Hhit Hnext]; subst.
    apply spinS_not_recurrent.
    apply (Hnext τ (CTree.spinS : ctreeW nat Bn unit)).
    unfold emit_or_silent.
    exact (trans_brS (branchn 2)
      (fun i => Vector.nth [repeat_emit_7; CTree.spinS]%vector i)
      (Fin.FS Fin.F1)).
  Qed.

  Theorem event_recurrence_rejects_return :
    ~ recurrent_label L (Ret tt : ctreeW nat Bn unit).
  Proof.
    intro H; inversion H as [t Hhit Hnext]; subst.
    pose proof (Hnext (val tt) Stuck (trans_ret tt)) as HS.
    inversion HS as [t' HS_hit HS_next]; subst.
    inversion HS_hit as [t'' Hcan Hcont]; subst.
    destruct Hcan as (l & u & HT).
    eapply Stuck_is_stuck; exact HT.
  Qed.
End EventRecurrenceControls.
