From Stdlib Require Import List Lia Arith.PeanoNat Fin Sorting.Permutation.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Interp.Refine.
From examples Require Import CSL.HeapQ CSL.Allocator.Layout.

Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope list_scope.

Inductive Actor := Owner | Remote0 | Remote1.
Inductive owner_pc := ORead | OCAS (old : nat) | ODrain | OOffer (client : bool).
Inductive remote_pc := RPoll | RRead (block : nat)
  | RLink (block old : nat) | RCAS (block old : nat).
Record AState := {
  aheap : Heap;
  acount : nat;
  owner_state : owner_pc;
  remote0_state : remote_pc;
  remote1_state : remote_pc
}.

(** One selected source segment, ending at its first yield.  The helpers
    below only assemble this example's result; missing checked cells fault. *)
Definition turn (base : nat) (who : Actor) (s : AState)
  : option (AState * option SObs) :=
  let finish (h : Heap) (op : owner_pc) (r0 r1 : remote_pc)
      (event : option (nat * nat)) :=
    Some ({| aheap := h;
             acount := match event with None => acount s | Some _ => S (acount s) end;
             owner_state := op; remote0_state := r0; remote1_state := r1 |},
          match event with None => None
          | Some (tag,block) => Some (SPop tag block (acount s)) end) in
  let own pc h event := finish h pc (remote0_state s) (remote1_state s) event in
  let remote (client : bool) :=
    let pc := if client then remote1_state s else remote0_state s in
    let done pc h event :=
      if client then finish h (owner_state s) (remote0_state s) pc event
      else finish h (owner_state s) pc (remote1_state s) event in
    match pc with
    | RPoll =>
        match aheap s (mailbox base client) with
        | None => None
        | Some block =>
            if Nat.eqb block 0 then done RPoll (aheap s) None
            else
              let h := upd (aheap s) (mailbox base client) 0 in
              match h (S block) with
              | None => None
              | Some _ => done (RRead block)
                  (upd h (S block) (if client then 2 else 1)) None
              end
        end
    | RRead block =>
        match aheap s (remote_head base) with
        | None => None
        | Some old => done (RLink block old) (aheap s) None
        end
    | RLink block old =>
        match aheap s block with
        | None => None
        | Some _ => done (RCAS block old) (upd (aheap s) block old) None
        end
    | RCAS block old =>
        match aheap s (remote_head base) with
        | None => None
        | Some current =>
            if Nat.eqb current old
            then done RPoll (upd (aheap s) (remote_head base) block)
              (Some (tag_retire,block))
            else done (RRead block) (aheap s) (Some (tag_retry,block))
        end
    end in
  match who with
  | Remote0 => remote false
  | Remote1 => remote true
  | Owner =>
      match owner_state s with
      | ORead =>
          match aheap s (remote_head base) with
          | None => None
          | Some old => own (OCAS old) (aheap s) None
          end
      | OCAS old =>
          match aheap s (remote_head base) with
          | None => None
          | Some current =>
              if Nat.eqb current old then
                let h := upd (aheap s) (remote_head base) 0 in
                match h (drain_head base) with
                | None => None
                | Some _ => own ODrain (upd h (drain_head base) old) None
                end
              else own ORead (aheap s) None
          end
      | ODrain =>
          match aheap s (drain_head base) with
          | None => None
          | Some block =>
              if Nat.eqb block 0 then own (OOffer false) (aheap s) None
              else
                match aheap s block, aheap s (local_head base) with
                | Some next, Some local =>
                    own ODrain
                      (upd (upd (upd (aheap s) block local)
                        (local_head base) block) (drain_head base) next)
                      (Some (tag_reclaim,block))
                | _, _ => None
                end
          end
      | OOffer client =>
          let next := if client then ORead else OOffer true in
          match aheap s (mailbox base client) with
          | None => None
          | Some offered =>
              if Nat.eqb offered 0 then
                match aheap s (local_head base) with
                | None => None
                | Some block =>
                    if Nat.eqb block 0 then own next (aheap s) None
                    else
                      match aheap s block with
                      | None => None
                      | Some successor =>
                          own next
                            (upd (upd (aheap s) (local_head base) successor)
                              (mailbox base client) block)
                            (Some (tag_alloc,block))
                      end
                end
              else own next (aheap s) None
          end
      end
  end.

Definition initial_state (capacity c : nat) : AState :=
  {| aheap := page_heap 1 capacity hemp; acount := c;
     owner_state := ORead; remote0_state := RPoll; remote1_state := RPoll |}.

Fixpoint free_chain (h : Heap) (nodes : list nat) : Prop :=
  match nodes with
  | [] => True
  | block :: rest => h block = Some (hd 0 rest) /\ free_chain h rest
  end.

Definition held (pc : remote_pc) : list nat :=
  match pc with RPoll => [] | RRead block | RLink block _ | RCAS block _ => [block] end.
Definition mailbox_nodes (block : nat) : list nat :=
  if Nat.eqb block 0 then [] else [block].
Definition cached_remote (base capacity : nat) (h : Heap) (pc : remote_pc) : Prop :=
  match pc with
  | RPoll | RRead _ => True
  | RLink block old =>
      (old = 0 \/ In old (page_blocks base capacity)) /\ old <> block
  | RCAS block old =>
      (old = 0 \/ In old (page_blocks base capacity)) /\ old <> block /\
      h block = Some old
  end.
Definition backing (base capacity : nat) (h : Heap) : Prop :=
  forall x, h x <> None <-> base <= x /\ x < base + page_size capacity.

Definition allocator_inv (base capacity : nat) (s : AState) : Prop :=
  0 < base /\ backing base capacity (aheap s) /\
  exists (L R D : list nat) (m0 m1 : nat),
    aheap s (remote_head base) = Some (hd 0 R) /\
    aheap s (local_head base) = Some (hd 0 L) /\
    aheap s (drain_head base) = Some (hd 0 D) /\
    free_chain (aheap s) L /\ free_chain (aheap s) R /\ free_chain (aheap s) D /\
    aheap s (mailbox base false) = Some m0 /\
    aheap s (mailbox base true) = Some m1 /\
    Permutation (L ++ R ++ D ++ mailbox_nodes m0 ++ mailbox_nodes m1 ++
      held (remote0_state s) ++ held (remote1_state s)) (page_blocks base capacity) /\
    (match owner_state s with ODrain => True | _ => D = [] end) /\
    (match owner_state s with
     | OCAS old => old = 0 \/ In old (page_blocks base capacity)
     | _ => True end) /\
    cached_remote base capacity (aheap s) (remote0_state s) /\
    cached_remote base capacity (aheap s) (remote1_state s).

Definition state_equiv (s t : AState) : Prop :=
  heq (aheap s) (aheap t) /\ acount s = acount t /\
  owner_state s = owner_state t /\ remote0_state s = remote0_state t /\
  remote1_state s = remote1_state t.

Fixpoint run_turns (base : nat) (script : list Actor) (s : AState)
  : option (AState * list SObs) :=
  match script with
  | [] => Some (s,[])
  | who :: rest =>
      match turn base who s with
      | None => None
      | Some (next,event) =>
          match run_turns base rest next with
          | None => None
          | Some (last,logs) =>
              Some (last,match event with None => logs | Some o => o :: logs end)
          end
      end
  end.

Lemma init_chain_links h nodes :
  (forall prefix block rest, nodes = prefix ++ block :: rest ->
    h block = Some (hd 0 rest)) -> free_chain h nodes.
Proof.
  induction nodes as [|block rest IH]; intro Links; [exact I|].
  split.
  - exact (Links [] block rest eq_refl).
  - apply IH; intros prefix next tail E.
    apply (Links (block :: prefix) next tail); cbn; now rewrite E.
Qed.

Lemma initial_state_inv capacity c :
  allocator_inv 1 capacity (initial_state capacity c).
Proof.
  unfold allocator_inv, initial_state; cbn [aheap owner_state remote0_state remote1_state].
  split; [lia|]; split.
  - intro x; apply page_heap_closed_dom.
  - exists (page_blocks 1 capacity), [], [], 0, 0.
    split; [apply page_heap_remote|].
    split; [apply page_heap_local_blocks|].
    split; [apply page_heap_drain|].
    split.
    + apply init_chain_links; intros prefix block rest E.
      eapply page_heap_link; exact E.
    + split; [exact I|]; split; [exact I|].
      split; [apply page_heap_mailbox|].
      split; [apply page_heap_mailbox|].
      split.
      * cbn [mailbox_nodes held app]; rewrite app_nil_r; reflexivity.
      * repeat split.
Qed.

Lemma turn_counter base who s t event :
  turn base who s = Some (t,event) ->
  match event with
  | None => acount t = acount s
  | Some o => acount t = S (acount s) /\ sidx o = acount s
  end.
Proof.
  destruct s as [h c op r0 r1]; destruct who;
    cbn [turn aheap acount owner_state remote0_state remote1_state];
    [destruct op|destruct r0|destruct r1]; cbn; intro T;
    repeat match type of T with
    | context [match ?v with Some _ => _ | None => _ end] => destruct v eqn:?
    | context [if ?v then _ else _] => destruct v eqn:?
    end;
    try discriminate; inversion T; subst; cbn; auto.
Qed.

From Stdlib Require Import List Lia Arith.PeanoNat Fin
  Classes.RelationClasses Program.Equality.
From Coinduction Require Import coinduction rel tactics.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Interp.Refine.

Import ICtree ICTreeNotations ListNotations.
Local Open Scope ictree_scope.
Local Open Scope list_scope.
Local Typeclasses Transparent equ.

Lemma state_equiv_refl s : state_equiv s s.
Proof.
  unfold state_equiv; split; [apply heq_refl | repeat split; reflexivity].
Qed.

Lemma state_equiv_sym s t : state_equiv s t -> state_equiv t s.
Proof.
  intros [Hh [Hc [Ho [H0 H1]]]].
  unfold state_equiv; split; [now apply heq_sym |].
  repeat split; symmetry; assumption.
Qed.

Lemma state_equiv_trans s t u :
  state_equiv s t -> state_equiv t u -> state_equiv s u.
Proof.
  intros [Hh [Hc [Ho [H0 H1]]]] [Kh [Kc [Ko [K0 K1]]]].
  unfold state_equiv; split; [eapply heq_trans; eauto |].
  repeat split; congruence.
Qed.

#[global] Instance state_equiv_equivalence : Equivalence state_equiv.
Proof.
  split.
  - exact state_equiv_refl.
  - exact state_equiv_sym.
  - exact state_equiv_trans.
Qed.

Local Lemma trees_upd_heq h k a v :
  heq h k -> heq (upd h a v) (upd k a v).
Proof.
  intros H x; unfold upd; destruct (Nat.eqb x a); [reflexivity | apply H].
Qed.

Local Lemma trees_upd_lookup h a v x :
  upd h a v x = if Nat.eqb x a then Some v else h x.
Proof. reflexivity. Qed.

(** Both faults and successful turns are preserved.  In particular this
    statement does not assume the ownership invariant or heap finiteness. *)
Lemma turn_respects_heq base who s t :
  state_equiv s t ->
  match turn base who s, turn base who t with
  | None, None => True
  | Some (s',event), Some (t',event') =>
      state_equiv s' t' /\ event = event'
  | _, _ => False
  end.
Proof.
  destruct s as [h c op r0 r1], t as [k d oq q0 q1].
  intros [Hh [Hc [Ho [H0 H1]]]].
  cbn in Hh, Hc, Ho, H0, H1.
  subst d oq q0 q1.
  destruct who; [destruct op | destruct r0 | destruct r1];
    cbn [turn].
  all: repeat first
    [ progress (rewrite trees_upd_lookup)
    | progress (rewrite <- Hh)
    | progress (cbn [aheap acount owner_state remote0_state remote1_state])
    | match goal with
      | Hheap : heq ?left ?right |- context [?left ?x] =>
          let Hr := fresh "Hread" in destruct (left x) eqn:Hr
      | |- context [if ?b then _ else _] =>
          let Hb := fresh "Htest" in destruct b eqn:Hb
      end ].
  all: try exact I.
  all: split; [|reflexivity].
  all: unfold state_equiv;
    cbn [aheap acount owner_state remote0_state remote1_state].
  all: split;
    [ repeat apply trees_upd_heq; exact Hh
    | repeat split; reflexivity ].
Qed.

Corollary turn_respects_heq_some base who s t s' event :
  state_equiv s t -> turn base who s = Some (s',event) ->
  exists t', turn base who t = Some (t',event) /\ state_equiv s' t'.
Proof.
  intros Hst Hstep.
  pose proof (turn_respects_heq base who s t Hst) as H.
  rewrite Hstep in H.
  destruct (turn base who t) as [[t' event']|] eqn:Ht;
    cbn in H; [|contradiction].
  destruct H as [Hnext Hevent]; subst event'.
  exists t'; split; [assumption || reflexivity | exact Hnext].
Qed.

Corollary turn_respects_heq_none base who s t :
  state_equiv s t -> (turn base who s = None <-> turn base who t = None).
Proof.
  intro Hst; pose proof (turn_respects_heq base who s t Hst) as H.
  destruct (turn base who s) as [[s' event]|];
    destruct (turn base who t) as [[t' event']|];
    cbn in H; try contradiction; split; intro Hnone;
    try discriminate; reflexivity.
Qed.

(** Physical source-pool order is [client1; client0; owner]. *)
Definition actor_of_slot (i : Fin.t 3) : Actor :=
  match i with
  | Fin.F1 => Remote1
  | Fin.FS Fin.F1 => Remote0
  | Fin.FS (Fin.FS _) => Owner
  end.

Definition slot_of_actor (who : Actor) : Fin.t 3 :=
  match who with
  | Owner => Fin.FS (Fin.FS Fin.F1)
  | Remote0 => Fin.FS Fin.F1
  | Remote1 => Fin.F1
  end.

Lemma actor_of_slot_of_actor who : actor_of_slot (slot_of_actor who) = who.
Proof. destruct who; reflexivity. Qed.

Lemma slot_of_actor_of_slot i : slot_of_actor (actor_of_slot i) = i.
Proof.
  refine (Fin.caseS' i
    (fun j => slot_of_actor (actor_of_slot j) = j) _ _).
  - reflexivity.
  - intro j; refine (Fin.caseS' j
      (fun k => slot_of_actor (actor_of_slot (Fin.FS k)) = Fin.FS k) _ _).
    + reflexivity.
    + intro k; refine (Fin.caseS' k
        (fun z => slot_of_actor (actor_of_slot (Fin.FS (Fin.FS z))) =
          Fin.FS (Fin.FS z)) _ _).
      * reflexivity.
      * intro impossible; inversion impossible.
Qed.

(** Every nondeterministic turn begins with exactly one real branch node.
    The post-effect guards are invisible, not additional scheduling choices. *)
CoFixpoint model_nd (base : nat) (s : AState)
  : ictreeW SObs (unit * SSig) :=
  Br 2 (fun i =>
    match turn base (actor_of_slot i) s with
    | None => stuck
    | Some (next,None) => Guard (model_nd base next)
    | Some (next,Some event) =>
        Vis (Log event) (fun _ => Guard (model_nd base next))
    end).

CoFixpoint model_rr (base : nat) (s : AState) (cursor : nat)
  : ictreeW SObs (unit * SSig) :=
  match turn base (actor_of_slot (rr_pick 2 cursor)) s with
  | None => stuck
  | Some (next,None) => Guard (model_rr base next (S cursor))
  | Some (next,Some event) =>
      Vis (Log event) (fun _ => Guard (model_rr base next (S cursor)))
  end.

Lemma unfold_model_nd base s :
  model_nd base s ≅
  Br 2 (fun i =>
    match turn base (actor_of_slot i) s with
    | None => stuck
    | Some (next,None) => Guard (model_nd base next)
    | Some (next,Some event) =>
        Vis (Log event) (fun _ => Guard (model_nd base next))
    end).
Proof. step; now cbn. Qed.

Lemma unfold_model_rr base s cursor :
  model_rr base s cursor ≅
  match turn base (actor_of_slot (rr_pick 2 cursor)) s with
  | None => stuck
  | Some (next,None) => Guard (model_rr base next (S cursor))
  | Some (next,Some event) =>
      Vis (Log event) (fun _ => Guard (model_rr base next (S cursor)))
  end.
Proof. step; now cbn. Qed.

Lemma model_nd_respects_heq_equ base : forall s t,
  state_equiv s t -> model_nd base s ≅ model_nd base t.
Proof.
  coinduction R IH; intros s t Hst.
  rewrite !unfold_model_nd.
  constructor; intro i.
  pose proof (turn_respects_heq base (actor_of_slot i) s t Hst) as Hturn.
  destruct (turn base (actor_of_slot i) s) as [[s' event]|];
    destruct (turn base (actor_of_slot i) t) as [[t' event']|];
    cbn in Hturn; try contradiction.
  - destruct Hturn as [Hnext Hevent]; subst event'.
    destruct event as [o|].
    + step; cbn; constructor; intros [].
      step; cbn; constructor; apply IH; exact Hnext.
    + step; cbn; constructor; apply IH; exact Hnext.
  - reflexivity.
Qed.

Lemma model_nd_respects_heq base s t :
  state_equiv s t -> model_nd base s ~ model_nd base t.
Proof.
  intro Hst.
  eapply equ_clos_sbisim_goal;
    [apply model_nd_respects_heq_equ; exact Hst | reflexivity | reflexivity].
Qed.

(** The proof compares finite indices through their numeric values, never
    through equality of proof fields in [Fin.of_nat_lt]. *)
Local Lemma trees_rr_pick_three_congr cursor cursor' :
  cursor mod 3 = cursor' mod 3 -> rr_pick 2 cursor = rr_pick 2 cursor'.
Proof.
  intro Hmod; apply Fin.to_nat_inj; unfold rr_pick.
  rewrite !Fin.to_nat_of_nat; exact Hmod.
Qed.

Local Lemma trees_succ_mod_three cursor cursor' :
  cursor mod 3 = cursor' mod 3 -> S cursor mod 3 = S cursor' mod 3.
Proof.
  intro Hmod.
  replace (S cursor) with (cursor + 1)%nat by lia.
  replace (S cursor') with (cursor' + 1)%nat by lia.
  rewrite (Nat.Div0.add_mod cursor 1 3), (Nat.Div0.add_mod cursor' 1 3).
  now rewrite Hmod.
Qed.

Lemma model_rr_respects_heq_equ base : forall s t cursor cursor',
  state_equiv s t -> cursor mod 3 = cursor' mod 3 ->
  model_rr base s cursor ≅ model_rr base t cursor'.
Proof.
  coinduction R IH; intros s t cursor cursor' Hst Hmod.
  rewrite !unfold_model_rr.
  rewrite <- (trees_rr_pick_three_congr cursor cursor' Hmod).
  pose proof (turn_respects_heq base
    (actor_of_slot (rr_pick 2 cursor)) s t Hst) as Hturn.
  destruct (turn base (actor_of_slot (rr_pick 2 cursor)) s)
      as [[s' event]|];
    destruct (turn base (actor_of_slot (rr_pick 2 cursor)) t)
      as [[t' event']|];
    cbn in Hturn; try contradiction.
  - destruct Hturn as [Hnext Hevent]; subst event'.
    destruct event as [o|]; cbn.
    + constructor; intros [].
      step; cbn; constructor; apply IH;
        [exact Hnext | now apply trees_succ_mod_three].
    + constructor; apply IH;
        [exact Hnext | now apply trees_succ_mod_three].
  - reflexivity.
Qed.

Lemma model_rr_respects_heq base s t cursor cursor' :
  state_equiv s t -> cursor mod 3 = cursor' mod 3 ->
  model_rr base s cursor ~ model_rr base t cursor'.
Proof.
  intros Hst Hmod.
  eapply equ_clos_sbisim_goal;
    [exact (model_rr_respects_heq_equ base s t cursor cursor' Hst Hmod)
    | reflexivity | reflexivity].
Qed.

(** The finite fold uses the actual result of each turn; faults propagate. *)
Lemma run_turns_append base left right s :
  run_turns base (left ++ right) s =
  match run_turns base left s with
  | None => None
  | Some (middle,first) =>
      match run_turns base right middle with
      | None => None
      | Some (last,second) => Some (last,first ++ second)
      end
  end.
Proof.
  revert s; induction left as [|who left IH]; intro s.
  - cbn [run_turns app].
    destruct (run_turns base right s) as [[last logs]|]; reflexivity.
  - cbn [run_turns app].
    destruct (turn base who s) as [[next event]|]; [|reflexivity].
    rewrite IH.
    destruct (run_turns base left next) as [[middle first]|]; [|reflexivity].
    destruct (run_turns base right middle) as [[last second]|]; [|reflexivity].
    destruct event; reflexivity.
Qed.

Corollary run_turns_compose base left right s middle last first second :
  run_turns base left s = Some (middle,first) ->
  run_turns base right middle = Some (last,second) ->
  run_turns base (left ++ right) s = Some (last,first ++ second).
Proof.
  intros Hleft Hright; rewrite run_turns_append, Hleft, Hright; reflexivity.
Qed.

Lemma run_turns_append_inv base left right s last logs :
  run_turns base (left ++ right) s = Some (last,logs) ->
  exists middle first second,
    run_turns base left s = Some (middle,first) /\
    run_turns base right middle = Some (last,second) /\
    logs = first ++ second.
Proof.
  rewrite run_turns_append; intro Hrun.
  destruct (run_turns base left s) as [[middle first]|] eqn:Hleft;
    [|discriminate].
  destruct (run_turns base right middle) as [[last' second]|] eqn:Hright;
    [|discriminate].
  inversion Hrun; subst.
  exists middle, first, second; repeat split; assumption || reflexivity.
Qed.

Lemma run_turns_counter base script s last logs :
  run_turns base script s = Some (last,logs) ->
  acount last = (acount s + length logs)%nat.
Proof.
  revert s last logs; induction script as [|who rest IH];
    intros s last logs Hrun.
  - cbn [run_turns] in Hrun; inversion Hrun; subst; cbn; lia.
  - cbn [run_turns] in Hrun.
    destruct (turn base who s) as [[next event]|] eqn:Hstep;
      [|discriminate].
    destruct (run_turns base rest next) as [[last' suffix]|] eqn:Hrest;
      [|discriminate].
    pose proof (IH next last' suffix Hrest) as Hsuffix.
    pose proof (turn_counter base who s next event Hstep) as Hcounter.
    destruct event as [o|]; cbn in Hrun, Hcounter.
    + destruct Hcounter as [Hcount Hindex].
      inversion Hrun; subst; cbn; lia.
    + inversion Hrun; subst; cbn; lia.
Qed.

Lemma run_turns_respects_heq base script s t :
  state_equiv s t ->
  match run_turns base script s, run_turns base script t with
  | None, None => True
  | Some (s',logs), Some (t',logs') =>
      state_equiv s' t' /\ logs = logs'
  | _, _ => False
  end.
Proof.
  revert s t; induction script as [|who rest IH]; intros s t Hst.
  - cbn [run_turns]; split; [exact Hst | reflexivity].
  - cbn [run_turns].
    pose proof (turn_respects_heq base who s t Hst) as Hturn.
    destruct (turn base who s) as [[next event]|];
      destruct (turn base who t) as [[next' event']|];
      cbn in Hturn; try contradiction.
    + destruct Hturn as [Hnext Hevent]; subst event'.
      specialize (IH next next' Hnext).
      destruct (run_turns base rest next) as [[last logs]|];
        destruct (run_turns base rest next') as [[last' logs']|];
        cbn in IH; try contradiction.
      * destruct IH as [Hlast Hlogs]; subst logs'.
        split; [exact Hlast | reflexivity].
      * exact I.
    + exact I.
Qed.

Corollary run_turns_respects_heq_some base script s t last logs :
  state_equiv s t -> run_turns base script s = Some (last,logs) ->
  exists last', run_turns base script t = Some (last',logs) /\
    state_equiv last last'.
Proof.
  intros Hst Hrun.
  pose proof (run_turns_respects_heq base script s t Hst) as H.
  rewrite Hrun in H.
  destruct (run_turns base script t) as [[last' logs']|] eqn:Ht;
    cbn in H; [|contradiction].
  destruct H as [Hlast Hlogs]; subst logs'.
  exists last'; split; [assumption || reflexivity | exact Hlast].
Qed.

Corollary run_turns_respects_heq_none base script s t :
  state_equiv s t ->
  (run_turns base script s = None <-> run_turns base script t = None).
Proof.
  intro Hst; pose proof (run_turns_respects_heq base script s t Hst) as H.
  destruct (run_turns base script s) as [[last logs]|];
    destruct (run_turns base script t) as [[last' logs']|];
    cbn in H; try contradiction; split; intro Hnone;
    try discriminate; reflexivity.
Qed.

From Stdlib Require Import List Lia Arith.PeanoNat Sorting.Permutation.
From TICL Require Import Lang.CSL.
From examples Require Import CSL.HeapQ CSL.Allocator.Layout.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Lemma ai_free_chain_frame h h' xs :
  free_chain h xs ->
  (forall b, In b xs -> h' b = h b) ->
  free_chain h' xs.
Proof.
  revert h h'; induction xs as [|b xs IH]; intros h h' Hchain Hframe.
  - exact I.
  - cbn [free_chain] in *; destruct Hchain as [Hb Hxs]; split.
    + rewrite Hframe; [exact Hb | now left].
    + eapply IH; [exact Hxs | intros x Hx; apply Hframe; now right].
Qed.

Lemma ai_free_chain_upd h xs a v :
  free_chain h xs ->
  (forall b, In b xs -> b <> a) ->
  free_chain (upd h a v) xs.
Proof.
  intros Hchain Haway; eapply ai_free_chain_frame; [exact Hchain |].
  intros b Hb; apply upd_neq, Haway, Hb.
Qed.

Lemma ai_cached_remote_frame base capacity h h' pc :
  cached_remote base capacity h pc ->
  (forall b, In b (held pc) -> h' b = h b) ->
  cached_remote base capacity h' pc.
Proof.
  destruct pc; cbn [cached_remote held]; intros H Hframe; try exact H.
  destruct H as [Hbound [Hneq Hlink]]; repeat split; try assumption.
  rewrite Hframe; [exact Hlink | now left].
Qed.

Lemma ai_partition_member base capacity xs x :
  Permutation xs (page_blocks base capacity) ->
  In x xs -> In x (page_blocks base capacity).
Proof. intros Hp Hx; eapply Permutation_in; eauto. Qed.

Lemma ai_partition_nodup base capacity xs :
  Permutation xs (page_blocks base capacity) -> NoDup xs.
Proof.
  intro Hp; eapply Permutation_NoDup; [apply Permutation_sym, Hp |].
  apply page_blocks_nodup.
Qed.

Lemma ai_partition_count base capacity xs :
  Permutation xs (page_blocks base capacity) ->
  forall x, count_occ Nat.eq_dec xs x <= 1.
Proof.
  intro Hp; apply (proj1 (NoDup_count_occ Nat.eq_dec xs)).
  now apply (ai_partition_nodup base capacity).
Qed.

Lemma ai_partition_disjoint base capacity xs ys zs :
  Permutation (xs ++ ys ++ zs) (page_blocks base capacity) ->
  forall b, In b xs -> ~ In b ys.
Proof.
  intros Hp b Hx Hy.
  pose proof (ai_partition_count base capacity _ Hp b) as Hcount.
  repeat rewrite count_occ_app in Hcount.
  apply (proj1 (count_occ_In Nat.eq_dec xs b)) in Hx.
  apply (proj1 (count_occ_In Nat.eq_dec ys b)) in Hy.
  lia.
Qed.

Lemma ai_head_bound base capacity xs :
  (forall b, In b xs -> In b (page_blocks base capacity)) ->
  hd 0 xs = 0 \/ In (hd 0 xs) (page_blocks base capacity).
Proof.
  destruct xs as [|b xs]; cbn; intro H; [now left | right; apply H; now left].
Qed.

Lemma ai_head_distinct xs b :
  ~ In b xs -> 0 <> b -> hd 0 xs <> b.
Proof.
  destruct xs as [|a xs]; cbn; intros Hnot Hzero; [exact Hzero |].
  intro E; apply Hnot; now left.
Qed.

Lemma ai_backing_present base capacity h x :
  backing base capacity h ->
  base <= x /\ x < base + page_size capacity ->
  exists v, h x = Some v.
Proof.
  intros Hback Hrange.
  pose proof (proj2 (Hback x) Hrange) as Hpresent.
  destruct (h x) as [v|]; [now exists v | contradiction].
Qed.

Lemma ai_backing_upd base capacity h a v :
  backing base capacity h ->
  base <= a /\ a < base + page_size capacity ->
  backing base capacity (upd h a v).
Proof.
  intros Hback Ha x.
  rewrite upd_dom; [apply Hback | now apply (proj2 (Hback a))].
Qed.

Lemma allocator_inv_backing base capacity s :
  allocator_inv base capacity s -> backing base capacity (aheap s).
Proof. intros [_ [H _]]; exact H. Qed.

Lemma allocator_inv_null base capacity s :
  allocator_inv base capacity s -> aheap s 0 = None.
Proof.
  intros [Hbase [Hback _]].
  destruct (aheap s 0) as [v|] eqn:E; [|reflexivity].
  assert (Hpresent : aheap s 0 <> None) by (rewrite E; discriminate).
  apply Hback in Hpresent; lia.
Qed.

Lemma allocator_inv_outside base capacity s x :
  allocator_inv base capacity s ->
  (x < base \/ base + page_size capacity <= x) -> aheap s x = None.
Proof.
  intros [_ [Hback _]] Hout.
  destruct (aheap s x) as [v|] eqn:E; [|reflexivity].
  assert (Hpresent : aheap s x <> None) by (rewrite E; discriminate).
  apply Hback in Hpresent; lia.
Qed.

Lemma allocator_inv_held_member base capacity s (client : bool) b :
  allocator_inv base capacity s ->
  In b (held (if client then remote1_state s else remote0_state s)) ->
  In b (page_blocks base capacity).
Proof.
  intros (_ & _ & L & R & D & m0 & m1 & Hr & Hl & Hd & CL & CR & CD &
    Hm0 & Hm1 & Hp & Hop & Ho & Hc0 & Hc1) Hin.
  eapply ai_partition_member; [exact Hp |].
  repeat rewrite in_app_iff; destruct client; tauto.
Qed.

(* These small tactics only discharge finite ownership arithmetic.  In
   particular, a cached head is never used as a freshness witness. *)
Ltac ai_member :=
  match goal with
  | Hp : Permutation ?xs (page_blocks ?base ?capacity)
    |- In ?x (page_blocks _ _) =>
      apply (ai_partition_member base capacity xs x Hp);
      repeat rewrite in_app_iff; cbn [held mailbox_nodes Nat.eqb In]; intuition congruence
  end.

Ltac ai_block_bounds x :=
  match goal with
  | Hp : Permutation _ (page_blocks ?base ?capacity) |- _ =>
      let Hx := fresh "Hblock" in
      assert (Hx : In x (page_blocks base capacity)) by ai_member;
      apply page_blocks_bounds in Hx
  end.

Ltac ai_interval :=
  first
    [ solve [unfold remote_head, local_head, drain_head, mailbox, page_size; lia]
    | match goal with
      | |- _ <= S ?b /\ _ =>
          solve [ai_block_bounds b; unfold page_size in *; lia]
      | |- _ <= ?b /\ _ =>
          solve [ai_block_bounds b; unfold page_size in *; lia]
      end ].

Ltac ai_count_contradiction x :=
  match goal with
  | Hp : Permutation ?xs (page_blocks ?base ?capacity) |- _ =>
      let Hcount := fresh "Hcount" in
      pose proof (ai_partition_count base capacity xs Hp x) as Hcount;
      repeat rewrite count_occ_app in Hcount;
      try unfold mailbox_nodes in Hcount;
      repeat match goal with
      | E : Nat.eqb ?a ?b = ?v |- _ => progress rewrite E in Hcount
      end;
      cbn [held count_occ Nat.eqb] in Hcount;
      repeat match type of Hcount with
      | context [Nat.eq_dec ?a ?b] =>
          destruct (Nat.eq_dec a b); try congruence
      end;
      repeat match goal with
      | Hin : In x ?ys |- _ =>
          apply (proj1 (count_occ_In Nat.eq_dec ys x)) in Hin
      end;
      lia
  end.

Ltac ai_distinct :=
  first
    [ solve [unfold remote_head, local_head, drain_head, mailbox; lia]
    | match goal with
      | |- ?a <> S ?b =>
          solve [eapply page_blocks_link_payload_disjoint; ai_member]
      | |- S ?b <> ?a =>
          solve [let E := fresh "Ealias" in intro E; symmetry in E;
            let H := fresh "Hdisjoint" in
            assert (H : a <> S b) by
              (eapply page_blocks_link_payload_disjoint; ai_member);
            contradiction]
      end
    | match goal with
      | |- ?a <> ?b =>
          first
            [ solve [ai_block_bounds a;
                unfold remote_head, local_head, drain_head, mailbox in *; lia]
            | solve [ai_block_bounds b;
                unfold remote_head, local_head, drain_head, mailbox in *; lia]
            | solve [match a with S ?x => ai_block_bounds x end;
                unfold remote_head, local_head, drain_head, mailbox in *; lia]
            | solve [match b with S ?x => ai_block_bounds x end;
                unfold remote_head, local_head, drain_head, mailbox in *; lia]
            | let E := fresh "Ealias" in
              intro E; rewrite E in *; ai_count_contradiction b ]
      end ].

Ltac ai_heap :=
  repeat first [rewrite upd_eq | rewrite upd_neq by ai_distinct];
  first [assumption | reflexivity].

Ltac ai_chain :=
  first [assumption | exact I |
    eapply ai_free_chain_upd; [ai_chain | intros; ai_distinct]].

Ltac ai_backing :=
  first [assumption |
    eapply ai_backing_upd; [ai_backing | ai_interval]].

Ltac ai_permutation :=
  match goal with
  | Hp : Permutation ?old ?page |- Permutation ?new ?page =>
      eapply Permutation_trans; [|exact Hp];
      apply (proj2 (Permutation_count_occ Nat.eq_dec new old));
      let x := fresh "x" in intro x;
      repeat rewrite count_occ_app;
      try unfold mailbox_nodes;
      repeat match goal with
      | E : Nat.eqb ?a ?b = ?v |- _ => progress rewrite E
      end;
      cbn [held count_occ Nat.eqb];
      repeat match goal with
      | |- context [Nat.eq_dec ?a ?b] => destruct (Nat.eq_dec a b)
      end; lia
  end.

Ltac ai_cached h :=
  eapply ai_cached_remote_frame with (h := h);
  [assumption | intros; ai_heap].

Ltac ai_obligation h :=
  first
    [ assumption | reflexivity | exact I
    | solve [ai_backing]
    | solve [ai_heap]
    | solve [ai_chain]
    | solve [ai_cached h]
    | solve [ai_permutation]
    | solve [ai_member]
    | solve [apply ai_head_bound; intros; ai_member]
    | match goal with
      | |- hd 0 ?xs <> ?b =>
          solve [apply ai_head_distinct;
            [intro; ai_count_contradiction b | ai_distinct]]
      end
    | solve [ai_distinct] ].

Local Ltac ai_reduce_turn :=
  cbn [turn aheap acount owner_state remote0_state remote1_state].

Ltac ai_finish h L R D m0 m1 :=
  cbn [aheap acount owner_state remote0_state remote1_state];
  try rewrite Nat.eqb_refl;
  repeat match goal with
  | E : Nat.eqb _ _ = _ |- _ => progress rewrite E
  end;
  do 2 eexists; split; [reflexivity |];
  unfold allocator_inv; cbn [aheap acount owner_state remote0_state remote1_state];
  split; [assumption |]; split; [ai_backing |];
  exists L, R, D, m0, m1;
  cbn [hd held];
  repeat split; ai_obligation h.

Lemma ai_turn_complete base capacity who s :
  allocator_inv base capacity s ->
  exists t event, turn base who s = Some (t,event) /\
    allocator_inv base capacity t.
Proof.
  destruct s as [h count op p0 p1].
  cbn [allocator_inv aheap acount owner_state remote0_state remote1_state].
  intros (Hbase & Hback & L & R & D & m0 & m1 & Hr & Hl & Hd & CL & CR & CD &
    Hm0 & Hm1 & Hp & Hop & Ho & Hc0 & Hc1).
  cbn [aheap acount owner_state remote0_state remote1_state] in *.
  destruct who.
  - destruct op as [|old| |client].
    + cbn in Hop; subst D.
      ai_reduce_turn; rewrite Hr.
      ai_finish h L R (@nil nat) m0 m1.
    + cbn in Hop; subst D.
      ai_reduce_turn; rewrite Hr.
      destruct (Nat.eqb (hd 0 R) old) eqn:Ecas.
      * apply Nat.eqb_eq in Ecas; subst old.
        rewrite upd_neq by ai_distinct; rewrite Hd.
        ai_finish h L (@nil nat) R m0 m1.
      * ai_finish h L R (@nil nat) m0 m1.
    + destruct D as [|b D].
      * ai_reduce_turn; rewrite Hd; cbn [hd Nat.eqb].
        ai_finish h L R (@nil nat) m0 m1.
      * cbn [free_chain] in CD; destruct CD as [Hnext CD].
        assert (Eb : Nat.eqb b 0 = false) by
          (apply Nat.eqb_neq; ai_distinct).
        ai_reduce_turn; rewrite Hd; cbn [hd]; rewrite Eb, Hnext, Hl.
        ai_finish h (b :: L) R D m0 m1.
    + cbn in Hop; subst D; destruct client.
      * destruct m1 as [|m1].
        -- destruct L as [|b L ].
           ++ ai_reduce_turn; rewrite Hm1; cbn [Nat.eqb]; rewrite Hl;
                cbn [hd Nat.eqb].
              ai_finish h (@nil nat) R (@nil nat) m0 0.
           ++ cbn [free_chain] in CL; destruct CL as [Hnext CL].
              assert (Eb : Nat.eqb b 0 = false) by
                (apply Nat.eqb_neq; ai_distinct).
              ai_reduce_turn; rewrite Hm1; cbn [Nat.eqb]; rewrite Hl;
                cbn [hd]; rewrite Eb, Hnext.
              ai_finish h L R (@nil nat) m0 b.
        -- ai_reduce_turn; rewrite Hm1; cbn [Nat.eqb].
           ai_finish h L R (@nil nat) m0 (S m1).
      * destruct m0 as [|m0].
        -- destruct L as [|b L ].
           ++ ai_reduce_turn; rewrite Hm0; cbn [Nat.eqb]; rewrite Hl;
                cbn [hd Nat.eqb].
              ai_finish h (@nil nat) R (@nil nat) 0 m1.
           ++ cbn [free_chain] in CL; destruct CL as [Hnext CL].
              assert (Eb : Nat.eqb b 0 = false) by
                (apply Nat.eqb_neq; ai_distinct).
              ai_reduce_turn; rewrite Hm0; cbn [Nat.eqb]; rewrite Hl;
                cbn [hd]; rewrite Eb, Hnext.
              ai_finish h L R (@nil nat) b m1.
        -- ai_reduce_turn; rewrite Hm0; cbn [Nat.eqb].
           ai_finish h L R (@nil nat) (S m0) m1.
  - destruct p0 as [|b|b old|b old].
    + destruct m0 as [|m0].
      * ai_reduce_turn; rewrite Hm0; cbn [Nat.eqb].
        ai_finish h L R D 0 m1.
      * assert (Hcell : exists v, h (S (S m0)) = Some v).
        { eapply ai_backing_present; [exact Hback | ai_interval]. }
        destruct Hcell as [v Hv].
        ai_reduce_turn; rewrite Hm0; cbn [Nat.eqb].
        rewrite upd_neq by ai_distinct; rewrite Hv.
        ai_finish h L R D 0 m1.
    + ai_reduce_turn; rewrite Hr.
      ai_finish h L R D m0 m1.
    + cbn [cached_remote] in Hc0; destruct Hc0 as [Hbound Hneq].
      assert (Hcell : exists v, h b = Some v).
      { eapply ai_backing_present; [exact Hback | ai_interval]. }
      destruct Hcell as [v Hv].
      ai_reduce_turn; rewrite Hv.
      ai_finish h L R D m0 m1.
    + cbn [cached_remote] in Hc0;
        destruct Hc0 as [Hbound [Hneq Hlink]].
      ai_reduce_turn; rewrite Hr.
      destruct (Nat.eqb (hd 0 R) old) eqn:Ecas.
      * apply Nat.eqb_eq in Ecas; subst old.
        ai_finish h L (b :: R) D m0 m1.
      * ai_finish h L R D m0 m1.
  - destruct p1 as [|b|b old|b old].
    + destruct m1 as [|m1].
      * ai_reduce_turn; rewrite Hm1; cbn [Nat.eqb].
        ai_finish h L R D m0 0.
      * assert (Hcell : exists v, h (S (S m1)) = Some v).
        { eapply ai_backing_present; [exact Hback | ai_interval]. }
        destruct Hcell as [v Hv].
        ai_reduce_turn; rewrite Hm1; cbn [Nat.eqb].
        rewrite upd_neq by ai_distinct; rewrite Hv.
        ai_finish h L R D m0 0.
    + ai_reduce_turn; rewrite Hr.
      ai_finish h L R D m0 m1.
    + cbn [cached_remote] in Hc1; destruct Hc1 as [Hbound Hneq].
      assert (Hcell : exists v, h b = Some v).
      { eapply ai_backing_present; [exact Hback | ai_interval]. }
      destruct Hcell as [v Hv].
      ai_reduce_turn; rewrite Hv.
      ai_finish h L R D m0 m1.
    + cbn [cached_remote] in Hc1;
        destruct Hc1 as [Hbound [Hneq Hlink]].
      ai_reduce_turn; rewrite Hr.
      destruct (Nat.eqb (hd 0 R) old) eqn:Ecas.
      * apply Nat.eqb_eq in Ecas; subst old.
        ai_finish h L (b :: R) D m0 m1.
      * ai_finish h L R D m0 m1.
Qed.

Lemma turn_total base capacity who s :
  allocator_inv base capacity s ->
  exists t event, turn base who s = Some (t,event).
Proof.
  intro Hinv; destruct (ai_turn_complete base capacity who s Hinv)
    as (t & event & Hturn & Hnext).
  now exists t, event.
Qed.

Lemma turn_preserves_inv base capacity who s t event :
  allocator_inv base capacity s ->
  turn base who s = Some (t,event) -> allocator_inv base capacity t.
Proof.
  intros Hinv Hturn.
  destruct (ai_turn_complete base capacity who s Hinv)
    as (t' & event' & Hturn' & Hnext).
  rewrite Hturn in Hturn'; inversion Hturn'; subst; exact Hnext.
Qed.

Lemma turn_preserves_backing base capacity who s t event :
  allocator_inv base capacity s ->
  turn base who s = Some (t,event) ->
  forall x, aheap t x <> None <-> aheap s x <> None.
Proof.
  intros Hinv Hturn x.
  pose proof (turn_preserves_inv base capacity who s t event Hinv Hturn) as Hnext.
  pose proof (allocator_inv_backing base capacity s Hinv) as Hbefore.
  pose proof (allocator_inv_backing base capacity t Hnext) as Hafter.
  rewrite (Hbefore x), (Hafter x); reflexivity.
Qed.

Lemma run_turns_preserves_inv base capacity script s last logs :
  allocator_inv base capacity s ->
  run_turns base script s = Some (last,logs) ->
  allocator_inv base capacity last.
Proof.
  revert s last logs; induction script as [|who rest IH];
    intros s last logs Hinv Hrun.
  - cbn [run_turns] in Hrun; inversion Hrun; subst; exact Hinv.
  - cbn [run_turns] in Hrun.
    destruct (turn base who s) as [[next event]|] eqn:Hstep;
      [|discriminate].
    destruct (run_turns base rest next) as [[last' suffix]|] eqn:Hrest;
      [|discriminate].
    inversion Hrun; subst.
    eapply IH; [eapply turn_preserves_inv; eauto | exact Hrest].
Qed.

Lemma run_turns_total base capacity script s :
  allocator_inv base capacity s ->
  exists last logs, run_turns base script s = Some (last,logs).
Proof.
  revert s; induction script as [|who rest IH]; intros s Hinv.
  - exists s, []; reflexivity.
  - destruct (turn_total base capacity who s Hinv) as (next & event & Hstep).
    assert (Hnext : allocator_inv base capacity next).
    { eapply turn_preserves_inv; eauto. }
    destruct (IH next Hnext) as (last & logs & Hrest).
    exists last, (match event with None => logs | Some o => o :: logs end).
    cbn [run_turns]; rewrite Hstep, Hrest; reflexivity.
Qed.
