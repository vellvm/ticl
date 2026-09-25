From Stdlib Require Import List Lia Arith.PeanoNat Fin Sorting.Permutation.
From TICL Require Import Utils.Execution.
From TICL Require Import ICTree.Interp.Yield.Execution.
From TICL Require Import Lang.CSL ICTree.Core ICTree.Equ ICTree.SBisim
  ICTree.Events.Writer ICTree.Interp.Refine.
From TICL Require Import Lang.CSL.Queue.Representation.
From examples Require Import CSL.Allocator.Layout.

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
  : option (AState * option (indexed (nat * nat))) :=
  let finish (h : Heap) (op : owner_pc) (r0 r1 : remote_pc)
      (event : option (nat * nat)) :=
    Some ({| aheap := h;
             acount := match event with None => acount s | Some _ => S (acount s) end;
             owner_state := op; remote0_state := r0; remote1_state := r1 |},
          match event with None => None
          | Some (tag,block) => Some (stamp (tag,block) (acount s)) end) in
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

(** The ownership VIEW: the invariant body with its ghost lists exposed.
    [allocator_inv] is exactly its existential closure -- a regrouping of the
    existing invariant, not a stronger ownership premise.  The ghost lists
    are proposition-level witnesses; nothing is added to [AState] or
    extracted into executable state. *)
Definition allocator_view (base capacity : nat) (s : AState) (L R D : list nat)
  : Prop :=
  0 < base /\ backing base capacity (aheap s) /\
  exists (m0 m1 : nat),
    aheap s (remote_head base) = Some (hd 0 R) /\
    aheap s (local_head base) = Some (hd 0 L) /\
    aheap s (drain_head base) = Some (hd 0 D) /\
    linked (fun a next => aheap s a = Some next) L 0 /\
    linked (fun a next => aheap s a = Some next) R 0 /\
    linked (fun a next => aheap s a = Some next) D 0 /\
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

Definition allocator_inv (base capacity : nat) (s : AState) : Prop :=
  exists L R D, allocator_view base capacity s L R D.

Definition state_equiv (s t : AState) : Prop :=
  heq (aheap s) (aheap t) /\ acount s = acount t /\
  owner_state s = owner_state t /\ remote0_state s = remote0_state t /\
  remote1_state s = remote1_state t.

Lemma initial_state_inv capacity c :
  allocator_inv 1 capacity (initial_state capacity c).
Proof.
  unfold allocator_inv, allocator_view, initial_state;
    cbn [aheap owner_state remote0_state remote1_state].
  exists (page_blocks 1 capacity), [], [].
  split; [lia|]; split.
  - intro x; apply page_heap_closed_dom.
  - exists 0, 0.
    split; [apply page_heap_remote|].
    split; [apply page_heap_local_blocks|].
    split; [apply page_heap_drain|].
    split.
    + apply linked_of_splits; intros prefix block rest E.
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
  | Some o => acount t = S (acount s) /\ indexed_index o = acount s
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
  Classes.RelationClasses Classes.RelationPairs Program.Equality.
From ExtLib Require Import Data.Option.
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

(** Both faults and successful turns are preserved.  In particular this
    statement does not assume the ownership invariant or heap finiteness. *)
#[global] Instance turn_proper base :
  Proper (eq ==> state_equiv ==> Roption (RelProd state_equiv eq)) (turn base).
Proof.
  intros who who' <- s t Hst.
  destruct s as [h c op r0 r1], t as [k d oq q0 q1].
  destruct Hst as [Hh [Hc [Ho [H0 H1]]]].
  cbn in Hh, Hc, Ho, H0, H1.
  subst d oq q0 q1.
  destruct who; [destruct op | destruct r0 | destruct r1];
    cbn [turn].
  all: repeat first
    [ progress (rewrite upd_unfold)
    | progress (rewrite <- Hh)
    | progress (cbn [aheap acount owner_state remote0_state remote1_state])
    | match goal with
      | Hheap : heq ?left ?right |- context [?left ?x] =>
          let Hr := fresh "Hread" in destruct (left x) eqn:Hr
      | |- context [if ?b then _ else _] =>
          let Hb := fresh "Htest" in destruct b eqn:Hb
      end ].
  all: constructor.
  all: split; unfold RelCompFun; cbn [fst snd]; [|reflexivity].
  all: unfold state_equiv;
    cbn [aheap acount owner_state remote0_state remote1_state].
  all: split;
    [ repeat apply upd_heq; exact Hh
    | repeat split; reflexivity ].
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

Lemma turn_event_counter base who s s' event :
  turn base who s = Some (s',event) ->
  acount s' = (acount s + List.length (event_obs event))%nat.
Proof.
  intro Hstep; pose proof (turn_counter base who s s' event Hstep) as H.
  destruct event as [o|]; cbn [event_obs List.length] in H |- *;
    [destruct H as [Hcount _]; lia | lia].
Qed.

From Stdlib Require Import List Lia Arith.PeanoNat Sorting.Permutation.
From TICL Require Import Lang.CSL.
From TICL Require Import Lang.CSL.Queue.Representation.
From examples Require Import CSL.Allocator.Layout.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Lemma ai_cached_remote_frame base capacity h h' pc :
  cached_remote base capacity h pc ->
  (forall b, In b (held pc) -> h' b = h b) ->
  cached_remote base capacity h' pc.
Proof.
  destruct pc; cbn [cached_remote held]; intros H Hframe; try exact H.
  destruct H as [Hbound [Hneq Hlink]]; repeat split; try assumption.
  rewrite Hframe; [exact Hlink | now left].
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
Proof. intros (_ & _ & _ & _ & H & _); exact H. Qed.

Lemma allocator_inv_null base capacity s :
  allocator_inv base capacity s -> aheap s 0 = None.
Proof.
  intros (_ & _ & _ & Hbase & Hback & _).
  destruct (aheap s 0) as [v|] eqn:E; [|reflexivity].
  assert (Hpresent : aheap s 0 <> None) by (rewrite E; discriminate).
  apply Hback in Hpresent; lia.
Qed.

Lemma allocator_inv_outside base capacity s x :
  allocator_inv base capacity s ->
  (x < base \/ base + page_size capacity <= x) -> aheap s x = None.
Proof.
  intros (_ & _ & _ & _ & Hback & _) Hout.
  destruct (aheap s x) as [v|] eqn:E; [|reflexivity].
  assert (Hpresent : aheap s x <> None) by (rewrite E; discriminate).
  apply Hback in Hpresent; lia.
Qed.

Lemma allocator_inv_held_member base capacity s (client : bool) b :
  allocator_inv base capacity s ->
  In b (held (if client then remote1_state s else remote0_state s)) ->
  In b (page_blocks base capacity).
Proof.
  intros (L & R & D & _ & _ & m0 & m1 & Hr & Hl & Hd & CL & CR & CD &
    Hm0 & Hm1 & Hp & Hop & Ho & Hc0 & Hc1) Hin.
  eapply Permutation_in; [exact Hp |].
  repeat rewrite in_app_iff; destruct client; tauto.
Qed.

(* These small tactics only discharge finite ownership arithmetic.  In
   particular, a cached head is never used as a freshness witness. *)
Ltac ai_member :=
  match goal with
  | Hp : Permutation ?xs (page_blocks ?base ?capacity)
    |- In ?x (page_blocks _ _) =>
      eapply Permutation_in; [exact Hp |];
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
      assert (Hcount : count_occ Nat.eq_dec xs x <= 1) by
        (apply (proj1 (NoDup_count_occ Nat.eq_dec xs));
         eapply Permutation_NoDup;
           [apply Permutation_sym, Hp | apply page_blocks_nodup]);
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
    eapply linked_mono;
    [ let a := fresh "a" in let b := fresh "b" in
      let Hin := fresh "Hin" in let Hab := fresh "Hab" in
      intros a b Hin Hab; rewrite upd_neq by ai_distinct; exact Hab
    | ai_chain ]].

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
    | match goal with
      | |- hd 0 ?xs = 0 \/ In (hd 0 ?xs) (page_blocks _ _) =>
          solve [destruct (head_in_or_default 0 xs) as [Hzero | Hhead];
            [now left | right; ai_member]]
      end
    | match goal with
      | |- hd 0 ?xs <> ?b =>
          solve [apply head_not_in;
            [intro; ai_count_contradiction b | ai_distinct]]
      end
    | solve [ai_distinct] ].

Local Ltac ai_reduce_turn :=
  cbn [turn aheap acount owner_state remote0_state remote1_state].

(** ** Ownership change of one turn.

    Every constructor below is a projection of an actual executable turn.
    In particular detach uses the current R, and publication prepends to R. *)
Definition owner_after_offer (client : bool) := if client then ORead else OOffer true.

Inductive ownership_transition :
  Actor -> owner_pc -> owner_pc -> option (indexed (nat * nat)) ->
  list nat -> list nat -> list nat -> list nat -> list nat -> list nat -> Prop :=
| ownership_read L R :
    ownership_transition Owner ORead (OCAS (List.hd 0 R)) None L R [] L R []
| ownership_cas_fail old L R :
    List.hd 0 R <> old ->
    ownership_transition Owner (OCAS old) ORead None L R [] L R []
| ownership_detach L R :
    ownership_transition Owner (OCAS (List.hd 0 R)) ODrain None L R [] L [] R
| ownership_drain_empty L R :
    ownership_transition Owner ODrain (OOffer false) None L R [] L R []
| ownership_drain L R b D idx :
    ownership_transition Owner ODrain ODrain (Some (stamp (tag_reclaim,b) idx))
      L R (b :: D) (b :: L) R D
| ownership_offer_empty client L R :
    ownership_transition Owner (OOffer client) (owner_after_offer client) None
      L R [] L R []
| ownership_offer client L R b idx :
    ownership_transition Owner (OOffer client) (owner_after_offer client)
      (Some (stamp (tag_alloc,b) idx)) (b :: L) R [] L R []
| ownership_remote who pc event L R D :
    who <> Owner ->
    (event = None \/ exists b idx, event = Some (stamp (tag_retry,b) idx)) ->
    ownership_transition who pc pc event L R D L R D
| ownership_publish who pc L R D b idx :
    who <> Owner ->
    ownership_transition who pc pc (Some (stamp (tag_retire,b) idx))
      L R D L (b :: R) D.

(** Finish one branch: the computed result, its ownership view at the new
    ghost lists, and the ownership constructor of the branch. *)
Ltac ai_finish h L R D m0 m1 :=
  cbn [aheap acount owner_state remote0_state remote1_state];
  try rewrite Nat.eqb_refl;
  repeat match goal with
  | E : Nat.eqb _ _ = _ |- _ => progress rewrite E
  end;
  do 2 eexists; exists L, R, D; split; [reflexivity |]; split;
  [ unfold allocator_view;
      cbn [aheap acount owner_state remote0_state remote1_state];
    split; [assumption |]; split; [ai_backing |];
    exists m0, m1;
    cbn [hd held];
    repeat split; ai_obligation h
  | cbn [owner_state];
    first [apply ownership_read | apply ownership_detach |
      apply ownership_drain_empty | apply ownership_drain |
      apply ownership_offer_empty | apply ownership_offer |
      apply ownership_cas_fail; now apply Nat.eqb_neq |
      apply ownership_publish; discriminate |
      apply ownership_remote; [discriminate|left; reflexivity] |
      apply ownership_remote; [discriminate|right; do 2 eexists; reflexivity]] ].

(** Transition completeness: on the ownership view every turn succeeds,
    re-establishes the view, and changes ownership by one constructor. *)
Lemma turn_view_complete base capacity who s L R D :
  allocator_view base capacity s L R D ->
  exists t event L' R' D',
    turn base who s = Some (t,event) /\
    allocator_view base capacity t L' R' D' /\
    ownership_transition who (owner_state s) (owner_state t)
      event L R D L' R' D'.
Proof.
  destruct s as [h count op p0 p1].
  cbn [allocator_view aheap acount owner_state remote0_state remote1_state].
  intros (Hbase & Hback & m0 & m1 & Hr & Hl & Hd & CL & CR & CD &
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
      * cbn [linked] in CD; destruct CD as [Hnext CD].
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
           ++ cbn [linked] in CL; destruct CL as [Hnext CL].
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
           ++ cbn [linked] in CL; destruct CL as [Hnext CL].
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

Lemma turn_view_step base capacity who s t event L R D :
  allocator_view base capacity s L R D ->
  turn base who s = Some (t,event) ->
  exists L' R' D', allocator_view base capacity t L' R' D' /\
    ownership_transition who (owner_state s) (owner_state t)
      event L R D L' R' D'.
Proof.
  intros Hview Hturn.
  destruct (turn_view_complete base capacity who s L R D Hview)
    as (t' & event' & L' & R' & D' & Hturn' & Hview' & Hstep).
  rewrite Hturn in Hturn'; injection Hturn' as <- <-.
  exists L', R', D'; split; assumption.
Qed.

Lemma turn_total base capacity who s :
  allocator_inv base capacity s ->
  exists t event, turn base who s = Some (t,event).
Proof.
  intros (L & R & D & Hview).
  destruct (turn_view_complete base capacity who s L R D Hview)
    as (t & event & _ & _ & _ & Hturn & _).
  now exists t, event.
Qed.

Lemma turn_preserves_inv base capacity who s t event :
  allocator_inv base capacity s ->
  turn base who s = Some (t,event) -> allocator_inv base capacity t.
Proof.
  intros (L & R & D & Hview) Hturn.
  destruct (turn_view_step base capacity who s t event L R D Hview Hturn)
    as (L' & R' & D' & Hview' & _).
  now exists L', R', D'.
Qed.

Lemma allocator_initial_inv capacity c s :
  s = initial_state capacity c -> allocator_inv 1 capacity s.
Proof. intros ->; apply initial_state_inv. Qed.

(** ** The allocator's validity and construction interface.

    Exactly two instantiations of [Utils.Execution]; no example-local
    execution record, constructor or replay proof remains. *)
Definition allocator_valid (capacity c : nat)
  (e : Execution AState Actor (option (indexed (nat * nat)))) : Prop :=
  execution_valid (fun who s o s' => turn 1 who s = Some (s',o))
    (fun s => s = initial_state capacity c) e.

Definition allocator_execution (capacity c : nat) (picks : nat -> Actor)
  : Execution AState Actor (option (indexed (nat * nat))) :=
  execution_of_choices (turn 1) (allocator_inv 1 capacity)
    (fun who s Hs =>
       match turn_total 1 capacity who s Hs with
       | ex_intro _ t (ex_intro _ ev H) => ex_intro _ (t,ev) H
       end)
    (fun who s s' o Hs Hstep => turn_preserves_inv 1 capacity who s s' o Hs Hstep)
    (initial_state capacity c) (initial_state_inv capacity c) picks.
