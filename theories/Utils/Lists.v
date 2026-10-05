From Stdlib Require Import List Lia Arith.PeanoNat Sorting.Permutation.

Import ListNotations.

(** Pure list operations shared by abstract and heap-backed queues. *)
Lemma hd_app {A} (l1 l2 : list A) d :
  hd d (l1 ++ l2) = hd (hd d l2) l1.
Proof. now destruct l1. Qed.

Lemma hd_default {A} (l : list A) d d' :
  l <> [] -> hd d l = hd d' l.
Proof. destruct l; intro H; [contradiction | reflexivity]. Qed.

Lemma last_in {A} (l : list A) d : l <> [] -> In (last l d) l.
Proof.
  intro H; destruct (exists_last H) as (l' & x & ->).
  rewrite last_last, in_app_iff; right; apply in_eq.
Qed.

Definition rotl {A} (l : list A) : list A :=
  match l with [] => [] | x :: xs => xs ++ [x] end.

Lemma rotl_cons {A} (x : A) xs : rotl (x :: xs) = xs ++ [x].
Proof. reflexivity. Qed.

Lemma rotl_perm {A} (l : list A) : Permutation l (rotl l).
Proof.
  destruct l as [| x xs]; cbn; [constructor |].
  apply Permutation_cons_app; rewrite app_nil_r; apply Permutation_refl.
Qed.

Lemma rotl_nonnil {A} (l : list A) : l <> [] -> rotl l <> [].
Proof.
  intro H; destruct l as [| x xs]; [contradiction |]; cbn.
  intro C; apply app_eq_nil in C as (_ & C); discriminate.
Qed.

Fixpoint rotlN {A} (n : nat) (l : list A) : list A :=
  match n with 0 => l | S k => rotlN k (rotl l) end.

(** Zero-based FIRST matching position. Duplicate payloads are allowed.
    The comparator is explicit: clients can use [Nat.eqb] or their existing
    [RelDec] equality without installing another equality instance. Only the
    lemmas connecting matches to propositional equality require correctness. *)
Fixpoint find_index {A} (eqb : A -> A -> bool) (t : A) (l : list A) : option nat :=
  match l with
  | [] => None
  | h :: ts => if eqb h t then Some 0 else option_map S (find_index eqb t ts)
  end.

Lemma find_index_cons {A} (eqb : A -> A -> bool) t h ts :
  find_index eqb t (h :: ts) =
    (if eqb h t then Some 0 else option_map S (find_index eqb t ts)).
Proof. reflexivity. Qed.

Lemma find_index_app_l {A} (eqb : A -> A -> bool) t ts n l :
  find_index eqb t ts = Some n -> find_index eqb t (ts ++ l) = Some n.
Proof.
  revert n; induction ts as [| a ts IH]; intros n H; cbn in *; [discriminate |].
  destruct (eqb a t); [exact H |].
  destruct (find_index eqb t ts) as [m |] eqn:Hf; cbn in *; [| discriminate].
  erewrite IH; eauto.
Qed.

Lemma find_index_nonnil {A} (eqb : A -> A -> bool) t l n :
  find_index eqb t l = Some n -> l <> [].
Proof. destruct l; cbn; intros H; [discriminate | congruence]. Qed.

(** A non-head occurrence moves one position closer, even with duplicates. *)
Lemma find_index_rotl {A} (eqb : A -> A -> bool) t v vs d :
  find_index eqb t (v :: vs) = Some (S d) ->
  find_index eqb t (rotl (v :: vs)) = Some d.
Proof.
  cbn; destruct (eqb v t); [discriminate |].
  destruct (find_index eqb t vs) as [m |] eqn:Hf; cbn; [| discriminate].
  intro H; injection H as H; subst m.
  now apply find_index_app_l.
Qed.

Section EqualitySearch.
  Context {A : Type} (eqb : A -> A -> bool)
    (eqb_correct : forall x y, eqb x y = true <-> x = y).

  Lemma find_index_last_ex t ts :
    exists n, find_index eqb t (ts ++ [t]) = Some n.
  Proof.
    induction ts as [| a ts IH]; cbn.
    - exists 0; now rewrite (proj2 (eqb_correct t t) eq_refl).
    - destruct (eqb a t); [now exists 0 |].
      destruct IH as (n & Hn); exists (S n); now rewrite Hn.
  Qed.

  Lemma find_index_in t l n : find_index eqb t l = Some n -> In t l.
  Proof.
    revert n; induction l as [| a l IH]; intros n H; cbn in *; [discriminate |].
    destruct (eqb a t) eqn:Ha.
    - left; now apply eqb_correct.
    - right; destruct (find_index eqb t l) eqn:Hf; cbn in H; [| discriminate].
      eapply IH; reflexivity.
  Qed.

  Lemma find_index_none t l : find_index eqb t l = None <-> ~ In t l.
  Proof.
    induction l as [| a l IH]; cbn; [tauto |].
    destruct (eqb a t) eqn:Ha.
    - apply eqb_correct in Ha; subst a; split; [discriminate | tauto].
    - assert (Hne : a <> t).
      { intro H; apply eqb_correct in H; congruence. }
      split.
      + intro H; assert (Hnone : find_index eqb t l = None).
        { destruct (find_index eqb t l); cbn in H; congruence. }
        apply IH in Hnone; tauto.
      + intro H; assert (Hnone : find_index eqb t l = None) by (apply IH; tauto).
        now rewrite Hnone.
  Qed.

  Lemma find_index_head t v vs : find_index eqb t (v :: vs) = Some 0 -> v = t.
  Proof.
    cbn; destruct (eqb v t) eqn:Hv.
    - intros _; now apply eqb_correct.
    - destruct (find_index eqb t vs); discriminate.
  Qed.

  (** A head occurrence wraps around; an earlier duplicate may become first. *)
  Lemma find_index_rotl_pres t v vs d :
    find_index eqb t (v :: vs) = Some d ->
    exists d', find_index eqb t (rotl (v :: vs)) = Some d'.
  Proof.
    intros H; destruct d as [| d].
    - apply find_index_head in H; subst v; cbn; apply find_index_last_ex.
    - exists d; now apply find_index_rotl.
  Qed.
End EqualitySearch.

(** Splitting a pointwise relation across an append needs the prefix lengths;
    [Forall2_app_inv_l] alone only produces an existential decomposition. *)
Lemma Forall2_app_inv_len {A B} (R : A -> B -> Prop)
  (l1 l2 : list A) (l1' l2' : list B) :
  length l1 = length l1' ->
  Forall2 R (l1 ++ l2) (l1' ++ l2') -> Forall2 R l1 l1' /\ Forall2 R l2 l2'.
Proof.
  revert l1'; induction l1 as [| a l1 IH]; intros [| b l1'] Hlen H;
    cbn in Hlen, H; try discriminate.
  - split; [constructor | exact H].
  - rewrite Forall2_cons_iff in H; destruct H as [Hab H].
    apply IH in H as [H1 H2]; [| lia].
    split; [rewrite Forall2_cons_iff; split; assumption | exact H2].
Qed.

(** ** Heads of lists that may be empty *)

(** The head of a possibly-empty list is either the supplied default or an
    actual member.  Callers combine this with their own membership premise. *)
Lemma head_in_or_default {A} (d : A) (xs : list A) :
  List.hd d xs = d \/ In (List.hd d xs) xs.
Proof. destruct xs as [| x xs]; cbn; [now left | right; now left]. Qed.

Lemma head_not_in {A} (d x : A) (xs : list A) :
  ~ In x xs -> d <> x -> List.hd d xs <> x.
Proof.
  destruct xs as [| a xs]; cbn; intros Hnot Hd; [exact Hd |].
  intro E; apply Hnot; left; exact E.
Qed.

(** ** Relation-polymorphic linking of a list of nodes

    [linked edge nodes last] says consecutive members of [nodes] are related by
    [edge], with the final member related to [last].  The terminator is a
    PARAMETER: that is what lets a client retarget the last link by
    [linked_split] + [linked_app] instead of a bespoke surgery lemma.  The
    relation is arbitrary, so the same predicate serves free-list links stored
    at [a] and queue links stored at [S a]. *)
Fixpoint linked {A : Type} (edge : A -> A -> Prop)
  (nodes : list A) (last : A) : Prop :=
  match nodes with
  | [] => True
  | a :: rest => edge a (List.hd last rest) /\ linked edge rest last
  end.

Lemma linked_app {A} (edge : A -> A -> Prop) (xs ys : list A) last :
  linked edge xs (List.hd last ys) ->
  linked edge ys last ->
  linked edge (xs ++ ys) last.
Proof.
  revert last; induction xs as [| a xs IH]; intros last H1 H2; cbn in *;
    [exact H2 |].
  destruct H1 as [Ha Hxs]; split.
  - now rewrite hd_app.
  - now apply IH.
Qed.

Lemma linked_split {A} (edge : A -> A -> Prop) (xs ys : list A) last :
  linked edge (xs ++ ys) last ->
  linked edge xs (List.hd last ys) /\ linked edge ys last.
Proof.
  revert last; induction xs as [| a xs IH]; intros last H; cbn in *;
    [split; [exact I | exact H] |].
  destruct H as [Ha Hrest]; apply IH in Hrest as [H1 H2].
  rewrite hd_app in Ha; split; [split; assumption | exact H2].
Qed.

Lemma linked_mono {A} (edge edge' : A -> A -> Prop) (nodes : list A) last :
  (forall a b, In a nodes -> edge a b -> edge' a b) ->
  linked edge nodes last -> linked edge' nodes last.
Proof.
  induction nodes as [| a rest IH]; cbn; intros Hmono H; [exact I |].
  destruct H as [Ha Hrest]; split.
  - apply Hmono; [now left | exact Ha].
  - apply IH; [intros x y Hx; apply Hmono; now right | exact Hrest].
Qed.

(** Every list-suffix lookup licenses the whole chain at once. *)
Lemma linked_of_splits {A} (edge : A -> A -> Prop) (nodes : list A) last :
  (forall prefix a rest, nodes = prefix ++ a :: rest -> edge a (List.hd last rest)) ->
  linked edge nodes last.
Proof.
  induction nodes as [| a rest IH]; intro Links; [exact I |].
  split.
  - apply (Links [] a rest); reflexivity.
  - apply IH; intros prefix b rest' E.
    apply (Links (a :: prefix) b rest'); cbn; now rewrite E.
Qed.

(** ** Small [map]/[seq]/[firstn] facts used to read windows.

    The write direction: a window is determined by its pointwise values. *)
Lemma map_seq_eq {A} lo len (f : nat -> A) xs d :
  length xs = len ->
  (forall i, i < len -> f (lo+i) = nth i xs d) ->
  map f (seq lo len) = xs.
Proof.
  intros Hlen Hnth; apply List.nth_ext with (d := f lo) (d' := d).
  - rewrite List.length_map, List.length_seq; symmetry; exact Hlen.
  - intros i Hi; rewrite List.length_map, List.length_seq in Hi.
    rewrite List.map_nth, List.seq_nth by exact Hi; now apply Hnth.
Qed.

Lemma firstn_seq lo len k :
  k <= len -> List.firstn k (List.seq lo len) = List.seq lo k.
Proof.
  revert lo len; induction k as [|k IH]; intros lo len Hk; [reflexivity|].
  destruct len as [|len]; [lia|].
  cbn [List.seq List.firstn]; f_equal; apply IH; lia.
Qed.

Lemma map_seq_firstn {A} (f : nat -> A) lo len k :
  k <= len ->
  List.firstn k (List.map f (List.seq lo len)) = List.map f (List.seq lo k).
Proof.
  intro Hk; now rewrite <- (firstn_seq lo len k Hk), List.firstn_map.
Qed.

(** ** Periodic choice sequences.

    [first :: rest] makes the period nonempty, including a one-element
    period, without an arbitrary default for an empty cycle. *)
Definition periodic_choices {A : Type}
  (prefix : list A) (first : A) (rest : list A) (k : nat) : A :=
  if Nat.ltb k (length prefix)
  then List.nth k prefix first
  else List.nth ((k - length prefix) mod (S (length rest))) (first :: rest) first.

Lemma periodic_choices_before {A} (prefix : list A) first rest k :
  k < length prefix ->
  periodic_choices prefix first rest k = List.nth k prefix first.
Proof.
  intro Hk; unfold periodic_choices.
  now rewrite (proj2 (Nat.ltb_lt k (length prefix)) Hk).
Qed.

Lemma periodic_choices_after {A} (prefix : list A) first rest k :
  length prefix <= k ->
  periodic_choices prefix first rest k =
    List.nth ((k - length prefix) mod (S (length rest))) (first :: rest) first.
Proof.
  intro Hk; unfold periodic_choices.
  destruct (Nat.ltb_spec k (length prefix)); [lia|reflexivity].
Qed.

Lemma periodic_choices_nth {A} (prefix : list A) first rest j :
  periodic_choices prefix first rest (length prefix + j) =
    List.nth (j mod (S (length rest))) (first :: rest) first.
Proof.
  rewrite periodic_choices_after by lia.
  now replace (length prefix + j - length prefix) with j by lia.
Qed.

(** The [i]-th choice of any whole round. *)
Lemma periodic_choices_round {A} (prefix : list A) first rest rounds i :
  i < S (length rest) ->
  periodic_choices prefix first rest
    (length prefix + rounds * S (length rest) + i) =
    nth i (first :: rest) first.
Proof.
  intro Hi.
  replace (length prefix + rounds * S (length rest) + i)
    with (length prefix + (i + rounds * S (length rest))) by lia.
  rewrite periodic_choices_nth, Nat.Div0.mod_add.
  now rewrite Nat.mod_small by exact Hi.
Qed.

Lemma periodic_prefix_script {A} (prefix : list A) first rest :
  map (periodic_choices prefix first rest) (seq 0 (length prefix)) = prefix.
Proof.
  apply (map_seq_eq 0 (length prefix) _ prefix first); [reflexivity|].
  intros i Hi; cbn [Nat.add]; now apply periodic_choices_before.
Qed.

Lemma periodic_cycle_script {A} (prefix : list A) first rest rounds :
  map (periodic_choices prefix first rest)
    (seq (length prefix + rounds * S (length rest)) (S (length rest))) =
    first :: rest.
Proof.
  apply (map_seq_eq _ (S (length rest)) _ (first :: rest) first); [reflexivity|].
  intros i Hi; now apply periodic_choices_round.
Qed.
