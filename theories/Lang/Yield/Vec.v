From Stdlib Require Import Fin.

(** Replace the value stored at one finite index. *)
Definition replace_pool {A n} (v : Fin.t n -> A) (i : Fin.t n) (a : A) : Fin.t n -> A :=
  fun j =>
    match Fin.eq_dec i j with
    | left _ => a
    | right _ => v j
    end.

Lemma replace_pool_hit {A n} (v : Fin.t n -> A) (i : Fin.t n) (a : A) :
  replace_pool v i a i = a.
Proof.
  unfold replace_pool.
  destruct (Fin.eq_dec i i) as [_ | Hneq].
  - reflexivity.
  - contradiction Hneq; reflexivity.
Qed.

Lemma replace_pool_miss {A n} (v : Fin.t n -> A) (i j : Fin.t n) (a : A) :
  i <> j -> replace_pool v i a j = v j.
Proof.
  intro Hneq.
  unfold replace_pool.
  destruct (Fin.eq_dec i j) as [Heq | _].
  - contradiction Hneq; exact Heq.
  - reflexivity.
Qed.

(** Remove one index from a non-empty finite vector/function. *)
Fixpoint remove_pool {A} {n : nat} : (Fin.t (S n) -> A) -> Fin.t (S n) -> Fin.t n -> A :=
  match n return (Fin.t (S n) -> A) -> Fin.t (S n) -> Fin.t n -> A with
  | 0 => fun _ _ j => match j with end
  | S n' => fun v i j =>
      match i in Fin.t (S n0) return n0 = S n' -> Fin.t (S n') -> A with
      | F1 => fun _ j => v (FS j)
      | FS i' => fun e j =>
          match j in Fin.t (S n1) return n1 = n' -> A with
          | F1 => fun _ => v F1
          | FS j' => fun e' => remove_pool (fun k => v (FS k)) (Fin.cast i' e) (Fin.cast j' e')
          end eq_refl
      end eq_refl j
  end.

(** Prepend a value at [F1] and shift the existing pool right. *)
Definition cons_pool {A n} (x : A) (v : Fin.t n -> A) : Fin.t (S n) -> A :=
  fun i => Fin.caseS' i (fun _ => A) x (fun j => v j).

Lemma cons_pool_head {A n} (x : A) (v : Fin.t n -> A) :
  cons_pool x v Fin.F1 = x.
Proof. reflexivity. Qed.

Lemma cons_pool_tail {A n} (x : A) (v : Fin.t n -> A) (i : Fin.t n) :
  cons_pool x v (Fin.FS i) = v i.
Proof. reflexivity. Qed.
