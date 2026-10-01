(** * The canonical CSL effect interpreter.

    This module owns the CSL effect sum, its interpretation state and the one
    payload-polymorphic handler [sh] that pairs the shared checked heap with
    the shared indexing writer.  Everything here is stated over effects and
    trees: it does not mention CSL syntax.  The source language
    ([Lang.CSL.Mod]) specializes these laws to its denotation.

    Generic checked heap access, allocation search, indexed observation and
    the scheduler/segment machinery live one layer further down and are
    re-exported from here. *)

From Stdlib Require Import List Lia Arith.PeanoNat Fin Vector.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad.

From Coinduction Require Import coinduction lattice tactics.

From TICL Require Export
  Events.HeapModel
  ICTree.Events.Heap
  ICTree.Events.Writer
  ICTree.Interp.Heap
  ICTree.Logic.Heap
  ICTree.Trace
  ICTree.Interp.Refine
  ICTree.Interp.Yield.Nondeterministic
  ICTree.Interp.Yield.Segments.

From TICL Require Import
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Trans
  ICTree.Events.State
  ICTree.Events.Yield
  ICTree.Interp.State.Mod
  ICTree.Interp.Yield.Mod
  ICTree.Interp.Yield.SBisim
  ICTree.Interp.Yield.RoundRobin
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.AG
  ICTree.Logic.Bind
  ICTree.Logic.Iter
  ICTree.Logic.State
  Logic.World
  Logic.Core
  Utils.Vectors.

Import ICtree ICTreeNotations TiclNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.

(** ** Effects and interpretation state *)

(** [sE] is a notation, not a definition: the payload-polymorphic handler
    [sh] below is typed over [heapE + writerE A], so instantiating it at the
    tagged payload yields this sum syntactically, and rewrites stated over
    [sE] keep matching terms elaborated through [sh]. *)
Notation sE := (heapE + writerE (nat * nat))%type.

Definition semit (q v : nat) : ictree sE unit :=
  ICtree.trigger (Log (q,v)).

(** Interpretation state: the SHARED managed memory (data heap and live
    allocation extents) and one GLOBAL occurrence counter.  A state is
    [((h,allocs),c)]. *)
Notation SSig := (ManagedHeap * nat)%type.

(** The one CSL handler: the shared checked-heap handler summed with the
    shared indexing handler.  It is polymorphic in the observation payload;
    the tagged source language uses [nat * nat], a unary reference model uses
    [nat].  The occurrence index is supplied by [h_indexed], which owns the
    counter and passes the managed memory through unchanged. *)
Definition sh {A : Type} :
  (heapE + writerE A) ~> stateT SSig (ictreeW (indexed A)) :=
  h_sum heap_handler h_indexed.

(** ** Thread effects *)

Definition CEff := (yieldE + (forkE + sE))%type.
#[global] Instance ReSum_heap_CEff : ReSum heapE CEff :=
  fun e => inr (inr (inl e)).
#[global] Instance ReSumRet_heap_CEff : ReSumRet heapE CEff :=
  fun e response => response.
#[global] Instance ReSum_tagged_CEff : ReSum (writerE (nat * nat)) CEff :=
  fun e => inr (inr (inr e)).
#[global] Instance ReSumRet_tagged_CEff : ReSumRet (writerE (nat * nat)) CEff :=
  fun e response => response.
Definition source_yield : ictree CEff unit :=
  Vis (inl Yield) (fun _ => Ret tt).
Definition source_fork : ictree CEff bool :=
  Vis (inr (inl Fork)) (fun b => Ret b).

(** ** The two response-relation instances of the generic segment theory. *)
Notation csl_sb :=
  (fun X (t u : ictreeW (indexed (nat * nat)) X) => t ~ u).
Notation csl_equ :=
  (fun X (t u : ictreeW (indexed (nat * nat)) X) => t ≅ u).

(** ** Raw physical free through the shared heap event *)

Lemma raw_heap_free_head a (K : unit -> thread sE) :
  (heap_free (E:=CEff) a >>= K) ≅
    Vis (inr (inr (inl (HFree a)))) K.
Proof.
  unfold heap_free, ICtree.trigger, resum, resum_ret,
    ReSum_heap_CEff, ReSumRet_heap_CEff.
  rewrite bind_vis; setoid_rewrite bind_ret_l; reflexivity.
Qed.

Lemma interp_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) c :
  managed_free memory base = Some memory' ->
  interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,c) ~
  interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',c).
Proof.
  intro Free.
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K))
    (ts @ i := Vis (inr (inr (inl (HFree base)))) K)
    (Some i) m (memory,c)
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_heap_free_head base K))) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user with (e:=inl (HFree base)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (heap_handler_free base memory memory' c Free) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l, Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_rr_heap_free_invalid n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory : ManagedHeap) c :
  managed_free memory base = None ->
  interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,c) ~
  (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Invalid.
  pose proof (interp_schedule_rr_equ sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K))
    (ts @ i := Vis (inr (inr (inl (HFree base)))) K)
    (Some i) m (memory,c)
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_heap_free_head base K))) as Hpool.
  rewrite Hpool.
  erewrite interp_schedule_rr_user with (e:=inl (HFree base)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (heap_handler_free_invalid base memory c Invalid) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Lemma interp_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) c :
  managed_free memory base = Some memory' ->
  interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,c) ~
  interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',c).
Proof.
  intro Free.
  pose proof ((interp_schedule_nd_equ sh) (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K))
    (ts @ i := Vis (inr (inr (inl (HFree base)))) K)
    (Some i) (memory,c)
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_heap_free_head base K))) as Hpool.
  rewrite Hpool.
  erewrite (interp_schedule_nd_user sh) with (e:=inl (HFree base)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (heap_handler_free base memory memory' c Free) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_ret_l, Vector.replace_replace_eq; reflexivity.
Qed.

Lemma interp_nd_heap_free_invalid n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory : ManagedHeap) c :
  managed_free memory base = None ->
  interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,c) ~
  (stuck : ictreeW (indexed (nat * nat)) (unit * SSig)).
Proof.
  intro Invalid.
  pose proof ((interp_schedule_nd_equ sh) (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K))
    (ts @ i := Vis (inr (inr (inl (HFree base)))) K)
    (Some i) (memory,c)
    (replace_pool_equ ts ts i _ _ (pool_equ_refl ts) (raw_heap_free_head base K))) as Hpool.
  rewrite Hpool.
  erewrite (interp_schedule_nd_user sh) with (e:=inl (HFree base)) (k:=K)
    by (rewrite Vector.nth_replace_eq; reflexivity).
  lazymatch goal with |- (?t >>= ?next) ~ _ =>
    etransitivity;
    [apply sbisim_clo_bind_eq with (k2:=next);
      [eapply equ_clos_sbisim_goal;
        [exact (heap_handler_free_invalid base memory c Invalid) | reflexivity | reflexivity]
      | intro result; reflexivity] |]
  end.
  rewrite bind_stuck_equ; reflexivity.
Qed.

Local Typeclasses Transparent equ sbisim.

(** ** Selection from an unfocused nonempty pool *)

Lemma anl_csl_nd_select n (ts : pool sE (S n)) (memory : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (memory,c)}, {w} |= ψ )>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  apply anl_br.
Qed.

Lemma anr_csl_nd_select n (ts : pool sE (S n)) (memory : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    ts (None) (memory,c)}, {w} |= φ AN ψ ]> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    ts (Some j) (memory,c)}, {w} |= ψ ]>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  apply anr_br.
Qed.

Lemma aul_csl_nd_select n (ts : pool sE (S n)) (memory : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,c))}, {w} |= ψ )> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (memory,c)}, {w} |= φ AU ψ )>))).

Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply aul_br.
Qed.

Lemma aur_csl_nd_select n (ts : pool sE (S n)) (memory : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    ts (None) (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,c))}, {w} |= ψ ]> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    ts (Some j) (memory,c)}, {w} |= φ AU ψ ]>))).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply aur_br.
Qed.

Lemma ag_csl_nd_select n (ts : pool sE (S n)) (memory : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (memory,c)}, {w} |= AG φ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (memory,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply ag_br.
Qed.

Lemma anl_csl_rr_select n (ts : pool sE (S n)) m (memory : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (memory,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma anr_csl_rr_select n (ts : pool sE (S n)) m (memory : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    ts (None) m (memory,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma aul_csl_rr_select n (ts : pool sE (S n)) m (memory : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (memory,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma aur_csl_rr_select n (ts : pool sE (S n)) m (memory : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    ts (None) m (memory,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma ag_csl_rr_select n (ts : pool sE (S n)) m (memory : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (memory,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (memory,c)}, {w} |= AG φ )>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

(** ** Valid whole-block free through the shared raw heap event *)

Lemma anl_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',c)}, {w} |= φ AN ψ )>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' c Free); reflexivity.
Qed.

Lemma anr_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,c)}, {w} |= φ AN ψ ]> <->
   <[ {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',c)}, {w} |= φ AN ψ ]>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' c Free); reflexivity.
Qed.

Lemma aul_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',c)}, {w} |= φ AU ψ )>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' c Free); reflexivity.
Qed.

Lemma aur_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,c)}, {w} |= φ AU ψ ]> <->
   <[ {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',c)}, {w} |= φ AU ψ ]>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' c Free); reflexivity.
Qed.

Lemma ag_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) (memory,c)}, {w} |= AG φ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (memory',c)}, {w} |= AG φ )>).
Proof.
  intro Free; rewrite (interp_nd_heap_free n ts i base K memory memory' c Free); reflexivity.
Qed.

Lemma anl_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',c)}, {w} |= φ AN ψ )>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' c Free); reflexivity.
Qed.

Lemma anr_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,c)}, {w} |= φ AN ψ ]> <->
   <[ {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',c)}, {w} |= φ AN ψ ]>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' c Free); reflexivity.
Qed.

Lemma aul_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',c)}, {w} |= φ AU ψ )>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' c Free); reflexivity.
Qed.

Lemma aur_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  managed_free memory base = Some memory' ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,c)}, {w} |= φ AU ψ ]> <->
   <[ {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',c)}, {w} |= φ AU ψ ]>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' c Free); reflexivity.
Qed.

Lemma ag_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  base (K : unit -> thread sE) m (memory memory' : ManagedHeap) c w
  (φ : ticllW (indexed (nat * nat))) :
  managed_free memory base = Some memory' ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) base >>= K)) (Some i) m (memory,c)}, {w} |= AG φ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (memory',c)}, {w} |= AG φ )>).
Proof.
  intro Free; rewrite (interp_rr_heap_free n ts i base K m memory memory' c Free); reflexivity.
Qed.
