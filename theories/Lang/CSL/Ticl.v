From Stdlib Require Import Arith.PeanoNat Fin Vector.
From Coinduction Require Import coinduction lattice tactics.
From TICL Require Import
  Lang.CSL.Syntax Lang.CSL.Heap Lang.CSL.Denote Lang.CSL.Interp
  ICTree.Core ICTree.Equ ICTree.SBisim ICTree.Events.Writer
  ICTree.Events.Yield ICTree.Events.Heap ICTree.Interp.Refine ICTree.Interp.Yield.Mod
  ICTree.Interp.Yield.RoundRobin ICTree.Logic.Trans
  ICTree.Logic.AX ICTree.Logic.AF ICTree.Logic.AG
  ICTree.Logic.Bind ICTree.Logic.State ICTree.Logic.CanStep Logic.Core Utils.Vectors.

Import ICtree ICTreeNotations TiclNotations VectorNotations.
Local Open Scope ictree_scope.
Local Open Scope fin_vector_scope.
Local Open Scope ticl_scope.
Local Typeclasses Transparent equ sbisim.

(** ** Selection from an unfocused nonempty pool *)

Lemma anl_csl_nd_select n (ts : pool sE (S n)) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (h,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (h,c)}, {w} |= ψ )>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  apply anl_br.
Qed.

Lemma anr_csl_nd_select n (ts : pool sE (S n)) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    ts (None) (h,c)}, {w} |= φ AN ψ ]> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (h,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    ts (Some j) (h,c)}, {w} |= ψ ]>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  apply anr_br.
Qed.

Lemma aul_csl_nd_select n (ts : pool sE (S n)) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (h,c))}, {w} |= ψ )> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (h,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (h,c)}, {w} |= φ AU ψ )>))).

From Coinduction Require Import coinduction.
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply aul_br.
Qed.

Lemma aur_csl_nd_select n (ts : pool sE (S n)) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    ts (None) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (h,c))}, {w} |= ψ ]> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (h,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    ts (Some j) (h,c)}, {w} |= φ AU ψ ]>))).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply aur_br.
Qed.

Lemma ag_csl_nd_select n (ts : pool sE (S n)) h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    ts (None) (h,c)}, {w} |= AG φ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    ts (Some j) (h,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    ts (Some j) (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_schedule_nd_select sh).
  symmetry; apply ag_br.
Qed.

Lemma anl_csl_rr_select n (ts : pool sE (S n)) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma anr_csl_rr_select n (ts : pool sE (S n)) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    ts (None) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma aul_csl_rr_select n (ts : pool sE (S n)) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma aur_csl_rr_select n (ts : pool sE (S n)) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    ts (None) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

Lemma ag_csl_rr_select n (ts : pool sE (S n)) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    ts (None) m (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    ts (Some (rr_pick n m)) (S m) (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite interp_schedule_rr_select; reflexivity.
Qed.

(** ** Checked silent effects *)

Lemma anl_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h c Lookup); reflexivity.
Qed.

Lemma anr_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h c Lookup); reflexivity.
Qed.

Lemma aul_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h c Lookup); reflexivity.
Qed.

Lemma aur_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h c Lookup); reflexivity.
Qed.

Lemma ag_csl_nd_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some value)) (Some i) (h,c)}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_read_value n ts i a value K h c Lookup); reflexivity.
Qed.

Lemma anl_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h c Lookup); reflexivity.
Qed.

Lemma anr_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h c Lookup); reflexivity.
Qed.

Lemma aul_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h c Lookup); reflexivity.
Qed.

Lemma aur_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some value ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h c Lookup); reflexivity.
Qed.

Lemma ag_csl_rr_read n (ts : pool sE (S n)) (i : Fin.t (S n))
  a value (K : option nat -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  h a = Some value ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRead a) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some value)) (Some i) m (h,c)}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_read_value n ts i a value K m h c Lookup); reflexivity.
Qed.

Lemma anl_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (upd h a v,c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h c Present); reflexivity.
Qed.

Lemma anr_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (upd h a v,c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h c Present); reflexivity.
Qed.

Lemma aul_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (upd h a v,c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h c Present); reflexivity.
Qed.

Lemma aur_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (upd h a v,c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h c Present); reflexivity.
Qed.

Lemma ag_csl_nd_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (upd h a v,c)}, {w} |= AG φ )>)).
Proof.
  intros Present.
  rewrite (interp_nd_source_write_present n ts i a v K h c Present); reflexivity.
Qed.

Lemma anl_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (upd h a v,c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h c Present); reflexivity.
Qed.

Lemma anr_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (upd h a v,c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h c Present); reflexivity.
Qed.

Lemma aul_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (upd h a v,c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h c Present); reflexivity.
Qed.

Lemma aur_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a <> None ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (upd h a v,c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h c Present); reflexivity.
Qed.

Lemma ag_csl_rr_write n (ts : pool sE (S n)) (i : Fin.t (S n))
  a v (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  h a <> None ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CWrite a v) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (upd h a v,c)}, {w} |= AG φ )>)).
Proof.
  intros Present.
  rewrite (interp_rr_write_present n ts i a v K m h c Present); reflexivity.
Qed.

Lemma anl_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h c Pos Base Free First); reflexivity.
Qed.

Lemma anr_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h c Pos Base Free First); reflexivity.
Qed.

Lemma aul_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h c Pos Base Free First); reflexivity.
Qed.

Lemma aur_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h c Pos Base Free First); reflexivity.
Qed.

Lemma ag_csl_nd_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c)}, {w} |= AG φ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_nd_source_alloc_first n ts i size base K h c Pos Base Free First); reflexivity.
Qed.

Lemma anl_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h c Pos Base Free First); reflexivity.
Qed.

Lemma anr_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h c Pos Base Free First); reflexivity.
Qed.

Lemma aul_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h c Pos Base Free First); reflexivity.
Qed.

Lemma aur_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h c Pos Base Free First); reflexivity.
Qed.

Lemma ag_csl_rr_alloc n (ts : pool sE (S n)) (i : Fin.t (S n))
  size base (K : option nat -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  Nat.lt 0 size -> Nat.lt 0 base -> block_free h base size ->
  (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c)}, {w} |= AG φ )>)).
Proof.
  intros Pos Base Free First.
  rewrite (interp_rr_alloc_first n ts i size base K m h c Pos Base Free First); reflexivity.
Qed.

Lemma anl_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) (upd h a desired,c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h c Lookup); reflexivity.
Qed.

Lemma anr_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) (upd h a desired,c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h c Lookup); reflexivity.
Qed.

Lemma aul_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) (upd h a desired,c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h c Lookup); reflexivity.
Qed.

Lemma aur_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) (upd h a desired,c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h c Lookup); reflexivity.
Qed.

Lemma ag_csl_nd_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some true)) (Some i) (upd h a desired,c)
  else
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some false)) (Some i) (h,c)}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_nd_source_cas_value n ts i a expected desired current K h c Lookup); reflexivity.
Qed.

Lemma anl_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m (upd h a desired,c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h c Lookup); reflexivity.
Qed.

Lemma anr_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m (upd h a desired,c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h c Lookup); reflexivity.
Qed.

Lemma aul_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m (upd h a desired,c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h c Lookup); reflexivity.
Qed.

Lemma aur_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  h a = Some current ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m (upd h a desired,c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h c Lookup); reflexivity.
Qed.

Lemma ag_csl_rr_cas n (ts : pool sE (S n)) (i : Fin.t (S n))
  a expected desired current (K : option bool -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  h a = Some current ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CCAS a expected desired) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   (<( {if Nat.eqb current expected then
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some true)) (Some i) m (upd h a desired,c)
  else
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some false)) (Some i) m (h,c)}, {w} |= AG φ )>)).
Proof.
  intros Lookup.
  rewrite (interp_rr_cas_value n ts i a expected desired current K m h c Lookup); reflexivity.
Qed.

(** ** Source flow and pool structure *)

Lemma anl_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (h,c)); reflexivity.
Qed.

Lemma anr_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (h,c)); reflexivity.
Qed.

Lemma aul_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (h,c)); reflexivity.
Qed.

Lemma aur_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (h,c)); reflexivity.
Qed.

Lemma ag_csl_nd_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some x)) (Some i) (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_ret n ts i x K (h,c)); reflexivity.
Qed.

Lemma anl_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (h,c)); reflexivity.
Qed.

Lemma anr_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (h,c)); reflexivity.
Qed.

Lemma aul_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (h,c)); reflexivity.
Qed.

Lemma aur_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (h,c)); reflexivity.
Qed.

Lemma ag_csl_rr_ret {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (x : A) (K : option A -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CRet x) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some x)) (Some i) m (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_ret n ts i x K m (h,c)); reflexivity.
Qed.

Lemma anl_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (h,c)); reflexivity.
Qed.

Lemma anr_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (h,c)); reflexivity.
Qed.

Lemma aul_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (h,c)); reflexivity.
Qed.

Lemma aur_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (h,c)); reflexivity.
Qed.

Lemma ag_csl_nd_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_bind n ts i p next K (h,c)); reflexivity.
Qed.

Lemma anl_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (h,c)); reflexivity.
Qed.

Lemma anr_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (h,c)); reflexivity.
Qed.

Lemma aul_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (h,c)); reflexivity.
Qed.

Lemma aur_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (h,c)); reflexivity.
Qed.

Lemma ag_csl_rr_bind {A B : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (p : CProg A) (next : A -> CProg B) (K : option B -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CBind p next) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow p >>= fun flow =>
      match flow with None => K None | Some x => denote_flow (next x) >>= K end)) (Some i) m (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_bind n ts i p next K m (h,c)); reflexivity.
Qed.

Lemma anl_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (h,c)); reflexivity.
Qed.

Lemma anr_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (h,c)); reflexivity.
Qed.

Lemma aul_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (h,c)); reflexivity.
Qed.

Lemma aur_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (h,c)); reflexivity.
Qed.

Lemma ag_csl_nd_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_until_none n ts i body K (h,c)); reflexivity.
Qed.

Lemma anl_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (h,c)); reflexivity.
Qed.

Lemma anr_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (h,c)); reflexivity.
Qed.

Lemma aul_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (h,c)); reflexivity.
Qed.

Lemma aur_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (h,c)); reflexivity.
Qed.

Lemma ag_csl_rr_until_none {A : Type} n (ts : pool sE (S n)) (i : Fin.t (S n))
  (body : CProg (option A)) (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CUntilNone body) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow body >>= until_tail body K)) (Some i) m (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_until_none n ts i body K m (h,c)); reflexivity.
Qed.

Lemma anl_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (h,c)); reflexivity.
Qed.

Lemma anr_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (h,c)); reflexivity.
Qed.

Lemma aul_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (h,c)); reflexivity.
Qed.

Lemma aur_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (h,c)); reflexivity.
Qed.

Lemma ag_csl_nd_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_nd sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_nd_source_fork n ts i child K (h,c)); reflexivity.
Qed.

Lemma anl_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (h,c)); reflexivity.
Qed.

Lemma anr_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (h,c)); reflexivity.
Qed.

Lemma aul_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (h,c)); reflexivity.
Qed.

Lemma aur_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (h,c)); reflexivity.
Qed.

Lemma ag_csl_rr_fork n (ts : pool sE (S n)) (i : Fin.t (S n))
  (child : CProg unit) (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CFork child) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S (S n))
    ((denote_flow child >>= fun _ => K None) :: (ts @ i := K (Some tt)))%vector (Some (Fin.FS i)) m (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite (interp_rr_fork n ts i child K m (h,c)); reflexivity.
Qed.

(** ** Observable emission and cooperative selection *)

Lemma anl_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {w} |= φ )> /\
    <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= ψ )>)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply anl_log_iff.
Qed.

Lemma anr_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {w} |= φ )> /\
    <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= ψ ]>)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply anr_log_iff.
Qed.

Lemma aul_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {w} |= ψ )> \/
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {w} |= φ )> /\
    <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= φ AU ψ )>))).
Proof.
  rewrite interp_nd_source_emit_log.
  apply aul_log_iff.
Qed.

Lemma aur_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {w} |= ψ ]> \/
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {w} |= φ )> /\
    <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= φ AU ψ ]>))).
Proof.
  rewrite interp_nd_source_emit_log.
  apply aur_log_iff.
Qed.

Lemma ag_csl_nd_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {w} |= φ )> /\
    <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some i) (h,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= AG φ )>)).
Proof.
  rewrite interp_nd_source_emit_log.
  apply ag_log_iff.
Qed.

Lemma anl_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= ψ )>)).
Proof.
  rewrite interp_rr_emit_log.
  apply anl_log_iff.
Qed.

Lemma anr_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {w} |= φ )> /\
    <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= ψ ]>)).
Proof.
  rewrite interp_rr_emit_log.
  apply anr_log_iff.
Qed.

Lemma aul_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {w} |= ψ )> \/
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= φ AU ψ )>))).
Proof.
  rewrite interp_rr_emit_log.
  apply aul_log_iff.
Qed.

Lemma aur_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {w} |= ψ ]> \/
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {w} |= φ )> /\
    <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= φ AU ψ ]>))).
Proof.
  rewrite interp_rr_emit_log.
  apply aur_log_iff.
Qed.

Lemma ag_csl_rr_emit n (ts : pool sE (S n)) (i : Fin.t (S n))
  tag value (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CEmit tag value) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   (<( {log (stamp (tag,value) c);;
    interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {w} |= φ )> /\
    <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some i) m (h,S c)}, {Obs (Log (stamp (tag,value) c)) tt} |= AG φ )>)).
Proof.
  rewrite interp_rr_emit_log.
  apply ag_log_iff.
Qed.

Lemma anl_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c)}, {w} |= ψ )>)).
Proof.
  rewrite interp_nd_source_yield.
  apply anl_csl_nd_select.
Qed.

Lemma anr_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c)}, {w} |= ψ ]>)).
Proof.
  rewrite interp_nd_source_yield.
  apply anr_csl_nd_select.
Qed.

Lemma aul_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c))}, {w} |= ψ )> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c)}, {w} |= φ AU ψ )>))).
Proof.
  rewrite interp_nd_source_yield.
  apply aul_csl_nd_select.
Qed.

Lemma aur_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c))}, {w} |= ψ ]> \/
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c)}, {w} |= φ AU ψ ]>))).
Proof.
  rewrite interp_nd_source_yield.
  apply aur_csl_nd_select.
Qed.

Lemma ag_csl_nd_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   (<( {Br n (fun j : Fin.t (S n) =>
    interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c))}, {w} |= φ )> /\
    forall j : Fin.t (S n),
      <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some tt)) (Some j) (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite interp_nd_source_yield.
  apply ag_csl_nd_select.
Qed.

Lemma anl_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (h,c)}, {w} |= φ AN ψ )>)).
Proof.
  rewrite interp_rr_yield.
  apply anl_csl_rr_select.
Qed.

Lemma anr_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (h,c)}, {w} |= φ AN ψ ]>)).
Proof.
  rewrite interp_rr_yield.
  apply anr_csl_rr_select.
Qed.

Lemma aul_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (h,c)}, {w} |= φ AU ψ )>)).
Proof.
  rewrite interp_rr_yield.
  apply aul_csl_rr_select.
Qed.

Lemma aur_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   (<[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (h,c)}, {w} |= φ AU ψ ]>)).
Proof.
  rewrite interp_rr_yield.
  apply aur_csl_rr_select.
Qed.

Lemma ag_csl_rr_yield n (ts : pool sE (S n)) (i : Fin.t (S n))
   (K : option unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CYield) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   (<( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some tt)) (Some (rr_pick n m)) (S m) (h,c)}, {w} |= AG φ )>)).
Proof.
  rewrite interp_rr_yield.
  apply ag_csl_rr_select.
Qed.

(** ** Finite heaps supply their constructive first-fit witness *)

Lemma anl_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c)}, {w} |= φ AN ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anl_csl_nd_alloc n ts i size base K h c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anl_csl_nd_alloc n ts i size base K h c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma anr_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c)}, {w} |= φ AN ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anr_csl_nd_alloc n ts i size base K h c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anr_csl_nd_alloc n ts i size base K h c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aul_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c)}, {w} |= φ AU ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aul_csl_nd_alloc n ts i size base K h c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aul_csl_nd_alloc n ts i size base K h c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aur_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c)}, {w} |= φ AU ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aur_csl_nd_alloc n ts i size base K h c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aur_csl_nd_alloc n ts i size base K h c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma ag_csl_nd_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_nd sh (S n)
    (ts @ i := K (Some base)) (Some i) (hunion (hblock base size) h,c)}, {w} |= AG φ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (ag_csl_nd_alloc n ts i size base K h c w φ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (ag_csl_nd_alloc n ts i size base K h c w φ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma anl_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c)}, {w} |= φ AN ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anl_csl_rr_alloc n ts i size base K m h c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anl_csl_rr_alloc n ts i size base K m h c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma anr_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c)}, {w} |= φ AN ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (anr_csl_rr_alloc n ts i size base K m h c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (anr_csl_rr_alloc n ts i size base K m h c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aul_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c)}, {w} |= φ AU ψ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aul_csl_rr_alloc n ts i size base K m h c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aul_csl_rr_alloc n ts i size base K m h c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma aur_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  heap_finite h -> Nat.lt 0 size ->
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <[ {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c)}, {w} |= φ AU ψ ]>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (aur_csl_rr_alloc n ts i size base K m h c w φ ψ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (aur_csl_rr_alloc n ts i size base K m h c w φ ψ Pos Base Free First)).
    apply Hall; assumption.
Qed.

Lemma ag_csl_rr_alloc_finite n (ts : pool sE (S n)) (i : Fin.t (S n))
  size (K : option nat -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  heap_finite h -> Nat.lt 0 size ->
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (denote_flow (CAlloc size) >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   forall base,
     Nat.lt 0 base -> block_free h base size ->
     (forall j, Nat.lt 0 j -> Nat.lt j base -> ~ block_free h j size) ->
     <( {interp_schedule_rr sh (S n)
    (ts @ i := K (Some base)) (Some i) m (hunion (hblock base size) h,c)}, {w} |= AG φ )>).
Proof.
  intros Finite Pos; split.
  - intros Hsource base Base Free First.
    apply (proj1 (ag_csl_rr_alloc n ts i size base K m h c w φ Pos Base Free First)); exact Hsource.
  - intro Hall.
    destruct (heap_handler_alloc_finite h size c Finite Pos)
      as (base & Base & Free & First & _).
    apply (proj2 (ag_csl_rr_alloc n ts i size base K m h c w φ Pos Base Free First)).
    apply Hall; assumption.
Qed.

(** ** Total single-cell free through the shared raw heap event *)

Lemma anl_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (hfree a h,c)}, {w} |= φ AN ψ )>).
Proof.
  rewrite (interp_nd_heap_free n ts i a K h c); reflexivity.
Qed.

Lemma anr_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) (h,c)}, {w} |= φ AN ψ ]> <->
   <[ {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (hfree a h,c)}, {w} |= φ AN ψ ]>).
Proof.
  rewrite (interp_nd_heap_free n ts i a K h c); reflexivity.
Qed.

Lemma aul_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (hfree a h,c)}, {w} |= φ AU ψ )>).
Proof.
  rewrite (interp_nd_heap_free n ts i a K h c); reflexivity.
Qed.

Lemma aur_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) (h,c)}, {w} |= φ AU ψ ]> <->
   <[ {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (hfree a h,c)}, {w} |= φ AU ψ ]>).
Proof.
  rewrite (interp_nd_heap_free n ts i a K h c); reflexivity.
Qed.

Lemma ag_csl_nd_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_nd sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) (h,c)}, {w} |= AG φ )> <->
   <( {interp_schedule_nd sh (S n)
    (ts @ i := K tt) (Some i) (hfree a h,c)}, {w} |= AG φ )>).
Proof.
  rewrite (interp_nd_heap_free n ts i a K h c); reflexivity.
Qed.

Lemma anl_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (hfree a h,c)}, {w} |= φ AN ψ )>).
Proof.
  rewrite (interp_rr_heap_free n ts i a K m h c); reflexivity.
Qed.

Lemma anr_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) m (h,c)}, {w} |= φ AN ψ ]> <->
   <[ {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (hfree a h,c)}, {w} |= φ AN ψ ]>).
Proof.
  rewrite (interp_rr_heap_free n ts i a K m h c); reflexivity.
Qed.

Lemma aul_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) m h c w
  (φ ψ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (hfree a h,c)}, {w} |= φ AU ψ )>).
Proof.
  rewrite (interp_rr_heap_free n ts i a K m h c); reflexivity.
Qed.

Lemma aur_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) (ψ : ticlrW (indexed (nat * nat)) (unit * SSig)) :
  (<[ {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) m (h,c)}, {w} |= φ AU ψ ]> <->
   <[ {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (hfree a h,c)}, {w} |= φ AU ψ ]>).
Proof.
  rewrite (interp_rr_heap_free n ts i a K m h c); reflexivity.
Qed.

Lemma ag_csl_rr_heap_free n (ts : pool sE (S n)) (i : Fin.t (S n))
  a (K : unit -> thread sE) m h c w
  (φ : ticllW (indexed (nat * nat))) :
  (<( {interp_schedule_rr sh (S n)
    (ts @ i := (heap_free (E:=CEff) a >>= K)) (Some i) m (h,c)}, {w} |= AG φ )> <->
   <( {interp_schedule_rr sh (S n)
    (ts @ i := K tt) (Some i) m (hfree a h,c)}, {w} |= AG φ )>).
Proof.
  rewrite (interp_rr_heap_free n ts i a K m h c); reflexivity.
Qed.

(** ** Source loops: actual observations sustain AG; guard-only divergence does not *)

Lemma run_nd_emit_loop_ag tag value h c w :
  not_done w ->
  <( {run_nd (CUntilNone (CBind (CEmit tag value)
    (fun _ => CRet (Some tt : option unit)))) h c}, {w} |= AG ⊤ )>.
Proof.
  revert c w; coinduction R CIH; intros c w Hw.
  unfold run_nd, denote.
  change (agcbt (entailsL (unit * SSig) <[ ⊤ ]>) R
    (interp_schedule_nd sh 1
      (([Ret tt] : pool sE 1) @ Fin.F1 :=
        (denote_flow
          (CUntilNone
            (CBind (CEmit tag value) (fun _ => CRet (Some tt : option unit))))
          >>= fun _ => Ret tt))
      (Some Fin.F1) (h,c)) w).
  rewrite interp_nd_source_until_none, interp_nd_source_bind,
    interp_nd_source_emit_log.
  unfold log, ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  split; [split; [exact I | exact Hw] |].
  split.
  - apply can_step_vis; [exact tt | exact Hw].
  - intros t' w' Htr.
    apply ktrans_vis in Htr as ([] & -> & <- & Hnd).
    rewrite interp_nd_source_ret.
    erewrite (interp_schedule_nd_guard sh) by reflexivity.
    cbn [Vector.replace].
    apply CIH.
    constructor.
Qed.

Lemma run_rr_emit_loop_ag tag value h c w :
  not_done w ->
  <( {run_rr (CUntilNone (CBind (CEmit tag value)
    (fun _ => CRet (Some tt : option unit)))) h c}, {w} |= AG ⊤ )>.
Proof.
  revert c w; coinduction R CIH; intros c w Hw.
  unfold run_rr, denote.
  change (agcbt (entailsL (unit * SSig) <[ ⊤ ]>) R
    (interp_schedule_rr sh 1
      (([Ret tt] : pool sE 1) @ Fin.F1 :=
        (denote_flow
          (CUntilNone
            (CBind (CEmit tag value) (fun _ => CRet (Some tt : option unit))))
          >>= fun _ => Ret tt))
      (Some Fin.F1) 0 (h,c)) w).
  rewrite interp_rr_until_none, interp_rr_bind, interp_rr_emit_log.
  unfold log, ICtree.trigger.
  rewrite bind_vis.
  setoid_rewrite bind_ret_l.
  split; [split; [exact I | exact Hw] |].
  split.
  - apply can_step_vis; [exact tt | exact Hw].
  - intros t' w' Htr.
    apply ktrans_vis in Htr as ([] & -> & <- & Hnd).
    rewrite interp_rr_ret.
    erewrite interp_schedule_rr_guard by reflexivity.
    cbn [Vector.replace].
    apply CIH.
    constructor.
Qed.

(** The silent loop starts focused, so the whole run is raw-equivalent to its
    own guard and hence to [stuck]; no scheduler tau is erased. *)
Lemma run_nd_silent_loop_no_ag h c w :
  ~ <( {run_nd (CUntilNone (CRet (Some tt : option unit))) h c}, {w} |= AG ⊤ )>.
Proof.
  set (p := CUntilNone (CRet (Some tt : option unit))).
  assert (Hraw : denote p ≅ Guard (denote p)).
  { unfold p, denote.
    etransitivity; [apply source_raw_until |].
    etransitivity; [apply source_raw_ret |].
    reflexivity. }
  assert (Hguard : run_nd p h c ≅ Guard (run_nd p h c)).
  { unfold run_nd.
    etransitivity.
    - apply ((interp_schedule_nd_equ sh) 1 _ [Guard (denote p)]).
      apply SBisim.cons_pool_equ; [exact Hraw | apply SBisim.pool_equ_refl].
    - unfold interp_schedule_nd.
      rewrite (SBisim.trans_schedule_focused_guard
        0 [Guard (denote p)] Fin.F1 (denote p) eq_refl).
      rewrite interp_erase_guard, Mod.interp_state_tau.
      reflexivity. }
  rewrite (equ_guard_stuck _ Hguard).
  apply ag_stuck.
Qed.

Lemma run_rr_silent_loop_no_ag h c w :
  ~ <( {run_rr (CUntilNone (CRet (Some tt : option unit))) h c}, {w} |= AG ⊤ )>.
Proof.
  set (p := CUntilNone (CRet (Some tt : option unit))).
  assert (Hraw : denote p ≅ Guard (denote p)).
  { unfold p, denote.
    etransitivity; [apply source_raw_until |].
    etransitivity; [apply source_raw_ret |].
    reflexivity. }
  assert (Hguard : run_rr p h c ≅ Guard (run_rr p h c)).
  { unfold run_rr.
    etransitivity.
    - apply (interp_schedule_rr_equ sh 1 _ [Guard (denote p)]).
      apply SBisim.cons_pool_equ; [exact Hraw | apply SBisim.pool_equ_refl].
    - unfold interp_schedule_rr.
      rewrite unfold_run_round_robin,
        (schedule_focused_guard 0 [Guard (denote p)] Fin.F1 (denote p) eq_refl).
      rewrite interp_erase_guard, Mod.interp_state_tau.
      reflexivity. }
  rewrite (equ_guard_stuck _ Hguard).
  apply ag_stuck.
Qed.
