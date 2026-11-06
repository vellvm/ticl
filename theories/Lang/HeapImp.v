From Stdlib Require Import
  Nat
  Strings.String
  QArith.QArith
  Arith.PeanoNat.


From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList
  Data.String.

From TICL Require Import
  CTree.Core
  CTree.Interp.State.Mod
  CTree.Events.Heap
  CTree.Events.State
  CTree.Events.Writer
  CTree.Logic.Trans
  Logic.Core
  CTree.Logic.AX
  CTree.Logic.AF
  CTree.Logic.EX
  CTree.Logic.EF
  CTree.Logic.Bind
  CTree.Logic.CanStep
  CTree.Logic.State
  Utils.Maps.

Generalizable All Variables.

Import CTree CTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.
Local Open Scope nat_scope.

(** * HeapImp: A simple imperative language with string-indexed variables and a heap *)
(** In this module we define a simple imperative language with string-indexed variables and a heap.
    The language is denoted in terms of a set of events [stateE], which include [get] and [put] events.
    The semantics of those events are given in terms of instrumentation handler [h_stateW], which is a state monad
    that also keeps track of the memory, which is a store (map from strings to natural numbers) and a heap.

    This is a simple deep-embedding of a simple imperative language, which allows us to prove structural versions of
    our sequential and loop lemmas from [State.v], over standard program constructs (assignments, conditionals, sequences, etc.).
*)
Module HeapImp.

  Import Ctx.
  (** A context is a map from strings to natural numbers *)
  Definition Store := alist string nat.
  Definition Heap := alist nat nat.

  Record Mem := { store: Store; heap: Heap }.

  Abbreviation memE := (stateE Mem).
  Opaque lookup.

  (** Convenience: update just the store, preserving the heap *)
  Definition update_store (x: string) (v: nat) (mem: Mem) : Mem :=
    {| store := add x v (store mem); heap := heap mem |}.

  (** Convenience: update just the heap, preserving the store *)
  Definition update_heap (a: nat) (v: nat) (mem: Mem) : Mem :=
    {| store := store mem; heap := add a v (heap mem) |}.

  (** Convenience: remove a heap cell, preserving the store *)
  Definition free_heap (a: nat) (mem: Mem) : Mem :=
    {| store := store mem; heap := remove a (heap mem) |}.
    
  (** * The syntax of HeapImp programs *)
  Inductive CExp :=
  | CConst (z: nat)
  | CAdd (x y: CExp)
  | CSub (x y: CExp)
  | CStoreRead (x: string)
  | CHeapAlloc (v: CExp) (* allocate N: nat elements *)
  | CHeapRead (a: CExp). (* dereference on address a *)

  Coercion CStoreRead: string >-> CExp.
  Coercion CConst: nat >-> CExp.
  
  Variant CComp :=
    | CEq  (l r: CExp)
    | CLe (l r: CExp)
    | CLt  (l r: CExp).
  
  Inductive CProg :=
  | CIf (c: CComp) (t: CProg) (e: CProg)
  | CWhile (c: CComp) (b: CProg) 
  | CSkip
  | CHeapWrite (a: CExp) (v: CExp)
  | CHeapFree (a: CExp)
  | CVarWrite (x: string) (v: CExp)
  | CSeq (l r: CProg).

  (** Helper: compute the next fresh heap address *)
  Fixpoint fresh_addr (h: alist nat nat) : nat :=
    match h with
    | nil => 0
    | cons (k, _) rest => Nat.max (S k) (fresh_addr rest)
    end.

  (** Helper: initialize n consecutive heap cells starting at base *)
  Fixpoint heap_init (base n: nat) (h: Heap) : Heap :=
    match n with
    | 0 => h
    | S n' => add base 0 (heap_init (S base) n' h)
    end.

  Section Denotation.
    (** [B]: the branch signature; HeapImp is deterministic so it is never constrained. *)
    Context {B: Type -> Type}.

    (** Lower shared heap commands to this backend's existing state effects. *)
    Definition h_heapimp : heapE ~> ctree memE B :=
      fun _ e =>
        match e in heapE X return ctree memE B X with
        | HRead a =>
            m <- get ;;
            match lookup a (heap m) with
            | Some v => Ret v
            | None => Stuck
            end
        | HWrite a v =>
            m <- get ;;
            put (update_heap a v m)
        | HAlloc n =>
            m <- get ;;
            let base := fresh_addr (heap m) in
            put {| store := store m; heap := heap_init base n (heap m) |} ;;
            Ret base
        | HFree a =>
            m <- get ;;
            put (free_heap a m)
        | HCAS a expected desired =>
            m <- get ;;
            match lookup a (heap m) with
            | None => Stuck
            | Some current =>
                if Nat.eqb current expected
                then put (update_heap a desired m) ;; Ret true
                else Ret false
            end
        end.

    (** Handler equations.  Zero allocation and absent frees still log the
        state; a matching CAS logs even when the value is unchanged, while a
        mismatching CAS returns without logging. *)
    Lemma instr_heapimp_alloc_zero (m : Mem) :
      instr_stateE (h_heapimp _ (HAlloc 0)) m ~
        (log m;; Ret (m, fresh_addr (heap m)) : ctreeW Mem B (Mem * nat)).
    Proof.
      destruct m as [s h].
      unfold h_heapimp, instr_stateE.
      rewrite interp_state_bind, interp_state_get, bind_ret_l.
      cbn [heap_init heap store fst snd].
      rewrite interp_state_bind, interp_state_put, bind_bind.
      setoid_rewrite bind_ret_l.
      setoid_rewrite interp_state_ret; reflexivity.
    Qed.

    Lemma instr_heapimp_free a (m : Mem) :
      instr_stateE (h_heapimp _ (HFree a)) m ~
        (log (free_heap a m);; Ret (free_heap a m, tt) : ctreeW Mem B (Mem * unit)).
    Proof.
      unfold h_heapimp, instr_stateE.
      rewrite interp_state_bind, interp_state_get, bind_ret_l.
      apply interp_state_put.
    Qed.

    Lemma instr_heapimp_write a v (m : Mem) :
      instr_stateE (h_heapimp _ (HWrite a v)) m ~
        (log (update_heap a v m);; Ret (update_heap a v m, tt) : ctreeW Mem B (Mem * unit)).
    Proof.
      unfold h_heapimp, instr_stateE.
      rewrite interp_state_bind, interp_state_get, bind_ret_l.
      apply interp_state_put.
    Qed.

    Lemma instr_heapimp_cas_success a expected desired (m : Mem) :
      lookup a (heap m) = Some expected ->
      instr_stateE (h_heapimp _ (HCAS a expected desired)) m ~
        (log (update_heap a desired m);; Ret (update_heap a desired m, true) : ctreeW Mem B (Mem * bool)).
    Proof.
      intros Lookup.
      unfold h_heapimp, instr_stateE.
      rewrite interp_state_bind, interp_state_get, bind_ret_l; cbn [fst snd].
      rewrite Lookup, Nat.eqb_refl.
      rewrite interp_state_bind, interp_state_put, bind_bind.
      setoid_rewrite bind_ret_l.
      setoid_rewrite interp_state_ret; reflexivity.
    Qed.

    Lemma instr_heapimp_cas_failure a actual expected desired (m : Mem) :
      lookup a (heap m) = Some actual -> actual <> expected ->
      instr_stateE (h_heapimp _ (HCAS a expected desired)) m ~ (Ret (m, false) : ctreeW Mem B (Mem * bool)).
    Proof.
      intros Lookup Hne.
      unfold h_heapimp, instr_stateE.
      rewrite interp_state_bind, interp_state_get, bind_ret_l; cbn [fst snd].
      apply Nat.eqb_neq in Hne.
      rewrite Lookup, Hne.
      rewrite interp_state_ret; reflexivity.
    Qed.

    (** Denotation of expressions to [ctree] *)
    Fixpoint cdenote_exp(e: CExp): ctree memE B nat :=
      match e with
      | CStoreRead v => m <- get ;;
                 match lookup v (store m) with
                 | Some x => Ret x
                 | None => Stuck
                 end
      | CConst z => Ret z
      | CAdd a b =>
          x <- cdenote_exp a ;;
          y <- cdenote_exp b ;;
          Ret (x + y)
      | CSub a b =>
          x <- cdenote_exp a ;;
          y <- cdenote_exp b ;;
          Ret (x - y)
      | CHeapAlloc sz =>
          n <- cdenote_exp sz ;;
          h_heapimp _ (HAlloc n)
      | CHeapRead a =>
          addr <- cdenote_exp a ;;
          h_heapimp _ (HRead addr)
      end.

    (** Denotation of boolean comparison expressions to [ctree] *)
    Definition cdenote_comp(c: CComp): ctree memE B bool :=
      match c with
      | CEq a b =>
          x <- cdenote_exp a ;;
          y <- cdenote_exp b ;;
          Ret (x =? y)
      | CLe a b =>
          x <- cdenote_exp a ;;
          y <- cdenote_exp b ;;
          Ret (x <=? y)
      | CLt a b =>
          x <- cdenote_exp a ;;
          y <- cdenote_exp b ;;
          Ret (x <? y)
      end.

    (** Denotation of programs to [ctree] *)
    Fixpoint cdenote_prog (s: CProg): ctree memE B unit :=
      match s with
      | CVarWrite x e =>
          v <- cdenote_exp e;;
          m <- get ;;
          put {| store := add x v (store m); heap := heap m |}
      | CHeapWrite a v =>
          addr <- cdenote_exp a ;;
          val <- cdenote_exp v ;;
          h_heapimp _ (HWrite addr val)
      | CHeapFree a =>
          addr <- cdenote_exp a ;;
          h_heapimp _ (HFree addr)
      | CIf c t e =>
          bv <- cdenote_comp c ;;
          if bv then
            cdenote_prog t
          else
            cdenote_prog e
      | CWhile c b =>       
          CTree.iter
            (fun _ =>
               cv <- cdenote_comp c ;;
               if cv then
                 bv <- cdenote_prog b ;;
                 continue
               else
                 break) tt
      | CSkip => Ret tt        
      | CSeq l r =>
          cdenote_prog l ;;
          cdenote_prog r
      end.

    (** Instrumentation of expressions, comparisons and programs *)
    Definition instr_exp(e: CExp) (mem: Mem) : ctreeW Mem B (Mem * nat) :=
      instr_stateE (cdenote_exp e) mem.

    Definition instr_comp(c: CComp) (mem: Mem) : ctreeW Mem B (Mem * bool) :=
      instr_stateE (cdenote_comp c) mem.
      
    Definition instr_prog(p: CProg) (mem: Mem) : ctreeW Mem B (Mem * unit) :=
      instr_stateE (cdenote_prog p) mem.
  End Denotation.
  
  (** * Notations *)
  Declare Scope heapimp_scope.
  Local Open Scope heapimp_scope.
  Local Open Scope string_scope.

  (** Expression grammar *)
  Declare Custom Entry heapexp.
  Notation "'<e{' e '}>'" := e (at level 0, e custom heapexp at level 95) : heapimp_scope.
  Notation "( x )" := x (in custom heapexp, x at level 99) : heapimp_scope.
  Notation "{ x }" := x (in custom heapexp at level 0, x constr) : heapimp_scope.
  Notation "x" := x (in custom heapexp at level 0, x constr at level 0) : heapimp_scope.
  Notation "a + b" := (CAdd a b)
    (in custom heapexp at level 50, left associativity) : heapimp_scope.
  Notation "a - b" := (CSub a b)
    (in custom heapexp at level 50, left associativity) : heapimp_scope.
  Notation "'!' a" := (CHeapRead a)
    (in custom heapexp at level 1) : heapimp_scope.

  (** Comparison grammar *)
  Declare Custom Entry heapcomp.
  Notation "'<b{' c '}>'" := c (at level 0, c custom heapcomp at level 95) : heapimp_scope.
  Notation "( x )" := x (in custom heapcomp, x at level 99) : heapimp_scope.
  Notation "{ x }" := x (in custom heapcomp at level 0, x constr) : heapimp_scope.
  Notation "x" := x (in custom heapcomp at level 0, x constr at level 0) : heapimp_scope.
  Notation "a =? b" := (CEq a b)
    (in custom heapcomp at level 70, a custom heapexp, b custom heapexp, no associativity) : heapimp_scope.
  Notation "a >=? b" := (CLe b a)
    (in custom heapcomp at level 70, a custom heapexp, b custom heapexp, no associativity) : heapimp_scope.
  Notation "a >? b" := (CLt b a)
    (in custom heapcomp at level 70, a custom heapexp, b custom heapexp, no associativity) : heapimp_scope.
  Notation "a <=? b" := (CLe a b)
    (in custom heapcomp at level 70, a custom heapexp, b custom heapexp, no associativity) : heapimp_scope.
  Notation "a <? b" := (CLt a b)
    (in custom heapcomp at level 70, a custom heapexp, b custom heapexp, no associativity) : heapimp_scope.

  (** Program grammar *)
  Declare Custom Entry heapprog.
  Notation "'<{' p '}>'" := p (at level 0, p custom heapprog at level 95) : heapimp_scope.
  Notation "( x )" := x (in custom heapprog, x at level 99) : heapimp_scope.
  Notation "{ x }" := x (in custom heapprog at level 0, x constr) : heapimp_scope.
  Notation "x" := x (in custom heapprog at level 0, x constr at level 0) : heapimp_scope.

  Notation "x ':=' c" := (CVarWrite x c)
    (in custom heapprog at level 0, x constr at level 0,
      c custom heapexp at level 95, no associativity) : heapimp_scope.
  Notation "'!' a ':=' v" := (CHeapWrite a v)
    (in custom heapprog at level 0, a custom heapexp at level 0,
      v custom heapexp at level 95, no associativity) : heapimp_scope.

  Notation "'if' c 'then' t 'else' e" :=
    (CIf c t e) (in custom heapprog at level 89,
      c constr, t custom heapprog at level 99, e custom heapprog at level 99) : heapimp_scope.
  Notation "'if' c 'then' t 'done'" :=
    (CIf c t CSkip) (in custom heapprog at level 89,
      c constr, t custom heapprog at level 99) : heapimp_scope.
  Notation "'while' c 'do' b 'done'" :=
    (CWhile c b) (in custom heapprog at level 89,
      c constr, b custom heapprog at level 99) : heapimp_scope.
  Notation "'skip'" :=
    (CSkip) (in custom heapprog at level 0) : heapimp_scope.
  Notation "t1 ;;; t2" := (CSeq t1 t2)
    (in custom heapprog at level 90, right associativity) : heapimp_scope.

  (** Proposition grammar (Mem -> Prop) *)
  Declare Custom Entry heapprop.
  Notation "'<p{' p '}>'"
    := p (at level 0, p custom heapprop at level 95) : heapimp_scope.
  Notation "( x )" := x (in custom heapprop, x at level 99) : heapimp_scope.
  Notation "{ x }" := x (in custom heapprop at level 0, x constr) : heapimp_scope.
  Notation "x" := x (in custom heapprop at level 0, x constr at level 0) : heapimp_scope.

  Notation "x '=?' c" := (fun m : Mem => lookup x (store m) = Some c)
    (in custom heapprop at level 70,
      x constr at level 0, c constr at level 0, no associativity) : heapimp_scope.
  Notation "x '<?' c" := (fun m : Mem => assert1 x (store m) (fun v => v < c))
    (in custom heapprop at level 70,
      x constr at level 0, c constr at level 0, no associativity) : heapimp_scope.
  Notation "x '<=?' c" := (fun m : Mem => assert1 x (store m) (fun v => v <= c))
    (in custom heapprop at level 70,
      x constr at level 0, c constr at level 0, no associativity) : heapimp_scope.
  Notation "x '>?' c" := (fun m : Mem => assert1 x (store m) (fun v => v > c))
    (in custom heapprop at level 70,
      x constr at level 0, c constr at level 0, no associativity) : heapimp_scope.
  Notation "x '>=?' c" := (fun m : Mem => assert1 x (store m) (fun v => v >= c))
    (in custom heapprop at level 70,
      x constr at level 0, c constr at level 0, no associativity) : heapimp_scope.

  (** TICL observation: memory satisfies a heapprop *)
  Notation "'obs' p" :=
    (CNow (vis_with (fun Y (pat : writerE _ Y) =>
                       match pat in writerE _ Y return Y -> Prop with
                       | Log mem => fun 'tt => p mem
                       end)))
      (in custom ticl at level 75, p constr) : ticl_scope.

  Section Lemmas.
    Context {B: Type -> Type}.
    (** Fix the branch signature of the denotations for this section. *)
    Local Abbreviation instr_exp := (@instr_exp B).
    Local Abbreviation instr_comp := (@instr_comp B).
    Local Abbreviation instr_prog := (@instr_prog B).
    Local Abbreviation instr_stateE := (@instr_stateE Mem B).
    Local Abbreviation log := (@log Mem B).

    (** Utility lemmas *)
    Lemma var_eq{X}: forall (p: ctreeW Mem B X) c v m,
        lookup c (store m) = Some v ->      
        <( p, {Obs (Log m) tt} |=L obs <p{ c =? v }> )>.
    Proof.
      intros.
      apply ticl_vis; eauto with ticl. 
    Qed.

    Lemma var_ge{X}: forall (p: ctreeW Mem B X) c v v' m,
        v' >= v ->
        lookup c (store m) = Some v' ->
        <( p, {Obs (Log m) tt} |=L obs <p{ c >=? v }> )>.
    Proof.
      intros.
      apply ticl_vis; eauto with ticl.
      constructor.
      exists v'; intuition.
    Qed.

    Lemma var_le{X}: forall (p: ctreeW Mem B X) c v v' m,
        v' <= v ->
        lookup c (store m) = Some v' ->
        <( p, {Obs (Log m) tt} |=L obs <p{ c <=? v }> )>.
    Proof.
      intros.
      apply ticl_vis; eauto with ticl.
      constructor.
      exists v'; intuition.
    Qed.

    (** An interpreted [Ret] returns its value and the unchanged state in one step
        with a native pre-return postcondition. Generic in [E]/[h] so its universes
        stay flexible. *)
    Lemma axr_state_ret_eq{E Σ W X} (h: E ~> stateT Σ (ctreeW W B)): forall (x: X) σ (w: WorldW W),
        not_done w ->
        <( {interp_state h (Ret x: ctree E B X) σ}, w |=R ret= {(σ, x)} w )>.
    Proof.
      intros.
      rewrite interp_state_ret.
      apply ret_ret; eauto with ticl.
    Qed.

    (** Comparing [x] and [c] returns a boolean [b] in one step *)
    Lemma axr_ccomp_lt: forall x (c: string) b mem w (v: nat),
        lookup c (store mem) = Some v ->
        b = Nat.ltb x v ->
        not_done w ->
        <( {instr_comp <b{ x <? c }> mem}, {w} |=R ret= {(mem, b)} {w} )>.
    Proof.
      intros; subst b.
      Opaque Nat.ltb.
      unfold instr_comp, instr_stateE; cbn.
      repeat (rewrite interp_state_bind || rewrite interp_state_ret ||
              rewrite interp_state_get || rewrite bind_ret_l).
      cbn.
      rewrite H; cbn.
      repeat (rewrite interp_state_bind || rewrite interp_state_ret || rewrite bind_ret_l).
      apply ret_ret; eauto with ticl.
    Qed.
      
    (** Constant expressions are evaluated to the constant in one step *)
    Lemma axr_cexp_const: forall (v v': nat) mem mem' w w',
        v = v' ->
        mem = mem' ->
        w = w' ->
        not_done w ->
        <( {instr_exp v mem}, w |=R ret= {(mem', v')} w' )>.
    Proof.
      intros; subst.
      unfold instr_exp, instr_stateE; cbn.
      now apply axr_state_ret_eq.
    Qed.

    (** Adding [v1] to [c] returns [v2] in one step *)
    Lemma axr_cexp_add: forall (c: string) (v0 v1 v2: nat) mem mem' w w',
        lookup c (store mem) = Some v0  ->
        v2 = v0 + v1 ->
        mem = mem' ->
        w = w' ->
        not_done w ->
        <( {instr_exp <e{ c + v1 }> mem}, w |=R ret= {(mem', v2)} w' )>.
    Proof.
      intros; subst.
      unfold instr_exp, instr_stateE; cbn.
      repeat (rewrite interp_state_bind || rewrite interp_state_ret ||
              rewrite interp_state_get || rewrite bind_ret_l).
      cbn; rewrite H; cbn.
      repeat (rewrite interp_state_bind || rewrite interp_state_ret || rewrite bind_ret_l).
      apply ret_ret; eauto with ticl.
    Qed.

    (** Subtracting [v1] from [c] returns [v2] in one step *)
    Lemma axr_cexp_sub: forall (c: string) (v0 v1 v2: nat) mem mem' w w',
        lookup c (store mem) = Some v0  ->
        v2 = v0 - v1 ->
        mem = mem' ->
        w = w' ->
        not_done w ->
        <( {instr_exp <e{ c - v1 }> mem}, w |=R ret= {(mem', v2)} w' )>.
    Proof.
      intros; subst.
      unfold instr_exp, instr_stateE; cbn.
      repeat (rewrite interp_state_bind || rewrite interp_state_ret ||
              rewrite interp_state_get || rewrite bind_ret_l).
      cbn; rewrite H; cbn.
      repeat (rewrite interp_state_bind || rewrite interp_state_ret || rewrite bind_ret_l).
      apply ret_ret; eauto with ticl.
    Qed.
    
    (** * Variable assignment: structural temporal lemmas *)
    (** A variable write reaches an indexed endpoint after logging the new context. *)
    Lemma au_cprog_var_write {b : bool}: forall x a mem r w
        (φ : ticllW Mem) (ψ : ticl_at (writerE Mem) (Mem * unit) b),
        let mem' := update_store x r mem in
        entails (Mem * nat) true (CRet (fun y z => (mem, r) = y /\ w = z)) (instr_exp a mem) w ->
        entails unit false φ (log mem') w ->
        entails (Mem * unit) b ψ (Ret (mem', tt): ctreeW Mem B (Mem * unit)) (Obs (Log mem') tt) ->
        entails (Mem * unit) b (Cu Q_A φ ψ) (instr_prog <{ x := a }> mem) w.
    Proof.
      unfold instr_prog, instr_exp.
      intros; cbn.
      eapply (au_state_bind_r_eq _ _ (b:=b)).
      - cleft; eauto with ticl.
      - eapply (au_state_bind_r_eq _ _ (b:=b)).
        + apply ticl_not_done in H0 as Hd.
          cleft; apply axr_get; eauto with ticl.
        + apply (au_put _ (b:=b)); eauto with ticl.
    Qed.

    (** * Heap write: structural temporal lemmas *)
    (** A heap write reaches an indexed endpoint after logging the updated heap. *)
    Lemma au_cprog_heap_write {b : bool}: forall ae ve mem addr val w
        (φ : ticllW Mem) (ψ : ticl_at (writerE Mem) (Mem * unit) b),
        let mem' := update_heap addr val mem in
        entails (Mem * nat) true (CRet (fun y z => (mem, addr) = y /\ w = z)) (instr_exp ae mem) w ->
        entails (Mem * nat) true (CRet (fun y z => (mem, val) = y /\ w = z)) (instr_exp ve mem) w ->
        entails unit false φ (log mem') w ->
        entails (Mem * unit) b ψ (Ret (mem', tt): ctreeW Mem B (Mem * unit)) (Obs (Log mem') tt) ->
        entails (Mem * unit) b (Cu Q_A φ ψ) (instr_prog (CHeapWrite ae ve) mem) w.
    Proof.
      unfold instr_prog, instr_exp.
      intros; cbn.
      eapply (au_state_bind_r_eq _ _ (b:=b)).
      - cleft; eauto with ticl.
      - eapply (au_state_bind_r_eq _ _ (b:=b)).
        + cleft; eauto with ticl.
        + eapply (au_state_bind_r_eq _ _ (b:=b)).
          * apply ticl_not_done in H1 as Hd.
            cleft; apply axr_get; eauto with ticl.
          * apply (au_put _ (b:=b)); eauto with ticl.
    Qed.

    (** * Heap free: structural temporal lemmas *)
    (** A heap free reaches an indexed endpoint after logging the updated heap. *)
    Lemma au_cprog_heap_free {b : bool}: forall ae mem addr w
        (φ : ticllW Mem) (ψ : ticl_at (writerE Mem) (Mem * unit) b),
        let mem' := free_heap addr mem in
        entails (Mem * nat) true (CRet (fun y z => (mem, addr) = y /\ w = z)) (instr_exp ae mem) w ->
        entails unit false φ (log mem') w ->
        entails (Mem * unit) b ψ (Ret (mem', tt): ctreeW Mem B (Mem * unit)) (Obs (Log mem') tt) ->
        entails (Mem * unit) b (Cu Q_A φ ψ) (instr_prog (CHeapFree ae) mem) w.
    Proof.
      unfold instr_prog, instr_exp.
      intros; cbn.
      eapply (au_state_bind_r_eq _ _ (b:=b)).
      - cleft; eauto with ticl.
      - eapply (au_state_bind_r_eq _ _ (b:=b)).
        + apply ticl_not_done in H0 as Hd.
          cleft; apply axr_get; eauto with ticl.
        + apply (au_put _ (b:=b)); eauto with ticl.
    Qed.
    
    (** * Sequence: structural temporal lemmas *)
    (** Sequential composition  [a ;;; b] lemmas *)
    Lemma anr_cprog_seq: forall a b mem mem' w w' (φ : ticlrW Mem (Mem * unit)) (ψ : ticllW Mem),
        <( {instr_prog a mem}, w |=R ret= {(mem', tt)} w' )> ->
        <( {instr_prog b mem'}, w' |=R ψ AN φ )> ->
        <( {instr_prog <{ a ;;; b }> mem}, w |=R ψ AN φ )>.
    Proof.
      unfold instr_prog. 
      intros; cbn.
      eapply (an_state_bind_r_eq _ _ (b:=true)); eauto.
    Qed.
    
    Lemma au_cprog_seq {suffix : bool}: forall a b mem mem' w w'
        (φ : ticllW Mem) (ψ : ticl_at (writerE Mem) (Mem * unit) suffix),
        entails (Mem * unit) true (Cu Q_A φ (CRet (fun y z => (mem', tt) = y /\ w' = z))) (instr_prog a mem) w ->
        entails (Mem * unit) suffix (Cu Q_A φ ψ) (instr_prog b mem') w' ->
        entails (Mem * unit) suffix (Cu Q_A φ ψ) (instr_prog <{ a ;;; b }> mem) w.
    Proof.
      unfold instr_prog.
      intros; cbn.
      eapply (au_state_bind_r_eq _ _ (b:=suffix)); eauto.
    Qed.
    
    Lemma ag_cprog_seq: forall a b mem mem' w w' φ,
        <( {instr_prog a mem}, w |=R φ AU ret= {(mem', tt)} w' )> ->
        <( {instr_prog b mem'}, w' |=L AG φ )> ->
        <( {instr_prog <{ a ;;; b }> mem}, w |=L AG φ )>.
    Proof.
      unfold instr_prog. 
      intros; cbn.
      eapply ag_state_bind_r_eq; eauto.
    Qed.

    (** * Conditional: structural temporal lemmas *)
    (** If-then-else [if c then t else f] lemmas *)
    Lemma au_cprog_ite {suffix : bool}: forall c mem w
        (φ : ticllW Mem) (ψ : ticl_at (writerE Mem) (Mem * unit) suffix) (b: bool) t f,
        entails (Mem * bool) true (CRet (fun y z => (mem, b) = y /\ w = z)) (instr_comp c mem) w ->
        (if b then
           entails (Mem * unit) suffix (Cu Q_A φ ψ) (instr_prog t mem) w
         else
           entails (Mem * unit) suffix (Cu Q_A φ ψ) (instr_prog f mem) w) ->
        entails (Mem * unit) suffix (Cu Q_A φ ψ) (instr_prog <{ if c then t else f }> mem) w.
    Proof.
      unfold instr_prog, instr_comp. 
      intros; cbn.
      eapply (au_state_bind_r_eq _ _ (b:=suffix)).
      - cleft; eauto with ticl.
      - destruct b; eauto with ticl.
    Qed.

    (** * While loops *)
    (** Unroll one iteration of the while loop if [c] evaluates to [true] *)
    Lemma au_cprog_while_true {b : bool}: forall c t w w'
        (φ : ticllW Mem) (ψ : ticl_at (writerE Mem) (Mem * unit) b) mem mem',
        entails (Mem * bool) true (CRet (fun y z => (mem, true) = y /\ w = z)) (instr_comp c mem) w ->
        entails (Mem * unit) true (Cu Q_A φ (CRet (fun y z => (mem', tt) = y /\ w' = z))) (instr_prog t mem) w ->
        entails (Mem * unit) b (Cu Q_A φ ψ) (instr_prog <{ while c do t done }> mem') w' ->
        entails (Mem * unit) b (Cu Q_A φ ψ) (instr_prog <{ while c do t done }> mem) w.
    Proof.
      unfold instr_prog, instr_comp; cbn; intros.
      apply (au_state_iter_next_eq _ _ (b:=b)) with tt w' mem'; eauto with ticl.
      - eapply (au_state_bind_r_eq _ _ (b:=true)).
        + cleft; eauto with ticl.
        + cbn; apply ticl_not_done in H1.
          eapply (au_state_bind_r_eq _ _ (b:=true)); eauto with ticl.
          cleft; apply axr_state_ret_eq; eauto with ticl.
      - apply ticl_not_done in H1; eauto with ticl.
    Qed.

    (** The loop terminates if [c] evaluates to [false] *)
    Lemma au_cprog_while_false {b : bool}: forall c t w
        (φ : ticllW Mem) (ψ : ticl_at (writerE Mem) (Mem * unit) b) mem,
        entails (Mem * bool) true (CRet (fun y z => (mem, false) = y /\ w = z)) (instr_comp c mem) w ->
        entails (Mem * unit) b ψ (Ret (mem, tt): ctreeW Mem B (Mem * unit)) w ->
        entails (Mem * unit) b (Cu Q_A φ ψ) (instr_prog <{ while c do t done }> mem) w.
    Proof.
      unfold instr_prog, instr_comp; cbn; intros.
      unfold instr_stateE; rewrite interp_state_unfold_iter.
      eapply (u_bind_r_eq (b:=b) Q_A).
      - eapply (au_state_bind_r_eq _ _ (b:=true)).
        + cleft; eauto with ticl.
        + apply ticl_not_done in H0.
          cleft; apply axr_state_ret_eq; eauto with ticl.
      - cleft; eauto with ticl.
    Qed.

    (** Termination lemma for a while loop, lifts the [au_state_iter_prefix_nat] lemma from [State.v] 
        to the level of HeapImp programs. *)
    Theorem aul_cprog_while mem (t: CProg) Ri f c (φ ψ : ticllW Mem):
      Ri mem ->
      <( {instr_comp c mem}, {Obs (Log mem) tt} |=R ret={(mem, true)} {Obs (Log mem) tt} )> ->
      (forall mem,
          Ri mem ->        
          exists (b: bool), <( {instr_comp c mem}, {Obs (Log mem) tt} |=R ret={(mem, b)} {Obs (Log mem) tt} )> /\
            if b then
              <( {instr_prog t mem}, {Obs (Log mem) tt} |=L φ AU ψ )> \/ 
                <( {instr_prog t mem}, {Obs (Log mem) tt} |=R φ AU ret {fun '(mem', _) w' =>
                                              w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem} )>
            else
              <( {Ret (mem, inr unit tt): ctreeW Mem B (Mem * (unit + unit))}, {Obs (Log mem) tt} |=L ψ )>) ->
        <( {instr_prog <{ while c do t done }> mem}, {Obs (Log mem) tt} |=L φ AU ψ )>.
    Proof.
      unfold instr_prog, instr_comp.
      intros HR Hb H.
      eapply au_state_iter_prefix_nat with
        (Ri:=fun 'tt (mem : Mem) (w : WorldW Mem) =>
               w = Obs (Log mem) tt /\
               exists (b: bool),
                 entails (Mem * bool) true (CRet (fun y z => (mem, b) = y /\ w = z)) (instr_stateE (cdenote_comp c) mem) w /\
                   if b then
                     entails (Mem * unit) false (Cu Q_A φ ψ) (instr_stateE (cdenote_prog t) mem) w \/
                       entails (Mem * unit) true
                         (Cu Q_A φ (CRet (fun '(mem', _) w' =>
                           w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem)))
                         (instr_stateE (cdenote_prog t) mem) w
                   else
                     entails (Mem * (unit + unit)) false ψ (Ret (mem, inr unit tt): ctreeW Mem B (Mem * (unit + unit))) w)
        (f:= fun _ mem _ => f mem); eauto with ticl.
      - intros [] mem' w' _ (-> & b' & Hb' & HR').
        destruct b'.
        + (* true *)
          destruct HR'.
          * left.
            eapply (au_state_bind_r_eq _ _ (b:=false)); eauto with ticl.
            -- cleft; eauto with ticl.
            -- eapply ticll_state_bind_l; eauto with ticl.
          * right.
            eapply (au_state_bind_r_eq _ _ (b:=true)); eauto with ticl.
            -- cleft; eauto with ticl.
            -- eapply (au_state_bind_r _ _ (b:=true)) with (R:=fun _ mem'0 w' => w' = Obs (Log mem'0) tt /\ Ri mem'0 /\ f mem'0 < f mem'); eauto with ticl.
               intros [] mem_ w_ (-> & HR_ & Hf).
               destruct (H _ HR_) as (b_ & Hb_ & HR'_).
               apply (au_state_ret _ _ (b:=true)), ret_ret; eauto with ticl.
               exists tt; cbn; intuition (eauto with ticl).
        + (* false *)
          left.
          eapply (au_state_bind_r_eq _ _ (b:=false)); eauto with ticl.
          * cleft; eauto with ticl.
          * cbn.
            apply (au_state_ret _ _ (b:=false)); eauto with ticl.
    Qed.

    (** Termination lemma for a while loop (suffix version) lifts the [au_state_iter_nat] lemma from [State.v] 
        to the level of HeapImp programs. *)
    Theorem aur_cprog_while_termination mem (t: CProg) Ri f c
        (φ : ticllW Mem) (ψ : ticlrW Mem (Mem * unit)) b:
        Ri mem ->
        <( {instr_comp c mem}, {Obs (Log mem) tt} |=R ret={(mem, b)} {Obs (Log mem) tt} )> ->
        (forall mem,
            Ri mem ->
            exists (b: bool), <( {instr_comp c mem}, {Obs (Log mem) tt} |=R ret={(mem, b)} {Obs (Log mem) tt} )> /\
            if b then
              <( {instr_prog t mem}, {Obs (Log mem) tt} |=R φ AU ret {fun '(mem', _) w' => w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem} )>
            else
              <( {Ret (mem, tt): ctreeW Mem B (Mem * unit)}, {Obs (Log mem) tt} |=R ψ )>) ->
        <( {instr_prog <{ while c do t done }> mem}, {Obs (Log mem) tt} |=R φ AU ψ )>.
    Proof.
      unfold instr_prog, instr_comp; intros.
      eapply (au_state_iter_nat _ _ (b:=true)) with
        (Ri:=fun 'tt (mem : Mem) (w : WorldW Mem) =>
               w = Obs (Log mem) tt /\
               exists b : bool,
                 entails (Mem * bool) true (CRet (fun y z => (mem, b) = y /\ Obs (Log mem) tt = z)) (instr_stateE (cdenote_comp c) mem) (Obs (Log mem) tt) /\
                   (if b
                    then
                      entails (Mem * unit) true
                        (Cu Q_A φ (CRet (fun '(mem', _) w' =>
                          w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem)))
                        (instr_stateE (cdenote_prog t) mem) (Obs (Log mem) tt)
                    else entails (Mem * unit) true ψ (Ret (mem, tt): ctreeW Mem B (Mem * unit)) (Obs (Log mem) tt)))
        (f:= fun _ mem _ => f mem); eauto with ticl.
      - intros [] mem' w' Hd (-> & b' & Hb' & HR).
        eapply (au_state_bind_r_eq _ _ (b:=true)); eauto with ticl.
        + cleft; eauto with ticl.
        + destruct b'.
          * (* true *)
            eapply (au_state_bind_r _ _ (b:=true)) with (R:=fun _ mem'0 w' => w' = Obs (Log mem'0) tt /\ Ri mem'0 /\ f mem'0 < f mem'); eauto with ticl.
            intros [] mem_ w_ (-> & HR_ & Hf).
            destruct (H1 _ HR_) as (b_ & Hb_ & HR'_).
            apply (au_state_ret _ _ (b:=true)), ret_ret; cbn; intuition (eauto with ticl).
          * (* false *)
            apply (au_state_ret _ _ (b:=true)), ret_ret; intuition (eauto with ticl).
    Qed.

    (** Invariance lemma for an infinite while loop, lifts the [ag_state_iter] lemma from [State.v] 
        to the level of HeapImp programs. *)
    Lemma ag_cprog_while: forall c (t: CProg) (R : Mem -> Prop) mem (φ : ticllW Mem),
        R mem ->      
        (forall mem,
            R mem ->
            <( {instr_prog <{while c do t done }> mem}, {Obs (Log mem) tt} |=L φ )> /\          
            <( {instr_comp c mem}, {Obs (Log mem) tt} |=R ret={(mem, true)} {Obs (Log mem) tt} )>  /\            
            <( {instr_prog t mem}, {Obs (Log mem) tt} |=R AX (φ AU ret {fun '(mem', _) w' => w' = Obs (Log mem') tt /\ R mem'}) )>) ->
      <( {instr_prog <{ while c do t done }> mem}, {Obs (Log mem) tt} |=L AG φ )>.
    Proof.
      unfold instr_prog, instr_comp. 
      intros; subst.
      eapply ag_state_iter with (R:=fun 'tt (mem : Mem) (w : WorldW Mem) =>
                                      w = Obs (Log mem) tt /\
                                      entails (Mem * unit) false φ (instr_prog <{while c do t done }> mem) w /\
                                      entails (Mem * bool) true (CRet (fun y z => (mem, true) = y /\ w = z)) (instr_comp c mem) w /\
                                      entails (Mem * unit) true
                                        (Cx Q_A (CNow (fun _ => True))
                                          (Cu Q_A φ (CRet (fun '(mem', _) w' =>
                                            w' = Obs (Log mem') tt /\ R mem'))))
                                        (instr_prog t mem) w); eauto with ticl.
      - intros [] mem' w' Hd (-> & Ht & Hc & HR); intuition.
        rewrite interp_state_bind.
        eapply (ticl_bind_ret_eq (b:=true)); eauto with ticl.
        cbn; rewrite interp_state_bind.
        eapply (ax_au_bind_r (b:=true)); [exact HR |].
        intros [mem_ []] w'' (Hd'' & HR').
        destruct (H0 _ HR') as (? & ? & ?).
        apply (au_state_ret _ _ (b:=true)), ret_ret; eauto with ticl.
        exists tt; subst; cbn; intuition (eauto with ticl).
    Qed.
  End Lemmas.
  
End HeapImp.
