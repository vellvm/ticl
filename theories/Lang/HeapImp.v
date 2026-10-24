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

  Notation memE := (stateE Mem).
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
      apply sbisim_clo_bind_eq; [reflexivity | intros []].
      rewrite bind_ret_l, interp_state_ret; reflexivity.
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
      apply sbisim_clo_bind_eq; [reflexivity | intros []].
      rewrite bind_ret_l, interp_state_ret; reflexivity.
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
      (in custom ticll at level 75, p constr) : ticl_scope.

  Section Lemmas.
    Context {B: Type -> Type}.
    (** Fix the branch signature of the denotations for this section. *)
    Local Notation instr_exp := (@instr_exp B).
    Local Notation instr_comp := (@instr_comp B).
    Local Notation instr_prog := (@instr_prog B).
    Local Notation instr_stateE := (@instr_stateE Mem B).
    Local Notation log := (@log Mem B).

    (** Utility lemmas *)
    Lemma var_eq{X}: forall (p: ctreeW Mem B X) c v m,
        lookup c (store m) = Some v ->      
        <( p, {Obs (Log m) tt} |= obs <p{ c =? v }> )>.
    Proof with eauto with ticl.
      intros.
      apply ticll_vis... 
    Qed.

    Lemma var_ge{X}: forall (p: ctreeW Mem B X) c v v' m,
        v' >= v ->
        lookup c (store m) = Some v' ->
        <( p, {Obs (Log m) tt} |= obs <p{ c >=? v }> )>.
    Proof with eauto with ticl.
      intros.
      apply ticll_vis...
      constructor.
      exists v'; intuition.
    Qed.

    Lemma var_le{X}: forall (p: ctreeW Mem B X) c v v' m,
        v' <= v ->
        lookup c (store m) = Some v' ->
        <( p, {Obs (Log m) tt} |= obs <p{ c <=? v }> )>.
    Proof with eauto with ticl.
      intros.
      apply ticll_vis...
      constructor.
      exists v'; intuition.
    Qed.

    (** An interpreted [Ret] returns its value and the unchanged state in one step
        (the [done=] sibling of [axr_state_ret]). Generic in [E]/[h] so its universes
        stay flexible. *)
    Lemma axr_state_ret_eq{E Σ W X} (h: E ~> stateT Σ (ctreeW W B)): forall (x: X) σ (w: WorldW W),
        not_done w ->
        <[ {interp_state h (Ret x: ctree E B X) σ}, w |= AX done= {(σ, x)} w ]>.
    Proof with eauto with ticl.
      intros.
      rewrite interp_state_ret.
      apply axr_ret...
    Qed.

    (** Comparing [x] and [c] returns a boolean [b] in one step *)
    Lemma axr_ccomp_lt: forall x (c: string) b mem w (v: nat),
        lookup c (store mem) = Some v ->
        b = Nat.ltb x v ->
        not_done w ->
        <[ {instr_comp <b{ x <? c }> mem}, {w} |= AX (done= {(mem, b)} {w}) ]>.
    Proof with eauto with ticl.
      intros.
      Opaque Nat.ltb.
      unfold instr_comp, instr_stateE; cbn.
      eapply anr_state_bind_r_eq...
      - apply axr_state_ret_eq...
      - eapply anr_state_bind_r_eq...
        + eapply anr_state_bind_r_eq...
          * unfold instr_stateE; rewrite interp_state_get.
            apply axr_ret...
          * setoid_rewrite H.
            apply axr_state_ret_eq...
        + rewrite H0.
          apply axr_state_ret_eq...
    Qed.
      
    (** Constant expressions are evaluated to the constant in one step *)
    Lemma axr_cexp_const: forall (v v': nat) mem mem' w w',
        v = v' ->
        mem = mem' ->
        w = w' ->
        not_done w ->
        <[ {instr_exp v mem}, w |= AX done= {(mem', v')} w' ]>.
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
        <[ {instr_exp <e{ c + v1 }> mem}, w |= AX done= {(mem', v2)} w' ]>.
    Proof with eauto with ticl.
      intros; subst.
      unfold instr_exp, instr_stateE; cbn.
      rewrite bind_bind.
      eapply anr_state_bind_r_eq.
      - unfold instr_stateE; rewrite interp_state_get.
        apply axr_ret...
      - setoid_rewrite H.
        rewrite ?bind_ret_l.
        apply axr_state_ret_eq...
    Qed.

    (** Subtracting [v1] from [c] returns [v2] in one step *)
    Lemma axr_cexp_sub: forall (c: string) (v0 v1 v2: nat) mem mem' w w',
        lookup c (store mem) = Some v0  ->
        v2 = v0 - v1 ->
        mem = mem' ->
        w = w' ->
        not_done w ->
        <[ {instr_exp <e{ c - v1 }> mem}, w |= AX done= {(mem', v2)} w' ]>.
    Proof with eauto with ticl.
      intros; subst.
      unfold instr_exp, instr_stateE; cbn.
      rewrite bind_bind.
      eapply anr_state_bind_r_eq.
      - unfold instr_stateE; rewrite interp_state_get.
        apply axr_ret...
      - setoid_rewrite H.
        rewrite ?bind_ret_l.
        apply axr_state_ret_eq...
    Qed.
    
    (** * Variable assignment: structural temporal lemmas *)
    (** A variable write [x := a] eventually (suffix) [AU] returns, where [r] is the evaluation of [a]. 
        Assignments are instrumented with a [log] event, which records the new context.
    *)
    Lemma aur_cprog_var_write: forall x a mem r w R ψ,
        let mem' := update_store x r mem in
        <[ {instr_exp a mem}, w |= AX done= {(mem, r)} w ]> ->
        <( {log mem'}, w |= ψ )> ->
        R (mem', tt) (Obs (Log mem') tt) ->
        <[ {instr_prog <{ x := a }> mem}, w |= ψ AU ret R ]>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_exp.
      intros; cbn.
      eapply aur_state_bind_r_eq.
      - cleft...
      - eapply aur_state_bind_r_eq.
        + cleft; apply anr_get...
          csplit; apply ticll_not_done in H0...
        + apply aur_put...
    Qed.

    (** A variable write [x := a] eventually (prefix) [AU] returns, where [r] is the evaluation of [a]. 
        Assignments are instrumented with a [log] event, which records the new context.
    *)
    Lemma aul_cprog_var_write: forall x a mem r w ψ φ,
        let mem' := update_store x r mem in
        <[ {instr_exp a mem}, w |= AX done= {(mem, r)} w ]> ->
        <( {log mem'}, w |= ψ )> ->
        <( {Ret (mem', tt): ctreeW Mem B (Mem * unit)}, {Obs (Log mem') tt} |= φ )> ->
        <( {instr_prog <{ x := a }> mem}, w |= ψ AU φ )>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_exp.
      intros; cbn.
      eapply aul_state_bind_r_eq.
      - cleft...
      - eapply aul_state_bind_r_eq.
        + cleft; apply anr_get...
          csplit; apply ticll_not_done in H0...
        + apply aul_put...
    Qed.

    (** * Heap write: structural temporal lemmas *)
    (** A heap write [*a := v] eventually (suffix) [AU] returns. *)
    Lemma aur_cprog_heap_write: forall ae ve mem addr val w R ψ,
        let mem' := update_heap addr val mem in
        <[ {instr_exp ae mem}, w |= AX done= {(mem, addr)} w ]> ->
        <[ {instr_exp ve mem}, w |= AX done= {(mem, val)} w ]> ->
        <( {log mem'}, w |= ψ )> ->
        R (mem', tt) (Obs (Log mem') tt) ->
        <[ {instr_prog (CHeapWrite ae ve) mem}, w |= ψ AU ret R ]>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_exp.
      intros; cbn.
      eapply aur_state_bind_r_eq.
      - cleft...
      - eapply aur_state_bind_r_eq.
        + cleft...
        + eapply aur_state_bind_r_eq.
          * cleft; apply anr_get...
            csplit; apply ticll_not_done in H1...
          * apply aur_put...
    Qed.

    (** A heap write [*a := v] eventually (prefix) [AU] returns. *)
    Lemma aul_cprog_heap_write: forall ae ve mem addr val w ψ φ,
        let mem' := update_heap addr val mem in
        <[ {instr_exp ae mem}, w |= AX done= {(mem, addr)} w ]> ->
        <[ {instr_exp ve mem}, w |= AX done= {(mem, val)} w ]> ->
        <( {log mem'}, w |= ψ )> ->
        <( {Ret (mem', tt): ctreeW Mem B (Mem * unit)}, {Obs (Log mem') tt} |= φ )> ->
        <( {instr_prog (CHeapWrite ae ve) mem}, w |= ψ AU φ )>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_exp.
      intros; cbn.
      eapply aul_state_bind_r_eq.
      - cleft...
      - eapply aul_state_bind_r_eq.
        + cleft...
        + eapply aul_state_bind_r_eq.
          * cleft; apply anr_get...
            csplit; apply ticll_not_done in H1...
          * apply aul_put...
    Qed.

    (** * Heap free: structural temporal lemmas *)
    (** A heap free eventually (suffix) [AU] returns. *)
    Lemma aur_cprog_heap_free: forall ae mem addr w R ψ,
        let mem' := free_heap addr mem in
        <[ {instr_exp ae mem}, w |= AX done= {(mem, addr)} w ]> ->
        <( {log mem'}, w |= ψ )> ->
        R (mem', tt) (Obs (Log mem') tt) ->
        <[ {instr_prog (CHeapFree ae) mem}, w |= ψ AU ret R ]>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_exp.
      intros; cbn.
      eapply aur_state_bind_r_eq.
      - cleft...
      - eapply aur_state_bind_r_eq.
        + cleft; apply anr_get...
          csplit; apply ticll_not_done in H0...
        + apply aur_put...
    Qed.

    (** A heap free eventually (prefix) [AU] returns. *)
    Lemma aul_cprog_heap_free: forall ae mem addr w ψ φ,
        let mem' := free_heap addr mem in
        <[ {instr_exp ae mem}, w |= AX done= {(mem, addr)} w ]> ->
        <( {log mem'}, w |= ψ )> ->
        <( {Ret (mem', tt): ctreeW Mem B (Mem * unit)}, {Obs (Log mem') tt} |= φ )> ->
        <( {instr_prog (CHeapFree ae) mem}, w |= ψ AU φ )>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_exp.
      intros; cbn.
      eapply aul_state_bind_r_eq.
      - cleft...
      - eapply aul_state_bind_r_eq.
        + cleft; apply anr_get...
          csplit; apply ticll_not_done in H0...
        + apply aul_put...
    Qed.
    
    (** * Sequence: structural temporal lemmas *)
    (** Sequential composition  [a ;;; b] lemmas *)
    Lemma anr_cprog_seq: forall a b mem mem' w w' φ ψ,
        <[ {instr_prog a mem}, w |= ψ AN done= {(mem', tt)} w' ]> ->
        <[ {instr_prog b mem'}, w' |= ψ AN φ ]> ->
        <[ {instr_prog <{ a ;;; b }> mem}, w |= ψ AN φ ]>.
    Proof.
      unfold instr_prog. 
      intros; cbn.
      eapply anr_state_bind_r_eq; eauto.
    Qed.
    
    Lemma aur_cprog_seq: forall a b mem mem' w w' φ ψ,
        <[ {instr_prog a mem}, w |= φ AU AX done= {(mem', tt)} w' ]> ->
        <[ {instr_prog b mem'}, w' |= φ AU ψ ]> ->
        <[ {instr_prog <{ a ;;; b }> mem}, w |= φ AU ψ ]>.
    Proof.
      unfold instr_prog.
      intros; cbn.
      eapply aur_state_bind_r_eq; eauto.
    Qed.
    
    Lemma aul_cprog_seq: forall a b mem mem' w w' φ ψ,
        <[ {instr_prog a mem}, w |= φ AU AX done= {(mem', tt)} w' ]> ->
        <( {instr_prog b mem'}, w' |= φ AU ψ )> ->
        <( {instr_prog <{ a ;;; b }> mem}, w |= φ AU ψ )>.
    Proof.
      unfold instr_prog. 
      intros; cbn.
      eapply aul_state_bind_r_eq; eauto.
    Qed.
    
    Lemma ag_cprog_seq: forall a b mem mem' w w' φ,
        <[ {instr_prog a mem}, w |= φ AU AX done= {(mem', tt)} w' ]> ->
        <( {instr_prog b mem'}, w' |= AG φ )> ->
        <( {instr_prog <{ a ;;; b }> mem}, w |= AG φ )>.
    Proof.
      unfold instr_prog. 
      intros; cbn.
      eapply ag_state_bind_r_eq; eauto.
    Qed.

    (** * Conditional: structural temporal lemmas *)
    (** If-then-else [if c then t else f] lemmas *)
    Lemma aul_cprog_ite: forall c mem w φ ψ (b: bool) t f,
        <[ {instr_comp c mem}, w |= AX done= {(mem, b)} w ]> ->
        (if b then
           <( {instr_prog t mem}, w |= φ AU ψ )>
         else
           <( {instr_prog f mem}, w |= φ AU ψ )>) ->
        <( {instr_prog <{ if c then t else f }> mem}, w |= φ AU ψ )>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_comp. 
      intros; cbn.
      eapply aul_state_bind_r_eq.
      - cleft...
      - destruct b...
    Qed.

    Lemma aur_cprog_ite: forall c mem w φ ψ (b: bool) t f,
        <[ {instr_comp c mem}, w |= AX done= {(mem, b)} w ]> ->
        (if b then
           <[ {instr_prog t mem}, w |= φ AU ψ ]>
         else
           <[ {instr_prog f mem}, w |= φ AU ψ ]>) ->
        <[ {instr_prog <{ if c then t else f }> mem}, w |= φ AU ψ ]>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_comp. 
      intros; cbn.
      eapply aur_state_bind_r_eq.
      - cleft...
      - destruct b...
    Qed.

    (** * While loops *)
    (** Unroll one iteration of the while loop if [c] evaluates to [true] *)
    Lemma aul_cprog_while_true: forall c t w w' φ ψ mem mem',
        <[ {instr_comp c mem}, w |= AX done={(mem, true)} w ]> ->
        <[ {instr_prog t mem}, w |= φ AU AX done={(mem', tt)} w' ]> ->
        <( {instr_prog <{ while c do t done }> mem'}, w' |= φ AU ψ )> ->   
        <( {instr_prog <{ while c do t done }> mem}, w |= φ AU ψ )>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_comp; cbn; intros.
      apply aul_state_iter_next_eq with tt w' mem'...
      - eapply aur_state_bind_r_eq.
        + cleft...
        + cbn; apply ticll_not_done in H1.
          eapply aur_state_bind_r_eq...
          cleft; apply axr_state_ret_eq...
      - apply ticll_not_done in H1...
    Qed.

    (** The loop terminates if [c] evaluates to [false] *)
    Lemma aul_cprog_while_false: forall c t w φ ψ mem,
        <[ {instr_comp c mem}, w |= AX done={(mem, false)} w ]> ->
        <( {Ret (mem, tt): ctreeW Mem B (Mem * unit)}, w |= ψ )> ->
        <( {instr_prog <{ while c do t done }> mem}, w |= φ AU ψ )>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_comp; cbn; intros.
      unfold instr_stateE; rewrite interp_state_unfold_iter.
      eapply aul_bind_r_eq.
      - eapply aur_state_bind_r_eq.
        + cleft...
        + apply ticll_not_done in H0.
          cleft; apply axr_state_ret_eq...
      - cleft...
    Qed.

    (** Unroll one iteration of the while loop if [c] evaluates to [true], suffix [AU] version *)
    Lemma aur_cprog_while_true: forall c t w w' φ ψ mem mem',
        <[ {instr_comp c mem}, w |= AX done={(mem, true)} w ]> ->
        <[ {instr_prog t mem}, w |= φ AU AX done={(mem', tt)} w' ]> ->
        <[ {instr_prog <{ while c do t done }> mem'}, w' |= φ AU AX ψ ]> ->   
        <[ {instr_prog <{ while c do t done }> mem}, w |= φ AU AX ψ ]>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_comp; cbn; intros.
      apply aur_state_iter_next_eq with tt w' mem'...
      - eapply aur_state_bind_r_eq.
        + cleft...
        + cbn. 
          eapply aur_state_bind_r_eq...
          cleft; apply axr_state_ret_eq.
          now apply aur_not_done in H1.
      - now apply aur_not_done in H1. 
    Qed.

    (** The loop terminates if [c] evaluates to [false], suffix [AU] version *)
    Lemma aur_cprog_while_false: forall c t w φ ψ mem,
        <[ {instr_comp c mem}, w |= AX done={(mem, false)} w ]> ->
        <[ {Ret (mem, tt): ctreeW Mem B (Mem * unit)}, w |= AX ψ ]> ->
        <[ {instr_prog <{ while c do t done }> mem}, w |= φ AU AX ψ ]>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_comp; cbn; intros.
      unfold instr_stateE; rewrite interp_state_unfold_iter.
      eapply aur_bind_r_eq.
      - eapply aur_state_bind_r_eq.
        + cleft...
        + cleft; apply axr_state_ret_eq.
          cdestruct H.
          apply can_step_not_done in Hs...
      - cleft...
    Qed.
    
    (** Termination lemma for a while loop, lifts the [aul_state_iter_nat] lemma from [State.v] 
        to the level of HeapImp programs. *)
    Theorem aul_cprog_while mem (t: CProg) Ri f c φ ψ:
      Ri mem ->
      <[ {instr_comp c mem}, {Obs (Log mem) tt} |= AX done={(mem, true)} {Obs (Log mem) tt} ]> ->
      (forall mem,
          Ri mem ->        
          exists (b: bool), <[ {instr_comp c mem}, {Obs (Log mem) tt} |= AX done={(mem, b)} {Obs (Log mem) tt} ]> /\
            if b then
              <( {instr_prog t mem}, {Obs (Log mem) tt} |= φ AU ψ )> \/ 
                <[ {instr_prog t mem}, {Obs (Log mem) tt} |= φ AU ret {fun '(mem', _) w' =>
                                              w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem} ]>
            else
              <( {Ret (mem, inr unit tt): ctreeW Mem B (Mem * (unit + unit))}, {Obs (Log mem) tt} |= ψ )>) ->
        <( {instr_prog <{ while c do t done }> mem}, {Obs (Log mem) tt} |= φ AU ψ )>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_comp.
      intros HR Hb H.
      eapply aul_state_iter_nat with
        (Ri:=fun 'tt mem w =>
               w = Obs (Log mem) tt /\
               exists (b: bool),
                 <[ {instr_stateE (cdenote_comp c) mem}, w |= AX done={(mem, b)} w ]> /\
                   if b then
                     <( {instr_stateE (cdenote_prog t) mem}, w |= φ AU ψ )> \/ 
                       <[ {instr_stateE (cdenote_prog t) mem}, w |= φ AU ret {fun '(mem', _) w' =>
                                                                                    w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem} ]>
                   else
                     <( {Ret (mem, inr unit tt): ctreeW Mem B (Mem * (unit + unit))}, w |= ψ )>)
        (f:= fun _ mem _ => f mem)...
      - intros [] mem' w' _ (-> & b' & Hb' & HR').
        destruct b'.
        + (* true *)
          destruct HR'.
          * left.
            eapply aul_state_bind_r_eq...
            -- cleft...
            -- eapply ticll_state_bind_l...
          * right.
            eapply aur_state_bind_r_eq...
            -- cleft...
            -- eapply aur_state_bind_r with (R:=fun _ mem'0 w' => w' = Obs (Log mem'0) tt /\ Ri mem'0 /\ f mem'0 < f mem')...
               intros [] mem_ w_ (-> & HR_ & Hf).
               destruct (H _ HR_) as (b_ & Hb_ & HR'_).
               apply aur_state_ret...
               exists tt; cbn; intuition (eauto with ticl).
        + (* false *)
          left.
          eapply aul_state_bind_r_eq...
          * cleft...
          * cbn.
            apply aul_state_ret...
    Qed.

    (** Termination lemma for a while loop (suffix version) lifts the [aur_state_iter_nat] lemma from [State.v] 
        to the level of HeapImp programs. *)
    Theorem aur_cprog_while_termination mem (t: CProg) Ri f c φ ψ b:    
        Ri mem ->
        <[ {instr_comp c mem}, {Obs (Log mem) tt} |= AX done={(mem, b)} {Obs (Log mem) tt} ]> ->
        (forall mem,
            Ri mem ->
            exists (b: bool), <[ {instr_comp c mem}, {Obs (Log mem) tt} |= AX done={(mem, b)} {Obs (Log mem) tt} ]> /\
            if b then
              <[ {instr_prog t mem}, {Obs (Log mem) tt} |= φ AU ret {fun '(mem', _) w' => w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem} ]>
            else
              <[ {Ret (mem, tt): ctreeW Mem B (Mem * unit)}, {Obs (Log mem) tt} |= φ AN ψ ]>) ->
        <[ {instr_prog <{ while c do t done }> mem}, {Obs (Log mem) tt} |= φ AU ψ ]>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_comp; intros.
      eapply aur_state_iter_nat with
        (Ri:=fun 'tt mem w =>
               w = Obs (Log mem) tt /\
               exists b : bool,
                 <[ {instr_stateE (cdenote_comp c) mem}, {Obs (Log mem) tt} |= AX (done= {(mem, b)} {Obs (Log mem) tt}) ]> /\
                   (if b
                    then
                      <[ {instr_stateE (cdenote_prog t) mem}, {Obs (Log mem) tt} |= {φ} AU ret {fun '(mem', _) (w' : WorldW Mem) =>
                                                                         w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem} ]>
                    else <[ {Ret (mem, tt): ctreeW Mem B (Mem * unit)}, {Obs (Log mem) tt} |= {φ} AN {ψ} ]>))
        (f:= fun _ mem _ => f mem)...
      - intros [] mem' w' Hd (-> & b' & Hb' & HR).
        eapply aur_state_bind_r_eq...
        + cleft...
        + destruct b'.
          * (* true *)
            eapply aur_state_bind_r with (R:=fun _ mem'0 w' => w' = Obs (Log mem'0) tt /\ Ri mem'0 /\ f mem'0 < f mem')...
            intros [] mem_ w_ (-> & HR_ & Hf).
            destruct (H1 _ HR_) as (b_ & Hb_ & HR'_).
            apply aur_state_ret; cbn; intuition (eauto with ticl).
          * (* false *)
            apply aur_state_ret; intuition.
    Qed.

    (** Invariance lemma for an infinite while loop, lifts the [ag_state_iter] lemma from [State.v] 
        to the level of HeapImp programs. *)
    Lemma ag_cprog_while: forall c (t: CProg) R mem φ,
        R mem ->      
        (forall mem,
            R mem ->
            <( {instr_prog <{while c do t done }> mem}, {Obs (Log mem) tt} |= φ )> /\          
            <[ {instr_comp c mem}, {Obs (Log mem) tt} |= AX done={(mem, true)} {Obs (Log mem) tt} ]>  /\            
            <[ {instr_prog t mem}, {Obs (Log mem) tt} |= AX (φ AU ret {fun '(mem', _) w' => w' = Obs (Log mem') tt /\ R mem'}) ]>) ->
      <( {instr_prog <{ while c do t done }> mem}, {Obs (Log mem) tt} |= AG φ )>.
    Proof with eauto with ticl.
      unfold instr_prog, instr_comp. 
      intros; subst.
      eapply ag_state_iter with (R:=fun 'tt mem w =>
                                      w = Obs (Log mem) tt /\
                                      <( {instr_prog <{while c do t done }> mem}, w |= φ )> /\
                                        <[ {instr_comp c mem}, w |= AX done={(mem, true)} w ]>  /\            
                                        <[ {instr_prog t mem}, w |= AX (φ AU ret {fun '(mem', _) w' =>
                                                                                        w' = Obs (Log mem') tt /\ R mem'}) ]>)...
      - intros [] mem' w' Hd (-> & Ht & Hc & HR); intuition.
        rewrite interp_state_bind.
        eapply anr_bind_r_eq...
        cbn; rewrite interp_state_bind.
        eapply axr_aur_bind_r; [exact HR |].
        intros [mem_ []] w'' (Hd'' & HR').
        destruct (H0 _ HR') as (? & ? & ?).
        apply aur_state_ret...
        exists tt; subst; cbn; intuition (eauto with ticl).
    Qed.
  End Lemmas.
  
End HeapImp.
