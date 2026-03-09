From Stdlib Require Import
  Nat
  Strings.String
  QArith.QArith.


From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList
  Data.String.

From TICL Require Import
  ICTree.Core
  ICTree.SBisim
  ICTree.Equ
  ICTree.Interp.State
  ICTree.Events.State
  ICTree.Events.Writer
  Logic.Trans
  Logic.Core
  ICTree.Logic.AX
  ICTree.Logic.AF
  ICTree.Logic.EX
  ICTree.Logic.EF
  ICTree.Logic.Bind
  ICTree.Logic.CanStep
  ICTree.Logic.State
  Lang.Maps.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.
Local Open Scope nat_scope.

Generalizable All Variables.

(** * StImp: A simple imperative language with string-indexed variables *)
(** In this module we define a simple imperative language with string-indexed variables.
    The language is denoted in terms of a set of events [stateE], which include [get] and [put] events.
    The semantics of those events are given in terms of instrumentation handler [h_stateE], which is a state monad
    that also keeps track of the context, which is a map from strings to natural numbers.

    This is a simple deep-embedding of a simple imperative language, which allows us to prove structural versions of
    our sequential and loop lemmas from [State.v], over standard program constructs (assignments, conditionals, sequences, etc.).
*)
Module HeapImp.

  Import Ctx.
  (** A context is a map from strings to natural numbers *)
  Definition Store := alist string nat.
  Definition Heap := alist nat nat.

  Record Mem := { store: Store; heap: Heap }.

  Definition memE := stateE Mem.
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
    
  (** * The syntax of StImp programs *)
  (** It includes [CVar], [CConst], [CAdd], [CSub], [CEq], [CLe], [CLt], [CAssgn], [CIf], [CWhile], [CSkip], [CSeq] commands. *)
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

  (** Denotation of expressions to [ictree] *)
  Fixpoint cdenote_exp(e: CExp): ictree memE nat :=
    match e with
    | CStoreRead v => m <- get ;;
               match lookup v (store m) with
               | Some x => Ret x
               | None => stuck
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
        m <- get ;;
        let base := fresh_addr (heap m) in
        let h' := heap_init base n (heap m) in
        put {| store := store m; heap := h' |} ;;
        Ret base
    | CHeapRead a =>
        addr <- cdenote_exp a ;;
        m <- get ;;
        match lookup addr (heap m) with
        | Some x => Ret x
        | None => stuck
        end
    end.

  (** Denotation of boolean comparison expressions to [ictree] *)
  Definition cdenote_comp(c: CComp): ictree memE bool :=
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

  (** Denotation of programs to [ictree] *)
  Fixpoint cdenote_prog (s: CProg): ictree memE unit :=
    match s with
    | CVarWrite x e =>
        v <- cdenote_exp e;;
        m <- get ;;
        put {| store := add x v (store m); heap := heap m |}
    | CHeapWrite a v =>
        addr <- cdenote_exp a ;;
        val <- cdenote_exp v ;;
        m <- get ;;
        put {| store := store m; heap := add addr val (heap m) |}
    | CHeapFree a =>
        addr <- cdenote_exp a ;;
        m <- get ;;
        put {| store := store m; heap := remove addr (heap m) |}
    | CIf c t e =>
        bv <- cdenote_comp c ;;
        if bv then
          cdenote_prog t
        else
          cdenote_prog e
    | CWhile c b =>       
        ICtree.iter
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
  Definition instr_exp(e: CExp) (mem: Mem) : ictreeW Mem (nat * Mem) :=
    instr_stateE (cdenote_exp e) mem.

  Definition instr_comp(c: CComp) (mem: Mem) : ictreeW Mem (bool * Mem) :=
    instr_stateE (cdenote_comp c) mem.
    
  Definition instr_prog(p: CProg) (mem: Mem) : ictreeW Mem (unit * Mem) :=
    instr_stateE (cdenote_prog p) mem.
  
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
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log mem as z := pat return (encode z -> Prop) in
                       fun 'tt => p mem)))
      (in custom ticll at level 75, p constr) : ticl_scope.

  (** Utility lemmas *)
  Lemma var_eq{X}: forall (p: ictreeW Mem X) c v m,
      lookup c (store m) = Some v ->      
      <( p, {Obs (Log m) tt} |= obs <p{ c =? v }> )>.
  Proof with eauto with ticl.
    intros.
    apply ticll_vis... 
  Qed.

  Lemma var_ge{X}: forall (p: ictreeW Mem X) c v v' m,
      v' >= v ->
      lookup c (store m) = Some v' ->
      <( p, {Obs (Log m) tt} |= obs <p{ c >=? v }> )>.
  Proof.
    intros.
    apply ticll_vis...
    constructor.
    exists v'; intuition.
  Qed.

  Lemma var_le{X}: forall (p: ictreeW Mem X) c v v' m,
      v' <= v ->
      lookup c (store m) = Some v' ->
      <( p, {Obs (Log m) tt} |= obs <p{ c <=? v }> )>.
  Proof.
    intros.
    apply ticll_vis...
    constructor.
    exists v'; intuition.
  Qed.

  (** Comparing [x] and [c] returns a boolean [b] in one step *)
  Lemma axr_ccomp_lt: forall x (c: string) b mem w (v: nat),
      lookup c (store mem) = Some v ->
      b = Nat.ltb x v ->
      not_done w ->
      <[ {instr_comp <b{ x <? c }> mem}, {w} |= AX (done= {(b, mem)} {w}) ]>.
  Proof with eauto with ticl.
    intros.
    Opaque Nat.ltb.
    unfold instr_comp, instr_stateE.    
    eapply anr_state_bind_r_eq...
    - apply axr_state_ret...
    - eapply anr_state_bind_r_eq...
      + eapply anr_state_bind_r_eq...
        * rewrite interp_state_get.
          apply axr_ret...
        * setoid_rewrite H.
          apply axr_state_ret...
      + rewrite H0.
        apply axr_state_ret...
  Qed.
    
  (** Constant expressions are evaluated to the constant in one step *)
  Lemma axr_cexp_const: forall (v v': nat) mem mem' w w',
      v = v' ->
      mem = mem' ->
      w = w' ->
      not_done w ->
      <[ {instr_exp v mem}, w |= AX done= {(v', mem')} w' ]>.
  Proof.
    intros; subst.
    unfold instr_exp, instr_stateE; cbn.
    rewrite interp_state_ret.
    now apply axr_ret.
  Qed.

  (** Adding [v1] to [c] returns [v2] in one step *)
  Lemma axr_cexp_add: forall (c: string) (v0 v1 v2: nat) mem mem' w w',
      lookup c (store mem) = Some v0  ->
      v2 = v0 + v1 ->
      mem = mem' ->
      w = w' ->
      not_done w ->
      <[ {instr_exp <e{ c + v1 }> mem}, w |= AX done= {(v2, mem')} w' ]>.
  Proof with eauto with ticl.
    intros; subst.
    unfold instr_exp, instr_stateE; cbn.
    rewrite bind_bind.
    eapply anr_state_bind_r_eq.
    - apply axr_get...
    - setoid_rewrite H.
      rewrite ?bind_ret_l.
      apply axr_state_ret...
  Qed.

  (** Subtracting [v1] from [c] returns [v2] in one step *)
  Lemma axr_cexp_sub: forall (c: string) (v0 v1 v2: nat) mem mem' w w',
      lookup c (store mem) = Some v0  ->
      v2 = v0 - v1 ->
      mem = mem' ->
      w = w' ->
      not_done w ->
      <[ {instr_exp <e{ c - v1 }> mem}, w |= AX done= {(v2, mem')} w' ]>.
  Proof with eauto with ticl.
    intros; subst.
    unfold instr_exp, instr_stateE; cbn.
    rewrite bind_bind.
    eapply anr_state_bind_r_eq.
    - apply axr_get...
    - setoid_rewrite H.
      rewrite ?bind_ret_l.
      apply axr_state_ret...
  Qed.
  
  (** * Variable assignment: structural temporal lemmas *)
  (** A variable write [x := a] eventually (suffix) [AU] returns, where [r] is the evaluation of [a]. 
      Assignments are instrumented with a [log] event, which records the new context.
  *)
  Lemma aur_cprog_var_write: forall x a mem r w R ψ,
      let mem' := update_store x r mem in
      <[ {instr_exp a mem}, w |= AX done= {(r, mem)} w ]> ->
      <( {log mem'}, w |= ψ )> ->
      R (tt, mem') (Obs (Log mem') tt) ->
      <[ {instr_prog <{ x := a }> mem}, w |= ψ AU AX done R ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_exp.
    intros; cbn.
    eapply aur_state_bind_r_eq.
    - cleft...
    - eapply aur_state_bind_r_eq.
      + eapply aur_get...
        apply ticll_not_done in H0...
      + eapply aur_put...
  Qed.

  (** A variable write [x := a] eventually (prefix) [AU] returns, where [r] is the evaluation of [a]. 
      Assignments are instrumented with a [log] event, which records the new context.
  *)
  Lemma aul_cprog_var_write: forall x a mem r w ψ φ,
      let mem' := update_store x r mem in
      <[ {instr_exp a mem}, w |= AX done= {(r, mem)} w ]> ->
      <( {log mem'}, w |= ψ )> ->
      <( {Ret (tt, mem')}, {Obs (Log mem') tt} |= φ )> ->
      <( {instr_prog <{ x := a }> mem}, w |= ψ AU φ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_exp.
    intros; cbn.
    eapply aul_state_bind_r_eq.
    - cleft...
    - eapply aul_state_bind_r_eq.
      + eapply aur_get...
        apply ticll_not_done in H0...
      + rewrite interp_state_put.
        cright.
        apply anl_log.
        * cleft...
        * apply ticll_bind_l...
  Qed.

  (** * Heap write: structural temporal lemmas *)
  (** A heap write [*a := v] eventually (suffix) [AU] returns. *)
  Lemma aur_cprog_heap_write: forall ae ve mem addr val w R ψ,
      let mem' := update_heap addr val mem in
      <[ {instr_exp ae mem}, w |= AX done= {(addr, mem)} w ]> ->
      <[ {instr_exp ve mem}, w |= AX done= {(val, mem)} w ]> ->
      <( {log mem'}, w |= ψ )> ->
      R (tt, mem') (Obs (Log mem') tt) ->
      <[ {instr_prog (CHeapWrite ae ve) mem}, w |= ψ AU AX done R ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_exp.
    intros; cbn.
    eapply aur_state_bind_r_eq.
    - cleft...
    - eapply aur_state_bind_r_eq.
      + cleft...
      + eapply aur_state_bind_r_eq.
        * eapply aur_get...
          apply ticll_not_done in H1...
        * eapply aur_put...
  Qed.

  (** A heap write [*a := v] eventually (prefix) [AU] returns. *)
  Lemma aul_cprog_heap_write: forall ae ve mem addr val w ψ φ,
      let mem' := update_heap addr val mem in
      <[ {instr_exp ae mem}, w |= AX done= {(addr, mem)} w ]> ->
      <[ {instr_exp ve mem}, w |= AX done= {(val, mem)} w ]> ->
      <( {log mem'}, w |= ψ )> ->
      <( {Ret (tt, mem')}, {Obs (Log mem') tt} |= φ )> ->
      <( {instr_prog (CHeapWrite ae ve) mem}, w |= ψ AU φ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_exp.
    intros; cbn.
    eapply aul_state_bind_r_eq.
    - cleft...
    - eapply aul_state_bind_r_eq.
      + cleft...
      + eapply aul_state_bind_r_eq.
        * eapply aur_get...
          apply ticll_not_done in H1...
        * rewrite interp_state_put.
          cright.
          apply anl_log.
          -- cleft...
          -- apply ticll_bind_l...
  Qed.

  (** * Heap free: structural temporal lemmas *)
  (** A heap free eventually (suffix) [AU] returns. *)
  Lemma aur_cprog_heap_free: forall ae mem addr w R ψ,
      let mem' := free_heap addr mem in
      <[ {instr_exp ae mem}, w |= AX done= {(addr, mem)} w ]> ->
      <( {log mem'}, w |= ψ )> ->
      R (tt, mem') (Obs (Log mem') tt) ->
      <[ {instr_prog (CHeapFree ae) mem}, w |= ψ AU AX done R ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_exp.
    intros; cbn.
    eapply aur_state_bind_r_eq.
    - cleft...
    - eapply aur_state_bind_r_eq.
      + eapply aur_get...
        apply ticll_not_done in H0...
      + eapply aur_put...
  Qed.

  (** A heap free eventually (prefix) [AU] returns. *)
  Lemma aul_cprog_heap_free: forall ae mem addr w ψ φ,
      let mem' := free_heap addr mem in
      <[ {instr_exp ae mem}, w |= AX done= {(addr, mem)} w ]> ->
      <( {log mem'}, w |= ψ )> ->
      <( {Ret (tt, mem')}, {Obs (Log mem') tt} |= φ )> ->
      <( {instr_prog (CHeapFree ae) mem}, w |= ψ AU φ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_exp.
    intros; cbn.
    eapply aul_state_bind_r_eq.
    - cleft...
    - eapply aul_state_bind_r_eq.
      + eapply aur_get...
        apply ticll_not_done in H0...
      + rewrite interp_state_put.
        cright.
        apply anl_log.
        * cleft...
        * apply ticll_bind_l...
  Qed.
  
  (** * Sequence: structural temporal lemmas *)
  (** Sequential composition  [a ;;; b] lemmas *)
  Lemma anr_cprog_seq: forall a b mem mem' w w' φ ψ,
      <[ {instr_prog a mem}, w |= ψ AN done= {(tt,mem')} w' ]> ->
      <[ {instr_prog b mem'}, w' |= ψ AN φ ]> ->
      <[ {instr_prog <{ a ;;; b }> mem}, w |= ψ AN φ ]>.
  Proof.
    unfold instr_prog. 
    intros; cbn.
    eapply anr_state_bind_r_eq; eauto.
  Qed.
  
  Lemma aur_cprog_seq: forall a b mem mem' w w' φ ψ,
      <[ {instr_prog a mem}, w |= φ AU AX done= {(tt,mem')} w' ]> ->
      <[ {instr_prog b mem'}, w' |= φ AU ψ ]> ->
      <[ {instr_prog <{ a ;;; b }> mem}, w |= φ AU ψ ]>.
  Proof.
    unfold instr_prog.
    intros; cbn.
    eapply aur_state_bind_r_eq; eauto.
  Qed.
  
  Lemma aul_cprog_seq: forall a b mem mem' w w' φ ψ,
      <[ {instr_prog a mem}, w |= φ AU AX done= {(tt,mem')} w' ]> ->
      <( {instr_prog b mem'}, w' |= φ AU ψ )> ->
      <( {instr_prog <{ a ;;; b }> mem}, w |= φ AU ψ )>.
  Proof.
    unfold instr_prog. 
    intros; cbn.
    eapply aul_state_bind_r_eq; eauto.
  Qed.
  
  Lemma ag_cprog_seq: forall a b mem mem' w w' φ,
      <[ {instr_prog a mem}, w |= φ AU AX done= {(tt,mem')} w' ]> ->
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
      <[ {instr_comp c mem}, w |= AX done= {(b, mem)} w ]> ->
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
      <[ {instr_comp c mem}, w |= AX done= {(b, mem)} w ]> ->
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
      <[ {instr_comp c mem}, w |= AX done={(true, mem)} w ]> ->
      <[ {instr_prog t mem}, w |= φ AU AX done={(tt, mem')} w' ]> ->
      <( {instr_prog <{ while c do t done }> mem'}, w' |= φ AU ψ )> ->   
      <( {instr_prog <{ while c do t done }> mem}, w |= φ AU ψ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; cbn; intros.
    apply aul_state_iter_next_eq with tt w' mem'...
    - eapply aur_state_bind_r_eq.
      + cleft...
      + cbn; apply ticll_not_done in H1.
        eapply aur_state_bind_r_eq...
        apply aur_state_ret; intuition.
    - apply ticll_not_done in H1...
  Qed.

  (** The loop terminates if [c] evaluates to [false] *)
  Lemma aul_cprog_while_false: forall c t w φ ψ mem,
      <[ {instr_comp c mem}, w |= AX done={(false, mem)} w ]> ->
      <( {Ret (tt, mem)}, w |= ψ )> ->
      <( {instr_prog <{ while c do t done }> mem}, w |= φ AU ψ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; cbn; intros.
    rewrite instr_state_unfold_iter.
    eapply aul_bind_r_eq.
    - eapply aur_state_bind_r_eq.
      + cleft...
      + apply ticll_not_done in H0.
        apply aur_state_ret...
    - cleft...
  Qed.

  (** Unroll one iteration of the while loop if [c] evaluates to [true], suffix [AU] version *)
  Lemma aur_cprog_while_true: forall c t w w' φ ψ mem mem',
      <[ {instr_comp c mem}, w |= AX done={(true, mem)} w ]> ->
      <[ {instr_prog t mem}, w |= φ AU AX done={(tt, mem')} w' ]> ->
      <[ {instr_prog <{ while c do t done }> mem'}, w' |= φ AU AX ψ ]> ->   
      <[ {instr_prog <{ while c do t done }> mem}, w |= φ AU AX ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; cbn; intros.
    apply aur_state_iter_next_eq with tt w' mem'...
    - eapply aur_state_bind_r_eq.
      + cleft...
      + cbn. 
        eapply aur_state_bind_r_eq...
        apply aur_state_ret; intuition.
        now apply aur_not_done in H1.
    - now apply aur_not_done in H1. 
  Qed.

  (** The loop terminates if [c] evaluates to [false], suffix [AU] version *)
  Lemma aur_cprog_while_false: forall c t w φ ψ mem,
      <[ {instr_comp c mem}, w |= AX done={(false, mem)} w ]> ->
      <[ {Ret (tt, mem)}, w |= AX ψ ]> ->
      <[ {instr_prog <{ while c do t done }> mem}, w |= φ AU AX ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; cbn; intros.
    rewrite instr_state_unfold_iter.
    eapply aur_bind_r_eq.
    - eapply aur_state_bind_r_eq.
      + cleft...
      + apply aur_state_ret...
        cdestruct H.
        apply can_step_not_done in Hs...
    - cleft...
  Qed.
  
  (** Termination lemma for a while loop, lifts the [aul_state_iter_nat] lemma from [State.v] 
      to the level of StImp programs. *)
  Theorem aul_cprog_while mem (t: CProg) Ri f c φ ψ:
    Ri mem ->
    <[ {instr_comp c mem}, {Obs (Log mem) tt} |= AX done={(true, mem)} {Obs (Log mem) tt} ]> ->
    (forall mem,
        Ri mem ->        
        exists (b: bool), <[ {instr_comp c mem}, {Obs (Log mem) tt} |= AX done={(b, mem)} {Obs (Log mem) tt} ]> /\
          if b then
            <( {instr_prog t mem}, {Obs (Log mem) tt} |= φ AU ψ )> \/ 
              <[ {instr_prog t mem}, {Obs (Log mem) tt} |= φ AU AX done {fun '(_, mem') w' =>
                                            w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem} ]>
          else
            <( {Ret (inr unit tt, mem)}, {Obs (Log mem) tt} |= ψ )>) ->
      <( {instr_prog <{ while c do t done }> mem}, {Obs (Log mem) tt} |= φ AU ψ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp.
    intros HR Hb H.
    eapply aul_state_iter_nat with
      (Ri:=fun 'tt mem w =>
             w = Obs (Log mem) tt /\
             exists (b: bool),
               <[ {instr_stateE (cdenote_comp c) mem}, w |= AX done={(b, mem)} w ]> /\
                 if b then
                   <( {instr_stateE (cdenote_prog t) mem}, w |= φ AU ψ )> \/ 
                     <[ {instr_stateE (cdenote_prog t) mem}, w |= φ AU AX done {fun '(_, mem') w' =>
                                                                                  w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem} ]>
                 else
                   <( {Ret (inr unit tt, mem)}, w |= ψ )>)
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
             apply aur_state_ret...
             exists tt; intuition.
      + (* false *)
        left.
        eapply aul_state_bind_r_eq...
        * cleft...
        * cbn.
          apply aul_state_ret...
  Qed.

  (** Termination lemma for a while loop (suffix version) lifts the [aur_state_iter_nat] lemma from [State.v] 
      to the level of StImp programs. *)
  Theorem aur_cprog_while_termination mem (t: CProg) Ri f c φ ψ b:    
      Ri mem ->
      <[ {instr_comp c mem}, {Obs (Log mem) tt} |= AX done={(b, mem)} {Obs (Log mem) tt} ]> ->
      (forall mem,
          Ri mem ->
          exists (b: bool), <[ {instr_comp c mem}, {Obs (Log mem) tt} |= AX done={(b, mem)} {Obs (Log mem) tt} ]> /\
          if b then
            <[ {instr_prog t mem}, {Obs (Log mem) tt} |= φ AU AX done {fun '(_, mem') w' => w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem} ]>
          else
            <[ {Ret (tt, mem)}, {Obs (Log mem) tt} |= φ AN ψ ]>) ->
      <[ {instr_prog <{ while c do t done }> mem}, {Obs (Log mem) tt} |= φ AU ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp; intros.
    eapply aur_state_iter_nat with
      (Ri:=fun 'tt mem w =>
             w = Obs (Log mem) tt /\
             exists b : bool,
               <[ {instr_stateE (cdenote_comp c) mem}, {Obs (Log mem) tt} |= AX (done= {(b, mem)} {Obs (Log mem) tt}) ]> /\
                 (if b
                  then
                    <[ {instr_stateE (cdenote_prog t) mem}, {Obs (Log mem) tt} |= {φ} AU AX (done {fun '(_, mem') (w' : WorldW Mem) =>
                                                                       w' = Obs (Log mem') tt /\ Ri mem' /\ f mem' < f mem}) ]>
                  else <[ {Ret (tt, mem)}, {Obs (Log mem) tt} |= {φ} AN {ψ} ]>))
      (f:= fun _ mem _ => f mem)...
    - intros [] mem' w' Hd (-> & b' & Hb' & HR).
      eapply aur_state_bind_r_eq...
      + cleft...
      + destruct b'.
        * (* true *)
          eapply aur_state_bind_r with (R:=fun _ mem'0 w' => w' = Obs (Log mem'0) tt /\ Ri mem'0 /\ f mem'0 < f mem')...
          intros [] mem_ w_ (Hd_ & HR_ & Hf).
          apply aur_state_ret; intuition.
        * (* false *)
          apply aur_state_ret; intuition.
  Qed.

  (** Invariance lemma for an infinite while loop, lifts the [ag_state_iter] lemma from [State.v] 
      to the level of StImp programs. *)
  Lemma ag_cprog_while: forall c (t: CProg) R mem φ,
      R mem ->      
      (forall mem,
          R mem ->
          <( {instr_prog <{while c do t done }> mem}, {Obs (Log mem) tt} |= φ )> /\          
          <[ {instr_comp c mem}, {Obs (Log mem) tt} |= AX done={(true,mem)} {Obs (Log mem) tt} ]>  /\            
          <[ {instr_prog t mem}, {Obs (Log mem) tt} |= AX (φ AU AX done {fun '(_, mem') w' => w' = Obs (Log mem') tt /\ R mem'}) ]>) ->
    <( {instr_prog <{ while c do t done }> mem}, {Obs (Log mem) tt} |= AG φ )>.
  Proof with eauto with ticl.
    unfold instr_prog, instr_comp. 
    intros; subst.
    eapply ag_state_iter with (R:=fun 'tt mem w =>
                                    w = Obs (Log mem) tt /\
                                    <( {instr_prog <{while c do t done }> mem}, w |= φ )> /\
                                      <[ {instr_comp c mem}, w |= AX done={(true,mem)} w ]>  /\            
                                      <[ {instr_prog t mem}, w |= AX (φ AU AX done {fun '(_, mem') w' =>
                                                                                      w' = Obs (Log mem') tt /\ R mem'}) ]>)...
    - intros [] mem' w' Hd (-> & Ht & Hc & HR); intuition.
      rewrite interp_state_bind.
      eapply anr_bind_r_eq...
      cbn; rewrite interp_state_bind.
      cdestruct HR.
      csplit...      
      + destruct Hs as (t_ & w_ & TR).
        eapply can_step_bind_l...
        specialize (HR _ _ TR).
        now apply aur_not_done in HR.
      + intros t_ w_ TR...
        apply ktrans_bind_inv in TR as [(? & TR & Hd_ & ->) | (([] & mem_) & ? & ? & ? & TR)].
        * specialize (HR _ _ TR).
          apply aur_bind_r with (R:=fun '(_, mem') (w' : WorldW Mem) => w' = Obs (Log mem') tt /\ R mem')...
          intros [_ mem_] w'' (Hd'' & HR').
          apply aur_state_ret...
          exists tt; subst; intuition.
        * specialize (HR _ _ H1).
          now apply aur_stuck, anr_stuck in HR.
  Qed.
  
End HeapImp.