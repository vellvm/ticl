From Stdlib Require Import
  PeanoNat
  Lia.

From ExtLib Require Import
  Structures.Maps
  RelDec
  Data.Map.FMapAList
  Data.String.

From TICL Require Import
  CTree.Core
  CTree.Interp.State.Mod
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

Generalizable All Variables.

(** * MeS: A secure tagged heap language with instrumentation *)
(** In this module we define a simple imperative language with nondeterministic interleavings,
    and shared memory, tagged with a security label [H] for high-security and [L] for low-security.

    The language is defined in terms of a set of events [secE], which include [Read] and [Write] events.
    The semantics of those events are given in terms of instrumentation handler [h_secE], which is a state monad
    that also keeps track of the security labels of the memory cells.

    This language is used in [examples/Sec.v] to prove the security of an infinite interleaving of client programs.
*)
Module ME.
  (** Security labels *)
  Variant Sec: Set := H | L.
  
  (** Preorder of [sec] labels *)
  Reserved Notation "a ≺ b" (at level 52, left associativity).
  Variant sec_lt: relation Sec :=
    | SecLt: L ≺ H
  where "a ≺ b" := (sec_lt a b).
  Local Hint Constructors sec_lt: core.
  
  Reserved Notation "a ⪯ b" (at level 52, left associativity).
  Variant sec_lte: relation Sec :=
    | SecRefl: forall a, a ⪯ a
    | SecHL: L ≺ H -> L ⪯ H
  where "a ⪯ b" := (sec_lte a b).
  Local Hint Constructors sec_lte: core.
  
  Local Instance sec_lte_refl: Reflexive sec_lte := SecRefl.
  Local Instance sec_lt_trans: Transitive sec_lt.
  Proof.
    red; intros [] [] [] *; auto; intros.
    inv H0. inv H1.
  Qed.
  
  Local Instance sec_lte_trans: Transitive sec_lte.
  Proof. red; intros [] [] [] *; auto. Qed.
  
  Lemma sec_lte_dec(l r: Sec): { l ⪯ r } + { r ≺ l }.
  Proof.
    revert r; induction l; destruct r.
    - left; reflexivity. 
    - right; auto. 
    - left; auto.
    - left; reflexivity.
  Qed.
  
  Lemma sec_lte_H(l: Sec): l ⪯ H.
  Proof. destruct l; repeat econstructor. Qed.
  
  Lemma sec_lte_L(l: Sec): L ⪯ l.
  Proof. destruct l; repeat econstructor. Qed.
  
  (** Both values and addresses are natural numbers for simplicity *)
  Abbreviation Addr := nat.
  
  (** Heap events, indexed by their result type *)
  Variant secE: Type -> Type :=
    | Read (l: Sec) (addr: Addr): secE (option nat)
    | Write (l: Sec) (addr: Addr) (val: nat): secE unit.


  (* Secure tagged heaps *)
  #[local] Parameter (St: Type) 
    (MF: Map Addr (Sec * nat) St) 
    (OF: @MapOk Addr (Sec * nat) St eq MF).
  #[global] Existing Instance MF.
  #[global] Existing Instance OF.
  
  Section MeS.
    (** [B]: branch signature; the scheduler's choice is an observable binary branch *)
    Context {B: Type -> Type} `{HB: B2 -< B}.

  (** * Ghost state *)
  (** The instrumentation handler [h_secE] keeps track of the security labels of the memory cells.
    It instruments every read with
     [m: memory address it targets]
     [ml: Security-level of the instruction]
     [al: Security-level of the address cell previously written]
   *)               
  Record SecObs := { ml: Sec; al: Sec }.

  (* Insecure interpreter, does not check labels *)
  Definition h_secE: secE ~> stateT St (ctreeW SecObs B) :=
    fun _ e (st: St) =>
      match e in secE X return ctreeW SecObs B (St * X) with
      | Read l addr =>
          match lookup addr st with
          (* [addr] exists and set to [(v, l_a)] *)
          | Some (l_a, v) =>
              (* Instrumentation *)
              log {| ml:=l_a; al := l |} ;;
              Ret (st, Some v)
          (* [addr] does not exist, return [None] *)
          | None => Ret (st, None)
          end
      | Write l addr v =>
          (* Set [addr] to [(l, v)] *)
          Ret (add addr (l, v) st, tt)
      end.

  (** * The syntax of secure tagged heap programs *)
  (** It includes [Read], [Write], [If], [Ret], [Bind] commands. *)
  Inductive CProg : Type -> Type :=
  | CRead (l: Sec) (addr: Addr): CProg (option nat)
  | CWrite (l: Sec) (addr: Addr) (v: nat): CProg unit
  | CIf {A B X} (c: {A} + {B}) (t: CProg X) (e: CProg X): CProg X
  | CRet {A}(a: A): CProg A
  | CBind {A B}(l: CProg A) (k: A -> CProg B): CProg B.

  Fixpoint denote_cprog {A}(s: CProg A): ctree secE B A :=
    match s with
    | CRead l addr => CTree.trigger (Read l addr)
    | CWrite l addr v => CTree.trigger (Write l addr v)
    | CIf c t e =>
        if c then
          denote_cprog t
        else
          denote_cprog e
    | CRet x => Ret x
    | CBind l k =>
        x <- denote_cprog l ;;        
        denote_cprog (k x)
    end.

  (** * Scheduler programming language *)
  (** The scheduler programming language is a language that allows for interleaving of client programs.
    It includes [SLoop], [SBr], [SCall], [SRet], [SBind] commands.

    The idea is that we write client programs in [CProg], then write the scheduler program in [SProg] to interleave them.
    Denoting both languages to [ctree] gives us a way to reason about the interleaving of client programs.
  *)
  Inductive SProg: Type -> Type :=
  | SLoop {X}(i: X) (b: X -> SProg X): SProg unit
  | SBr {X} (l r: SProg X): SProg X
  | SCall {X} (p: CProg X): SProg X
  | SRet {A}(a: A): SProg A
  | SBind {A B}(l: SProg A) (k: A -> SProg B): SProg B.

  (** Denotation of scheduler programs to [ctree] *)
  Fixpoint denote_sprog {A}(s: SProg A): ctree secE B A :=
    match s with
    | @SLoop X i b =>
        CTree.iter
          (fun (i: X) =>
             x <- denote_sprog (b i) ;;
             Ret (inl x)) i
    | SBr l r =>
        brS2 (denote_sprog l) (denote_sprog r)
    | SCall p => denote_cprog p
    | SRet x => Ret x
    | SBind l k =>
        x <- denote_sprog l ;;        
        denote_sprog (k x)
    end.

  (** Instrumentation of client programs *)
  Definition instr_cprog {X}(p: CProg X): St -> ctreeW SecObs B (St * X) :=
    interp_state h_secE (denote_cprog p).

  (** Instrumentation of scheduler programs *)
  Definition instr_sprog {X}(p: SProg X): St -> ctreeW SecObs B (St * X) :=
    interp_state h_secE (denote_sprog p).

  (** We lift the structural Ticl lemmas to the level of MeS programs. *)
  (** Bind lemmas *)
  Lemma au_cprog_bind_r{X Y} {b : bool}: forall (h: CProg X) (k: X -> CProg Y) m w (φ : ticll (writerE SecObs)) (ψ : ticl_at (writerE SecObs) (St * Y) b) R,
      (forall r m w, R r m w -> entails (St * Y) b <( φ AU ψ )> (instr_cprog (k r) m) w) ->
      entails (St * X) true <( φ AU ret {fun '(m, r) w => R r m w} )> (instr_cprog h m) w ->
      entails (St * Y) b <( φ AU ψ )> (instr_cprog (CBind h k) m) w.
  Proof.
    unfold instr_cprog; cbn; intros.
    eapply au_state_bind_r; eauto with ticl.
  Qed.
  
  Lemma au_cprog_bind_r_eq{X Y} {b : bool}: forall (h: CProg X) (k: X -> CProg Y) m w r w' m' (φ : ticll (writerE SecObs)) (ψ : ticl_at (writerE SecObs) (St * Y) b),
      entails (St * X) true <( φ AU ret={(m', r)} w' )> (instr_cprog h m) w ->
      entails (St * Y) b <( φ AU ψ )> (instr_cprog (k r) m') w' ->
      entails (St * Y) b <( φ AU ψ )> (instr_cprog (CBind h k) m) w.
  Proof.
    unfold instr_cprog; cbn; intros.
    eapply au_state_bind_r_eq; eauto with ticl.
  Qed.
  
  Lemma au_sprog_bind_r{X Y} {b : bool}: forall (h: SProg X) (k: X -> SProg Y) m w (φ : ticll (writerE SecObs)) (ψ : ticl_at (writerE SecObs) (St * Y) b) R,
      (forall r m w, R r m w -> entails (St * Y) b <( φ AU ψ )> (instr_sprog (k r) m) w) ->
      entails (St * X) true <( φ AU ret {fun '(m, r) w => R r m w} )> (instr_sprog h m) w ->
      entails (St * Y) b <( φ AU ψ )> (instr_sprog (SBind h k) m) w.
  Proof.
    unfold instr_sprog; cbn; intros.
    eapply au_state_bind_r; eauto with ticl.
  Qed.
  
  Lemma au_sprog_bind_r_eq{X Y} {b : bool}: forall (h: SProg X) (k: X -> SProg Y) m m' (r: X) w w' (φ : ticll (writerE SecObs)) (ψ : ticl_at (writerE SecObs) (St * Y) b),
      entails (St * X) true <( φ AU ret={(m', r)} w' )> (instr_sprog h m) w ->
      entails (St * Y) b <( φ AU ψ )> (instr_sprog (k r) m') w' ->
      entails (St * Y) b <( φ AU ψ )> (instr_sprog (SBind h k) m) w.
  Proof.
    unfold instr_sprog; cbn; intros.
    eapply au_state_bind_r_eq; eauto with ticl.
  Qed.  
  
  Lemma an_sprog_bind_l{X Y} {b : bool}: forall (h: SProg X) (k: X -> SProg Y) m m' (r: X) w w' (φ : ticll (writerE SecObs)) (ψ : ticl_at (writerE SecObs) (St * Y) b),
      entails (St * X) true <( φ AN ret={(m', r)} w' )> (instr_sprog h m) w ->
      entails (St * Y) b ψ (instr_sprog (k r) m') w' ->
      entails (St * Y) b <( φ AN ψ )> (instr_sprog (SBind h k) m) w.
  Proof.
    unfold instr_sprog; cbn; intros.
    eapply an_state_bind_l_eq; eauto with ticl.
  Qed.

  (** Branch lemmas *)
  Lemma an_sprog_br{X} {suffix : bool}: forall (a b: SProg X) m w (φ : ticll (writerE SecObs)) (ψ : ticl_at (writerE SecObs) (St * X) suffix),
      entails (St * X) false <( φ )> (instr_sprog (SBr a b) m) w ->
      entails (St * X) suffix <( ψ )> (instr_sprog a m) w ->
      entails (St * X) suffix <( ψ )> (instr_sprog b m) w ->
      entails (St * X) suffix <( φ AN ψ )> (instr_sprog (SBr a b) m) w.
  Proof.
    unfold instr_sprog; cbn; intros.
    unfold brS2.
    apply (an_state_brS _ _ _ true); split; eauto with ticl.
    intros []; eauto with ticl.
  Qed.

  (** Call lemmas, call from [SProg] into the client [CProg]. *)
  Lemma ticl_sprog_call{X} {b : bool}: forall (p: CProg X) m w (ψ : ticl_at (writerE SecObs) (St * X) b),
      entails (St * X) b <( ψ )> (instr_cprog p m) w ->
      entails (St * X) b <( ψ )> (instr_sprog (SCall p) m) w.
  Proof.
    unfold instr_sprog, instr_cprog; cbn; intros; eauto with ticl.
  Qed.

  Lemma ticl_cprog_if{P Q X} {b : bool}: forall (c: {P} + {Q}) (t e: CProg X) m w (ψ : ticl_at (writerE SecObs) (St * X) b),
      match c with
      | left _ => entails (St * X) b <( ψ )> (instr_cprog t m) w
      | right _ => entails (St * X) b <( ψ )> (instr_cprog e m) w
      end ->
      entails (St * X) b <( ψ )> (instr_cprog (CIf c t e) m) w.
  Proof.
    unfold instr_cprog; cbn; intros []; intros; eauto with ticl.
  Qed.
  
  (** Invariance lemmas, uses [ag_state_iter] from [State.v] *)
  Lemma ag_sprog_invariance{X}: forall (b: X -> SProg X) R m s (i:X) (φ : ticll (writerE SecObs)),
      R i m s ->
      (forall i m s,
          R i m s ->
          <( {instr_sprog (SLoop i b) m}, {Obs (Log s) tt} |=L φ )> /\
            <( {instr_sprog (b i) m}, {Obs (Log s) tt} |=R AX (φ AU ret {fun '(m', i') w' =>
              exists s', w' = Obs (Log s') tt /\ R i' m' s' }) )>) ->
      <( {instr_sprog (SLoop i b) m}, {Obs (Log s) tt} |=L AG φ )>.
  Proof.
    unfold instr_sprog; cbn.
    intros.
    eapply ag_state_iter with
      (R:=fun (i : X) (m : St) (w : WorldW SecObs) =>
            exists s, w = Obs (Log s) tt /\
              entails (St * unit) false φ (interp_state h_secE (denote_sprog (SLoop i b)) m) (Obs (Log s) tt) /\ 
              entails (St * X) true
                <( AX (φ AU ret {fun '(m', i') w' => exists s', w' = Obs (Log s') tt /\ R i' m' s'}) )>
                (interp_state h_secE (denote_sprog (b i)) m) (Obs (Log s) tt)); eauto with ticl.
    intros i' m' w' _ (s' & -> & Hb & HR); split; [exact Hb |].
    ticl_normalize.
    rewrite interp_state_bind.
    eapply (ax_au_bind_r (b:=true)); [exact HR |].
    intros [m_ r_] w'' (s'' & -> & HR').
    apply (au_state_ret h_secE m_ (b:=true)); apply ret_ret; eauto with ticl.
    exists r_; split2; [reflexivity | constructor |].
    exists s''; split; eauto with ticl.
  Qed.
  End MeS.
End ME.