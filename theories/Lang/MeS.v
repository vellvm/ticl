From Stdlib Require Import
  PeanoNat
  Lia.

From ExtLib Require Import
  Structures.Maps
  RelDec
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
  Notation Addr := nat.
  
  Variant secE: Type :=
    | Read (l: Sec) (addr: Addr)
    | Write (l: Sec) (addr: Addr) (val: nat).
  

  (* Secure tagged heaps *)
  #[local] Parameter (St: Type) 
    (MF: Map Addr (Sec * nat) St) 
    (OF: @MapOk Addr (Sec * nat) St eq MF).
  #[global] Existing Instance MF.
  #[global] Existing Instance OF.
  
  Global Instance encode_secE: Encode secE :=
    fun e => match e with
          | Read l addr => option nat
          | Write l addr v => unit
          end.
  
        
  (** * Ghost state *)
  (** The instrumentation handler [h_secE] keeps track of the security labels of the memory cells.
    It instruments every read with
     [m: memory address it targets]
     [ml: Security-level of the instruction]
     [al: Security-level of the address cell previously written]
   *)               
  Record SecObs := { ml: Sec; al: Sec }.

  (* Insecure interpreter, does not check labels *)
  Definition h_secE: secE ~> stateT St (ictreeW SecObs) :=
    fun e => mkStateT
            (fun (st: St) =>                                     
               match e return ictreeW SecObs (encode e * St) with
               | Read l addr =>
                   match lookup addr st with
                   (* [addr] exists and set to [(v, l_a)] *)
                   | Some (l_a, v) =>
                       (* Instrumentation *)
                       log {| ml:=l_a; al := l |} ;;
                       Ret (Some v, st)
                   (* [addr] does not exist, return [None] *)
                   | None => Ret (None, st)
                   end
               | Write l addr v =>
                   (* Set [addr] to [(l, v)] *)
                   Ret (tt, add addr (l, v) st)
               end).

  (** * The syntax of secure tagged heap programs *)
  (** It includes [Read], [Write], [If], [Ret], [Bind] commands. *)
  Inductive CProg : Type -> Type :=
  | CRead (l: Sec) (addr: Addr): CProg (option nat)
  | CWrite (l: Sec) (addr: Addr) (v: nat): CProg unit
  | CIf {A B X} (c: {A} + {B}) (t: CProg X) (e: CProg X): CProg X
  | CRet {A}(a: A): CProg A
  | CBind {A B}(l: CProg A) (k: A -> CProg B): CProg B.

  Fixpoint denote_cprog {A}(s: CProg A): ictree secE A :=
    match s with
    | CRead l addr => ICtree.trigger (Read l addr)
    | CWrite l addr v => ICtree.trigger (Write l addr v)
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
    Denoting both languages to [ictree] gives us a way to reason about the interleaving of client programs.
  *)
  Inductive SProg: Type -> Type :=
  | SLoop {X}(i: X) (b: X -> SProg X): SProg unit
  | SBr {X} (l r: SProg X): SProg X
  | SCall {X} (p: CProg X): SProg X
  | SRet {A}(a: A): SProg A
  | SBind {A B}(l: SProg A) (k: A -> SProg B): SProg B.

  (** Denotation of scheduler programs to [ictree] *)
  Fixpoint denote_sprog {A}(s: SProg A): ictree secE A :=
    match s with
    | @SLoop X i b =>
        ICtree.iter
          (fun (i: X) =>
             x <- denote_sprog (b i) ;;
             Ret (inl x)) i
    | SBr l r =>
        ICtree.br2 (denote_sprog l) (denote_sprog r)
    | SCall p => denote_cprog p
    | SRet x => Ret x
    | SBind l k =>
        x <- denote_sprog l ;;        
        denote_sprog (k x)
    end.

  (** Instrumentation of client programs *)
  Definition instr_cprog {X}(p: CProg X): St -> ictreeW SecObs (X * St) :=
    interp_state h_secE (denote_cprog p).

  (** Instrumentation of scheduler programs *)
  Definition instr_sprog {X}(p: SProg X): St -> ictreeW SecObs (X * St) :=
    interp_state h_secE (denote_sprog p).

  (** We lift the structural Ticl lemmas to the level of MeS programs. *)
  (** Bind lemmas *)
  Lemma aur_cprog_bind_r{X Y}: forall (h: CProg X) (k: X -> CProg Y) m w φ ψ R,
      (forall r m w, R r m w -> <[ {instr_cprog (k r) m}, w |= φ AU ψ ]>) ->
      <[ {instr_cprog h m}, w |= φ AU AX done {fun '(r, m) w => R r m w} ]> ->
      <[ {instr_cprog (CBind h k) m}, w |= φ AU ψ ]>.
  Proof with eauto with ticl.
    unfold instr_cprog; cbn; intros.
    eapply aur_state_bind_r...
  Qed.
  
  Lemma aur_cprog_bind_r_eq{X Y}: forall (h: CProg X) (k: X -> CProg Y) m w r w' m' φ ψ,
      <[ {instr_cprog h m}, w |= φ AU AX done={(r, m')} w' ]> ->
      <[ {instr_cprog (k r) m'}, w' |= φ AU ψ ]> ->
      <[ {instr_cprog (CBind h k) m}, w |= φ AU ψ ]>.
  Proof with eauto with ticl.
    unfold instr_cprog; cbn; intros.
    eapply aur_state_bind_r_eq...
  Qed.
  
  Lemma aur_sprog_bind_r{X Y}: forall (h: SProg X) (k: X -> SProg Y) m w φ ψ R,
      (forall r m w, R r m w -> <[ {instr_sprog (k r) m}, w |= φ AU ψ ]>) ->
      <[ {instr_sprog h m}, w |= φ AU AX done {fun '(r, m) w => R r m w} ]> ->
      <[ {instr_sprog (SBind h k) m}, w |= φ AU ψ ]>.
  Proof with eauto with ticl.
    unfold instr_sprog; cbn; intros.
    eapply aur_state_bind_r...
  Qed.
  
  Lemma aur_sprog_bind_r_eq{X Y}: forall (h: SProg X) (k: X -> SProg Y) m m' (r: X) w w' φ ψ,
      <[ {instr_sprog h m}, w |= φ AU AX done={(r,m')} w' ]> ->
      <[ {instr_sprog (k r) m'}, w' |= φ AU ψ ]> ->
      <[ {instr_sprog (SBind h k) m}, w |= φ AU ψ ]>.
  Proof with eauto with ticl.
    unfold instr_sprog; cbn; intros.
    eapply aur_state_bind_r_eq...
  Qed.  
  
  Lemma anr_sprog_bind_l{X Y}: forall (h: SProg X) (k: X -> SProg Y) m m' (r: X) w w' φ ψ,
      <[ {instr_sprog h m}, w |= φ AN AX done={(r,m')} w' ]> ->
      <[ {instr_sprog (k r) m'}, w' |= ψ ]> ->
      <[ {instr_sprog (SBind h k) m}, w |= φ AN ψ ]>.
  Proof with eauto with ticl.
    unfold instr_sprog; cbn; intros.
    eapply anr_state_bind_l_eq...
  Qed.

  (** Branch lemmas *)
  Lemma anr_sprog_br{X}: forall (a b: SProg X) m w φ ψ,
      <( {instr_sprog (SBr a b) m}, w |= φ )> ->
      <[ {instr_sprog a m}, w |= ψ ]> ->
      <[ {instr_sprog b m}, w |= ψ ]> ->
      <[ {instr_sprog (SBr a b) m}, w |= φ AN ψ ]>.
  Proof with eauto with ticl.
    unfold instr_sprog; cbn; intros.
    apply anr_state_br; split...
    intros []...
  Qed.

  (** Call lemmas, call from [SProg] into the client [CProg]. *)
  Lemma ticlr_sprog_call{X}: forall (p: CProg X) m w ψ,
      <[ {instr_cprog p m}, w |= ψ ]> ->
      <[ {instr_sprog (SCall p) m}, w |= ψ ]>.
  Proof with eauto with ticl.
    unfold instr_sprog, instr_cprog; cbn; intros...
  Qed.

  Lemma ticlr_cprog_if{A B X}: forall (c: {A} + {B}) (t e: CProg X) m w ψ,
      match c with
      | left _ => <[ {instr_cprog t m}, w |= ψ ]>
      | right _ => <[ {instr_cprog e m}, w |= ψ ]>
      end ->
      <[ {instr_cprog (CIf c t e) m}, w |= ψ ]>.
  Proof with eauto with ticl.
    unfold instr_cprog; cbn; intros []; intros...
  Qed.
  
  (** Invariance lemmas, uses [ag_state_iter] from [State.v] *)
  Lemma ag_sprog_invariance{X}: forall (b: X -> SProg X) R m s (i:X) φ,
      R i m s ->
      (forall i m s,
          R i m s ->
          <( {instr_sprog (SLoop i b) m}, {Obs (Log s) tt} |= φ )> /\
            <[ {instr_sprog (b i) m}, {Obs (Log s) tt} |= AX (φ AU AX done {fun '(i', m') w' =>
              exists s', w' = Obs (Log s') tt /\ R i' m' s' }) ]>) ->
      <( {instr_sprog (SLoop i b) m}, {Obs (Log s) tt} |= AG φ )>.
  Proof with eauto with ticl.
    unfold instr_sprog; cbn.
    intros.
    eapply ag_state_iter with
      (R:=fun i m w =>
            exists s, w = Obs (Log s) tt /\
              <( {interp_state h_secE (denote_sprog (SLoop i b)) m}, {Obs (Log s) tt} |= φ )> /\
              <[ {interp_state h_secE (denote_sprog (b i)) m}, {Obs (Log s) tt}
                             |= AX (φ AU AX done {fun '(i', m') w' => exists s', w' = Obs (Log s') tt /\ R i' m' s'}) ]>)...
    intros i' m' w' _ (s' & -> & Hb & HR); split...
    rewrite interp_state_bind.
    cdestruct HR.
    csplit...      
    - destruct Hs as (t_ & w_ & TR).
      eapply can_step_bind_l...
      specialize (HR _ _ TR).
      now apply aur_not_done in HR.
    - intros t_ w_ TR...
      apply ktrans_bind_inv in TR as [(? & TR & Hd_ & ->) | ((? & ctx_) & ? & ? & ? & TR)].
      + specialize (HR _ _ TR).
        apply aur_bind_r with (R:=fun '(i', m') w' => exists s', w' = Obs (Log s') tt /\ R i' m' s')...
        intros [r_ m_] w'' (? & -> & HR').
        apply aur_state_ret...
        exists r_; intuition.
        exists x0; split...
      + specialize (HR _ _ H2).
        now apply aur_stuck, anr_stuck in HR.
  Qed.
End ME.