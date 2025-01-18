From Coq Require Import
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

Module ME.
  (*| Security labels |*)
  Variant Sec: Set := H | L.
  
  (*| Preorder of [sec] labels |*)
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
  
  (*| Both values and addresses are nat |*)
  Notation Addr := nat.
  
  Variant secE: Type :=
    | Read (l: Sec) (addr: Addr)
    | Write (l: Sec) (addr: Addr) (val: nat).
  

  (* Secure tagged heaps *)
  Context `{MF: Map Addr (Sec * nat) St} `{OF: MapOk Addr (Sec * nat) St eq}.
  
  Global Instance encode_secE: Encode secE :=
    fun e => match e with
          | Read l addr => option nat
          | Write l addr v => unit
          end.
  
  (* Ghost state, instrument every read with
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

  (* Client program *)
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

  (* Scheduler program *)
  Inductive SProg: Type -> Type :=
  | SLoop {X}(i: X) (b: X -> SProg X): SProg unit
  | SBr {X} (l r: SProg X): SProg X
  | SCall {X} (p: CProg X): SProg X
  | SRet {A}(a: A): SProg A
  | SBind {A B}(l: SProg A) (k: A -> SProg B): SProg B.

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

  (* Instrumentation of client programs *)
  Definition instr_cprog {X}(p: CProg X): St -> ictreeW SecObs (X * St) :=
    interp_state h_secE (denote_cprog p).

  (* Instrumentation of scheduler programs *)
  Definition instr_sprog {X}(p: SProg X): St -> ictreeW SecObs (X * St) :=
    interp_state h_secE (denote_sprog p).
  
End ME.
