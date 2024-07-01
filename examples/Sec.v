From Coq Require Import Arith.PeanoNat.

From CTree Require Import
  CTree.Equ
  CTree.Core
  CTree.Events.Writer
  Logic.Ctl
  CTree.SBisim
  CTree.Logic.Trans
  CTree.Logic.AF
  CTree.Logic.AX
  CTree.Logic.AG
  CTree.Logic.State
  CTree.Logic.Bind
  CTree.Logic.CanStep
  CTree.Interp.Core
  CTree.Interp.State
  CTree.Events.State.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Maps.

Generalizable All Variables.

Import Ctree CTreeNotations CtlNotations.
Local Open Scope ctree_scope.
Local Open Scope ctl_scope.

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

Section SecurityEx.
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
  Definition h_secE: secE ~> stateT St (ctreeW SecObs) :=
    fun e => mkStateT
            (fun (st: St) =>                                     
               match e return ctreeW SecObs (encode e * St) with
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

  (* Trigger instructions *)
  Definition read: Sec -> Addr -> ctree secE (option nat) :=
    fun (l: Sec) (addr: Addr) => Ctree.trigger (Read l addr). 
  
  Definition write: Sec -> Addr -> nat -> ctree secE unit :=
    fun (l: Sec) (addr: Addr) (s: nat) => Ctree.trigger (Write l addr s).

  (* Alice (H) writes [secret] to odd addresses *)
  Definition sec_alice1(secret: nat)(i: Addr): ctree secE unit :=
    if Nat.Even_Odd_dec i then
      (* [i] even, write to [i+1] *)
      write H (S i) secret
    else
      (* [i] odd, write to [i] *)
      write H i secret.
 
  (* Bob (L) reads from even addresses *)
  Definition sec_bob1(i: Addr): ctree secE unit :=
    if Nat.Even_Odd_dec i then
      (* [i] even, read [i] *)
      read L i;; Ret tt
    else
      (* [i] odd, read [i+1] *)
      read L (S i) ;; Ret tt.

  (* The (unfair) infinite interleaving of Alice/Bob *)
  Definition sec_system(secret: nat): ctree secE void :=
    for 0 to ∞
      (fun i =>
         (br2
            (sec_alice1 secret i)
            (sec_bob1 i));;
         (* Increase counter by 1 *)
         Ret (S i)).

  Definition no_leak(i: Addr) (σ: St): Prop :=
    Nat.Even i -> exists v, lookup i σ = Some (L, v).

  (* Safety property: All memory labels [ml] accessed by
     label [al ≺ ml], or there does not exist a low intruction that reads from
     high-security memory *)
  Typeclasses Transparent equ.
  Theorem ag_safety_sec: forall (secret: nat) (σ: St),
      (forall i, no_leak i σ) ->
      <( {interp_state h_secE (sec_system secret) σ},
         {Obs (Log {| ml := L; al := L |}) tt} |= AG visW {fun obs => obs.(al) ⪯ obs.(ml)} )>.
  Proof with eauto with ctl.
    intros.    
    unfold sec_system, forever.
    apply ag_state_iter with
      (R:=fun _ σ w =>
            exists (obs: SecObs), w = Obs (Log obs) tt
                             /\ obs.(al) ⪯ obs.(ml)
                             /\ forall i, no_leak i σ)...
    intros i σ' w Hd (obs & -> & Hobs & Hσ0). 
    rewrite interp_state_map; unfold map.
    split; [csplit; auto|].
    unfold br2; cbn...
    rewrite interp_state_bind, interp_state_br, ?bind_br.
    apply axr_br; split; [csplit; auto|].
    intro c. (* Choice witness *)
    rewrite bind_bind, bind_guard, sb_guard.
    ddestruction c; unfold sec_alice1, sec_bob1;
      destruct (Nat.Even_Odd_dec i).
    - (* Alice runs, [i] is even *)
      rewrite (@interp_state_trigger _ _ _ _ _ _ (Write H (S i) secret) _); cbn.
      rewrite bind_bind, bind_ret_l, bind_guard, sb_guard, bind_ret_l,
        interp_state_ret, bind_ret_l.
      cleft; apply anr_ret...
      eexists; split2...
      eexists; split2...
      intros i0 Heven.
      destruct (Hσ0 i0 Heven) as (v & ?); exists v.
      destruct (Nat.eq_dec i0 (S i)).
      + (* i0 = S i *)
        rewrite e0 in Heven.
        exfalso.
        apply Nat.Even_succ in Heven.
        apply Nat.Even_Odd_False with i...
      + (* i0 <> i *)
        rewrite OF.(mapsto_lookup).
        apply mapsto_add_neq with (R:=eq); auto.
        now rewrite <- mapsto_lookup.
    - (* Alice runs, [i] is odd *)
      rewrite (@interp_state_trigger _ _ _ _ _ _ (Write H i secret) _); cbn.
      rewrite bind_bind, bind_ret_l, bind_guard, sb_guard, bind_ret_l,
        interp_state_ret, bind_ret_l.
      cleft; apply anr_ret...
      eexists; split2...
      eexists; split2...
      intros i0 Heven.
      destruct (Hσ0 i0 Heven) as (v & ?); exists v.
      destruct (Nat.eq_dec i0 i).
      * (* i0 = i *)
        rewrite e in Heven.
        exfalso.
        apply Nat.Even_Odd_False with i...
      * (* i0 <> i *)
        rewrite OF.(mapsto_lookup).
        apply mapsto_add_neq with (R:=eq); auto.
        now rewrite <- mapsto_lookup.
    - (* Bob runs, [i] is even *)
      rewrite interp_state_bind, bind_bind.
      rewrite (@interp_state_trigger _ _ _ _ _ _ (Read L i) _); cbn.
      rewrite bind_bind.
      destruct (lookup i σ') eqn:Hlook.
      + destruct p as (l, a).
        eapply aur_bind_r_eq; [eapply aur_bind_r_eq|].
        * apply aur_vis...
          right; split.
          -- apply ctll_vis...
          -- intros [].
             cleft; apply anr_ret...
        * cleft; apply anr_ret... 
        * rewrite bind_guard, sb_guard, bind_ret_l, interp_state_ret, bind_ret_l,
            interp_state_ret, bind_ret_l.
          cleft; apply anr_ret... 
          eexists; intuition.
          eexists; intuition; cbn.
          apply sec_lte_L.
      + rewrite bind_ret_l, bind_guard, sb_guard, bind_ret_l, interp_state_ret,
          bind_ret_l, interp_state_ret, bind_ret_l.
        cleft; apply anr_ret... 
        eexists; intuition.
        eexists; intuition.
    - (* Bob runs, [i] is odd *)
      rewrite interp_state_bind, bind_bind.
      rewrite (@interp_state_trigger _ _ _ _ _ _ (Read L (S i)) _); cbn.
      rewrite bind_bind.
      destruct (lookup (S i) σ') eqn:Hlook.
      + destruct p as (l, a).
        eapply aur_bind_r_eq; [eapply aur_bind_r_eq|].
        * apply aur_vis...
          right; split.
          -- apply ctll_vis...
          -- intros [].
             cleft; apply anr_ret... 
        * cleft; apply anr_ret... 
        * rewrite bind_guard, sb_guard, bind_ret_l, interp_state_ret, bind_ret_l,
            interp_state_ret, bind_ret_l.
          cleft; apply anr_ret... 
          eexists; intuition.
          eexists; intuition; cbn.
          apply sec_lte_L.
      + rewrite bind_ret_l, bind_guard, sb_guard, bind_ret_l, interp_state_ret,
          bind_ret_l, interp_state_ret, bind_ret_l.
        cleft; apply anr_ret... 
        eexists; intuition.
        eexists; intuition.
  Qed.
  Print Assumptions ag_safety_sec.
End SecurityEx.
