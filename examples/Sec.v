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
Proof.
  destruct l; repeat econstructor.
Qed.

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

  (* Insecure interpreter, does not check labels *)
  Definition h_secE: secE ~> stateT St (ctree void) :=
    fun e => mkStateT
            (fun (st: St) =>                                     
               match e return ctree void (encode e * St) with
               | Read _ addr =>                                 
                   match lookup addr st with
                   (* [addr] exists and set to [(v, l_a)] *)
                   | Some (l_a, v) => Ret (Some v, st)
                   (* [addr] does not exist, return [None] *)
                   | None => Ret (None, st)
                   end
               | Write l addr v =>
                   (* Set [addr] to [(l, v)] *)
                   Ret (tt, add addr (l, v) st)
               end).

  (* Ghost state, instrument every read with
     [m: memory address it targets]
     [ml: Security-level of the instruction]
     [al: Security-level of the address cell previously written]
   *)
               
  (* Instrumented semantics, simply log every successful read with [readG] *)
  Definition h_secE_instr: secE ~> stateT St (ctreeW St) :=
    h_writerΣ h_secE.
  
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
    Ctree.forever void
      (fun (i: nat) =>
         (br2
            (sec_alice1 secret i)
            (sec_bob1 i));;
         (* Increase counter by 1 *)
         Ret (S i)) 0.
  
  Definition noleak(i: Addr) (σ: St) : Prop :=
    Nat.Even i ->
    exists v, lookup i σ = Some (L, v).

  (* Safety property: there does not exist a memory label [ml] accessed by
     label [al ≺ ml], or there does not exist a low intruction that reads from
     high-security memory *)
  Typeclasses Transparent equ.
  Theorem ag_safety_sec: forall (secret: nat) (σ: St),
      (forall i, noleak i σ) ->
      <( {interp_state h_secE_instr (sec_system secret) σ},
         {Obs (Log σ) tt} |= AG visW {fun σ => forall i, noleak i σ} )>.
  Proof with eauto with ctl.
    intros.    
    unfold sec_system, forever.
    apply ag_iterW with (R:=fun _ => True)...
    intros i σ' [] Hσ0. 
    rewrite map_bind, interp_state_bind.
    unfold br2.
    rewrite interp_state_br.
    rewrite bind_br.
    apply ax_br; split... 
    intro c.
    rewrite bind_guard.
    apply au_guard.       
    ddestruction c; unfold sec_alice1, sec_bob1;
      destruct (Nat.Even_Odd_dec i);
      rewrite <- interp_state_bind;
      setoid_rewrite map_ret;
      rewrite interp_state_bind.
    - (* Alice runs, [i] is even *)
      eapply au_bind_r_eq.
      + rewrite (@interp_state_trigger _ _ _ _ _ _ (Write H (S i) secret) _); cbn.
        rewrite bind_bind, resumCtree_ret', bind_ret_l.
        eapply au_bind_r_eq; [eapply au_bind_r_eq|].
        * apply au_vis_l...
           -- apply ctl_vis...
           -- intros [].
              cright; apply ax_done...
        * cright; apply ax_done...
        * apply au_guard.
          cright; apply ax_done...
      + cbn.
        rewrite interp_state_ret.
        cright; apply ax_done; split...
        eexists; split...
        do 2 eexists; split...
        cbn; intuition.
        eexists; intuition.
        * intro Heven.
          unfold noleak in *.
          destruct (Nat.eq_dec i0 (S i)).
          -- (* i0 = S i *)
            rewrite e0 in Heven.
            apply Nat.Even_succ in Heven.
            exfalso.
            apply Nat.Even_Odd_False with i...
          -- (* i0 <> S i *)
            destruct (Hσ0 i0 Heven) as (v & ?).
            exists v.
            rewrite OF.(mapsto_lookup).
            apply mapsto_add_neq with (R:=eq); auto.
            now rewrite <- mapsto_lookup.
    - (* Alice runs, [i] is odd *)
      eapply au_bind_r_eq.
      + rewrite (@interp_state_trigger _ _ _ _ _ _ (Write H i secret) _); cbn.
        rewrite bind_bind, resumCtree_ret', bind_ret_l.
        eapply au_bind_r_eq; [eapply au_bind_r_eq|].
        * apply au_vis_l...
          -- apply ctl_vis...
          -- intros [].
             cright; apply ax_done...
        * cright; apply ax_done...
        * cbn.
          apply au_guard.
          cright; apply ax_done...
      + cbn.
        rewrite interp_state_ret.
        cright; apply ax_done; split...
        eexists; split...
        do 2 eexists; split...
        cbn; intuition.
        eexists; intuition.
        * intro Heven.
          unfold noleak in *.
          destruct (Nat.eq_dec i0 i).
          -- (* i0 = i *)
            rewrite e in Heven.
            exfalso.
            apply Nat.Even_Odd_False with i...
          -- (* i0 <> i *)
            destruct (Hσ0 i0 Heven) as (v & ?).
            exists v.
            rewrite OF.(mapsto_lookup).
            apply mapsto_add_neq with (R:=eq); auto.
            now rewrite <- mapsto_lookup.
    - (* Bob runs, [i] is even *)
      eapply au_bind_r_eq.
      + rewrite interp_state_bind.
        rewrite (@interp_state_trigger _ _ _ _ _ _ (Read L i) _); cbn.
        rewrite ?bind_bind.          
        destruct (lookup i σ') eqn:Hlook.
        * destruct p as (l, a).
          rewrite resumCtree_ret', bind_ret_l, bind_bind.
          -- eapply au_bind_r_eq; [eapply au_bind_r_eq|].
             ++ apply au_vis_l...
                ** apply ctl_vis...
                ** intros [].
                   cright; apply ax_done...
             ++ rewrite bind_ret_l, sb_guard.
                cright; apply ax_done...
             ++ cbn.
                rewrite interp_state_ret.
                cright; apply ax_done...
        * rewrite resumCtree_ret', bind_ret_l, ?bind_bind.
          eapply au_bind_r_eq. 
          -- apply au_vis_l...
             apply ctl_vis...
             intros [].
             cright; apply ax_done...
          -- rewrite bind_bind, bind_ret_l, bind_guard, sb_guard, bind_ret_l,
               interp_state_ret.
             cright; apply ax_done...
      + cbn.
        rewrite interp_state_ret.
        cright; apply ax_done; split...
        eexists; split...
        do 2 eexists; split...
        cbn; intuition.
        eexists; intuition.
    - (* Bob runs, [i] is odd *)
      eapply au_bind_r_eq.
      + rewrite interp_state_bind.
        rewrite (@interp_state_trigger _ _ _ _ _ _ (Read L (S i)) _); cbn.
        repeat rewrite bind_bind.          
        destruct (lookup (S i) σ') eqn:Hlook.
        * destruct p as (l, a).
          rewrite resumCtree_ret', bind_ret_l, bind_bind.
          -- eapply au_bind_r_eq; [eapply au_bind_r_eq|].
             ++ apply au_vis_l...
                ** apply ctl_vis...
                ** intros [].
                   cright; apply ax_done...
             ++ rewrite bind_ret_l, sb_guard.
                cright; apply ax_done...
             ++ cbn.
                rewrite interp_state_ret.
                cright; apply ax_done...
        * rewrite resumCtree_ret', bind_ret_l, ?bind_bind.
          eapply au_bind_r_eq. 
          -- apply au_vis_l...
             apply ctl_vis...
             intros [].
             cright; apply ax_done...
          -- rewrite bind_bind, bind_ret_l, bind_guard, sb_guard, bind_ret_l,
               interp_state_ret.
             cright; apply ax_done...
      + cbn.
        rewrite interp_state_ret.
        cright; apply ax_done; split...
        eexists; split...
        do 2 eexists; split...
        cbn; intuition.
        eexists; intuition.
  Qed.
  Print Assumptions ag_safety_sec.
End SecurityEx.
