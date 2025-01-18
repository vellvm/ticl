From Coq Require Import
  Arith.PeanoNat.

From TICL Require Import
  ICTree.Equ
  ICTree.Core
  ICTree.Events.Writer
  Logic.Core
  ICTree.SBisim
  ICTree.Logic.Trans
  ICTree.Logic.AF
  ICTree.Logic.AX
  ICTree.Logic.AG
  ICTree.Logic.State
  ICTree.Logic.Bind
  ICTree.Logic.CanStep
  ICTree.Interp.Core
  ICTree.Interp.State
  ICTree.Events.State
  Lang.MeS.

From ExtLib Require Import
  Structures.MonadState
  Data.Monads.StateMonad
  Structures.Maps.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ictree_scope.
Local Open Scope ticl_scope.
Local Open Scope nat_scope.

Module Sec.
  Include ME.

  Existing Instance sec_lte_refl. 
  Existing Instance sec_lt_trans. 

  (* Alice (H) writes [secret] to odd addresses *)
  Definition alice (secret: nat)(i: Addr): CProg unit :=
    CIf (Nat.Even_Odd_dec i)
      (CWrite H (S i) secret)
      (CWrite H i secret).

  Definition bob (i: Addr): CProg unit :=
    CBind
      (CIf (Nat.Even_Odd_dec i)
         (CRead H i)
         (CRead H (S i)))
      (fun _=> CRet tt).

  Definition sched (secret: nat): SProg unit :=
    SLoop 0
      (fun i =>
         SBind
           (SBr
              (SCall (alice secret i))
              (SCall (bob i)))
           (fun _ => SRet (1 + i))).
  
  Definition no_leak(i: Addr) (σ: St): Prop :=
    Nat.Even i -> exists v, lookup i σ = Some (L, v).

  (* Safety property: All memory labels [ml] accessed by label [al] satisfy [al ≺ ml] *)
  Local Typeclasses Transparent equ.
  Local Typeclasses Transparent sbisim.
  Theorem ag_safety_sec: forall (secret: nat) (m: St),
      (forall i, no_leak i m) ->
      <( {instr_sprog (sched secret) m}, {Obs (Log {| ml := L; al := L |}) tt}
           |= AG visW {fun obs => obs.(al) ⪯ obs.(ml)} )>.
  Proof with eauto with ticl.
    intros.    
    unfold sched. 
    apply ag_sprog_invariance with
      (R:=fun _ m obs => obs.(al) ⪯ obs.(ml) /\ forall i, no_leak i m)...
    unfold no_leak in *.
    intros i m' s' (Hobs & Hm0).
    (* LEF: HERE *)
    fail.
    
    rewrite interp_state_map; unfold map.
    split; [csplit; auto|].
    unfold br2; cbn...
    rewrite interp_state_bind, bind_bind, interp_state_bind, bind_bind,
      interp_state_br, bind_br.
    apply axr_br; split; [csplit; auto|].
    intro c. (* Choice witness *)
    rewrite sb_guard; ddestruction c; unfold sec_alice1, sec_bob1;
      destruct (Nat.Even_Odd_dec i).
    - (* Alice runs, [i] is even *)
      rewrite (@interp_state_trigger _ _ _ _ _ _ (Write H (S i) secret) _); cbn.
      rewrite bind_bind, bind_ret_l, bind_guard, sb_guard, bind_ret_l,
        interp_state_ret, bind_ret_l, interp_state_ret, bind_ret_l.
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
        interp_state_ret, bind_ret_l, interp_state_ret, bind_ret_l.
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
      destruct (Hσ0 _ e) as (v & ?).
      rewrite H1.
      eapply aur_bind_r_eq; [eapply aur_bind_r_eq|].
      + apply aur_vis...
        right; split.
        * apply ticll_vis...
        * intros [].
          cleft; apply anr_ret...
      + cleft; apply anr_ret... 
      + rewrite sb_guard, bind_ret_l, interp_state_ret,
          bind_ret_l, interp_state_ret, bind_ret_l, interp_state_ret, bind_ret_l.
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
          -- apply ticll_vis...
          -- intros [].
             cleft; apply anr_ret... 
        * cleft; apply anr_ret... 
        * rewrite bind_guard, sb_guard, bind_ret_l, interp_state_ret, bind_ret_l,
            interp_state_ret, bind_ret_l, interp_state_ret, bind_ret_l.
          cleft; apply anr_ret... 
          eexists; intuition.
          eexists; intuition; cbn.
          apply sec_lte_L.
      + rewrite bind_ret_l, bind_guard, sb_guard, bind_ret_l, interp_state_ret,
          bind_ret_l, interp_state_ret, bind_ret_l, interp_state_ret, bind_ret_l.
        cleft; apply anr_ret... 
        eexists; intuition.
        eexists; intuition.
  Qed.
  Print Assumptions ag_safety_sec.
End SecurityEx.
