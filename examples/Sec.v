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
         (CRead L i)
         (CRead L (S i)))
      (fun _=> CRet tt).

  Definition sched (secret: nat): SProg unit :=
    SLoop 0
      (fun i =>
         SBr
           (SBind (SCall (alice secret i))
              (fun _ => SRet (1 + i)))
           (SBind (SCall (bob i))
              (fun _ => SRet (1 + i)))).
  
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
    split;[csplit; auto|].
    apply anr_sprog_br. 
    - csplit...
    - (* Alice goes *)
      unfold alice.
      eapply aur_sprog_bind_r with (R:=fun 'tt m w => exists s'0 : SecObs,
                                             w = Obs (Log s'0) tt /\ al s'0 ⪯ ml s'0
                                             /\ (forall i0 : Addr, no_leak i0 m))... 
      + intros [] * HR.
        cleft.
        unfold instr_sprog; cbn.
        apply axr_state_ret...
        destruct HR as (s_ & -> & ?)...
      + apply ticlr_sprog_call, ticlr_cprog_if.
        destruct (Nat.Even_Odd_dec i); unfold instr_cprog; cbn.
        * (* Alice runs, [i] is even *)
          rewrite (@interp_state_trigger _ _ _ _ _ _ (Write H (S i) secret) _); cbn.
          rewrite bind_ret_l, sb_guard.
          cleft; apply anr_ret...
          -- csplit...
          -- exists s'; intuition.
             intros Heven.
             destruct (Hm0 i0 Heven) as (v & ?); exists v.
             destruct (Nat.eq_dec i0 (S i)).
             ++ (* i0 = S i *)
               rewrite e0 in Heven.
               exfalso.
               apply Nat.Even_succ in Heven.
               apply Nat.Even_Odd_False with i...
             ++ (* i0 <> i *)
               rewrite OF.(mapsto_lookup).
               apply mapsto_add_neq with (R:=eq); auto.
               now rewrite <- mapsto_lookup.
        * (* Alice runs, [i] is odd *)
          rewrite (@interp_state_trigger _ _ _ _ _ _ (Write H i secret) _); cbn.
          rewrite bind_ret_l, sb_guard.
          cleft; apply anr_ret...
          -- csplit...
          -- exists s'; intuition.
             intros Heven.
             destruct (Hm0 i0 Heven) as (v & ?); exists v.
             destruct (Nat.eq_dec i0 i).
             ++ (* i0 = i *)
               rewrite e in Heven.
               exfalso.
               apply Nat.Even_Odd_False with i...
             ++ (* i0 <> i *)
               rewrite OF.(mapsto_lookup).
               apply mapsto_add_neq with (R:=eq); auto.
               now rewrite <- mapsto_lookup.
    - (* Bob runs, [i] is even *)
      unfold bob.
      eapply aur_sprog_bind_r with (R:=fun 'tt m w => exists s'0 : SecObs,
                                           w = Obs (Log s'0) tt /\ al s'0 ⪯ ml s'0
                                           /\ (forall i0 : Addr, no_leak i0 m))...
      + intros [] * HR.
        cleft.
        apply axr_state_ret...
        destruct HR as (s_ & -> & ?)...
      + eapply ticlr_sprog_call.        
        eapply aur_cprog_bind_r with (R:=fun _ m w =>
                                           exists s'0 : SecObs,
                                             w = Obs (Log s'0) tt /\ al s'0 ⪯ ml s'0
                                             /\ (forall i0 : Addr, no_leak i0 m))...
        * intros.
          cleft.
          apply axr_state_ret...
          destruct H1 as (? & -> & ?)...
        * apply ticlr_cprog_if.          
          destruct (Nat.Even_Odd_dec i); unfold instr_cprog; cbn.
          -- (* Bob runs, [i] is even *)
             rewrite (@interp_state_trigger _ _ _ _ _ _ (Read L i) _); cbn.
             destruct (Hm0 _ e) as (v & ?).
             rewrite H1.
             rewrite bind_bind.             
             eapply aur_log...
             ++ rewrite bind_ret_l, sb_guard.
                cleft.
                apply axr_ret...
             ++ csplit...
          -- (* Bob runs, [i] is odd *)
            rewrite (@interp_state_trigger _ _ _ _ _ _ (Read L (S i)) _); cbn.
            destruct (lookup (S i) m') eqn:Hlook.
            ++ destruct p as (l, a).
               eapply aur_bind_r_eq; [eapply aur_bind_r_eq|].
               ** apply aur_vis...
                  right; split.
                  --- csplit... 
                  --- intros [].
                      cleft; apply anr_ret...
                      csplit...
               ** cleft; apply anr_ret...
                  csplit...
               ** rewrite sb_guard.
                  cleft.
                  apply axr_ret...
                  eexists; intuition...
                  apply sec_lte_L.
            ++ rewrite bind_ret_l,  sb_guard.
               cleft.
               apply axr_ret...
  Qed.
  Print Assumptions ag_safety_sec.
End Sec.
