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

  Definition h_secE: secE ~> stateT St (ctree void) :=
    fun e => mkStateT
            (fun (st: St) =>                                     
               match e return ctree void (encode e * St) with
               | Read l addr =>                                 
                   match lookup addr st with
                   (* [addr] exists and set to [(v, l_a)] *)
                   | Some (l_a, v) =>
                       (* [l_a ⪯ l] *)
                       if sec_lte_dec l_a l then
                         Ret (Some v, st)
                       else
                         Ret (None, st)
                   (* [addr] does not exist, return [None] *)
                   | None => Ret (None, st)
                   end
               | Write l addr v =>                   
                   match lookup addr st with
                   (* [addr] exists and set to [(_, l_a)] *)
                   | Some (l_a, _) =>
                       (* [l_a ⪯ l] *)
                       if sec_lte_dec l_a l then
                         Ret (tt, add addr (l, v) st)
                       else
                         Ret (tt, st)
                   (* [addr] does not exist, create it *)
                   | None =>
                       Ret (tt, add addr (l, v) st)
                   end
               end).

  (* Ghost state, instrument every read with
     [m: memory address it targets]
     [ml: Security-level of the instruction]
     [al: Security-level of the address cell previously written]
   *)
  Record readG :=
    {
      m : Addr;
      ml: Sec;
      al: Sec;
    }.

  Definition initG :=
    {| m := 0; ml:= L; al:= L |}.
               
  (* Instrumented semantics, simply log every successful read with [readG] *)
  Definition h_secE_instr: secE ~> stateT St (ctreeW readG) :=
    h_writerA
      h_secE
      (fun (e: secE) (_: encode e) (σ: St) =>
         match e with
         | Read al addr =>
             match lookup addr σ with
             | Some (ml, _) => Some {| m:= addr; ml := ml; al := al |}
             | None => None
             end
         | Write _ _ _ => None
         end).

  (* Trigger instructions *)
  Definition read: Sec -> Addr -> ctree secE (option nat) :=
    fun (l: Sec) (addr: Addr) =>
      @Ctree.trigger secE secE _ _ (ReSum_refl) (ReSumRet_refl) (Read l addr).
  
  Definition write: Sec -> Addr -> nat -> ctree secE unit :=
    fun (l: Sec) (addr: Addr) (s: nat) =>
      Ctree.trigger (Write l addr s).

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
  
  Definition noleak(i: Addr) (σ: St) secret : Prop :=
    if Nat.Even_Odd_dec i then
      exists v, lookup i σ = Some (L, v)
    else
      lookup i σ = Some (H, secret).


  Ltac even_odd :=
    match goal with
    | [H: Nat.Even ?x, H': Nat.Even (S ?x) |- _] =>
        exfalso;
        apply Nat.Even_succ in H';
        apply Nat.Even_Odd_False with x; [apply H | apply H']
    | [H: Nat.Odd ?x, H': Nat.Odd (S ?x) |- _] =>
        exfalso;
        apply Nat.Odd_succ in H';
        apply Nat.Even_Odd_False with x; [apply H' | apply H]          
    end.

  From Coq Require Import Lia.

  (* Safety property: there does not exist a memory label [ml] accessed by
     label [al ≺ ml], or there does not exist a low intruction that reads from
     high-security memory *)
  Typeclasses Transparent equ.
  Theorem ag_safety_sec: forall (secret: nat) (σ: St),
      (forall i, noleak i σ secret) ->
      <( {interp_state h_secE_instr (sec_system secret) σ},
         {Obs (Log initG) tt} |= AG visW \s, s.(ml) ⪯ s.(al) )>.
  Proof.
    intros.    
    unfold sec_system, forever.
    apply ag_iter_state_vis with (R:=fun '(i, σ) => noleak i σ secret).
    - now specialize (H0 0).
    - unfold initG.
      econstructor; cbn.
      reflexivity.
    - intros.
      rewrite map_bind, interp_state_bind.
      unfold br2.
      destruct e, v.
      rewrite interp_state_br.
      rewrite bind_br.
      apply ax_br; split; auto with ctl.
      intro i.
      rewrite bind_guard.
      apply au_guard.       
      ddestruction i; unfold sec_alice1, sec_bob1; destruct (Nat.Even_Odd_dec x);
        rewrite <- interp_state_bind;
        setoid_rewrite map_ret;
        rewrite interp_state_bind.
      + (* Alice runs, [x] is even *)
        eapply au_bind_r_eq.
        * rewrite (@interp_state_trigger _ _ _ _ _
                     h_secE_instr (Write H (S x) secret)); cbn.
          rewrite bind_bind.          
          destruct (lookup (S x)%nat s) eqn:Hlook.
          -- destruct p.
             destruct (sec_lte_dec s0 H); inv s1;
               rewrite resumCtree_ret', ?bind_ret_l;
               apply au_guard.
             ++ right; apply ax_done; intuition.
                eexists; split; [|split]; auto.
             ++ right; apply ax_done; intuition.
                eexists; split; [|split]; auto.
          -- rewrite resumCtree_ret', ?bind_ret_l.
             apply au_guard.
             right; apply ax_done; intuition.
             eexists; split; [|split]; auto.
        * cbn.
          rewrite interp_state_ret.
          right; apply ax_done; intuition.
          eexists; intuition.
          exists (Log r), tt; intuition.
          do 2 eexists; intuition.          
          unfold noleak in H1 |- *; intros.
          destruct (Nat.Even_Odd_dec (S x));
            destruct (Nat.Even_Odd_dec x); try even_odd;
            destruct H1 as (v & Hv).
          rewrite mapsto_lookup.
          apply mapsto_add_eq.
      + (* Alice runs, [x] is odd *)
        eapply au_bind_r_eq.
        * rewrite (@interp_state_trigger _ _ _ _ _
                     h_secE_instr (Write H x secret)); cbn.
          rewrite bind_bind.          
          destruct (lookup x s) eqn:Hlook.
          -- destruct p.
             destruct (sec_lte_dec s0 H); inv s1;
               rewrite resumCtree_ret', ?bind_ret_l;
               apply au_guard.
             ++ right; apply ax_done; intuition.
                eexists; split; [|split]; auto.
             ++ right; apply ax_done; intuition.
                eexists; split; [|split]; auto.
          -- rewrite resumCtree_ret', ?bind_ret_l.
             apply au_guard.
             right; apply ax_done; intuition.
             eexists; split; [|split]; auto.
        * cbn.
          rewrite interp_state_ret.
          right; apply ax_done; intuition.
          eexists; intuition.
          exists (Log r), tt; intuition.
          do 2 eexists; intuition.
          unfold noleak in H1 |- *; intros.
          destruct (Nat.Even_Odd_dec (S x));
            destruct (Nat.Even_Odd_dec x); try even_odd.
          admit.
      + (* Bob runs, [x] is even *)
        rewrite interp_state_bind, bind_bind.
        eapply au_bind_r_eq.        
        * rewrite (@interp_state_trigger _ _ _ _ _
                     h_secE_instr (Read L x)); cbn.
          rewrite bind_bind.          
          destruct (lookup x s) eqn:Hlook.
          -- destruct p.
             destruct (sec_lte_dec s0 L); inv s1;
               rewrite resumCtree_ret', ?bind_ret_l, ?Hlook.
             ++ admit. (* A custom lemma for [trigger Log] might be useful *)
             ++ admit.
          -- rewrite resumCtree_ret', bind_ret_l, Hlook, bind_ret_l.
             apply au_guard.
             right.
             apply ax_done; intuition.
             eexists; split; auto.
        * cbn.
          rewrite interp_state_ret, bind_ret_l, interp_state_ret.
          right.
          apply ax_done; intuition.
          eexists; split; auto.
          exists (Log r), tt; intuition.
          do 2 eexists; intuition.
          admit.
      + (* Bob runs, [x] is odd *)
        rewrite interp_state_bind, bind_bind.
        eapply au_bind_r_eq.        
        * rewrite (@interp_state_trigger _ _ _ _ _
                     h_secE_instr (Read L (S x))); cbn.
          rewrite bind_bind.          
          destruct (lookup (S x) s) eqn:Hlook.
          -- destruct p.
             destruct (sec_lte_dec s0 L); inv s1;
               rewrite resumCtree_ret', ?bind_ret_l, ?Hlook.
             ++ admit. (* A custom lemma for [trigger Log] might be useful *)
             ++ admit.
          -- rewrite resumCtree_ret', bind_ret_l, Hlook, bind_ret_l.
             apply au_guard.
             right.
             apply ax_done; intuition.
             eexists; split; auto.
        * cbn.
          rewrite interp_state_ret, bind_ret_l, interp_state_ret.
          right.
          apply ax_done; intuition.
          eexists; split; auto.
          exists (Log r), tt; intuition.
          do 2 eexists; intuition.
          admit.
  Admitted.
                
End SecurityEx.
          
          
          
          
  
