From TICL Require Import CTree.Core Events.WriterE Logic.Core Logic.Simulation
  CTree.Logic.Sim CTree.Logic.CanStep CTree.Logic.AX CTree.Logic.AF CTree.Logic.Bind
  CTree.Logic.Iter CTree.Logic.State CTree.Logic.Soundness.
From TICL Require Import CTree.Events.Writer CTree.Interp.State.Mod.
From TICL Require Lang.StImp Lang.HeapImp.
From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Strings.String.
Import CTreeNotations TiclNotations.
Local Open Scope ctree_scope.
Local Open Scope ticl_scope.
Generalizable All Variables.

Section Grammar.
Context {E : Type -> Type} {X : Type}.
Variables (P Q : World E -> Prop) (R : X -> World E -> Prop).
Variables (p q : ticll E) (r s : ticlr E X).
Check (<( now P AU now Q )> : ticll E).
Check (<( p AU ret R )> : ticlr E X).
Check (<( (p /\ AG q) AU (r \/ AX s) )> : ticlr E X).
Check (<( p AU q )> : ticll E).
Fail Check (<( ret R )> : ticll E).
Fail Check (<( ⊤ )> : ticlr E X).
Fail Check <( r AU s )>.
Fail Check <( p /\ r )>.
Fail Check (CAnd r (CRet (fun (_ : bool) (_ : World E) => True))).
Fail Check (contramap (fun x : X => x) p).
Fail Check (contramap (fun _ : bool => true) r).
Example boolean_precedence : <( p \/ q /\ p )> = CAnd (COr p q) p.
Proof. reflexivity. Qed.
End Grammar.

Section SharedTactics.
Context `{KMS : Kripke M E B} {X : Type}.
Variables (t : M E B X) (w : World E) (b : bool) (f g : ticl_at E X b).
Variables (p q : ticll E) (r s : ticlr E X).
Goal entails X b f t w -> entails X b g t w -> entails X b (CAnd f g) t w.
Proof. intros Hf Hg; csplit. exact Hf. exact Hg. Qed.
Goal entails X b (CAnd f g) t w -> entails X b f t w.
Proof. intro H; cdestruct H. assumption. Qed.
Goal <( t,w |=R r )> -> <( t,w |=R s )> -> <( t,w |=R r /\ s )>.
Proof. intros Hr Hs; csplit. exact Hr. exact Hs. Qed.
Goal <( t,w |=L p /\ q )> -> <( t,w |=L p )>.
Proof. intro H; cdestruct H. assumption. Qed.
Goal equiv_ticl X b f g -> entails X b f t w -> entails X b g t w.
Proof. intros He Hf; ticl_normalize; rewrite <- He; exact Hf. Qed.
Goal entails X b (CAnd f g) t w -> True.
Proof. intro H; ticl_normalize in H; lazymatch type of H with @entails _ _ _ _ _ _ (CAnd _ _) _ _ => exact I end. Qed.
End SharedTactics.
Section AbstractMode.
Context {E B : Type -> Type} {X : Type} (b : bool).
Variables (t : ctree E B X) (w : World E) (phi : ticll E) (psi : ticl_at E X b).
Goal entails X false phi (Step t) w -> entails X b psi t w -> entails X b (Cx Q_A phi psi) (Step t) w.
Proof. intros Hp Hr; apply (an_step (b:=b)); auto. Qed.
Goal entails X false phi (Step t) w -> entails X b (Cu Q_A phi psi) t w -> entails X b (Cu Q_A phi psi) (Step t) w.
Proof. intros Hp Hr; apply (au_step (b:=b)); right; auto. Qed.
End AbstractMode.
Definition changed_input : ctree void1 Bn nat := Ret 1.
Definition changed_k : nat -> ctree void1 Bn bool := fun _ => Ret true.
Goal entails bool false (CNow (fun _ => True)) (CTree.bind changed_input changed_k) Pure.
Proof.
 eapply ticl_bind_ret with (R:=fun n w => n = 1 /\ w = Pure).
 - apply ret_ret; constructor; auto.
 - intros n w [-> ->]; apply ticl_now; split; constructor.
Qed.
Goal entails bool true (CRet (fun x _ => x = true)) (CTree.bind changed_input changed_k) Pure.
Proof.
 eapply ticl_bind_ret with (R:=fun n w => n = 1 /\ w = Pure).
 - apply ret_ret; constructor; auto.
 - intros n w [-> ->]; apply ret_ret; constructor; auto.
Qed.
Theorem changed_until_prefix : forall q, entails bool false (Cu q (CNow (fun _ => True)) (CNow (fun _ => True))) (CTree.bind changed_input changed_k) Pure.
Proof.
 intro q; eapply (u_bind_r (b:=false) q) with (R:=fun n w => n = 1 /\ w = Pure).
 - cleft; apply ret_ret; constructor; auto.
 - intros n w [-> ->]; cleft; apply ticl_now; split; constructor.
Qed.
Theorem changed_until_suffix : forall q, entails bool true (Cu q (CNow (fun _ => True)) (CRet (fun x _ => x = true))) (CTree.bind changed_input changed_k) Pure.
Proof.
 intro q; eapply (u_bind_r (b:=true) q) with (R:=fun n w => n = 1 /\ w = Pure).
 - cleft; apply ret_ret; constructor; auto.
 - intros n w [-> ->]; cleft; apply ret_ret; constructor; auto.
Qed.
Check (changed_until_prefix Q_A).
Check (changed_until_prefix Q_E).
Check (changed_until_suffix Q_A).
Check (changed_until_suffix Q_E).
Definition countdown (n : nat) : ctree void1 Bn (nat + bool) :=
 match n with 0 => Ret (inr true) | S n => Step (Ret (inl n)) end.
Section Countdown.
Variable b : bool.
Variable p : ticl_at void1 bool b.
Hypothesis Hexit : forall w, not_done w -> entails bool b p (Ret true : ctree void1 Bn bool) w.
Theorem countdown_indexed : forall n, entails bool b (Cu Q_A (CNow (fun _ => True)) p) (iter countdown n) Pure.
Proof.
 intro n; eapply (u_iter_nat (b:=b) Q_A (fun (_:nat) w => not_done w) (fun n _ => n)).
 - constructor.
 - intros [|s] w Hw; cbn [countdown].
   + cleft; apply ret_ret; [exact Hw | cbn; apply Hexit; exact Hw].
   + apply (au_step (b:=true)); right; split.
     * apply ticl_now; auto.
     * cleft; apply ret_ret; [exact Hw | cbn; split; [exact Hw | apply Nat.lt_succ_diag_r]].
Qed.
End Countdown.
Goal forall n, entails bool true (Cu Q_A (CNow (fun _ => True)) (CRet (fun x _ => x = true))) (iter countdown n) Pure.
Proof. apply countdown_indexed; intros; apply ret_ret; auto. Qed.
Goal forall n, entails bool false (Cu Q_A (CNow (fun _ => True)) (CNow (fun _ => True))) (iter countdown n) Pure.
Proof. apply countdown_indexed; intros; apply ticl_now; auto. Qed.


Section StateIndex.
Context {E B : Type -> Type} {S W X Y : Type}.
Variable h : forall T, E T -> stateT S (ctreeW W B) T.
Variable s : S.
Variable b : bool.
Variables (t : ctree E B Y) (k : Y -> ctree E B X) (w : WorldW W).
Variables (phi : ticllW W) (psi : ticl_at (writerE W) (S * X) b) (R : Y -> S -> WorldW W -> Prop).
Goal entails (S * Y) true (Cu Q_A phi (CRet (fun '(s,y) => R y s))) (interp_state h t s) w ->
 (forall y s' w', R y s' w' -> entails (S * X) b (Cu Q_A phi psi) (interp_state h (k y) s') w') ->
 entails (S * X) b (Cu Q_A phi psi) (interp_state h (CTree.bind t k) s) w.
Proof. apply (au_state_bind_r h s (b:=b)). Qed.
End StateIndex.

Definition state_countdown (n : nat) : ctree (stateE nat) Bn (nat + bool) :=
  match n with
  | 0 => Ret (inr true)
  | S k => TICL.CTree.Core.put k ;; Ret (inl k)
  end.

Section StatefulCountdown.
Variable b : bool.
Variable p : ticl_at (writerE nat) (nat * bool) b.
Hypothesis Hexit : entails (nat * bool) b p
  (Ret (0,true) : ctreeW nat Bn (nat * bool)) (Obs (Log 0) tt).

Example state_countdown_indexed (q : ticlq) :
  entails (nat * bool) b (Cu q (CNow (fun _ => True)) p)
    (instr_stateE (iter state_countdown 2) 2) Pure.
Proof.
  unfold instr_stateE.
  eapply (u_state_iter (b:=b) h_stateW 2 q
    (fun i s (w : WorldW nat) => s = i /\ (i = 0 -> w = Obs (Log 0) tt))
    (ltof _ (fun '(i,s,w) => i))).
  - apply well_founded_ltof.
  - constructor.
  - split; [reflexivity|discriminate].
  - intros [|n] sigma w Hd [-> Hlast]; cbn [state_countdown].
    + rewrite interp_state_ret; cleft;
        (apply ret_ret; [exact Hd|cbn; rewrite (Hlast eq_refl); exact Hexit]).
    + rewrite interp_state_bind, interp_state_put, bind_bind.
      setoid_rewrite bind_ret_l; setoid_rewrite interp_state_ret; cbn [fst].
      destruct q; [apply (af_log (b:=true)) | apply (ef_log (b:=true))];
        try exact Hd;
        (cleft; apply ret_ret; [constructor|cbn; split; [constructor|split;
          [split; [reflexivity|intros ->; reflexivity]|
           unfold ltof; cbn; apply Nat.lt_succ_diag_r]]]).
Qed.
End StatefulCountdown.

Example state_countdown_suffix q :
  entails (nat * bool) true
    (Cu q (CNow (fun _ => True)) (CRet (fun result _ => result = (0,true))))
    (instr_stateE (iter state_countdown 2) 2) Pure.
Proof.
  apply (state_countdown_indexed true); apply ret_ret;
    [constructor|reflexivity].
Qed.

Example state_countdown_prefix q :
  entails (nat * bool) false (Cu q (CNow (fun _ => True)) <(visW {eq 0})>)
    (instr_stateE (iter state_countdown 2) 2) Pure.
Proof.
  apply (state_countdown_indexed false); apply ticl_vis;
    constructor; reflexivity.
Qed.

Section Derivations.
Context {E B : Type -> Type} {X : Type} (b : bool).
Variables (t : ctree E B X) (w : World E)
  (phi : ticll E) (psi : ticl_at E X b).
Example derivation_guard : syntails X b t w psi ->
  syntails X b (Guard t) w psi.
Proof. apply SynGuard. Qed.
Example derivation_until_step : syntails X false (Step t) w phi ->
  syntails X b t w (Cu Q_A phi psi) ->
  entails X b (Cu Q_A phi psi) (Step t) w.
Proof. intros Hp Hs; eapply soundness; eapply SynAuStepL; eassumption. Qed.
End Derivations.

Example derivation_now :
  syntails nat false (Ret 1 : ctree void1 Bn nat) Pure (CNow (fun _ => True)).
Proof. apply SynNow; constructor. Qed.
Example derivation_ret :
  syntails nat true (Ret 1 : ctree void1 Bn nat) Pure (CRet (fun n _ => n = 1)).
Proof. apply SynRet; constructor. Qed.

Section Simulation.
Context {E B : Type -> Type} {X : Type}.
Variable RV : X -> X -> Prop.
Variables (p : ticll E) (r : ticlr E X) (t t' : ctree E B X) (w w' : World E).
Example prefix_simulation : csim event_eq RV t t' -> entails X false p t w ->
  entails X false p t' w.
Proof.
  intros Hsim Hp; apply (proj1 (framer_event_eq X false RV p t' w)).
  eapply (ticl_csim false event_eq RV p).
  - exact I.
  - exact Hsim.
  - apply simW_refl; [apply event_eq_refl|eapply ticl_not_done; exact Hp].
  - exact Hp.
Qed.
Example suffix_simulation :
  (forall x y1 y2, RV x y1 -> RV x y2 -> y1 = y2) ->
  csim event_eq RV t t' -> simW event_eq RV w w' -> entails X true r t w ->
  entails X true (framer X true event_eq RV r) t' w'.
Proof.
  intros Hu Hsim Hw Hr; eapply (ticl_csim true event_eq RV r).
  - split; [apply event_eq_right_unique|exact Hu].
  - exact Hsim.
  - exact Hw.
  - exact Hr.
Qed.
End Simulation.

Section JudgmentEntrypoints.
Context `{KMS : Kripke M E B} {X Y : Type}.
Variables (t : M E B X) (u : M E B Y) (w : World E).
Variables (p q : ticll E) (r s : ticlr E X).

Definition prefix_X : Prop := <( t,w |=L p )>.
Definition prefix_Y : Prop := <( u,w |=L p )>.
Definition suffix_X : Prop := <( t,w |=R r )>.
Definition prefix_domain_X : M E B X -> World E -> Prop := entailsL X p.
Definition prefix_domain_Y : M E B Y -> World E -> Prop := entailsL Y p.
Definition suffix_domain_X : M E B X -> World E -> Prop := entailsR r.
Fail Definition suffix_domain_Y : M E B Y -> World E -> Prop := entailsR r.
Check (entailsL X p).
Check (entailsL Y p).
Check (entailsR r).
Definition truth_quote : Prop := <( t,w |=L ⊤ )>.
Definition return_quote : Prop :=
  <( t,w |=R AX (ret {fun _ _ => True}) )>.
Check <( t,w |=L p )>.
Check <( t,w |=R r )>.
Check <( t,w |=R (p /\ AG q) AU (r \/ AX s) )>.
Fail Definition wrong_independent_result : Prop := <( u,w |=R r )>.
Fail Definition wrong_L_sort : Prop := <( t,w |=L r )>.
Fail Definition wrong_R_sort : Prop := <( t,w |=R p )>.
Variable i : option Type.
Variable unknown : ticl E i.
Fail Definition unknown_L_index : Prop := <( t,w |=L unknown )>.
Fail Definition unknown_R_index : Prop := <( t,w |=R unknown )>.
Variable wrong : ticlr E (X -> False).
Fail Definition wrong_result_judgment : Prop := <( t,w |=R wrong )>.

Goal <( t,w |=L p )> -> <( t,w |=L q )> -> <( t,w |=L p /\ q )>.
Proof.
  intros Hp Hq; csplit.
  Show.
  - exact Hp.
  - exact Hq.
Qed.
Goal <( t,w |=R r )> -> <( t,w |=R s )> -> <( t,w |=R r /\ s )>.
Proof.
  intros Hr Hs; csplit.
  Show.
  - exact Hr.
  - exact Hs.
Qed.
Goal <( t,w |=L p /\ q )> -> <( t,w |=L p )>.
Proof. intro H; cdestruct H. Show. assumption. Qed.
Goal <( t,w |=R r /\ s )> -> <( t,w |=R r )>.
Proof. intro H; cdestruct H. Show. assumption. Qed.

Goal <( t,w |=L p /\ q )> -> True.
Proof.
  intro H; ticl_normalize in H.
  lazymatch type of H with
  | @entails _ _ _ _ _ false (CAnd _ _) _ _ => exact I
  end.
Qed.
Goal <( t,w |=R r /\ s )> -> True.
Proof.
  intro H; ticl_normalize in H.
  lazymatch type of H with
  | @entails _ _ _ _ _ true (CAnd _ _) _ _ => exact I
  end.
Qed.

Goal <( t,w |=L p )> -> <( t,w |=L p \/ q )>.
Proof. intro H; cleft; exact H. Qed.
Goal <( t,w |=L q )> -> <( t,w |=L p \/ q )>.
Proof. intro H; cright; exact H. Qed.
Goal <( t,w |=R r )> -> <( t,w |=R r \/ s )>.
Proof. intro H; cleft; exact H. Qed.
Goal <( t,w |=R s )> -> <( t,w |=R r \/ s )>.
Proof. intro H; cright; exact H. Qed.
Goal <( t,w |=L p \/ q )> -> <( t,w |=L q \/ p )>.
Proof. intro H; cdestruct H; [cright | cleft]; exact H. Qed.
Goal <( t,w |=R r \/ s )> -> <( t,w |=R s \/ r )>.
Proof. intro H; cdestruct H; [cright | cleft]; exact H. Qed.

(* A variable path quantifier exercises both common until-induction branches.
   The endpoint mode stays fixed by each tag; no mode is destructed. *)
Goal forall z : ticlq, <( t,w |=L {Cu z p q} )> -> not_done w.
Proof. intros z H; eapply ticl_not_done; eassumption. Qed.
Goal forall z : ticlq, <( t,w |=R {Cu z p r} )> -> not_done w.
Proof. intros z H; eapply ticl_not_done; eassumption. Qed.

Goal forall z : ticlq, <( t,w |=L {Cg z p} )> -> <( t,w |=L p )>.
Proof. intros z H; step in H; exact (proj1 H). Qed.
(* Globals have prefix sort. For a suffix consumer, expose its global guard
   with the common next law before stepping that guard. *)
Goal forall z : ticlq,
  <( t,w |=R {Cg z p} AN r )> -> <( t,w |=L p )>.
Proof.
  intros z H; apply ticl_an in H as (H & _ & _).
  step in H; exact (proj1 H).
Qed.

(* These rewrites must succeed through the public entrypoints themselves. *)
Goal equiv_ticl X false p q -> <( t,w |=L p )> -> <( t,w |=L q )>.
Proof. intros He Hp; rewrite <- He; exact Hp. Qed.
Goal equiv_ticl X true r s -> <( t,w |=R r )> -> <( t,w |=R s )>.
Proof. intros He Hr; rewrite <- He; exact Hr. Qed.

Variable b : bool.
Variables f g : ticl_at E X b.
Check (entails X b f t w).
Goal entails X b f t w -> entails X b (COr f g) t w.
Proof. intro H; cleft; exact H. Qed.
Goal entails X b g t w -> entails X b (COr f g) t w.
Proof. intro H; cright; exact H. Qed.
Goal entails X b (COr f g) t w -> entails X b (COr g f) t w.
Proof. intro H; cdestruct H; [cright | cleft]; exact H. Qed.
Goal forall z : ticlq, entails X b (Cu z p f) t w -> not_done w.
Proof. intros z H; eapply ticl_not_done; eassumption. Qed.
Goal forall z : ticlq,
  entails X b (Cx Q_A (Cg z p) f) t w -> entails X false p t w.
Proof.
  intros z H; apply ticl_an in H as (H & _ & _).
  step in H; exact (proj1 H).
Qed.
End JudgmentEntrypoints.

Section EntrypointModelRewriting.
Context `{KS : KripkeSetoid M E B X meq}.
Variables (t u : M E B X) (w : World E).
Variables (p : ticll E) (r : ticlr E X).
Goal meq t u -> (<( t,w |=L p )> <-> <( u,w |=L p )>).
Proof. intro H; now rewrite H. Qed.
Goal meq t u -> (<( t,w |=R r )> <-> <( u,w |=R r )>).
Proof. intro H; now rewrite H. Qed.
End EntrypointModelRewriting.

Section EntrypointCTreeRewriting.
Context {E B : Type -> Type} {X : Type}.
Variables (t : ctree E B X) (w : World E).
Variables (p : ticll E) (r : ticlr E X).
Goal <( {Guard t},w |=L p )> <-> <( t,w |=L p )>.
Proof. now rewrite sb_guard. Qed.
Goal <( {Guard t},w |=R r )> <-> <( t,w |=R r )>.
Proof. now rewrite sb_guard. Qed.
End EntrypointCTreeRewriting.

(** A bare logger must inhabit the logical model's result universe, not only
    the universe chosen for the event reply. Joint kernel checking with the
    framing examples exercises that distinction. *)
Section LoggedReturn.
Context {S : Type} {B : Type -> Type}.
Example log_native_return (s : S) :
  <( {CTree.Events.Writer.log (B:=B) s}, Pure
     |=R AX ret {fun result w => result = tt /\ w = Obs (Log s) tt} )>.
Proof.
  ticl_normalize; unfold CTree.Events.Writer.log.
  apply (an_vis (b:=true) _ _ tt); split.
  - apply ticl_now; split; constructor.
  - intros []; apply ret_ret; [constructor | split; reflexivity].
Qed.
End LoggedReturn.

Module StoreExtension.
Import StImp.StImp.
Definition x : string := "x"%string.
Check <( var x = 0 )>.
Check <( var x < 1 )>.
Check <( var x <= 1 )>.
Check <( var x > 0 )>.
Check <( var x >= 0 )>.
End StoreExtension.

Module HeapExtension.
Import HeapImp.HeapImp.
Local Open Scope heapimp_scope.
Definition x : string := "x"%string.
Check (<p{ x =? 0 }> : Mem -> Prop).
Check (<( obs <p{ x =? 0 }> )> : ticll (writerE Mem)).
End HeapExtension.

Section ReturnMapping.
Context {E : Type -> Type}.
Check (eq_refl : ticll E = ticl E None).
Check (eq_refl : ticlr E nat = ticl E (Some (nat : Type))).
Definition mapped_source : ticlr E nat :=
  Cu Q_A (CNow (fun _ => True)) (CRet (fun n _ => n = 1)).
Example return_mapping :
  contramap (fun b : bool => if b then 1 else 0) mapped_source =
  Cu Q_A (CNow (fun _ => True))
    (CRet (fun (b : bool) _ => (if b then 1 else 0) = 1)).
Proof. reflexivity. Qed.
End ReturnMapping.
