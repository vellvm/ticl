From Coq Require Import
  List
  Lia.

From ExtLib Require Import RelDec.

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
  ICTree.Logic.State.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations ListNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.
Local Open Scope list_scope.

Generalizable All Variables.

Module ME.
  Context {T: Type} {HDec: RelDec (@eq T)} {HCor: RelDec_Correct HDec}.
  Variant queueE : Type :=
  | Push (s: T)
  | Pop.

  Global Instance encode_queueE: Encode queueE :=
    fun e => match e with
          | Push s => unit
          | Pop => option T
          end.
  
  Definition push : T -> ictree queueE unit :=
    fun (s: T) => @ICtree.trigger queueE queueE _ _ (ReSum_refl) (ReSumRet_refl) (Push s).
  
  Definition pop : ictree queueE (option T) :=
    ICtree.trigger Pop.
  
  Arguments push /.
  Arguments pop /.

  Definition Q := list T. 
  
  (* Queue instrumented semantics *)
  Definition h_queueE: queueE ~> stateT Q (ictreeW T) :=
    fun e =>
      mkStateT (fun q =>
                  match e return ictreeW T (encode e * list T) with
                  | Push v => Ret (tt, q ++ [v])
                  | Pop => match q with
                          | nil => Ret (None, nil)
                          | h :: ts =>
                             log h ;; (* Instrument the head of the queue [h] at pop *)
                             Ret (Some h, ts)
                          end
                  end).
  
  Inductive CProg : Type -> Type :=
  | CPop : CProg (option T)
  | CPush (x: T): CProg unit
  | CIfSome{X} (c: option X) (t: X -> CProg unit): CProg unit
  | CUntilNone {A} (b: CProg (option A)) : CProg unit
  | CRet {A}(a: A): CProg A
  | CBind {A B}(l: CProg A) (k: A -> CProg B): CProg B.

  Fixpoint cdenote_prog {A}(s: CProg A): ictree queueE A :=
    match s with
    | CPop => pop
    | CPush x => push x
    | CIfSome c t =>
        match c with
        | Some x => cdenote_prog (t x)
        | None => Ret tt
        end
    | CUntilNone b => 
        ICtree.iter
          (fun _ =>
             vb <- cdenote_prog b ;;
             match vb with
             | Some v => continue
             | None => break
             end) tt
    | CRet x => Ret x
    | CBind l k =>
        x <- cdenote_prog l ;;        
        cdenote_prog (k x)
    end.

  (* Instrumentation of queue programs *)
  Definition instr_prog {X}(p: CProg X): Q -> ictreeW T (X * Q) :=
    interp_state h_queueE (cdenote_prog p).

  (* Pop *)
  Lemma axr_pop_nil: forall w,
      not_done w ->
      <[ {instr_prog CPop nil}, w |= AX (done= {(None, nil)} w) ]>.
  Proof with auto with ticl.
    intros; unfold instr_prog; cbn.
    unfold trigger.
    rewrite interp_state_vis; cbn.
    rewrite bind_ret_l, sb_guard, interp_state_ret.
    apply axr_ret...
  Qed.
  
  Lemma anr_pop_cons: forall w h ts φ,
      not_done w ->
      <( {log h}, w |= φ )> ->
      <[ {instr_prog CPop (h::ts)}, w |= φ AN AX (done= {(Some h, ts)} {Obs (Log h) tt}) ]>.
  Proof with auto with ticl.
    intros; unfold instr_prog; cbn.
    unfold trigger.
    rewrite interp_state_vis; cbn.
    rewrite bind_bind.
    apply anr_log.
    - rewrite bind_ret_l, sb_guard, interp_state_ret.
      unfold resum_ret, ReSumRet_refl.
      apply axr_ret...
    - now apply ticll_bind_l.
  Qed.

  Lemma aur_pop_cons: forall w h ts φ,
      not_done w ->
      <( {log h}, w |= φ )> ->
      <[ {instr_prog CPop (h::ts)}, w |= φ AU AX (done= {(Some h, ts)} {Obs (Log h) tt}) ]>.
  Proof with auto with ticl.
    intros; unfold instr_prog; cbn.
    cright.
    apply implr_auan_anau.
    cleft.
    apply anr_pop_cons...
  Qed.

  Lemma axr_push: forall w x q,
      not_done w ->
      <[ {instr_prog (CPush x) q}, w |= AX (done= {(tt, q ++ [x])} w) ]>.
  Proof with auto with ticl.
    intros; unfold instr_prog; cbn.
    unfold trigger.
    rewrite interp_state_vis; cbn.
    rewrite bind_ret_l, sb_guard, interp_state_ret.
    unfold resum_ret, ReSumRet_refl.
    apply axr_ret...
  Qed.

  (*| Ret lemma |*)
  Lemma axr_qprog_ret{X}: forall (x: X) w q R,
      R (x, q) w ->
      not_done w ->
      <[ {instr_prog (CRet x) q}, w |= AX done R ]>.
  Proof with eauto with ticl.
    unfold instr_prog; cbn; intros.
    rewrite interp_state_ret; subst.
    apply axr_ret...
  Qed.
  
  (*| Sequence lemmas |*)
  Lemma aul_qprog_bind{X Y}: forall (h: CProg X) (k: X -> CProg Y) q q' (r: X) w w' φ ψ,
      <[ {instr_prog h q}, w |= φ AU AX done={(r,q')} w' ]> ->
      <( {instr_prog (k r) q'}, w' |= φ AU ψ )> ->
      <( {instr_prog (CBind h k) q}, w |= φ AU ψ )>.
  Proof with eauto with ticl.
    unfold instr_prog; cbn; intros.
    eapply aul_state_bind_r_eq...
  Qed.

  Lemma aur_qprog_bind_r{X Y}: forall (h: CProg X) (k: X -> CProg Y) q q' (r: X) w w' φ ψ,
      <[ {instr_prog h q}, w |= φ AU AX done={(r,q')} w' ]> ->
      <[ {instr_prog (k r) q'}, w' |= φ AU ψ ]> ->
      <[ {instr_prog (CBind h k) q}, w |= φ AU ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog; cbn; intros.
    eapply aur_state_bind_r_eq...
  Qed.
  
  Lemma anr_qprog_bind_l{X Y}: forall (h: CProg X) (k: X -> CProg Y) q q' (r: X) w w' φ ψ,
      <[ {instr_prog h q}, w |= φ AN AX done={(r,q')} w' ]> ->
      <[ {instr_prog (k r) q'}, w' |= ψ ]> ->
      <[ {instr_prog (CBind h k) q}, w |= φ AN ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog; cbn; intros.
    eapply anr_state_bind_l_eq...
  Qed.

  (*| Conditionals |*)
  Lemma equivr_ifsome_some{X}: forall (k: X -> CProg unit) q ψ x w,
    <[ {instr_prog (k x) q}, w |= ψ ]> <->
    <[ {instr_prog (CIfSome (Some x) k) q}, w |= ψ ]>.
  Proof with eauto.
    unfold instr_prog; cbn; intros...
  Qed.
  
  (*| While loops |*)
  Lemma aul_qprog_until_now{X}: forall w φ ψ (b: CProg (option X)) q,
      <( {instr_prog b q}, w |= φ AU ψ )> ->
      <( {instr_prog (CUntilNone b) q}, w |= φ AU ψ )>.
  Proof with eauto with ticl.
    unfold instr_prog; cbn; intros.
    rewrite unfold_iter, bind_bind.
    now eapply ticll_state_bind_l. 
  Qed.
  
  (* Termination *)
  Theorem aur_qprog_termination {X}(b: CProg (option X)) q (Ri: rel Q (WorldW T)) w (f: Q -> nat) φ ψ:    
    Ri q w ->
    not_done w ->
    (forall q w,
        Ri q w ->
        not_done w ->
        exists (opt: option X) q' w',
          not_done w' /\
          <[ {instr_prog b q}, w |= φ AU AX done={(opt, q')} w' ]> /\
            match opt with
            | Some _ => Ri q' w' /\ f q' < f q
            | None => <[ {Ret (tt, q')}, w' |= φ AN ψ ]>
            end) ->
    <[ {instr_prog (CUntilNone b) q}, w |= φ AU ψ ]>.
  Proof with eauto with ticl.
    unfold instr_prog; intros; cbn.
    eapply aur_state_iter_nat with
      (Ri:=fun 'tt q w =>
             exists (opt: option X) q' w',
               not_done w' /\
               <[ {interp_state h_queueE (cdenote_prog b) q}, w |= φ AU AX done={(opt, q')} w' ]> /\
                 match opt with
                 | Some _ => Ri q' w' /\ f q' < f q
                 | None => <[ {Ret (tt, q')}, w' |= φ AN ψ ]>
                 end)
      (f:= fun _ q _ => f q)...
    - intros [] q' w' Hd (opt & q_ & w_ & Hd' & Hopt & HR).
      eapply aur_state_bind_r_eq...      
      destruct opt eqn:Heqo.
      + (* Some x *)
        apply aur_state_ret; intuition.
      + (* None *)
        apply aur_state_ret; intuition.
  Qed.

  (* Eventually *)
  Theorem aul_qprog_eventually {X} (b: CProg (option X)) q (Ri: rel Q (WorldW T)) w (f: Q -> nat) φ ψ:    
    Ri q w ->
    not_done w ->
    (forall q w,
        Ri q w ->
        not_done w ->
        <[ {instr_prog b q}, w |= φ AU AX done {fun '(opt, q') w' => exists x, opt = Some x /\ not_done w' /\ Ri q' w' /\ f q' < f q} ]> \/
        <( {instr_prog b q}, w |= φ AU ψ )>) ->
    <( {instr_prog (CUntilNone b) q}, w |= φ AU ψ )>.
  Proof with eauto with ticl.
    unfold instr_prog; intros; cbn.
    eapply aul_state_iter_nat with
      (Ri:=fun 'tt q w =>
             <[ {interp_state h_queueE (cdenote_prog b) q}, w
                          |= φ AU AX done {fun '(opt, q') w' => exists x, opt = Some x /\ not_done w' /\ Ri q' w' /\ f q' < f q} ]> \/
               <( {interp_state h_queueE (cdenote_prog b) q}, w |= φ AU ψ )>)
      (f:= fun _ q _ => f q)...
    - intros [] q' w' Hd [HR | HR].
      + (* Steps *)
        right.
        eapply aur_state_bind_r.
        * apply HR.
        * cbn; intros opt q_ w_ (x_ & Heqx_ & Hd_ & HR_ & Hf_); subst.
          apply aur_state_ret...
          exists tt; intuition...
      + (* Matches *)
        left.
        apply ticll_state_bind_l...
  Qed.

  (* Invariance *)
  Lemma ag_qprog_invariance: forall (b: CProg (option unit)) R q w φ,
      R q w ->
      not_done w ->
      (forall q w,
          R q w ->
          not_done w ->
          <( {instr_prog (CUntilNone b) q}, w |= φ )> /\
          <[ {instr_prog b q}, w |= AX (φ AU AX done {fun '(r, q') w' => r = Some tt /\ not_done w' /\ R q' w'}) ]>) ->
      <( {instr_prog (CUntilNone b) q}, w |= AG φ )>.
  Proof with eauto with ticl.
    unfold instr_prog; cbn.
    intros.
    eapply ag_state_iter with
      (R:=fun 'tt q w =>
            <( {interp_state h_queueE (cdenote_prog (CUntilNone b)) q}, w |= φ )> /\
              <[ {interp_state h_queueE (cdenote_prog b) q}, w
                 |= AX (φ AU AX done {fun '(r, q') w' => r = Some tt /\ not_done w' /\ R q' w'}) ]>)...
    - intros [] q' w' Hd (Hl & HR); cbn in Hl; split...
      rewrite interp_state_bind.
      cdestruct HR.
      csplit...      
      + destruct Hs as (t_ & w_ & TR).
        eapply can_step_bind_l...
        specialize (HR _ _ TR).
        now apply aur_not_done in HR.
      + intros t_ w_ TR...
        apply ktrans_bind_inv in TR as [(? & TR & Hd_ & ->) | (([] & ctx_) & ? & ? & ? & TR)].
        * specialize (HR _ _ TR).
          apply aur_bind_r with (R:=fun '(r, q') w' => r = Some tt /\ not_done w' /\ R q' w')... 
          intros [r_ q_] w'' (-> & Hd'' & HR').
          apply aur_state_ret...
        * specialize (HR _ _ H2).
          now apply aur_stuck, anr_stuck in HR.
        * specialize (HR _ _ H2).
          now apply aur_stuck, anr_stuck in HR.
  Qed.

End ME.
