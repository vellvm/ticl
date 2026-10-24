From Stdlib Require Import
  List
  Lia.

From ExtLib Require Import RelDec.

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
  CTree.Logic.State.

Generalizable All Variables.

Import CTree CTreeNotations TiclNotations ListNotations.
Local Open Scope ticl_scope.
Local Open Scope ctree_scope.
Local Open Scope list_scope.

(** * MeQ: A queue language with instrumentation *)
(** CTrees are a denotational model for programming languages with events, nondeterminism and infinite loops.
    In this module, we demonstrate the common patterns for reasoning with CTrees and Ticl, and introduce a queue language with instrumentation.

    There are two events
    [Push] pushes a value to the queue, and [Pop] pops a value from the queue.
    The queue is represented as a list of values.

    The semantics of those events are given in terms of instrumentation handler
    [h_queueE], which is a state monad
    that also keeps track of the successfully popped elements, while ignoring
    pushes. Different temporal specifications might require different
    instrumentation handlers. Ticl offers flexibility in that regard.

    The language is used in [examples/Queue.v] to prove the always-eventually liveness property for a round-robin queue.
*)
Module ME.
  #[local] Parameter (T: Type) 
    (HDec: RelDec (@eq T)) 
    (HCor: RelDec_Correct HDec).
  #[global] Existing Instance HDec.
  #[global] Existing Instance HCor.

  (** Queue events, indexed by their result type: [Pop] returns [None] if the queue is empty, and [Some x] if the head of the queue is [x] *)
  Variant queueE : Type -> Type :=
  | Push (s: T) : queueE unit
  | Pop : queueE (option T).

  Section MeQ.
    (** [B]: branch signature of the denotation (queue programs do not branch) *)
    Context {B: Type -> Type}.

    Definition push : T -> ctree queueE B unit :=
      fun (s: T) => CTree.trigger (Push s).

    Definition pop : ctree queueE B (option T) :=
      CTree.trigger Pop.

    Arguments push /.
    Arguments pop /.

    Definition Q := list T.

    (** Queue instrumentation handler [h_queueE]. Emit [writeE] events for [Pop] events, recording the successfully popped elements. *)
    Definition h_queueE: queueE ~> stateT Q (ctreeW T B) :=
      fun _ e q =>
        match e in queueE X return ctreeW T B (Q * X) with
        | Push v => Ret (q ++ [v], tt)
        | Pop => match q with
                | nil => Ret (nil, None)
                | h :: ts =>
                    log h ;; (* Instrument the head of the queue [h] at pop *)
                    Ret (ts, Some h)
                end
        end.

    (** * The syntax of queue programs *)
    (** It includes [Pop], [Push], [IfSome], [UntilNone], [Ret], [Bind] commands.
  We chose [IfSome] for control flow as we already have options in the language, as the result of [Pop] is an option.
  The same is true for [UntilNone], which represents a loop that terminates when the result of the loop is [None].
     *)
    Inductive CProg : Type -> Type :=
    | CPop : CProg (option T)
    | CPush (x: T): CProg unit
    | CIfSome{X} (c: option X) (t: X -> CProg unit): CProg unit
    | CUntilNone {A} (b: CProg (option A)) : CProg unit
    | CRet {A}(a: A): CProg A
    | CBind {A B}(l: CProg A) (k: A -> CProg B): CProg B.

    Fixpoint cdenote_prog {A}(s: CProg A): ctree queueE B A :=
      match s with
      | CPop => pop
      | CPush x => push x
      | CIfSome c t =>
          match c with
          | Some x => cdenote_prog (t x)
          | None => Ret tt
          end
      | CUntilNone b =>
          CTree.iter
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

    (** Instrumentation of queue programs *)
    Definition instr_prog {X}(p: CProg X): Q -> ctreeW T B (Q * X) :=
      interp_state h_queueE (cdenote_prog p).

    (** Unfold an interpreted trigger into its handler, up to the administrative guard. *)
    Local Ltac unfold_trigger :=
      rewrite interp_state_trigger; cbn;
      change (Monad.bind ?a ?b) with (CTree.bind a b).

    (** We lift the structural Ticl lemmas to the level of MeQ programs. *)
    (** Pop lemmas *)
    Lemma axr_pop_nil: forall w,
        not_done w ->
        <[ {instr_prog CPop nil}, w |= AX (done= {(nil, None)} w) ]>.
    Proof with auto with ticl.
      intros; unfold instr_prog; cbn.
      unfold_trigger.
      rewrite bind_ret_l, sb_guard.
      apply axr_ret...
    Qed.

    Lemma anr_pop_cons: forall w h ts φ,
        not_done w ->
        <( {log h: ctreeW T B unit}, w |= φ )> ->
        <[ {instr_prog CPop (h::ts)}, w |= φ AN AX (done= {(ts, Some h)} {Obs (Log h) tt}) ]>.
    Proof with auto with ticl.
      intros; unfold instr_prog; cbn.
      unfold_trigger.
      rewrite bind_bind.
      apply anr_log.
      - rewrite bind_ret_l, sb_guard.
        apply axr_ret...
      - now apply ticll_bind_l.
    Qed.

    Lemma aur_pop_cons: forall w h ts φ,
        not_done w ->
        <( {log h: ctreeW T B unit}, w |= φ )> ->
        <[ {instr_prog CPop (h::ts)}, w |= φ AU AX (done= {(ts, Some h)} {Obs (Log h) tt}) ]>.
    Proof with auto with ticl.
      intros; unfold instr_prog; cbn.
      cright.
      apply implr_auan_anau.
      cleft.
      apply anr_pop_cons...
    Qed.

    Lemma axr_push: forall w x q,
        not_done w ->
        <[ {instr_prog (CPush x) q}, w |= AX (done= {(q ++ [x], tt)} w) ]>.
    Proof with auto with ticl.
      intros; unfold instr_prog; cbn.
      unfold_trigger.
      rewrite bind_ret_l, sb_guard.
      apply axr_ret...
    Qed.

    (** Ret lemmas *)
    Lemma axr_qprog_ret{X}: forall (x: X) w q R,
        R (q, x) w ->
        not_done w ->
        <[ {instr_prog (CRet x) q}, w |= ret R ]>.
    Proof with eauto with ticl.
      unfold instr_prog; cbn; intros.
      apply axr_state_ret...
    Qed.

    (** Sequence lemmas *)
    Lemma aul_qprog_bind{X Y}: forall (h: CProg X) (k: X -> CProg Y) q q' (r: X) w w' φ ψ,
        <[ {instr_prog h q}, w |= φ AU AX done={(q',r)} w' ]> ->
        <( {instr_prog (k r) q'}, w' |= φ AU ψ )> ->
        <( {instr_prog (CBind h k) q}, w |= φ AU ψ )>.
    Proof with eauto with ticl.
      unfold instr_prog; cbn; intros.
      eapply aul_state_bind_r_eq...
    Qed.

    Lemma aur_qprog_bind_r{X Y}: forall (h: CProg X) (k: X -> CProg Y) q q' (r: X) w w' φ ψ,
        <[ {instr_prog h q}, w |= φ AU AX done={(q',r)} w' ]> ->
        <[ {instr_prog (k r) q'}, w' |= φ AU ψ ]> ->
        <[ {instr_prog (CBind h k) q}, w |= φ AU ψ ]>.
    Proof with eauto with ticl.
      unfold instr_prog; cbn; intros.
      eapply aur_state_bind_r_eq...
    Qed.

    Lemma anr_qprog_bind_l{X Y}: forall (h: CProg X) (k: X -> CProg Y) q q' (r: X) w w' φ ψ,
        <[ {instr_prog h q}, w |= φ AN AX done={(q',r)} w' ]> ->
        <[ {instr_prog (k r) q'}, w' |= ψ ]> ->
        <[ {instr_prog (CBind h k) q}, w |= φ AN ψ ]>.
    Proof with eauto with ticl.
      unfold instr_prog; cbn; intros.
      eapply anr_state_bind_l_eq...
    Qed.

    (** Conditional lemmas *)
    Lemma equivr_ifsome_some{X}: forall (k: X -> CProg unit) q ψ x w,
        <[ {instr_prog (k x) q}, w |= ψ ]> <->
        <[ {instr_prog (CIfSome (Some x) k) q}, w |= ψ ]>.
    Proof with eauto.
      unfold instr_prog; cbn; intros...
    Qed.

    (** While loops use the [iter] lemmas from [Iter.v] and [State.v] *)
    Lemma aul_qprog_until_now{X}: forall w φ ψ (b: CProg (option X)) q,
        <( {instr_prog b q}, w |= φ AU ψ )> ->
        <( {instr_prog (CUntilNone b) q}, w |= φ AU ψ )>.
    Proof with eauto with ticl.
      unfold instr_prog; cbn; intros.
      rewrite unfold_iter, bind_bind.
      now eapply ticll_state_bind_l.
    Qed.

    (** Termination lemma, uses [aur_state_iter_nat] from [State.v] *)
    Theorem aur_qprog_termination {X}(b: CProg (option X)) q (Ri: rel Q (WorldW T)) w (f: Q -> nat) φ ψ:
      Ri q w ->
      not_done w ->
      (forall q w,
          Ri q w ->
          not_done w ->
          exists (opt: option X) q' w',
            not_done w' /\
            <[ {instr_prog b q}, w |= φ AU AX done={(q',opt)} w' ]> /\
              match opt with
              | Some _ => Ri q' w' /\ f q' < f q
              | None => <[ {Ret (q', tt): ctreeW T B (Q * unit)}, w' |= φ AN ψ ]>
              end) ->
      <[ {instr_prog (CUntilNone b) q}, w |= φ AU ψ ]>.
    Proof with eauto with ticl.
      unfold instr_prog; intros; cbn.
      eapply aur_state_iter_nat with
        (Ri:=fun 'tt q w =>
               exists (opt: option X) q' w',
                 not_done w' /\
                 <[ {interp_state h_queueE (cdenote_prog b) q}, w |= φ AU AX done={(q',opt)} w' ]> /\
                   match opt with
                   | Some _ => Ri q' w' /\ f q' < f q
                   | None => <[ {Ret (q', tt): ctreeW T B (Q * unit)}, w' |= φ AN ψ ]>
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

    (** Eventually lemma, uses [aul_state_iter_nat] from [State.v] *)
    Theorem aul_qprog_eventually {X} (b: CProg (option X)) q (Ri: rel Q (WorldW T)) w (f: Q -> nat) φ ψ:
      Ri q w ->
      not_done w ->
      (forall q w,
          Ri q w ->
          not_done w ->
          <[ {instr_prog b q}, w |= φ AU ret {fun '(q', opt) w' => exists x, opt = Some x /\ not_done w' /\ Ri q' w' /\ f q' < f q} ]> \/
          <( {instr_prog b q}, w |= φ AU ψ )>) ->
      <( {instr_prog (CUntilNone b) q}, w |= φ AU ψ )>.
    Proof with eauto with ticl.
      unfold instr_prog; intros; cbn.
      eapply aul_state_iter_nat with
        (Ri:=fun 'tt q w =>
               <[ {interp_state h_queueE (cdenote_prog b) q}, w
                            |= φ AU ret {fun '(q', opt) w' => exists x, opt = Some x /\ not_done w' /\ Ri q' w' /\ f q' < f q} ]> \/
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

    (** Invariance lemma, uses [ag_state_iter] from [State.v] *)
    Lemma ag_qprog_invariance: forall (b: CProg (option unit)) R q w φ,
        R q w ->
        not_done w ->
        (forall q w,
            R q w ->
            not_done w ->
            <( {instr_prog (CUntilNone b) q}, w |= φ )> /\
            <[ {instr_prog b q}, w |= AX (φ AU ret {fun '(q', r) w' => r = Some tt /\ not_done w' /\ R q' w'}) ]>) ->
        <( {instr_prog (CUntilNone b) q}, w |= AG φ )>.
    Proof with eauto with ticl.
      unfold instr_prog; cbn.
      intros.
      eapply ag_state_iter with
        (R:=fun 'tt q w =>
              <( {interp_state h_queueE (cdenote_prog (CUntilNone b)) q}, w |= φ )> /\
                <[ {interp_state h_queueE (cdenote_prog b) q}, w
                   |= AX (φ AU ret {fun '(q', r) w' => r = Some tt /\ not_done w' /\ R q' w'}) ]>)...
      - intros [] q' w' Hd (Hl & HR); cbn in Hl; split...
        rewrite interp_state_bind.
        eapply axr_aur_bind_r; [exact HR |].
        intros [q_ r_] w'' (-> & Hd'' & HR').
        apply aur_state_ret...
    Qed.
  End MeQ.
End ME.
