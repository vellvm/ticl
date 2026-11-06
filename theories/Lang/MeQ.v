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
        <( {instr_prog CPop nil}, w |=R ret= {(nil, None)} w )>.
    Proof.
      intros; unfold instr_prog; cbn.
      unfold_trigger.
      rewrite bind_ret_l, sb_guard.
      apply ret_ret; auto with ticl.
    Qed.

    Lemma anr_pop_cons: forall w h ts (φ : ticll (writerE T)),
        not_done w ->
        <( {log h: ctreeW T B unit}, w |=L φ )> ->
        <( {instr_prog CPop (h::ts)}, w |=R φ AN ret= {(ts, Some h)} {Obs (Log h) tt} )>.
    Proof.
      intros; unfold instr_prog; cbn.
      unfold_trigger.
      rewrite bind_bind.
      apply (an_log (b:=true)).
      - rewrite bind_ret_l, sb_guard.
        apply ret_ret; auto with ticl.
      - now apply ticll_bind_l.
    Qed.

    Lemma aur_pop_cons: forall w h ts (φ : ticll (writerE T)),
        not_done w ->
        <( {log h: ctreeW T B unit}, w |=L φ )> ->
        <( {instr_prog CPop (h::ts)}, w |=R φ AU ret= {(ts, Some h)} {Obs (Log h) tt} )>.
    Proof.
      intros; unfold instr_prog; cbn.
      cright.
      apply (impl_auan_anau (b:=true) φ _ _ w).
      cleft.
      apply anr_pop_cons; auto with ticl.
    Qed.

    Lemma axr_push: forall w x q,
        not_done w ->
        <( {instr_prog (CPush x) q}, w |=R ret= {(q ++ [x], tt)} w )>.
    Proof.
      intros; unfold instr_prog; cbn.
      unfold_trigger.
      rewrite bind_ret_l, sb_guard.
      apply ret_ret; auto with ticl.
    Qed.

    (** Ret lemmas *)
    Lemma axr_qprog_ret{X}: forall (x: X) w q R,
        R (q, x) w ->
        not_done w ->
        <( {instr_prog (CRet x) q}, w |=R ret R )>.
    Proof.
      unfold instr_prog; cbn; intros.
      apply axr_state_ret; eauto with ticl.
    Qed.

    (** Sequence lemmas *)
    Lemma au_qprog_bind_r {X Y} {b : bool}:
      forall (h : CProg X) (k : X -> CProg Y) q q' (r : X) w w'
        (φ : ticll (writerE T)) (ψ : ticl_at (writerE T) (Q * Y) b),
        entails (Q * X) true (Cu Q_A φ (TICL.Logic.Syntax.CRet (fun v z => (q', r) = v /\ w' = z))) (instr_prog h q) w ->
        entails (Q * Y) b (Cu Q_A φ ψ) (instr_prog (k r) q') w' ->
        entails (Q * Y) b (Cu Q_A φ ψ) (instr_prog (CBind h k) q) w.
    Proof.
      unfold instr_prog; cbn; intros.
      eapply au_state_bind_r_eq; eauto with ticl.
    Qed.

    Lemma anr_qprog_bind_l{X Y}: forall (h: CProg X) (k: X -> CProg Y) q q' (r: X) w w' (φ : ticll (writerE T)) (ψ : ticlr (writerE T) (Q * Y)),
        <( {instr_prog h q}, w |=R φ AN ret={(q',r)} w' )> ->
        <( {instr_prog (k r) q'}, w' |=R ψ )> ->
        <( {instr_prog (CBind h k) q}, w |=R φ AN ψ )>.
    Proof.
      unfold instr_prog; cbn; intros.
      ticl_normalize.
      eapply (an_state_bind_l_eq h_queueE q (b:=true)); eauto with ticl.
    Qed.

    (** Conditional lemmas *)
    Lemma equiv_ifsome_some {X} {b : bool}:
      forall (k : X -> CProg unit) q (ψ : ticl_at (writerE T) (Q * unit) b) x w,
        entails (Q * unit) b ψ (instr_prog (k x) q) w <->
        entails (Q * unit) b ψ (instr_prog (CIfSome (Some x) k) q) w.
    Proof.
      unfold instr_prog; cbn; intros; eauto.
    Qed.

    (** While loops use the [iter] lemmas from [Iter.v] and [State.v] *)
    Lemma aul_qprog_until_now{X}: forall w (φ ψ : ticll (writerE T)) (b: CProg (option X)) q,
        <( {instr_prog b q}, w |=L φ AU ψ )> ->
        <( {instr_prog (CUntilNone b) q}, w |=L φ AU ψ )>.
    Proof.
      unfold instr_prog; cbn; intros.
      rewrite unfold_iter, bind_bind.
      now eapply ticll_state_bind_l.
    Qed.

    (** Termination lemma, uses [au_state_iter_nat] from [State.v] *)
    Theorem aur_qprog_termination {X}(b: CProg (option X)) q (Ri: rel Q (WorldW T)) w (f: Q -> nat) (φ : ticll (writerE T)) (ψ : ticlr (writerE T) (Q * unit)):
      Ri q w ->
      not_done w ->
      (forall q w,
          Ri q w ->
          not_done w ->
          exists (opt: option X) q' w',
            not_done w' /\
            <( {instr_prog b q}, w |=R φ AU ret={(q',opt)} w' )> /\
              match opt with
              | Some _ => Ri q' w' /\ f q' < f q
              | None => <( {Ret (q', tt): ctreeW T B (Q * unit)}, w' |=R ψ )>
              end) ->
      <( {instr_prog (CUntilNone b) q}, w |=R φ AU ψ )>.
    Proof.
      ticl_normalize.
      unfold instr_prog; intros; cbn.
      eapply au_state_iter_nat with
        (Ri:=fun 'tt (q : Q) (w : WorldW T) =>
               exists (opt: option X) (q' : Q) (w' : WorldW T),
                 not_done w' /\
                 entails (Q * option X) true <( φ AU ret={(q',opt)} w' )> (interp_state h_queueE (cdenote_prog b) q) w /\
                   match opt with
                   | Some _ => Ri q' w' /\ f q' < f q
                   | None => entails (Q * unit) true ψ (Ret (q', tt) : ctreeW T B (Q * unit)) w'
                   end)
        (f:= fun _ q _ => f q); eauto with ticl.
      - intros [] q' w' Hd (opt & q_ & w_ & Hd' & Hopt & HR).
        eapply (au_state_bind_r_eq h_queueE q' (b:=true)); eauto with ticl.
        destruct opt eqn:Heqo.
        + (* Some x *)
          apply (au_state_ret h_queueE q_ (b:=true)); apply ret_ret; intuition.
        + (* None *)
          apply (au_state_ret h_queueE q_ (b:=true)); apply ret_ret; intuition.
    Qed.

    (** Eventually lemma, uses [au_state_iter_prefix_nat] from [State.v] *)
    Theorem aul_qprog_eventually {X} (b: CProg (option X)) q (Ri: rel Q (WorldW T)) w (f: Q -> nat) (φ ψ : ticll (writerE T)):
      Ri q w ->
      not_done w ->
      (forall q w,
          Ri q w ->
          not_done w ->
          <( {instr_prog b q}, w |=R φ AU ret {fun '(q', opt) w' => exists x, opt = Some x /\ not_done w' /\ Ri q' w' /\ f q' < f q} )> \/
          <( {instr_prog b q}, w |=L φ AU ψ )>) ->
      <( {instr_prog (CUntilNone b) q}, w |=L φ AU ψ )>.
    Proof.
      unfold instr_prog; intros; cbn.
      eapply au_state_iter_prefix_nat with
        (Ri:=fun 'tt (q : Q) (w : WorldW T) =>
               entails (Q * option X) true
                 <( φ AU ret {fun '(q', opt) w' => exists x, opt = Some x /\ not_done w' /\ Ri q' w' /\ f q' < f q} )>
                 (interp_state h_queueE (cdenote_prog b) q) w \/
               entails (Q * option X) false <( φ AU ψ )> (interp_state h_queueE (cdenote_prog b) q) w)
        (f:= fun _ q _ => f q); eauto with ticl.
      - intros [] q' w' Hd [HR | HR].
        + (* Steps *)
          right.
          eapply (au_state_bind_r h_queueE q' (b:=true)).
          * apply HR.
          * cbn; intros opt q_ w_ (x_ & Heqx_ & Hd_ & HR_ & Hf_); subst.
            apply (au_state_ret h_queueE q_ (b:=true)); apply ret_ret; eauto with ticl.
            exists tt; intuition; eauto with ticl.
        + (* Matches *)
          left.
          apply ticll_state_bind_l; eauto with ticl.
    Qed.

    (** Invariance lemma, uses [ag_state_iter] from [State.v] *)
    Lemma ag_qprog_invariance: forall (b: CProg (option unit)) R q w (φ : ticll (writerE T)),
        R q w ->
        not_done w ->
        (forall q w,
            R q w ->
            not_done w ->
            <( {instr_prog (CUntilNone b) q}, w |=L φ )> /\
            <( {instr_prog b q}, w |=R AX (φ AU ret {fun '(q', r) w' => r = Some tt /\ not_done w' /\ R q' w'}) )>) ->
        <( {instr_prog (CUntilNone b) q}, w |=L AG φ )>.
    Proof.
      unfold instr_prog; cbn.
      intros.
      eapply ag_state_iter with
        (R:=fun 'tt (q : Q) (w : WorldW T) =>
              entails (Q * unit) false φ (interp_state h_queueE (cdenote_prog (CUntilNone b)) q) w /\
              entails (Q * option unit) true
                <( AX (φ AU ret {fun '(q', r) w' => r = Some tt /\ not_done w' /\ R q' w'}) )>
                (interp_state h_queueE (cdenote_prog b) q) w); eauto with ticl.
      - intros [] q' w' Hd (Hl & HR); cbn in Hl; split; [exact Hl |].
        ticl_normalize.
        rewrite interp_state_bind.
        eapply (ax_au_bind_r (b:=true)); [exact HR |].
        intros [q_ r_] w'' (-> & Hd'' & HR').
        apply (au_state_ret h_queueE q_ (b:=true)); apply ret_ret; eauto with ticl.
    Qed.
  End MeQ.
End ME.
