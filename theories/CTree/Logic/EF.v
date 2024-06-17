From Coq Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice.

From CTree Require Import
  Events.Core
  Events.WriterE
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Interp.Core
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.EX.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
  
(*| CTL logic lemmas on c/itrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Opaque Ctree.stuck.
  Lemma eul_stuck: forall w φ ψ,
      <( {Ctree.stuck: ctree E X}, w |= φ EU ψ )> <->
      <( {Ctree.stuck: ctree E X}, w |= ψ )>.
  Proof with auto with ctl.
    split; intros.
    - cdestruct H...
      cdestruct H.
      now apply ktrans_stuck in TR.
    - now cleft. 
  Qed.

  Lemma eur_stuck: forall w φ ψ,
      <[ {Ctree.stuck: ctree E X}, w |= φ EU ψ ]> <->
      <[ {Ctree.stuck: ctree E X}, w |= ψ ]>.
  Proof with auto with ctl.
    split; intros.
    - cdestruct H...
      cdestruct H.
      now apply ktrans_stuck in TR.
    - now cleft. 
  Qed.

  Lemma eul_ret: forall (r: X) w φ ψ,
      <( {Ret r}, w |= ψ \/ φ EX ψ )> <->
      <( {Ret r}, w |= φ EU ψ )>.
  Proof with auto with ctl.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H...
      assert (Hd: not_done w) by now apply ktrans_not_done in TR.
      inv Hd.
      + apply ktrans_done in TR as (-> & ?).
        exists (Ctree.stuck), (Done r); split.
        * now constructor.
        * rewrite H0 in H.
          now cleft.
      + apply ktrans_finish in TR as (-> & ?).
        exists (Ctree.stuck), (Finish e v r); split.
        * now constructor.
        * rewrite H0 in H.
          now cleft.
    - now cleft.
    - cdestruct H.
      cright; csplit...
      assert (Hd: not_done w) by now apply ktrans_not_done in TR.
      inv Hd.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H.
        apply eul_stuck in H.
        apply ctll_not_done in H; inv H.
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H.
        apply eul_stuck in H.
        apply ctll_not_done in H; inv H.
  Qed.

  Lemma eur_ret: forall (r: X) w φ ψ,
      <[ {Ret r}, w |= ψ \/ φ EX ψ ]> <->
      <[ {Ret r}, w |= φ EU ψ ]>.
  Proof with auto with ctl.
    split; intros H; cdestruct H.
    - now cleft.
    - cright; csplit; cdestruct H...
      assert (Hd: not_done w) by now apply ktrans_not_done in TR.
      inv Hd.
      + apply ktrans_done in TR as (-> & ?).
        exists (Ctree.stuck), (Done r); split.
        * now constructor.
        * rewrite H0 in H.
          now cleft.
      + apply ktrans_finish in TR as (-> & ?).
        exists (Ctree.stuck), (Finish e v r); split.
        * now constructor.
        * rewrite H0 in H.
          now cleft.
    - now cleft.
    - cdestruct H.
      assert (Hd: not_done w) by now apply ktrans_not_done in TR.
      inv Hd.
      + apply ktrans_done in TR as (-> & ?).
        rewrite H0 in H.
        apply eur_stuck in H.
        cright; csplit...
        exists (Ctree.stuck), (Done r); split...
        constructor...
      + apply ktrans_finish in TR as (-> & ?).
        rewrite H0 in H.
        apply eur_stuck in H.
        cright; csplit...
        exists (Ctree.stuck), (Finish e v r); split...
        constructor...
  Qed.
  
  Lemma eul_br: forall n (k: fin' n -> ctree E X) w φ ψ,
      (<( {Br n k}, w |= φ )> \/
         <( {Br n k}, w |= ψ )> /\
           exists (i: fin' n), <( {k i}, w |= ψ EU φ )>) <->
        <( {Br n k}, w |= ψ EU φ )>.
  Proof with auto with ctl.
    split; intros.
    - destruct H as [Hφ | (Hψ & i & H)].
      + now cleft. 
      + cright; csplit...
        apply ctll_not_done in Hψ.
        exists (k i), w; split...
        apply ktrans_br.
        exists i...
    - cdestruct H.
      + now left.
      + right; split...
        * now cdestruct H.
        * cdestruct H...
          apply ktrans_br in TR as (i & ? & <- & ?).
          rewrite H0 in H.
          exists i.
          apply H.
  Qed.          

  Lemma eur_br: forall n (k: fin' n -> ctree E X) w φ ψ,
      (<[ {Br n k}, w |= φ ]> \/
         <( {Br n k}, w |= ψ )> /\
           exists (i: fin' n), <[ {k i}, w |= ψ EU φ ]>) <->
        <[ {Br n k}, w |= ψ EU φ ]>.
  Proof with auto with ctl.
    split; intros.
    - destruct H as [Hφ | (Hψ & i & H)].
      + now cleft. 
      + cright; csplit...
        apply ctll_not_done in Hψ.
        exists (k i), w; split...
        apply ktrans_br.
        exists i...
    - cdestruct H.
      + now left.
      + right; split...
        * now cdestruct H.
        * cdestruct H...
          apply ktrans_br in TR as (i & ? & <- & ?).
          rewrite H0 in H.
          exists i.
          apply H.
  Qed.

  Lemma eul_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ ψ,
      (<( {Vis e k}, w |= φ )> \/
         <( {Vis e k}, w |= ψ )> /\
           exists (v: encode e), <( {k v}, {Obs e v} |= ψ EU φ )>) <->
        <( {Vis e k}, w |= ψ EU φ )>.
  Proof with auto with ctl.
    split; intros.
    - destruct H as [Hφ | (Hψ & i & H)].
      + now cleft. 
      + cright; csplit...
        apply ctll_not_done in Hψ.
        exists (k i), (Obs e i); split...
        apply ktrans_vis.
        exists i...
    - cdestruct H.
      + now left.
      + right; split...
        * now cdestruct H.
        * cdestruct H...
          apply ktrans_vis in TR as (i & -> & ? & ?).
          rewrite <- H0 in H.
          exists i.
          apply H.
  Qed.

  Lemma eur_vis: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ ψ,
      (<[ {Vis e k}, w |= φ ]> \/
         <( {Vis e k}, w |= ψ )> /\
           exists (v: encode e), <[ {k v}, {Obs e v} |= ψ EU φ ]>) <->
        <[ {Vis e k}, w |= ψ EU φ ]>.
  Proof with auto with ctl.
    split; intros.
    - destruct H as [Hφ | (Hψ & i & H)].
      + now cleft. 
      + cright; csplit...
        apply ctll_not_done in Hψ.
        exists (k i), (Obs e i); split...
        apply ktrans_vis.
        exists i...
    - cdestruct H.
      + now left.
      + right; split...
        * now cdestruct H.
        * cdestruct H...
          apply ktrans_vis in TR as (i & -> & ? & ?).
          rewrite <- H0 in H.
          exists i.
          apply H.
  Qed.

  Lemma eur_not_done: forall φ ψ (t: ctree E X) (w: World E),
      <[ t, w |= φ EU EN ψ ]> ->
      not_done w.
  Proof.
    intros.
    cdestruct H; cdestruct H;
      now apply ktrans_not_done with t t0 w0.
  Qed.
End BasicLemmas.
