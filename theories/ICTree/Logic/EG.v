From Stdlib Require Import
  Basics
  Classes.Morphisms.

From Coinduction Require Import
  coinduction lattice tactics.

From TICL Require Import
  Events.Core
  ICTree.Core
  ICTree.Equ
  ICTree.SBisim
  ICTree.Logic.Trans
  ICTree.Logic.CanStep
  Logic.Setoid
  ICTree.Logic.EX
  ICTree.Logic.EF
  Logic.Core.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.

(* Lemmas on the structure of ictree [t] and AG proofs *)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma eg_vis: forall e (k: encode e -> ictree E X) w φ,
      (<( {Vis e k}, w |= φ )> /\ exists v, <( {k v}, {Obs e v} |= EG φ )>) <->
         <( {Vis e k}, w |= EG φ )>.
  Proof with eauto with ticl.
    split; intros.
    - destruct H as (Hφ & v & H).
      csplit...
      exists (k v), (Obs e v); split...
      apply ticll_not_done in Hφ.
      apply ktrans_vis.      
      exists v; split2...
    - cdestruct H.
      split...
      apply ktrans_vis in TR as (v & -> & Heqt & ?).
      rewrite <- Heqt in H.
      exists v.
      apply H. 
  Qed.
  
  Lemma eg_br: forall n (k: fin' n -> ictree E X) w φ,
      (<( {Br n k}, w |= φ )> /\ exists (i: fin' n), <( {k i}, w |= EG φ )>) <->
        <( {Br n k}, w |= EG φ )>.
  Proof with eauto with ticl.
    split; intros.
    - destruct H as (Hφ & i & H).
      csplit...
      + exists (k i), w; split...
        apply ticll_not_done in Hφ.
        apply ktrans_br.
        exists i... 
    - cdestruct H.
      apply ktrans_br in TR as (i & Heqt & -> & ?).
      split...
      rewrite Heqt in H.
      exists i.
      apply H. 
  Qed.

  Lemma eg_stuck: forall w φ,
      ~ <( {stuck: ictree E X}, w |= EG φ )>.
  Proof.
    intros * H.
    cdestruct H; subst.
    now apply ktrans_stuck in TR.
  Qed.

  Lemma eg_ret: forall (x: X) w φ,      
      ~ <( {Ret x}, w |= EG φ )>.
  Proof.
    intros * H. 
    cdestruct H.
    assert(Hd: not_done w) by now apply ticll_not_done in Hp.
    inv Hd.
    - apply ktrans_done in TR as (-> & Heqt).
      rewrite Heqt in H.
      now apply eg_stuck in H.
    - apply ktrans_finish in TR as (-> & Heqt).
      rewrite Heqt in H.
      now apply eg_stuck in H.
  Qed.

End BasicLemmas.
