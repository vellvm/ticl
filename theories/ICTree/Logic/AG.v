From Coq Require Import
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
  ICTree.Logic.AX
  ICTree.Logic.AF
  Logic.Core.

Generalizable All Variables.

Import ICtree ICTreeNotations TiclNotations.
Local Open Scope ticl_scope.
Local Open Scope ictree_scope.

(* Lemmas on the structure of ictree [t] and AG proofs *)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma ag_vis: forall e (k: encode e -> ictree E X)
                  (v : encode e) w φ,
      (<( {Vis e k}, w |= φ )> /\ forall v, <( {k v}, {Obs e v} |= AG φ )>) <->
         <( {Vis e k}, w |= AG φ )>.
  Proof with eauto with ticl.
    split; intros.
    - destruct H as (Hφ & H).      
      csplit...
      + apply ticll_not_done in Hφ.
        apply can_step_vis...
      + intros t' w' TR.
        apply ktrans_vis in TR as (v' & -> & <- & ?)...
    - cdestruct H.
      split...
      intro v'.
      apply H, ktrans_vis...
  Qed.
  
  Lemma ag_br: forall n (k: fin' n -> ictree E X) w φ,
      (<( {Br n k}, w |= φ )> /\ forall (i: fin' n), <( {k i}, w |= AG φ )>) <->
        <( {Br n k}, w |= AG φ )>.
  Proof with eauto with ticl.
    split; intros.
    - destruct H as (Hφ & H).
      csplit...
      + apply ticll_not_done in Hφ.
        apply can_step_br...
      + intros t' w' TR.
        apply ktrans_br in TR as (i' & -> & -> & Hd).
        apply H.
    - cdestruct H.
      split...
      intro i.
      apply H, ktrans_br...
  Qed.

  Lemma ag_stuck: forall w φ,
      ~ <( {stuck: ictree E X}, w |= AG φ )>.
  Proof.
    intros * H.
    cdestruct H; subst. 
    now apply can_step_stuck in Hs.
  Qed.

  Lemma ag_ret: forall (x: X) w φ,      
      ~ <( {Ret x}, w |= AG φ )>.
  Proof.
    intros * H. 
    cdestruct H.
    destruct Hs as (t' & w' & TR).    
    specialize (H _ _ TR).
    apply ticll_not_done in Hp.
    inv Hp.
    + apply ktrans_done in TR as (-> & ?).
      rewrite H0 in H.
      now apply ag_stuck in H.
    + apply ktrans_finish in TR as (-> & ?).
      rewrite H0 in H.
      now apply ag_stuck in H.
  Qed.

End BasicLemmas.
