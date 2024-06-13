From Coq Require Import
  Basics
  Arith.Wf_nat
  Classes.Morphisms.

From CTree Require Import
  Events.Core
  Events.WriterE
  CTree.Core
  CTree.Equ
  CTree.SBisim
  CTree.Interp.Core
  CTree.Interp.State
  CTree.Logic.Trans
  CTree.Logic.CanStep
  Logic.Ctl
  Logic.AX
  Logic.Kripke
  Logic.Setoid.

Set Implicit Arguments.
Generalizable All Variables.

Import CTreeNotations CtlNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
  
(*| CTL logic lemmas on c/itrees |*)
Section BasicLemmas.
  Context {E: Type} {HE: Encode E} {X: Type}.

  Lemma aur_stuck: forall w φ ψ,
      <[ {Ctree.stuck: ctree E X}, w |= φ AU ψ ]> ->
      <[ {Ctree.stuck: ctree E X}, w |= ψ ]>.
  Proof.
    intros * H.
    remember (Ctree.stuck) as S.
    cinduction H; subst.
    - apply Hp.
    - now apply can_step_stuck in Hs.
  Qed.

  Lemma au_ret_r: forall (r: X) w φ ψ,      
      <( {Ret r}, w |= ψ )> ->
      <( {Ret r}, w |= φ AU ψ )>.
  Proof.
    intros * Hr.
    now cleft. 
  Qed.
  
  Lemma au_br: forall n (k: fin' n -> ctree E X) w ψ φ,
      not_done w ->
      (<( {Br n k}, w |= φ )> \/
         <( {Br n k}, w |= ψ )> /\
           forall (i: fin' n), <( {k i}, w |= ψ AU φ )>) ->
      <( {Br n k}, w |= ψ AU φ )>.     
  Proof with auto with ctl.
   intros e k * Hd [Hφ | (Hψ & H)].
   - now cleft. 
   - cright; csplit...
     + now apply can_step_br.
     + intros t' w' TR'.
       apply ktrans_br in TR' as (? & -> & -> & ?).
       apply H.
  Qed.

  Lemma au_br_inv: forall n (k: fin' n -> ctree E X) w ψ φ,
      <( {Br n k}, w |= ψ AU φ )> ->
        (<( {Br n k}, w |= φ )> \/
          forall (i: fin' n), <( {k i}, w |= ψ AU φ )>).
  Proof with eauto with ctl.
    intros.
    cdestruct H.
    - now left. 
    - cdestruct H.
      right.
      intros i.
      apply H, ktrans_br...
  Qed.

  Lemma au_vis_r: forall (e: E) (k: encode e -> ctree E X) w φ ψ,
      not_done w ->
      <( {Vis e k}, w |= φ )> ->
      <( {Vis e k}, w |= ψ AU φ )>.        
  Proof.
    intros e k * Hd H. 
    now cleft. 
  Qed.
  
  Lemma au_vis_l: forall (e: E) (k: encode e -> ctree E X) (_: encode e) w φ ψ,
      not_done w ->
      <( {Vis e k}, w |= ψ )> ->
      (forall (x: encode e), <( {k x}, {Obs e x} |= ψ AU φ )>) ->
      <( {Vis e k}, w |= ψ AU φ )>.        
  Proof with auto with ctl.
    intros e k wit * Hd Hψ H. 
    cright; csplit...    
    + now apply can_step_vis.
    + intros t' w' TR'.
      apply ktrans_vis in TR' as (? & -> & ? & ?).
      now rewrite <- H0.
  Qed.
  
End BasicLemmas.

