From TICL Require Import
  ICTree.Core ICTree.Equ ICTree.Events.Yield ICTree.Interp.Refine
  Lang.CSL.Heap Lang.CSL.Syntax.

Import ICtree ICTreeNotations.
Local Open Scope ictree_scope.

Definition CEff := (yieldE + (forkE + sE))%type.
Definition heap_event (e : sE) : ictree CEff (encode e) :=
  Vis (inr (inr e)) (fun x => Ret x).
Definition source_yield : ictree CEff unit :=
  Vis (inl Yield) (fun _ => Ret tt).
Definition source_fork : ictree CEff bool :=
  Vis (inr (inl Fork)) (fun b => Ret b).

Fixpoint denote_flow {A : Type} (p : CProg A) : ictree CEff (option A) :=
  match p in CProg A return ictree CEff (option A) with
  | CRead a => x <- heap_event (SRd a);; Ret (Some x)
  | CWrite a v => heap_event (SWr a v);; Ret (Some tt)
  | CEmit q v => heap_event (SEmit q v);; Ret (Some tt)
  | CYield => source_yield;; Ret (Some tt)
  | CFork body =>
      child <- source_fork;;
      if child then denote_flow body;; Ret None else Ret (Some tt)
  | CRet x => Ret (Some x)
  | CBind body next =>
      flow <- denote_flow body;;
      match flow with None => Ret None | Some x => denote_flow (next x) end
  | CUntilNone body =>
      ICtree.iter
        (fun _ : unit =>
          flow <- denote_flow body;;
          match flow with
          | None => Ret (inr None)
          | Some None => Ret (inr (Some tt))
          | Some (Some _) => Ret (inl tt)
          end) tt
  | CAlloc size => a <- heap_event (SAlloc size);; Ret (Some a)
  | CCAS a expected desired =>
      b <- heap_event (SCAS a expected desired);; Ret (Some b)
  end.

Definition denote (p : CProg unit) : thread sE :=
  denote_flow p;; Ret tt.

Lemma denote_flow_branchfree {A} (p : CProg A) : BranchFree (denote_flow p).
Proof.
  induction p as [a|a v|q v| |body IH|A x|A B body IH next IHnext|A body IH|size|a expected desired];
    cbn [denote_flow].
  - apply branchfree_bind.
    + unfold heap_event; apply bf_vis; intro x; apply bf_ret.
    + intro x; apply bf_ret.
  - apply branchfree_bind.
    + unfold heap_event; apply bf_vis; intros []; apply bf_ret.
    + intros []; apply bf_ret.
  - apply branchfree_bind.
    + unfold heap_event; apply bf_vis; intros []; apply bf_ret.
    + intros []; apply bf_ret.
  - apply branchfree_bind.
    + unfold source_yield; apply bf_vis; intros []; apply bf_ret.
    + intros []; apply bf_ret.
  - apply branchfree_bind.
    + unfold source_fork; apply bf_vis; intro b; apply bf_ret.
    + intros []; cbn.
      * apply branchfree_bind; [exact IH|intro flow; apply bf_ret].
      * apply bf_ret.
  - apply bf_ret.
  - apply branchfree_bind; [exact IH|].
    intros [x|]; [apply IHnext|apply bf_ret].
  - apply branchfree_iter; intros [].
    apply branchfree_bind; [exact IH|].
    intros [[x|]|]; apply bf_ret.
  - apply branchfree_bind.
    + unfold heap_event; apply bf_vis; intro a; apply bf_ret.
    + intro a; apply bf_ret.
  - apply branchfree_bind.
    + unfold heap_event; apply bf_vis; intro b; apply bf_ret.
    + intro b; apply bf_ret.
Qed.

Lemma denote_branchfree (p : CProg unit) : BranchFree (denote p).
Proof.
  unfold denote; apply branchfree_bind;
    [apply denote_flow_branchfree|intro flow; apply bf_ret].
Qed.

Lemma denote_fork_bind (p : CProg unit) (next : unit -> CProg unit) :
  denote (CBind (CFork p) next) ≅
  Vis (inr (inl Fork))
    (fun child : bool => if child then denote p else denote (next tt)).
Proof.
  unfold denote; cbn [denote_flow]; unfold source_fork.
  rewrite !bind_bind, bind_vis.
  step; constructor; intro child.
  rewrite bind_ret_l; destruct child; cbn.
  - rewrite !bind_bind.
    apply equ_clo_bind_eq; intro flow.
    rewrite !bind_ret_l; reflexivity.
  - rewrite !bind_ret_l; reflexivity.
Qed.
