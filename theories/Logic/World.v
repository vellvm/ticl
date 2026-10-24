From Stdlib Require Import
  Relations
  Program.Equality
  Classes.Morphisms.

From TICL Require Import
  Utils.Utils.

Generalizable All Variables.

(** * Kripke worlds over an indexed event signature [E : Type -> Type] *)
Variant World (E: Type -> Type) :=
  | Pure
  | Obs {Y} (e : E Y) (v : Y)
  | Done {X} (x: X)
  | Finish {Y X} (e: E Y) (v: Y) (x: X).
Global Hint Constructors World: ticl.

Arguments Pure {E}.
Arguments Obs {E} {Y} e v.
Arguments Done {E} {X} x.
Arguments Finish {E} {Y X} e v x.

Variant not_pure {E}: World E -> Prop :=
  | NotPureObs {Y}: forall (e: E Y) (v: Y),
      not_pure (Obs e v)
  | NotPureFinish {Y X}: forall (e: E Y) (v: Y) (x: X),
      not_pure (Finish e v x).
Global Hint Constructors not_pure: ticl.

Variant is_pure {E}: World E -> Prop :=
  | IsPurePure:
      is_pure Pure
  | IsPureDone {X}: forall (x: X),
      is_pure (Done x).
Global Hint Constructors is_pure: ticl.

Variant vis_with {E} (R: forall Y, E Y -> Y -> Prop) : World E -> Prop :=
  | VisWithVis {Y}: forall (e: E Y) (v: Y),
      R Y e v -> vis_with R (Obs e v).
Global Hint Constructors vis_with: ticl.

Variant done_with {E} {X} (R: X -> World E -> Prop): World E -> Prop :=
  | DoneWithDone: forall (x: X),
      R x Pure -> done_with R (Done x)
  | DoneWithFinish {Y}: forall (e: E Y) (v: Y) (x: X),
      R x (Obs e v) -> done_with R (Finish e v x).
Global Hint Constructors done_with: ticl.

Definition done_eq {E} {X} (x: X): World E -> Prop :=
  @done_with E X (fun x' w' => x = x').

Variant done_of {E} {X} (x: X): relation (World E) :=
  | PureWithDone:
      done_of x Pure (Done x)
  | ObsWithFinish {Y}: forall (e: E Y) (v: Y),
      done_of x (Obs e v) (Finish e v x).
Global Hint Constructors done_of: ticl.

Lemma done_of_eq {E} {X}: forall (x: X) (w wd: World E),
    done_of x w wd <-> done_with (fun x' w' => x = x' /\ w = w') wd.
Proof.
  split; intros; inversion H; intuition auto with ticl; subst; constructor.
Qed.

Definition finish_with {E} {X} (R: X -> forall Y, E Y -> Y -> Prop) : X -> World E -> Prop :=
  fun x w => exists Y (e: E Y) (v: Y), w = Obs e v /\ R x Y e v.
Global Hint Unfold done_eq finish_with: ticl.

Variant not_done {E}: World E -> Prop :=
  | NotDonePure: not_done Pure
  | NotDoneObs {Y}: forall (e: E Y) (v: Y),
      not_done (Obs e v).
Global Hint Constructors not_done: ticl.

Variant is_done {E} X: World E -> Prop :=
  | DoneDone: forall (x: X), is_done X (Done x)
  | DoneFinish {Y}: forall (e: E Y) (v: Y) (x: X),
      is_done X (Finish e v x).
Global Hint Constructors is_done: ticl.

Definition not_done_dec {E}: forall (w: World E),
    {not_done w} + {exists X, is_done X w}.
Proof.
  dependent destruction w; intros.
  - left; econstructor.
  - left; econstructor.
  - right; eexists; econstructor.
  - right; eexists; econstructor.
Qed.

Definition not_pure_dec {E}: forall (w: World E),
    {not_pure w} + {is_pure w}.
Proof.
  dependent destruction w; intros.
  - right; econstructor.
  - left; econstructor.
  - right; econstructor.
  - left; econstructor.
Qed.
