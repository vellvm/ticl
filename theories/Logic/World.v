From Stdlib Require Import
  Relations
  Program.Equality
  Classes.Morphisms.

From TICL Require Import
  Events.Core.

Generalizable All Variables.

Variant World (E:Type@{eff}) `{Encode E} :=
  | Pure
  | Obs (e : E) (v : encode e)
  | Done {X} (x: X)
  | Finish {X} (e: E) (v: encode e) (x: X).    
Global Hint Constructors World: ticl.

Arguments Pure {E} {_}.
Arguments Obs {E} {_} e v.
Arguments Done {E} {_} {X} x.
Arguments Finish {E} {_} {X} e v x.

Variant not_pure `{Encode E}: World E -> Prop :=
  | NotPureObs: forall (e: E) (v: encode e),
      not_pure (Obs e v)
  | NotPureFinish {X}: forall (e: E) (v: encode e) (x: X),
      not_pure (Finish e v x).
Global Hint Constructors not_pure: ticl.

Variant is_pure `{Encode E}: World E -> Prop :=
  | IsPurePure:
      is_pure Pure
  | IsPureDone {X}: forall (x: X),
      is_pure (Done x).
Global Hint Constructors is_pure: ticl.

Variant vis_with `{Encode E} (R: forall e, encode e -> Prop) : World E -> Prop :=
  | VisWithVis: forall (e: E) (v: encode e),
      R e v -> vis_with R (Obs e v).
Global Hint Constructors vis_with: ticl.

Variant done_with `{Encode E} {X} (R: X -> World E -> Prop): World E -> Prop :=
  | DoneWithDone: forall (x: X),
      R x Pure -> done_with R (Done x)
  | DoneWithFinish: forall (e: E) (v: encode e) (x: X),
      R x (Obs e v) -> done_with R (Finish e v x).
Global Hint Constructors done_with: ticl.

Definition done_eq `{Encode E} {X} (x: X): World E -> Prop :=
  @done_with E H X (fun x' w' => x = x').

Variant done_of `{Encode E} {X} (x: X): relation (World E) :=
  | PureWithDone:
      done_of x Pure (Done x)
  | ObsWithFinish: forall (e: E) (v: encode e),
      done_of x (Obs e v) (Finish e v x).
Global Hint Constructors done_of: ticl.

Lemma done_of_eq`{Encode E} {X}: forall (x: X) w wd,
    done_of x w wd <-> done_with (fun x' w' => x = x' /\ w = w') wd.
Proof.
  split; intros; inversion H0; intuition auto with ticl; subst; constructor.
Qed.

Definition finish_with `{Encode E} {X} (R: X -> forall (e:E), encode e -> Prop) : X -> World E -> Prop :=
  fun x w => exists (e: E) (v: encode e), w = Obs e v /\ R x e v.
Global Hint Unfold done_eq finish_with: ticl.

Variant not_done `{Encode E}: World E -> Prop :=
  | NotDonePure: not_done Pure
  | NotDoneObs: forall (e: E) (v: encode e),
      not_done (Obs e v).
Global Hint Constructors not_done: ticl.

Variant is_done `{Encode E} X: World E -> Prop :=
  | DoneDone: forall (x: X), is_done X (Done x)
  | DoneFinish: forall (e: E) (v: encode e) (x: X),
      is_done X (Finish e v x).
Global Hint Constructors is_done: ticl.

Definition not_done_dec `{Encode E}: forall (w: World E),
    {not_done w} + {exists X, is_done X w}.
Proof.
  dependent destruction w; intros.
  - left; econstructor.
  - left; econstructor.
  - right; eexists; econstructor. 
  - right; eexists; econstructor.
Qed.

Definition not_pure_dec `{Encode E}: forall (w: World E),
    {not_pure w} + {is_pure w}.
Proof.
  dependent destruction w; intros.
  - right; econstructor. 
  - left; econstructor.
  - right; econstructor. 
  - left; econstructor.
Qed.
