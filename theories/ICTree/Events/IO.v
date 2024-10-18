From TICL Require Import
  ICTree.Core.

From TICL Require Export
  Events.Core
  Events.IoE.

Notation fd := nat (only parsing).

Definition fresh {S}: ictree (ioE S) fd :=
  @ICtree.trigger (ioE S) (ioE S) _ _ (ReSum_refl) (ReSumRet_refl) Fresh.

Definition read {S}(f: fd): ictree (ioE S) (option S) :=
  @ICtree.trigger (ioE S) (ioE S) _ _ (ReSum_refl) (ReSumRet_refl) (Read f).

Definition write {S}(f: fd)(s: S): ictree (ioE S) bool :=
  @ICtree.trigger (ioE S) (ioE S) _ _ (ReSum_refl) (ReSumRet_refl) (Write f s).

Definition open {S}(f: fd): ictree (ioE S) bool :=
  @ICtree.trigger (ioE S) (ioE S) _ _ (ReSum_refl) (ReSumRet_refl) (Open f).

Definition close {S}(f: fd): ictree (ioE S) bool :=
  @ICtree.trigger (ioE S) (ioE S) _ _ (ReSum_refl) (ReSumRet_refl) (Close f).


