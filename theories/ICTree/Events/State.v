(*| Useful instructions: State |*)
From TICL Require Import
  ICTree.Core.

From TICL Require Export
  Events.Core
  Events.StateE.

Import ICTreeNotations.
Local Open Scope ictree_scope.

Definition get {S}: ictree (stateE S) S :=
  @ICtree.trigger (stateE S) (stateE S) _ _ (ReSum_refl) (ReSumRet_refl) Get.

Definition put {S}: S -> ictree (stateE S) unit :=
  fun (s: S) => ICtree.trigger (Put s).
