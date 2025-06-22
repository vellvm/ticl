From TICL Require Import
  ICTree.Core.

From TICL Require Export
  Events.Core
  Events.StateE.

Import ICTreeNotations.
Local Open Scope ictree_scope.

(** Create a [Get] event node, with subevents if needed *)
Definition get {S}: ictree (stateE S) S :=
  @ICtree.trigger (stateE S) (stateE S) _ _ (ReSum_refl) (ReSumRet_refl) Get.

(** Create a [Put] event node, with subevents if needed *)
Definition put {S}: S -> ictree (stateE S) unit :=
  fun (s: S) => ICtree.trigger (Put s).
