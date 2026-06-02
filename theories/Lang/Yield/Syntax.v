From Stdlib Require Import Nat Strings.String.

Module YieldSyntax.
  Definition var := string.
  Definition value := nat.

  Inductive YExp : Type :=
  | YVar (_ : var)
  | YLit (_ : value)
  | YPlus (_ _ : YExp)
  | YMinus (_ _ : YExp)
  | YMult (_ _ : YExp).

  Inductive YStmt : Type :=
  | YAssign (x : var) (e : YExp)
  | YSeq (a b : YStmt)
  | YIf (i : YExp) (t e : YStmt)
  | YWhile (t : YExp) (b : YStmt)
  (** [YFork inactive active] keeps the prior branch polarity:
      the fork result [true] selects [inactive], and [false] selects [active]. *)
  | YFork (inactive active : YStmt)
  | YSkip
  | YYield.

  (** Yield treats any non-zero natural as true. *)
  Definition is_true (v : value) : bool := negb (v =? 0).
End YieldSyntax.
Export YieldSyntax.
