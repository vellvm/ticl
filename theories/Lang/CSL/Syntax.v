Module CSLSyntax.
  Inductive CProg : Type -> Type :=
  | CRead (a : nat) : CProg nat
  | CWrite (a v : nat) : CProg unit
  | CEmit (tag value : nat) : CProg unit
  | CYield : CProg unit
  | CFork (body : CProg unit) : CProg unit
  | CRet {A : Type} (value : A) : CProg A
  | CBind {A B : Type} (body : CProg A) (next : A -> CProg B) : CProg B
  | CUntilNone {A : Type} (body : CProg (option A)) : CProg unit
  | CAlloc (size : nat) : CProg nat
  | CCAS (a expected desired : nat) : CProg bool.
End CSLSyntax.
Export CSLSyntax.
