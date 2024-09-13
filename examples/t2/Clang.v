From ExtLib Require
  Structures.Maps.
From ExtLib Require Import Data.String.

From Coq Require Import
  ZArith.ZArith
  Strings.String.

From CTree Require Import
  CTree.Core
  CTree.Interp.State
  CTree.Events.State
  CTree.Events.Writer.

Generalizable All Variables.

Import Ctree CTreeNotations.
Local Open Scope ctl_scope.
Local Open Scope ctree_scope.
Local Open Scope Z_scope.

Generalizable All Variables.

Module Clang.
  Module M := Maps.
  Context `{MM: @M.Map string Z Ctx}.
  Definition Mem := stateE Ctx.

  Definition assert(k: string)(p: Z -> Prop)(m: Ctx): Prop :=
    match M.lookup k m with
    | Some v => p v
    | None => False
    end.
  
  Definition load(k: string): ctree Mem Z :=
    m <- get ;;
    match M.lookup k m with
    | Some v => Ret v
    | None => Ret 0%Z
    end.

  Definition store(k: string) (v: Z): ctree Mem unit :=
    m <- get ;;    
    put (M.add k v m).

  (* a := f b *)
  Definition update(a: string) (b: string) (f: Z -> Z): ctree Mem unit :=
    m <- get ;;
    match M.lookup b m with
    | Some v => put (M.add a (f v) m)
    | None => put (M.add a (f 0%Z) m)
    end.
  
  Declare Scope clang_scope.
  Local Open Scope clang_scope.
  Declare Custom Entry clang.
  
  Notation "[[ e ]]" := e (at level 0, e custom clang at level 95) : clang_scope.
  Notation "( x )" := x (in custom clang, x at level 99) : clang_scope.
  Notation "{ x }" := x (in custom clang at level 0, x constr): clang_scope.
  Notation "x" := x (in custom clang at level 0, x constr at level 0) : clang_scope.

  Notation "x := c" := (store x c)
                         (in custom clang at level 60, right associativity) : clang_scope.
  
  Notation "x ::= y '+' c" := (update x y (fun z => z + c))
                                (in custom clang at level 60, right associativity) : clang_scope.
  
  Notation "x ::= y '-' c" := (update x y (fun z => z - c))
                                (in custom clang at level 60, right associativity) : clang_scope.
  
  Notation "'while' c '?>' z 'do' b 'done'" :=
    (@Ctree.iter _ _ unit unit
       (fun 'tt =>
          x <- load c;;
          if x >? z then
            b ;; continue
          else
            break
       ) tt) (in custom clang at level 63): ctree_scope.

  Notation "t1 ;;; t2" := (Ctree.bind t1 (fun _ => t2)) (in custom clang at level 62, right associativity): clang_scope.
End Clang.
