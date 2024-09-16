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

  Inductive CExp :=
  | CVar (x: string)
  | CConst (z: Z)
  | CAdd (x y: CExp)
  | CSub (x y: CExp).

  Inductive CStmt :=
  | CAssgn (x: string) (e: CExp)
  | CIfGte (l r: CExp) (t: CStmt) (e: CStmt)
  | CWhileGt (l r: CExp) (b: CStmt).

  Definition CProg := list CStmt.

  Fixpoint cdenote_exp(e: CExp): ctree Mem Z :=
    match e with
    | CVar v => load v
    | CConst z => Ret z
    | CAdd a b =>
        x <- cdenote_exp a ;;
        y <- cdenote_exp b ;;
        Ret (x + y)
    | CSub a b =>
        x <- cdenote_exp a ;;
        y <- cdenote_exp b ;;
        Ret (x - y)
    end.

  Fixpoint cdenote_stmt (s: CStmt): ctree Mem unit :=
    match s with
    | CAssgn x e =>
        v <- cdenote_exp e ;;
        store x v
    | CIfGte l r t e =>
        vl <- cdenote_exp l ;;
        vr <- cdenote_exp r ;;
        if vr <=? vl then
          cdenote_stmt t
        else
          cdenote_stmt e
    | CWhileGt l r b =>
        vl <- cdenote_exp l ;;
        vr <- cdenote_exp r ;;
        Ctree.iter
          (fun _ =>
             if vr <? vl then
               cdenote_stmt b ;;
               continue
             else
               break) tt
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

  Lemma clang_instr_mem_seq: forall a b ctx w,
      
    <( {instr_stateE [[ a ;;; b ]] ctx}, w |= AF φ )>
End Clang.
