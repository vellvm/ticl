From TICL Require Import
  Logic.Kripke
  Utils.Utils.

From TICL Require Import Events.WriterE.
From Equations Require Import Equations.
Generalizable All Variables.

Variant ticlq := Q_A | Q_E.

(** * Indexed TICL syntax
    [None] describes prefix properties; [Some X] describes native-return
    postconditions over [X]. Temporal guards are always prefix properties. *)
Inductive ticl (E : Type -> Type) : option Type -> Type :=
| CNow (p : World E -> Prop) : ticl E None
| CRet {X : Type} (p : X -> World E -> Prop) : ticl E (Some X)
| Cu {i : option Type} (q : ticlq)
    (p : ticl E None) (r : ticl E i) : ticl E i
| Cx {i : option Type} (q : ticlq)
    (p : ticl E None) (r : ticl E i) : ticl E i
| Cg (q : ticlq) (p : ticl E None) : ticl E None
| CAnd {i : option Type} (p r : ticl E i) : ticl E i
| COr {i : option Type} (p r : ticl E i) : ticl E i.

Arguments CNow {E} p.
Arguments CRet {E X} p.
Arguments Cu {E i} q p r.
Arguments Cx {E i} q p r.
Arguments Cg {E} q p.
Arguments CAnd {E i} p r.
Arguments COr {E i} p r.

Notation ticll E := (ticl E None).
Notation ticlr E X := (ticl E (Some (X : Type))).
Notation ticl_at E X suffix :=
  (ticl E (if (suffix : bool) then Some (X : Type) else None)).

Section IndexedInduction.
  Context {E : Type -> Type} {X : Type}.
  Variable P : forall b, ticl_at E X b -> Prop.
  Variable Hnow : forall p, P false (CNow p).
  Variable Hret : forall p, P true (CRet p).
  Variable Hu : forall b q p, P false p -> forall r, P b r -> P b (Cu q p r).
  Variable Hx : forall b q p, P false p -> forall r, P b r -> P b (Cx q p r).
  Variable Hg : forall q p, P false p -> P false (Cg q p).
  Variable Hand : forall b p, P b p -> forall r, P b r -> P b (CAnd p r).
  Variable Hor : forall b p, P b p -> forall r, P b r -> P b (COr p r).

  Equations ticl_at_ind (b : bool) (p : ticl_at E X b) : P b p :=
  ticl_at_ind false (CNow p) := Hnow p;
  ticl_at_ind true (CRet p) := Hret p;
  ticl_at_ind b (Cu q p r) := Hu b q p (ticl_at_ind false p) r (ticl_at_ind b r);
  ticl_at_ind b (Cx q p r) := Hx b q p (ticl_at_ind false p) r (ticl_at_ind b r);
  ticl_at_ind false (Cg q p) := Hg q p (ticl_at_ind false p);
  ticl_at_ind b (CAnd p r) := Hand b p (ticl_at_ind b p) r (ticl_at_ind b r);
  ticl_at_ind b (COr p r) := Hor b p (ticl_at_ind b p) r (ticl_at_ind b r).
End IndexedInduction.

Section PrefixInduction.
  Context {E : Type -> Type}.
  Variable P : ticll E -> Prop.
  Variable Hnow : forall p, P (CNow p).
  Variable Hu : forall q p, P p -> forall r, P r -> P (Cu q p r).
  Variable Hx : forall q p, P p -> forall r, P r -> P (Cx q p r).
  Variable Hg : forall q p, P p -> P (Cg q p).
  Variable Hand : forall p, P p -> forall r, P r -> P (CAnd p r).
  Variable Hor : forall p, P p -> forall r, P r -> P (COr p r).

  Equations ticll_ind (p : ticll E) : P p :=
  ticll_ind (CNow p) := Hnow p;
  ticll_ind (Cu q p r) := Hu q p (ticll_ind p) r (ticll_ind r);
  ticll_ind (Cx q p r) := Hx q p (ticll_ind p) r (ticll_ind r);
  ticll_ind (Cg q p) := Hg q p (ticll_ind p);
  ticll_ind (CAnd p r) := Hand p (ticll_ind p) r (ticll_ind r);
  ticll_ind (COr p r) := Hor p (ticll_ind p) r (ticll_ind r).
End PrefixInduction.

(** * Return-predicate traversal. Prefix guards are unchanged. *)
Equations map_ret {E : Type -> Type} {X Y : Type}
    (f : (X -> World E -> Prop) -> (Y -> World E -> Prop))
    (p : ticlr E X) : ticlr E Y :=
map_ret f (CRet p) := CRet (f p);
map_ret f (Cu q p r) := Cu q p (map_ret f r);
map_ret f (Cx q p r) := Cx q p (map_ret f r);
map_ret f (CAnd p r) := CAnd (map_ret f p) (map_ret f r);
map_ret f (COr p r) := COr (map_ret f p) (map_ret f r).

(** Transform every atom, including prefix guards, without changing indices. *)
Equations map_atoms {E : Type -> Type} {X : Type}
  (now_map : (World E -> Prop) -> World E -> Prop)
  (ret_map : (X -> World E -> Prop) -> X -> World E -> Prop)
  (b : bool) (p : ticl E (if b then Some X else None))
  : ticl E (if b then Some X else None) :=
map_atoms now_map ret_map false (CNow P) := CNow (now_map P);
map_atoms now_map ret_map true (CRet P) := CRet (ret_map P);
map_atoms now_map ret_map b (Cu q p r) :=
  Cu q (map_atoms now_map ret_map false p) (map_atoms now_map ret_map b r);
map_atoms now_map ret_map b (Cx q p r) :=
  Cx q (map_atoms now_map ret_map false p) (map_atoms now_map ret_map b r);
map_atoms now_map ret_map false (Cg q p) := Cg q (map_atoms now_map ret_map false p);
map_atoms now_map ret_map b (CAnd p r) :=
  CAnd (map_atoms now_map ret_map b p) (map_atoms now_map ret_map b r);
map_atoms now_map ret_map b (COr p r) :=
  COr (map_atoms now_map ret_map b p) (map_atoms now_map ret_map b r).

Definition contramap {E : Type -> Type} {X Y : Type}
    (f : Y -> X) : ticlr E X -> ticlr E Y :=
  map_ret (fun p y w => p (f y) w).

(** * One grammar for formulas and judgments. Constructor indices enforce sorts. *)
Bind Scope ticl_scope with ticl.
Module TiclNotations.
  Local Open Scope ticl_scope.
  Declare Custom Entry ticl.
  Notation "<( e )>" := e
    (at level 0, e custom ticl at level 95) : ticl_scope.
  Notation "( x )" := x
    (in custom ticl, x at level 99) : ticl_scope.
  Notation "{ x }" := x
    (in custom ticl at level 0, x constr) : ticl_scope.
  Notation "x" := x
    (in custom ticl at level 0, x constr at level 0) : ticl_scope.

  Notation "'now' p" := (CNow p) (in custom ticl at level 74) : ticl_scope.
  Notation "'pure'" := (CNow (fun w => w = Pure))
    (in custom ticl at level 74) : ticl_scope.
  Notation "'vis' R" := (CNow (vis_with R))
    (in custom ticl at level 74) : ticl_scope.
  Notation "'visW' R" :=
    (CNow (vis_with (fun Y (pat : writerE _ Y) =>
      match pat in writerE _ Y return Y -> Prop with
      | Log v => fun 'tt => R v
      end))) (in custom ticl at level 74) : ticl_scope.
  Notation "'ret' R" := (CRet R) (in custom ticl at level 74) : ticl_scope.
  Notation "'ret=' r w" := (CRet (fun r' w' => r = r' /\ w = w'))
    (in custom ticl at level 74) : ticl_scope.
  Notation "⊤" := (CNow (fun _ => True)) (in custom ticl) : ticl_scope.
  Notation "⊥" := (CNow (fun _ => False)) (in custom ticl) : ticl_scope.
  Notation "p 'EN' q" := (Cx Q_E p q) (in custom ticl at level 75) : ticl_scope.
  Notation "p 'AN' q" := (Cx Q_A p q) (in custom ticl at level 75) : ticl_scope.
  Notation "p 'EU' q" := (Cu Q_E p q) (in custom ticl at level 75) : ticl_scope.
  Notation "p 'AU' q" := (Cu Q_A p q) (in custom ticl at level 75) : ticl_scope.
  Notation "'EG' p" := (Cg Q_E p) (in custom ticl at level 75) : ticl_scope.
  Notation "'AG' p" := (Cg Q_A p) (in custom ticl at level 75) : ticl_scope.
  Notation "'EF' p" := <( ⊤ EU p )>
    (in custom ticl at level 74, p at level 74) : ticl_scope.
  Notation "'AF' p" := <( ⊤ AU p )>
    (in custom ticl at level 74, p at level 74) : ticl_scope.
  Notation "'EX' p" := <( ⊤ EN p )>
    (in custom ticl at level 74, p at level 74) : ticl_scope.
  Notation "'AX' p" := <( ⊤ AN p )>
    (in custom ticl at level 74, p at level 74) : ticl_scope.
  Notation "p '/\' q" := (CAnd p q)
    (in custom ticl at level 77, left associativity) : ticl_scope.
  Notation "p '\/' q" := (COr p q)
    (in custom ticl at level 77, left associativity) : ticl_scope.
End TiclNotations.
