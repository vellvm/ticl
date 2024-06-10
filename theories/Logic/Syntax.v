
From CTree Require Import
  Events.Core
  Logic.Kripke
  Utils.Utils.

From CTree Require Import
  Events.WriterE.

From Equations Require Import Equations.
Generalizable All Variables.

Variant ctlq := Q_A | Q_E.

Section CtlSyntax.
  Context {E: Type} {HE: Encode E}.
  
  Inductive ctll: Type :=
  (* Property [φ] holds right now and not in a [done] world *)
  | CNowL (φ: World E -> Prop): ctll
  (* Path quantifier [q]; property [φ: ctll] holds finitely, until [ψ: ctlr] stops it *)
  | CuL (q: ctlq) (φ ψ: ctll): ctll
  | CxL (q: ctlq) (φ: ctll): ctll
  (* Path quantifier [q]; property [φ] holds always (strong always) *)
  | Cg (q: ctlq) (φ: ctll) : ctll
  (* Boolean combinators *)
  | CAndL (p q: ctll): ctll
  | COrL (p q: ctll): ctll
  | CImplL (p q: ctll): ctll.
  
  Inductive ctlr {X: Type} : Type :=
  (* Model returns with type [X] and [φ] holds at this point *)
  | CDone (φ: X -> World E -> Prop): ctlr
  | CuR (q: ctlq) (φ: ctll) (ψ: ctlr): ctlr
  | CxR (q: ctlq) (p: ctlr): ctlr
  (* Boolean combinators *)
  | CAndR (p: ctll) (q: ctlr): ctlr
  | COrR (p: ctll) (q: ctlr): ctlr
  | CImplR (p: ctll) (q: ctlr): ctlr.

  Arguments ctlr: clear implicits.

End CtlSyntax.

Arguments ctll E {HE}.
Arguments ctlr E {HE} X.

(*| Coq notation for CTL formulas |*)
Module CtlNotations.
  Declare Scope ctl_scope.
  Local Open Scope ctl_scope.

  (* left CTL syntax (no termination) *)
  Declare Custom Entry ctll.

  Notation "<( e )>" := e (at level 0, e custom ctll at level 95) : ctl_scope.
  Notation "( x )" := x (in custom ctll, x at level 99) : ctl_scope.
  Notation "{ x }" := x (in custom ctll at level 0, x constr): ctl_scope.
  Notation "x" := x (in custom ctll at level 0, x constr at level 0) : ctl_scope.

  (* Right CTL syntax (with termination) *)
  Declare Custom Entry ctlr.

  Notation "<[ e ]>" := e (at level 0, e custom ctlr at level 95) : ctl_scope.
  Notation "( x )" := x (in custom ctlr, x at level 99) : ctl_scope.
  Notation "{ x }" := x (in custom ctlr at level 0, x constr): ctl_scope.
  Notation "x" := x (in custom ctlr at level 0, x constr at level 0) : ctl_scope.

  (* Temporal syntax: base predicates *)
  Notation "'now' p" :=
    (CNowL p)
      (in custom ctll at level 74): ctl_scope.

  Notation "'pure'" :=
    (CNowL (fun w => w = Pure))
      (in custom ctll at level 74): ctl_scope.

  Notation "'vis' R" :=
    (CNowL (vis_with R))
      (in custom ctll at level 74): ctl_scope.

  Notation "'visW' R" :=
    (CNowL (vis_with (fun pat : writerE _ =>
                       let 'Log v as x := pat return (encode x -> Prop) in
                       fun 'tt => R v)))
      (in custom ctll at level 75): ctl_scope.
  
  Notation "'done' R" :=
    (CDone R)
      (in custom ctlr at level 74): ctl_scope.

  Notation "'done=' r w" :=
    (CDone (fun r' w' => r = r' /\ w = w'))
      (in custom ctlr at level 74): ctl_scope.

  Notation "'finish' R" :=
    (CDone (finish_with R))
      (in custom ctlr at level 74): ctl_scope.
  
  Notation "'finishW' R" :=
    (CDone (finish_with (fun '(x, s) (pat : writerE _) =>
                           let 'Log w as u := pat return (encode u -> Prop) in
                           fun 'tt => R x s w)))
      (in custom ctlr at level 75): ctl_scope.

  Notation "⊤" := (CNowL (fun _ => True))
                    (in custom ctll at level 76): ctl_scope.
  
  Notation "⊥" := (CNowL (fun _ => False))
                    (in custom ctll at level 76): ctl_scope.
  Notation "⊤" := (CNowL (fun _ => True))
                    (in custom ctlr at level 76): ctl_scope.  
  Notation "⊥" := (CNowL (fun _ => False))
                    (in custom ctlr at level 76): ctl_scope.

  (* Temporal syntax *)
  Notation "'EX' p" := (CxL Q_E p) (in custom ctll at level 75): ctl_scope.
  Notation "'AX' p" := (CxL Q_A p) (in custom ctll at level 75): ctl_scope.

  Notation "'EX' p" := (CxR Q_E p) (in custom ctlr at level 75): ctl_scope.
  Notation "'AX' p" := (CxR Q_A p) (in custom ctlr at level 75): ctl_scope.

  Notation "p 'EU' q" := (CuL Q_E p q) (in custom ctll at level 75): ctl_scope.
  Notation "p 'AU' q" := (CuL Q_A p q) (in custom ctll at level 75): ctl_scope.

  Notation "p 'EU' q" := (CuR Q_E p q) (in custom ctlr at level 75): ctl_scope.
  Notation "p 'AU' q" := (CuR Q_A p q) (in custom ctlr at level 75): ctl_scope.

  Notation "'EG' p" := (Cg Q_E p) (in custom ctll at level 75): ctl_scope.
  Notation "'AG' p" := (Cg Q_A p) (in custom ctll at level 75): ctl_scope.

  Notation "'EG' p" := (Cg Q_E p) (in custom ctll at level 75): ctl_scope.
  Notation "'AG' p" := (Cg Q_A p) (in custom ctll at level 75): ctl_scope.

  (* Syntactic sugar [AF, EF] is finally *)
  Notation "'EF' p" := <( ⊤ EU p )> (in custom ctll at level 74): ctl_scope.
  Notation "'AF' p" := <( ⊤ AU p )> (in custom ctll at level 74): ctl_scope.

  Notation "'EF' p" := <[ ⊤ EU p ]> (in custom ctlr at level 74): ctl_scope.
  Notation "'AF' p" := <[ ⊤ AU p ]> (in custom ctlr at level 74): ctl_scope.

  (* Propositional syntax *)
  Notation "p '/\' q" := (CAndL p q)
                           (in custom ctll at level 77, left associativity): ctl_scope.
  Notation "p '\/' q" := (COrL p q)
                           (in custom ctll at level 77, left associativity): ctl_scope.
  Notation "p '->' q" := (CImplL p q)
                           (in custom ctll at level 78, right associativity): ctl_scope.
  Notation " ¬ p" := (CImplL p <( ⊥ )>)
                       (in custom ctll at level 76): ctl_scope.
  Notation "p '<->' q" := (CAndL (CImplL p q) (CImplL q p))
                            (in custom ctll at level 77): ctl_scope.

  Notation "p '/\' q" := (CAndR p q)
                           (in custom ctlr at level 77, left associativity): ctl_scope.
  Notation "p '\/' q" := (CAndR p q)
                           (in custom ctlr at level 77, left associativity): ctl_scope.
  Notation "p '->' q" := (CImplR p q)
                           (in custom ctlr at level 78, right associativity): ctl_scope.

End CtlNotations.
