From TICL Require Import
  Events.Core
  Logic.Kripke
  Utils.Utils.

From TICL Require Import
  Events.WriterE.

From Equations Require Import Equations.
Generalizable All Variables.

Variant ticlq := Q_A | Q_E.

Section TiclSyntax.
  Context {E: Type} {HE: Encode E}.

  Inductive ticll: Type :=
  (* Property [φ] holds right now, while in [not_done] world *)
  | CNow (φ: World E -> Prop): ticll
  (* Path quantifier [q]; property [φ: ticll] holds finitely, until [ψ: ticlr] stops it *)
  | CuL (q: ticlq) (φ ψ: ticll): ticll
  | CxL (q: ticlq) (φ ψ: ticll): ticll
  (* Path quantifier [q]; property [φ] holds always (strong always) *)
  | Cg (q: ticlq) (φ: ticll) : ticll
  (* Boolean combinators *)
  | CAndL (p q: ticll): ticll
  | COrL (p q: ticll): ticll.
  
  Inductive ticlr {X: Type} : Type :=
  (* Model returns with type [X] and [φ] holds at this point *)
  | CDone (φ: X -> World E -> Prop): ticlr
  | CuR (q: ticlq) (φ: ticll) (ψ: ticlr): ticlr
  | CxR (q: ticlq) (φ: ticll) (ψ: ticlr): ticlr
  (* Boolean combinators *)
  | CAndR (p: ticlr) (q: ticlr): ticlr
  | COrR (p: ticlr) (q: ticlr): ticlr
  | CImplR (p: ticll) (q: ticlr): ticlr.

    
  Arguments ticlr: clear implicits.

End TiclSyntax.

Arguments ticll E {HE}.
Arguments ticlr E {HE} X.

Section Contramap.
  Context {E: Type} {HE: Encode E} {X Y: Type}.
  Definition contramap(f: Y -> X): ticlr E X -> ticlr E Y :=
    fix F φ :=
      match φ with
      | CDone p => CDone (fun y w => p (f y) w)
      | CuR q φ ψ => CuR q φ (F ψ)
      | CxR q φ ψ => CxR q φ (F ψ)
      | CAndR φ ψ => CAndR (F φ) (F ψ)
      | COrR φ ψ => COrR (F φ) (F ψ)
      | CImplR φ ψ => CImplR φ (F ψ)
      end.

  (* TODO: Contramap laws, identity and composition *)
  (* contramap f id = id, contramap (f . g) p = contramap g (contramap f p) *)
End Contramap.

Bind Scope ticl_scope with ticll ticlr.

(*| Coq notation for TICL formulas |*)
Module TiclNotations.
  Local Open Scope ticl_scope.

  (* left TICL syntax (no termination) *)
  Declare Custom Entry ticll.
  
  Notation "<( e )>" := e (at level 0, e custom ticll at level 95) : ticl_scope.
  Notation "( x )" := x (in custom ticll, x at level 99) : ticl_scope.
  Notation "{ x }" := x (in custom ticll at level 0, x constr): ticl_scope.
  Notation "x" := x (in custom ticll at level 0, x constr at level 0) : ticl_scope.

  (* Right TICL syntax (with termination) *)
  Declare Custom Entry ticlr.

  Notation "<[ e ]>" := e (at level 0, e custom ticlr at level 95) : ticl_scope.
  Notation "( x )" := x (in custom ticlr, x at level 99) : ticl_scope.
  Notation "{ x }" := x (in custom ticlr at level 0, x constr): ticl_scope.
  Notation "x" := x (in custom ticlr at level 0, x constr at level 0) : ticl_scope.

  (* Temporal syntax: base predicates *)
  Notation "'now' p" :=
    (CNow p)
      (in custom ticll at level 74): ticl_scope.

  Notation "'pure'" :=
    (CNow (fun w => w = Pure))
      (in custom ticll at level 74): ticl_scope.

  Notation "'vis' R" :=
    (CNow (vis_with R))
      (in custom ticll at level 74): ticl_scope.

  Notation "'visW' R" :=
    (CNow (vis_with (fun pat : writerE _ =>
                       let 'Log v as x := pat return (encode x -> Prop) in
                       fun 'tt => R v)))
      (in custom ticll at level 75): ticl_scope.
  
  Notation "'done' R" :=
    (CDone R)
      (in custom ticlr at level 74): ticl_scope.

  Notation "'done=' r w" :=
    (CDone (fun r' w' => r = r' /\ w = w'))
      (in custom ticlr at level 74): ticl_scope.

  Notation "'finish' R" :=
    (CDone (finish_with R))
      (in custom ticlr at level 74): ticl_scope.
  
  Notation "'finishW' R" :=
    (CDone (finish_with (fun '(x, s) (pat : writerE _) =>
                           let 'Log w as u := pat return (encode u -> Prop) in
                           fun 'tt => R x s w)))
      (in custom ticlr at level 75): ticl_scope.

  Notation "⊤" := (CNow (fun _ => True))
                    (in custom ticll at level 76): ticl_scope.
  
  Notation "⊥" := (CNow (fun _ => False))
                     (in custom ticll at level 76): ticl_scope.
  Notation "⊤" := (CNow (fun _ => True))
                    (in custom ticlr at level 76): ticl_scope.
  
  Notation "⊥" := (CNow (fun _ => False))
                    (in custom ticlr at level 76): ticl_scope.
  
  Notation "⫪" := (CDone (fun _ _ => True))
                    (in custom ticlr at level 76): ticl_scope.
  
  Notation "⫫" := (CDone (fun _ _ => False))
                    (in custom ticlr at level 76): ticl_scope.
  
  (* Temporal syntax *)
  Notation "p 'EN' q" := (CxL Q_E p q) (in custom ticll at level 75): ticl_scope.
  Notation "p 'AN' q" := (CxL Q_A p q) (in custom ticll at level 75): ticl_scope.

  Notation "p 'EN' q" := (CxR Q_E p q) (in custom ticlr at level 75): ticl_scope.
  Notation "p 'AN' q" := (CxR Q_A p q) (in custom ticlr at level 75): ticl_scope.

  Notation "p 'EU' q" := (CuL Q_E p q) (in custom ticll at level 75): ticl_scope.
  Notation "p 'AU' q" := (CuL Q_A p q) (in custom ticll at level 75): ticl_scope.

  Notation "p 'EU' q" := (CuR Q_E p q) (in custom ticlr at level 75): ticl_scope.
  Notation "p 'AU' q" := (CuR Q_A p q) (in custom ticlr at level 75): ticl_scope.

  Notation "'EG' p" := (Cg Q_E p) (in custom ticll at level 75): ticl_scope.
  Notation "'AG' p" := (Cg Q_A p) (in custom ticll at level 75): ticl_scope.

  Notation "'EG' p" := (Cg Q_E p) (in custom ticll at level 75): ticl_scope.
  Notation "'AG' p" := (Cg Q_A p) (in custom ticll at level 75): ticl_scope.

  (* Syntactic sugar [AF, EF] is finally *)
  Notation "'EF' p" := <( ⊤ EU p )> (in custom ticll at level 74): ticl_scope.
  Notation "'AF' p" := <( ⊤ AU p )> (in custom ticll at level 74): ticl_scope.

  Notation "'EF' p" := <[ ⊤ EU p ]> (in custom ticlr at level 74): ticl_scope.
  Notation "'AF' p" := <[ ⊤ AU p ]> (in custom ticlr at level 74): ticl_scope.

  Notation "'EX' p" := <( ⊤ EN p )> (in custom ticll at level 74): ticl_scope.
  Notation "'AX' p" := <( ⊤ AN p )> (in custom ticll at level 74): ticl_scope.

  Notation "'EX' p" := <[ ⊤ EN p ]> (in custom ticlr at level 74): ticl_scope.
  Notation "'AX' p" := <[ ⊤ AN p ]> (in custom ticlr at level 74): ticl_scope.
  
  (* Propositional syntax *)
  Notation "p '/\' q" := (CAndL p q)
                           (in custom ticll at level 77, left associativity): ticl_scope.
  Notation "p '\/' q" := (COrL p q)
                           (in custom ticll at level 77, left associativity): ticl_scope.

  Notation "p '/\' q" := (CAndR p q)
                           (in custom ticlr at level 77, left associativity): ticl_scope.  
  Notation "p '\/' q" := (COrR p q)
                           (in custom ticlr at level 77, left associativity): ticl_scope.
  Notation "p '->' q" := (CImplR p q)
                           (in custom ticlr at level 78, right associativity): ticl_scope.
End TiclNotations.
