From CTree Require Import
                   Events.Core
                   Logic.Kripke
                   Utils.Utils.

Generalizable All Variables.

Variant ctlQ := Q_A | Q_E.

(* Free boolean algebra over [T] *)
Inductive CBool (T: Type): Type :=
| CBase: T -> CBool T
| CAnd: CBool T -> CBool T -> CBool T
| COr: CBool T -> CBool T -> CBool T
| CImpl: CBool T -> CBool T -> CBool T
| CNot: CBool T -> CBool T.
  
Section CtlSyntax.
  Context (E: Type) {HE: Encode E}.

  Inductive ctll :=
  (* Property [φ] holds right now and not in a [done] world *)
  | CNowL (φ: World E -> Prop): ctll
  (* With path quantifier [q]; property [φ] holds always (strong always) *)
  | CgL (q: ctlQ) (φ: ctll): ctll
  (* With path quantifier [q]; property [φ] holds next step *)
  | CxL (q: ctlQ) (φ: ctll): ctll
  (* With path quantifier [q]; property [φ] holds finitely, until [ψ] stops it *)
  | CuL (q: ctlQ) (φ ψ: ctll): ctll
  (* Boolean combinators of the above [ctll] *)
  | CBoolL (p: CBool ctll): ctll.

  Inductive ctlr (X: Type) :=
  (* Property [φ] holds right now and not in a [done] world *)
  | CNowR (φ: World E -> Prop): ctlr X
  (* Model returns with type [X] and [φ] holds at this point *)
  | CDoneR (φ: X -> World E -> Prop): ctlr X
  (* With path quantifier [q]; property [φ] holds next step *)
  | CxR (q: ctlQ) (φ: ctlr X): ctlr X
  (* With path quantifier [q]; property [φ: ctll] holds finitely, until [ψ: ctlr] stops it *)
  | CuR (q: ctlQ) (φ: ctll) (ψ: ctlr X): ctlr X
  (* Boolean combinators of the above [ctlr] *)
  | CBoolR (p: CBool (ctlr X)): ctlr X.
End CtlSyntax.

Arguments CBase {T}.
Arguments CAnd {T}.
Arguments COr {T}.
Arguments CImpl {T}.
Arguments CNot {T}.

Arguments CNowL {E} {HE} φ.
Arguments CgL {E} {HE} q φ.
Arguments CxL {E} {HE} q φ.
Arguments CuL {E} {HE} q φ ψ.
Arguments CBoolL {E} {HE} p.

Arguments CNowR {E} {HE} {X} φ.
Arguments CDoneR {E} {HE} {X} φ.
Arguments CxR {E} {HE} {X} q φ.
Arguments CuR {E} {HE} {X} q φ ψ.
Arguments CBoolR {E} {HE} {X} p.
