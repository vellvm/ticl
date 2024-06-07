From CTree Require Import
                   Events.Core
                   Logic.Kripke
                   Utils.Utils.

Generalizable All Variables.

Variant ctlQ := Q_A | Q_E.

Inductive CProp (T: Type): Type :=
| CBase: T -> CProp T
| CAnd: CProp T -> CProp T -> CProp T
| COr: CProp T -> CProp T -> CProp T
| CImpl: CProp T -> CProp T -> CProp T.
  
Section CtlSyntax.
  Context (E: Type) {HE: Encode E}.

  Inductive ctll :=
  | CNowL (φ: World E -> Prop): ctll
  | CgL (q: ctlQ) (φ: ctll): ctll
  | CxL (q: ctlQ) (φ: ctll): ctll
  | CuL (q: ctlQ) (φ ψ: ctll): ctll
  | CPropL (p: CProp ctll): ctll.

  Inductive ctlr (X: Type) :=
  | CNowR (φ: World E -> Prop): ctlr X
  | CDoneR (φ: X -> World E -> Prop): ctlr X
  | CxR (q: ctlQ) (φ: ctlr X): ctlr X
  | CuR (q: ctlQ) (φ: ctll) (ψ: ctlr X): ctlr X
  | CPropR (p: CProp (ctlr X)): ctlr X.
End CtlSyntax.

Arguments CBase {T}.
Arguments CAnd {T}.
Arguments COr {T}.
Arguments CImpl {T}.

Arguments CNowL {E} {HE} φ.
Arguments CgL {E} {HE} q φ.
Arguments CxL {E} {HE} q φ.
Arguments CuL {E} {HE} q φ ψ.
Arguments CPropL {E} {HE} p.

Arguments CNowR {E} {HE} {X} φ.
Arguments CDoneR {E} {HE} {X} φ.
Arguments CxR {E} {HE} {X} q φ.
Arguments CuR {E} {HE} {X} q φ ψ.
Arguments CPropR {E} {HE} {X} p.
