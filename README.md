Temporal Interaction and Choice Logic (TICL)
==============================================

# About

Mechanized verification of liveness properties for programs with effects, nondeterminism,
and nontermination is difficult. Existing temporal reasoning frameworks operate on the
level of models (traces, automata) not executable code, creating a verification gap and losing
the benefits of modularity and composition enjoyed by structural program logics. Reasoning about
infinite traces and automata requires complex (co-)inductive proof techniques and familiarity
with proof assistant mechanics (e.g., guardedness checker). We propose a structural approach to
the verification of temporal properties with a new temporal logic that we call ticl. Using ticl,
we internalize complex (co-)inductive proof techniques to structural lemmas and reasoning about
variants and invariants. We show that it is possible to perform mechanized proofs of general
temporal properties, while working in a high-level of abstraction. We demonstrate the benefits of
ticl by giving mechanized proofs of safety and liveness properties for programs with queues,
secure memory, and distributed consensus.

# Building

The model of programs is the `ctree E B X` type of the [ctrees](https://github.com/vellvm/ctrees) library, consumed as the opam package `rocq-ctree` pinned to its `fix/universe-check` branch (see `INSTALL.md`).

Dependencies (all from opam, see `INSTALL.md` for pinned versions) are
- Rocq 9.2
- dune (>= 3.23)
- rocq-equations
- coq-ext-lib
- rocq-coinduction (>= 1.22, tower-based)
- rocq-relation-algebra, coq-itree (needed by ctrees)
- rocq-ctree (vellvm/ctrees, branch fix/universe-check; opam pin, see INSTALL.md)

Then use `make` in the root directory to build `TICL` and `make install` to install it.

# Documentation

Use `make doc` in the root directory to build the documentation. The documentation is accessed
by `main.html` in the root of the repository. The documentation is generated using rocqdoc.

Fair-scheduler liveness in [`Fair.v`](theories/CTree/Interp/Yield/Fair.v) reuses
the finite observation-prefix rules in [`CTree/Logic/Trace.v`](theories/CTree/Logic/Trace.v).
`fair_obs` excludes scheduling logs; queue and allocator recurrence results
require a `FairScheduler` policy.


