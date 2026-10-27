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

TICL targets Rocq 9.2. Its proof-library dependencies are published in the
Rocq opam repository; they are not git submodules.

## Standalone checkout

This canonical path pins [`elefthei/ctrees`](https://github.com/elefthei/ctrees/tree/dev)
at the immutable revision documented in `INSTALL.md` and the checked-in manifest:

```sh
opam repository add rocq-released https://rocq-prover.org/opam/released --switch default
opam install --switch default --deps-only .
opam exec --switch default -- dune build
```

`opam install --switch default .` installs TICL itself as well. In particular,
do not pin the old `elefthei/rocq-ext-lib` fork: it requires Rocq 9.1.1. The
released `coq-ext-lib` and official `rocq-coinduction.1.22` packages are the
Rocq 9.2 dependencies.

## Paired local CTree and TICL checkouts

Use a sibling checkout of `elefthei/ctrees` on `dev`, then install the working
trees in dependency order:

```sh
# From the CTree checkout
opam install --switch default --working-dir -y .
# From the TICL checkout
opam pin add --switch default --working-dir --ignore-pin-depends --no-action -y rocq-ticl.0.1 .
opam install --switch default --working-dir --ignore-pin-depends -y .
```

`--working-dir` includes uncommitted changes. TICL's `--ignore-pin-depends`
keeps its immutable remote pin from replacing the local CTree checkout.
The explicit pin refresh also updates metadata when TICL is already locally
pinned; `opam install` alone can otherwise leave its old dependency constraint.

See `INSTALL.md` for the canonical isolated-switch recipe and the distinction
between local developer pins and portable frozen artifacts. After installing
dependencies, `make` builds `TICL` and `make install` installs it.

# Documentation

Use `make doc` in the root directory to build the documentation. The documentation is accessed
by `main.html` in the root of the repository. The documentation is generated using rocqdoc.

Fair-scheduler liveness in [`Fair.v`](theories/CTree/Interp/Yield/Fair.v) reuses
the finite observation-prefix rules in [`CTree/Logic/Trace.v`](theories/CTree/Logic/Trace.v).
`fair_obs` excludes scheduling logs; queue and allocator recurrence results
require a `FairScheduler` policy.


