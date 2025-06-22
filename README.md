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

Dependencies are
- Rocq 9.0.0
- coq-equations
- coq-ext-lib
- relation-algebra
- The coinduction library (https://github.com/elefthei/coinduction)

Then use `make` in the root directory to build `TICL` and `make install` to install it.

# Documentation

Use `make doc` in the root directory to build the documentation. The documentation is accessed
by `main.html` in the root of the repository. The documentation is generated using coqdoc.


