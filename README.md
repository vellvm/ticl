Interaction and Choice Temporal Logic (ICTL)
==============================================

# About

Mechanized verification of liveness properties for programs with effects, nondeterminism, 
and nontermination is difficult. Existing temporal reasoning frameworks operate on the 
level of models (traces, automata) not executable code, creating a verification gap and losing 
the benefits of modularity and composition enjoyed by structural program logics. Reasoning about 
infinite traces and automata requires complex (co-)inductive proof techniques and familiarity 
with proof assistant mechanics (e.g., guardedness checker). We propose a structural approach to 
the verification of temporal properties with a new temporal logic that we call ictl. Using ictl, 
we internalize complex (co-)inductive proof techniques to structural lemmas and reasoning about 
variants and invariants. We show that it is possible to perform mechanized proofs of general 
temporal properties, while working in a high-level of abstraction. We demonstrate the benefits of
ictl by giving mechanized proofs of safety and liveness properties for programs with queues, 
secure memory, and distributed consensus.

# Building

Dependencies are
- Coq 8.19.0
- coq-equations
- coq-ext-lib
- relation-algebra
- The coinduction library (https://github.com/elefthei/coinduction)

Then use `dune build` in the root directory to build `ICTL` and `dune install` to install it.

# File structure
```
.
├── coq-ictl.opam
├── _CoqProject
├── dune-project
├── examples
│   ├── Election.v
│   ├── Lock.v
│   ├── Queue.v
│   ├── Sec.v
│   ├── t2
│   │   ├── P25.v
│   │   └── P26.v
│   └── Tick.v
├── LICENSE
└── theories
    ├── Classes.v
    ├── dune
    ├── Events
    │   ├── Core.v
    │   ├── StateE.v
    │   └── WriterE.v
    ├── ICTree
    │   ├── Core.v
    │   ├── Eq
    │   │   ├── Bind.v
    │   │   └── Core.v
    │   ├── Equ.v
    │   ├── Events
    │   │   ├── IO.v
    │   │   ├── State.v
    │   │   └── Writer.v
    │   ├── Interp
    │   │   ├── Core.v
    │   │   └── State.v
    │   ├── Logic
    │   │   ├── AF.v
    │   │   ├── AG.v
    │   │   ├── AX.v
    │   │   ├── Bind.v
    │   │   ├── CanStep.v
    │   │   ├── EF.v
    │   │   ├── EG.v
    │   │   ├── EX.v
    │   │   ├── Iter.v
    │   │   ├── Ret.v
    │   │   ├── Soundness.v
    │   │   ├── State.v
    │   │   └── Trans.v
    │   ├── SBisim
    │   │   ├── Core.v
    │   │   └── SSim.v
    │   ├── SBisim.v
    │   └── Trans.v
    ├── ICTree.v
    ├── Lang
    │   ├── Clang.v
    │   ├── Par.v
    │   ├── Vec.v
    │   └── Yield.v
    ├── Logic
    │   ├── Congruence.v
    │   ├── Ctl.v
    │   ├── Semantics.v
```


