Installation instructions
========================

This document provides instructions for installing and checking the proofs
for 'Ticl' the Structural temporal logic for mechanized program verification
on a Linux or MacOS system. If you are running on Windows, most of these
instructions should still apply, but you may need to adapt to the package
manager of your choice.

# Prerequisites

## OCaml

Using your package manager, install `opam-2.3.0` or later. For example, on Ubuntu:

```bash
sudo apt install opam
```

Then, initialize `opam` and create a switch:

```bash
opam init
opam switch create ticl 5.3.0
eval $(opam env)
```

## Rocq and the Ticl dependencies

Ticl depends on the Rocq proof assistant for proof verification and on a few
opam packages. Add the Rocq opam repository:

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
```

Then install Rocq 9.2 and the dependencies. We have tested `Ticl` with these
exact versions and cannot guarantee future versions will work without changes
to the code.

```bash
opam install dune.3.23.1 rocq-prover.9.2.0 rocq-equations.1.3.2+9.2 \
  coq-ext-lib.0.13.2 rocq-coinduction.1.22 rocq-relation-algebra.1.9.1 \
  coq-itree.5.2.1
```

- `rocq-coinduction` (>= 1.22) provides the tower-based coinduction library
  (`Chain`, `tower`, `coinduction R CIH`); the companion API is not used.
- `coq-itree`, `rocq-relation-algebra` and `coq-ext-lib` are needed by the
  `ctrees` library.

## The `ctrees` library (git submodule)

Ticl's model of programs is the `ctree E B X` type of the `ctrees` library
(https://github.com/vellvm/ctrees, branch `fix/universe-check`), vendored as a
git submodule in `ctrees/` and built together with Ticl by dune. After cloning,
fetch the submodule:

```bash
git clone --recurse-submodules https://github.com/vellvm/ticl
# or, in an existing checkout:
git submodule update --init
```

## Building and checking Ticl proofs and documentation

To typecheck all proofs in TICL (and the vendored `ctrees` theories), from
the repository root, run:

```bash
dune build
dune build @doc
```

The last command also generates the documentation for Ticl in HTML format.
For artifact evaluation, the list of all lemmas can be found in `_build/default/main.html`.
Open that file in your browser to see an index of all the lemmas in the paper and how they
correspond to the Rocq development.
