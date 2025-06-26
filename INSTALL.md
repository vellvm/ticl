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

Then, initialize `opam`:

```bash
opam init
```

Then proceed to install the `dune` build system:

```bash
opam install dune
```

## Rocq

Ticl depends on the Rocq proof assistant for proof verification.
First, add the Rocq package switch to opam:

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
```

Then, install the Rocq version 9.0.0. We have tested `Ticl` with that version and
cannot guarantee future versions of Rocq will work without changes to the code.

```bash
opam pin add rocq-prover 9.0.0
```

Then install the equations package for rocq:

## Ticl dependencies

Ticl depends on the `coq-equations` package for dependent type pattern matching.
Install it via opam:

```bash
opam install coq-equations
```

Then proceed to download and install the `rocq-ext-lib` package, which
provides many useful libraries for Rocq. For artifact evaluation, we provide
the `rocq-ext-lib` package in the root of the artifact folder. Otherwise, download
and install it from Github.

```bash
cd rocq-ext-lib
make install
cd ..
```

Then install the coinduction library in Rocq. For artifact evaluation, we provide
the `coinduction` package in the root of the artifact folder. Otherwise, download
and install it from Github.

```bash
cd coinduction
make install
cd ..
```

## Building and checking Ticl proofs and documentation

To typecheck all proofs in TICL, from the root of the artifact folder, run:

```bash
cd ticl
make
make doc
```

The last command also generates the documentation for Ticl in HTML format.
For artifact evaluation, the list of all lemmas can be found in `_build/default/main.html`.
Open that file in your browser to see an index of all the lemmas in the paper and how they
correspond to the Rocq development.
