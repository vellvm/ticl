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

## Python

Ticl uses python-3.3 or later for some of its literate programming capabilities. If you do not
want to generate literate Rocq proofs using Alectryon and Sphinx, feel free to skip this section.

You can install Python using your package manager. For example, on Ubuntu:

```bash
sudo apt install python3
```

Python 3.3 comes with virtual environments, which we recommend using to install the
dependencies of Ticl. To create a virtual environment, run:

```bash
python3 -m venv venv
```

Then, activate the virtual environment:

```bash
source venv/bin/activate
```

Finally, install the required Python packages:

```bash
pip3 install -r requirements.txt
```

