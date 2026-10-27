Installation instructions
========================

These instructions build the Tisl proof development on Linux or macOS using
the dedicated `tisl-review-9.2` opam switch. The checked development uses OCaml
5.3.0, Dune 3.23.1, Rocq core and Stdlib 9.2.0, and the immutable CTree revision
`7470697761fdba323348e8b97e0870ac1ce1cbae` from
[`elefthei/ctrees`](https://github.com/elefthei/ctrees/tree/dev). Dependency
downloads require network access; this is a source artifact, not an offline
environment image.

`dune build` only builds; it does not download opam dependencies. For a
standalone development checkout in the existing default switch, the canonical
path uses the immutable remote CTree pin from the checked-in manifest:

```sh
opam repository add rocq-released https://rocq-prover.org/opam/released --switch default
opam install --switch default --deps-only .
opam exec --switch default -- dune build
```

Use `opam install --switch default .` instead to install TICL itself. The old
`elefthei/rocq-ext-lib` fork is intentionally not pinned because it requires
Rocq 9.1.1; this development uses the released `coq-ext-lib` package. Likewise,
the official `rocq-coinduction.1.22` release from `damien-pous/coinduction`
provides `Coinduction.all` and the tower API.

For paired local CTree and TICL checkouts, install the working trees in
dependency order:

```sh
# cwd: /path/to/ctrees
opam install --switch default --working-dir -y .
# cwd: /path/to/ticl
opam pin add --switch default --working-dir --ignore-pin-depends --no-action -y rocq-ticl.0.1 .
opam install --switch default --working-dir --ignore-pin-depends -y .
```

The explicit pin refresh updates metadata even when TICL is already locally
pinned; `opam install` alone can otherwise retain its old dependency constraint.

`--working-dir` includes uncommitted changes. TICL's `--ignore-pin-depends`
keeps its immutable remote pin from replacing the local CTree checkout. This
local pin is non-portable developer state, not a frozen artifact; the isolated
and artifact workflows below retain the public immutable CTree revision.

# Prerequisites and dedicated switch

Install opam 2.3.0 or later, GNU Make, Python 3, Git, and the system prerequisites
requested by opam. Initialize opam if necessary, without changing its selected
switch. All commands below run from the proof repository root unless stated
otherwise.

```sh
opam init --bare --no-setup
SW=tisl-review-9.2
opam switch create "$SW" ocaml-base-compiler.5.3.0 --no-switch -y
opam repository add rocq-released https://rocq-prover.org/opam/released --switch "$SW" -y
opam install --switch "$SW" -y dune.3.23.1 rocq-core.9.2.0 rocq-stdlib.9.2.0 \
  rocq-equations.1.3.2+9.2 coq-ext-lib.0.13.2 rocq-coinduction.1.22 \
  rocq-relation-algebra.1.9.1 coq-itree.5.2.1 odoc.3.2.1
opam pin add --switch "$SW" -y rocq-ctree.2.0-dev \
  git+https://github.com/elefthei/ctrees.git#7470697761fdba323348e8b97e0870ac1ce1cbae
opam exec --switch "$SW" -- dune build -j 1
```

Skip successful initialization and switch/repository setup when resuming. Reuse
an existing switch only if its compiler and installed package versions match
this recipe. Otherwise choose the first unused name `tisl-review-9.2-2`, `-3`,
and so on, and set `SW` accordingly; do not replace or modify an unrelated
switch. `--no-switch` leaves the selected default unchanged; `opam exec` avoids
changing the caller's shell environment.

Rocq core and Stdlib are separate packages: `rocq-prover.9.2.0` is not the
package used here. Equations resolves the compatibility package `coq-core`
at version 9.2.0; the frozen export records the complete resolved closure.
Hosted CI runs on `lang/yield` and removes the Rocq container's older Stdlib
pin before resolving dependencies, so the manifest's `rocq-stdlib >= 9.2`
requirement is honored alongside Dune 3.23.1.

The `rocq-coinduction` package provides the tower-based coinduction library;
`coq-itree`, `rocq-relation-algebra`, and `coq-ext-lib` support CTree. The
canonical CTree pin is in `rocq-ticl.opam.template`; Dune generates
`rocq-ticl.opam` from the project metadata and template. Do not substitute a
moving branch for the recorded commit.

After changing canonical metadata, regenerate and promote the checked-in manifest:

```sh
opam exec --switch "$SW" -- dune build -j 1 @opam
opam exec --switch "$SW" -- dune promote rocq-ticl.opam
opam exec --switch "$SW" -- dune build -j 1 @opam
```

With Dune language 3.23, the first command reports a diff with exit status 1
when promotion is needed; the final command checks the promoted bytes.
A plain proof build does not update this file. See the
[Dune opam-alias contract](https://dune.readthedocs.io/en/stable/reference/aliases/opam.html).

# Building proofs and documentation

```sh
opam exec --switch "$SW" -- dune build -j 1
opam exec --switch "$SW" -- make doc
```

`make doc` builds `@doc` and copies `docs/main.html` to
`_build/default/main.html`. Open that copied index in a browser; the source
index's relative links are intended for the generated build directory.
The existing navigation remains available alongside the frame, fair-turn,
queue-client, allocator, and assumption-control map.
Documentation generation additionally uses odoc 3.2.1, included in the recipe
and frozen closure.

# Formal evidence

`artifact/theorem-map.csv` gives one fully qualified declaration per row, with
its manuscript section, module, and source-development category. The historical
comparison is the initial 2025 artifact release, revision
`e8f801d21cf09f0f4e247a51c9a7726cd6d7dfc5`; it is not asserted to be byte-identical
to the final published artifact. `not-applicable` marks the newly checked
regression examples rather than a historical theorem counterpart. Categories
describe the result relative to that release, not a priority claim against the
literature. In particular, the heap-queue recurrence is extended, whereas the
new allocated passive-client proof integrates generic temporal framing with
runner-safe source rewriting. The simulation and runner controls distinguish
inherited logical assumptions from client assumptions; their role as controls
does not mean their exact declarations existed in the historical release.

`examples/CSL/Evidence.v` imports the mapped modules and runs `Check` followed by
`Print Assumptions` on each declaration. The audit captures fresh query output
and recursively rechecks the compiled evidence root; a successful source build
alone is not an assumption audit.

```sh
python3 tools/artifact.py audit --switch "$SW"
python3 tools/artifact.py measure --switch "$SW"
opam switch export --switch "$SW" artifact/environment.export --freeze
python3 tools/artifact.py package --switch "$SW" --output /path/to/tisl-A1.tar.gz
python3 tools/artifact.py verify-package --switch "$SW" --archive /path/to/tisl-A1.tar.gz
```

Audit and measurement logs and parsed summaries are written under
`artifact/results/`. Measurements are serial full compilations with Dune's
cache disabled and a separately timed recursive kernel recheck; they are not
runtime benchmarks or a claim of cold filesystem caches. Package verification
rebuilds the extracted, checksummed bytes in a fresh switch, not the original
working tree. The bundle retains required license and copyright attribution;
these notices and public source fingerprints limit anonymity.

# Importing the frozen environment

The packaged `tisl-A1/` directory contains `environment.export`, `source/`, and
the pinned source in `dependencies/ctrees/`. From the extracted `tisl-A1/`
directory, choose a fresh switch name:

```sh
SW=tisl-A1-local
opam switch create "$SW" --empty --no-switch -y
opam repository add rocq-released https://rocq-prover.org/opam/released --switch "$SW" -y
opam switch import --switch "$SW" environment.export --yes
opam pin add --switch "$SW" -y rocq-ctree.2.0-dev ./dependencies/ctrees
```

Then, from `source/`, run:

```sh
opam exec --switch "$SW" -- dune build -j 1
opam exec --switch "$SW" -- make doc
python3 tools/artifact.py audit --switch "$SW"
```

The export includes exact package versions and pins but not all downloaded
archives, so importing it also requires network access. Keep the default
switch unchanged and do not overwrite an existing local switch.
