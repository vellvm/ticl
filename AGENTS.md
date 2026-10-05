# Ticl repository guidance

## Purpose

Ticl is Temporal Interaction and Choice Logic: a Rocq development for structural verification of arbitrary temporal properties over interaction-and-choice trees. Nested properties such as `AG AF` are supported by the same reusable program-structure lemmas as simpler safety and liveness properties.

## Proof dependency ladder

Keep dependencies directed from reusable foundations toward applications:

1. General semantics and temporal reasoning: `theories/Logic/` defines the temporal logic and worlds; `theories/ICTree/` defines trees, equality, bisimulation, transitions, and the general modality-by-program-structure lemmas in `theories/ICTree/Logic/`.
2. Interpretation: `theories/ICTree/Interp/` defines effect handlers/interpreters and reusable reasoning about interpreted trees. Reuse `Core.v`, `State/Mod.v`, `Heap.v`, and the existing generic state/iteration lifting lemmas in `theories/ICTree/Logic/State.v`. A theorem that does not mention language syntax belongs at this reusable layer, not in an example or language implementation.
3. Languages: `theories/Lang/` owns syntax, denotation into trees, and structural Ticl lemmas stated over language programs. `MeQ.v` is the queue language, `MeS.v` is tagged secure memory, and `StImp.v` is the general imperative-language example. Language proofs specialize reusable interpretation lemmas.
4. Examples: `examples/` defines concrete programs, invariants, variants, representations, and their correctness proofs. Example proofs should apply language structural lemmas; do not reproduce interpreter unfolding, transition inversion, induction/coinduction, or scheduler machinery here when a reusable lower-layer lemma can express the argument.

Read `examples/Queue.v` and `theories/Lang/MeQ.v` as the reference pattern. The queue theorem `rotate_agaf_pop` proves `AG AF` by applying `ag_qprog_invariance`, `aul_qprog_eventually`, and the queue operation/bind lemmas. Domain-specific list facts stay in the example; general temporal reasoning stays below it.

## CSL ownership

- `theories/Lang/CSL/Mod.v` is the sole CSL language implementation: its memory commands, program syntax, and denotation. Reuse the shared heap model and PCM/separation support instead of defining competing heaps or resource algebras.
- `theories/ICTree/Interp/CSL/Mod.v` is the sole CSL interpreter implementation. It interprets effects/trees, not CSL syntax, and must not import `theories/Lang/` or `examples/`.
- CSL language structural theorems specialize interpreter theorems; queue and allocator programs remain clients. Support files are allowed, but they must not define a second CSL language/interpreter or retain an obsolete forwarding facade.
- Queue-specific programs, representations, and recurrence/framing/composition proofs belong in `examples/CSL/Queue/`; allocator programs belong in `examples/CSL/Allocator/`.
- The canonical memory state carries data cells and live allocation extents. `CAlloc` is malloc; `CFree` releases the recorded whole block. `CFree 0` does nothing, and invalid nonzero frees are stuck. Allocator `remote_free` is free-list publication, not physical heap deallocation.
- Heap models, events, and resource algebras are below both interpreters and languages. Keep them independent of example layouts and program syntax.

## Refactoring and proof rules

Preserve the modality-by-program-structure theorem family, its coverage, theorem strength, and nondeterministic/round-robin distinctions. An exported structural theorem or standalone verification theorem is not dead merely because a search finds no callers. Generalize and deduplicate proof machinery underneath these APIs rather than replacing them with manual rewrite instructions.

Put a new reusable fact at the lowest layer that can state it without importing a higher layer. Before writing a new handler, interpreter, heap operation, temporal proof, or separation law, look for an existing equivalent and reuse it. Do not add new axioms, `Admitted`, fake semantics, bounded allocation fallbacks, or compatibility aliases to make a refactor compile; Stdlib UIP and functional extensionality are always allowed and need no audit or caveat prose in documentation. Migrate every caller when moving an API, and delete the superseded implementation only after its replacement exists.

Preserve existing operational behavior, visible observations, fault behavior, scheduling semantics, separation laws, and theorem hypotheses during organizational changes. Examples must not become the source of reusable interpretation facts.

## Building and checking

Run from the repository root with the project's Rocq/opam environment active. `make` invokes `dune build`; `make doc` invokes `dune build @doc`; `make install` builds and installs the package. The documented compiler baseline is Rocq 9.0.0; the Dune project requires Dune 3.21 and the ExtLib, Equations, and Coinduction theories. `theories/dune` uses qualified subdirectories and the logical theory name `TICL`; `_CoqProject` maps `_build/default/theories` to `TICL` and `_build/default/examples` to `examples`; CSL example modules import each other through `From examples`.

Validate changed behavior with concrete operation/program proofs as well as compiling the affected examples. Keep existing liveness and counterexample theorems, especially nested `AG AF` and scheduler-specific results. Do not treat graphify reports, generated `_build/` files, or historical zero-caller lists as authoritative source code or proof of safe deletion.
