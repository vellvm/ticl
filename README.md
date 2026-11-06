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

# Indexed formulas

`ticl E : option Type -> Type` uses `None` for prefix properties and `Some X`
for native-return postconditions. `ticll E` and `ticlr E X` are notation aliases;
both use the `<( ... )>` grammar. Temporal guards remain prefix formulas.
Native `ret R` requires one common return value across its completion transitions.

For a model returning `X`, `entails X b` evaluates `ticl_at E X b`:
`false` selects prefixes and `true` selects postconditions. Shared structural,
state, and language lemmas accept an abstract mode. The derivation family
`syntails X b` and `CTree.Logic.Soundness.soundness` cover the same modes.
Direct-body prefix iteration and return-driven iteration retain separate rules.
[`CTree/Logic/State.v`](theories/CTree/Logic/State.v) shares native-return bind
and iteration proofs across path quantifiers and endpoint modes. The
`u_state_iter_prefix_ghost` and `u_state_iter_ghost` rules carry an arbitrary
ghost rank together with the index, state, and world. Full-configuration and
natural-rank rules specialize these kernels; direct-prefix and return-driven
contracts remain distinct. Existing AN/EN and AU/EU interfaces retain their
contracts.
[`examples/IndexedSyntax.v`](examples/IndexedSyntax.v) checks these interfaces,
including grammar boundaries, changed-result binds, and a state-changing
countdown with exact final state, result, and observation.

With the build's opam switch active, check all three roots together so the kernel
sees their combined universe constraints:

```sh
opam exec -- rocqchk -o \
  -Q _build/default/theories TICL \
  -Q _build/default/examples examples \
  examples.IndexedSyntax examples.Scheduling examples.CSL.Evidence
```

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

## Scheduling observations

`CTree.Interp.Yield.Mod.schedule_policy` preserves source branches and emits
`Scheduled i` at each pool selection. The instrumented runner in
[`Policy.v`](theories/CTree/Interp/Yield/Policy.v) records program observations
under `inl` and selected slots under `inr`. Ordinary `interp_schedule_rr` is its
`rr_scheduler` specialization: one selection produces one logged pick, not an
extra silent step. `fair_obs` excludes these scheduling logs from program-event
predicates. `rr_fair` certifies the round-robin policy's pick stream;
`nd_not_fair` refutes the corresponding claim for nondeterministic selection.

## Structural CoCSL proof layers

[`Lang/CoCSL/Mod.v`](theories/Lang/CoCSL/Mod.v) provides the scheduled
AN/EN/AU/EU/AG/EG family and AX/EX/AF/EF specializations for ND and RR.
Commands, expressions, checked successes, and faults retain the actual CPS
continuation, pool, focus, state, and cursor. A scheduled native return means
termination of the entire pool, not completion of one source block.

The q-polymorphic `x_csl_*` and `u_csl_*` rules accept proper semantic
endpoints; their current-state guard must imply a live world. Complete
until-none/while AU/EU rules cut at actual continuing runs with a decreasing
ghost rank. AG/EG rules require a real next step before another loop cutpoint.
Silent guards and fork expansion alone do not establish progress. These source
rules specialize `au_family_wf`, `eu_family_wf`, `ag_family`, and `eg_family` in
[`CTree/Logic/Iter.v`](theories/CTree/Logic/Iter.v).

[`Lang/CoCSL/Sequential.v`](theories/Lang/CoCSL/Sequential.v) shares one checked
`write_list` macro and chronological `write_snapshots` across standalone,
ND, RR, and fair prefixes. Repeated addresses emit every snapshot; the first
missing address stops execution. Allocation tables, context, and counters
remain unchanged. Queue and allocator initialization reuse `node_writes` and
`link_updates` from [`Events/HeapModel.v`](theories/Events/HeapModel.v).
The queue representation deliberately reverses `node_writes` before
`apply_writes`, preserving historical first-match behavior on overlapping
addresses; checked initialization retains chronological last-write-wins order.

[`CTree/Interp/CSL/Frame.v`](theories/CTree/Interp/CSL/Frame.v) transports every
formula atom through `framer`; native postconditions acquire `frame_post`
for ND or `frame_postW` for logged RR.
Literal prefix preservation additionally requires `prefix_stable`.
Unconditional framing stays allocation-free. Conditional single-allocation
framing requires the same first-fit base in both heaps and a complete managed
post-state relation, including allocation-table ownership.

Example proofs compose these structural families without proof-level induction
or coinduction. Shared finite-prefix, closure, replay, and returning-pool rules
own that recursion below the examples. Heap-mutation AG/AF proofs use the source
loop and write rules directly, not a recurrence oracle over a trace model.

Fair-scheduler liveness in [`Fair.v`](theories/CTree/Interp/Yield/Fair.v) reuses
the finite observation-prefix rules in [`CTree/Logic/Trace.v`](theories/CTree/Logic/Trace.v).
`f_emit_list` and `f_emit_turns` lift finite observation prefixes for either
path quantifier and an abstract endpoint mode; unobserved turns still take a
visible step. The AF visibility and native-return corollaries specialize these
shared proofs.
`fair_obs` excludes scheduling logs. Fair-policy queue and allocator recurrence
results require a `FairScheduler`; their ND/RR contracts remain separate.

CoCSL denotation congruence (`denote_flow_bind_equ`, `denote_flow_fork_equ`,
`denote_equ`) and `denote_assign_lit` live in
[`Lang/CoCSL/Mod.v`](theories/Lang/CoCSL/Mod.v). The owned action relation,
projections, and canonical runner `owned_interp` live in
[`CTree/Interp/CSL/Owned.v`](theories/CTree/Interp/CSL/Owned.v).
`prim_reflect_joined`, `owned_interp_action`, and `owned_interp_trans_forward`
relate owned actions directly to the ND scheduler and checked CSL handler.
[`Lang/CoCSL/Owned.v`](theories/Lang/CoCSL/Owned.v) supplies source admission,
coupling, and the admission-free fork equation `owned_fork_runner`.

[`CTree/Interp/CSL/Asep.v`](theories/CTree/Interp/CSL/Asep.v) lifts ordinary
managed-heap `Utils.Pcm.asep` through `asep_at` and `asep_sat`. A proof-only
`AsepState` holds the complete current owned configuration and three live
predecessor worlds; it stores no execution prefix or trace. Each
`local_obligation` pins its heap to the corresponding current component.
An actual `asep_step` updates the global world and only the owner's local world;
empty logs preserve worlds, while retained selection/source-Step tau remains
a temporal step. Ordinary Rocq invariants can contain these TISL judgments.
`asep_at_inv` exposes both local derivations, current validity, and the invariant
at the same view; `asep_sat_inv` also recovers its tree/world relation.
The `asep_*` roots preserve asynchronous AN/EN and AX/EX, AG, native return,
AU/EU and AF/EF-return. These rules require one-action closure of the ordinary
invariant. `asep_ret` retains the invariant and both native-return postconditions
at their local predecessor worlds, with the native extensional result relation.
Common-execution EG instead requires the pointwise judgment at every state of
one execution with infinitely many retained raw labels from each owner;
retained Tau counts, erased reads do not. The same execution witnesses all
three EG conclusions.
Components remain branch-free and address-confined, with disjoint reserved
heaps, no allocation, and no context writes; checked faults remain stuck.
Projection and direct operational reflection live in the two `Owned.v` layers.
No simultaneous-next, transient-event synchronization, or generic RR/fair-run
composition law is claimed.

`asep_at_intro` combines a valid initial view, its initialized invariant, and
the two local TISL proofs; `asep_sat_intro` relates that view to its runner.
`asep_ret_elim` supplies the final native state, WF, saved local predecessor
worlds, and the invariant's remembered facts. Frozen base or phase facts are
initialized and preserved explicitly, not inferred from arbitrary live worlds.
`asep_at_auc_ret_step` preserves pointwise native-return AU obligations; it does
not assert preservation for arbitrary transient endpoints.
The independent `state_split_iff` API still exposes WF and both projected
current-state predicates through the same heap conjunction.

[`CSL/Frame/Asep.v`](examples/CSL/Frame/Asep.v), module `InvariantSeparation`,
independently proves concrete cursor-free separation contracts for the unchanged
two-worker programs. `split_cells` is ordinary managed-heap `Utils.Pcm.asep`.
`u_bind_r` obtains Parent's `parent_post`; the continuation retains that actual
`frame_post` proof across Child's foreign observation and early Parent return.
`workers_post` records the final spatial split, context/counter, current Child
world, and the saved Parent proof at a different world, before native return's
value transition. The raw-next proofs distinguish a scheduler pick from
the following one-cell heap observation. Exact loop turns preserve `loop_inv`
and decrease `k - counter` until an emission meets `fresh_emit k`, proving
`AG (AF fresh_emit k)` under both ND and RR without worker fairness.
The eight roots are checked in `CSL/Evidence.v`; their dependency closure excludes
both owned modules and the generic pointwise/source separation modules. No runtime
provenance or richer observations are added. These actual-shared-run instances
retain real global indices; the generic pointwise rules separately preserve
arbitrary local projected predicates under their stated invariant obligations.

Allocator initialization in
[`CSL/Allocator/Execution.v`](examples/CSL/Allocator/Execution.v) proves checked
standalone `instr_flow_init_links` and `instr_flow_init_page` equations once.
RR and ND initialization specialize `run_rr_prefix` and `run_nd_prefix`,
preserving pool focus, cursor, allocation extents, and untouched payloads.
Fair-scheduler initialization uses the same instrumented observation signature as RR.


