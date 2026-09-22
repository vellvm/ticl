# Cooperative heap queues

`TICL.Lang.CSL` is a typed cooperative fork/yield language over a disjoint heap
PCM. `Lang.CSL.Queue.Program.allocated_parallel_queues values1 values2` constructs two linked
queues by source execution on `hemp`, then starts their workers. The lower-level
`Lang.CSL.Queue.Program.parallel_queues u v` remains available for preallocated heaps. Both
workers own **different queues in one shared heap**; they do not concurrently
modify one queue, and the facade does not assert a general CSL parallel rule.

## Library ownership

Import `Lang.CSL` for the language, interpreter, source segments, and structural
TICL matrix. Import `Lang.CSL.Queue` for the reusable queue development. The old
example-local implementation modules were moved, not retained as compatibility
re-export files.

| Layer | Canonical reusable content |
| --- | --- |
| `ICTree.Trace` | Observation-polymorphic finite log prefixes, labeled finite steps, guarded prefix alignment |
| `ICTree.Logic.Trace` | Structural AF/AGAF rules for finite observation prefixes |
| `ICTree.Logic.Bind` | Five exact `*_log_iff` rules, shared by the CSL emit matrix |
| `ICTree.Logic.State` | Ghost-ranked `aul_state_iter_ghost` over arbitrary handlers |
| `ICTree.Interp.State.Mod` | Generic `interp_state_trigger_bind` normalization |
| `Utils.Relations` | One lexicographic construction, finite first-index search, interval counts, and infinite-occurrence facts |
| `Lang.CSL.Heap` | Checked heap laws shared by both observation alphabets |
| `Lang.CSL.Segments` | Exact and bisimilar first-yield segments, guard transport, arbitrary-pool ND/RR equations |
| `Lang.CSL.Queue` | Queue representation/layout, one polymorphic rotation implementation and proof, framing, composition, source programs, and recurrence |

Concrete address layouts, overlap counterexamples, allocator-specific state
machines and their fairness/rank arguments, and regression consumers remain in
`examples/CSL`. No library module imports an example. The exact and bisimilar
segment judgments remain distinct; administrative guards are not replaced by
visible scheduler steps.

Operational consumers use the public checked-operation normal forms instead of
local read/write/emit/allocation/CAS tactics. Temporal consumers use the source
matrix, log-prefix rules, and state-iteration rules. Queue recurrence shares the
same ghost-ranked rule with active queue composition; it does not reprove the
underlying fixed point.

## Actual execution and proof boundary

The source execution is:

```text
raw source denotations
  -> existing Yield vector scheduler
  -> modulo-cursor branch refinement
  -> Spawn/Yield erasure
  -> one shared checked heap handler
```

`ICTree.Interp.Refine` owns the stateful cursor API, erasing runner, observational
`BranchFree` predicate and closure proofs, and parity picker facts.
`ICTree.Interp.Yield.RoundRobin` owns the handler-parametric pool interpreter and
its eight execution equations. Neither module imports a language or example.
`Lang.CSL.Interp` instantiates that API with `sh`; it owns source-constructor
execution equations and scoped-fork startup. No example-local pool interpreter
or bridge module is used.

Every encountered `Br` is refined, including source branches in a generic raw
pool. `Br 0` has one alternative and still advances the cursor. Guards, events,
and Spawn do not advance it. `denote_branchfree` proves that CSL source trees
have no branch nodes. This policy does not force a nonyielding worker to yield,
and no universal fairness theorem for arbitrary or changing pools is claimed.

Fork prepends the child while retaining parent focus. Thus the initial queue
pool is `[queue2; queue1]`, slot 1 is focused, and cursor 0 has not yet been used
for selection. The parent runs first. `queue_pick_next`, parked iteration guards,
and `queue_pool_turn` establish the subsequent alternation explicitly.

`rotate_once` executes nine source instructions: read head, read payload, emit,
read next, write head, read old tail, write the tail/header link, clear the moved
node's link, and write tail. Only the worker's final yield relinquishes focus.
The singleton case links through the header. There is no atomic-rotation
primitive and no output generated from ghost payload lists.

`Program.interp_rr_rotate_once` composes the source constructor rules for those
instructions, preserving fault behavior and the entire post-emit heap suffix.
`queue_pool_bisim` matches both failed-read cases and takes its coinductive step
at a real `Log (SPop ...)` transition, not at an administrative guard.
`Program.run_rr_parallel_bisim` proves equivalence of the actual `run_rr` source
execution to the tagged cyclic reference for any heap, without unused queue
representation premises. The reference alone is not evidence of source execution.

`Program.run_rr_allocated_parallel` proves that actual silent allocation and
checked initialization from `hemp` reach a finite heap with two PCM-separated
queues and the original worker execution, at the same observation counter.
It also covers empty input lists. No initialized heap is assumed.

`Lang.CSL.Queue.Ticl` exposes recurrence directly for
`run_rr (allocated_parallel_queues values1 values2) hemp c`:

- `rotate_agaf_pop_alloc`: queue 1 ordinary recurrence.
- `rotate_agaf_pop_alloc_q2`: queue 2 ordinary recurrence.
- `rotate_agaf_pop_alloc_fresh`: queue 1 recurrence at every inclusive index bound.
- `rotate_agaf_pop_alloc_q2_fresh`: queue 2 recurrence at every inclusive index bound.

These four theorems require only one successful `find` premise for each payload
list, not representation, disjointness, or preallocated-heap premises. They
transport the existing worker recurrence through the proved initialization
bisimulation. The lower-level statements remain:

- `rotate_agaf_pop_rr`: queue 1 ordinary recurrence.
- `rotate_agaf_pop_rr_q2`: queue 2 ordinary recurrence.
- `rotate_agaf_pop_rr_fresh`: queue 1 recurrence at every inclusive index bound.
- `rotate_agaf_pop_rr_q2_fresh`: queue 2 recurrence at every inclusive index bound.
- `rotate_agaf_pop_rr_owned`: queue 1 recurrence from actual PCM separation.

Each lower-level conclusion is `AG (AF visW {...})` over `run_rr (parallel_queues u v) h c`.
Both membership premises remain: both workers must be nonempty and productive
for recurrence. The internal execution bisimulation also covers faulty heaps.
Freshness means `k <= sidx`; `sfresh_excludes_retained` prevents counting an old
observation at index `j` toward the bound `S j`.

## Heap and ownership contract

The canonical heap is `nat -> option nat`, with pointwise `heq`, pointwise
`hdisj`, and left-biased `hunion`. This representation does **not** impose finite
support. `heap_finite` is an existential proof bound, not a new carrier or runtime
field. `SSig` remains `(Heap * nat)%type`; results remain `(result, SSig)`.

`Events.HeapE` supplies the single shared command algebra: `HRead`, `HWrite`,
`HAlloc`, `HFree`, and `HCAS`. `ICTree.Events.Heap` supplies the polymorphic
`heap_read`, `heap_write`, `heap_alloc`, `heap_free`, and `heap_cas` triggers.
Neither module imports a language, concrete heap, allocator, or observation type.
CSL uses `sE := heapE + writerE (nat * nat)`; QLang uses
`qE := heapE + writerE nat`. Their observation handlers are separate from the
shared checked `heap_handler`, whose allocation search is polymorphic in the
observation alphabet.

`CAlloc size` uses `heap_alloc`/`HAlloc` and a guarded, constructive search inside the shared
handler. It returns the least positive base whose entire interval is free and
initializes exactly `size` cells to zero, preserving every old allocated value
and address zero. It neither emits nor yields, and advances neither the
observation counter nor the scheduler cursor. There is no runtime fuel,
caller-selected base, heap-wide maximum, classical choice, or allocation log.
Size zero is `stuck`. Positive requests terminate on every finite heap; an
infinite heap with no suitable interval silently diverges, as proved by
`alloc_search_no_space`. This is not a finite-memory exhaustion policy.

Reads and writes remain checked; writes never allocate implicitly. Emit records
`SPop tag value c`, preserves the heap, and increments the global observation
counter. CAS faults on an absent cell, updates and returns `true` on a matching
value, and otherwise returns `false` without changing the heap. It does not log.
The scheduler cursor is separate. There is no variable store, lock, or implicit
read/write yield.

`HFree a` removes exactly one cell via `Pcm.hfree`, without a presence check,
observation, or counter change. An absent free succeeds; a subsequent read of
that address faults. `free_local_frame` still requires ownership of the removed
cell. Physical free is available to raw CSL threads, not a new `CFree` syntax
constructor; the allocator example's `remote_free` remains CAS-based free-list
publication, not heap deletion.

HeapImp lowers the same five commands to its existing `Get`/`Put` effects.
Its association-list policies remain different: writes may create a cell,
allocation starts at `fresh_addr` (zero on an empty heap), and allocation of zero
cells still performs `Put`. Writes, free of an absent cell, and successful CAS
including same-value CAS retain full-memory logging. Failed CAS does not `Put`.

`qrep` reserves address zero through `h 0 = None`; the handler itself has no
special address-zero check. Header `hdr` stores tail and `S hdr` stores head;
node `a` stores payload and `S a` stores its next pointer. `qrep` permits
unrelated allocated cells, and an empty queue may retain a stale allocated tail.
`qrepX := qrep /\ qex` expresses exact ownership. Framing requires both heap
disjointness and a frame that leaves address zero unallocated.

`owned_queues` is precisely `asep (qrepX ...) (qrepX ...)`, using transparent
`HeapPCM`, not a conjunction standing in for separation. `owned_queues_sound`
uses `compose3` and pointwise footprint agreement; it does not equate heap
functions by Leibniz equality.

## Structural temporal interface

`From TICL Require Import Lang.CSL.` exports `Lang.CSL.Ticl`. Its 100 source rules
are the full name product
`{anl,anr,aul,aur,ag}_csl_{nd,rr}_{read,write,emit,yield,fork,ret,bind,until_none,alloc,cas}`.
They apply to arbitrary nonempty focused pools and continuations, not only queue
or allocator fixtures. Another 30 rules use suffixes `select`, `alloc_finite`,
and `heap_free`, giving 130 independently named equivalences.

Silent rules transport the interpreted residual in the same world. Emit rules
keep the current-prefix obligation in the old world and place only the successor
in `Obs (Log (SPop tag value c)) tt`. ND yield checks every branch, including the
single branch of a singleton pool; RR yield selects `rr_pick n m` and advances
only the cursor. Fork prepends its child but keeps the parent focused. Bind and
until preserve the pool and the outer `None` halt flow. These rules assert no
fairness or unconditional loop termination.

`interp_nd_source_` and `interp_rr_` expose the checked success and fault normal
forms in `Lang.CSL.Interp`; the promoted read/write helpers are public there.
Finite-allocation rules quantify over the first-fit witness supplied by
`heap_finite`, rather than requiring a caller-chosen address. Raw `heap_free`
rules take a `unit` continuation and preserve focus, pool size, cursor, counter,
and observation world. Fault rules compose with the generic stuck rules:
strong AN and AG are false, while AU may match its target immediately.

## Runtime queue construction

`new_queue values` allocates one block of `2 * S (length values)` cells, then
`init_queue` and `fill_nodes` execute ordinary checked writes. Header `hdr`
stores the last node and `S hdr` the first; `queue_nodes hdr count` starts at
`hdr + 2` with stride two. Both odd and even runtime bases are valid. Duplicate
payloads are permitted. `new_queue []` allocates two header cells and writes
zero to both, rather than requesting an invalid zero-size block.

`interp_rr_fill_nodes`, `interp_rr_init_queue`, and `interp_rr_new_queue` prove
execution with arbitrary raw continuation, pool, focus, cursor, and observation
index. `new_queue_heap` describes the exact result of those writes, not a second
interpreter. `new_queue_heap_owned` separates the exact `qheap` resource from
the unchanged old heap; it does not claim exact queue ownership of unrelated
cells. Allocation addresses need not remain the same under framing.

Both blocks are initialized before fork. Initialization emits and yields
nothing; the existing parent-first startup and rotation loop are unchanged.
The infinite workers do not allocate or free further storage.

## Donor provenance

These directories were **copy sources only**, not build or runtime dependencies:

```text
P = /home/eioannidis/ticl-sl/spark_submission/experiments/prove-scoped-pcm-transport-and-owned-structural-rules/proofs
Q = /home/eioannidis/ticl-sl/spark_submission/experiments/heap-backed-rotating-queue-and-unused-frame-transport/proofs
S = /home/eioannidis/ticl-sl/spark_submission/experiments/separate-active-composition-from-unused-framing/proofs
```

| Source | Current owner |
| --- | --- |
| `P/Pcm.v`, complete | `theories/Lang/CSL/Pcm.v` |
| `S/SLang.v`, heap prefix | `theories/Lang/CSL/Heap.v` |
| `Q/HeapQ.v` | `theories/Lang/CSL/Queue/Representation.v` |
| `Q/QLang.v` | `theories/Lang/CSL/Queue/Sequential.v`, shared `Operations.v` |
| `Q/Recurrence.v` | `theories/Lang/CSL/Queue/Recurrence.v`, `ICTree/Logic/State.v`, `Utils/Relations.v` |
| `Q/Trace.v` | `theories/Lang/CSL/Queue/Trace.v` |
| `Q/Layout.v` | `theories/Lang/CSL/Queue/Layout.v`; concrete fixtures in `examples/CSL/Layout.v` |
| `Q/Frame.v` | `theories/Lang/CSL/Queue/Frame.v` |
| `S/Sep2.v` | `theories/Lang/CSL/Queue/Separation.v` |
| `S/SLang.v`, turn/scheduler suffix | `theories/Lang/CSL/Queue/Alternating.v`, shared `Operations.v` |
| `S/Lex.v` | `theories/Utils/Relations.v` |
| `S/Compose.v` | `theories/Lang/CSL/Queue/Composition.v` |
| `Q/Overlap.v` | `examples/CSL/Overlap.v` |

The initial donor integration preserved the resource and observable contracts.
The current library cutover consolidates the duplicated heap handlers, rotation
programs/proofs, lexicographic induction, finite search, trace algebra, and
source-constructor normalization. `Pcm.hsingle`, `cellsat`, and the PCM framing
laws have one owning heap layer. The queue model retains `rot_detach_split` and
both `rot_heap_spec` conjuncts; no ownership premise was dropped from framing.

No `Layout2.v`, frozen donor TICL installation, or older exact-domain heap donor
was used. `Queue.Sequential` retains the untagged sequential observation
alphabet; `Queue.Alternating.sbody` alternates `turnk 1 u` and `turnk 2 v`
according to parity. Both instantiate `Queue.Operations.queue_turn` and
`queue_turn_spec`, so their memory operations and resource proof have one owner.

The new refiner's modulo-counter mechanism follows the read-only provenance
`git show 161d1eadedb7479b162fcde688e750b3a45ae37e:theories/Interp/Refine.v`.
Its old CTree API, arity-zero fault case, and state-first pairs were not copied.
In that original extraction, the only modified pre-existing proof file was
`ICTree/Eq/Bind.v`, which gained the generic `bind_stuck_equ` immediately after
`bind_guard`. Existing State/Yield work and Dune configuration were preserved.
The dynamic-allocation extension uses only the current repository: it adds no
donor dependency and changes no generic scheduler or refiner API.

## Behavioral verification

The existing operational regression modules and the shared-event/temporal suites compile:

- `PcmTests`: same-cell and overlapping-block ownership exclusion, distinct-cell
  separation, and the actual fresh-block split beside an unchanged points-to frame.
- `HeapTests`: checked access/fault behavior, exact emit observation/counter,
  zero-initialized allocation, whole-block first-fit rejection of partial overlap,
  zero-size faults, and silent divergence on a saturated infinite heap.
- `RoundRobinTests`: modulo choices, returned cursors, singleton-branch cursor
  advance, actual scheduler selection, and a language-independent shared state
  counter with complete trace `1,11,12,22` and final state 22.
- `InterpTests`: a child sees the parent's write, a scoped child skips both
  remaining loop body and post-loop continuation, and the finite alternating
  tagged trace. Allocation tests read a fresh zero cell and allocate across two
  active threads: parent base 1, child base 3, emit indices 0 and 1. All contracts
  include the final returned shared state.
- `QueueTests`: both literal preallocated fixtures and dynamically initialized
  programs on `hemp`, with both tags' ordinary/fresh recurrence and four-pop
  prefixes. The demo prefix is `(1,7,0),(2,8,1),(1,9,2),(2,8,3)`. Duplicate
  payloads still produce tags `1,2,1,2` at indices `0,1,2,3`. Source probes read
  the newly initialized `[7;9]` queue and both zero pointers of an empty queue.
- `NegativeTests`: retains the ownership/sequential/freshness controls. The
  low-level `parallel_queues` still faults on `hemp`. Dynamically initializing
  `[]` and `[8]` succeeds, but the first worker then faults on its null payload
  read; that execution is `stuck` and fails queue-1 recurrence. Sequential
  controls are not claims about arbitrary concurrent pools.
- `examples/HeapEventTests`: allocation/free/reallocation through shared triggers,
  single-cell deletion with a surviving block cell and frame, absent free,
  checked read-after-free, all 15 trigger embeddings, and the distinct HeapImp
  zero-allocation/write/free/CAS instrumentation policies.
- `TiclTests`: 23 temporal consumers using the new structural cells, including
  first-fit and finite allocation, shared write/CAS ordering, scoped child halt,
  universal ND versus cursor-dependent RR selection, productive and silent loops,
  strong termination/fault controls, immediate AU matching, and one-step raw free
  completion. Final heap postconditions use pointwise `heq`.

The shared-event and structural-rule extension passed its event-only, backend,
interpreter/helper, temporal-interface, and consumer compilation gates, followed
by `dune build`. All 130 public names were individually checked after importing
only the `Lang.CSL` umbrella. The current focused checks are:

```sh
dune build _build/default/examples/HeapEventTests.vo \
  _build/default/examples/CSL/TiclTests.vo
dune build
```

The initial baseline, every dependency gate, and the final `make build` passed.
The allocation extension rejected both requested temporary mutations with
nonzero proof compilation status:

1. Replacing `block_freeb`'s recursive `None` branch with `true` failed in
   `Heap.block_freeb_spec`, before the heap/source regression modules.
2. Replacing only `new_queue`'s `CAlloc` prefix with `CRet 1` failed in
   `Program.interp_rr_new_queue` at the source allocation equation, before
   `QueueTests`.

Both correct bodies were restored immediately. Afterwards:

```sh
dune build examples/CSL/PcmTests.vo examples/CSL/HeapTests.vo \
  examples/CSL/RoundRobinTests.vo examples/CSL/InterpTests.vo \
  examples/CSL/QueueTests.vo examples/CSL/NegativeTests.vo
make build
```

Both commands exited zero. No commit or index modification was performed.

The earlier scheduler migration separately recorded rejection of `rr_pick`
returning `Fin.F1` in `rr_pick_even`, and per-thread `run_rr` interpretation in
`run_rr_unfold`. Those generic mechanisms were not mutated for this extension.

## Trust-base audit

`coqtop -quiet -Q _build/default/theories TICL -Q _build/default/examples examples`
ran the post-build `Print Assumptions` audit for `sh_alloc_finite`,
`interp_rr_alloc`, `interp_rr_new_queue`, `run_rr_allocated_parallel`,
`run_rr_parallel_bisim`, and all four new dynamic recurrence theorems.
The changed `.v` files contain no `Admitted`, `admit`, `Axiom`, `Parameter`,
`Classical`, or choice declaration. Imports were checked for obsolete State
paths, HQ dependencies, donor runtime paths, and layer violations.

The structural-rule audit separately checked `anl_csl_nd_yield`,
`anr_csl_rr_emit`, `aul_csl_nd_until_none`, `aur_csl_rr_cas`,
`ag_csl_rr_until_none`, `aur_csl_nd_alloc_finite`, `ag_csl_rr_alloc_finite`,
`anr_csl_nd_heap_free`, `ag_csl_rr_heap_free`, `nd_emit_loop_ag`, and
`rr_emit_loop_ag` through `rocq_assumptions`. Each reports only the inherited
`FunctionalExtensionality.functional_extensionality_dep` and
`Eqdep.Eq_rect_eq.eq_rect_eq`. No new axiom or unfinished proof command was
introduced; the new heap postconditions do not identify functions by
functional extensionality.

The library extraction audit found `Utils.Relations.finite_first` closed under
the global context. `ICTree.Logic.State.aul_state_iter_ghost` and
`ICTree.Trace.rr_aligned_sbisim` use only inherited UIP. The generalized
`Lang.CSL.Segments.source_segment_scheduler_steps` uses inherited UIP and
dependent functional extensionality. Boolean-observation smoke proofs exercise
the promoted trace and AF-return rules independently of `SObs`.

The previously recorded baseline `examples.Queue.Queue.rotate_agaf_pop` prints:

```text
Axioms:
Eqdep.Eq_rect_eq.eq_rect_eq :
  forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
  x = eq_rect p Q x p h
MeQ.ME.T : Type
MeQ.ME.HDec : RelDec.RelDec eq
MeQ.ME.HCor : RelDec.RelDec_Correct MeQ.ME.HDec
```

`interp_schedule_rr_user` and `denote_branchfree` print only the same inherited
`Eqdep.Eq_rect_eq.eq_rect_eq` axiom. `run_rr_fork_bind`,
`run_rr_parallel_bisim`, and the five lower-level source recurrence theorems print:

```text
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq :
  forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
  x = eq_rect p Q x p h
```

The dynamic audit found only the already accepted assumptions:

| Audited theorem | Assumptions |
|---|---|
| `Heap.sh_alloc_finite` | `Eqdep.Eq_rect_eq.eq_rect_eq` (UIP) |
| `Interp.interp_rr_alloc` | UIP and dependent functional extensionality |
| `Program.interp_rr_new_queue` | UIP and dependent functional extensionality |
| `Program.run_rr_allocated_parallel` | UIP and dependent functional extensionality |
| `Program.run_rr_parallel_bisim` | UIP and dependent functional extensionality |
| All four `Queue.rotate_agaf_pop_alloc*` theorems | UIP and dependent functional extensionality |

The functional-extensionality dependency is inherited from the **pre-existing**
`ICTree.Interp.Yield.SBisim.schedule_pool_proper`, whose `Print Assumptions`
reports those same two axioms. That scheduler proof was not changed.
`interp_schedule_rr_equ` consumes it as required by the pool-congruence API.
This is not an added heap-extensionality axiom: `Heap.upd_pcm` and
`Queue.owned_queues_sound` each print `Closed under the global context`.
There is no new admitted constant, allocator-choice or finite-support oracle,
assumed initialization correctness, fairness or recurrence axiom, or assumed
program bisimulation.
