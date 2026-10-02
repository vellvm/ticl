# Cooperative heap queues

`TICL.Lang.CSL.Mod` is a typed cooperative fork/yield language over a disjoint heap
PCM and a shared variable context: heap commands and Yield-style expressions,
assignment, conditionals and loops live in one `CProg` AST. `examples.CSL.Queue.Shared`
verifies one heap queue rotated forever by two spawned workers (see below).
`examples.CSL.Queue.Program.allocated_parallel_queues values1 values2` constructs two linked
queues by source execution on `managed_empty`, then starts their workers. The lower-level
`examples.CSL.Queue.Program.parallel_queues u v` remains available for preallocated heaps. Both
workers own **different queues in one shared heap**; they do not concurrently
modify one queue, and the facade does not assert a general CSL parallel rule.

## Library ownership

`ICTree.Interp.CSL.Mod` is the one CSL interpreter: the effect sum `sE`, the
state `SSig`, the observation sum `CSLObs`, the payload-polymorphic handler
`sh` (heap, context and indexed-emission handlers), thread effects, the
context get/put laws, the raw physical-free laws, and the effect-level
select/heap-free Ticl rules. It imports no language or example.
`Lang.CSL.Mod` is the one CSL language: `CExp`, `CProg`, their denotation,
source execution equations, exact first-yield segment rules, the structural
Ticl matrix, the Yield-fragment rules, and the source-pool rules; it
re-exports the interpreter and the generic Yield scheduler/logic layers. Import
`examples.CSL.Queue` for the queue development and `examples.CSL.Allocator.*`
for the allocator. The previous split implementation modules were removed, not
retained as compatibility re-export files.

| Layer | Canonical reusable content |
| --- | --- |
| `ICTree.Trace` | Observation-polymorphic finite log prefixes, labeled finite steps, guarded prefix alignment |
| `ICTree.Logic.Trace` | Structural AF/AGAF rules for finite observation prefixes |
| `ICTree.Logic.Bind` | Five exact `*_log_iff` rules, shared by the CSL emit matrix |
| `ICTree.Logic.State` | Ghost-ranked `aul_state_iter_ghost` over arbitrary handlers |
| `ICTree.Interp.State.Mod` | Generic `interp_state_trigger_bind` normalization |
| `Utils.Relations` | Lexicographic ranks, bounded predicate search, interval counts, and infinite-occurrence facts |
| `Utils.Lists` | Comparator-parametric first-match search and shared list-rotation lemmas |
| `Utils.Vectors` | Pointwise update/removal/cons laws shared by pool equivalence and bisimulation |
| `ICTree.Interp.CSL.Mod` | CSL effects, managed state, the shared handler instance, raw free and select rules |
| `ICTree.Interp.Yield.Segments` | Exact and bisimilar first-yield segments, guard transport, arbitrary-pool ND/RR equations |
| `ICTree.Interp.Yield.SBisim` | Guard alignment (`galigned`), its preservation by erasure/state/round-robin interpretation, guard-equivalent pool congruence |
| `ICTree.Logic.Yield` | Thread rules over arbitrary handlers; `ClosedTurns`/`RankedTurns` pool invariance and eventuality rules (ND and RR) |
| `Utils.Maps` | The variable context `Ctx.Ctx` shared by languages and the CSL interpreter |
| `Lang.CSL.Mod` | CSL syntax, denotation, source execution equations, source segment rules, structural matrix, Yield-fragment and source-pool rules |

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

The abstract and heap-backed queues use the same `find_index` implementation.
Natural payloads pass `Nat.eqb`; the abstract queue passes its existing
`@rel_dec T eq HDec`. Equality-dependent search lemmas take comparator
correctness explicitly. Repeated payloads select their **first** occurrence;
rotation preserves existence without claiming that duplicate payloads have a
unique position. `List.hd default list` replaces the old `hdf list default`.

Duplicate vector inversion and unused triple-projection well-foundedness
helpers were removed in favor of `inversion_0` and Stdlib's `wf_inverse_image`.
Scheduler parity and allocator cursor proofs share `rr_pick_mod_congr`.
Obsolete allocator transport/specialization helpers were removed, but unused
public structural rules and substantive verification goals remain intentional
proof roots. In particular, the 140 CSL rules, `aur_schedule_update`,
`free_local_disj`, `free_local_frame`, and allocator safety/liveness results are
not classified as dead merely because no other theorem references them.

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
`Lang.CSL.Mod` instantiates that API with `sh`; it owns source-constructor
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
at a real `Log (stamp ...)` transition, not at an administrative guard.
`Program.run_rr_parallel_bisim` proves equivalence of the actual `run_rr` source
execution to the tagged cyclic reference for any heap, without unused queue
representation premises. The reference alone is not evidence of source execution.

`Program.run_rr_allocated_parallel` proves that actual silent allocation and
checked initialization from `managed_empty` reach a finite heap with two
PCM-separated queues, an allocation table recording both actual blocks, and the
original worker execution, at the same observation counter.
It also covers empty input lists. No initialized heap is assumed.

`examples.CSL.Queue.Ticl` exposes recurrence directly for
`run_rr (allocated_parallel_queues values1 values2) (managed_empty,(ctx,c))`:

- `rotate_agaf_pop_alloc`: queue 1 ordinary recurrence.
- `rotate_agaf_pop_alloc_q2`: queue 2 ordinary recurrence.
- `rotate_agaf_pop_alloc_fresh`: queue 1 recurrence at every inclusive index bound.
- `rotate_agaf_pop_alloc_q2_fresh`: queue 2 recurrence at every inclusive index bound.

These four theorems require one successful `find_index Nat.eqb` premise per payload
list, not representation, disjointness, or preallocated-heap premises. They
transport the existing worker recurrence through the proved initialization
bisimulation. The lower-level statements remain:

- `rotate_agaf_pop_rr`: queue 1 ordinary recurrence.
- `rotate_agaf_pop_rr_q2`: queue 2 ordinary recurrence.
- `rotate_agaf_pop_rr_fresh`: queue 1 recurrence at every inclusive index bound.
- `rotate_agaf_pop_rr_q2_fresh`: queue 2 recurrence at every inclusive index bound.
- `rotate_agaf_pop_rr_owned`: queue 1 recurrence from actual PCM separation.

Each lower-level conclusion is `AG (AF visW {...})` over
`run_rr (parallel_queues u v) ((h,allocs),(ctx,c))` for an arbitrary extent table
`allocs` and context `ctx`; the queue predicates are `csl_indexed P`.
Both membership premises remain: both workers must be nonempty and productive
for recurrence. The internal execution bisimulation also covers faulty heaps.
Freshness is `indexed_after P k`: the payload satisfies `P` and its occurrence
index is at least `k`. `ICTree.Logic.Trace.indexed_excludes_retained` prevents
counting an old observation at index `j` toward the bound `S j`.

## One shared queue, two spawned workers

`shared_queue hdr` forks `worker 1 hdr`, then `worker 2 hdr`, and terminates;
the remaining pool is `[worker 2 hdr; worker 1 hdr]` (`run_{nd,rr}_two_forks`;
`scheduled_visible_two_forks` exhibits both `Spawn` events). Both workers rotate
the SAME queue. `exact_worker_turn` is an exact first-yield source segment of
one worker: one pop logged as `inr (stamp (tag,v) c)`, one rotation, and a
return to the same worker. `shared_worker_turn` packages it with the standard
invariant/position variant, for either worker, so the generic
`ag_csl_{nd,rr}_invariance` and `aul_csl_{nd,rr}_eventually` rules apply with
no fairness or phase argument. The public results are
`shared_rotate_agaf_pop_{nd,rr}` and `_fresh` (from any represented queue
containing the payload) and `shared_rotate_agaf_pop_alloc_{nd,rr}` and `_fresh`
(from `managed_empty`, one `find_index` premise). The plain theorems reuse the
fresh certificate at bound `0`. Under round robin worker 2 runs first, because
the parent is gone and the cursor is still `0`.

The pool rules rely on `interp_schedule_{nd,rr}_guard_equ`: pools equal up to
finitely many leading guards per slot are bisimilar for every focus, cursor and
state, proved through the guard-alignment relation `galigned`.

## Heap and ownership contract

The canonical data heap is `nat -> option nat`, with pointwise `heq`, pointwise
`hdisj`, and left-biased `hunion`. This representation does **not** impose finite
support. `heap_finite` is an existential proof bound, not a new carrier or runtime
field. The managed memory `ManagedHeap := Heap * AllocationTable` pairs the data
heap with the live malloc extents (base to positive length, same partial-map
representation); `ProductPCM` gives it componentwise separation, so an extent
record is an owned resource. `SSig` is `ManagedHeap * (Ctx.Ctx * nat)`, a state is
`((h,allocs),(ctx,c))`, and results remain `(result, SSig)`. The context is
shared by all threads and is not part of heap ownership. Runners take a full
state: `run_rr p ((h,allocs),(ctx,c))`, `run_nd p ...`, and the pool runners
`run_{nd,rr}_pool`. Runners start at `managed_empty` or an explicit `(h,allocs)`;
preallocated data uses `(h,hemp)`.

`Events.HeapE` supplies the single shared command algebra: `HRead`, `HWrite`,
`HAlloc`, `HFree`, and `HCAS`. `ICTree.Events.Heap` supplies the polymorphic
`heap_read`, `heap_write`, `heap_alloc`, `heap_free`, and `heap_cas` triggers.
Neither module imports a language, concrete heap, allocator, or observation type.
CSL uses `sE := heapE + (stateE Ctx.Ctx + writerE (nat * nat))`; the sequential
queue model uses `qE := heapE + (stateE Ctx.Ctx + writerE nat)`. Both are
interpreted by the one payload-polymorphic
`sh := h_sum heap_handler (h_sum csl_context_handler csl_emit_handler)`, at
payloads `nat * nat` and `nat`. Observations are `CSLObs A := Ctx.Ctx + indexed A`.

`CAlloc size` uses `heap_alloc`/`HAlloc` and a guarded, constructive search inside the shared
handler. It returns the least positive base whose entire interval is free and
initializes exactly `size` cells to zero, preserving every old allocated value
and address zero. It neither emits nor yields, and advances neither the
observation counter nor the scheduler cursor. There is no runtime fuel,
caller-selected base, heap-wide maximum, classical choice, or separate allocation
log; success records exactly `upd allocs base size` in the extent table.
Size zero is `stuck`. Positive requests terminate on every finite heap; an
infinite heap with no suitable interval silently diverges, as proved by
`alloc_search_no_space`. This is not a finite-memory exhaustion policy.

Reads and writes remain checked; writes never allocate implicitly. Emit records
`inr (stamp (tag,value) c)`, preserves the managed memory and context, and
increments the global observation counter. CAS faults on an absent cell, updates
and returns `true` on a matching value, and otherwise returns `false` without
changing the heap. It does not log. The scheduler cursor is separate. A
variable read `CVar x` looks up the shared context, yields once on success and
returns the captured value; an unbound variable is `stuck`. `CAssign x e`
evaluates `e`, then reads the current context again and logs exactly
`inl (add x v ctx)`; it does not change the counter. There is no lock.

`CFree base` (`HFree base`) is whole-block free through `managed_free`: at a
live recorded base it removes every cell of exactly that extent and its extent
record. `CFree 0` is a no-op even if address zero holds data. Every other free —
an interior pointer, an unknown base, or a second free of the same base — is
`stuck`, as are later reads, writes, and CAS on released cells. Free neither
emits nor yields, and changes neither the counter nor the cursor.
`managed_free_frame` releases exactly an owned `block_owned` resource while
preserving any disjoint frame. The allocator example's `remote_free` remains
CAS-based free-list publication, not heap deletion.

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

`From TICL Require Import Lang.CSL.Mod.` exports the full matrix. Its 110
source rules are the name product
`{anl,anr,aul,aur,ag}_csl_{nd,rr}_{read,write,emit,yield,fork,ret,bind,until_none,alloc,cas,free}`.
They apply to arbitrary nonempty focused pools and continuations, not only queue
or allocator fixtures. Another 30 rules use suffixes `select` and `heap_free`
(effect level, in `ICTree.Interp.CSL.Mod`) and `alloc_finite`, giving 140
independently named equivalences.

Silent rules transport the interpreted residual in the same world. Emit rules
keep the current-prefix obligation in the old world and place only the successor
in `Obs (Log (inr (stamp (tag,value) c))) tt`. ND yield checks every branch, including the
single branch of a singleton pool; RR yield selects `rr_pick n m` and advances
only the cursor. Fork prepends its child but keeps the parent focused. Bind and
until preserve the pool and the outer `None` halt flow. These rules assert no
fairness or unconditional loop termination.

`interp_nd_source_` and `interp_rr_` expose the checked success and fault normal
forms in `Lang.CSL.Mod`, including `*_free`/`*_free_invalid` and the
read/write/CAS `*_missing` faults. Finite-allocation rules quantify over the
first-fit witness supplied by `heap_finite`, rather than requiring a
caller-chosen address. Free rules require `managed_free memory base = Some
memory'` and preserve focus, pool size, cursor, counter, and observation world.
Fault rules compose with the generic stuck rules: strong AN and AG are false,
while AU may match its target immediately.

The Yield fragment is reasoned about through `scheduled_visible` (Spawn and
Yield visible), the standalone erased views `instr_exp_erased` and
`instr_flow_erased` (outer option flow exposed), and `run_nd`: expression rules
`axr_csl_exp_*`, singleton rules `axr_csl_nd_skip`, `axax_csl_nd_yield` (the
`AX AX` count is ND-specific), assignment rules `a{u,l}r_csl_{flow,nd}_assign*`,
bind and conditional rules `*_csl_flow_bind*`/`*_csl_flow_if`, and raw-event
while rules `*_csl_raw_while*` over `World CEff`, which make no scheduled
liveness claim.

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
| `P/Pcm.v`, complete | `theories/Utils/Pcm.v` (interface), `theories/Events/HeapModel.v` (heap model) |
| `S/SLang.v`, heap prefix | `theories/ICTree/Interp/CSL/Mod.v` |
| `Q/HeapQ.v` | `examples/CSL/Queue/Representation.v` |
| `Q/QLang.v` | `examples/CSL/Queue/Sequential.v`, shared `Operations.v` |
| `Q/Recurrence.v` | `examples/CSL/Queue/Recurrence.v`, `ICTree/Logic/State.v`, `Utils/Relations.v` |
| `Q/Trace.v` | `examples/CSL/Queue/Trace.v` |
| `Q/Layout.v` | `examples/CSL/Queue/Layout.v`; stride-two node geometry in `theories/Events/HeapModel.v` |
| `Q/Frame.v` | `examples/CSL/Queue/Frame.v` |
| `S/Sep2.v` | `examples/CSL/Queue/Separation.v` |
| `S/SLang.v`, turn/scheduler suffix | `examples/CSL/Queue/Alternating.v`, shared `Operations.v` |
| `S/Lex.v` | `theories/Utils/Relations.v` |
| `S/Compose.v` | `examples/CSL/Queue/Composition.v` |
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

Verification uses the actual proof development and its source programs. The
regression consumers are general statements in their semantic owners, plus one
lifecycle consumer of the source language:

- `Events.HeapModel`: `block_pto_overlap_false` (a block and an overlapping
  points-to cannot separate), `hfree_absent_noop` (deleting an absent key of a
  partial map is pointwise the identity; a CSL `CFree` of a non-base address is
  `stuck` instead), and `managed_free_frame` (whole-block free releases exactly
  an owned `block_owned` resource and preserves a disjoint frame).
- `Lang.HeapImp.HeapImp`: the five `instr_heapimp_*` equations for zero
  allocation, free, write, and successful/failed CAS. Same-value CAS still logs;
  a mismatching CAS does not.
- `ICTree.Eq.Bind.equ_guard_stuck`: a tree raw-equivalent to its own guard is
  raw-equivalent to `stuck`.
- `Lang.CSL.Mod`: `run_{nd,rr}_emit_loop_ag` (a productive `CUntilNone` loop
  satisfies `AG ⊤` in every not-done world) and `run_{nd,rr}_silent_loop_no_ag`
  (a silent loop is `stuck`, hence fails `AG ⊤`), beside the structural matrix.
- `examples/CSL/Memory.v`: `lifecycle_scope` (both CAS outcomes, adjacent
  first-fit blocks, whole-extent release, and the exact stamp sequence),
  `reuse_first_fit`, `free_null_unchanged`, and the `*_stuck` faults for
  interior-pointer free, double free, and read/write/CAS after free.
- `examples/CSL/Control.v`: `scoped_fork_no_parent_replay` (a child runs only
  its body), `context_resume_preserves_updates` (one yield per variable read,
  late context read in assignment, separate counter), and
  `missing_variable_stuck`.
- `examples/CSL/Queue/Shared.v`: `shared_queue_rr_prefix3` (the first three
  complete rotations of the allocated shared queue under round robin) and
  `allocated_shared_queue_empty_stuck`/`_no_ag`.
- `examples.CSL.Queue.Program`: `parallel_queues_four_pop_bisim` (the exact first
  four pops of any two represented, disjoint queues, then the reference loop;
  payloads may repeat), `parallel_queues_hemp_stuck`, and
  `allocated_parallel_queues_empty_stuck`; `examples.CSL.Queue.Ticl` derives the two
  corresponding `*_no_ag` results for an arbitrary formula.
- `examples/CSL/Overlap.v` and `examples/CSL/Allocator/Counterexamples.v` keep
  their witness queue, heaps, scripts, and observation tables as section-local
  `Let`s, discharged into the public statements.

`dune build` compiles all of them.

## Assumptions

The CSL development adds no `Axiom`, `Parameter`, `Admitted`, or `admit`. It
uses no allocator-choice or finite-support oracle and assumes no initialization
correctness, fairness, recurrence, or program bisimulation.
